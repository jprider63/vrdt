{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NamedFieldPuns #-}
module Crdtoa.Application
(
-- * Application abstraction
  module Crdtoa.Application
, API.StoreId(..)
, API.AppData(..)
, Ser.Serialize
) where

import Control.Monad ((>=>))
import Servant (Proxy(..), (:<|>)(..), NoContent(..))
import qualified Control.Concurrent.Async as Async
import qualified Control.Concurrent.STM as STM
import qualified Control.Exception as Exc
import qualified Data.Serialize as Ser
import qualified Data.UUID.V4 as UUIDv4
import qualified Network.HTTP.Client as HTTP
import qualified Network.HTTP.Client.TLS as TLS
import qualified Servant as Servant hiding (Proxy, (:<|>))
import qualified Servant.Client.Streaming as Client
import qualified Servant.Types.SourceT as SourceT

import Servant.Extras ()
import qualified Control.Concurrent.STM.Extras as STME
import qualified Crdtoa.API as API

maxBackoffSec :: Int
maxBackoffSec = 600 -- five minutes

-- FIXME: when connecting to an empty store, no data is sent to the client and
-- so the client reaches ResponseTimeout
--
-- TODO: log to stderr; look up logging libraries; monad-logger maybe?
--
-- TODO: make a pipes or conduit based interface? what about other
-- serialization libraries?
--
-- FIXME: when we disconnect the last sent message may have been lost
--
-- FIXME: the clientid in the post body of stream breaks servant server?

createV0 :: Client.ClientM API.StoreId
sendV0 :: API.StoreId -> API.AppData -> Client.ClientM NoContent
listenV0 :: API.StoreId -> Client.ClientM (SourceT.SourceT IO API.AppData)
streamV0 :: API.StoreId -> API.ClientId -> API.UpStream -> Client.ClientM API.DownStream
createV0 :<|> sendV0 :<|> listenV0 :<|> streamV0 = Client.client (Proxy :: Proxy API.API)

-- | The base URL of a server to connect with.
newtype Server = Server String
-- | A receiver function which will be called for each message received from
-- your network.
newtype Recv a = Recv (a -> IO ())

data Client a = Client
    { background :: Async.Async ()
    , store :: API.StoreId
    , send :: a -> IO ()
    }

-- | A callback-based interface for an application which sends and receives
-- 'API.AppData' values.
--
-- Prefer one of the @with*@ variants such as 'withSer' or 'withRaw' over use
-- of this function. If you do use this function, you'll need to clean up the
-- background resources yourself.
runRaw
    :: Server
    -> Maybe API.StoreId
    -> Maybe API.ClientId
    -> Recv API.AppData
    -> IO (Client API.AppData)
runRaw (Server server) storeSpec clientSpec recv = do
    env <- Client.mkClientEnv
        <$> HTTP.newManager TLS.tlsManagerSettings
        <*> Client.parseBaseUrl server
    store <- maybe (createStore env) return storeSpec
    client <- maybe createClient return clientSpec
    outbox <- STM.newTQueueIO
    pillow <- STME.newWakeupIO
    -- The background thread runs the connect-loop once. It will complain if an
    -- exception occurs or the connect-loop finishes early. An additional
    -- exception will be raised when waiting on the async at application quit.
    background <- Async.async $ let
        connect = connectStream env store client (sendFrom outbox) (receiveTo recv)
        action = do
            connectLoop connect pillow 0
            fail "background thread ended early"
        handlers =
            [ Exc.Handler ignoreAsyncCancelled -- Don't complain when exiting
            , Exc.Handler $ complainAndRethrowSomeException "background,catches"
            ]
        in action `Exc.catches` handlers
    return Client
        { background = background
        , store = store
        , send = \a -> STM.atomically $ do
            STME.wakeup pillow
            STM.writeTQueue outbox a
        }
  where
    createClient
        = API.ClientId <$> UUIDv4.nextRandom
    createStore env
        = Client.withClientM createV0 env
        $ either (error "createStore,either") return
        -- TODO this junk ^ eats actual errors

sendFrom :: STM.TQueue API.AppData -> API.UpStream
sendFrom = Servant.toSourceIO
-- FIXME: when sending an update fails, resulting in a disconnect, this loses
-- the update completely.. there's no backpressure so we can't fix that

receiveTo :: Recv API.AppData -> API.DownStream -> IO ()
receiveTo (Recv recv)
    = SourceT.foreach complainMidstream recv
    . SourceT.mapMaybe justUpdates
  where
    -- Filter to only Update messages until TODO caching locally and resend.
    justUpdates = \case
        API.Update _ update -> Just update
        API.RequestResendUpdates -> Nothing
    -- This handles an error sent intentionally by the stream producer. Since
    -- we don't expect any errors from the stream producer currently, we just
    -- report it.
    complainMidstream err = putStrLn $ "[ERROR] Received from stream: " <> err

-- | Describe whether a connection attempt showed the existence of a server at
-- the other end which responds positively to the request we sent.
data ConnectionAttempt = Ok | Demerit

-- | Backoff before running the next connection-attempt according to the number
-- of demerits since the last successful connection.
connectLoop :: IO ConnectionAttempt -> STME.Wakeup -> Int -> IO ()
connectLoop tryConnect wakeup demerits = do
    exponentialBackoff wakeup demerits
    tryConnect >>= adjustDemerits >>= connectLoop tryConnect wakeup
  where
    adjustDemerits = return . \case
        Demerit -> 1 + demerits
        Ok -> 0

-- | Make one connection attempt and block while sending from the up-stream and
-- receiving the down-stream. Return whether or not the attempt worked.
connectStream :: Client.ClientEnv -> API.StoreId -> API.ClientId -> API.UpStream -> (API.DownStream -> IO ()) -> IO ConnectionAttempt
connectStream env store client source sink
    = action `Exc.catches` handlers
  where
    constM = const . return
    action
        = Client.withClientM (streamV0 store client source) env
        $ either
            (complainClientError "connectStream,either" >=> constM Demerit)
            (sink >=> constM Ok)
    handlers =
        [ Exc.Handler $ complainClientError "connectStream,catches" >=> constM Demerit
        , Exc.Handler $ \case
            HTTP.HttpExceptionRequest _ HTTP.IncompleteHeaders ->
                putStrLn "Disconnect midstream. Reconnecting.." >> return Ok
            HTTP.HttpExceptionRequest _ HTTP.NoResponseDataReceived ->
                putStrLn "Disconnect before stream. Reconnecting.." >> return Ok
            exc ->
                complainHttpException "connectStream,catches" exc >> return Demerit
        ]

-- | Sleep exponentially according to the number of demerits.
--
-- FIXME: this function isn't necessary once we have a proper logging library?
exponentialBackoff :: STME.Wakeup -> Int -> IO ()
exponentialBackoff wakeup demerits = do
    putStrLn $ "[DEBUG] Demerits:" <> show demerits <> ", BackoffSec:" <> show backoffSec
    STME.sleepSec wakeup $ fromIntegral backoffSec
  where
    backoffSec = exponentialBackoffSec maxBackoffSec $ fromIntegral demerits

-- | A callback-based interface for an application which sends and receives
-- 'API.AppData' values.
--
-- This function follows the bracket-pattern to ensure that internal resources
-- are cleaned up. If an exception occurred in a background thread, it will be
-- re-raised when this returns.
withRaw
    :: Server
    -> Maybe API.StoreId
    -> Maybe API.ClientId
    -> Recv API.AppData
    -> (Client API.AppData -> IO a)
    -> IO a
withRaw server store client recv
    = Exc.bracket acquire release
  where
    acquire = runRaw server store client recv
    release Client{background} = do
        Async.cancel background
        Async.wait background `Exc.catch` ignoreAsyncCancelled -- Don't complain when exiting

-- | A callback-based interface for an application which sends and receives
-- 'Ser.Serialize'able values.
--
-- This function follows the bracket-pattern to ensure that internal resources
-- are cleaned up. If an exception occurred in a background thread, it will be
-- re-raised when this returns.
withSer
    :: Ser.Serialize u
    => Server
    -> Maybe API.StoreId
    -> Maybe API.ClientId
    -> Recv (Either String u)
    -- ^ Deserialization errors are exposed to the receive function so that the
    -- application can be made aware of error cases, eg. receiving data from an
    -- incompatible version. The package /safecopy/ can be used to mitigate
    -- some data structure versioning issues.
    -> (Client u -> IO a)
    -- ^ The send function will serialize data before writing to the wire.
    -> IO a
withSer server store client (Recv recvSer) actionSer
    = withRaw server store client (Recv recvRaw) actionRaw
  where
    recvRaw = recvSer . Ser.decodeLazy . \(API.AppData bs) -> bs
    actionRaw c@Client{send=sendRaw} = actionSer c{send=sendRaw . API.AppData . Ser.encodeLazy}

-- FIXME: on the first connection to a new store, the listen times out
-- because the server never sends anything back.. debugging with curl, we
-- have:
--
-- $ curl --trace-ascii - -X POST localhost:8080/v0/listen/demo-store-id
-- == Info:   Trying ::1:8080...
-- == Info: TCP_NODELAY set
-- == Info: connect to ::1 port 8080 failed: Connection refused
-- == Info:   Trying 127.0.0.1:8080...
-- == Info: TCP_NODELAY set
-- == Info: Connected to localhost (127.0.0.1) port 8080 (#0)
-- => Send header, 102 bytes (0x66)
-- 0000: POST /v0/listen/demo-store-id HTTP/1.1
-- 0028: Host: localhost:8080
-- 003e: User-Agent: curl/7.67.0
-- 0057: Accept: */*
-- 0064:
-- == Info: Empty reply from server
-- == Info: Connection #0 to host localhost left intact
-- curl: (52) Empty reply from server
-- ? 52

-- | @exponentialBackoffSec cap n@ computes the number of seconds, up to @cap@,
-- to backoff after @n@ failures.
--
-- FIXME: use the max in the power so that it takes the same number of failures to reach any max
--
-- >>> exponentialBackoffSec 30 <$> [0..5]
-- [0,2,6,19,30,30]
--
-- >>> exponentialBackoffSec 600 <$> [0..10]
-- [0,2,6,19,54,147,402,600,600,600,600]
--
-- >>> exponentialBackoffSec (-600) <$> [0..10]
-- [0,2,6,19,54,147,402,600,600,600,600]
--
-- >>> exponentialBackoffSec 600 <$> reverse [-10..0]
-- [0,2,6,19,54,147,402,600,600,600,600]
exponentialBackoffSec :: Int -> Float -> Int
exponentialBackoffSec cap = min (abs cap) . subtract 1 . round . exp . abs

-- | Log a message about an 'HTTP.HttpExceptionRequest' exception.
--
-- 'HTTP.HttpExceptionContent' values seen:
--
-- * @HTTP.ConnectionFailure _@ when connecting to server or a port that doesn't exist.
-- * @HTTP.ResponseTimeout@ when a server doesn't send any data back (eg. netcat).
-- * @HTTP.IncompleteHeaders@ when a server disconnects midstream.
complainHttpException :: String -> HTTP.HttpException -> IO ()
complainHttpException loc (HTTP.HttpExceptionRequest _req info) =
    putStrLn $ "[ERROR] " <> loc <> ": HttpException with " <> (head . words . show $ info)
complainHttpException loc (HTTP.InvalidUrlException url reason) =
    putStrLn $ "[ERROR] " <> loc <> ": HttpException for bad url '" <> url <> "': " <> reason
{-# INLINE complainHttpException #-}

-- | Log a message about a 'Client.ClientError' exception.
--
-- 'Client.FailureResponse' values seen:
--
-- * @Client.FailureResponse@ in a cafe and received a 406 from a network gatekeeper.
complainClientError :: String -> Client.ClientError -> IO ()
complainClientError loc exc =
    putStrLn $ "[ERROR] " <> loc <> ": Servant ClientError." <> (head . words . show $ exc)
{-# INLINE complainClientError #-}

-- | Log a message and rethrow a 'Exc.SomeException' exception.
--
-- We rethrow because this could be an OOM or a SigInt or another thing that
-- must be handled by killing the thread/process.
complainAndRethrowSomeException :: String -> Exc.SomeException -> IO ()
complainAndRethrowSomeException loc exc = do
    putStrLn $ "[BUG] Exception reached " <> loc <> ": " <> show exc
    Exc.throwIO exc
{-# INLINE complainAndRethrowSomeException #-}

-- | Do nothing about an 'Async.AsyncCancelled' exception.
ignoreAsyncCancelled :: Monad m => Async.AsyncCancelled -> m ()
ignoreAsyncCancelled Async.AsyncCancelled = return ()
{-# INLINE ignoreAsyncCancelled #-}

-- | Do nothing about a 'NoContent' response.
acceptNoContent :: Monad m => NoContent -> m ()
acceptNoContent NoContent = return ()
{-# INLINE acceptNoContent #-}
