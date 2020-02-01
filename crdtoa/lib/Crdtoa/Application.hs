{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
module Crdtoa.Application
(
-- * Application abstraction
  module Crdtoa.Application
, API.StoreId(..)
, API.AppData(..)
, Ser.Serialize
) where

import Control.Monad (when, forever, (>=>))
import Servant (Proxy(..), (:<|>)(..), NoContent(..))
import qualified Control.Concurrent as Conc
import qualified Control.Concurrent.Async as Async
import qualified Control.Concurrent.STM as STM
import qualified Control.Exception as Exc
import qualified Data.Serialize as Ser
import qualified Network.HTTP.Client as HTTP
import qualified Network.HTTP.Client.TLS as TLS
import qualified Servant.Client.Streaming as Client
import qualified Servant.Types.SourceT as SourceT

import qualified Crdtoa.API as API

maxBackoffSec :: Int
maxBackoffSec = 600 -- five minutes

-- FIXME: when connecting to an empty store, no data is sent to the client and
-- so the client reaches ResponseTimeout
--
-- FIXME: when the sender becomes active, the listener should become active too
--      TODO: pull the wakeup tmvar out as an abstraction
--
-- TODO: log to stderr; look up logging libraries; monad-logger maybe?
--
-- TODO: generate a clientid with uuid:Data.UUID.V4.nextRandom

_createV0 :: Client.ClientM API.StoreId
sendV0 :: API.StoreId -> API.AppData -> Client.ClientM NoContent
listenV0 :: API.StoreId -> Client.ClientM (SourceT.SourceT IO API.AppData)
streamV0 :: API.StoreId -> API.ClientId -> SourceT.SourceT IO API.AppData -> Client.ClientM (SourceT.SourceT IO API.AppData)
_createV0 :<|> sendV0 :<|> listenV0 :<|> streamV0 = Client.client (Proxy :: Proxy API.API)

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
-- 'API.AppData' values to the store via the server.
--
-- Prefer one of the @with*@ variants such as 'withSer' or 'withRaw' over use
-- of this function. If you do use this function, you'll need to clean up the
-- background resources yourself.
runRaw
    :: Server
    -> Maybe API.StoreId
    -> Recv API.AppData
    -> IO (Client API.AppData)
runRaw (Server server) requestStore (Recv recv) = do
    env <- Client.mkClientEnv
        <$> HTTP.newManager TLS.tlsManagerSettings
        <*> Client.parseBaseUrl server

    let Just store = requestStore -- FIXME: call createV0

    outbox <- STM.atomically $ STM.newTQueue
    wakeup <- STM.atomically $ STM.newEmptyTMVar
    background <- Async.async $ beManager env store outbox wakeup
    return Client
        { background = background
        , store = store
        , send = \a -> STM.atomically $ do
            _ <- STM.tryPutTMVar wakeup ()
            STM.writeTQueue outbox a
        }
  where
    -- The manager runs the sender and listener once. It will complain if
    -- either of them quits or throws an exception. An additional exception
    -- will be raised when the application quits.
    beManager env store outbox wakeup
        = action `Exc.catches` handlers
      where
        action = do
            Async.withAsync (beSender env store outbox wakeup) $ \sender -> do
                Async.withAsync (beListener env store wakeup 0) $ \listener -> do
                    (a, _) <- Async.waitAny [sender, listener]
                    case a of
                        _ | a == sender -> fail "sender thread exited early"
                          | a == listener -> fail "sender thread exited early"
                          | otherwise -> fail "an unknown thread exited early"
        handlers =
            [ Exc.Handler ignoreAsyncCancelled -- Don't complain when exiting
            , Exc.Handler $ complainAndRethrowSomeException "manager"
            ]
    -- The sender blocks on outbox and sends things forever, until there's an
    -- error. Then it blocks on wakeup until either the listener or a send
    -- action wakes it up.
    beSender env store outbox wakeup = forever $ do
        putStrLn "[DEBUG] Sender waiting for item"
        item <- STM.atomically $ do
            _ <- STM.tryTakeTMVar wakeup
            STM.readTQueue outbox
        putStrLn "[DEBUG] Sender working"
        sentItem <- (action item `Exc.catches` handlers)
        when (not sentItem) $ do
            putStrLn "[DEBUG] Sender going to sleep"
            STM.atomically $ do
                STM.unGetTQueue outbox item
                STM.takeTMVar wakeup
      where
        action item =
            Client.runClientM (sendV0 store item) env
                >>= either
                    (complainClientError "sender,either" >=> unsent)
                    (acceptNoContent >=> sent)
                    -- TODO wakeup listener on success
        handlers =
            [ -- TODO: fill in handlers when we see exceptions reach the manager
            ]
        sent = const . return $ True
        unsent = const . return $ False
    -- The listener attempts to listen forever, handling its own error cases
    -- internally. It counts how many errors since it last heard back from the
    -- server, and backs off.
    beListener env store wakeupSender errors = do
        putStrLn $ "[DEBUG] Errors:" <> show errors <> ", BackoffSec:" <> show (exponentialBackoffSec maxBackoffSec errors)
        exponentialBackoff maxBackoffSec errors
        (action `Exc.catches` handlers)
            >>= beListener env store wakeupSender
      where
        action =
            Client.withClientM (listenV0 store) env
            . either (complainClientError "listener,either" >=> demerit)
            $ \stream -> do
                _ <- STM.atomically $ STM.tryPutTMVar wakeupSender ()
                SourceT.foreach complainMidstream recv stream
                reset ()
        handlers =
            [ Exc.Handler $ complainClientError "listener,catches" >=> demerit
            , Exc.Handler $ \case
                HTTP.HttpExceptionRequest _ HTTP.IncompleteHeaders ->
                    putStrLn "Disconnect midstream. Reconnecting.." >> reset ()
                HTTP.HttpExceptionRequest _ HTTP.NoResponseDataReceived ->
                    putStrLn "Disconnect before stream. Reconnecting.." >> reset ()
                exc ->
                    complainHttpException "listener,catches" exc >> demerit ()
            ]
        -- reset and demerit are shorthand for adjusting the error count which
        -- is used to compute backoff.
        demerit = const . return $ errors + 1
        reset = const . return $ 1
        -- This handles an error sent intentionally by the stream producer
        -- instead of treating it like a generic exception.
        complainMidstream err = putStrLn $ "[ERROR] Received from stream: " <> err

-- | A callback-based interface for an application which sends and receives
-- 'API.AppData' values.
--
-- Connect with the server to exchange updates in the store. If no store is
-- specified, the server will generate one. It is available in the returned
-- 'Client'.
-- 
-- This function follows the bracket-pattern to ensure that internal resources
-- are cleaned up.  If an exception occurred in a background thread, it will be
-- re-raised when this returns.
withRaw
    :: Server
    -> Maybe API.StoreId
    -> Recv API.AppData
    -> (Client API.AppData -> IO a)
    -> IO a
withRaw server store recv = Exc.bracket acquire release
  where
    acquire = runRaw server store recv
    release Client{background} = do
        Async.cancel background
        Async.wait background -- TODO: `Exc.catch` ignoreAsyncCancelled

-- | A callback-based interface for an application which sends and receives
-- 'Ser.Serialize'able values to the store via the server and follows the
-- bracket-pattern to ensure that internal resources are cleaned up.
withSer
    :: Ser.Serialize u
    => Server
    -> Maybe API.StoreId
    -> Recv (Either String u)
    -- ^ Deserialization errors are exposed to the receive function so that the
    -- application can be made aware of error cases, eg. receiving data from an
    -- incompatible version. The package /safecopy/ can be used to mitigate
    -- some data structure versioning issues.
    -> (Client u -> IO a)
    -- ^ The send function will serialize data before writing to the wire.
    -> IO a
withSer server store (Recv recvSer) actionSer = withRaw server store (Recv recvRaw) actionRaw
  where
    recvRaw = recvSer . Ser.decodeLazy . \(API.AppData bs) -> bs
    actionRaw client@Client{send=sendRaw} = actionSer client{send=sendRaw . API.AppData . Ser.encodeLazy}

-- TODO: make a pipes or conduit based interface? what about other
-- serialization libraries?

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

exponentialBackoff :: Int -> Float -> IO ()
exponentialBackoff cap = Conc.threadDelay . secToMicrosec . exponentialBackoffSec cap
  where
    round' = round :: Float -> Int
    secToMicrosec = (* round' 1e6)

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
