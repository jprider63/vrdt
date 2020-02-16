{-# LANGUAGE NamedFieldPuns #-}
<<<<<<< HEAD:kyowon-client/src/Kyowon/Client.hs
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Kyowon.Client
(
-- * Application abstraction
  module Kyowon.Client -- Application
=======
module Crdtoa.Application
(
-- * Application abstraction
  withSer
, withRaw
, runRaw
, Server(..)
, Recv(..)
, Client(store, send)
>>>>>>> da18ca4454fce5f25dcb862fd7964265cd95561f:crdtoa/lib/Crdtoa/Application.hs
, API.StoreId(..)
, API.AppData(..)
, Ser.Serialize
) where

import Servant (Proxy(..), (:<|>)(..), NoContent(..))
import qualified Control.Concurrent.Async as Async
import qualified Control.Concurrent.STM as STM
import qualified Control.Exception as Exc
import qualified Data.Serialize as Ser
import qualified Data.UUID.V4 as UUIDv4
import qualified Network.HTTP.Client as HTTP
import qualified Network.HTTP.Client.TLS as TLS
import qualified Servant.Client.Streaming as Client
import qualified Servant.Types.SourceT as SourceT

<<<<<<< HEAD:kyowon-client/src/Kyowon/Client.hs
import           Kyowon.API (API)
import qualified Kyowon.API.V0 as API -- JP: For now. Update this. XXX
import           Kyowon.Types (ClientId)

data StoreRef a = StoreRef {
    storeRefServer :: Server
  , storeRefStore  :: API.StoreId
  }
=======
import Crdtoa.Log (slowLog, LogLevel(..), setupLogger)
import Servant.Extras ()
import qualified Control.Concurrent.STM.Extras as STME
import qualified Crdtoa.API as API
>>>>>>> da18ca4454fce5f25dcb862fd7964265cd95561f:crdtoa/lib/Crdtoa/Application.hs

maxBackoffSec :: Int
maxBackoffSec = 600 -- five minutes

-- error cases
--
-- 1. connect to a netcat listener and don't send anything, wait 30s
--      -> ResponseTimeout, backoff, ConnnectionError, backoff..
-- 1. connect to a new store and don't send anything, wait 30s
--      -> Listener stays connected
-- 1. connect to a store with some data, assert that it is received, don't send anything, wait 30s
--      -> Received, Listener stays connected
--
-- happy path
--
-- 1. connect to a store, send something, assert that it is forwarded -> OK
--
-- offline behavior
--
-- 1. connect to a store, kill the server, observe listener backoff
--      -> OK
-- 1. connect to a store, kill the server, send something, observe backoff
--      -> OK
-- 1. without starting the server, connect to a store, observe listener backoff
--      -> OK, kinda
--      -> FIXME: The shared wakeup abstraction means that both threads wake up, but
--      since they have different demerit counts, they race to set the next
--      sleep time.
-- 1. without starting the server, connect to a store, send something, observer backoff
--      -> OK, kinda
--      -> FIXME: The shared wakeup abstraction means that both threads wake up, but
--      since they have different demerit counts, they race to set the next
--      sleep time.
--
-- reconnection
--
-- 1. connect to a store, kill the server, start the server, observe listener reconnect
--      -> OK
-- 1. connect to a store, kill the server, send something, start the server, observe draining
--      -> OK
-- 1. connect to a store with some data, kill the server, start the server, observe listener reconnect, assert that data is received
--      -> This test doesn't make sense. Since the server doesn't persist the
--      data yet, it won't resend it to the client.

<<<<<<< HEAD:kyowon-client/src/Kyowon/Client.hs
_createV0 :: Client.ClientM API.StoreId
sendV0 :: API.StoreId -> API.AppData -> Client.ClientM NoContent
listenV0 :: API.StoreId -> Client.ClientM (SourceT.SourceT IO API.AppData)
-- <<<<<<< HEAD:kwik-client/src/Kwik/Client.hs
-- createV0 :<|> sendV0 :<|> listenV0 = Client.client (Proxy :: Proxy API)
-- 
-- main :: Warp.Port -> IO ()
-- main port = do
--     putStrLn "Application demo"
--     mgr <- HTTP.newManager HTTP.defaultManagerSettings
--     let burl = Client.BaseUrl Client.Http "localhost" port ""
--         env = Client.mkClientEnv mgr burl
-- 
--     let store = API.StoreId "demo-store-id" -- FIXME: get via createV0
-- 
--     -- send each line of stdin forever
--     (print =<<) . Conc.forkIO . Mon.forever $ do
--         input <- API.AppData . fromString <$> getLine
--         Client.runClientM (sendV0 store input) env
-- 
--     -- listen and print received messages forever
--     Mon.forever $ do
--         putStrLn $ "Listening on store " <> show store
--         Client.withClientM (listenV0 store) env $ \case
--             Left err -> putStrLn $ "Error in making stream request: " <> show err
--             Right stream -> SourceT.foreach
--                 (\err -> putStrLn $ "Error receiving stream: " <> err)
--                 print
--                 stream
-- 
-- -- FIXME: if the server is killed while clients are listening,
-- -- there's an "incomplete headers" IO exception from the listen
-- -- thread .. this is almost equivalent to the tcp disconnection case
-- -- that we're building to support explicitly.. needs to be handled
-- -- properly
-- =======
streamV0 :: API.StoreId -> ClientId -> SourceT.SourceT IO API.AppData -> Client.ClientM (SourceT.SourceT IO API.AppData)
_createV0 :<|> sendV0 :<|> listenV0 :<|> streamV0 = Client.client (Proxy :: Proxy API.API)
=======
-- TODO: make a pipes or conduit based interface? what about other
-- serialization libraries?

createV0 :: Client.ClientM API.StoreId
sendV0 :: API.StoreId -> (API.ClientId, API.AppData) -> Client.ClientM NoContent
listenV0 :: API.StoreId -> API.ClientId -> Client.ClientM API.ServerStream
createV0 :<|> sendV0 :<|> listenV0 = Client.client (Proxy :: Proxy API.API)
>>>>>>> da18ca4454fce5f25dcb862fd7964265cd95561f:crdtoa/lib/Crdtoa/Application.hs

-- | The base URL of a server to connect with.
newtype Server = Server String
-- | A receiver function which will be called for each message received from
-- your network.
newtype Recv a = Recv (a -> IO ())

-- | A client handle. Use it to send data like @send client myData@ or retrieve
-- the name of the connected store.
data Client a = Client
    { background :: Async.Async ()
    , store :: API.StoreId
    , send :: a -> IO ()
    }
-- TODO: jp says to expose the clientid, like storeid, because it's generated

-- | A callback-based interface for an application which sends and receives
-- 'API.AppData' values.
--
-- Prefer one of the @with*@ variants such as 'withSer' or 'withRaw' over use
-- of this function. If you do use this function, you'll need to clean up the
-- @background@ resources yourself.
runRaw
    :: Server
    -> Maybe API.StoreId
    -> Maybe API.ClientId
    -> Recv API.AppData
    -> IO (Client API.AppData)
runRaw (Server server) storeSpec clientSpec recv = do
    () <- setupLogger
    env <- Client.mkClientEnv
        <$> HTTP.newManager TLS.tlsManagerSettings
        <*> Client.parseBaseUrl server
    store <- maybe (createStore env) return storeSpec
    client <- maybe createClient return clientSpec
    outbox <- STM.newTQueueIO
    wakeup <- STME.newWakeupIO
    background <- Async.async $ manager env store client outbox recv wakeup
    return Client
        { background = background
        , store = store
        , send = \a -> STM.atomically $ do
            STME.wakeup wakeup
            STM.writeTQueue outbox a
        }
  where
    createClient
        = API.ClientId <$> UUIDv4.nextRandom
    createStore env
        = Client.withClientM createV0 env
        $ either (error "createStore,either") return
        -- FIXME this junk ^ eats actual errors

-- | The manager thread blocks while running the sender and listener once. It
-- will complain if either of them returns or throws and exception. Exceptions
-- are rethrown by the manager.
manager :: Client.ClientEnv -> API.StoreId -> API.ClientId -> STM.TQueue API.AppData -> Recv API.AppData -> STME.Wakeup -> IO ()
manager env store client outbox recv wakeup = action `Exc.catches` handlers
  where
    beSender = connectLoop (connectSend env store client outbox) wakeup 0
    beListener = connectLoop (connectListen env store client $ receiveTo recv) wakeup 0
    action = do
        Async.withAsync beSender $ \sender -> do
            Async.withAsync beListener $ \listener -> do
                (a, _) <- Async.waitAny [sender, listener]
                case a of
                    _ | a == sender -> fail "sender thread exited early"
                      | a == listener -> fail "listener thread exited early"
                      | otherwise -> fail "an unknown thread exited early"
    handlers =
        [ Exc.Handler ignoreAsyncCancelled -- Don't complain when exiting
        , Exc.Handler $ complainAndRethrowSomeException "manager,catches"
        ]

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
    adjustDemerits attempt = return $ case attempt of
        Demerit -> 1 + demerits
        Ok -> 0

-- | Connect obtain an item from the queue and send it via the send endpoint.
-- Exceptions are handled internally to assess the success of the connection
-- attempt. In the event of an exception, the item to be resent later.
--
-- XXX: consider using flushTQueue/mapConcurrently
-- XXX: how would that work with connectLoop?
connectSend :: Client.ClientEnv -> API.StoreId -> API.ClientId -> STM.TQueue API.AppData -> IO ConnectionAttempt
connectSend env store client source = action `Exc.catches` handlers
  where
    withNextItem = Exc.bracketOnError
        (STM.atomically $ STM.readTQueue source)
        (STM.atomically . STM.unGetTQueue source)
    action = withNextItem $ \item -> do
        slowLog DEBUG $ "Sender sending item: " <> show item
        Client.runClientM (sendV0 store (client, item)) env
            >>= either Exc.throwIO -- Use the existing handlers, put the item back on the queue
                (\resp -> acceptNoContent resp >> pure Ok)
    handlers =
        [ Exc.Handler $ \exc ->
            complainClientError "connectSend,catches" exc >> return Demerit
        ]

-- | Connect to the listen endpoint and block while receiving the stream or
-- until an exception occurs. Exceptions are handled internally to assess the
-- success of the connection attempt.
connectListen :: Client.ClientEnv -> API.StoreId -> API.ClientId -> (API.ServerStream -> IO ()) -> IO ConnectionAttempt
connectListen env store client sink = action `Exc.catches` handlers
  where
    action = do
        slowLog DEBUG "Listener connecting"
        Client.withClientM (listenV0 store client) env
            $ either Exc.throwIO -- Use the existing handlers
                (\resp -> sink resp >> return Ok)
    handlers =
        [ Exc.Handler $ \exc ->
            complainClientError "connectListen,catches" exc >> return Demerit
        , Exc.Handler $ \exc -> case exc of
            HTTP.HttpExceptionRequest _ HTTP.IncompleteHeaders ->
                slowLog INFO "Disconnect midstream. Reconnecting.." >> return Ok
            _ ->
                complainHttpException "connectListen,catches" exc >> return Demerit
        ]

-- |
--
-- TODO: inline this after clients start handling RequestResendUpdates
receiveTo :: Recv API.AppData -> API.ServerStream -> IO ()
receiveTo (Recv recv)
    = SourceT.foreach complainMidstream recv
    . SourceT.mapMaybe justUpdates
  where
    justUpdates item = case item of
        API.Update _ update -> Just update
        API.RequestResendUpdates -> Nothing
    -- This handles an error sent intentionally by the stream producer. Since
    -- we don't expect any errors from the stream producer currently, we just
    -- report it.
    complainMidstream err = slowLog WARNING $ "Received from stream: " <> err

-- | Sleep exponentially according to the number of demerits.
--
-- FIXME: this function isn't necessary once we have a proper logging library?
exponentialBackoff :: STME.Wakeup -> Int -> IO ()
exponentialBackoff wakeup demerits = do
    if demerits > 0
    then slowLog DEBUG $ "Demerits:" <> show demerits <> ", BackoffSec:" <> show backoffSec
    else return ()
    STME.sleepSec wakeup $ fromIntegral backoffSec
  where
    backoffSec = exponentialBackoffSec maxBackoffSec $ fromIntegral demerits

-- | A callback-based interface for an application which sends and receives
-- 'API.AppData' values.
--
-- This function follows the bracket-pattern to ensure that internal resources
-- are cleaned up. If an uncaught exception occurred in a background thread, it
-- will be re-raised when this returns.
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
-- are cleaned up. If an uncaught exception occurred in a background thread, it
-- will be re-raised when this returns.
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
<<<<<<< HEAD:kyowon-client/src/Kyowon/Client.hs
    actionRaw client@Client{send=sendRaw} = actionSer client{send=sendRaw . API.AppData . Ser.encodeLazy}

-- TODO: make a pipes or conduit based interface? what about other
-- serialization libraries?
-- >>>>>>> crdtoa:crdtoa/lib/Crdtoa/Application.hs

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
=======
    actionRaw c@Client{send=sendRaw} = actionSer c{send=sendRaw . API.AppData . Ser.encodeLazy}
>>>>>>> da18ca4454fce5f25dcb862fd7964265cd95561f:crdtoa/lib/Crdtoa/Application.hs

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
    slowLog WARNING $ loc <> ": HttpException with " <> (head . words . show $ info)
complainHttpException loc (HTTP.InvalidUrlException url reason) =
    slowLog WARNING $ loc <> ": HttpException for bad url '" <> url <> "': " <> reason
{-# INLINE complainHttpException #-}

-- | Log a message about a 'Client.ClientError' exception.
--
-- 'Client.FailureResponse' values seen:
--
-- * @Client.FailureResponse@ in a cafe and received a 406 from a network gatekeeper.
complainClientError :: String -> Client.ClientError -> IO ()
complainClientError loc exc =
    slowLog WARNING $ loc <> ": Servant ClientError." <> (head . words . show $ exc)
{-# INLINE complainClientError #-}

-- | Log a message and rethrow a 'Exc.SomeException' exception.
--
-- We rethrow because this could be an OOM or a SigInt or another thing that
-- must be handled by killing the thread/process.
complainAndRethrowSomeException :: String -> Exc.SomeException -> IO ()
complainAndRethrowSomeException loc exc = do
    slowLog WARNING $ "Exception reached " <> loc <> ": " <> show exc
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
