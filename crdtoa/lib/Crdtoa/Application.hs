{-# LANGUAGE OverloadedStrings #-}
module Crdtoa.Application
(
-- * Application abstraction
  Server(..)
, Send(..)
, Recv(..)
, runRaw
, runSer
-- * Reexports
, API.StoreId(..)
, API.AppData(..)
, Async.Async
, Async.cancel
, Ser.Serialize
) where

import Servant (Proxy(..), (:<|>)(..), NoContent(..))
import qualified Control.Concurrent.Async as Async
import qualified Control.Monad as Mon
import qualified Data.Serialize as Ser
import qualified Network.HTTP.Client as HTTP
import qualified Servant.Client.Streaming as Client
import qualified Servant.Types.SourceT as SourceT

import qualified Crdtoa.API as API

_createV0 :: Client.ClientM API.StoreId
sendV0 :: API.StoreId -> API.AppData -> Client.ClientM NoContent
listenV0 :: API.StoreId -> Client.ClientM (SourceT.SourceT IO API.AppData)
_createV0 :<|> sendV0 :<|> listenV0 = Client.client (Proxy :: Proxy API.API)

-- | The base URL of a server to connect with.
newtype Server = Server String
-- | A receiver function which will be called for each message received from
-- your network.
newtype Recv a = Recv (a -> IO ())
-- | A send function which can be called to broadcast a message to your
-- network.
newtype Send a = Send (a -> IO ())

-- | A callback-based interface for an application which sends and receives
-- 'API.AppData' values to the store via the server.
--
-- TODO: change to receive a Maybe Server to signal the need to call createV0
runRaw
    :: Server
    -> API.StoreId
    -- ^ The store your application instance should communicate with.
    -> Recv API.AppData
    -> IO (Async.Async (), Send API.AppData)
    -- ^ This async represents the listener thread. Cancel the async to stop it
    -- from calling the receiver function and recover the associated resources.
    --
    -- FIXME: this doesn't work at all, probably because the receiving thread
    -- is masking interrupts while receiving on the TCP socket
runRaw (Server server) store (Recv recv) = do
    env <- Client.mkClientEnv
        <$> HTTP.newManager HTTP.defaultManagerSettings
        <*> Client.parseBaseUrl server
    listener <- Async.async . Mon.forever $ do
        Client.withClientM
            (listenV0 store)
            env
        $ either
            handleListenReqErr
            (SourceT.foreach handleMidstreamErr recv)
    let send x = do
            Client.runClientM
                (sendV0 store x)
                env
            >>= either
                handleSendReqErr
                (\NoContent -> return ())
    return (listener, Send send)
  where
    handleSendReqErr e = putStrLn $ "Error in making send request: " <> show e
    handleListenReqErr e = putStrLn $ "Error in making stream request: " <> show e
    handleMidstreamErr e = putStrLn $ "Error receiving stream: " <> e

-- | A callback-based interface for an application which sends and receives
-- 'Serialize'able values to the store via the server.
--
-- See 'runRaw' for information about the parameters.
runSer :: Ser.Serialize a => Server -> API.StoreId
    -> Recv (Either String a)
    -- ^ This receive function exposes deserialization errors so that the
    -- application can be made aware of error cases, such as receiving data
    -- from an incompatible version. The package /safecopy/ can be used to
    -- mitigate some data structure versioning issues.
    -> IO (Async.Async (), Send a)
    -- ^ This send function will serialize data before writing to the wire.
    -- See 'runRaw' for an explanation of the 'Async.Async'.
runSer server store (Recv recvSer) = do
    let recvRaw = recvSer . Ser.decodeLazy . \(API.AppData bs) -> bs
    (listener, Send sendRaw) <- runRaw server store (Recv recvRaw)
    let sendSer = sendRaw . API.AppData . Ser.encodeLazy
    return (listener, Send sendSer)

-- TODO: make a pipes or conduit based interface? what about other
-- serialization libraries?

-- FIXME: if the server is killed while clients are listening,
-- there's an "incomplete headers" IO exception from the listen
-- thread .. this is almost equivalent to the tcp disconnection case
-- that we're building to support explicitly.. needs to be handled
-- properly

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

-- FIXME: on launch with a server that doesn't exist, an IO acception that is
-- thrown.. that should be caught and conveyed to the application code through
-- the tbd application library abstraction
--
-- $ cabal v2-run crdtoa app 8090
-- /usr/bin/cabal ['/usr/bin/cabal', 'v2-run', 'crdtoa', 'app', '8090']
-- Up to date
-- Application demo
-- ThreadId 9
-- Listening on store StoreId "demo-store-id"
-- crdtoa: HttpExceptionRequest Request {
--   host                 = "localhost"
--   port                 = 8090
--   secure               = False
--   requestHeaders       = [("Accept","application/octet-stream")]
--   path                 = "/v0/listen/demo-store-id"
--   queryString          = ""
--   method               = "POST"
--   proxy                = Nothing
--   rawBody              = False
--   redirectCount        = 10
--   responseTimeout      = ResponseTimeoutDefault
--   requestVersion       = HTTP/1.1
-- }
--  (ConnectionFailure Network.Socket.connect: <socket: 23>: does not exist (Connection refused))
