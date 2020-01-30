module Crdtoa.Application
(
-- * Application abstraction
  Server(..)
, Recv(..)
, Client(..)
, withSer
, withRaw
, runRaw
-- * Reexports
, API.StoreId(..)
, API.AppData(..)
, Ser.Serialize
) where

import Servant (Proxy(..), (:<|>)(..), NoContent(..))
import qualified Control.Concurrent as Conc
import qualified Control.Exception as Exc
import qualified Control.Monad as Mon
import qualified Data.Serialize as Ser
import qualified Network.HTTP.Client as HTTP
import qualified Servant.Client.Streaming as Client
import qualified Servant.Types.SourceT as SourceT

import qualified Crdtoa.API as API

-- TODO: generate a clientid with uuid:Data.UUID.V4.nextRandom
-- TODO: buffer sends when network is down, and return the size of the buffer

_createV0 :: Client.ClientM API.StoreId
sendV0 :: API.StoreId -> API.AppData -> Client.ClientM NoContent
listenV0 :: API.StoreId -> Client.ClientM (SourceT.SourceT IO API.AppData)
_createV0 :<|> sendV0 :<|> listenV0 = Client.client (Proxy :: Proxy API.API)

-- | The base URL of a server to connect with.
newtype Server = Server String
-- | A receiver function which will be called for each message received from
-- your network.
newtype Recv a = Recv (a -> IO ())
-- | A function which cancels a backing thread.
type Cancel = IO ()

data Client a = Client
    { listener :: IO ()
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
        <$> HTTP.newManager HTTP.defaultManagerSettings
        <*> Client.parseBaseUrl server
    let Just store = requestStore -- FIXME: call createV0
    listener <- Conc.forkIO . Mon.forever $ do
            Client.withClientM (listenV0 store) env
            $ either
                handleListenReqErr
                (SourceT.foreach handleMidstreamErr recv)
    -- TODO: insert into a channel, then attempt to drain the channel
    let send x = do
            Client.runClientM (sendV0 store x) env
            >>= either
                handleSendReqErr
                acceptNoContent
    return Client
        { listener = Conc.killThread listener
        , store = store
        , send = send
        }
  where
    handleSendReqErr e = putStrLn $ "Error in making send request: " <> show e
    handleListenReqErr e = putStrLn $ "Error in making stream request: " <> show e
    handleMidstreamErr e = putStrLn $ "Error receiving stream: " <> e
    acceptNoContent NoContent = return ()

-- | A callback-based interface for an application which sends and receives
-- 'API.AppData' values to the store via the server. 
--
-- This follows the bracket pattern to ensure that internal resources are
-- cleaned up.
withRaw
    :: Server
    -> Maybe API.StoreId
    -> Recv API.AppData
    -> (Client API.AppData -> IO a)
    -> IO a
withRaw server store recv = Exc.bracket acquire release
  where
    acquire = runRaw server store recv
    release = listener

-- | A callback-based interface for an application which sends and receives
-- 'Serialize'able values to the store via the server.
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
