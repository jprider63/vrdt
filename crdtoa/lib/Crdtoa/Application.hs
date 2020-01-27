{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
module Crdtoa.Application where

import Data.String (fromString)
import Servant (Proxy(..), (:<|>)(..), NoContent)
import qualified Control.Concurrent as Conc
import qualified Control.Monad as Mon
import qualified Network.HTTP.Client as HTTP
import qualified Network.Wai.Handler.Warp as Warp
import qualified Servant.Client.Streaming as Client
import qualified Servant.Types.SourceT as SourceT

import qualified Crdtoa.API as API

createV0 :: Client.ClientM API.StoreId
sendV0 :: API.StoreId -> API.AppData -> Client.ClientM NoContent
listenV0 :: API.StoreId -> Client.ClientM (SourceT.SourceT IO API.AppData)
createV0 :<|> sendV0 :<|> listenV0 = Client.client (Proxy :: Proxy API.API)

main :: Warp.Port -> IO ()
main port = do
    putStrLn "Application demo"
    mgr <- HTTP.newManager HTTP.defaultManagerSettings
    let burl = Client.BaseUrl Client.Http "localhost" port ""
        env = Client.mkClientEnv mgr burl

    let store = API.StoreId "demo-store-id" -- FIXME: get via createV0

    -- send each line of stdin forever
    (print =<<) . Conc.forkIO . Mon.forever $ do
        input <- API.AppData . fromString <$> getLine
        Client.runClientM (sendV0 store input) env

    -- listen and print received messages forever
    Mon.forever $ do
        putStrLn $ "Listening on store " <> show store
        Client.withClientM (listenV0 store) env $ \case
            Left err -> putStrLn $ "Error in making stream request: " <> show err
            Right stream -> SourceT.foreach
                (\err -> putStrLn $ "Error receiving stream: " <> err)
                print
                stream

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
