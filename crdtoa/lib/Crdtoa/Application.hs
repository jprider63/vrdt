module Crdtoa.Application where

import Servant (Proxy(..), (:<|>)(..), NoContent)
import qualified Network.HTTP.Client as HTTP
import qualified Network.Wai.Handler.Warp as Warp
import qualified Servant.Client.Streaming as Client
import qualified Servant.Types.SourceT as SourceT

import qualified Crdtoa.API as API

postStream :: [String] -> Client.ClientM (SourceT.SourceT IO String)
createV0 :: Client.ClientM API.StoreId
sendV0 :: API.StoreId -> API.AppData -> Client.ClientM NoContent
listenV0 :: API.StoreId -> Client.ClientM (SourceT.SourceT IO API.AppData)
postStream
 :<|> createV0
 :<|> sendV0
 :<|> listenV0 = Client.client (Proxy :: Proxy API.API)

main :: Warp.Port -> IO ()
main port = do
    print "application demo"
    mgr <- HTTP.newManager HTTP.defaultManagerSettings
    let burl = Client.BaseUrl Client.Http "localhost" port ""
        env = Client.mkClientEnv mgr burl

    Client.withClientM (postStream $ words "hello there stream") env $ \result -> do
        case result of
            Left err -> putStrLn $ "Error in making stream request: " <> show err
            Right stream -> SourceT.foreach
                (\err -> putStrLn $ "Error receiving stream: " <> err)
                print
                stream
