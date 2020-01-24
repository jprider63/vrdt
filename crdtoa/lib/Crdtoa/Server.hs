module Crdtoa.Server where

import Control.Concurrent (threadDelay)
import Control.Monad.IO.Class (liftIO)
import Servant (Proxy(..), (:<|>)(..), NoContent)
import Text.Printf (printf)
import qualified Data.Time as Time
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Middleware.RequestLogger as Logger
import qualified Servant.Server as Server
import qualified Servant.Types.SourceT as SourceT

import qualified Crdtoa.API as API

main :: Warp.Port -> IO ()
main port = do
    printf "Starting server on port %d\n" port
    Warp.runSettings serverSettings
        . Logger.logStdoutDev -- XXX switch to logStdout later
        $ Server.serve (Proxy :: Proxy API.API) endpoints
  where
    -- XXX may need to ensure warp settings enable keep-alive and chunked-transfer
    serverSettings
        = Warp.setPort port
        $ Warp.defaultSettings

-- store structure should be a
--  * Map AppName ??
--  * Map StoreId ([AppData], Chan AppData)

endpoints :: Server.Server API.API
endpoints
    = strm -- :<|> hello
    :<|> createV0 :<|> sendV0 :<|> listenV0
  where
    strm xs = do
        liftIO $ putStrLn $ "Server saw" <> show xs
        return $ SourceT.fromStepT . mk $ xs
    mk [] = SourceT.Stop
    mk (x:xs) = SourceT.Effect $ do
        threadDelay $ round (1e6::Float)
        t <- Time.getCurrentTime
        return $ SourceT.Yield (show t <> x) (mk xs)

-- TODO: when reusing this for v1, make sure to namespace to a different set of stores
createV0 :: API.AppName -> Server.Handler API.StoreId
createV0 = undefined

sendV0 :: API.StoreId -> API.AppData -> Server.Handler Servant.NoContent
sendV0 = undefined

listenV0 :: API.StoreId -> Server.Handler (SourceT.SourceT IO API.AppData)
listenV0 = undefined
