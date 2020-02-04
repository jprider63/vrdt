{-# LANGUAGE TupleSections #-}
module Crdtoa.Server where

import Control.Monad.IO.Class (liftIO)
import Servant (Proxy(..), (:<|>)(..))
import Text.Printf (printf)
import qualified Control.Concurrent.Async as Async
import qualified Control.Concurrent.STM as STM
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Middleware.RequestLogger as Logger
import qualified Servant.Server as Server
import qualified Servant.Types.SourceT as SourceT

import qualified Crdtoa.API as API
import qualified Crdtoa.Server.Store as Store

main :: Warp.Port -> IO ()
main port = do
    state <- STM.newTMVarIO mempty
    printf "Starting server on port %d\n" port
    Warp.run port
        . Logger.logStdoutDev -- XXX switch to logStdout later
        . Server.serve (Proxy :: Proxy API.API)
        $ endpoints state

endpoints :: Store.MutState -> Server.Server API.API
endpoints mut = createV0 mut :<|> undefined :<|> undefined :<|> streamV0 mut

createV0 :: Store.MutState -> Server.Handler API.StoreId
createV0 = undefined
    -- TODO: look into random words? uuid? for this.. words are nice because they're share-able

streamV0 :: Store.MutState -> API.StoreId -> API.ClientId -> SourceT.SourceT IO API.AppData -> Server.Handler (SourceT.SourceT IO API.ServerMessage)
streamV0 mut store client incoming
    = liftIO . Async.withAsync (receiveBroadcastStream mut store client incoming) $ \bcast -> do
        resp <- generateResponseStream mut store client
        return $ SourceT.mapStepT (manage bcast) resp
  where
    -- On each step, poll the broadcast thread to see if it is finished.
    manage async step = SourceT.Effect $ do
        -- FIXME: make this execute on each step?
        print =<< Async.poll async
        return step

-- | Generate a response stream with a backlog followed by live updates for the
-- client.
generateResponseStream :: Store.MutState -> API.StoreId -> API.ClientId -> IO (SourceT.SourceT IO API.ServerMessage)
generateResponseStream mut store client
    = STM.atomically
        . Store.modifyTMVar mut
        $ Store.modifyStore (with responseStream) store
  where
    responseStream storeVal = do
        backlog <- return $ Store.backlog client storeVal
        live <- Store.listen client storeVal
        return (uncurry API.Update <$> backlog <> live)
    -- Make sure x is returned alongside the result of applying it to f.
    with f x = f x >>= return . (x,)

-- | Receive a stream by logging and broadcasting every update.
receiveBroadcastStream :: Store.MutState -> API.StoreId -> API.ClientId -> SourceT.SourceT IO API.AppData -> IO ()
receiveBroadcastStream mut store client incoming
    = SourceT.foreach
        (\err -> putStrLn $ "[ERROR] Error in client stream: " <> err)
        (\update -> STM.atomically
            . Store.modifyTMVar_ mut
            $ Store.mapStore (broadcast update) store)
        incoming
  where
    broadcast update storeVal
        = Store.broadcast client update
        . Store.log client update
        $ storeVal
