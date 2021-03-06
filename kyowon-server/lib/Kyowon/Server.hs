{-# LANGUAGE TupleSections #-}
module Kyowon.Server where

import Control.Monad.IO.Class (liftIO)
import Servant (Proxy(..), (:<|>)(..), NoContent(..))
import Text.Printf (printf)
import qualified Control.Concurrent.STM as STM
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Middleware.RequestLogger as Logger
import qualified Servant.Server as Server
import qualified Servant.Types.SourceT as SourceT

import qualified Control.Concurrent.STM.Extras as STME
import qualified Kyowon.Core.API as API
import qualified Kyowon.Server.Store as Store

main :: Warp.Port -> IO ()
main port = do
    state <- STM.newTMVarIO mempty
    printf "Starting server on port %d\n" port
    Warp.run port
        . Logger.logStdoutDev -- XXX switch to logStdout later
        . Server.serve (Proxy :: Proxy API.API)
        $ endpoints state

endpoints :: Store.MutState -> Server.Server API.API
endpoints mut = createV0 mut :<|> sendV0 mut :<|> listenV0 mut

createV0 :: Store.MutState -> Server.Handler API.StoreId
createV0 = undefined
    -- TODO: look into random words? uuid? for this.. words are nice because they're share-able

-- | Generate a response stream with a backlog followed by live updates for the
-- client.
listenV0 :: Store.MutState -> API.StoreId -> API.ClientId -> Server.Handler API.ServerStream
listenV0 mut store client = do
    liftIO
        . STM.atomically
        . STME.modifyTMVar mut
        $ Store.modifyStore (with responseStream) store
  where
    responseStream storeVal = do
        backlog <- return $ Store.backlog client storeVal
        live <- Store.listen client storeVal
        -- concatenate SourceTs and apply Update to the tuples within
        let stream = (uncurry API.Update <$> backlog <> live)
        -- unconditionally prepend the stream with a welcome message to prevent response timeouts
        -- TODO: make the welcome message specify which messages the server has (bloom filter; see Types.hs)
        return $ SourceT.source [API.RequestResendUpdates] <> stream
    -- Apply x to f for the effect. Return x alongside of the result.
    with f x = f x >>= return . (x,)

-- | Log and broadcast every update.
sendV0 :: Store.MutState -> API.StoreId -> (API.ClientId, API.AppData) -> Server.Handler NoContent
sendV0 mut store (client, update) = do
    liftIO
        . STM.atomically
        . STME.modifyTMVar_ mut
        $ Store.mapStore broadcast store
    return NoContent
  where
    broadcast storeVal
        = Store.broadcast client update
        . Store.log client update
        $ storeVal
