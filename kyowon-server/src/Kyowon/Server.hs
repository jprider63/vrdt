{-# LANGUAGE TupleSections #-}
module Kyowon.Server where

import Control.Monad.IO.Class (liftIO)
import qualified Data.ByteString.Char8 as BSC
import Servant (Proxy(..), (:<|>)(..), NoContent(..))
import Text.Printf (printf)
import qualified Control.Concurrent.STM as STM
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Middleware.RequestLogger as Logger
import qualified Servant.Server as Server
import qualified Servant.Types.SourceT as SourceT

<<<<<<< HEAD:crdtoa/lib/Crdtoa/Server.hs
import qualified Control.Concurrent.STM.Extras as STME
import qualified Crdtoa.API as API
import qualified Crdtoa.Server.Store as Store

main :: Warp.Port -> IO ()
main port = do
    state <- STM.newTMVarIO mempty
=======
import           Kyowon.API (API)
import qualified Kyowon.API.V0 as API -- JP: For now. Eventually should move things around.
import qualified Kyowon.Types as API -- JP: For now. Eventually should move things around.

-- main :: Warp.Port -> IO ()
-- main port = do
main :: IO ()
main = do
    let port = 3000 -- JP: Parse argv. XXX
    state <- MVar.newMVar mempty
>>>>>>> master:kyowon-server/src/Kyowon/Server.hs
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

<<<<<<< HEAD:crdtoa/lib/Crdtoa/Server.hs
-- | Log and broadcast every update.
sendV0 :: Store.MutState -> API.StoreId -> (API.ClientId, API.AppData) -> Server.Handler NoContent
sendV0 mut store (client, update) = do
    liftIO
        . STM.atomically
        . STME.modifyTMVar_ mut
        $ Store.mapStore broadcast store
=======
sendV0 :: MutState -> API.StoreId -> API.AppData -> Server.Handler Servant.NoContent
sendV0 mut store update = do
    -- -- FIXME: get a real client id
    -- let client = API.ClientId $ BSC.pack "foo"
    -- FIXME: get a real client id (maybe use a hash of ip?)
    let client = API.ClientId $ fromString "foo"
    -- XXX: consider doing `evaluate . force`
    liftIO . MVar.modifyMVar_ mut $ \state -> do
        -- TODO: extract pure domain functions from this
        -- "fetch or create store"
        (logs_, chan) <- maybe emptyStore return $ Map.lookup store state
        -- XXX: logs are in reverse order .. do we care?
        -- "append or create-append log"
        let logs = Map.alter (pure . maybe [update] (update:)) client logs_
        -- "send on the channel for current listeners"
        Chan.writeChan chan update
        -- "put the modified store back"
        return $ Map.insert store (logs, chan) state
>>>>>>> master:kyowon-server/src/Kyowon/Server.hs
    return NoContent
  where
    broadcast storeVal
        = Store.broadcast client update
        . Store.log client update
        $ storeVal
