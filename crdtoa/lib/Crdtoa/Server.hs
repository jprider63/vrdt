{-# LANGUAGE TupleSections #-}
module Crdtoa.Server where

import Control.Monad.IO.Class (liftIO)
import Servant (Proxy(..), (:<|>)(..), NoContent(..))
import Text.Printf (printf)
import qualified Control.Concurrent.Chan as Chan
import qualified Control.Concurrent.MVar as MVar
import qualified Control.Exception as Exc
import qualified Data.Map as Map
import qualified Network.Wai.Handler.Warp as Warp
import qualified Network.Wai.Middleware.RequestLogger as Logger
import qualified Servant.Server as Server
import qualified Servant.Types.SourceT as SourceT

import qualified Crdtoa.API as API

main :: Warp.Port -> IO ()
main port = do
    state <- MVar.newMVar mempty
    printf "Starting server on port %d\n" port
    Warp.run port
        . Logger.logStdoutDev -- XXX switch to logStdout later
        . Server.serve (Proxy :: Proxy API.API)
        $ endpoints state

-- TODO: when reusing this code for different incompatible API versions, make
-- sure to namespace stores under their namespaces
--
-- TOOD: switch to STM instead
type MutState = MVar.MVar State
type State = Map.Map API.StoreId Store
type Store = (Map.Map API.ClientId [API.AppData], Chan.Chan API.AppData)
emptyStore :: IO Store
emptyStore = return . (mempty,) =<< Chan.newChan

endpoints :: MutState -> Server.Server API.API
endpoints state = createV0 state :<|> sendV0 state :<|> listenV0 state

-- TODO: when reusing this for v1, make sure to namespace to a different set of
-- stores
createV0 :: MutState -> Server.Handler API.StoreId
createV0 = undefined
    -- TODO: look into random words? uuid? for this.. words are nice because they're share-able

sendV0 :: MutState -> API.StoreId -> API.AppData -> Server.Handler Servant.NoContent
sendV0 mut store update = do
    -- FIXME: get a real client id (maybe use a hash of ip?)
    let client = API.ClientId "foo"
    -- XXX: consider doing `evaluate . force`
    liftIO . MVar.modifyMVar_ mut $ \state -> do
        -- TODO: extract pure domain functions from this
        -- "fetch or create store"
        (logs_, chan) <- maybe emptyStore return $ Map.lookup store state
        -- XXX: logs are in reverse order .. do we care?
        -- "append or create-append log"
        let logs = Map.alter (pure . maybe mempty (update:)) client logs_
        -- "send on the channel for current listeners"
        Chan.writeChan chan update
        -- "put the modified store back"
        return $ Map.insert store (logs, chan) state
    return NoContent

-- | Fetch the store. Duplicate its channel and concatenate all of its old
-- logs. Emit the old logs and the channel contents as a stream to the client.
-- No optimization of the communication is performed, and so the logs sent may
-- be extensive.
--
-- XXX: Race potential: if another thread holds a reference to the channel
-- outside of the MVar and sends on that reference, then this function may miss
-- that element. To remove this potential for a race, use cloneChan in this
-- function.
--
-- XXX: Currently it's not clear how the stream is meant to end, or whether the
-- runtime will correctly GC the channel. Need to read about MVars and GC.
--
-- FIXME: currently this echos from client A back to A,B,C... it shouldn't send
-- back to A .. same goes for the logs, i guess
listenV0 :: MutState -> API.StoreId -> Server.Handler (SourceT.SourceT IO API.AppData)
listenV0 mut store = do
    (updates, chan) <- liftIO . MVar.modifyMVar mut $ \state -> do
        -- "fetch or create store"
        (logs, chan) <- maybe emptyStore return $ Map.lookup store state
        -- "create broadcast chan"
        bChan <- Chan.dupChan chan
        return
            ( Map.insert store (logs, chan) state
            , (concat $ Map.elems logs, bChan)
            )
    return
        $ SourceT.source updates
        <> SourceT.fromStepT (chanStepT chan)

-- | Emit elements from a channel to a stream. If the channel raises
-- 'Exc.BlockedIndefinitelyOnMVar' then the stream will stop.
--
-- XXX: Should that eror be emitted instead?
chanStepT :: Chan.Chan a -> SourceT.StepT IO a
chanStepT c = SourceT.Effect $ action `Exc.catch` handler
  where
    action = do
        v <- Chan.readChan c
        return $ SourceT.Yield v (chanStepT c)
    handler Exc.BlockedIndefinitelyOnMVar = return SourceT.Stop
