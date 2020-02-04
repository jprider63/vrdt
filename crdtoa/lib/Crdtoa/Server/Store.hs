{-# LANGUAGE TupleSections #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# OPTIONS_GHC -Wno-orphans #-} -- to define Show for TChan
module Crdtoa.Server.Store where

import Control.Concurrent.STM (STM)
import Servant.Types.SourceT (SourceT)
import qualified Control.Concurrent.STM as STM hiding (STM)
import qualified Data.Map as Map
import qualified Servant.Types.SourceT as SourceT hiding (SourceT)

import qualified Crdtoa.API as API

-- * Data model

type MutState = STM.TMVar State

type State = Map.Map API.StoreId Store
data Store = Store
    { logs :: Map.Map API.ClientId [API.AppData]
    , chan :: STM.TChan (API.ClientId, API.AppData)
    }

emptyStore :: STM Store
emptyStore = Store
    <$> return Map.empty
    <*> STM.newTChan

-- * State functions

-- | Fetch a store, apply the function, and return the modified state. The user
-- function may modify the contents and/or return a digest value. This works
-- well with 'modifyTMVar'.
--
-- If the store doesn't exist yet, it will be created. Since a new channel is
-- created as part of a new store, it's inadvisable to use this to only return
-- a digest value. Doing so likely isn't what you want, since such a digest may
-- hold a reference to the dangling channel. Always use this as part of
-- modifying state.
--
-- XXX: consider changing this to take MutState instead of having the disclaimer
modifyStore :: (Store -> STM (Store, b)) -> API.StoreId -> State -> STM (State, b)
modifyStore f store state = do
    (a, b) <- maybe (f =<< emptyStore) f $ Map.lookup store state
    return (Map.insert store a state, b)

-- | Fetch a store, apply the function, and return the modified state. The user
-- function may only modify the contents. This works well with 'modifyTMVar_'.
mapStore :: (Store -> STM Store) -> API.StoreId -> State -> STM State
mapStore f store state = Map.alterF go store state
  where
    -- create empty where there's Nothing and after operating wrap with Maybe
    go = fmap Just . maybe (f =<< emptyStore) f

-- * Store functions

-- ** Sending

-- | Apply an update to a store's log. Listeners who reconnect will receive
-- this via 'backlog'.
--
-- XXX: logs are in reverse order .. do we care?
log :: API.ClientId -> API.AppData -> Store -> Store
log client update store@Store{logs} = store{logs = Map.alter go client logs }
  where
    -- create empty where there's Nothing and after operating wrap with Maybe
    go = Just . maybe [update] (update:)

-- | Send an update on a store's channel. Current listeners will receive this
-- via 'listen'.
--
-- This is actually a side effect, but we return the store as though it wasn't.
broadcast :: API.ClientId -> API.AppData -> Store -> STM Store
broadcast client update store@Store{chan} = do
    STM.writeTChan chan (client, update)
    return store

-- ** Receiving

-- | Get the portion of the logs relevant to a recently reconnected client.
--
-- 1. Remove logs from this client.
-- 1. Pair each remaining update with its sender.
-- 1. Convert to a 'Servant.SourceT'.
backlog :: API.ClientId -> Store -> SourceT m (API.ClientId, API.AppData)
backlog client Store{logs} = SourceT.source . concatMap mkPairs . Map.toList . Map.delete client $ logs
  where
    mkPairs (sender, sent) = (sender,) <$> sent

-- | Get a source of broadcast messages for a connected client.
--
-- 1. Duplicate the existing channel, to receive broadcasts.
-- 1. Convert to a StepT and then a SourceT
-- 1. Apply a filter function that removes values not relevant to this client.
listen :: API.ClientId -> Store -> STM (SourceT IO (API.ClientId, API.AppData))
listen client Store{chan} = do
    broadcastChan <- STM.dupTChan chan
    return . SourceT.mapMaybe notOwn . SourceT.fromStepT . tchanStepT $ broadcastChan
  where
    notOwn pair@(sender, _)
        | client == sender = Nothing
        | otherwise = Just pair

-- * Integrations

-- | Emit elements from an 'STM.TChan' channel to a 'SourecT.StepT' stream.
--
-- FIXME: what are the stopping semantics of TChan that we could use here? See
-- 33f4e9a for the last version of this that caught exceptions to emit Stop.
tchanStepT :: STM.TChan a -> SourceT.StepT IO a
tchanStepT c = SourceT.Effect $ do
    v <- STM.atomically $ STM.readTChan c
    return $ SourceT.Yield v (tchanStepT c)

-- * Extensions to STM

-- | Take, apply, and put. The user function may modify the contents and/or
-- return a digest value. This will block when empty.
modifyTMVar :: STM.TMVar a -> (a -> STM (a, b)) -> STM b
modifyTMVar v f = do
    (a, b) <- f =<< STM.takeTMVar v
    STM.putTMVar v a
    return b

-- | Take, apply, and put. The user function may only modify the contents. This
-- will block when empty.
modifyTMVar_ :: STM.TMVar a -> (a -> STM a) -> STM ()
modifyTMVar_ v f = STM.putTMVar v =<< f =<< STM.takeTMVar v

-- | Take, apply, and put. The user function may only return a digest value.
-- This will block when empty.
queryTMVar :: STM.TMVar a -> (a -> STM b) -> STM b
queryTMVar v f = STM.readTMVar v >>= f

instance Show (STM.TChan a) where
    show _ = "TChan ?"
