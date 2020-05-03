{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

{-# LANGUAGE UndecidableInstances #-}

module VRDT.TwoPMap where

#if NotLiquid
import qualified Data.Aeson as Aeson
import           Data.Maybe
import           Data.Map (Map)
import qualified Data.Map as Map
#else
import           Liquid.Data.Maybe
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Prelude hiding (Maybe(..), isJust, maybe)
#endif

import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics

import           VRDT.Class


-- Keys are typically UniqueId (ClientId, NextId).

-- Two phase map (inserted and deleted).
data TwoPMap k v = TwoPMap {
    twoPMap :: Map.Map k v
  , twoPMapPending :: Map k [Operation v] -- ^ Pending operations of v (which hasn't been inserted yet).
  , twoPMapTombstone :: Set k
  }
-- TODO: Invariant that keys are disjoint.

data TwoPMapOp k v = 
    TwoPMapInsert k v
  | TwoPMapApply k (Operation v)
  | TwoPMapDelete k
  deriving (Generic)


-- instance (VRDT v, Ord k) => VRDT (TwoPMap k v) where
--     type Operation (TwoPMap k v) = TwoPMapOp k v
-- 
--     enabled m op = error "TODO"
--     apply m op = error "TODO"
--     lawCommutativity _ _ _ = ()

#if NotLiquid
instance (Ord k, VRDT v) => VRDTInitial (TwoPMap k v) where
    initVRDT = TwoPMap mempty mempty mempty
    
instance (Aeson.ToJSON k, Aeson.ToJSON v, Aeson.ToJSON (Operation v)) => Aeson.ToJSON (TwoPMapOp k v)
instance (Aeson.FromJSON k, Aeson.FromJSON v, Aeson.FromJSON (Operation v)) => Aeson.FromJSON (TwoPMapOp k v)
#endif


{-@ reflect enabledTwoPMap @-}
enabledTwoPMap :: (VRDT v, Ord k) => TwoPMap k v -> TwoPMapOp k v -> Bool
enabledTwoPMap (TwoPMap m p t) (TwoPMapInsert k v) = 
    let pendingEnabled = case Map.lookup k p of
          Nothing ->
            True
          Just ops ->
            -- Each pending op must be enabledTwoPMap.
            snd $ foldr (\op (v, acc) -> (apply v op, acc && enabled v op)) (v, True) ops
    in
    not (Map.member k m || Set.member k t) && pendingEnabled
enabledTwoPMap (TwoPMap m _p t) (TwoPMapApply k op) = case Map.lookup k m of
    Nothing ->
        -- JP: What do we do here? Just return True and then require Insert to be enabledTwoPMap for all pending?
        True
    Just v ->
        enabled v op
enabledTwoPMap (TwoPMap m _p t) (TwoPMapDelete k) = True


{-@ reflect applyTwoPMap @-}
applyTwoPMap :: (VRDT v, Ord k) => TwoPMap k v -> TwoPMapOp k v -> TwoPMap k v
applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v) = 
    -- Check if deleted.
    if Set.member k t then
        TwoPMap m p t
    else
        -- Apply pending operations.
        let (opsM, p') = Map.updateLookupWithKey (const $ const Nothing) k p in
        let v' = maybe v (foldr (\op v -> apply v op) v) opsM in -- $ Map.lookup k p in
        -- let p' = Map.delete k p in

        let m' = Map.insert k v' m in
        TwoPMap m' p' t
applyTwoPMap (TwoPMap m p t) (TwoPMapApply k op) = 
    -- Check if deleted.
    if Set.member k t then
        TwoPMap m p t
    else
        let (updatedM, m') = Map.updateLookupWithKey (\_ v -> Just $ apply v op) k m in
        
        -- Add to pending if not inserted.
        let p' = if isJust updatedM then p else Map.insertWith (++) k [op] p in

        TwoPMap m' p' t
applyTwoPMap (TwoPMap m p t) (TwoPMapDelete k) =
    let m' = Map.delete k m in
    let p' = Map.delete k p in
    let t' = Set.insert k t in
    TwoPMap m' p' t'

{-@ ple lawNonCausal @-}
{-@ lawNonCausal :: (Ord k, VRDT v) => x : TwoPMap k v -> {op1 : TwoPMapOp k v | enabledTwoPMap x op1} -> {op2 : TwoPMapOp k v | enabledTwoPMap x op2} -> {enabledTwoPMap (applyTwoPMap x op1) op2 <=> enabledTwoPMap (applyTwoPMap x op2) op1} @-}
lawNonCausal :: (Ord k, VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
lawNonCausal x (TwoPMapDelete k) op2 = ()
lawNonCausal x op1 op2 = ()

    

{-@ ple lawCommutativity @-}
{-@ lawCommutativity :: (Ord k, VRDT v) => x : TwoPMap k v -> op1 : TwoPMapOp k v -> op2 : TwoPMapOp k v -> {(enabledTwoPMap x op1 && enabledTwoPMap x op2  && enabledTwoPMap (applyTwoPMap x op1) op2 && enabledTwoPMap (applyTwoPMap x op2) op1) => applyTwoPMap (applyTwoPMap x op1) op2 == applyTwoPMap (applyTwoPMap x op2) op1} @-}
lawCommutativity :: (Ord k, VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
lawCommutativity x op1 op2 = ()


