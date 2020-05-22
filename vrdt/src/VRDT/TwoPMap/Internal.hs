{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

{-# LANGUAGE UndecidableInstances #-}

module VRDT.TwoPMap.Internal where

-- #define NotCheckAll True

#if NotLiquid
import qualified Data.Aeson as Aeson
import           Data.Maybe
import           Data.Map (Map)
import qualified Data.Map as Map
#else
import           Liquid.Data.Maybe
import           Liquid.Data.List
import qualified Liquid.Data.List as List
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           VRDT.Class.Proof
import           Prelude hiding (Maybe(..), isJust, maybe, foldr, flip, const)
#endif

import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics

import           Liquid.Data.Map.Props
import           VRDT.Class
import           VRDT.Internal
import           Liquid.ProofCombinators
import           ProofCombinators

-- Keys are typically UniqueId (ClientId, NextId).

-- Two phase map (inserted and deleted).
{-@ data TwoPMap k v = TwoPMap {
    twoPMap :: Map.Map k v
  , twoPMapPending :: Map k [Operation v]
  , twoPMapTombstone :: Set k
}
@-}
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
#ifdef NotLiquid
  deriving (Generic)
#endif
{-@ measure isInsert @-}
isInsert :: TwoPMapOp k v -> Bool
isInsert (TwoPMapInsert _ _) = True
isInsert _ = False

{-@ measure isDelete @-}
isDelete :: TwoPMapOp k v -> Bool
isDelete (TwoPMapDelete _) = True
isDelete _ = False

{-@ measure isDelete @-}
isApply :: TwoPMapOp k v -> Bool
isApply (TwoPMapApply _ _) = True
isApply _ = False

{-
-- Bad version 1. 
-- Doesn't allow you to delete and insert safely.

compatible :: TwoPMapOp k v -> TwoPMapOp k v -> Bool
compatible (TwoPMapDelete k') (TwoPMapInsert k v) 
  | k == k'   = False
  | otherwise = True
compatible (TwoPMapInsert k v) (TwoPMapDelete k') 
  | k == k'   = True
  | otherwise = True
compatible (TwoPMapInsert k v) (TwoPMapInsert k' v') | k == k'   = False
compatible (TwoPMapInsert k v) (TwoPMapInsert k' v') | otherwise = True
compatible (TwoPMapDelete k)   (TwoPMapDelete k')                = True

apply (TwoPMap m p t) (TwoPMapInsert k v) = TwoPMap (Map.insert k v m) p t

-- Good version.


apply (TwoPMap m p t) (TwoPMapInsert k v) 
  | Set.member k t = TwoPMap m p t
  | otherwise = TwoPMap (Map.insert k v m) p t
-}


#if NotLiquid
instance (Ord k, VRDT v, Ord (Operation v)) => VRDTInitial (TwoPMap k v) where
    initVRDT = TwoPMap mempty mempty mempty
    
instance (Aeson.ToJSON k, Aeson.ToJSON v, Aeson.ToJSON (Operation v)) => Aeson.ToJSON (TwoPMapOp k v)
instance (Aeson.FromJSON k, Aeson.FromJSON v, Aeson.FromJSON (Operation v)) => Aeson.FromJSON (TwoPMapOp k v)
#endif


{-@ reflect compatibleTwoPMap @-}
compatibleTwoPMap :: (Eq k, VRDT v) => TwoPMapOp k v -> TwoPMapOp k v -> Bool
compatibleTwoPMap (TwoPMapInsert k v) (TwoPMapInsert k' v') | k == k' = False
compatibleTwoPMap (TwoPMapInsert k v) (TwoPMapApply k' vop') | k == k' = compatibleState v vop'
compatibleTwoPMap (TwoPMapApply k' vop') (TwoPMapInsert k v) | k == k' = compatibleState v vop'
compatibleTwoPMap (TwoPMapApply k op) (TwoPMapApply k' op') | k == k' = compatible op op'
compatibleTwoPMap _                   _                               = True


{-@ reflect compatibleStateTwoPMap @-}
compatibleStateTwoPMap :: (Ord k, VRDT v) => TwoPMap k v -> TwoPMapOp k v -> Bool
compatibleStateTwoPMap (TwoPMap m p t) (TwoPMapInsert k' v)
  | Nothing <- Map.lookup k' m
  = case Map.lookup k' p of
    Nothing -> True
    Just ps -> allCompatibleState v ps
  | otherwise
  = False
compatibleStateTwoPMap (TwoPMap m p t) (TwoPMapApply k vo)
  | Just v <- Map.lookup k m
  = compatibleState v vo
  | Just ops <- Map.lookup k p
  = allCompatible (vo:ops)
  | otherwise
  = True
compatibleStateTwoPMap  _ _ = True
-- {-@ reflect enabledTwoPMap @-}
-- enabledTwoPMap :: (VRDT v, Ord k) => TwoPMap k v -> TwoPMapOp k v -> Bool
-- enabledTwoPMap (TwoPMap m p t) (TwoPMapInsert k v) = 
--     let pendingEnabled = case Map.lookup k p of
--           Nothing ->
--             True
--           Just ops ->
--             -- Each pending op must be enabledTwoPMap.
--             snd $ foldr (\op (v, acc) -> (apply v op, acc && enabled v op)) (v, True) ops
--     in
--     not (Map.member k m) && pendingEnabled
-- enabledTwoPMap (TwoPMap m _p t) (TwoPMapApply k op) = case Map.lookup k m of
--     Nothing ->
--         -- JP: What do we do here? Just return True and then require Insert to be enabledTwoPMap for all pending?
--         True
--     Just v ->
--         enabled v op
-- enabledTwoPMap (TwoPMap m _p t) (TwoPMapDelete k) = True

#ifndef NotLiquid
{-@ reflect flip @-}
flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x
#endif

{-@ reflect aupdate @-}
aupdate :: (t -> t1 -> a) -> t1 -> p -> t -> Maybe a
aupdate apply op _ v = Just (apply v op)

{-@ ple updateAupdateEqSize  @-}
{-@ updateAupdateEqSize :: Ord k => apply: (a -> b -> a) -> op:b -> k:k -> m:Map k a ->
  {Map.keys m == Map.keys (msnd (Map.updateLookupWithKey (aupdate apply op) k m))} @-}
updateAupdateEqSize :: Ord k => (a -> b -> a) -> b -> k -> Map k a -> ()
#if NotLiquid
updateAupdateEqSize apply op k m = ()
#else
updateAupdateEqSize apply op k m
  | Just x <- Map.lookup k m  = assert (isJust (aupdate apply op k x)) `cast`
                                assert (isJust (Map.mfst (Map.updateLookupWithKey (aupdate apply op) k m)))
  | Nothing <- Map.lookup k m = ()
#endif

{-@ lemmaUpdateNothing :: Ord k => k:k -> m:Map k v ->
   {(mfst (Map.updateLookupWithKey doubleConstNothing k m) == Map.lookup k m) &&
    (msnd (Map.updateLookupWithKey doubleConstNothing k m) == Map.delete k m)} @-}
lemmaUpdateNothing :: Ord k => k -> Map k v -> ()
lemmaUpdateNothing _ _ = undefined

#ifndef NotLiquid
{-@ reflect const @-}
const :: a -> b -> a
const x _ = x
#endif

{-@ reflect doubleConstNothing @-}
doubleConstNothing :: a -> b -> Maybe c
doubleConstNothing _ _ = Nothing

{-@ reflect applyTwoPMap @-}
{-@ applyTwoPMap :: (Ord k, Ord (Operation v), VRDT v) => x:TwoPMap k v ->
   op:TwoPMapOp k v -> {vv:TwoPMap k v |
     Set.isSubsetOf (twoPMapTombstone x) (twoPMapTombstone vv)
  && (not (isDelete op) => Set.isSubsetOf (Map.keys (twoPMap x)) (Map.keys (twoPMap vv)))} @-}
applyTwoPMap :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMap k v
applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v) = 
    -- Check if deleted.
    if Set.member k t then
        TwoPMap m p t
    else
        -- Apply pending operations.
        let (opsM, p') = Map.updateLookupWithKey doubleConstNothing k p in
        let v' = maybe v (foldr (flip apply) v) opsM in -- $ Map.lookup k p in
        -- let p' = Map.delete k p in

        let m' = Map.insert k v' m in
        TwoPMap m' p' t
applyTwoPMap (TwoPMap m p t) (TwoPMapApply k op) = 
    -- Check if deleted.
    if Set.member k t then
        TwoPMap m p t
    else
        let (updatedM, m') =
#ifndef NotLiquid
              updateAupdateEqSize apply op k m `cast`
#endif
              Map.updateLookupWithKey (aupdate apply op) k m in
        
        -- Add to pending if not inserted.
        let p' = if isJust updatedM then p else insertPending k op p in

        TwoPMap m' p' t
applyTwoPMap (TwoPMap m p t) (TwoPMapDelete k) =
    let m' = Map.delete k m in
    let p' = Map.delete k p in
    let t' = Set.insert k t in
    TwoPMap m' p' t'