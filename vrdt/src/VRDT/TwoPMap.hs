{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

{-# LANGUAGE UndecidableInstances #-}

module VRDT.TwoPMap where

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
  deriving (Generic)

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


instance (Ord k, Ord (Operation v), VRDT v) => VRDT (TwoPMap k v) where
  type Operation (TwoPMap k v) = TwoPMapOp k v
  apply x op = applyTwoPMap x op
  compatible x y = compatibleTwoPMap x y
  compatibleState x y = compatibleStateTwoPMap x y
  lawCommutativity x op1 op2 = VRDT.TwoPMap.lawCommutativity x op1 op2
  lawCompatibilityCommutativity op1 op2 = ()

{-@ reflect compatibleTwoPMap @-}
compatibleTwoPMap :: (Eq k, VRDT v) => TwoPMapOp k v -> TwoPMapOp k v -> Bool
compatibleTwoPMap (TwoPMapInsert k v) (TwoPMapInsert k' v') | k == k' = False
compatibleTwoPMap (TwoPMapApply k op) (TwoPMapApply k' op') | k == k' = compatible op op'
compatibleTwoPMap _                   _                               = True


{-@ reflect compatibleStateTwoPMap @-}
compatibleStateTwoPMap :: (Ord k, VRDT v) => TwoPMap k v -> TwoPMapOp k v -> Bool
compatibleStateTwoPMap (TwoPMap m t p) (TwoPMapInsert k' v)
  | Nothing <- Map.lookup k' m
  = True
  | otherwise
  = False
compatibleStateTwoPMap (TwoPMap m t p) (TwoPMapApply k vo)
  | Just v <- Map.lookup k m
  = compatibleState v vo
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

-- {-@ ple lawNonCausal @-}
-- {-@ lawNonCausal :: (Ord k, VRDT v) => x : TwoPMap k v -> {op1 : TwoPMapOp k v | enabledTwoPMap x op1} -> {op2 : TwoPMapOp k v | enabledTwoPMap x op2} -> {enabledTwoPMap (applyTwoPMap x op1) op2 <=> enabledTwoPMap (applyTwoPMap x op2) op1} @-}
-- lawNonCausal :: (Ord k, VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
-- lawNonCausal x (TwoPMapDelete k) op2 = ()
-- lawNonCausal x op1 op2 = ()

--{-@ ple lawCompatTwoPMap @-}
--{-@ lawCompatTwoPMap :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> op1 : TwoPMapOp k v -> op2 : TwoPMapOp k v -> {(compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2) => } @-}

-- {-@ ple lawCommutativity @-}
{-@ lawCommutativity :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> op1 : TwoPMapOp k v -> op2 : TwoPMapOp k v -> {(compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2)  => ((applyTwoPMap (applyTwoPMap x op1) op2 == applyTwoPMap (applyTwoPMap x op2) op1) && compatibleStateTwoPMap (applyTwoPMap x op1) op2)} @-}
lawCommutativity :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
lawCommutativity x op1 op2
  | not (compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2) = ()
lawCommutativity x (TwoPMapInsert k1 v1) (TwoPMapInsert k2 v2) = lawCommutativityII x k1 v1 k2 v2
lawCommutativity x (TwoPMapInsert k1 v1) (TwoPMapApply k2 v2)  = lawCommutativityIA x k1 v1 k2 v2
lawCommutativity x (TwoPMapInsert k1 v1) (TwoPMapDelete k2)    = lawCommutativityID x k1 v1 k2
lawCommutativity x (TwoPMapApply k1 v1)  (TwoPMapInsert k2 v2) = lawCommutativityAI x k1 v1 k2 v2
lawCommutativity x (TwoPMapApply k1 v1)  (TwoPMapApply k2 v2)  = lawCommutativityAA x k1 v1 k2 v2
lawCommutativity x (TwoPMapApply k1 v1)  (TwoPMapDelete k2)    = lawCommutativityAD x k1 v1 k2
lawCommutativity x (TwoPMapDelete k1)  (TwoPMapInsert k2 v2)   = lawCommutativityDI x k1 k2 v2
lawCommutativity x (TwoPMapDelete k1)  (TwoPMapApply k2 v2)    = lawCommutativityDA x k1 k2 v2
lawCommutativity x (TwoPMapDelete k1)  (TwoPMapDelete k2)      = lawCommutativityDD x k1 (TwoPMapDelete k1) k2


{-@ lawCommutativityII :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapInsert k2 v2) == applyTwoPMap (applyTwoPMap x (TwoPMapInsert k2 v2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapInsert k2 v2))} @-}
lawCommutativityII :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> k -> v -> ()

{-@ lawCommutativityIA :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> k2:k -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2))} @-}
lawCommutativityIA :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> k -> Operation v -> ()

{-@ lawCommutativityID :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> k2:k -> {(compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapDelete k2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapDelete k2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapDelete k2) == applyTwoPMap (applyTwoPMap x (TwoPMapDelete k2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapDelete k2))} @-}
lawCommutativityID :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> k -> ()


{-@ lawCommutativityAIC :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  =>  compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapInsert k2 v2)} @-}
lawCommutativityAIC :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> k -> v -> ()

{-@ lawCommutativityAI :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapInsert k2 v2) == applyTwoPMap (applyTwoPMap x (TwoPMapInsert k2 v2)) (TwoPMapApply k1 vop1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapInsert k2 v2))} @-}
lawCommutativityAI :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> k -> v -> ()

{-@ lawCommutativityAA :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> k2:k -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapApply k1 vop1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapApply k2 vop2))} @-}
lawCommutativityAA :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> k -> Operation v -> ()

{-@ lawCommutativityAD :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> k2:k -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapDelete k2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapDelete k2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapDelete k2) == applyTwoPMap (applyTwoPMap x (TwoPMapDelete k2)) (TwoPMapApply k1 vop1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapDelete k2))} @-}
lawCommutativityAD :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> k -> ()

{-@ lawCommutativityDI :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapInsert k2 v2) == applyTwoPMap (applyTwoPMap x (TwoPMapInsert k2 v2)) (TwoPMapDelete k1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapInsert k2 v2))} @-}
lawCommutativityDI :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> v -> ()

{-@ lawCommutativityDA :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapDelete k1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapApply k2 vop2))} @-}
lawCommutativityDA :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> Operation v -> ()

{-@ lawCommutativityDD :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> {op1:TwoPMapOp k v | op1 = TwoPMapDelete k1} -> k2:k -> {(compatibleTwoPMap op1 (TwoPMapDelete k2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapDelete k2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapDelete k2) == applyTwoPMap (applyTwoPMap x (TwoPMapDelete k2)) (TwoPMapDelete k1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapDelete k2))} @-}
lawCommutativityDD :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> TwoPMapOp k v -> k -> ()

#ifdef NotCheckAll 
lawCommutativityII = undefined
lawCommutativityIA = undefined 
lawCommutativityID = undefined 
lawCommutativityAIC = undefined
lawCommutativityAI = undefined
lawCommutativityAA = undefined
lawCommutativityAD = undefined
lawCommutativityDI = undefined
lawCommutativityDA = undefined
lawCommutativityDD = undefined
#else 


-- incompatible (obvious)

-- ok
-- lawCommutativity x op1 op2
--   | not (compatibleTwoPMap op1 op2) || not (compatibleStateTwoPMap x op2) || not (compatibleStateTwoPMap x op1)
--   = ()


-- insert/any incompatible

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2
--   | compatibleStateTwoPMap x op1
--   , isJust (Map.lookup k m)
--   = ()

--ok
-- lawCommutativity x@(TwoPMap m p t) op1 op2@(TwoPMapInsert k' v')
--   | compatibleStateTwoPMap x op2
--   , isJust (Map.lookup k' m)
--   = ()


-- apply/apply, k == k'


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Just vv <- Map.lookup k m
--   = let vv_vop = apply vv vop
--         vv_vop' = apply vv vop' in
--       VRDT.Class.lawCommutativity vv vop vop' `cast`
--       lemmaInsertTwice k (apply vv_vop vop') vv_vop m `cast`
--       lemmaInsertTwice k (apply vv_vop' vop) vv_vop' m `cast`
--       lemmaLookupInsert m k vv_vop `cast`
--       lemmaLookupInsert m k vv_vop' `cast`
--       ()


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   = lemmaInsertPendingTwice k vop vop' p

-- apply/apply, k /= k'
-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   , Nothing <- Map.lookup k' m
--   = lemmaInsert k l0 k' l1 p
--   ? lemmaLookupInsert2 p k k' l1
--   ? lemmaLookupInsert2 p k' k l0
--   where l0 = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops
--         l1 = case Map.lookup k' p of
--                Nothing -> [vop']
--                Just ops -> insertList vop' ops

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   , Just v2 <- Map.lookup k' m
--   = lemmaInsert k (apply v1 vop) k' (apply v2 vop') m
--   ? lemmaLookupInsert2 m k k' (apply v2 vop')
--   ? lemmaLookupInsert2 m k' k (apply v1 vop)


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   , Nothing <- Map.lookup k' m
--   = lemmaLookupInsert2 m k' k (apply v1 vop)


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   , Just v2 <- Map.lookup k' m
--   = lemmaLookupInsert2 m k k' (apply v2 vop')



-- delete/apply tombstone
-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | Set.member k t
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaInsertDelete k (apply v1 vop) k' m
--   ? lemmaLookupDelete2 m k k'
--   ?  assert (Set.member k (Set.insert k' t))

-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | Set.member k t
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   =  lemmaLookupDelete2 p k k'
--   ?  lemmaLookupDelete2 m k k'
--   ?  lemmaInsertDelete k l k' p
--   ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
--   ?  assert ((Set.member k (Set.insert k' t)))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops

-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   =  lemmaLookupDelete2 p k k'
--   ?  lemmaLookupDelete2 m k k'
--   ?  lemmaInsertDelete k l k' p
--   ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
--   ?  assert ( (Set.member k (Set.insert k' t)))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops

--ok
-- lawCommutativity x@(TwoPMap m p t)  op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop)
--   | (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , Nothing <- Map.lookup k m
--   = lemmaDeleteInsert k l p
--   &&&  ((applyTwoPMap (applyTwoPMap x op1) op2
--     ==. applyTwoPMap (TwoPMap m (Map.insert k l p) t) op2
--     ==. (TwoPMap (Map.delete k m) (Map.delete k (Map.insert k l p)) (Set.insert k t)) 

--     ==. applyTwoPMap (TwoPMap m (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (applyTwoPMap x op2) op1) *** QED)
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops  

-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k')  op1@(TwoPMapApply k vop)
--   | Set.member k t
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , Just v1 <- Map.lookup k m
--   = lemmaDeleteInsert k (apply v1 vop) m
--   ? lemmaLookupDelete m k
--   ? assert (Set.member k (Set.insert k' t))
--   &&&  ((applyTwoPMap (applyTwoPMap x op1) op2
--     ==. applyTwoPMap (TwoPMap (Map.insert k (apply v1 vop) m) p t) op2
--     ==. (TwoPMap (Map.delete k (Map.insert k (apply v1 vop) m)) (Map.delete k p) (Set.insert k t))
--     -- ==. (TwoPMap m (Map.delete k p) (Set.insert k t))

--     ==. TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)
--     ==. applyTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (applyTwoPMap x op2) op1) *** QED) &&&
--     (   compatibleStateTwoPMap (applyTwoPMap x op2) op1
--     ==. compatibleStateTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) (TwoPMapApply k vop)
--     *** QED )

-- apply/delete k/=k'

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaInsertDelete k (apply v1 vop) k' m
--   ? lemmaLookupDelete2 m k k'
--   ?  assert (not (Set.member k (Set.insert k' t)))

-- flipped/ok 
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | not (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaInsertDelete k (apply v1 vop) k' m
--   ? lemmaLookupDelete2 m k k'
--   ?  assert (not (Set.member k (Set.insert k' t)))



-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   =  lemmaLookupDelete2 p k k'
--   ?  lemmaLookupDelete2 m k k'
--   ?  lemmaInsertDelete k l k' p
--   ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
--   ?  assert (not (Set.member k (Set.insert k' t)))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop) 
--   | not (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   =  lemmaLookupDelete2 p k k'
--   ?  lemmaLookupDelete2 m k k'
--   ?  lemmaInsertDelete k l k' p
--   ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
--   ?  assert (not (Set.member k (Set.insert k' t)))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops



-- apply/delete k==k'

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   = lemmaDeleteInsert k l p
--   ? assert (Set.member k (Set.insert k' t))
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t)  op2@(TwoPMapDelete k') op1@(TwoPMapApply k vop)
--   | not (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , Nothing <- Map.lookup k m
--   = lemmaDeleteInsert k l p
--   &&&  ((applyTwoPMap (applyTwoPMap x op1) op2
--     ==. applyTwoPMap (TwoPMap m (Map.insert k l p) t) op2
--     ==. (TwoPMap (Map.delete k m) (Map.delete k (Map.insert k l p)) (Set.insert k t)) 

--     ==. applyTwoPMap (TwoPMap m (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (applyTwoPMap x op2) op1) *** QED)
--   where l = case Map.lookup k p of
--                Nothing -> [vop]
--                Just ops -> insertList vop ops  

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaDeleteInsert k (apply v1 vop) m
--   ? assert (Set.member k (Set.insert k' t))

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k')  op1@(TwoPMapApply k vop)
--   | not (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , Just v1 <- Map.lookup k m
--   = lemmaDeleteInsert k (apply v1 vop) m
--   ? lemmaLookupDelete m k
--   ? assert (Set.member k (Set.insert k' t))
--   &&&  ((applyTwoPMap (applyTwoPMap x op1) op2
--     ==. applyTwoPMap (TwoPMap (Map.insert k (apply v1 vop) m) p t) op2
--     ==. (TwoPMap (Map.delete k (Map.insert k (apply v1 vop) m)) (Map.delete k p) (Set.insert k t))
--     -- ==. (TwoPMap m (Map.delete k p) (Set.insert k t))

--     ==. TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)
--     ==. applyTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--     ==. applyTwoPMap (applyTwoPMap x op2) op1) *** QED) &&&
--     (   compatibleStateTwoPMap (applyTwoPMap x op2) op1
--     ==. compatibleStateTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) (TwoPMapApply k vop)
--     *** QED )

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2
--   | Set.member k t
--   = Set.member k (twoPMapTombstone (applyTwoPMap x op2)) `cast` ()

-- delete/insert tombstone

-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | (Set.member k t)
--   , k == k'
--   , Nothing <- Map.lookup k p
--   = lemmaDeleteInsert k v' m
--   ? lemmaDeleteTwice k p
--   ? lemmaDeleteTwice k m
--   &&& lemmaLookupDelete m k
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   &&& (applyTwoPMap (applyTwoPMap x op1) op2
--    ==. applyTwoPMap (TwoPMap (Map.insert k v' m) p t) op2
--    ==. TwoPMap (Map.delete k (Map.insert k v' m)) (Map.delete k p) (Set.insert k t)
--    ==. TwoPMap (Map.delete k (Map.insert k v' m)) p (Set.insert k t)
--    ==. TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)
--    ==. applyTwoPMap (applyTwoPMap x op2) op1
--    *** QED)
--   &&& (compatibleStateTwoPMap (applyTwoPMap x op2) op1
--   === compatibleStateTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--   *** QED)
--   where v' = maybe v (foldr (flip apply) v) Nothing


-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | (Set.member k t)
--   , k == k'
--   , Just xx <- Map.lookup k p
--   = ()
--   ? lemmaDeleteInsert k (maybe v (foldr (flip apply) v) (Just xx))   m
--   ? lemmaDeleteTwice k p
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
--   ? Map.delete k m


-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | Set.member k t
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , compatibleStateTwoPMap x op1
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) Nothing) k' m
--   &&& lemmaDelete k k' p
--   ? (not (Set.member k (Set.insert k' t)))
--   ? (not (Map.member k m))
--   ? (not (Map.member k (Map.delete k' m)))

-- ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v) 
--   | (Set.member k t)
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) (Just xx)) k' m
--   &&& lemmaDelete k k' p
--   ? (not (Set.member k (Set.insert k' t)))
--   ? (not (Map.member k m))
--   ? (not (Map.member k (Map.delete k' m)))



-- insert/delete k==k'

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k == k'
--   , Nothing <- Map.lookup k p
--   = lemmaDeleteInsert k v' m
--   ? lemmaDeleteTwice k p
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   where v' = maybe v (foldr (flip apply) v) Nothing


-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , k == k'
--   , Nothing <- Map.lookup k p
--   = lemmaDeleteInsert k v' m
--   ? lemmaDeleteTwice k p
--   ? lemmaDeleteTwice k m
--   &&& lemmaLookupDelete m k
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   &&& (applyTwoPMap (applyTwoPMap x op1) op2
--    ==. applyTwoPMap (TwoPMap (Map.insert k v' m) p t) op2
--    ==. TwoPMap (Map.delete k (Map.insert k v' m)) (Map.delete k p) (Set.insert k t)
--    ==. TwoPMap (Map.delete k (Map.insert k v' m)) p (Set.insert k t)
--    ==. TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)
--    ==. applyTwoPMap (applyTwoPMap x op2) op1
--    *** QED)
--   &&& (compatibleStateTwoPMap (applyTwoPMap x op2) op1
--   === compatibleStateTwoPMap (TwoPMap (Map.delete k m) (Map.delete k p) (Set.insert k t)) op1
--   *** QED)
--   where v' = maybe v (foldr (flip apply) v) Nothing

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k == k'
--   , Just xx <- Map.lookup k p
--   = ()
--   ? lemmaDeleteInsert k (maybe v (foldr (flip apply) v) (Just xx))   m
--   ? lemmaDeleteTwice k p
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , k == k'
--   , Just xx <- Map.lookup k p
--   = ()
--   ? lemmaDeleteInsert k (maybe v (foldr (flip apply) v) (Just xx))   m
--   ? lemmaDeleteTwice k p
--   ? assert (Set.member k (Set.insert k' t))
--   ? lemmaUpdateNothing k p
--   &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
--   ? Map.delete k m



-- insert/delete k/=k'


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) Nothing) k' m
--   &&& lemmaDelete k k' p
--   &&& assert (not (Set.member k (Set.insert k' t)))

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , compatibleStateTwoPMap x op1
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) Nothing) k' m
--   &&& lemmaDelete k k' p
--   ? (not (Set.member k (Set.insert k' t)))
--   ? (not (Map.member k m))
--   ? (not (Map.member k (Map.delete k' m)))



-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) (Just xx)) k' m
--   &&& lemmaDelete k k' p
--   &&& assert (not (Set.member k (Set.insert k' t)))

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapDelete k') op1@(TwoPMapInsert k v) 
--   | not (Set.member k t)
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   =   lemmaLookupDelete2 m k k'
--   &&& lemmaLookupDelete2 p k k'
--   &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) (Just xx)) k' m
--   &&& lemmaDelete k k' p
--   ? (not (Set.member k (Set.insert k' t)))
--   ? (not (Map.member k m))
--   ? (not (Map.member k (Map.delete k' m)))


-- insert/insert

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapInsert k' v')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , Nothing <- Map.lookup k p
--   , Nothing <- Map.lookup k' p
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           v2 = maybe v' (foldr (flip apply) v') Nothing in
--         lemmaDelete k k' p
--     &&& lemmaLookupInsert2 m k k' v2
--     &&& lemmaLookupInsert2 m k' k v1
--     &&& lemmaInsert k v1 k' v2 m
--     &&& lemmaLookupDelete2 p k k'
--     &&& lemmaLookupDelete2 p k' k
--     &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
--      ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
--     ? (not (Map.member k' m))
--     ?  (not (Map.member k' (Map.insert k v1 m)))
    
-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapInsert k' v')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , Just vv1 <- Map.lookup k p
--   , Just vv2 <- Map.lookup k' p
--   =   let v1 = maybe v (foldr (flip apply) v) (Just vv1)
--           v2 = maybe v' (foldr (flip apply) v') (Just vv2) in
--         lemmaDelete k k' p
--     &&& lemmaLookupInsert2 m k k' v2
--     &&& lemmaLookupInsert2 m k' k v1
--     &&& lemmaInsert k v1 k' v2 m
--     &&& lemmaLookupDelete2 p k k'
--     &&& lemmaLookupDelete2 p k' k
--     &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
--      ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
--     ? (not (Map.member k' m))
--     ?  (not (Map.member k' (Map.insert k v1 m)))


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapInsert k' v')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , Just vv1 <- Map.lookup k p
--   , Nothing <- Map.lookup k' p
--   =   let v1 = maybe v (foldr (flip apply) v) (Just vv1)
--           v2 = maybe v' (foldr (flip apply) v') Nothing in
--         lemmaDelete k k' p
--     &&& lemmaLookupInsert2 m k k' v2
--     &&& lemmaLookupInsert2 m k' k v1
--     &&& lemmaInsert k v1 k' v2 m
--     &&& lemmaLookupDelete2 p k k'
--     &&& lemmaLookupDelete2 p k' k
--     &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
--      ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
--     ? (not (Map.member k' m))
--     ?  (not (Map.member k' (Map.insert k v1 m)))


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapInsert k' v')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k p
--   , Just vv2 <- Map.lookup k' p
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           v2 = maybe v' (foldr (flip apply) v') (Just vv2) in
--         lemmaDelete k k' p
--     &&& lemmaLookupInsert2 m k k' v2
--     &&& lemmaLookupInsert2 m k' k v1
--     &&& lemmaInsert k v1 k' v2 m
--     &&& lemmaLookupDelete2 p k k'
--     &&& lemmaLookupDelete2 p k' k
--     &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
--      ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
--     ? (not (Map.member k' m))
--     ?  (not (Map.member k' (Map.insert k v1 m)))

-- insert/apply

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , Nothing <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           l2 = case Map.lookup k' p of
--                  Nothing -> [vop']
--                  Just ops -> insertList vop' ops 
--           -- Nothing = Map.lookup k (Map.insert k' l2 p)
--           -- Nothing = Map.lookup k' (Map.insert k v1 m) 
--     in
--         (   applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)
--         *** QED
--         )
--         &&& lemmaDelete k k' p
--         &&& lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
--         ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapApply k' vop') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , Nothing <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           l2 = case Map.lookup k' p of
--                  Nothing -> [vop']
--                  Just ops -> insertList vop' ops 
--           -- Nothing = Map.lookup k (Map.insert k' l2 p)
--           -- Nothing = Map.lookup k' (Map.insert k v1 m) 
--     in
--         (   applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)
--         *** QED
--         )
--         &&& lemmaDelete k k' p
--         &&& lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
--         ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   , Nothing <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
--           l2 = case Map.lookup k' p of
--                  Nothing -> [vop']
--                  Just ops -> insertList vop' ops  in
--             lemmaDelete k k' p
--         &&& lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
--         ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )


-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapApply k' vop') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   , Nothing <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
--           l2 = case Map.lookup k' p of
--                  Nothing -> [vop']
--                  Just ops -> insertList vop' ops  in
--             lemmaDelete k k' p
--         &&& lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
--         ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )


-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   , Just vv <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
--           v2 = apply vv vop' in
--             lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 m k k' v2
--         -- &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsert k v1 k' v2 m

--         -- &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) (Map.delete k p) t
--         ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) (Map.delete k p)  t
--         ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )


-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t) op2@(TwoPMapApply k' vop')  op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , compatibleTwoPMap op1 op2
--   , k /= k'
--   , Just xx <- Map.lookup k p
--   , Just vv <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
--           v2 = apply vv vop' in
--             lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 m k k' v2
--         -- &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsert k v1 k' v2 m

--         -- &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) (Map.delete k p) t
--         ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) (Map.delete k p)  t
--         ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )
--         ?  (not (Map.member k m))
--         ?  (not (Map.member k (Map.insert k' v2 m)))

-- ok
-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , Just vv <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           v2 = apply vv vop' in
--             lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 m k k' v2
--         -- &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsert k v1 k' v2 m
--         -- &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) p t
--         ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) p  t
--         ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )

-- flipped/ok
-- lawCommutativity x@(TwoPMap m p t)  op2@(TwoPMapApply k' vop') op1@(TwoPMapInsert k v)
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , k /= k'
--   , Nothing <- Map.lookup k p
--   , Just vv <- Map.lookup k' m
--   =   let v1 = maybe v (foldr (flip apply) v) Nothing
--           v2 = apply vv vop' in
--             lemmaLookupInsert2 m k' k v1
--         &&& lemmaLookupInsert2 m k k' v2
--         -- &&& lemmaLookupInsert2 p k k' l2
--         &&& lemmaLookupDelete2 p k' k
--         &&& lemmaInsert k v1 k' v2 m
--         -- &&& lemmaInsertDelete k' l2 k p
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
--         ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) p t
--         ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) p  t
--         ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         )
--         ?  (not (Map.member k m))
--         ?  (not (Map.member k (Map.insert k' v2 m)))

-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , k == k'
--   , Nothing <- Map.lookup k p
--   =  ( Map.lookup k m === Nothing *** QED) 
--    
--   ? lemmaNotMemberLookupNothing k m
-- 
--    &&&( let v1 = maybe v (foldr (flip apply) v) Nothing
--           -- Just vv = Map.lookup k (Map.insert k v1 m)
--             -- Just vvv = Map.lookup k  (Map.insert k [vop'] p)
--             l2 = case Map.lookup k p of
--                    Nothing -> [vop']
--                    Just ops -> insertList vop' ops  in
--            (maybe v (foldr (flip apply) v) (Just [vop'])
--         ==.  foldr (flip apply) v [vop']
--         ==.  (flip apply) vop' (foldr (flip apply) v [])
--         ==.  (flip apply) vop' v
--         ==.  apply v vop'
--         ***  QED  )
--         -- -- &&& lemmaLookupInsert2 p k k' l2
--         -- -- &&& lemmaLookupDelete2 p k' k
--         -- -- &&& lemmaInsert k v1 k' v2 m
--         -- -- &&& lemmaInsertDelete k' l2 k p
--         &&& (l2 ==. [vop']  *** QED)
--         &&& (Map.lookup k (Map.insert k [vop'] p) ==. Just [vop'] *** QED)
--         &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
--             ? lemmaLookupInsert m k v1
--             ? lemmaLookupInsert p k l2
--             ? (Map.lookup k m ==. Nothing *** QED)
--             ? lemmaDeleteInsert k [vop'] p
--             ? lemmaInsertTwice k (apply v1 vop') v1 m
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
--         ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k vop')
--         ==.  TwoPMap (Map.insert k (apply v1 vop') (Map.insert k v1 m)) p t
--             ? ((Map.insert k (apply v1 vop') (Map.insert k v1 m)) ==. Map.insert k (apply v1 vop')  m *** QED)
--         ==.  TwoPMap (Map.insert k (apply v1 vop') m) p t
--               ? assert (not (Map.member k p))
--             ? (Map.delete k p ==. p *** QED)
--         ==.  TwoPMap (Map.insert k (apply v1 vop') m) (Map.delete k p) t
--         -- ==.  TwoPMap (Map.insert k v1 m) p  t
--         === TwoPMap (Map.insert k (apply v1 vop') m) -- here
--               (Map.delete k p) t
--         ==.  TwoPMap (Map.insert k (maybe v (foldr (flip apply) v) (Just [vop'])) m)
--               (Map.delete k (Map.insert k [vop'] p)) t
--         ===  applyTwoPMap (TwoPMap m (Map.insert k [vop'] p) t) op1 -- here
--         ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
--         *** QED
--         ) -- &&&
--         -- ( applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2 === applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1 *** QED)
--       ) 



-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , compatibleTwoPMap op1 op2
--   , compatibleStateTwoPMap x op1
--   , compatibleStateTwoPMap x op2
--   , k == k'
--   , Nothing <- Map.lookup k p
--   , Just vv <- Map.lookup k m
--   =  assert (not (isJust (Map.lookup k m))) -- let v1 = maybe v (foldr (flip apply) v) Nothing
      --     -- Just vv = Map.lookup k (Map.insert k v1 m)
      --     Just vvv = Map.lookup k  (Map.insert k [vop'] p)
      --     l2 = case Map.lookup k p of
      --            Nothing -> [vop']
      --            Just ops -> insertList vop' ops
      --     v2 = apply vv vop' in
      --       lemmaLookupInsert m k v1
      --   &&& lemmaLookupInsert p k l2
      --   &&& lemmaDeleteInsert k [vop'] p
      --   &&& lemmaInsertTwice k (apply v1 vop') v1 m
      --   &&& (maybe v (foldr (flip apply) v) (Just [vop'])
      --   ==.  foldr (flip apply) v [vop']
      --   ==.  (flip apply) vop' (foldr (flip apply) v [])
      --   ==.  (flip apply) vop' v
      --   ==.  apply v vop'
      --   ***  QED  )
      --   -- &&& lemmaLookupInsert2 p k k' l2
      --   -- &&& lemmaLookupDelete2 p k' k
      --   -- &&& lemmaInsert k v1 k' v2 m
      --   -- &&& lemmaInsertDelete k' l2 k p
      --   &&& (l2 ==. [vop'] ==. vvv *** QED)
      --   &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
      --   ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
      --   ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
      --   ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k vop')
      --   ==.  TwoPMap (Map.insert k (apply v1 vop') (Map.insert k v1 m)) p t
      --   -- ==.  TwoPMap (Map.insert k v1 m) p  t
      --   ==. TwoPMap (Map.insert k (apply v1 vop') m)
      --         (Map.delete k p) t
      --   ==.  TwoPMap (Map.insert k (maybe v (foldr (flip apply) v) Nothing) m)
      --         p t
      --   ==.  applyTwoPMap (TwoPMap (Map.insert k v2 m) p t) op1
      --   ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
      --   *** QED
      --   )


-- upgraded version
  -- ?  (m0' === m1')
  -- ?  (p0' === p1')
  -- ?  (t0' === t1')
  -- where TwoPMap m0 p0 t0 = applyTwoPMap x op1
  --       TwoPMap m1 p1 t1 = applyTwoPMap x op2
  --       TwoPMap m0' p0' t0' = applyTwoPMap (applyTwoPMap x op1) op2
  --       TwoPMap m1' p1' t1' = applyTwoPMap (applyTwoPMap x op2) op1

-- copy paste the following when needed
        -- TwoPMap m0 p0 t0 = applyTwoPMap x op1
        -- TwoPMap m1 p1 t1 = applyTwoPMap x op2
        -- TwoPMap m0' p0' t0' = applyTwoPMap (applyTwoPMap x op1) op2
        -- TwoPMap m1' p1' t1' = applyTwoPMap (applyTwoPMap x op2) op1





{-@ ple lawCommutativityII @-}
lawCommutativityII x@(TwoPMap m p t) k v k' v' = undefined
  -- | not (compatibleTwoPMap op1 op2
  -- && compatibleStateTwoPMap x op1
  -- && compatibleStateTwoPMap x op2)
  -- = ()
  -- | Set.member k t
  -- = ()
  -- | Set.member k' t
  -- , Nothing <- Map.lookup k p
  -- = lemmaLookupInsert2 m k' k v1
  -- | Set.member k' t
  -- , Just _ <- Map.lookup k p
  -- = lemmaLookupInsert2 m k' k v1
  -- , not (Set.member k' t)

  -- , Nothing <- Map.lookup k p
  -- , Nothing <- Map.lookup k' p
  -- =
  --       lemmaDelete k k' p
  --   &&& lemmaLookupInsert2 m k k' v2
  --   &&& lemmaLookupInsert2 m k' k v1
  --   &&& lemmaInsert k v1 k' v2 m
  --   &&& lemmaLookupDelete2 p k k'
  --   &&& lemmaLookupDelete2 p k' k
  --   &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
  --    ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
  --   ? (not (Map.member k' m))
  --   ?  (not (Map.member k' (Map.insert k v1 m)))
  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , Just vv1 <- Map.lookup k p
  -- , Just vv2 <- Map.lookup k' p
  -- =   let v1 = maybe v (foldr (flip apply) v) (Just vv1)
  --         v2 = maybe v' (foldr (flip apply) v') (Just vv2) in
  --       lemmaDelete k k' p
  --   &&& lemmaLookupInsert2 m k k' v2
  --   &&& lemmaLookupInsert2 m k' k v1
  --   &&& lemmaInsert k v1 k' v2 m
  --   &&& lemmaLookupDelete2 p k k'
  --   &&& lemmaLookupDelete2 p k' k
  --   &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
  --    ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
  --   ? (not (Map.member k' m))
  --   ?  (not (Map.member k' (Map.insert k v1 m)))

  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , compatibleTwoPMap op1 op2
  -- , Just vv1 <- Map.lookup k p
  -- , Nothing <- Map.lookup k' p
  -- =   let v1 = maybe v (foldr (flip apply) v) (Just vv1)
  --         v2 = maybe v' (foldr (flip apply) v') Nothing in
  --       lemmaDelete k k' p
  --   &&& lemmaLookupInsert2 m k k' v2
  --   &&& lemmaLookupInsert2 m k' k v1
  --   &&& lemmaInsert k v1 k' v2 m
  --   &&& lemmaLookupDelete2 p k k'
  --   &&& lemmaLookupDelete2 p k' k
  --   &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
  --    ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
  --   ? (not (Map.member k' m))
  --   ?  (not (Map.member k' (Map.insert k v1 m)))
  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , compatibleTwoPMap op1 op2
  -- , Nothing <- Map.lookup k p
  -- , Just vv2 <- Map.lookup k' p
  -- =   let v1 = maybe v (foldr (flip apply) v) Nothing
  --         v2 = maybe v' (foldr (flip apply) v') (Just vv2) in
  --       lemmaDelete k k' p
  --   &&& lemmaLookupInsert2 m k k' v2
  --   &&& lemmaLookupInsert2 m k' k v1
  --   &&& lemmaInsert k v1 k' v2 m
  --   &&& lemmaLookupDelete2 p k k'
  --   &&& lemmaLookupDelete2 p k' k
  --   &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
  --    ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
  --   ? (not (Map.member k' m))
  --   ?  (not (Map.member k' (Map.insert k v1 m)))

  where op1 = TwoPMapInsert k v
        op2 = TwoPMapInsert k' v'

        v1 = maybe v (foldr (flip apply) v) (Map.lookup k p)
        v2 = maybe v' (foldr (flip apply) v') (Map.lookup k' p) 
{-@ ple lawCommutativityIAEq' @-}
{-@ lawCommutativityIAEq' :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k:k -> v1:v -> {vop2:Operation v | (compatibleTwoPMap (TwoPMapInsert k v1) (TwoPMapApply k vop2) && compatibleStateTwoPMap x (TwoPMapInsert k v1) && compatibleStateTwoPMap x (TwoPMapApply k vop2))} -> {  compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k v1)) (TwoPMapApply k vop2)} @-}
lawCommutativityIAEq' :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> Operation v -> ()
lawCommutativityIAEq' x@(TwoPMap m p t) k v  vop'
  | not ( (compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2))
  = ()
  | isJust (Map.lookup k m)
  = ()
  | otherwise
  = ()

  where op1 = TwoPMapInsert k v
        op2 = TwoPMapApply k vop'

{-@ ple lawCommutativityIAEq @-}
{-@ lawCommutativityIAEq :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k:k -> v1:v -> vop2:Operation v -> { (compatibleTwoPMap (TwoPMapInsert k v1) (TwoPMapApply k vop2) && compatibleStateTwoPMap x (TwoPMapInsert k v1) && compatibleStateTwoPMap x (TwoPMapApply k vop2)) => (applyTwoPMap (applyTwoPMap x (TwoPMapInsert k v1)) (TwoPMapApply k vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k vop2)) (TwoPMapInsert k v1))} @-}
lawCommutativityIAEq :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> Operation v -> ()
lawCommutativityIAEq x@(TwoPMap m p t) k v1 vop2
  | not (compatibleTwoPMap (TwoPMapInsert k v1) (TwoPMapApply k vop2)) = ()
  | not (compatibleStateTwoPMap x (TwoPMapInsert k v1)) = ()
  | not (compatibleStateTwoPMap x (TwoPMapApply k vop2)) = ()

  | isJust (Map.lookup k m)
  = undefined -- () -- TODO OK

  | (Set.member k t) 
  = undefined -- () -- TODO OK

  | not (Set.member k t)
  , Nothing <- Map.lookup k p
  = undefined -- TODO
   -- -- OK. Takes 4.5 minues...
   -- ( Map.lookup k m === Nothing *** QED) 
   -- &&&( let v1 = maybe v (foldr (flip apply) v) Nothing
   --        -- Just vv = Map.lookup k (Map.insert k v1 m)
   --          -- Just vvv = Map.lookup k  (Map.insert k [vop'] p)
   --          l2 = case Map.lookup k p of
   --                 Nothing -> [vop']
   --                 Just ops -> insertList vop' ops  in
   --         (maybe v (foldr (flip apply) v) (Just [vop'])
   --      ==.  foldr (flip apply) v [vop']
   --      ==.  (flip apply) vop' (foldr (flip apply) v [])
   --      ==.  (flip apply) vop' v
   --      ==.  apply v vop'
   --      ***  QED  )
   --      -- -- &&& lemmaLookupInsert2 p k k' l2
   --      -- -- &&& lemmaLookupDelete2 p k' k
   --      -- -- &&& lemmaInsert k v1 k' v2 m
   --      -- -- &&& lemmaInsertDelete k' l2 k p
   --      &&& (l2 ==. [vop']  *** QED)
   --      &&& (Map.lookup k (Map.insert k [vop'] p) ==. Just [vop'] *** QED)
   --      &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
   --          ? lemmaLookupInsert m k v1
   --          ? lemmaLookupInsert p k l2
   --          ? (Map.lookup k m ==. Nothing *** QED)
   --          ? lemmaDeleteInsert k [vop'] p
   --          ? lemmaInsertTwice k (apply v1 vop') v1 m
   --      ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
   --      ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
   --      ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k vop')
   --      ==.  TwoPMap (Map.insert k (apply v1 vop') (Map.insert k v1 m)) p t
   --          ? ((Map.insert k (apply v1 vop') (Map.insert k v1 m)) ==. Map.insert k (apply v1 vop')  m *** QED)
   --      ==.  TwoPMap (Map.insert k (apply v1 vop') m) p t
   --            ? assert (not (Map.member k p))
   --          ? (Map.delete k p ==. p *** QED)
   --      ==.  TwoPMap (Map.insert k (apply v1 vop') m) (Map.delete k p) t
   --      -- ==.  TwoPMap (Map.insert k v1 m) p  t
   --      === TwoPMap (Map.insert k (apply v1 vop') m) -- here
   --            (Map.delete k p) t
   --      ==.  TwoPMap (Map.insert k (maybe v (foldr (flip apply) v) (Just [vop'])) m)
   --            (Map.delete k (Map.insert k [vop'] p)) t
   --      ===  applyTwoPMap (TwoPMap m (Map.insert k [vop'] p) t) op1 -- here
   --      ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
   --      *** QED
   --      ) -- &&&
   --      -- ( applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2 === applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1 *** QED)
   --    )
  | not (Set.member k t)
  , Just ops <- Map.lookup k p
  = 
    let v1' = foldr (flip apply) v1 ops in
    let v1'' = apply v1' vop2 in

    let ops2 = insertList vop2 ops in
    let v2' = foldr (flip apply) v1 ops2 in

    (   applyTwoPMap (applyTwoPMap x (TwoPMapInsert k v1)) (TwoPMapApply k vop2) 
    ==! applyTwoPMap (TwoPMap (Map.insert k v1' m) (Map.delete k p) t) (TwoPMapApply k vop2)  -- OK
        ?   lemmaLookupInsert m k v1'
        &&& (Map.lookup k (Map.insert k v1' m) === Just v1' *** QED)
        &&& assert (isJust (Map.lookup k (Map.insert k v1' m)))
    ==! TwoPMap (Map.insert k v1'' m) (Map.delete k p) t -- TODO
        ?   (v1'' ==! v2' *** QED) -- TODO
        &&& (Map.delete k p ==! Map.delete k (Map.insert k ops2 p) *** QED) -- TODO
    === TwoPMap (Map.insert k v2' m) (Map.delete k (Map.insert k ops2 p)) t -- OK
        ?   lemmaLookupInsert p k ops2
    ==! applyTwoPMap (TwoPMap m (Map.insert k ops2 p) t) (TwoPMapInsert k v1) -- OK
    ==! applyTwoPMap (applyTwoPMap x (TwoPMapApply k vop2)) (TwoPMapInsert k v1) -- OK
    *** QED)

  where op1 = TwoPMapInsert k v1
        op2 = TwoPMapApply k vop2


        vop' = vop2
        v = v1

        -- l1 = case Map.lookup k p of
        --        Nothing -> [vop']
        --        Just ops -> insertList vop' ops

{-@ ple lawCommutativityIANeq @-}
{-@ lawCommutativityIANeq :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> {k2:k | k1 /= k2} -> {vop2:Operation v | True} -> {  (compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2)) => ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2))} @-}
lawCommutativityIANeq :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> k -> Operation v -> ()
lawCommutativityIANeq x@(TwoPMap m p t) k v k' vop'
  -- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
  | not (compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2)
  = ()
  | Set.member k t
  = compatibleStateTwoPMap x op2 *** QED
  ? Set.member k (twoPMapTombstone (applyTwoPMap x op2))
  | Set.member k' t
  , Nothing <- Map.lookup k p
  = (Set.member k' (twoPMapTombstone (applyTwoPMap x op1)) *** QED)
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ===  applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
    &&& lemmaLookupInsert2 m k' k v1
  | Set.member k' t
  , Just _ <- Map.lookup k p
  = (Set.member k' (twoPMapTombstone (applyTwoPMap x op1)) *** QED)
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ===  applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
    &&& lemmaLookupInsert2 m k' k v1

  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , Nothing <- Map.lookup k p
  -- , Nothing <- Map.lookup k' m
  -- =        lemmaDelete k k' p
  --       &&& lemmaLookupInsert2 m k' k v1
  --       &&& lemmaLookupInsert2 p k k' l2
  --       &&& lemmaLookupDelete2 p k' k
  --       &&& lemmaInsertDelete k' l2 k p
  --       &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
  --       ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
  --       ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
  --       ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
  --       ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
  --       *** QED
  --       )
  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , Just xx <- Map.lookup k p
  -- , Nothing <- Map.lookup k' m
  -- =   
  --           lemmaDelete k k' p
  --       &&& lemmaLookupInsert2 m k' k v1
  --       &&& lemmaLookupInsert2 p k k' l2
  --       &&& lemmaLookupDelete2 p k' k
  --       &&& lemmaInsertDelete k' l2 k p
  --       &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
  --       ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
  --       ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
  --       ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
  --       ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
  --       *** QED
  --       )
  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , Just xx <- Map.lookup k p
  -- , Just vv <- Map.lookup k' m
  -- =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
  --         v2 = apply vv vop' in
  --           lemmaLookupInsert2 m k' k v1
  --       &&& lemmaLookupInsert2 m k k' v2
  --       -- &&& lemmaLookupInsert2 p k k' l2
  --       &&& lemmaLookupDelete2 p k' k
  --       &&& lemmaInsert k v1 k' v2 m

  --       -- &&& lemmaInsertDelete k' l2 k p
  --       &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
  --       ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) (TwoPMapApply k' vop')
  --       ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) (Map.delete k p) t
  --       ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) (Map.delete k p)  t
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
  --       ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
  --       *** QED
  --       )
  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , Nothing <- Map.lookup k p
  -- , Just vv <- Map.lookup k' m
  -- =   let v1 = maybe v (foldr (flip apply) v) Nothing
  --         v2 = apply vv vop' in
  --           lemmaLookupInsert2 m k' k v1
  --       &&& lemmaLookupInsert2 m k k' v2
  --       -- &&& lemmaLookupInsert2 p k k' l2
  --       &&& lemmaLookupDelete2 p k' k
  --       &&& lemmaInsert k v1 k' v2 m
  --       -- &&& lemmaInsertDelete k' l2 k p
  --       &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
  --       ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
  --       ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) p t
  --       ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) p  t
  --       ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
  --       ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
  --       *** QED
  --       )

  | otherwise = undefined
  where op1 = TwoPMapInsert k v
        op2 = TwoPMapApply k' vop'
        v1 = maybe v (foldr (flip apply) v) (Map.lookup k p)
        l2 = case Map.lookup k' p of
                 Nothing -> [vop']
                 Just ops -> insertList vop' ops 

{-@ ple lawCommutativityIA @-}
-- {-@ lawCommutativityIA :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> k2:k -> {vop2:Operation v | (compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))} -> {  ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2))} @-}

lawCommutativityIA x@(TwoPMap m p t) k v k' vop'
  | not ((compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))) = ()
  | k == k' = lawCommutativityIAEq x k v vop' &&& lawCommutativityIAEq' x k v vop'
  | otherwise = lawCommutativityIANeq x k v k' vop'

  where k1 = k
        k2 = k'
        vop2 = vop'
        v1 = v


-- checked
{-@ ple lawCommutativityID @-}
lawCommutativityID x@(TwoPMap m p t) k v k'
  | not (Set.member k t)
  , k /= k'
  , Nothing <- Map.lookup k p
  =   lemmaLookupDelete2 m k k'
  &&& lemmaLookupDelete2 p k k'
  &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) Nothing) k' m
  &&& lemmaDelete k k' p
  &&& assert (not (Set.member k (Set.insert k' t)))
  | not (Set.member k t)
  , k /= k'
  , Just xx <- Map.lookup k p
  =   lemmaLookupDelete2 m k k'
  &&& lemmaLookupDelete2 p k k'
  &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) (Just xx)) k' m
  &&& lemmaDelete k k' p
  &&& assert (not (Set.member k (Set.insert k' t)))
  | not (Set.member k t)
  , k == k'
  , Nothing <- Map.lookup k p
  = lemmaDeleteInsert k v' m
  ? lemmaDeleteTwice k p
  ? assert (Set.member k (Set.insert k' t))
  ? lemmaUpdateNothing k p
  | not (Set.member k t)
  , k == k'
  , Just xx <- Map.lookup k p
  = ()
  ? lemmaDeleteInsert k (maybe v (foldr (flip apply) v) (Just xx))   m
  ? lemmaDeleteTwice k p
  ? assert (Set.member k (Set.insert k' t))
  ? lemmaUpdateNothing k p
  | Set.member k t
  = Set.member k (Set.insert k' t)
  *** QED
  where v' = maybe v (foldr (flip apply) v) (Map.lookup k p)



{-@ ple lawCommutativityDIE @-}
{-@ lawCommutativityDIE :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapInsert k2 v2) == applyTwoPMap (applyTwoPMap x (TwoPMapInsert k2 v2)) (TwoPMapDelete k1)) )} @-}
lawCommutativityDIE :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> v -> ()
lawCommutativityDIE x k k' v' = lawCommutativityID x k' v' k

{-@ ple lawCommutativityDIC @-}
{-@ lawCommutativityDIC :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => (compatibleStateTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapInsert k2 v2))} @-}
lawCommutativityDIC :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> v -> ()
lawCommutativityDIC x@(TwoPMap m p t) k' k v
    | k == k' = (applyTwoPMap x (TwoPMapDelete k')
                 === TwoPMap (Map.delete k' m) (Map.delete k' p) (Set.insert k' t)
                 *** QED)
                &&& lemmaLookupDelete m k'
    | k /= k' = lemmaLookupDelete2 m k k' 
                &&& ((applyTwoPMap x (TwoPMapDelete k')
                === TwoPMap (Map.delete k' m) (Map.delete k' p) (Set.insert k' t)
                *** QED))


{-@ ple lawCommutativityDI @-}
lawCommutativityDI a b c d = lawCommutativityDIC a b c d &&& lawCommutativityDIE a b c d


{-@ ple lawCommutativityDAE @-}
{-@ lawCommutativityDAE :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapDelete k1)))} @-}
lawCommutativityDAE :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> Operation v -> ()
lawCommutativityDAE m k' k vop = lawCommutativityAD m k vop k'

{-@ ple lawCommutativityDAC @-}
{-@ lawCommutativityDAC :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))  => compatibleStateTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapApply k2 vop2)} @-}
lawCommutativityDAC :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> Operation v -> ()
lawCommutativityDAC x@(TwoPMap m p t) k' k vop
  | k == k' = (applyTwoPMap x (TwoPMapDelete k')
           === TwoPMap (Map.delete k' m) (Map.delete k' p) (Set.insert k' t)
           *** QED)
           &&& lemmaLookupDelete m k
  | k /= k' = lemmaLookupDelete2 m k k' 
              &&& ((applyTwoPMap x (TwoPMapDelete k')
           === TwoPMap (Map.delete k' m) (Map.delete k' p) (Set.insert k' t)
           *** QED))



{-@ ple lawCommutativityDA @-}
lawCommutativityDA x@(TwoPMap m p t) k' k vop =
    lawCommutativityDAC x k' k vop &&& lawCommutativityDAE x k' k vop


{-@ ple lawCommutativityDD @-}
lawCommutativityDD (TwoPMap m p t) k _ k' =
  lemmaDelete k k' m
  ? lemmaDelete k k' p
  ? (Set.insert k' (Set.insert k t) === Set.insert k (Set.insert k' t))
  

{-@ ple lawCommutativityAIC @-}
lawCommutativityAIC x@(TwoPMap m p t) k' vop' k v
  | not ( (compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2))
  = ()
  | Set.member k' t
  = ()
  | k == k'
  , Just _ <- Map.lookup k m
  = ()
  | k == k'
  , not (Set.member k' t)
  , Nothing <- Map.lookup k m
  =  ()
  | k /= k'
  , Just vv <- Map.lookup k' m
  = lemmaLookupInsert2 m k k' (apply vv vop')
  | otherwise
  = ()
  where op2 = TwoPMapInsert k v
        op1 = TwoPMapApply k' vop'
        TwoPMap m1 p1 t1 = applyTwoPMap x op1
        l1 = case Map.lookup k' p of
               Nothing -> [vop']
               Just ops -> insertList vop' ops

{-@ ple lawCommutativityAI @-}
lawCommutativityAI x@(TwoPMap m p t) k' vop' k v = lawCommutativityIA x k v k' vop' &&& lawCommutativityAIC x k' vop' k v
  
-- done
{-@ ple lawCommutativityAA @-}
lawCommutativityAA x@(TwoPMap m p t) k vop k' vop' = undefined
  -- | Set.member k t
  -- = ()
  -- | Set.member k' t
  -- , k == k'
  -- = ()
  -- | Set.member k' t
  -- , k /= k'
  -- , Nothing <- Map.lookup k m
  -- = ()
  -- | Set.member k' t
  -- , k /= k'
  -- , Just vv <- Map.lookup k m
  -- = (m1 === Map.insert k (apply vv vop) m *** QED)
  -- ? lemmaLookupInsert2 m k' k (apply vv vop)
  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , k /= k'
  -- , compatibleTwoPMap op1 op2
  -- , Nothing <- Map.lookup k m
  -- , Nothing <- Map.lookup k' m
  -- = lemmaInsert k l0 k' l1 p
  -- ? lemmaLookupInsert2 p k k' l1
  -- ? lemmaLookupInsert2 p k' k l0
  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , k /= k'
  -- , compatibleTwoPMap op1 op2
  -- , Just v1 <- Map.lookup k m
  -- , Just v2 <- Map.lookup k' m
  -- = lemmaInsert k (apply v1 vop) k' (apply v2 vop') m
  -- ? lemmaLookupInsert2 m k k' (apply v2 vop')
  -- ? lemmaLookupInsert2 m k' k (apply v1 vop)
  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , k /= k'
  -- , compatibleTwoPMap op1 op2
  -- , Just v1 <- Map.lookup k m
  -- , Nothing <- Map.lookup k' m
  -- = lemmaLookupInsert2 m k' k (apply v1 vop)
  -- | not (Set.member k t)
  -- , not (Set.member k' t)
  -- , k /= k'
  -- , compatibleTwoPMap op1 op2
  -- , Nothing <- Map.lookup k m
  -- , Just v2 <- Map.lookup k' m
  -- = lemmaLookupInsert2 m k k' (apply v2 vop')
  where l0 = case Map.lookup k p of
               Nothing -> [vop]
               Just ops -> insertList vop ops
        l1 = case Map.lookup k' p of
               Nothing -> [vop']
               Just ops -> insertList vop' ops
        op1 = TwoPMapApply k vop
        op2 = TwoPMapApply k' vop'
        TwoPMap m1 p1 t1 = applyTwoPMap x op1


-- done
{-@ ple lawCommutativityAD @-}
lawCommutativityAD x@(TwoPMap m p t) k vop k' = ()
  -- | not (Set.member k t)
  -- , k /= k'
  -- , compatibleTwoPMap op1 op2
  -- , Just v1 <- Map.lookup k m
  -- = lemmaInsertDelete k (apply v1 vop) k' m
  -- ? lemmaLookupDelete2 m k k'
  -- ?  assert (not (Set.member k (Set.insert k' t)))
  -- | not (Set.member k t)
  -- , k /= k'
  -- , compatibleTwoPMap op1 op2
  -- , Nothing <- Map.lookup k m
  -- =  lemmaLookupDelete2 p k k'
  -- ?  lemmaLookupDelete2 m k k'
  -- ?  lemmaInsertDelete k l k' p
  -- ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
  -- ?  assert (not (Set.member k (Set.insert k' t)))
  -- | not (Set.member k t)
  -- , k == k'
  -- , compatibleTwoPMap op1 op2
  -- , Nothing <- Map.lookup k m
  -- = lemmaDeleteInsert k l p
  -- ? assert (Set.member k (Set.insert k' t))
  -- | not (Set.member k t)
  -- , k == k'
  -- , compatibleTwoPMap op1 op2
  -- , Just v1 <- Map.lookup k m
  -- = lemmaDeleteInsert k (apply v1 vop) m
  -- ? assert (Set.member k (Set.insert k' t))
  -- | Set.member k t
  -- = Set.member k (twoPMapTombstone (applyTwoPMap x op2)) `cast` ()
  -- where op1 = TwoPMapApply k vop
  --       op2 = TwoPMapDelete k'
  --       l = case Map.lookup k p of
  --             Nothing -> [vop]
  --             Just ops -> insertList vop ops













#endif








{-@ ple lawCompatibilityCommutativity' @-}
{-@ lawCompatibilityCommutativity' :: (Eq k, Ord (Operation v), VRDT v) => op1:TwoPMapOp k v -> op2:TwoPMapOp k v -> {compatibleTwoPMap op1 op2 = compatibleTwoPMap op2 op1} @-}
lawCompatibilityCommutativity' :: (Eq k, Ord (Operation v), VRDT v) => TwoPMapOp k v -> TwoPMapOp k v -> ()
lawCompatibilityCommutativity' (TwoPMapInsert k v) (TwoPMapInsert k' v') | k == k' = ()
lawCompatibilityCommutativity' (TwoPMapApply k op) (TwoPMapApply k' op') | k == k' = lawCompatibilityCommutativity op op'
lawCompatibilityCommutativity' _ _ = ()














{-@ strongConvergence :: (Eq (Operation a), VRDT a) => s0:a -> ops1:[Operation a] -> ops2:[Operation a] -> {(isPermutation ops1 ops2 && allCompatibleState s0 ops1 && allCompatible ops1) => (applyAll s0 ops1 = applyAll s0 ops2)} @-}
strongConvergence :: (Eq (Operation a), VRDT a) => a -> [Operation a] -> [Operation a] -> ()
strongConvergence _ _ _ = undefined -- Proven in VRDT.Class.Proof


{-@ reflect allCompatibleState @-}
{-@ ple allCompatibleState @-}
{-@ allCompatibleState :: VRDT a => x:a -> ops:[Operation a] -> {vv:Bool | (vv && len ops > 0) => allCompatibleState x (List.tail ops)} @-}
allCompatibleState :: VRDT a => a -> [Operation a] -> Bool
allCompatibleState _ [] = True
allCompatibleState x (h:t) = compatibleState x h && allCompatibleState x t

{-@ reflect allCompatible @-}
{-@ ple allCompatible @-}
{-@ allCompatible :: VRDT a => xs:[Operation a] ->
  {vv:Bool | (vv && len xs > 0) => allCompatible (List.tail xs)} @-}
allCompatible :: VRDT a => [Operation a] -> Bool
allCompatible [] = True
allCompatible (op1:ops) = allCompatible' op1 ops

{-@ reflect allCompatible' @-}
allCompatible' :: VRDT a => Operation a -> [Operation a] -> Bool
allCompatible' _  []        = True
-- allCompatible' op (op':ops) = compatible op op' && allCompatible' op ops
-- allCompatible' op (op':ops) = compatible op op' && compatible op' op && allCompatible' op ops && allCompatible' op' ops
allCompatible' op (op':ops) = compatible op op' && allCompatible' op ops && allCompatible' op' ops

{-@ reflect applyAll @-}
applyAll :: VRDT a => a -> [Operation a] -> a
applyAll s []       = s
applyAll s (op:ops) = applyAll (apply s op) ops

{-@ reflect isPermutation @-}
{-@ ple isPermutation @-}
{-@ isPermutation :: Eq o => xs:[o] -> ys:[o] -> {v:Bool | v => len xs == len ys} @-}
isPermutation :: Eq o => [o] -> [o] -> Bool
isPermutation []    []    = True
isPermutation (_:_) []    = False
isPermutation []    (_:_) = False
isPermutation (op1:ops1') ops2 = case removeFirst op1 ops2 of
    Nothing -> False
    Just ops2' -> isPermutation ops1' ops2'

{-@ reflect removeFirst @-}
{-@ ple removeFirst @-}
{-@ removeFirst :: Eq o => x:o -> xs:[o] ->
   {vv:Maybe [o] | (isJust vv => 1 + len (fromJust vv) == len xs) &&
                   (List.elem' x xs => isJust vv)} @-}
removeFirst :: Eq o => o -> [o] -> Maybe [o]
removeFirst o [] = Nothing
removeFirst o (h:t) = 
  if h == o then 
    Just t 
  else 
    -- (h:) <$> removeFirst o t
    case removeFirst o t of
        Nothing -> Nothing
        Just t' -> Just (h:t')



