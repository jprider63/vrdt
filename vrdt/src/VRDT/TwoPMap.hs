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
import           Liquid.Data.List
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
instance (VRDT v, Ord k, Ord (Operation v)) => VRDT (TwoPMap k v) where
    type Operation (TwoPMap k v) = TwoPMapOp k v

    compatible = error "TODO"
    apply = applyTwoPMap
--     lawCommutativity _ _ _ = ()

instance (Ord k, VRDT v, Ord (Operation v)) => VRDTInitial (TwoPMap k v) where
    initVRDT = TwoPMap mempty mempty mempty
    
instance (Aeson.ToJSON k, Aeson.ToJSON v, Aeson.ToJSON (Operation v)) => Aeson.ToJSON (TwoPMapOp k v)
instance (Aeson.FromJSON k, Aeson.FromJSON v, Aeson.FromJSON (Operation v)) => Aeson.FromJSON (TwoPMapOp k v)
#endif


instance (Ord k, Ord (Operation v), VRDT v) => VRDT (TwoPMap k v) where
  type Operation (TwoPMap k v) = TwoPMapOp k v
  apply x op = applyTwoPMap x op
  compatible x y = compatibleTwoPMap x y
  lawCommutativity x op1 op2 = VRDT.TwoPMap.lawCommutativity x op1 op2
  lawCompatibilityCommutativity op1 op2 = lawCompatibilityCommutativity op1 op2

{-@ reflect compatibleTwoPMap @-}
compatibleTwoPMap :: (Eq k, VRDT v) => TwoPMapOp k v -> TwoPMapOp k v -> Bool
compatibleTwoPMap (TwoPMapInsert k v) (TwoPMapInsert k' v') | k == k' = False
compatibleTwoPMap (TwoPMapApply k op) (TwoPMapApply k' op') | k == k' = compatible op op'
compatibleTwoPMap _                   _                               = True


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

{-@ reflect flip @-}
flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

{-@ reflect aupdate @-}
aupdate :: (t -> t1 -> a) -> t1 -> p -> t -> Maybe a
aupdate apply op _ v = Just (apply v op)

{-@ ple updateAupdateEqSize  @-}
{-@ updateAupdateEqSize :: Ord k => apply: (a -> b -> a) -> op:b -> k:k -> m:Map k a ->
  {Map.keys m == Map.keys (msnd (Map.updateLookupWithKey (aupdate apply op) k m))} @-}
updateAupdateEqSize :: Ord k => (a -> b -> a) -> b -> k -> Map k a -> ()
updateAupdateEqSize apply op k m
  | Just x <- Map.lookup k m  = assert (isJust (aupdate apply op k x)) `cast`
                                assert (isJust (Map.mfst (Map.updateLookupWithKey (aupdate apply op) k m)))
  | Nothing <- Map.lookup k m = ()


{-@ reflect const @-}
const :: a -> b -> a
const x _ = x

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
        let (opsM, p') = Map.updateLookupWithKey (const $ const Nothing) k p in
        let v' = maybe v (foldr (flip apply) v) opsM in -- $ Map.lookup k p in
        -- let p' = Map.delete k p in

        let m' = Map.insert k v' m in
        TwoPMap m' p' t
applyTwoPMap (TwoPMap m p t) (TwoPMapApply k op) = 
    -- Check if deleted.
    if Set.member k t then
        TwoPMap m p t
    else
        let (updatedM, m') = updateAupdateEqSize apply op k m `cast`
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

{-@ ple lawCommutativity @-}
{-@ lawCommutativity :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> op1 : TwoPMapOp k v -> op2 : TwoPMapOp k v -> {(compatibleTwoPMap op1 op2) => applyTwoPMap (applyTwoPMap x op1) op2 == applyTwoPMap (applyTwoPMap x op2) op1} @-}
lawCommutativity :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
-- lawCommutativity (TwoPMap m p t) (TwoPMapDelete k) (TwoPMapDelete k') =
--     lemmaDelete k k' m
--   ? lemmaDelete k k' p
--   ? (Set.insert k' (Set.insert k t) === Set.insert k (Set.insert k' t))
-- lawCommutativity x@(TwoPMap m p t) (TwoPMapApply k op) op2
--   | Set.member k t
--   = Set.member k (twoPMapTombstone (applyTwoPMap x op2)) `cast` ()
-- lawCommutativity x@(TwoPMap m p t) op2 (TwoPMapApply k op)
--   | Set.member k t
--   = Set.member k (twoPMapTombstone (applyTwoPMap x op2)) `cast` ()

-- apply/apply, k == k'

-- lawCommutativity (TwoPMap m p t) (TwoPMapApply k op) (TwoPMapApply k' op')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k == k'
--   , not (compatible op op')
--   = ()
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

-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   = lemmaInsertPendingTwice k vop vop' p

-- apply/apply, k /= k'
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

-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   , Nothing <- Map.lookup k' m
--   = lemmaLookupInsert2 m k' k (apply v1 vop)

-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
--   | not (Set.member k t)
--   , not (Set.member k' t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Nothing <- Map.lookup k m
--   , Just v2 <- Map.lookup k' m
--   = lemmaLookupInsert2 m k k' (apply v2 vop')

-- apply/delete k/=k'


-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k /= k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaInsertDelete k (apply v1 vop) k' m
--   ? lemmaLookupDelete2 m k k'
--   ?  assert (not (Set.member k (Set.insert k' t)))

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

-- apply/delete k==k'

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

-- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapDelete k')
--   | not (Set.member k t)
--   , k == k'
--   , compatibleTwoPMap op1 op2
--   , Just v1 <- Map.lookup k m
--   = lemmaDeleteInsert k (apply v1 vop) m
--   ? assert (Set.member k (Set.insert k' t))



lawCommutativity _ _ _
  = ()

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


{-@ ple lawCompatibilityCommutativity' @-}
{-@ lawCompatibilityCommutativity' :: (Eq k, Ord (Operation v), VRDT v) => op1:TwoPMapOp k v -> op2:TwoPMapOp k v -> {compatibleTwoPMap op1 op2 = compatibleTwoPMap op2 op1} @-}
lawCompatibilityCommutativity' :: (Eq k, Ord (Operation v), VRDT v) => TwoPMapOp k v -> TwoPMapOp k v -> ()
lawCompatibilityCommutativity' (TwoPMapInsert k v) (TwoPMapInsert k' v') | k == k' = ()
lawCompatibilityCommutativity' (TwoPMapApply k op) (TwoPMapApply k' op') | k == k' = lawCompatibilityCommutativity op op'
lawCompatibilityCommutativity' _ _ = ()

