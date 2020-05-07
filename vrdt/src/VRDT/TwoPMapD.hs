{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

{-# LANGUAGE UndecidableInstances #-}

module VRDT.TwoPMapD where

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
import           Liquid.ProofCombinators

import           VRDT.ClassD


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
enabledTwoPMap :: Ord k => VRDT v -> TwoPMap k v -> TwoPMapOp k v -> Bool
enabledTwoPMap (CVRDT apply enabled lawCommutativity lawNonCausal) (TwoPMap m p t) (TwoPMapInsert k v) = 
    let pendingEnabled = case Map.lookup k p of -- ple can't figure out the value of pendingEnabled 
          Nothing ->
            True
          Just ops ->
            -- Each pending op must be enabledTwoPMap.
            snd $ foldr (\op (v, acc) -> (apply v op, acc && enabled v op)) (v, True) ops
    in
    not (Map.member k m || Set.member k t) && pendingEnabled
enabledTwoPMap (CVRDT apply enabled lawCommutativity lawNonCausal) (TwoPMap m _p t) (TwoPMapApply k op) = case Map.lookup k m of
    Nothing ->
        -- JP: What do we do here? Just return True and then require Insert to be enabledTwoPMap for all pending?
        True
    Just v ->
        enabled v op
enabledTwoPMap (CVRDT apply enabled lawCommutativity lawNonCausal) (TwoPMap m _p t) (TwoPMapDelete k) = True

{-@ reflect applyTwoMapH0 @-}
applyTwoMapH0 :: (b -> c -> b) -> c -> a -> b  -> Maybe b
applyTwoMapH0 apply op _ v = Just $ apply v op

{-@ reflect applyTwoPMap @-}
applyTwoPMap :: Ord k => VRDT v -> TwoPMap k v -> TwoPMapOp k v -> TwoPMap k v
applyTwoPMap (CVRDT apply enabled lawCommutativity lawNonCausal)  (TwoPMap m p t) (TwoPMapInsert k v) = 
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
applyTwoPMap (CVRDT apply enabled lawCommutativity lawNonCausal) (TwoPMap m p t) (TwoPMapApply k op) = 
    -- Check if deleted.
    if Set.member k t then
        TwoPMap m p t
    else
        let (updatedM, m') = Map.updateLookupWithKey (applyTwoMapH0 apply op) k m in
        
        -- Add to pending if not inserted.
        let p' = if isJust updatedM then p else Map.insertWith (++) k [op] p in

        TwoPMap m' p' t
applyTwoPMap (CVRDT apply enabled lawCommutativity lawNonCausal) (TwoPMap m p t) (TwoPMapDelete k) =
    let m' = Map.delete k m in
    let p' = Map.delete k p in
    let t' = Set.insert k t in
    TwoPMap m' p' t'


{-@ ple lawNonCausal @-}
{-@ lawNonCausal :: Ord k =>  d:VRDT v -> x : TwoPMap k v -> {op1 : TwoPMapOp k v | enabledTwoPMap d x op1} -> {op2 : TwoPMapOp k v | enabledTwoPMap d x op2} -> {enabledTwoPMap d (applyTwoPMap d x op1) op2 <=> enabledTwoPMap d (applyTwoPMap d x op2) op1} @-}
lawNonCausal :: Ord k => VRDT v -> TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
-- lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) x (TwoPMapDelete k) (TwoPMapDelete k') = () -- DONE
-- lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) (TwoPMap m p t) _ (TwoPMapInsert k' v') | Set.member k' t  = () -- DONE 
-- lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) (TwoPMap m p t) (TwoPMapInsert k v) _   | Set.member k t  = () -- DONE
-- lawNonCausal d@(CVRDT apply enabled lawCommutativity lawNonCausal) x@(TwoPMap m p t) op1@(TwoPMapDelete k) op2@(TwoPMapInsert k' v')
--   | not (Set.member k' t)
--   ,  (isJust (Map.lookup k' p'))
--   =  ()
--   -- | otherwise
--   -- = ()
--   where m' = Map.delete k m
--         p' = Map.delete k p
--         t' = Set.insert k t         -- SMT error

-- lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) (TwoPMap m p t) (TwoPMapDelete k) (TwoPMapApply k' vop)
--   | Just x <- Map.lookup k' (Map.delete k m)
--   , Just y <- Map.lookup k' m
--   =   x ==! y -- finish up
--   *** QED
--   | otherwise
--   = ()
-- lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) (TwoPMap m p t) (TwoPMapApply k' vop) (TwoPMapDelete k) 
--   | Just x <- Map.lookup k' (Map.delete k m)
--   , Just y <- Map.lookup k' m
--   =   x ==! y -- finish up
--   *** QED
--   | otherwise
--   = ()

lawNonCausal d@(CVRDT apply enabled lawCommutativity lawNonCausal) x@(TwoPMap m p t) op1@(TwoPMapApply k vo) op2@(TwoPMapApply k' vo')
  -- | Set.member k t && Set.member k' t
  -- = ()
  -- | not (Set.member k t) && Set.member k' t
  -- , Nothing <- Map.lookup k m
  -- = ()
  -- | not (Set.member k t) && Set.member k' t
  -- , Just v <- Map.lookup k m
  -- , Just x' <- applyTwoMapH0 apply vo k v
  -- = Map.lookupInsertLemma k' k x' m
  -- | Set.member k t && not (Set.member k' t)
  -- , Just v <- Map.lookup k' m
  -- , Just x' <- applyTwoMapH0 apply vo' k' v
  -- = Map.lookupInsertLemma k k' x' m
  -- | not (Set.member k t) && not (Set.member k' t)
  -- , Just v <- Map.lookup k m
  -- , Just v' <- Map.lookup k' m
  -- , Just x' <- applyTwoMapH0 apply vo k v
  -- , Just x'' <- applyTwoMapH0 apply vo' k' v'
  -- , not (isJust $ Map.lookup k m'') || not (isJust $ Map.lookup k' m')
  -- = Map.lookupInsertLemma k' k x' m 
  -- ? Map.lookupInsertLemma k k' x'' m
  -- | not (Set.member k t) && not (Set.member k' t)
  -- , Just v <- Map.lookup k m
  -- , Just v' <- Map.lookup k' m
  -- , Just x' <- applyTwoMapH0 apply vo k v
  -- , Just x'' <- applyTwoMapH0 apply vo' k' v'
  -- , k' /= k
  -- =  Map.lookupInsertLemma k' k x' m  `cast`
  --    Map.lookupInsertLemma k k' x'' m
  | not (Set.member k t) && not (Set.member k' t)
  , Just v <- Map.lookup k m
  , Just v' <- Map.lookup k' m
  , Just x' <- applyTwoMapH0 apply vo k v
  , Just x'' <- applyTwoMapH0 apply vo' k' v'
  , k' == k
  =  Map.lookupInsertLemma k' k x' m  `cast`
     Map.lookupInsertLemma k k' x'' m
  -- | otherwise
  -- = ()
  where mm0@(TwoPMap m' p' t') = applyTwoPMap d x op1
        mm1@(TwoPMap m'' p'' t'') = applyTwoPMap d x op2


-- lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) x (TwoPMapInsert k v) (TwoPMapInsert k' v') = undefined
-- lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) x (TwoPMapInsert k v) (TwoPMapDelete k') = undefined
-- lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) x (TwoPMapInsert k v) (TwoPMapApply k' vo) = undefined
-- lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) x (TwoPMapApply k vo) (TwoPMapInsert k' v)  = undefined
lawNonCausal (CVRDT apply enabled lawCommutativity lawNonCausal) x _ _ = undefined


    

{-@ ple lawCommutativity @-}
{-@ lawCommutativity :: Ord k => d:VRDT v -> x : TwoPMap k v -> op1 : TwoPMapOp k v -> op2 : TwoPMapOp k v -> {(enabledTwoPMap d x op1 && enabledTwoPMap d x op2  && enabledTwoPMap d (applyTwoPMap d x op1) op2 && enabledTwoPMap d (applyTwoPMap d x op2) op1) => applyTwoPMap d (applyTwoPMap d x op1) op2 == applyTwoPMap d (applyTwoPMap d x op2) op1} @-}
lawCommutativity :: Ord k => VRDT v -> TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
lawCommutativity (CVRDT apply enabled lawCommutativity lawNonCausal) x op1 op2 = undefined


