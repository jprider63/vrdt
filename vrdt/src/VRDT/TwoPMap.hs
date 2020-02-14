{-@ LIQUID "--reflection" @-}

module VRDT.TwoPMap where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Maybe
import Data.Set (Set)
import qualified Data.Set as Set

import VRDT.Class


-- Keys are (ClientId, NextId)?

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

instance (VRDT v, Ord k) => VRDT (TwoPMap k v) where
    type Operation (TwoPMap k v) = TwoPMapOp k v

    enabled (TwoPMap m p t) (TwoPMapInsert k v) = 
        let pendingEnabled = case Map.lookup k p of
              Nothing ->
                True
              Just ops ->
                -- Each pending op must be enabled.
                snd $ foldr (\op (v, acc) -> (apply v op, acc && enabled v op)) (v, True) ops
        in
        not (Map.member k m || Set.member k t) && pendingEnabled
    enabled (TwoPMap m _p t) (TwoPMapApply k op) = case Map.lookup k m of
        Nothing ->
            -- JP: What do we do here? Just return True and then require Insert to be enabled for all pending?
            True
        Just v ->
            enabled v op
    enabled (TwoPMap m _p t) (TwoPMapDelete k) = True
    
    apply (TwoPMap m p t) (TwoPMapInsert k v) = 
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
    apply (TwoPMap m p t) (TwoPMapApply k op) = 
        -- Check if deleted.
        if Set.member k t then
            TwoPMap m p t
        else
            let (updatedM, m') = Map.updateLookupWithKey (\_ v -> Just $ apply v op) k m in
            
            -- Add to pending if not inserted.
            let p' = if isJust updatedM then p else Map.insertWith (++) k [op] p in

            TwoPMap m' p' t
    apply (TwoPMap m p t) (TwoPMapDelete k) =
        let m' = Map.delete k m in
        let p' = Map.delete k p in
        let t' = Set.insert k t in
        TwoPMap m' p' t'

    lawCommutativity _ _ _ = ()
    
    

