{-@ LIQUID "--reflection" @-}

module VRDT.TwoPMap where

import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set

import VRDT.Class

-- TODO: LWWMap Map k (t,v)


-- Keys are (ClientId, NextId)?

-- Two phase map (inserted and deleted).
data TwoPMap k v = TwoPMap {
    twoPMap :: Map.Map k v
  , twoPMapTombstone :: Set k
  }

data TwoPMapOp k v = 
    TwoPMapInsert k v
  | TwoPMapApply k (Operation v)
  | TwoPMapDelete k

instance (VRDT v, Ord k) => VRDT (TwoPMap k v) where
    type Operation (TwoPMap k v) = TwoPMapOp k v

    enabled (TwoPMap m t) (TwoPMapInsert k _v) = not $ Map.member k m || Set.member k t
    enabled (TwoPMap m t) (TwoPMapApply k _op) = Map.member k m || Set.member k t -- JP: This requires causal causal consistency. Can't apply an operation until it's inserted. 
    enabled (TwoPMap m t) (TwoPMapDelete k) = True
    
    apply (TwoPMap m t) (TwoPMapInsert k v) = 
        if Set.member k t then
            TwoPMap m t
        else
            let m' = Map.insert k v m in
            TwoPMap m' t
    apply (TwoPMap m t) (TwoPMapApply k op) = 
        let m' = Map.adjust (\v -> apply v op) k m in
        TwoPMap m' t
    apply (TwoPMap m t) (TwoPMapDelete k) =
        let m' = Map.delete k m in
        let t' = Set.insert k t in
        TwoPMap m' t'

    lawCommutativity _ _ _ = ()
    
    

