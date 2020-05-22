{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaAD where

import VRDT.TwoPMap.Internal
import VRDT.Class
import VRDT.Class.Proof
import Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Liquid.Data.List
import qualified Liquid.Data.List as List
import           Data.Set (Set)
import qualified Data.Set as Set
import           Liquid.Data.Map.Props
import           Liquid.ProofCombinators
import VRDT.Internal
import           Prelude hiding (Maybe(..), isJust, maybe, foldr, flip, const)
import           Liquid.Data.Maybe

{-@ lawCommutativityAD :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> k2:k -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapDelete k2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapDelete k2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapDelete k2) == applyTwoPMap (applyTwoPMap x (TwoPMapDelete k2)) (TwoPMapApply k1 vop1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapDelete k2))} @-}
lawCommutativityAD :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> k -> ()
lawCommutativityAD x@(TwoPMap m p t) k vop k'
  | not (Set.member k t)
  , k /= k'
  , compatibleTwoPMap op1 op2
  , Just v1 <- Map.lookup k m
  = lemmaInsertDelete k (apply v1 vop) k' m
  ? lemmaLookupDelete2 m k k'
  ?  assert (not (Set.member k (Set.insert k' t)))
  | not (Set.member k t)
  , k /= k'
  , compatibleTwoPMap op1 op2
  , Nothing <- Map.lookup k m
  =  lemmaLookupDelete2 p k k'
  ?  lemmaLookupDelete2 m k k'
  ?  lemmaInsertDelete k l k' p
  ?  assert (not (isJust (Map.lookup k (Map.delete k' m))))
  ?  assert (not (Set.member k (Set.insert k' t)))
  | not (Set.member k t)
  , k == k'
  , compatibleTwoPMap op1 op2
  , Nothing <- Map.lookup k m
  = lemmaDeleteInsert k l p
  ? assert (Set.member k (Set.insert k' t))
  | not (Set.member k t)
  , k == k'
  , compatibleTwoPMap op1 op2
  , Just v1 <- Map.lookup k m
  = lemmaDeleteInsert k (apply v1 vop) m
  ? assert (Set.member k (Set.insert k' t))
  | Set.member k t
  = Set.member k (twoPMapTombstone (applyTwoPMap x op2)) *** QED
  where op1 = TwoPMapApply k vop
        op2 = TwoPMapDelete k'
        l = case Map.lookup k p of
              Nothing -> [vop]
              Just ops -> insertList vop ops
