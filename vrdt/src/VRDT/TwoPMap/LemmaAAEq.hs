{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaAAEq where

import VRDT.TwoPMap.Internal
import VRDT.Class
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
import           VRDT.Class.Proof

{-@ lemmaAllCompatibleInsert :: (Ord (Operation a), VRDT a) => ops:[Operation a] -> v0:Operation a -> v1:Operation a -> {(allCompatible' v0 ops && allCompatible' v1 ops && compatible v0 v1) => allCompatible' v0 (insertList v1 ops)} @-}
lemmaAllCompatibleInsert :: (Ord (Operation a), VRDT a) => [Operation a] -> Operation a -> Operation a -> ()
lemmaAllCompatibleInsert = undefined

{-@ lawCommutativityAAEq :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapApply k1 vop2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapApply k1 vop2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapApply k1 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop2)) (TwoPMapApply k1 vop1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapApply k1 vop2))} @-}
lawCommutativityAAEq :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> Operation v -> ()
lawCommutativityAAEq x@(TwoPMap m p t) k vop vop'
  | not (compatibleTwoPMap op1 op2
  && compatibleStateTwoPMap x op1
  && compatibleStateTwoPMap x op2)
  = ()
  | Set.member k t
  = ()
  | Just vv <- Map.lookup k m
  = let vv_vop = apply vv vop
        vv_vop' = apply vv vop' in
      VRDT.Class.lawCommutativity vv vop vop' &&&
      lemmaInsertTwice k (apply vv_vop vop') vv_vop m &&&
      lemmaInsertTwice k (apply vv_vop' vop) vv_vop' m &&&
      lemmaLookupInsert m k vv_vop &&&
      lemmaLookupInsert m k vv_vop' &&&
      ()
  | Nothing <- Map.lookup k m
  , Nothing <- Map.lookup k p
  =    compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k vop)) (TwoPMapApply k vop')
  ==. compatibleStateTwoPMap (TwoPMap m1 p1 t1) (TwoPMapApply k vop')
      ? lemmaInsertPendingTwice k vop vop' p
      ? lemmaLookupInsert p k l0
      ? lemmaLookupInsert p k l1
      ? lawCompatibilityCommutativity vop' vop
  ==. allCompatible (vop':l0)
  ==. allCompatible (vop':[vop])
  ==. compatible vop' vop
  *** QED
  | Nothing <- Map.lookup k m
  , Just ops <- Map.lookup k p
  =   compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k vop)) (TwoPMapApply k vop')
  ==. compatibleStateTwoPMap (TwoPMap m1 p1 t1) (TwoPMapApply k vop')
      ? lemmaInsertPendingTwice k vop vop' p
      ? lemmaLookupInsert p k l0
      ? lemmaLookupInsert p k l1
      ? lawCompatibilityCommutativity vop' vop
      ? lemmaAllCompatibleInsert ops vop' vop
  ==. allCompatible (vop':l0)
  ==. allCompatible (vop':insertList vop ops)
  ==. allCompatible' vop' (insertList vop ops)

  *** QED
  | otherwise = undefined
  where l0 = case Map.lookup k p of
               Nothing -> [vop]
               Just ops -> insertList vop ops
        l1 = case Map.lookup k p of
               Nothing -> [vop']
               Just ops -> insertList vop' ops
        op1 = TwoPMapApply k vop
        op2 = TwoPMapApply k vop'
        TwoPMap m1 p1 t1 = applyTwoPMap x op1


-- -- ok


-- -- ok
-- -- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
