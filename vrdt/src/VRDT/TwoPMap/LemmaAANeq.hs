{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaAANeq where

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

{-@ lawCommutativityAANeq :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> {k2:k | k1 /= k2} -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapApply k1 vop1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapApply k2 vop2))} @-}
lawCommutativityAANeq :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> k -> Operation v -> ()
lawCommutativityAANeq x@(TwoPMap m p t) k vop k' vop'
  | not (compatibleTwoPMap op1 op2
  && compatibleStateTwoPMap x op1
  && compatibleStateTwoPMap x op2)
  = ()
  | Set.member k t
  = ()
  | Set.member k' t
  , Nothing <- Map.lookup k m
  = lemmaLookupInsert2 p k' k l0
  | Set.member k' t
  , Just vv <- Map.lookup k m
  = (m1 === Map.insert k (apply vv vop) m *** QED)
  ? lemmaLookupInsert2 m k' k (apply vv vop)
  | Nothing <- Map.lookup k m
  , Nothing <- Map.lookup k' m
  = lemmaInsert k l0 k' l1 p
  ? lemmaLookupInsert2 p k k' l1
  ? lemmaLookupInsert2 p k' k l0
  | Just v1 <- Map.lookup k m
  , Just v2 <- Map.lookup k' m
  = lemmaInsert k (apply v1 vop) k' (apply v2 vop') m
  &&& lemmaLookupDelete2 p k' k
  ? lemmaLookupInsert2 m k k' (apply v2 vop')
  ? lemmaLookupInsert2 m k' k (apply v1 vop)
  | Just v1 <- Map.lookup k m
  , Nothing <- Map.lookup k' m
  = lemmaLookupInsert2 m k' k (apply v1 vop)
  &&& lemmaLookupDelete2 p k' k
  | Nothing <- Map.lookup k m
  , Just v2 <- Map.lookup k' m
  = lemmaLookupInsert2 m k k' (apply v2 vop')
  where l0 = case Map.lookup k p of
               Nothing -> [vop]
               Just ops -> insertList vop ops
        l1 = case Map.lookup k' p of
               Nothing -> [vop']
               Just ops -> insertList vop' ops
        op1 = TwoPMapApply k vop
        op2 = TwoPMapApply k' vop'
        TwoPMap m1 p1 t1 = applyTwoPMap x op1


-- -- ok
-- -- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
-- --   | not (Set.member k t)
-- --   , not (Set.member k' t)
-- --   , k == k'
-- --   , compatibleTwoPMap op1 op2
-- --   , Just vv <- Map.lookup k m
-- --   = let vv_vop = apply vv vop
-- --         vv_vop' = apply vv vop' in
-- --       VRDT.Class.lawCommutativity vv vop vop' `cast`
-- --       lemmaInsertTwice k (apply vv_vop vop') vv_vop m `cast`
-- --       lemmaInsertTwice k (apply vv_vop' vop) vv_vop' m `cast`
-- --       lemmaLookupInsert m k vv_vop `cast`
-- --       lemmaLookupInsert m k vv_vop' `cast`
-- --       ()


-- -- ok
-- -- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapApply k vop) op2@(TwoPMapApply k' vop')
-- --   | not (Set.member k t)
-- --   , not (Set.member k' t)
-- --   , k == k'
-- --   , compatibleTwoPMap op1 op2
-- --   , Nothing <- Map.lookup k m
-- --   = lemmaInsertPendingTwice k vop vop' p
