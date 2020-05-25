{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaAA where

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
import VRDT.TwoPMap.LemmaAAEq
import VRDT.TwoPMap.LemmaAANeq
{-@ lawCommutativityAA :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> k2:k -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapApply k1 vop1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapApply k2 vop2))} @-}
lawCommutativityAA :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> k -> Operation v -> ()
lawCommutativityAA x@(TwoPMap m p t) k vop k' vop'
  | k == k' = lawCommutativityAAEq x k vop vop'
  | otherwise = lawCommutativityAANeq x k vop k' vop'

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
