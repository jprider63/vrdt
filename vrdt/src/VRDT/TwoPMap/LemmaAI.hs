{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaAI where

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
import           VRDT.TwoPMap.LemmaIA



{-@ lawCommutativityAIC :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  =>  compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapInsert k2 v2)} @-}
lawCommutativityAIC :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> k -> v -> ()
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
  , Nothing <- Map.lookup k p
  =   compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k vop')) op2
  === compatibleStateTwoPMap (TwoPMap m1 p1 t1) (TwoPMapInsert k v)
    ? lemmaLookupInsert p k l1
  === allCompatibleState v l1
  === allCompatibleState v [vop']
  === compatibleState v vop'
  === True
  *** QED
  | k == k'
  , not (Set.member k' t)
  , Nothing <- Map.lookup k m
  , Just ops <- Map.lookup k p
  =  ()  
  | k /= k'
  , Just vv <- Map.lookup k' m
  = lemmaLookupInsert2 m k k' (apply vv vop')
  &&& lemmaLookupInsert2 p k k' l1
  | otherwise
  = lemmaLookupInsert2 p k k' l1
  where op2 = TwoPMapInsert k v
        op1 = TwoPMapApply k' vop'
        TwoPMap m1 p1 t1 = applyTwoPMap x op1
        l1 = case Map.lookup k' p of
               Nothing -> [vop']
               Just ops -> insertList vop' ops


{-@ lawCommutativityAI :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> vop1:Operation v -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapApply k1 vop1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapApply k1 vop1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapInsert k2 v2) == applyTwoPMap (applyTwoPMap x (TwoPMapInsert k2 v2)) (TwoPMapApply k1 vop1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapApply k1 vop1)) (TwoPMapInsert k2 v2))} @-}
lawCommutativityAI :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> Operation v -> k -> v -> ()
lawCommutativityAI x@(TwoPMap m p t) k' vop' k v = lawCommutativityIA x k v k' vop' &&& lawCommutativityAIC x k' vop' k v
