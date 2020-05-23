{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaIAC where

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

{-@ lawCommutativityIAEq' :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k:k -> v1:v -> vop2:Operation v -> {  (compatibleTwoPMap (TwoPMapInsert k v1) (TwoPMapApply k vop2) && compatibleStateTwoPMap x (TwoPMapInsert k v1) && compatibleStateTwoPMap x (TwoPMapApply k vop2)) => compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k v1)) (TwoPMapApply k vop2)} @-}
lawCommutativityIAEq' :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> Operation v -> ()
lawCommutativityIAEq' x@(TwoPMap m p t) k v  vop'
  | not ( (compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2))
  = ()
  | isJust (Map.lookup k m)
  = ()
  | Set.member k t
  = ()
  | Nothing <- Map.lookup k p
  = (applyTwoPMap x op1
  ==. (TwoPMap (Map.insert k (maybe v (foldr (flip apply) v) Nothing) m) p t)
  ==. (TwoPMap (Map.insert k v1 m) p t) *** QED)
  &&& (m1 === Map.insert k v1 m *** QED)
  &&& lemmaLookupInsert m k v1
  | Just ops <- Map.lookup k p
  = ( compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k v)) (TwoPMapApply k vop')
      ? lemmaLookupInsert m k v1
      ? (Map.lookup k m1 ==. Just v1 *** QED)
      ? (v1 ==. foldr (flip apply) v ops *** QED)
      ? lemma0 ops vop' v
  ==. compatibleStateTwoPMap (TwoPMap m1 p1 t1) (TwoPMapApply k vop')
  ==. compatibleState v1 vop'
  ==. compatibleState (foldr (flip apply) v ops) vop'
  *** QED)
  where op1 = TwoPMapInsert k v
        op2 = TwoPMapApply k vop'
        v1 = maybe v (foldr (flip apply) v) (Map.lookup k p)
        TwoPMap m1 p1 t1 = applyTwoPMap x op1


{-@ lemma0 :: (Ord (Operation v), VRDT v) => ops:[Operation v] -> vop:Operation v ->
  {v:v | allCompatibleState v ops && compatibleState v vop && allCompatible' vop ops} ->
  {compatibleState (List.foldr (flip apply) v ops) vop} @-}
lemma0 :: (Ord (Operation v), VRDT v) => [Operation v] -> Operation v -> v -> ()
lemma0 [] _ _ = ()
lemma0 (op:ops) vop v =
        lemma0 ops vop v
      ? lemma0 ops op v
      ? lawCompatibilityCommutativity op vop
      ? lawCommutativity (List.foldr (flip apply) v ops) op vop
      ? lawCommutativity (List.foldr (flip apply) v ops) vop op

