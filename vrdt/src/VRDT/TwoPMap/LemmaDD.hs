{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaDD where

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


{-@ lawCommutativityDD :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> {op1:TwoPMapOp k v | op1 = TwoPMapDelete k1} -> k2:k -> {(compatibleTwoPMap op1 (TwoPMapDelete k2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapDelete k2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapDelete k2) == applyTwoPMap (applyTwoPMap x (TwoPMapDelete k2)) (TwoPMapDelete k1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapDelete k2))} @-}
lawCommutativityDD :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> TwoPMapOp k v -> k -> ()
lawCommutativityDD (TwoPMap m p t) k _ k' =
  lemmaDelete k k' m
  ? lemmaDelete k k' p
  ? (Set.insert k' (Set.insert k t) === Set.insert k (Set.insert k' t))
