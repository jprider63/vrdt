{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaDA where

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
import           VRDT.TwoPMap.LemmaAD

{-@ lawCommutativityDAE :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapDelete k1)))} @-}
lawCommutativityDAE :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> Operation v -> ()
lawCommutativityDAE m k' k vop = lawCommutativityAD m k vop k'

{-@ lawCommutativityDAC :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> vop2:Operation v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))  => compatibleStateTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapApply k2 vop2)} @-}
lawCommutativityDAC :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> Operation v -> ()
lawCommutativityDAC x@(TwoPMap m p t) k' k vop
  | k == k' = (applyTwoPMap x (TwoPMapDelete k')
           === TwoPMap (Map.delete k' m) (Map.delete k' p) (Set.insert k' t)
           *** QED)
           &&& lemmaLookupDelete m k
           &&& lemmaLookupDelete p k
  | k /= k' = lemmaLookupDelete2 m k k'
           &&& lemmaLookupDelete2 p k k'
           &&& ((applyTwoPMap x (TwoPMapDelete k')
           === TwoPMap (Map.delete k' m) (Map.delete k' p) (Set.insert k' t)
           *** QED))

lawCommutativityDA x@(TwoPMap m p t) k' k vop =
    lawCommutativityDAC x k' k vop &&& lawCommutativityDAE x k' k vop
