{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaDI where

import VRDT.TwoPMap.LemmaID
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




{-@ lawCommutativityDIE :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapInsert k2 v2) == applyTwoPMap (applyTwoPMap x (TwoPMapInsert k2 v2)) (TwoPMapDelete k1)) )} @-}
lawCommutativityDIE :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> v -> ()
lawCommutativityDIE x k k' v' = lawCommutativityID x k' v' k


{-@ lawCommutativityDIC :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => (compatibleStateTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapInsert k2 v2))} @-}
lawCommutativityDIC :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> v -> ()
lawCommutativityDIC x@(TwoPMap m p t) k' k v
    | k == k' = (applyTwoPMap x (TwoPMapDelete k')
                 === TwoPMap (Map.delete k' m) (Map.delete k' p) (Set.insert k' t)
                 *** QED)
                &&& lemmaLookupDelete m k'
    | k /= k' = lemmaLookupDelete2 m k k' 
                &&& ((applyTwoPMap x (TwoPMapDelete k')
                === TwoPMap (Map.delete k' m) (Map.delete k' p) (Set.insert k' t)
                *** QED))

{-@ lawCommutativityDI :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapDelete k1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapDelete k1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapInsert k2 v2) == applyTwoPMap (applyTwoPMap x (TwoPMapInsert k2 v2)) (TwoPMapDelete k1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapDelete k1)) (TwoPMapInsert k2 v2))} @-}
lawCommutativityDI :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> k -> v -> ()
lawCommutativityDI a b c d = lawCommutativityDIC a b c d &&& lawCommutativityDIE a b c d
