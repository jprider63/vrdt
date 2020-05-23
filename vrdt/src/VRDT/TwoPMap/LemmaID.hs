{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaID where

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


{-@ lawCommutativityID :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> k2:k -> {(compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapDelete k2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapDelete k2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapDelete k2) == applyTwoPMap (applyTwoPMap x (TwoPMapDelete k2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapDelete k2))} @-}
lawCommutativityID :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> k -> ()
lawCommutativityID x@(TwoPMap m p t) k v k'
  | not (Set.member k t)
  , k /= k'
  , Nothing <- Map.lookup k p
  =   lemmaLookupDelete2 m k k'
  &&& lemmaLookupDelete2 p k k'
  &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) Nothing) k' m
  &&& lemmaDelete k k' p
  &&& assert (not (Set.member k (Set.insert k' t)))
  | not (Set.member k t)
  , k /= k'
  , Just xx <- Map.lookup k p
  =   lemmaLookupDelete2 m k k'
  &&& lemmaLookupDelete2 p k k'
  &&& lemmaInsertDelete k (maybe v (foldr (flip apply) v) (Just xx)) k' m
  &&& lemmaDelete k k' p
  &&& assert (not (Set.member k (Set.insert k' t)))
  | not (Set.member k t)
  , k == k'
  , Nothing <- Map.lookup k p
  = lemmaDeleteInsert k v' m
  ? lemmaDeleteTwice k p
  ? assert (Set.member k (Set.insert k' t))
  | not (Set.member k t)
  , k == k'
  , Just xx <- Map.lookup k p
  = ()
  ? lemmaDeleteInsert k (maybe v (foldr (flip apply) v) (Just xx))   m
  ? lemmaDeleteTwice k p
  ? assert (Set.member k (Set.insert k' t))
  | Set.member k t
  = Set.member k (Set.insert k' t)
  *** QED
  where v' = maybe v (foldr (flip apply) v) (Map.lookup k p)
