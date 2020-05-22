{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaII where

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


{-@ lawCommutativityII :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> k2:k -> v2:v -> {(compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapInsert k2 v2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapInsert k2 v2))  => ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapInsert k2 v2) == applyTwoPMap (applyTwoPMap x (TwoPMapInsert k2 v2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapInsert k2 v2))} @-}
lawCommutativityII :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> k -> v -> ()
lawCommutativityII x@(TwoPMap m p t) k v k' v'
  | not (compatibleTwoPMap op1 op2
  && compatibleStateTwoPMap x op1
  && compatibleStateTwoPMap x op2)
  = ()
  | Set.member k t
  = ()
  | Set.member k' t
  , Nothing <- Map.lookup k p
  = lemmaLookupInsert2 m k' k v1
  | Set.member k' t
  , Just _ <- Map.lookup k p
  =   lemmaLookupInsert2 m k' k v1
  &&& lemmaLookupDelete2 p k' k
  | Nothing <- Map.lookup k p
  , Nothing <- Map.lookup k' p
  =
        lemmaDelete k k' p
    &&& lemmaLookupInsert2 m k k' v2
    &&& lemmaLookupInsert2 m k' k v1
    &&& lemmaInsert k v1 k' v2 m
    &&& lemmaLookupDelete2 p k k'
    &&& lemmaLookupDelete2 p k' k
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
     ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
    ? (not (Map.member k' m))
    ?  (not (Map.member k' (Map.insert k v1 m)))
  | not (Set.member k t)
  , not (Set.member k' t)
  , Just vv1 <- Map.lookup k p
  , Just vv2 <- Map.lookup k' p
  =   let v1 = maybe v (foldr (flip apply) v) (Just vv1)
          v2 = maybe v' (foldr (flip apply) v') (Just vv2) in
        lemmaDelete k k' p
    &&& lemmaLookupInsert2 m k k' v2
    &&& lemmaLookupInsert2 m k' k v1
    &&& lemmaInsert k v1 k' v2 m
    &&& lemmaLookupDelete2 p k k'
    &&& lemmaLookupDelete2 p k' k
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
     ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
    ? (not (Map.member k' m))
    ?  (not (Map.member k' (Map.insert k v1 m)))
  | Just vv1 <- Map.lookup k p
  , Nothing <- Map.lookup k' p
  =   let v1 = maybe v (foldr (flip apply) v) (Just vv1)
          v2 = maybe v' (foldr (flip apply) v') Nothing in
        lemmaDelete k k' p
    &&& lemmaLookupInsert2 m k k' v2
    &&& lemmaLookupInsert2 m k' k v1
    &&& lemmaInsert k v1 k' v2 m
    &&& lemmaLookupDelete2 p k k'
    &&& lemmaLookupDelete2 p k' k
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
     ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
    ? (not (Map.member k' m))
    ?  (not (Map.member k' (Map.insert k v1 m)))
  | Nothing <- Map.lookup k p
  , Just vv2 <- Map.lookup k' p
  =   let v1 = maybe v (foldr (flip apply) v) Nothing
          v2 = maybe v' (foldr (flip apply) v') (Just vv2) in
        lemmaDelete k k' p
    &&& lemmaLookupInsert2 m k k' v2
    &&& lemmaLookupInsert2 m k' k v1
    &&& lemmaInsert k v1 k' v2 m
    &&& lemmaLookupDelete2 p k k'
    &&& lemmaLookupDelete2 p k' k
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==. applyTwoPMap (applyTwoPMap x op2) op1
     ==. TwoPMap (Map.insert k v1 (Map.insert k' v2 m) ) (Map.delete k (Map.delete k' p)) t *** QED)
    ? (not (Map.member k' m))
    ?  (not (Map.member k' (Map.insert k v1 m)))
  where op1 = TwoPMapInsert k v
        op2 = TwoPMapInsert k' v'

        v1 = maybe v (foldr (flip apply) v) (Map.lookup k p)
        v2 = maybe v' (foldr (flip apply) v') (Map.lookup k' p) 
