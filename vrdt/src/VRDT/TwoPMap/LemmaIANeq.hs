{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaIANeq where

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




{-@ lawCommutativityIANeq :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> {k2:k | k1 /= k2} -> {vop2:Operation v | True} -> {  (compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2)) => ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2))} @-}
lawCommutativityIANeq :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> k -> Operation v -> ()
lawCommutativityIANeq x@(TwoPMap m p t) k v k' vop'
  | not (compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2)
  = ()
  | Set.member k t
  = compatibleStateTwoPMap x op2 *** QED
  | Set.member k' t
  , Nothing <- Map.lookup k p
  = (Set.member k' (twoPMapTombstone (applyTwoPMap x op1)) *** QED)
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==.  applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
    &&& lemmaLookupInsert2 m k' k v1
  | Set.member k' t
  , Just _ <- Map.lookup k p
  = (Set.member k' (twoPMapTombstone (applyTwoPMap x op1)) *** QED)
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ==.  applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
    &&& lemmaLookupInsert2 m k' k v1
    &&& lemmaLookupDelete2 p k' k
  | Nothing <- Map.lookup k p
  , Nothing <- Map.lookup k' m
  =        lemmaDelete k k' p
        &&& lemmaLookupInsert2 m k' k v1
        &&& lemmaLookupInsert2 p k k' l2
        &&& lemmaLookupDelete2 p k' k
        &&& lemmaInsertDelete k' l2 k p
        &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
        ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
        ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
        *** QED
        )
  | Just xx <- Map.lookup k p
  , Nothing <- Map.lookup k' m
  =   
            lemmaDelete k k' p
        &&& lemmaLookupInsert2 m k' k v1
        &&& lemmaLookupInsert2 p k k' l2
        &&& lemmaLookupDelete2 p k' k
        &&& lemmaInsertDelete k' l2 k p
        &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
        ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
        ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
        *** QED
        )
  | Just xx <- Map.lookup k p
  , Just vv <- Map.lookup k' m
  =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
          v2 = apply vv vop' in
            lemmaLookupInsert2 m k' k v1
        &&& lemmaLookupInsert2 m k k' v2
        &&& lemmaLookupDelete2 p k' k
        &&& lemmaInsert k v1 k' v2 m
        &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) (TwoPMapApply k' vop')
        ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) (Map.delete k p) t
        ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) (Map.delete k p)  t
        ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
        *** QED
        )
  | Nothing <- Map.lookup k p
  , Just vv <- Map.lookup k' m
  =   let v1 = maybe v (foldr (flip apply) v) Nothing
          v2 = apply vv vop' in
            lemmaLookupInsert2 m k' k v1
        &&& lemmaLookupInsert2 m k k' v2
        &&& lemmaLookupDelete2 p k' k
        &&& lemmaInsert k v1 k' v2 m
        &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
        ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) p t
        ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) p  t
        ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
        *** QED
        )
  where op1 = TwoPMapInsert k v
        op2 = TwoPMapApply k' vop'
        v1 = maybe v (foldr (flip apply) v) (Map.lookup k p)
        l2 = case Map.lookup k' p of
                 Nothing -> [vop']
                 Just ops -> insertList vop' ops 
