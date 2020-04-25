{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Liquid.Data.Map.Props where 

import qualified Data.Set as S
#ifdef NotLiquid
import Liquid.Data.Map hiding (disjoint)
#else
import Liquid.Data.Map 
#endif NotLiquid
import Liquid.Data.Maybe 
import Liquid.ProofCombinators
import Prelude hiding (Maybe(..), lookup)

-- CPP hacks since `disjoint` doesn't exist in Data.Map for this version and lemmas don't exist for Data.Map.
#ifdef NotLiquid
disjoint :: a -> a -> Bool
disjoint m1 m2 = error "unused"

lemmaDisjoint' :: k -> v -> m k v -> m k v -> ()
lemmaDisjoint' k v m1 m2 = error "unused"

lemmaLookupInsert2 :: m k v -> k -> k -> v -> () 
lemmaLookupInsert2 k v m1 m2 = error "unused"

lemmaInsert :: k -> v -> k -> v -> m k v -> ()
lemmaInsert _ _ _ _ _ = error "unused"
#else

{-@ lemmaDisjoint :: Ord k => k:k -> m1:Map k v -> {m2:Map k v | disjoint m1 m2} -> {member k m1 => not (member k m2)} @-}
lemmaDisjoint :: Ord k => k -> Map k v -> Map k v -> ()
lemmaDisjoint _ _ Tip                                 = ()
lemmaDisjoint k m1 (Map k2 v2 m2) | not (member k m1) = ()
lemmaDisjoint k m1 (Map k2 v2 m2) | otherwise         = lemmaDisjoint k m1 m2


{-@ lemmaDisjoint' :: Ord k => k:k -> v:v -> m1:Map k v -> {m2:Map k v | disjoint m1 m2 && not (member k m2)} -> {disjoint (insert k v m1) m2} @-}
lemmaDisjoint' :: Ord k => k -> v -> Map k v -> Map k v -> ()
lemmaDisjoint' k v m1 m2 | S.member k (keys m2) = assert (not (member k m2)) -- unreachable
lemmaDisjoint' k v m1 m2 = 
        disjoint (insert k v m1) m2
    ==. S.null (S.intersection (keys (insert k v m1)) (keys m2))
    ==. S.null (S.intersection (S.insert k (keys m1)) (keys m2))
    *** QED


{-@ lemmaInsert :: Ord k => k1:k -> v1:v -> k2:k -> v2:v -> m:Map k v
                -> { (k1 /= k2) => (insert k1 v1 (insert k2 v2 m) == insert k2 v2 (insert k1 v1 m)) } @-}
lemmaInsert :: Ord k => k -> v -> k -> v -> Map k v -> ()
lemmaInsert k1 v1 k2 v2 Tip = ()
lemmaInsert k1 v1 k2 v2 (Map k v m) = lemmaInsert k1 v1 k2 v2 m

lemmaLookupInsert2 :: Ord k => Map k v -> k -> k -> v -> () 
{-@ lemmaLookupInsert2 :: Ord k => m:Map k v -> x:k -> k:k -> v:v 
                       -> { (k /= x) => (lookup x (insert k v m) == lookup x m) } @-}
lemmaLookupInsert2  Tip _ _ _ = () 
lemmaLookupInsert2 (Map k _ m)   x k' v
  | k == k'   = lemmaLookupInsert2 m x k' v 
  | otherwise = lemmaLookupInsert2 m x k' v



lemmaLookupInsert :: Ord k => Map k v -> k -> v -> () 
{-@ lemmaLookupInsert :: Ord k => m:Map k v -> k:k -> v:v
  -> {lookup k (insert k v m) == Just v } @-}
lemmaLookupInsert  Tip _ _ = () 
lemmaLookupInsert (Map k _ m)   k' x
  | k == k'   = lemmaLookupInsert m k' x 
  | otherwise = lemmaLookupInsert m k' x


lemmaLookupDelete2 :: Ord k => Map k v -> k ->  k -> () 
{-@ lemmaLookupDelete2 :: Ord k => m:Map k v -> x:k -> kd:k
   -> { (kd /= x => lookup x (delete kd m) == lookup x m) } @-}
lemmaLookupDelete2 Tip _ _        = ()
lemmaLookupDelete2 (Map k v m) x kd
  | k < kd    = lemmaLookupDelete2 m x kd 
  | k == kd   = 
        lookup x (delete kd (Map k v m))
    ==. lookup x m -- JP: Why can't PLE solve this?
    *** QED
        
  | otherwise =
        lookup x (delete kd (Map k v m))
    ==. lookup x (Map k v m) -- JP: Why can't PLE solve this?
    *** QED


lemmaLookupDelete :: Ord k => Map k v -> k -> () 
{-@ lemmaLookupDelete :: Ord k => m:Map k v -> kd:k -> {lookup kd (delete kd m) == Nothing } @-}
lemmaLookupDelete Tip _         = ()
lemmaLookupDelete (Map k v m) kd 
  | k < kd    = lemmaLookupDelete m kd 
  | k == kd   =
        lookup kd (delete kd (Map k v m))
    ==. lookup kd m ?    assert (not (member kd m)) 
                    &&& lemmaNotMemberLookupNothing kd m
    ==. Nothing
    *** QED

  | otherwise =
        lookup kd (delete kd (Map k v m))
    ==. lookup kd (Map k v m) ?   lemmaLessNotMember kd (Map k v m) 
                              &&& lemmaNotMemberLookupNothing kd (Map k v m)
    ==. Nothing
    *** QED

{-@ lemmaLessNotMember :: kd:k -> m:Map {k:k | kd < k} v -> {not (member kd m)} @-}
lemmaLessNotMember :: k -> Map k v -> ()
lemmaLessNotMember _ Tip = ()
lemmaLessNotMember k (Map _ _ m) = lemmaLessNotMember k m

{-@ lemmaNotMemberLookupNothing :: k:k -> {m:Map k v | not (member k m)} -> {lookup k m == Nothing} @-}
lemmaNotMemberLookupNothing :: k -> Map k v -> ()
lemmaNotMemberLookupNothing _ Tip = ()
lemmaNotMemberLookupNothing k (Map _ _ m) = lemmaNotMemberLookupNothing k m

#endif
