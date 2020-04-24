{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Liquid.Data.Map.Props where 

import Liquid.Data.Map 
import Liquid.Data.Maybe 
import Liquid.ProofCombinators
import Prelude hiding (Maybe(..), lookup)


lemmaLookupInsert2 :: Ord k => Map k v -> k -> k -> v -> () 
{-@ lemmaLookupInsert2 :: m:Map k v -> x:k -> k:k -> v:v 
                       -> { (k /= x) => (lookup x (insert k v m) == lookup x m) } @-}
lemmaLookupInsert2  Tip _ _ _ = () 
lemmaLookupInsert2 (Map k _ m)   x k' v
  | k == k'   = lemmaLookupInsert2 m x k' v 
  | otherwise = lemmaLookupInsert2 m x k' v



lemmaLookupInsert :: Ord k => Map k v -> k -> v -> () 
{-@ lemmaLookupInsert :: m:Map k v -> k:k -> v:v
  -> {lookup k (insert k v m) == Just v } @-}
lemmaLookupInsert  Tip _ _ = () 
lemmaLookupInsert (Map k _ m)   k' x
  | k == k'   = lemmaLookupInsert m k' x 
  | otherwise = lemmaLookupInsert m k' x


lemmaLookupDelete2 :: Ord k => Map k v -> k ->  k -> () 
{-@ lemmaLookupDelete2 :: m:Map k v -> x:k -> kd:k
   -> { (kd /= x => lookup x (delete kd m) == lookup x m) } @-}
lemmaLookupDelete2 Tip _ _        = ()
lemmaLookupDelete2 (Map k v m) x kd
  | k < kd    = lemmaLookupDelete2 m x kd 
  | k == kd   = 
        lookup x (delete kd (Map k v m))
    === lookup x m -- JP: Why can't PLE solve this?
    *** QED
        
  | otherwise =
        lookup x (delete kd (Map k v m))
    === lookup x (Map k v m) -- JP: Why can't PLE solve this?
    *** QED


lemmaLookupDelete :: Ord k => Map k v -> k -> () 
{-@ lemmaLookupDelete :: m:Map k v -> kd:k -> {lookup kd (delete kd m) == Nothing } @-}
lemmaLookupDelete Tip _         = ()
lemmaLookupDelete (Map k v m) kd 
  | k < kd    = lemmaLookupDelete m kd 
  | k == kd   =
        lookup kd (delete kd (Map k v m))
    === lookup kd m ?    assert (not (member kd m)) 
                    &&& lemmaNotMemberLookupNothing kd m
    === Nothing
    *** QED

  | otherwise =
        lookup kd (delete kd (Map k v m))
    === lookup kd (Map k v m) ?   lemmaLessNotMember kd (Map k v m) 
                              &&& lemmaNotMemberLookupNothing kd (Map k v m)
    === Nothing
    *** QED

{-@ lemmaLessNotMember :: kd:k -> m:Map {k:k | kd < k} v -> {not (member kd m)} @-}
lemmaLessNotMember :: k -> Map k v -> ()
lemmaLessNotMember _ Tip = ()
lemmaLessNotMember k (Map _ _ m) = lemmaLessNotMember k m

{-@ lemmaNotMemberLookupNothing :: k:k -> {m:Map k v | not (member k m)} -> {lookup k m == Nothing} @-}
lemmaNotMemberLookupNothing :: k -> Map k v -> ()
lemmaNotMemberLookupNothing _ Tip = ()
lemmaNotMemberLookupNothing k (Map _ _ m) = lemmaNotMemberLookupNothing k m
