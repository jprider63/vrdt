{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Liquid.Data.Map.Props where 

import Liquid.Data.Map 
import Liquid.Data.Maybe 
import Liquid.ProofCombinators


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
{-@ lemmaLookupDelete2 :: m:Map k v -> x:k -> k:k
   -> { (k /= x => lookup x (delete k m) == lookup x m) } @-}
lemmaLookupDelete2 Tip _ _        = ()
lemmaLookupDelete2 (Map k _ m) x k' 
  | k == k'   = lemmaLookupDelete2 m x k' 
  | otherwise = lemmaLookupDelete2 m x k'


{-@ ple lemmaLookupDelete @-}
lemmaLookupDelete :: Ord k => Map k v -> k -> () 
{-@ lemmaLookupDelete :: m:Map k v -> k:k -> {lookup k (delete k m) == Nothing } @-}
lemmaLookupDelete Tip _         = ()
lemmaLookupDelete (Map k _ m) k' 
  | k == k'   = lemmaLookupDelete m k' 
  | otherwise = lemmaLookupDelete m k'

