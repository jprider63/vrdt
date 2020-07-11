{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.Internal where

#if NotLiquid
import           Data.Map (Map)
import qualified Data.Map as Map
#else
import           Liquid.Data.Maybe hiding (concat)
import           Liquid.Data.Map (Map)
import           Liquid.Data.List
import           Liquid.ProofCombinators
import qualified Liquid.Data.Map as Map
import qualified Liquid.Data.Map.Props as Map
import           Prelude hiding (Maybe(..), concat, length)
import qualified Data.Set as S
#endif

{-@ reflect insertPending @-}
--{-@ insertPending :: (Ord k, Ord a) => k -> a -> Map k [a] -> Map k [a] @-}
insertPending :: (Ord k, Ord a) => k -> a -> Map k [a] -> Map k [a]
#if NotLiquid
insertPending k op p = Map.insertWith (++) k [op] p
#else
insertPending k op p = case Map.lookup k p of
    Nothing -> Map.insert k [op] p
    Just ops -> Map.insert k (insertList op ops) p

{-@ reflect insertList @-}
{-@ insertList :: Ord a => x:a -> xs:[a] -> {vv:[a] | length vv /= 0 && S.fromList vv == S.union (S.fromList xs) (S.singleton x)} @-}
insertList :: Ord a => a -> [a] -> [a]
insertList v [] = [v]
insertList v (h:t)
  | v <= h    = v:h:t
  | otherwise = h:insertList v t

{-@ insertListDestruct :: Ord a => x:a -> xs:[a] ->
  (lts::[a], {gts:[a] | (concat lts gts == xs) && (concat lts (cons x gts) == insertList x xs)}) @-}
insertListDestruct :: Ord a => a -> [a] -> ([a],[a])
insertListDestruct v [] = ([],[])
insertListDestruct v (h:t)
  | v <= h = ([], h:t)
  | otherwise =
    let (lts,gts) = insertListDestruct v t in
      (h:lts, gts)

{-@ lemmaInsertListTwice :: Ord a => x:a -> y:a -> xs:[a] -> {insertList y (insertList x xs) == insertList x (insertList y xs)} @-}
lemmaInsertListTwice :: Ord a => a -> a -> [a] -> ()
lemmaInsertListTwice x y [] = ()
lemmaInsertListTwice x y (z:zs)
  | x <= z, y <= z
  =  ()
  | x <= z, y > z
  = ()
  | x > z, y <= z
  = ()
  | otherwise
  = lemmaInsertListTwice x y zs


-- finish up
{-@ lemmaInsertPendingTwice :: (Ord a, Ord k) => k:k -> x:a -> y:a -> xs:Map k [a] -> {insertPending k y (insertPending k x xs) == insertPending k x (insertPending k y xs)} @-}
lemmaInsertPendingTwice :: (Ord k, Ord a) => k -> a -> a -> Map k [a] -> ()
lemmaInsertPendingTwice k x y m
  | Nothing <- Map.lookup k m
  = Map.lemmaLookupInsert m k [x]
  ? lemmaInsertListTwice x y []
  ? lemmaInsertListTwice y x []
  ? Map.lemmaLookupInsert m k [y]
  ? Map.lemmaInsertTwice k (insertList y [x]) [x] m
  ? Map.lemmaInsertTwice k (insertList x [y]) [y] m
  | Just zs <- Map.lookup k m
  = Map.lemmaLookupInsert m k (insertList x zs)
  ? Map.lemmaLookupInsert m k (insertList y zs)
  ? lemmaInsertListTwice x y zs
  ? lemmaInsertListTwice y x zs
  ? Map.lemmaInsertTwice k (insertList y (insertList x zs)) (insertList x zs) m
  ? Map.lemmaInsertTwice k (insertList x (insertList y zs)) (insertList y zs) m


{-@ lemmaInsertPendingTwiceNEq :: (Ord k,Ord a) => x:a -> y:a -> k:k -> {k':k | k /= k'} -> xs:Map k [a] ->
  {(insertPending k' y (insertPending k x xs) == insertPending k x (insertPending k' y xs))} @-}
lemmaInsertPendingTwiceNEq :: (Ord k, Ord a) => a -> a -> k -> k -> Map k [a] -> ()
lemmaInsertPendingTwiceNEq k k' x y m = undefined

{-@ lemmaInsertPendingLookup :: (Ord a, Ord k ) => y:a -> k:k -> {k':k | k /= k'} -> xs:Map k [a] ->
  {(Map.lookup k (insertPending k' y xs) == Map.lookup k xs)} @-}
lemmaInsertPendingLookup :: (Ord k, Ord a) => a -> k -> k -> Map k [a] -> ()
lemmaInsertPendingLookup k k' y m = undefined


  
#endif

