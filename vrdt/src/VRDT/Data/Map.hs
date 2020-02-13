{-@ LIQUID "--reflection" @-}

module Data.Map where 

import Prelude hiding (Maybe(..), lookup)
import Data.Maybe 
import qualified Data.Set as S

data Map k v = Tip | Map k v (Map k v)
{-@ data Map k v = Tip | Map {k::k,  v::v, m::Map {kk:k | kk /= k} v} @-}



{-@ reflect toList @-}
toList :: Map k v -> [(k,v)]
toList Tip = [] 
toList (Map k v m) = (k,v):toList m 

{-@ reflect empty @-}
empty :: Map k v 
{-@ empty :: {m:Map k v | S.null (keys m) } @-}
empty = Tip 


{-@ reflect member @-}
member :: Eq k => k -> Map k v -> Bool 
member _ Tip = False 
member x (Map k _ m) = x == k || member x m 

{-@ reflect elems @-}
elems :: Map k v -> [v]
elems Tip = [] 
elems (Map _ v m) = v:elems m

{-@ reflect null @-}
null :: Map k v -> Bool 
null Tip = True 
null _   = False  


{-@ measure size @-}
size :: Map k v -> Int 
{-@ size :: Map k v -> Nat @-} 
size Tip = 0
size (Map _ _ m) = 1 + size m  

{-@ reflect insert @-}
{-@ insert :: Eq k => k:k -> v -> m:Map k v -> {v:Map k v | keys v == S.union (S.singleton k) (keys m) } @-}
insert :: Eq k => k -> v -> Map k v -> Map k v
insert k v Tip = Map k v Tip
insert k' v' (Map k v m)
  | k == k'   = Map k v' m
  | otherwise = Map k v (insert k' v' m)

{-@ reflect delete @-}
{-@ delete :: k:k -> m:Map k v -> {v:Map k v | if (S.member k (keys m)) then (keys v == S.difference (keys m) (S.singleton k)) else (keys m == keys v) } @-}
delete :: Ord k => k -> Map k v -> Map k v 
delete _ Tip  = Tip 
delete k' (Map k v m)
  | k == k'   = delete k' m 
  | otherwise = Map k v (delete k' m)

{-@ reflect lookup @-}
lookup :: Eq k => k -> Map k v -> Maybe v 
{-@ lookup :: Eq k => k:k -> m:Map k v -> {v:Maybe {vv:v | S.member k (keys m)} | isJust v <=> S.member k (keys m)} @-}
lookup _ Tip  = Nothing 
lookup k' (Map k v m)
  | k == k'   = Just v 
  | otherwise = lookup k' m 


{-@ reflect findWithDefault @-}
findWithDefault :: Eq k => v -> k -> Map k v -> v 
findWithDefault v k m 
  = case lookup k m of
     Just v' -> v' 
     Nothing -> v  


{-@ measure keys @-}
keys :: Ord k => Map k v -> S.Set k 
keys Tip = S.empty 
keys (Map k _ m) = S.singleton k `S.union` keys m

{-@ inline disjoint @-}
disjoint :: Ord k => Map k v -> Map k v -> Bool 
disjoint m1 m2 = S.null (S.intersection (keys m1) (keys m2))