{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Liquid.Data.Map where 

import Prelude hiding (Maybe(..), lookup)
import Liquid.Data.Maybe 
import Liquid.ProofCombinators
import qualified Data.Set as S

data Map k v = 
    Tip 
  | Map {
      mapKey :: k
    , mapValue :: v 
    , mapTail :: Map k v
    }
{-@ 
data Map k v = Tip
  | Map {
      mapKey :: k
    , mapValue :: v 
    , mapTail :: Map {kk: k | mapKey < kk} v
    }
@-}
-- data Map k v = Tip | Map {k::k,  v::v, m::Map {kk:k | k < kk} v}
-- {-@ data Map k v = Tip | Map {k::k,  v::v, m::Map {kk:k | k /= kk} v} @-}



{-@ reflect toList @-}
toList :: Map k v -> [(k,v)]
toList Tip = [] 
toList (Map k v m) = (k,v):toList m 

{-@ reflect empty @-}
empty :: Ord k => Map k v 
{-@ empty :: Ord k => {m:Map k v | S.null (keys m) } @-}
empty = Tip 


{-@ reflect member @-}
{-@ member :: Ord k => k:k -> m:Map k v -> {vv:Bool | vv = S.member k (keys m)} @-}
member :: Ord k => k -> Map k v -> Bool 
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
{-@ insert :: Ord k => k:k -> v -> m:Map k v -> {v:Map k v | keys v == S.union (S.singleton k) (keys m) } @-}
insert :: Ord k => k -> v -> Map k v -> Map k v
insert k v Tip = Map k v Tip
insert k' v' (Map k v m)
  | k' == k   = Map k v' m
  | k' < k    = Map k' v' (Map k v m) -- ? assume ()
  | otherwise = Map k v (insert k' v' m)

{-@ reflect keyLeqLemma @-}
{-@ 
keyLeqLemma 
  :: Ord k 
  => kd:k 
  -> {k:k | kd <= k}
  -> v:v 
  -> {t:Map {k':k|k < k'} v | k == mapKey (Map k v t) && v == mapValue (Map k v t) && t == mapTail (Map k v t)}
  -> {not (S.member kd (keys t))}
@-}
keyLeqLemma 
  :: Ord k 
  => k 
  -> k 
  -> v 
  -> Map k v
  -> ()
keyLeqLemma kd k v Tip = ()
keyLeqLemma kd k v t@(Map k' v' t') = keyLeqLemma kd k' v' t'


{-@ reflect delete @-}
{-@ delete :: Ord k => kd:k -> m:Map k v -> {v:Map k v | if (S.member kd (keys m)) then (keys v == S.difference (keys m) (S.singleton kd)) else m == v } @-} -- (keys m == keys v) } @-}
delete :: Ord k => k -> Map k v -> Map k v 
delete _ Tip  = Tip 
delete kd (Map k v m)
  -- | kd == k   = delete kd m
  | kd == k   = m `by` keyLeqLemma kd k v m

  | kd > k    = Map k v (delete kd m)

  -- kd < k
  | otherwise = Map k v m `by` keyLeqLemma kd k v m
  


{-@ reflect lookup @-}
lookup :: Ord k => k -> Map k v -> Maybe v 
{-@ lookup :: Ord k => k:k -> m:Map k v -> {v:Maybe {vv:v | S.member k (keys m)} | isJust v <=> S.member k (keys m)} @-}
lookup _ Tip  = Nothing 
lookup k' (Map k v m)
  | k == k'   = Just v 
  | otherwise = lookup k' m 


{-@ reflect findWithDefault @-}
findWithDefault :: Ord k => v -> k -> Map k v -> v 
findWithDefault v k m 
  = case lookup k m of
     Just v' -> v' 
     Nothing -> v  


{-@ measure keys @-}
keys :: Ord k => Map k v -> S.Set k 
keys Tip = S.empty 
keys (Map k _ m) = S.singleton k `S.union` keys m

{-@ reflect disjoint @-}
disjoint :: Ord k => Map k v -> Map k v -> Bool 
disjoint m1 m2 = S.null (S.intersection (keys m1) (keys m2))

{-@ reflect updateLookupWithKey @-}
updateLookupWithKey :: Ord k => (k -> a -> Maybe a) -> k -> Map k a -> (Maybe a, Map k a)
updateLookupWithKey f k m = case lookup k m of
  Nothing -> (Nothing, m)
  Just x -> case f k x of
    Nothing -> (Just x, delete k m)
    Just x' -> (Just x, insert k x' m)

{-@ reflect insertWith @-}
insertWith :: Ord k => (a -> a -> a) -> k -> a -> Map k a -> Map k a
insertWith f k v m = case lookup k m of
  Nothing -> insert k v m
  Just v' -> insert k (f v v') m

