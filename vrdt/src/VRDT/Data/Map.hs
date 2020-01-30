{-@ LIQUID "--reflection" @-}

module Data.Map where 

import Prelude hiding (Maybe(..), lookup)
import Data.Maybe 
import qualified Data.Set as S

data Map k v = Tip | Map k v (Map k v)

{-@ reflect empty @-}
empty :: Map k v 
empty = Tip 


{-@ reflect member @-}
member :: k -> Map k v -> Bool 
member _ _ = False 

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
insert :: k -> v -> Map k v -> Map k v 
insert k v m = Map k v m  

{-@ reflect delete @-}
delete :: Ord k => k -> Map k v -> Map k v 
delete _ Tip  = Tip 
delete k' (Map k v m)
  | k == k'   = delete k' m 
  | otherwise = Map k v (delete k' m)

{-@ reflect lookup @-}
lookup :: Eq k => k -> Map k v -> Maybe v 
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