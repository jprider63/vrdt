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
{-@ insert :: Ord k => k:k -> v -> m:Map k v -> {v:Map k v | keys v == S.union (S.singleton k) (keys m) } @-}
insert :: Ord k => k -> v -> Map k v -> Map k v
insert k v Tip = Map k v Tip
insert k' v' (Map k v m)
  | k' == k   = Map k v' m
  | k' < k    = Map k' v' (Map k v m) -- ? assume ()
  | otherwise = Map k v (insert k' v' m)

-- {-@ ple keyLeqLemma @-}
{-@ 
keyLeqLemma 
  :: Ord k 
  => kd:k 
  -> {k:k | kd <= k}
  -> v:v 
  -> {t:Map k v | k == mapKey (Map k v t) && v == mapValue (Map k v t) && t == mapTail (Map k v t)}
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
keyLeqLemma kd k v t@(Map k' v' t') | k >= k' = assert (k < k') -- JP: This is unreachable. Why can't LH prove this?
-- keyLeqLemma kd k v t@(Map k' v' t') | kd == k = assert (k < k' && kd <= k && kd < k')
keyLeqLemma kd k v t@(Map k' v' t') = 
    case t' of 
      Tip -> 
        if kd < k' then
              not (S.member kd (keys t)) -- ? assert (k < k' && kd <= k && kd < k')
          ==. not (S.member kd (S.fromList [k']))
          ==. True
          *** QED
        else
            -- assert (k < k' && kd <= k && kd < k')
            assert (kd < k')
            -- error "unreachable"
      Map _ _ _ -> 
        undefined
        -- if k' <= kd then 
        --   keyLeqLemma kd k' v' t' 
        -- else
        --   ()

  -- where
  --   m = Map k v t


  -- if kd == k then
  --   ()
  -- else if kd < k then
  --   -- let m = Map k v t in 
  --   -- keyLeqLemma kd k' v' t'
  --   case t' of 
  --     Tip -> ()
  --     Map _ _ t'' -> keyLeqLemma kd k' v' t'
  -- else case t' of
  --   Tip -> ()
  --   Map k'' v'' t'' -> keyLeqLemma kd k'' v'' t''

-- keyLeqLemma kd k v Tip = () -- undefined -- TODO
-- keyLeqLemma kd _ _ (Map k v t) = case t of
--   Tip -> ()
--   Map k2 v2 t2 -> keyLeqLemma kd k2 v2 t2

-- {-@ ple delete @-}
{-@ reflect delete @-}
{-@ delete :: Ord k => k:k -> m:Map k v -> {v:Map k v | if (S.member k (keys m)) then (keys v == S.difference (keys m) (S.singleton k)) else (keys m == keys v) } @-}
delete :: Ord k => k -> Map k v -> Map k v 
delete _ Tip  = Tip 
delete kd (Map k v m)
  -- | kd == k   = delete kd m
  | kd == k   = m ? keyLeqLemma kd k v m

  | kd > k    = Map k v (delete kd m)

  -- kd < k
  | otherwise = Map k v m ? keyLeqLemma kd k v m
  


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
