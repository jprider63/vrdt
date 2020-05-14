{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module VRDT.Internal where

#if NotLiquid
import           Data.Map (Map)
import qualified Data.Map as Map
#else
import           Liquid.Data.Maybe
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Prelude hiding (Maybe(..))
#endif

{-@ reflect insertPending @-}
insertPending :: (Ord k, Ord a) => k -> a -> Map k [a] -> Map k [a]
#if NotLiquid
insertPending k op p = Map.insertWith (++) k [op] p
#else
insertPending k op p = case Map.lookup k p of
    Nothing -> Map.insert k [op] p
    Just ops -> Map.insert k (insertList op ops) p

{-@ reflect insertList @-}
insertList :: Ord a => a -> [a] -> [a]
insertList v [] = [v]
insertList v (h:t)
  | v <= h    = v:h:t
  | otherwise = h:insertList v t

#endif

