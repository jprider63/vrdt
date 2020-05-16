{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module VRDT.TwoPMap.P0 where

#if NotLiquid
import           Data.Maybe
import           Data.Map (Map)
import qualified Data.Map as Map
#else
import           Liquid.Data.Maybe
import           Liquid.Data.List
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Prelude hiding (Maybe(..), isJust, maybe, foldr, flip, const)
#endif

import VRDT.Class
import VRDT.TwoPMap.Types

-- {-@ ple lawCommutativity @-}
{-@ lawCommutativity :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> op1 : TwoPMapOp k v -> op2 : TwoPMapOp k v -> {(compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2)  => ((applyTwoPMap (applyTwoPMap x op1) op2 == applyTwoPMap (applyTwoPMap x op2) op1) && compatibleStateTwoPMap (applyTwoPMap x op1) op2)} @-}
lawCommutativity :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
lawCommutativity _ _ _ = undefined




{-@ ple lawCompatibilityCommutativity' @-}
{-@ lawCompatibilityCommutativity' :: (Eq k, Ord (Operation v), VRDT v) => op1:TwoPMapOp k v -> op2:TwoPMapOp k v -> {compatibleTwoPMap op1 op2 = compatibleTwoPMap op2 op1} @-}
lawCompatibilityCommutativity' :: (Eq k, Ord (Operation v), VRDT v) => TwoPMapOp k v -> TwoPMapOp k v -> ()
lawCompatibilityCommutativity' (TwoPMapInsert k v) (TwoPMapInsert k' v') | k == k' = ()
lawCompatibilityCommutativity' (TwoPMapApply k op) (TwoPMapApply k' op') | k == k' = lawCompatibilityCommutativity op op'
lawCompatibilityCommutativity' _ _ = ()

