{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-# LANGUAGE UndecidableInstances #-}

module VRDT.TwoPMap where

-- #define NotCheckAll True

#if NotLiquid
import qualified Data.Aeson as Aeson
import           Data.Maybe
import           Data.Map (Map)
import qualified Data.Map as Map
#else
import           Liquid.Data.Maybe
import           Liquid.Data.List
import qualified Liquid.Data.List as List
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           VRDT.Class.Proof
import           Prelude hiding (Maybe(..), isJust, maybe, foldr, flip, const)
#endif

import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Generics

import           Liquid.Data.Map.Props
import           VRDT.Class
import           VRDT.Internal
import           VRDT.TwoPMap.Internal
import           Liquid.ProofCombinators
import           ProofCombinators
import           VRDT.TwoPMap.LemmaIA
import           VRDT.TwoPMap.LemmaID
import           VRDT.TwoPMap.LemmaII
import           VRDT.TwoPMap.LemmaAA
import           VRDT.TwoPMap.LemmaAD
import           VRDT.TwoPMap.LemmaAI
import           VRDT.TwoPMap.LemmaDA
import           VRDT.TwoPMap.LemmaDD
import           VRDT.TwoPMap.LemmaDI

{-@ assume coercAxiom0 :: {v : () | applyTwoPMap' ~~ applyTwoPMap} @-}
coercAxiom0 :: ()
coercAxiom0 = ()

{-@ reflect applyTwoPMap' @-}
applyTwoPMap' :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> Operation (TwoPMap k v) -> TwoPMap k v
applyTwoPMap' = applyTwoPMap

instance (Ord k, Ord (Operation v), VRDT v) => VRDT (TwoPMap k v) where
  type Operation (TwoPMap k v) = TwoPMapOp k v
  apply x op = applyTwoPMap' x op
  compatible x y = compatibleTwoPMap x y
  compatibleState x y = compatibleStateTwoPMap x y
  lawCommutativity x op1 op2 = lawCommutativityTwoPMap x op1 op2
  lawCompatibilityCommutativity op1 op2 = undefined




{-@ lawCommutativityTwoPMap :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> op1 : TwoPMapOp k v -> op2 : TwoPMapOp k v -> {(compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2)  => ((applyTwoPMap (applyTwoPMap x op1) op2 == applyTwoPMap (applyTwoPMap x op2) op1) && compatibleStateTwoPMap (applyTwoPMap x op1) op2)} @-}
lawCommutativityTwoPMap :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> TwoPMapOp k v -> TwoPMapOp k v -> ()
lawCommutativityTwoPMap x op1 op2
  | not (compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2) = ()
lawCommutativityTwoPMap x (TwoPMapInsert k1 v1) (TwoPMapInsert k2 v2) = lawCommutativityII x k1 v1 k2 v2
lawCommutativityTwoPMap x (TwoPMapInsert k1 v1) (TwoPMapApply k2 v2)  = lawCommutativityIA x k1 v1 k2 v2
lawCommutativityTwoPMap x (TwoPMapInsert k1 v1) (TwoPMapDelete k2)    = lawCommutativityID x k1 v1 k2
lawCommutativityTwoPMap x (TwoPMapApply k1 v1)  (TwoPMapInsert k2 v2) = lawCommutativityAI x k1 v1 k2 v2
lawCommutativityTwoPMap x (TwoPMapApply k1 v1)  (TwoPMapApply k2 v2)  = lawCommutativityAA x k1 v1 k2 v2
lawCommutativityTwoPMap x (TwoPMapApply k1 v1)  (TwoPMapDelete k2)    = lawCommutativityAD x k1 v1 k2
lawCommutativityTwoPMap x (TwoPMapDelete k1)  (TwoPMapInsert k2 v2)   = lawCommutativityDI x k1 k2 v2
lawCommutativityTwoPMap x (TwoPMapDelete k1)  (TwoPMapApply k2 v2)    = lawCommutativityDA x k1 k2 v2
lawCommutativityTwoPMap x (TwoPMapDelete k1)  (TwoPMapDelete k2)      = lawCommutativityDD x k1 (TwoPMapDelete k1) k2
