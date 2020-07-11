{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}
module VRDT.CausalTree where

#if NotLiquid
import           Data.Aeson (ToJSON(..), FromJSON(..), (.:), (.=))
import qualified Data.Aeson as Aeson
#endif

-- import           Liquid.Data.List (List(..))
-- import qualified Liquid.Data.List as List
#if NotLiquid
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
#else
import qualified Liquid.Data.List as List
import           Liquid.Data.Maybe
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Prelude hiding (Maybe(..), concat)
#endif
import           Data.Maybe (mapMaybe)
import           Data.Time.Clock (UTCTime)
import           VRDT.Types
import           VRDT.Internal
import           ProofCombinators
import qualified VRDT.CausalTree.Internal as CT
import qualified VRDT.CausalTree.NEq as CT
import           VRDT.Class

{-@ assume coercAxiom0 :: {v : () | applyCausalTree ~~ CT.apply} @-}
coercAxiom0 :: ()
coercAxiom0 = ()

{-@ assume coercAxiom1 :: {v : () | compatibleCausalTree ~~ CT.compatible} @-}
coercAxiom1 :: ()
coercAxiom1 = ()

{-@ assume coercAxiom2 :: {v : () | compatibleStateCausalTree ~~ CT.compatibleState} @-}
coercAxiom2 :: ()
coercAxiom2 = ()


{-@ reflect applyCausalTree @-}
applyCausalTree :: Ord id => CT.CausalTree id a -> Operation (CT.CausalTree id a) -> CT.CausalTree id a
applyCausalTree = CT.apply

{-@ reflect compatibleCausalTree @-}
compatibleCausalTree :: Ord id => Operation (CT.CausalTree id a) -> Operation (CT.CausalTree id a) -> Bool
compatibleCausalTree = CT.compatible

{-@ reflect compatibleStateCausalTree @-}
compatibleStateCausalTree :: Ord id => CT.CausalTree id a -> Operation (CT.CausalTree id a) -> Bool
compatibleStateCausalTree = CT.compatibleState


instance Ord id => VRDT (CT.CausalTree id a) where
  type Operation (CT.CausalTree id a) = CT.CausalTreeOp id a
  apply x op = applyCausalTree x op
  compatible x y = compatibleCausalTree x y
  compatibleState x op = compatibleStateCausalTree x op
  lawCommutativity x op1 op2 = CT.lawCommutativity x op1 op2
  lawCompatibilityCommutativity op1 op2 = CT.lawCompatibilityCommutativity op1 op2

  

