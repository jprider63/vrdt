{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}

{-# LANGUAGE RecordWildCards #-}

module VRDT.MultiSet (
  module Internal
  , apply'
  ) where

import VRDT.Class

import Liquid.Data.Maybe
import Liquid.Data.Map
import           Prelude hiding (null, Maybe(..))
import qualified VRDT.MultiSet.Internal as Internal
import           VRDT.MultiSet.Internal (MultiSet(..), MultiSetOp(..))
import           ProofCombinators

{-@ reflect apply' @-}
apply' :: Ord a => MultiSet a -> Operation (MultiSet a) -> MultiSet a
apply' = Internal.apply

{-@ assume coercAxiom0 :: {v : () | apply' ~~ Internal.apply} @-}
coercAxiom0 :: ()
coercAxiom0 = ()
instance Ord a => VRDT (Internal.MultiSet a) where
    type Operation (Internal.MultiSet a) = Internal.MultiSetOp a

    apply = apply'

    compatible _ _ = True
    compatibleState _ _ = True
    
    lawCommutativity m op1 op2 = Internal.lawCommutativity m op1 op2 `cast` ()

    lawCompatibilityCommutativity _ _ = ()

#if NotLiquid
instance Ord a => VRDTInitial (MultiSet a) where
    initVRDT = MultiSet mempty mempty
#endif

