{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}

{-# LANGUAGE RecordWildCards #-}

module VRDT.MultiSet where

import VRDT.Class

import Liquid.Data.Maybe
import Liquid.Data.Map
import           Prelude hiding (null, Maybe(..))
import qualified VRDT.MultiSet.Internal as Internal
import           VRDT.MultiSet.Internal (MultiSet(..), MultiSetOp(..))
import           ProofCombinators


instance Ord a => VRDT (Internal.MultiSet a) where
    type Operation (Internal.MultiSet a) = Internal.MultiSetOp a

    apply = Internal.apply

    compatible _ _ = True
    compatibleState _ _ = True
    
    lawCommutativity m op1 op2 = Internal.lawCommutativity m op1 op2 `cast` ()

    lawCompatibilityCommutativity _ _ = ()

#if NotLiquid
instance Ord a => VRDTInitial (MultiSet a) where
    initVRDT = MultiSet mempty mempty
#endif

