{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-# LANGUAGE TypeFamilies, TypeFamilyDependencies #-}

module VRDT.Min where

-- import Data.Semigroup (Min(..))
import Language.Haskell.Liquid.ProofCombinators
-- import ProofCombinators

import VRDT.Class

-- JP: Use Data.Semigroup.Min? Are there any supported operations that would make it invalid?
{-@
data Min a = Min {
    unMin :: a
  }
@-}
data Min a = Min {
    unMin :: a
  }
  deriving (Eq, Ord)


instance Ord a => VRDT (Min a) where
    type Operation (Min a) = Min a

    apply (Min a) (Min b) | a < b = Min a
    apply (Min a) (Min b)         = Min b

    compatible _ _ = True
    compatibleState _ _ = True

    lawCommutativity min op1 op2 = ()
    lawCompatibilityCommutativity _ _ = ()

