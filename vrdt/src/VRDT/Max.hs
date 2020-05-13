{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-# LANGUAGE TypeFamilies, TypeFamilyDependencies #-}

module VRDT.Max where

-- import Data.Semigroup (Max(..))
-- import Language.Haskell.Liquid.ProofCombinators
-- import ProofCombinators

import VRDT.Class

-- JP: Use Data.Semigroup.Max? Are there any supported operations that would make it invalid?
{-@
data Max a = Max {
    unMax :: a
  }
@-}
data Max a = Max {
    unMax :: a
  }
  deriving (Eq, Ord)

instance Ord a => VRDT (Max a) where
    type Operation (Max a) = Max a

    compatible op1 op2 = True

    apply (Max a) (Max b) | a > b = Max a
    apply (Max a) (Max b)         = Max b

    lawCommutativity max op1 op2 = ()
    
    lawCompatibilityCommutativity op1 op2 = ()

