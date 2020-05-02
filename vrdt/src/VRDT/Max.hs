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

-- {-@ ple lawCommutativity @-}
-- {-@ ple lawNonCausal @-}
instance Ord a => VRDT (Max a) where
    type Operation (Max a) = Max a

    enabled max op = True

    apply (Max a) (Max b) | a > b = Max a
    apply (Max a) (Max b)         = Max b

    lawCommutativity max op1 op2 = ()
    
    lawNonCausal max op1 op2 = ()


-- {-@ reflect applyMax @-}
-- applyMax :: Ord a => Max a -> Max a -> Max a
-- applyMax (Max a) (Max b) | a > b = Max a
-- applyMax (Max a) (Max b)         = Max b
-- 
-- {-@ reflect enabledMax @-}
-- enabledMax :: Max a -> Max a -> Bool
-- enabledMax _ _ = True
-- 
-- 
-- {-@ ple lawCommutativityMax @-}
-- {-@ lawCommutativityMax :: x : Max a -> op1 : Max a -> op2 : Max a -> {applyMax op2 (applyMax op1 x) == applyMax op1 (applyMax op2 x)} @-}
-- lawCommutativityMax :: Ord a => Max a -> Max a -> Max a -> ()
-- lawCommutativityMax x@(Max x') op1@(Max op1') op2@(Max op2') = ()
-- 
-- {-@ ple lawNonCausal @-}
-- {-@ lawNonCausal :: Ord a => x : Max a -> {op1 : Max a | enabledMax x op1} -> {op2 : Max a | enabledMax x op2} -> {enabledMax (applyMax x op1) op2 <=> enabledMax (applyMax x op2) op1} @-}
-- lawNonCausal :: Ord a => Max a -> Max a -> Max a -> ()
-- lawNonCausal max op1 op2 = ()

