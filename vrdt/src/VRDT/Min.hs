{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

{-# LANGUAGE TypeFamilies, TypeFamilyDependencies #-}

module VRDT.Min where

-- import Data.Semigroup (Min(..))
import Language.Haskell.Liquid.ProofCombinators
-- import ProofCombinators

-- import VRDT.Class

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


-- instance Ord a => VRDT (Min a) where
--     type Operation (Min a) = Min a
-- 
--     apply (Min a) (Min b) = Min $ min a b
-- 
--     lawCommutativity min op1 op2 = ()
-- 
--     enabled _ _ = True


{-@ reflect applyMin @-}
applyMin :: Ord a => Min a -> Min a -> Min a
applyMin (Min a) (Min b) | a > b = Min a
applyMin (Min a) (Min b)         = Min b


{-@ ple lawCommutativityMin @-}
{-@ lawCommutativityMin :: x : Min a -> op1 : Min a -> op2 : Min a -> {applyMin op2 (applyMin op1 x) == applyMin op1 (applyMin op2 x)} @-}
lawCommutativityMin :: Ord a => Min a -> Min a -> Min a -> ()
lawCommutativityMin x@(Min x') op1@(Min op1') op2@(Min op2') = ()

