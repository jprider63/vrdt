{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

{-# LANGUAGE TypeFamilies, TypeFamilyDependencies #-}

module VRDT.Max where

import Data.Semigroup (Max(..))
import Language.Haskell.Liquid.ProofCombinators
-- import ProofCombinators

-- import VRDT.Class

-- -- JP: Use Data.Semigroup.Max? Are there any supported operations that would make it invalid?
-- newtype Max a = Max {
--     unMax :: a
--   }


-- instance Ord a => VRDT (Max a) where
--     type Operation (Max a) = Max a
-- 
--     apply (Max a) (Max b) = Max $ max a b
-- 
--     lawCommutativity max op1 op2 = ()


{-@ reflect applyMax @-}
applyMax :: Ord a => Max a -> Max a -> Max a
applyMax (Max a) (Max b) | a > b = Max a
applyMax (Max a) (Max b)         = Max b
-- applyMax (Max a) (Max b) = Max $ max a b



{-@ ple lawCommutativityMax @-}
{-@ lawCommutativityMax :: x : Max a -> op1 : Max a -> op2 : Max a -> {applyMax op2 (applyMax op1 x) == applyMax op1 (applyMax op2 x)} @-}
lawCommutativityMax :: Ord a => Max a -> Max a -> Max a -> ()
lawCommutativityMax x@(Max x') op1 op2
  | x >= op1 && x >= op2 = 
        applyMax op2 (applyMax op1 x) ? assert (applyMax op1 x == Max x')
    === applyMax op2 x
    === x
    -- === applyMax op1 x
    -- === applyMax op1 (applyMax op2 x)
    *** QED
  | otherwise = undefined
--     --     (applyMax op2 (applyMax op1 x) == applyMax op1 (applyMax op2 x))
--     -- ==! (applyMax op2 x == applyMax op1 (applyMax op2 x)) -- ? (assume ((applyMax op1 x) == x))
--     -- ==! applyMax op2 x == applyMax op1 x
--     -- ==! x == x
--     -- ==! True
--   | op1 >= x && op1 >= op2 =
--         applyMax op2 (applyMax op1 x)
--     ==! applyMax op2 op1
--     ==! op1
--     ==! applyMax op1 x
--     ==! applyMax op1 (applyMax op2 x)
--     *** QED

assert :: Bool -> Proof
{-@ assert :: b:{Bool | b} -> {v:Proof | b} @-}
assert _ = ()

-- assume :: Bool -> Proof
-- {-@ assume assume :: b:Bool -> {v:Proof | b} @-}
-- assume _ = ()
