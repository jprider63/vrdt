{-@ LIQUID "--reflection" @-}

{-# LANGUAGE TypeFamilies #-}

module VRDT.Max where

import Data.Semigroup (Max(..))

import VRDT.Class

-- -- JP: Use Data.Semigroup.Max? Are there any supported operations that would make it invalid?
-- newtype Max a = Max {
--     unMax :: a
--   }


instance Ord a => VRDT (Max a) where
    type Operation (Max a) = Max a

    apply (Max a) (Max b) = Max $ a

    lawCommutativity max op1 op2 = ()

-- {-@ reflect applyMax @-}
-- applyMax :: Max a -> Max a -> Max a
-- applyMax (Max a) (Max b) = Max $ max a b
-- 
-- 
-- {-@ lawCommutativityMax :: x : Max a -> op1 : Max a -> op2 : Max a -> {} @-}
-- lawCommutativityMax :: Max a -> Max a -> Max a -> ()
-- lawCommutativityMax max op1 op2 = ()

