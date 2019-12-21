module VRDT.Max where

import VRDT.Class

-- JP: Use Data.Semigroup.Max? Are there any supported operations that would make it invalid?
newtype Max a = Max {
    unMax :: a
  }


instance Ord a => VRDT (Max a) where
    type Operation (Max a) = Max a

    apply (Max a) (Max b) = Max $ max a b

    lawCommutativity max op1 op2 = ()


