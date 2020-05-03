{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.Sum where

import VRDT.Class


-- JP: Use Data.Semigroup.Sum?
{-@
data Sum a = Sum {
  unSum :: a
}
@-}
data Sum a = Sum {
  unSum :: a
}

instance Num a => VRDT (Sum a) where
  type Operation (Sum a) = Sum a

  enabled x op = True

  apply (Sum a) (Sum b) = Sum (a + b)

  lawCommutativity x op1 op2 = ()
  lawNonCausal x op1 op2 = ()
