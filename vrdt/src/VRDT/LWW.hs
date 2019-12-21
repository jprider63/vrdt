module VRDT.LWW where

import VRDT.Class

data LWW t a = LWW {
    lwwTime  :: t
  , lwwValue :: a
  }

instance Ord t => VRDT (LWW t a) where
    type Operation (LWW t a) = LWW t a

    apply l1@(LWW t1 _) l2@(LWW t2 _) 
      | t1 > t2   = l1
      | otherwise = l2
    
    lawCommutativity LWW{..} op1 op2 = ()

-- TODO: We need the invariant that two ops cannot have the same time... I guess we need enabled.

