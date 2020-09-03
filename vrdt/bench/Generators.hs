{-# LANGUAGE DeriveAnyClass #-}
module Generators where

import Control.DeepSeq (NFData(..))
import GHC.Generics (Generic(..))
import System.Random

import Types
import VRDT.Class
import VRDT.Max
import VRDT.Min

minGen :: Generator (Min Int) (Min Int) ()
minGen = Generator genInit gen initSt app
  where
    genInit = ()
    gen rng () = 
      let (m, rng') = random rng in
      (rng', (), Min m)

    initSt = Min maxBound
    app = apply

deriving instance Show a => Show (Min a)
deriving instance Generic (Min a)
deriving instance NFData a => NFData (Min a)

maxGen :: Generator (Max Int) (Max Int) ()
maxGen = Generator genInit gen initSt app
  where
    genInit = ()
    gen rng () = 
      let (m, rng') = random rng in
      (rng', (), Max m)

    initSt = Max minBound
    app = apply

deriving instance Show a => Show (Max a)
deriving instance Generic (Max a)
deriving instance NFData a => NFData (Max a)

