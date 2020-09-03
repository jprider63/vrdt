{-# LANGUAGE DeriveAnyClass #-}
module Generators where

import Control.DeepSeq (NFData(..))
import GHC.Generics (Generic(..))
import System.Random

import Types
import VRDT.Class
import VRDT.LWW
import VRDT.Max
import VRDT.Min
import VRDT.Sum

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

sumGen :: Generator (Sum Int) (Sum Int) ()
sumGen = Generator genInit gen initSt app
  where
    genInit = ()
    gen rng () = 
      let (m, rng') = randomR (-1000,1000) rng in -- uniformR?
      (rng', (), Sum m)

    initSt = Sum 0
    app = apply

deriving instance Show a => Show (Sum a)
deriving instance Generic (Sum a)
deriving instance NFData a => NFData (Sum a)

lwwGen :: Generator (LWW Int Int) (LWW Int Int) Int
lwwGen = Generator genInit gen initSt app
  where
    genInit = 0
    gen rng t = 
      let (v, rng') = random rng in -- uniformR?
      (rng', t+1, LWW t v)

    initSt = LWW 0 0
    app = apply

deriving instance (Show t, Show a) => Show (LWW t a)
deriving instance Generic (LWW t a)
deriving instance (NFData t, NFData a) => NFData (LWW t a)

