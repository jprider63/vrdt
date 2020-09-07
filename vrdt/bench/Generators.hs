{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Generators where

import Control.DeepSeq (NFData(..))
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import GHC.Generics (Generic(..))
import System.Random

import Types
import VRDT.Class
import VRDT.LWW
import VRDT.Max
import VRDT.Min
import VRDT.Sum
import VRDT.TwoPMap

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

twoPMapGen :: Generator (TwoPMap Int (Sum Int)) (TwoPMapOp Int (Sum Int)) (Seq Int, Int)
twoPMapGen = Generator genInit gen initSt app
  where
    genInit = (mempty, 0)
    gen :: RandomGen g => g -> (Seq Int, Int) -> (g, (Seq Int, Int), (TwoPMapOp Int (Sum Int)))
    gen rng (keys, t) =
      let (w, rng') = randomR (0,99) rng in
      
      -- 60% insert.
      if (w :: Int) < 60 || Seq.null keys then
        let (i, rng'') = randomR (-10000, 10000) rng' in
        let t' = t+1 in
        let keys' = keys |> t' in
        (rng'', (keys', t'), TwoPMapInsert t' (Sum i))

      -- 20% update.
      else if w < 80 then
        let (m, rng'') = randomR (-1000,1000) rng' in
        let (i, rng''') = randomR (0, Seq.length keys - 1) rng'' in
        let k = Seq.index keys i in
        (rng''', (keys, t), TwoPMapApply k (Sum m))

      -- 10% delete.
      else
        let (i, rng') = randomR (0, Seq.length keys - 1) rng in
        let k = Seq.index keys i in
        let keys' = Seq.deleteAt i keys in
        (rng', (keys', t), TwoPMapDelete k)

    initSt = initVRDT
    app = apply

deriving instance Eq t => Eq (Sum t)
deriving instance Ord t => Ord (Sum t)
instance (Show k, Show v, Show (Operation v)) => Show (TwoPMapOp k v) where
  show (TwoPMapInsert k v) = "insert (" <> show k <> ", " <> show v <> ")"
  show (TwoPMapApply k op) = "apply (" <> show k <> ", " <> show op <> ")"
  show (TwoPMapDelete k) = "delete " <> show k
instance (Show k, Show v) => Show (TwoPMap k v) where
  show (TwoPMap m _ _) = show m
deriving instance Generic (TwoPMap k v)
deriving instance (NFData k, NFData v, NFData (Operation v)) => NFData (TwoPMap k v)
-- deriving instance (Show k, Show v) => Show (TwoPMapOp k v)
-- deriving instance Generic (TwoPMapOp k v)
deriving instance (NFData k, NFData v, NFData (Operation v)) => NFData (TwoPMapOp k v)



-- TODO: CausalTree, 2PMap, MultiSet


