{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}

module Generators where

import Control.DeepSeq (NFData(..))
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Sequence (Seq, (|>))
import qualified Data.Sequence as Seq
import Data.Set (Set)
import qualified Data.Set as Set
import GHC.Generics (Generic(..))
import System.Random

import Types
import VRDT.CausalTree
import VRDT.Class
import VRDT.LWW
import VRDT.Max
import VRDT.Min
import VRDT.MultiSet
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

-- type KeyGen = (Seq Int, Int)
type KeyGen = (Seq Int, Set Int)


-- TODO: 
isEmpty :: KeyGen -> Bool
isEmpty (ks, _) = Seq.null ks

-- nextKey :: KeyGen -> (KeyGen, Int)
-- nextKey (keys, t) = 
--   let t' = t+1 in
--   let keys' = keys |> t' in
--   ((keys', t'), t')
nextKey :: RandomGen g => g -> KeyGen -> (g, KeyGen, Int)
nextKey rng (keys, keySet) = 
  let (rng', t') = genKey rng in
  let keys' = keys |> t' in
  let keySet' = Set.insert t' keySet in
  (rng', (keys', keySet'), t')

  where
    genKey rng =
      let (k, rng') = random rng in
      if Set.member k keySet then
        genKey rng'
      else
        (rng', k)

removeKey :: RandomGen g => g -> KeyGen -> (g, Int, KeyGen)
removeKey rng (keys, t) =
  let (i, rng') = randomR (0, Seq.length keys - 1) rng in
  let k = Seq.index keys i in
  let keys' = Seq.deleteAt i keys in
  (rng', k, (keys', t))

randomKey :: RandomGen g => g -> KeyGen -> (g, Int)
randomKey rng (keys, t) = 
  let (i, rng') = randomR (0, Seq.length keys - 1) rng in
  let k = Seq.index keys i in
  (rng', k)
  


twoPMapGen :: Generator (TwoPMap Int (Sum Int)) (TwoPMapOp Int (Sum Int)) KeyGen
twoPMapGen = Generator genInit gen initSt app
  where
    genInit = (mempty, mempty)
    gen :: RandomGen g => g -> KeyGen -> (g, KeyGen, (TwoPMapOp Int (Sum Int)))
    gen rng keyGen =
      let (w, rng') = randomR (0,99) rng in
      
      -- 60% insert.
      if (w :: Int) < 60 || isEmpty keyGen then
        let (i, rng'') = randomR (-10000, 10000) rng' in
        let (rng''', keyGen', t') = nextKey rng'' keyGen in
        (rng''', keyGen', TwoPMapInsert t' (Sum i))

      -- 20% update.
      else if w < 80 then
        let (m, rng'') = randomR (-1000,1000) rng' in
        let (rng''', k) = randomKey rng'' keyGen in
        (rng''', keyGen, TwoPMapApply k (Sum m))

      -- 20% delete.
      else
        let (rng', k, keyGen') = removeKey rng keyGen in
        (rng', keyGen', TwoPMapDelete k)

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

mapGen :: Generator (Map Int (Sum Int)) (TwoPMapOp Int (Sum Int)) KeyGen
mapGen = Generator genInit gen initSt app
  where
    genInit = (mempty, mempty)
    gen :: RandomGen g => g -> KeyGen -> (g, KeyGen, (TwoPMapOp Int (Sum Int)))
    gen rng keyGen =
      let (w, rng') = randomR (0,99) rng in
      
      -- 60% insert.
      if (w :: Int) < 60 || isEmpty keyGen then
        let (i, rng'') = randomR (-10000, 10000) rng' in
        let (rng''', keyGen', t') = nextKey rng'' keyGen in
        (rng''', keyGen', TwoPMapInsert t' (Sum i))

      -- 20% update.
      else if w < 80 then
        let (m, rng'') = randomR (-1000,1000) rng' in
        let (rng''', k) = randomKey rng'' keyGen in
        (rng''', keyGen, TwoPMapApply k (Sum m))

      -- 20% delete.
      else
        let (rng', k, keyGen') = removeKey rng keyGen in
        (rng', keyGen', TwoPMapDelete k)

    initSt = mempty
    app m (TwoPMapInsert k v) = Map.insert k v m
    app m (TwoPMapApply k op) = Map.adjust (flip apply op) k m
    app m (TwoPMapDelete k)   = Map.delete k m

deriving instance (Show a) => Show (MultiSet a)
deriving instance (Show a) => Show (MultiSetOp a)
deriving instance (NFData a) => NFData (MultiSet a)
deriving instance (NFData a) => NFData (MultiSetOp a)

multisetGen :: Generator (MultiSet Int) (MultiSetOp Int) KeyGen
multisetGen = Generator genInit gen initSt app
  where
    genInit = (mempty, mempty)
    gen rng keyGen = 
      let (w, rng') = randomR (0,99) rng in

      -- 60% insert.
      if (w :: Int) < 60 || isEmpty keyGen then
        let (i, rng'') = randomR (-10000, 10000) rng' in
        let (rng''', keyGen', t') = nextKey rng'' keyGen in
        (rng''', keyGen', MultiSetOpAdd t' i)

      -- 40% update.
      else 
        let (m, rng'') = randomR (-1000,1000) rng' in
        let (rng''', k) = randomKey rng'' keyGen in
        (rng''', keyGen, MultiSetOpAdd k m)


    initSt = initVRDT
    app = apply

causalTreeGen :: Generator (CausalTree Int Char) (CausalTreeOp Int Char) KeyGen
causalTreeGen = Generator genInit gen initSt app
  where
    genInit = (Seq.singleton initId, Set.singleton initId)
    gen rng keyGen =
      let (rng', parentK) = randomKey rng keyGen in
      let (rng'', keyGen', k) = nextKey rng' keyGen in

      let (w, rng''') = randomR (0,99) rng'' in
      -- 70% insert.
      if (w :: Int) < 70 || isEmpty keyGen then
        let (c, rng'''') = randomR ('a','z') rng''' in
        let op = CausalTreeOp parentK (CausalTreeAtom k (CausalTreeLetter c)) in
        (rng'''', keyGen', op)

      -- 30% delete.
      else
        let op = CausalTreeOp parentK (CausalTreeAtom k CausalTreeLetterDelete) in
        (rng''', keyGen', op)

    initSt = CausalTree (CausalTreeWeave (CausalTreeAtom initId CausalTreeLetterRoot) []) mempty
    initId = 0

    app = apply

deriving instance Generic (CausalTree i c)
deriving instance (NFData i, NFData c) => NFData (CausalTree i c)
deriving instance Generic (CausalTreeOp i c)
deriving instance (NFData i, NFData c) => NFData (CausalTreeOp i c)
deriving instance Generic (CausalTreeWeave i c)
deriving instance (NFData i, NFData c) => NFData (CausalTreeWeave i c)
deriving instance Generic (CausalTreeLetter c)
deriving instance (NFData c) => NFData (CausalTreeLetter c)
deriving instance Generic (CausalTreeAtom i c)
deriving instance (NFData i, NFData c) => NFData (CausalTreeAtom i c)

-- TODO: List?



