module VRDT.MultiSet where

import Data.Map (Map)
import qualified Data.Map as Map

import VRDT.Class

data MultiSet a = MultiSet {
    unMultiSet :: Map a Integer -- JP: Maybe use a hashmap?
  }

data MultiSetOp a = 
    MultiSetOpAdd a Integer    -- ^ Add `n` instances of element.
  | MultiSetOpRemove a Integer -- ^ Remove `n` instances of element.

instance Ord a => VRDT (MultiSet a) where
    type Operation (MultiSet a) = MultiSetOp a

    apply (MultiSetOpAdd e c) = MultiSet . Map.insertWith (+) e c . unMultiSet

    apply (MultiSetOpRemove e c) = MultiSet . Map.insertWith (+) e (-c) . unMultiSet

null :: MultiSet a -> Bool
null = Map.foldr (\c acc -> acc && c <= 0) True . unMultiSet

-- TODO: Prove correctness: vrdt : VRDT.MultiSet -> {ms : Data.MultiSet | equiv vrdt ms} -> {null vrdt == null ms}

size :: MultiSet a -> Integer
distinctSize :: MultiSet a -> Integer
member :: Ord a => a -> MultiSet a -> Bool
notMember :: Ord a => a -> MultiSet a -> Bool


occur :: Ord a => a -> MultiSet a -> Integer
occur e = max 0 . Map.findWithDefault 0 e . unMultiSet

empty :: MultiSet a
empty = MultiSet Map.empty

insert :: Ord a => a -> MultiSet a -> MultiSetOp a
insert e = insertMany e 1

insertMany :: Ord a => a -> Integer -> MultiSet a -> MultiSetOp a
insertMany e c _ = MultiSetOpAdd e c

delete :: Ord a => a -> MultiSet a -> MultiSetOp a
delete e = deleteMany e 1

deleteMany :: Ord a => a -> Integer -> MultiSet a -> MultiSetOp a 
deleteMany e c _ = MultiSetOpRemove e c

deleteAll :: Ord a => a -> MultiSet a -> MultiSetOp a
deleteAll e ms = deleteMany e (occur e ms) ms


