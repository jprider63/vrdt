{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module VRDT.MultiSet (
    MultiSet(..)
  , MultiSetOp(..)
  , null
  , size
  , distinctSize
  , member
  , notMember
  , occur
  , empty
  , insert
  , insertMany
  , delete
  , deleteMany
  , deleteAll
  ) where

import Data.Map (Map)
import qualified Data.Map as Map
import Prelude hiding (null)

import VRDT.Class

{-@
data MultiSet a = MultiSet {
    posMultiSet ::  Map a {c:Integer | c > 0}
  , negMultiSet :: {Map a {c:Integer | c <= 0} | Map.null (Map.intersection posMultiSet negMultiSet}
@-}
data MultiSet a = MultiSet {
    posMultiSet :: Map a Integer -- ^ Map for elements currently in the set.
  , negMultiSet :: Map a Integer -- ^ Map for elements not currently in the set.
  }

data MultiSetOp a = 
    MultiSetOpAdd a Integer    -- ^ Add `n` instances of element.
  | MultiSetOpRemove a Integer -- ^ Remove `n` instances of element.

instance Ord a => VRDT (MultiSet a) where
    type Operation (MultiSet a) = MultiSetOp a

    apply MultiSet{..}  (MultiSetOpAdd e c)
      | Just c' <- Map.lookup e posMultiSet = 
          let c'' = c' + c in
          if c'' > 0 then
            let posMultiSet' = Map.insert e c'' posMultiSet in
            MultiSet posMultiSet' negMultiSet
          else
            let posMultiSet' = Map.delete e posMultiSet in
            let negMultiSet' = Map.insert e c'' negMultiSet in
            MultiSet posMultiSet' negMultiSet'
      | Just c' <- Map.lookup e negMultiSet =
          let c'' = c' + c in
          if c'' > 0 then
            let posMultiSet' = Map.insert e c'' posMultiSet in
            let negMultiSet' = Map.delete e negMultiSet in
            MultiSet posMultiSet' negMultiSet'
          else
            let negMultiSet' = Map.insert e c'' negMultiSet in
            MultiSet posMultiSet negMultiSet'
      | c > 0 = 
          let posMultiSet' = Map.insert e c posMultiSet in
          MultiSet posMultiSet' negMultiSet
      | otherwise =
          let negMultiSet' = Map.insert e c negMultiSet in
          MultiSet posMultiSet negMultiSet'
    apply ms (MultiSetOpRemove e c) = apply ms (MultiSetOpAdd e (-c))

    enabled _ _ = True

--     apply (MultiSetOpRemove e c) = MultiSet . Map.insertWith (+) e (-c) . unMultiSet

    lawCommutativity MultiSet{..} op1 op2 = ()


null :: MultiSet a -> Bool
null = Map.null . posMultiSet

-- TODO: Prove correctness: vrdt : VRDT.MultiSet -> {ms : Data.MultiSet | equiv vrdt ms} -> {null vrdt == null ms}

size :: MultiSet a -> Integer
size = sum . Map.elems . posMultiSet

distinctSize :: MultiSet a -> Int -- Integer
distinctSize = Map.size . posMultiSet

member :: Ord a => a -> MultiSet a -> Bool
member e = Map.member e . posMultiSet

notMember :: Ord a => a -> MultiSet a -> Bool
notMember e = not . member e


occur :: Ord a => a -> MultiSet a -> Integer
occur e = Map.findWithDefault 0 e . posMultiSet

empty :: MultiSet a
empty = MultiSet Map.empty Map.empty

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


