{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

{-# LANGUAGE RecordWildCards #-}

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

-- import VRDT.Class

{-@ type PosInteger = {c:Integer | c > 0} @-}
{-@ type NegInteger = {c:Integer | c <= 0} @-}

-- {-@
-- data MultiSet a = MultiSet {
--     posMultiSet ::  Map a PosInteger
--   , negMultiSet :: {v:Map a NegInteger | True}
--   }
-- @-}
  -- TODO: Is this a parser error?
  -- , negMultiSet :: {v:Map a NegInteger | Map.null (Map.intersection posMultiSet negMultiSet}
data MultiSet a = MultiSet {
    posMultiSet :: Map a Integer -- ^ Map for elements currently in the set.
  , negMultiSet :: Map a Integer -- ^ Map for elements not currently in the set.
  }

-- {-@
-- data MultiSetOp a = 
--     MultiSetOpAdd {
--       multiSetOpAddValue :: a
--     , multiSetOpAdd :: PosInteger
--     }
--   | MultiSetOpRemove {
--       multiSetOpRemValue :: a
--     , multiSetOpRem :: NegInteger
--     }
-- @-}
data MultiSetOp a = 
    MultiSetOpAdd {
      multiSetOpAddValue :: a
    , multiSetOpAdd :: Integer -- ^ Add `n` instances of element.
    }
  | MultiSetOpRemove {
      multiSetOpRemValue :: a
    , multiSetOpRem :: Integer -- ^ Remove `n` instances of element.
    }

-- {-@ measure multiSetOpOrder :: MultiSetOp a -> Int @-}
{-@ reflect multiSetOpOrder @-}
multiSetOpOrder :: MultiSetOp a -> Int
multiSetOpOrder (MultiSetOpAdd _ _) = 0
multiSetOpOrder (MultiSetOpRemove _ _) = 1

-- instance Ord a => VRDT (MultiSet a) where
--     type Operation (MultiSet a) = MultiSetOp a
-- 
--     apply MultiSet{..}  (MultiSetOpAdd e c)
--       | Just c' <- Map.lookup e posMultiSet = 
--           let c'' = c' + c in
--           if c'' > 0 then
--             let posMultiSet' = Map.insert e c'' posMultiSet in
--             MultiSet posMultiSet' negMultiSet
--           else
--             let posMultiSet' = Map.delete e posMultiSet in
--             let negMultiSet' = Map.insert e c'' negMultiSet in
--             MultiSet posMultiSet' negMultiSet'
--       | Just c' <- Map.lookup e negMultiSet =
--           let c'' = c' + c in
--           if c'' > 0 then
--             let posMultiSet' = Map.insert e c'' posMultiSet in
--             let negMultiSet' = Map.delete e negMultiSet in
--             MultiSet posMultiSet' negMultiSet'
--           else
--             let negMultiSet' = Map.insert e c'' negMultiSet in
--             MultiSet posMultiSet negMultiSet'
--       | c > 0 = 
--           let posMultiSet' = Map.insert e c posMultiSet in
--           MultiSet posMultiSet' negMultiSet
--       | otherwise =
--           let negMultiSet' = Map.insert e c negMultiSet in
--           MultiSet posMultiSet negMultiSet'
--     apply ms (MultiSetOpRemove e c) = apply ms (MultiSetOpAdd e (-c))
-- 
--     enabled _ _ = True
-- 
--     lawCommutativity MultiSet{..} op1 op2 = ()

{-@ ple apply @-}
{-@ reflect apply @-}
{-@ apply :: Ord a => MultiSet a -> op : MultiSetOp a -> MultiSet a / [multiSetOpOrder op] @-}
apply :: Ord a => MultiSet a -> MultiSetOp a -> MultiSet a
apply MultiSet{..}  (MultiSetOpAdd e c) = case Map.lookup e posMultiSet of
    Just c' ->
      let c'' = c' + c in
      if c'' > 0 then
        let posMultiSet' = Map.insert e c'' posMultiSet in
        MultiSet posMultiSet' negMultiSet
      else
        let posMultiSet' = Map.delete e posMultiSet in
        let negMultiSet' = Map.insert e c'' negMultiSet in
        MultiSet posMultiSet' negMultiSet'

    Nothing -> case Map.lookup e negMultiSet of
      Just c' ->
        let c'' = c' + c in
        if c'' > 0 then
          let posMultiSet' = Map.insert e c'' posMultiSet in
          let negMultiSet' = Map.delete e negMultiSet in
          MultiSet posMultiSet' negMultiSet'
        else
          let negMultiSet' = Map.insert e c'' negMultiSet in
          MultiSet posMultiSet negMultiSet'
      Nothing -> 
        if c > 0 then
          let posMultiSet' = Map.insert e c posMultiSet in
          MultiSet posMultiSet' negMultiSet
        else
          let negMultiSet' = Map.insert e c negMultiSet in
          MultiSet posMultiSet negMultiSet'
apply ms (MultiSetOpRemove e c) = apply ms (MultiSetOpAdd e (-c))

{-@ ple lawCommutativity @-}
{-@ lawCommutativity :: s : MultiSet a -> op1 : MultiSetOp a -> op2 : MultiSetOp a -> {apply op2 (apply op1 x) == apply op2 (apply op1 x)} @-}
lawCommutativity :: MultiSet a -> MultiSetOp a -> MultiSetOp a -> ()
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


