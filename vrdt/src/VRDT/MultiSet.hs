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

  , enabled
  , apply
  , multiSetOpOrder
  ) where

-- #ifdef NotLiquid
-- import           Data.Map (Map)
-- import qualified Data.Map as Map
-- import           Data.Maybe
import           Liquid.ProofCombinators
-- #else
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Liquid.Data.Maybe
-- import           Language.Haskell.Liquid.ProofCombinators
-- #endif
-- import           Liquid.ProofCombinators
import           Prelude hiding (null, Maybe(..))
import qualified Data.Set as S

-- import VRDT.Class

{-@ type PosInteger = {c:Integer | c > 0} @-}
{-@ type NegInteger = {c:Integer | c <= 0} @-}

{-@
data MultiSet a = MultiSet {
    posMultiSet ::  Map a PosInteger
  , negMultiSet :: {v:Map a NegInteger | Map.disjoint posMultiSet v }
  }
@-} 
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

{-@ measure multiSetOpOrder @-}
{-@ multiSetOpOrder :: MultiSetOp a -> Nat @-}
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

{-@ reflect enabled @-}
enabled :: MultiSet k -> MultiSetOp k -> Bool 
enabled _ _ = True 

{-@ reflect apply @-}
{-@ apply :: Ord a => MultiSet a -> op : MultiSetOp a -> MultiSet a / [multiSetOpOrder op] @-}
apply :: Ord a => MultiSet a -> MultiSetOp a -> MultiSet a
apply MultiSet{..} (MultiSetOpAdd e c)
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

-- {-@ ple lawCommutativity @-}
{-@ lawCommutativity :: Ord a => x : MultiSet a -> op1 : MultiSetOp a -> op2 : MultiSetOp a -> {apply (apply x op1) op2 == apply (apply x op2) op1} / [multiSetOpOrder op1 + multiSetOpOrder op2] @-}
lawCommutativity :: Ord a => MultiSet a -> MultiSetOp a -> MultiSetOp a -> ()
-- lawCommutativity MultiSet{..} op1 op2 = ()
lawCommutativity x@MultiSet{..} op1@(MultiSetOpAdd v1 c1) op2@(MultiSetOpAdd v2 c2) 
  | Just c1' <- Map.lookup v1 posMultiSet
  , Just c2' <- Map.lookup v2 posMultiSet
  , v1 /= v2 =
    let c1'' = c1 + c1' in
    let c2'' = c2 + c2' in

    if c1'' > 0 then
      if c2'' > 0 then
            apply (apply x op1) op2
        === apply (MultiSet (Map.insert v1 c1'' posMultiSet) negMultiSet) op2
        === MultiSet (Map.insert v2 c2'' (Map.insert v1 c1'' posMultiSet)) negMultiSet
        === MultiSet (Map.insert v1 c1'' (Map.insert v2 c2'' posMultiSet)) negMultiSet
        === apply (MultiSet (Map.insert v2 c2'' posMultiSet) negMultiSet) op2
        === apply (apply x op2) op1
        *** QED
      else
        undefined
        -- ()

    else
        undefined
        -- ()

  | otherwise = undefined -- ()
lawCommutativity x@MultiSet{..} op1@(MultiSetOpAdd v1 c1) op2@(MultiSetOpRemove v2 c2) = 
    let op2' = MultiSetOpAdd v2 (-c2) in

        apply (apply x op1) op2
    === apply (apply x op1) op2' ? lawCommutativity x op1 op2'

    === apply (apply x op2') op1
    === apply (apply x op2) op1
    *** QED
lawCommutativity x@MultiSet{..} op1@(MultiSetOpRemove v1 c1) op2@(MultiSetOpAdd v2 c2) = 
    let op1' = MultiSetOpAdd v1 (-c1) in

        apply (apply x op1) op2
    === apply (apply x op1') op2 ? lawCommutativity x op1' op2

    === apply (apply x op2) op1'
    === apply (apply x op2) op1
    *** QED
lawCommutativity x@MultiSet{..} op1@(MultiSetOpRemove v1 c1) op2@(MultiSetOpRemove v2 c2) = 
    let op1' = MultiSetOpAdd v1 (-c1) in
    let op2' = MultiSetOpAdd v2 (-c2) in

        apply (apply x op1) op2
    === apply (apply x op1) op2'
    === apply (apply x op1') op2' ? lawCommutativity x op1' op2'

    === apply (apply x op2') op1'
    === apply (apply x op2') op1
    === apply (apply x op2) op1
    *** QED


{-@ ple lawNonCausal @-}
{-@ lawNonCausal :: Ord t => x : MultiSet t -> {op1 : MultiSetOp t | enabled x op1} -> {op2 : MultiSetOp t | enabled x op2} -> {enabled (apply x op1) op2 <=> enabled (apply x op2) op1} @-}
lawNonCausal :: Ord t => MultiSet t -> MultiSetOp t -> MultiSetOp t -> ()
lawNonCausal _ _ _ = () 

null :: MultiSet a -> Bool
null = Map.null . posMultiSet

-- TODO: Prove correctness: vrdt : VRDT.MultiSet -> {ms : Data.MultiSet | equiv vrdt ms} -> {null vrdt == null ms}

size :: MultiSet a -> Integer
size = sum . Map.elems . posMultiSet

distinctSize :: MultiSet a -> Int -- Integer
distinctSize = Map.size . posMultiSet

-- NV to JP: why member only checks posMultiSet???
member :: Ord a => a -> MultiSet a -> Bool
member e = Map.member e . posMultiSet

notMember :: Ord a => a -> MultiSet a -> Bool
notMember e = not . member e


occur :: Ord a => a -> MultiSet a -> Integer
occur e = Map.findWithDefault 0 e . posMultiSet

empty :: Ord a => MultiSet a
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


