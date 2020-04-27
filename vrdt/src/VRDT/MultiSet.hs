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

#ifdef NotLiquid
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe
#else
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Liquid.Data.Maybe
#endif
import qualified Liquid.Data.Map.Props as Map
import           Liquid.ProofCombinators
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

{-@ ple apply @-}
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

{-@ lawCommutativityNEq :: Ord a => x : MultiSet a -> v1:a -> c1:Integer -> {v2:a| v1 /= v2} -> c2:Integer -> {apply (apply x (MultiSetOpAdd v1 c1)) (MultiSetOpAdd v2 c2) == apply (apply x (MultiSetOpAdd v2 c2)) (MultiSetOpAdd v1 c1)} @-}
lawCommutativityNEq :: Ord a => MultiSet a -> a -> Integer -> a -> Integer -> ()
lawCommutativityNEq x@MultiSet{..} v1 c1 v2 c2 
  -- | Nothing <- Map.lookup v1 negMultiSet
  -- , Nothing <- Map.lookup v2 negMultiSet 
  = 
    let c1'' = case Map.lookup v1 posMultiSet of
          Nothing  -> case Map.lookup v1 negMultiSet of
            Nothing -> c1
            Just c1' -> c1 + c1'
          Just c1' -> c1 + c1'
    in
    let c2'' = case Map.lookup v2 posMultiSet of
          Nothing  -> case Map.lookup v2 negMultiSet of
            Nothing -> c2
            Just c2' -> c2 + c2'
          Just c2' -> c2 + c2'
    in

    if c1'' > 0 then
      if c2'' > 0 then
        --     apply (apply x op1) op2 ? 
        --             assert (Map.disjoint posMultiSet negMultiSet) 
        --         &&& assert (not (Map.member v1 (Map.delete v1 negMultiSet))) 
        --         &&& assert (Map.disjoint posMultiSet (Map.delete v1 negMultiSet))
        --         &&& Map.lemmaDisjoint' v1 c1'' posMultiSet (Map.delete v1 negMultiSet)
        -- ==. apply (MultiSet (Map.insert v1 c1'' posMultiSet) (Map.delete v1 negMultiSet)) op2 ? 
        --             assert (Map.disjoint (Map.delete v1 negMultiSet) (Map.insert v1 c1'' posMultiSet))
        --         &&& Map.lemmaDisjoint'' v2 c2'' (Map.delete v1 negMultiSet) (Map.insert v1 c1'' posMultiSet)
        --         &&& assert (Map.disjoint (Map.insert v2 c2'' (Map.insert v1 c1'' posMultiSet)) (Map.delete v2 (Map.delete v1 negMultiSet)))
        --         &&& Map.lemmaLookupDelete2 negMultiSet v2 v1
        --         &&& Map.lemmaLookupInsert2 posMultiSet v2 v1 c1''
        -- ==. MultiSet (Map.insert v2 c2'' (Map.insert v1 c1'' posMultiSet)) (Map.delete v2 (Map.delete v1 negMultiSet)) ?
        --             Map.lemmaInsert v2 c2'' v1 c1'' posMultiSet
        --         &&& Map.lemmaDelete v1 v2 negMultiSet
        -- ==. MultiSet (Map.insert v1 c1'' (Map.insert v2 c2'' posMultiSet)) (Map.delete v1 (Map.delete v2 negMultiSet)) ?
        --             assert (Map.disjoint negMultiSet posMultiSet) 
        --         &&& Map.lemmaDisjoint'' v2 c2'' negMultiSet posMultiSet
        --         &&& assert (Map.disjoint (Map.insert v2 c2'' posMultiSet) (Map.delete v2 negMultiSet))
        --         &&& Map.lemmaLookupInsert2 posMultiSet v1 v2 c2''
        --         &&& Map.lemmaLookupDelete2 negMultiSet v1 v2
        -- ==. apply (MultiSet (Map.insert v2 c2'' posMultiSet) (Map.delete v2 negMultiSet)) op1
        -- ==. apply (apply x op2) op1
        -- *** QED
        undefined

      else
            apply (apply x op1) op2 ? 
                    assert (Map.disjoint posMultiSet negMultiSet) 
                &&& assert (not (Map.member v1 (Map.delete v1 negMultiSet))) 
                &&& assert (Map.disjoint posMultiSet (Map.delete v1 negMultiSet))
                &&& Map.lemmaDisjoint' v1 c1'' posMultiSet (Map.delete v1 negMultiSet)
        ==. apply (MultiSet (Map.insert v1 c1'' posMultiSet) (Map.delete v1 negMultiSet)) op2 ? 
                    assert (Map.disjoint (Map.insert v1 c1'' posMultiSet) (Map.delete v1 negMultiSet))
                &&& Map.lemmaLookupDelete2 negMultiSet v2 v1
                &&& Map.lemmaLookupInsert2 posMultiSet v2 v1 c1''
                &&& Map.lemmaDisjoint'' v2 c2'' (Map.insert v1 c1'' posMultiSet) (Map.delete v1 negMultiSet)
        ==. MultiSet (Map.delete v2 (Map.insert v1 c1'' posMultiSet)) (Map.insert v2 c2'' (Map.delete v1 negMultiSet)) ?
                    Map.lemmaInsertDelete v1 c1'' v2 posMultiSet
                &&& Map.lemmaInsertDelete v2 c2'' v1 negMultiSet
        ==. MultiSet (Map.insert v1 c1'' (Map.delete v2 posMultiSet)) (Map.insert v2 c2'' (Map.delete v1 negMultiSet)) ?
                    Map.lemmaLookupDelete2 posMultiSet v1 v2
                &&& Map.lemmaLookupInsert2 negMultiSet v1 v2 c2''
                &&& Map.lemmaDisjoint'' v2 c2'' posMultiSet negMultiSet
                &&& Map.lemmaDisjoint'' v1 c1'' (Map.delete v2 posMultiSet) (Map.insert v2 c2'' negMultiSet)
        ==. apply (MultiSet (Map.delete v2 posMultiSet) (Map.insert v2 c2'' negMultiSet)) op1
        ==. apply (apply x op2) op1
        *** QED

    else
      undefined
      -- if c2'' > 0 then
      --       apply (apply x op2) op1 ? 
      --               assert (Map.disjoint posMultiSet negMultiSet) 
      --           &&& assert (not (Map.member v2 negMultiSet)) 
      --           &&& Map.lemmaDisjoint' v2 c2'' posMultiSet negMultiSet 
      --   ==. apply (MultiSet (Map.insert v2 c2'' posMultiSet) negMultiSet) op1 ? 
      --               assert (Map.disjoint (Map.insert v2 c2'' posMultiSet) negMultiSet)
      --           &&& assert (not (Map.member v1 negMultiSet)) 
      --           &&& Map.lemmaDisjoint'' v1 c1'' (Map.insert v2 c2'' posMultiSet) negMultiSet 
      --           &&& Map.lemmaLookupInsert2 posMultiSet v1 v2 c2''
      --   ==. MultiSet (Map.delete v1 (Map.insert v2 c2'' posMultiSet)) (Map.insert v1 c1'' negMultiSet) ?
      --               Map.lemmaInsertDelete v2 c2'' v1 posMultiSet
      --   ==. MultiSet (Map.insert v2 c2'' (Map.delete v1 posMultiSet)) (Map.insert v1 c1'' negMultiSet) ?
      --               Map.lemmaDisjoint'' v1 c1'' posMultiSet negMultiSet
      --           &&& Map.lemmaLookupDelete2 posMultiSet v2 v1
      --           &&& assert (not (Map.member v2 (Map.insert v1 c1'' negMultiSet)))
      --           &&& Map.lemmaNotMemberLookupNothing v2 (Map.insert v1 c1'' negMultiSet)
      --   ==. apply (MultiSet (Map.delete v1 posMultiSet) (Map.insert v1 c1'' negMultiSet)) op2
      --   ==. apply (apply x op1) op2
      --   *** QED

      -- else
      --       apply (apply x op1) op2 ? 
      --               assert (Map.disjoint posMultiSet negMultiSet) 
      --           &&& Map.lemmaDisjoint'' v1 c1'' posMultiSet negMultiSet
      --   ==. apply (MultiSet (Map.delete v1 posMultiSet) (Map.insert v1 c1'' negMultiSet)) op2 ? 
      --               Map.lemmaDisjoint'' v2 c2'' (Map.delete v1 posMultiSet) (Map.insert v1 c1'' negMultiSet)
      --           &&& Map.lemmaLookupInsert2 negMultiSet v2 v1 c1''
      --           &&& Map.lemmaLookupDelete2 posMultiSet v2 v1
      --   ==. MultiSet (Map.delete v2 (Map.delete v1 posMultiSet)) (Map.insert v2 c2'' (Map.insert v1 c1'' negMultiSet)) ?
      --               Map.lemmaInsert v2 c2'' v1 c1'' negMultiSet
      --           &&& Map.lemmaDelete v2 v1 posMultiSet
      --   ==. MultiSet (Map.delete v1 (Map.delete v2 posMultiSet)) (Map.insert v1 c1'' (Map.insert v2 c2'' negMultiSet)) ?
      --               Map.lemmaDisjoint'' v2 c2'' posMultiSet negMultiSet
      --           &&& Map.lemmaLookupDelete2 posMultiSet v1 v2
      --           &&& assert (not (Map.member v1 (Map.insert v2 c2'' negMultiSet)))
      --           &&& Map.lemmaNotMemberLookupNothing v1 (Map.insert v2 c2'' negMultiSet)
      --   ==. apply (MultiSet (Map.delete v2 posMultiSet) (Map.insert v2 c2'' negMultiSet)) op1
      --   ==. apply (apply x op2) op1
      --   *** QED

  -- | otherwise = undefined

  where
    op1 = MultiSetOpAdd v1 c1
    op2 = MultiSetOpAdd v2 c2


{-@ lawCommutativityEq :: Ord a => x : MultiSet a -> v:a -> c1:Integer -> c2:Integer -> {apply (apply x (MultiSetOpAdd v c1)) (MultiSetOpAdd v c2) == apply (apply x (MultiSetOpAdd v c2)) (MultiSetOpAdd v c1)} @-}
lawCommutativityEq :: Ord a => MultiSet a -> a -> Integer -> Integer -> ()
lawCommutativityEq x@MultiSet{..} v c1 c2 = undefined

  where
    v1 = v
    v2 = v

    op1 = MultiSetOpAdd v1 c1
    op2 = MultiSetOpAdd v2 c2



-- {-@ ple lawCommutativity @-}
{-@ lawCommutativity :: Ord a => x : MultiSet a -> op1 : MultiSetOp a -> op2 : MultiSetOp a -> {apply (apply x op1) op2 == apply (apply x op2) op1} / [multiSetOpOrder op1 + multiSetOpOrder op2] @-}
lawCommutativity :: Ord a => MultiSet a -> MultiSetOp a -> MultiSetOp a -> ()
-- lawCommutativity MultiSet{..} op1 op2 = ()
lawCommutativity x@MultiSet{..} op1@(MultiSetOpAdd v1 c1) op2@(MultiSetOpAdd v2 c2) 
  | v1 /= v2  = lawCommutativityNEq x v1 c1 v2 c2
  | otherwise = lawCommutativityEq x v1 c1 c2

  -- | Just c1' <- Map.lookup v1 posMultiSet
  -- , Just c2' <- Map.lookup v2 posMultiSet
  -- , v1 /= v2 = 
  --   let c1'' = c1 + c1' in
  --   let c2'' = c2 + c2' in


  -- -- | Just c1' <- Map.lookup v1 posMultiSet
  -- -- , v1 == v2 = 
  -- --   let c1'' = c1 + c1' in

  -- --   if c1'' > 0 then
  -- --     if c2'' > 0 then
  -- --       undefined
  -- --     else
  -- --       undefined -- TODO XXX
  -- --       -- ()

  -- --   else
  -- --       undefined -- TODO XXX
  -- --       -- ()

  -- | otherwise = undefined -- () -- TODO XXX
lawCommutativity x@MultiSet{..} op1@(MultiSetOpAdd v1 c1) op2@(MultiSetOpRemove v2 c2) = 
    let op2' = MultiSetOpAdd v2 (-c2) in

        apply (apply x op1) op2
    ==. apply (apply x op1) op2' ? lawCommutativity x op1 op2'

    ==. apply (apply x op2') op1
    ==. apply (apply x op2) op1
    *** QED
lawCommutativity x@MultiSet{..} op1@(MultiSetOpRemove v1 c1) op2@(MultiSetOpAdd v2 c2) = 
    let op1' = MultiSetOpAdd v1 (-c1) in

        apply (apply x op1) op2
    ==. apply (apply x op1') op2 ? lawCommutativity x op1' op2

    ==. apply (apply x op2) op1'
    ==. apply (apply x op2) op1
    *** QED
lawCommutativity x@MultiSet{..} op1@(MultiSetOpRemove v1 c1) op2@(MultiSetOpRemove v2 c2) = 
    let op1' = MultiSetOpAdd v1 (-c1) in
    let op2' = MultiSetOpAdd v2 (-c2) in

        apply (apply x op1) op2
    ==. apply (apply x op1) op2'
    ==. apply (apply x op1') op2' ? lawCommutativity x op1' op2'

    ==. apply (apply x op2') op1'
    ==. apply (apply x op2') op1
    ==. apply (apply x op2) op1
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

{-@ ple empty @-}
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




