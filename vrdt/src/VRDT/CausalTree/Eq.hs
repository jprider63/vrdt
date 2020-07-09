{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--noadt" @-}
module VRDT.CausalTree.Eq where

import VRDT.CausalTree.Internal
import qualified Liquid.Data.List              as List
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import qualified Data.Set as S
import           Liquid.Data.Map.Props
import           VRDT.Internal
import           Liquid.Data.Maybe
import           Prelude                 hiding ( Maybe(..)
                                                , empty
                                                )

import           VRDT.CausalTree.Lemmas
import           VRDT.CausalTree.NEq (lemmaApplyAtomFoldNeq)
import           Liquid.ProofCombinators
import           ProofCombinators

{-@ ple lawCommutativityEqN @-}
{-@ lawCommutativityEqN :: Ord id
  => x:CausalTree id a
  -> pid:id
  -> {atom1:CausalTreeAtom id a | insertInWeave (causalTreeWeave x) pid atom1 == Nothing}
  -> atom2:CausalTreeAtom id a
  -> {applyAtom (applyAtom x pid atom1) pid atom2  == applyAtom (applyAtom x pid atom2) pid atom1} @-}
lawCommutativityEqN :: forall id a. Ord id
  => CausalTree id a
  -> id
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lawCommutativityEqN x@(CausalTree weave children) pid atom1@(CausalTreeAtom id1 _) atom2@(CausalTreeAtom id2 _)
  | Nothing <- insertInWeave weave pid atom1
  = lemmaInsertInWeaveNothingEq
        weave
        pid
        atom1
        atom2
  &&& lemmaInsertPendingTwice pid atom1 atom2 children
  &&& toProof ( CausalTree weave (insertPending pid atom1 children)
  `cast` CausalTree weave (insertPending pid atom2 (insertPending pid atom1 children))
  `cast` CausalTree weave (insertPending pid atom2 children))

{-@ ple lawCommutativityEqNJ @-}
{-@ lawCommutativityEqNJ :: Ord id
  => x:CausalTree id a
  -> pid:id
  -> {atom1:CausalTreeAtom id a | insertInWeave (causalTreeWeave x) pid atom1 == Nothing}
  -> {atom2:CausalTreeAtom id a | isJust (insertInWeave (causalTreeWeave x) pid atom2)}
  -> {False} @-}
lawCommutativityEqNJ :: forall id a. Ord id
  => CausalTree id a
  -> id
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lawCommutativityEqNJ x@(CausalTree weave children) pid atom1@(CausalTreeAtom id1 _) atom2@(CausalTreeAtom id2 _)
  | Nothing <- insertInWeave weave pid atom1
  , Just _ <- insertInWeave weave pid atom2
  = ()

{-@ lawCommutativityEqJ :: Ord id
  => {x:CausalTree id a | idUniqueCausalTree x}
  -> pid:id
  -> {atom1:CausalTreeAtom id a | isJust (insertInWeave (causalTreeWeave x) pid atom1) && not (S.member (causalTreeAtomId atom1) (causalTreeIds x))}
  -> {atom2:CausalTreeAtom id a | isJust (insertInWeave (causalTreeWeave x) pid atom2)  && not (S.member (causalTreeAtomId atom2) (causalTreeIds x)) && (causalTreeAtomId atom1 /= causalTreeAtomId atom2)}
  -> {applyAtom (applyAtom x pid atom1) pid atom2  == applyAtom (applyAtom x pid atom2) pid atom1} @-}
lawCommutativityEqJ :: forall id a. Ord id
  => CausalTree id a
  -> id
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lawCommutativityEqJ x@(CausalTree weave children) pid atom1@(CausalTreeAtom id1 _) atom2@(CausalTreeAtom id2 _)
  | Just wop1 <- insertInWeave weave pid atom1
  , Just wop2 <- insertInWeave weave pid atom2
  , Nothing <- Map.lookup id1 children
  , Just pops2 <- Map.lookup id2 children
  = (Map.updateLookupWithKey constConstNothing id1 children
    === (Nothing, children)
    *** QED) &&&
    ( List.foldl' (applyAtomHelper pid) x [atom1]
    === List.foldl' (applyAtomHelper pid) (applyAtomHelper pid x atom1) []
    === List.foldl' (applyAtomHelper pid) (applyAtom x pid atom1) []
    === applyAtom x pid atom1
    === CausalTree wop1 children
    *** QED) &&&
    (List.foldl' (applyAtomHelper pid) (applyAtom x pid atom2) [atom1]
    === List.foldl' (applyAtomHelper pid) (applyAtomHelper pid (applyAtom x pid atom2) atom1) []
    === List.foldl' (applyAtomHelper pid) (applyAtom (applyAtom x pid atom2) pid atom1) []
    === applyAtom (applyAtom x pid atom2) pid atom1
    *** QED) &&&
    (Map.updateLookupWithKey constConstNothing id2 children
     ? (constConstNothing id2 pops2 === Nothing *** QED)
    === (Just pops2, Map.delete id2 children)
    *** QED) &&&
    (applyAtom x pid atom2
    === List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 children)) pops2
    *** QED) &&&


    (idUniqueCausalTree (CausalTree wop2 (Map.delete id2 children))
    === (idUniqueWeave wop2 && idUniqueMap (Map.delete id2 children) && S.null (S.intersection (weaveIds wop2) (pendingIds (Map.delete id2 children))))
    *** QED) &&&
    assume (idUniqueWeave wop2) &&&
    assume (idUniqueMap (Map.delete id2 children)) &&&
    assume (S.null (S.intersection (weaveIds wop2) (pendingIds (Map.delete id2 children)))) &&&
    (causalTreeIds x
    === S.union (weaveIds weave) (pendingIds children)
    *** QED) &&&
    lemmaLookupSubsetOf children id2 pops2 &&&
    (pendingListIds [atom1]
    `cast` pendingListIds ([] @ (CausalTreeAtom id a) )
    `cast` pendingListIds pops2
    `cast` idUniqueList pops2
    `cast` idUniqueList [atom1]
    `cast` idUniqueList ([] @ (CausalTreeAtom id a))
    `cast` ()) &&&
    lemmaApplyAtomFoldNeq (CausalTree wop2 (Map.delete id2 children)) pid id2 [atom1] pops2 &&&


    (applyAtom (applyAtom x pid atom2) pid atom1
    === List.foldl' (applyAtomHelper pid) (applyAtom x pid atom2) [atom1]
    === List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 children)) pops2) [atom1]
    === List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper pid) (CausalTree wop2 (Map.delete id2 children)) [atom1]) pops2
    *** QED ) &&&

    
    -- let Just wop1op2 = insertInWeave wop1 pid atom2
    --     Just wop2op1 = insertInWeave wop2 pid atom1 in
    -- lemmaInsertInWeaveJustEq weave pid wop1 wop2 atom1 atom2 &&&
    -- (Just wop1op2 === Just wop2op1 *** QED) &&&
    -- (applyAtom (applyAtom x pid atom1) pid atom2
    -- ==. applyAtom (CausalTree wop1 children) pid atom2
    -- ==. CausalTree wop1op2 children
    -- ==. CausalTree wop2op1 children
    -- ==. applyAtom (CausalTree wop2 children) pid atom1
    -- ==. applyAtom (applyAtom x pid atom2) pid atom1
    -- *** QED)
    ()
  -- | Just wop1 <- insertInWeave weave pid atom1
  -- , Just wop2 <- insertInWeave weave pid atom2
  -- , Nothing <- Map.lookup id1 children
  -- , Nothing <- Map.lookup id2 children
  -- = (Map.updateLookupWithKey constConstNothing id1 children
  --   ==. (Nothing, children)
  --   *** QED) &&&
  --   (applyAtom x pid atom1
  --   ==. CausalTree wop1 children
  --   *** QED) &&&
  --   (Map.updateLookupWithKey constConstNothing id2 children
  --   ==. (Nothing, children)
  --   *** QED) &&&
  --   (applyAtom x pid atom2
  --   ==. CausalTree wop2 children
  --   *** QED) &&&
  --   let Just wop1op2 = insertInWeave wop1 pid atom2
  --       Just wop2op1 = insertInWeave wop2 pid atom1 in
  --   lemmaInsertInWeaveJustEq weave pid wop1 wop2 atom1 atom2 &&&
  --   (Just wop1op2 === Just wop2op1 *** QED) &&&
  --   (applyAtom (applyAtom x pid atom1) pid atom2
  --   ==. applyAtom (CausalTree wop1 children) pid atom2
  --   ==. CausalTree wop1op2 children
  --   ==. CausalTree wop2op1 children
  --   ==. applyAtom (CausalTree wop2 children) pid atom1
  --   ==. applyAtom (applyAtom x pid atom2) pid atom1
  --   *** QED)
  | otherwise
  = undefined
  -- | Just _ <- insertInWeave weave pid atom1
  -- , Just _ <- insertInWeave weave pid atom2
  -- , Just [] <- Map.lookup pid children
  -- = undefined
  -- | Nothing <- insertInWeave weave pid atom1
  -- = Nothing === insertInWeave weave pid atom1 === Just wop1 *** QED
  -- | Nothing <- insertInWeave weave pid atom2
  -- = Nothing === insertInWeave weave pid atom2 === Just wop2 *** QED
  -- | Just (a:as) <- Map.lookup pid children
  -- = Nothing ==. Just (a:as) ==. Just [] *** QED


-- {-@ lawCommutativityEq :: Ord id => x : CausalTree id a -> op1 : CausalTreeOp id a -> {op2 : CausalTreeOp id a | causalTreeOpParent op1 == causalTreeOpParent op2 && (compatible op1 op2 && compatibleState x op1 && compatibleState x op2)} -> {apply (apply x op1) op2 == apply (apply x op2) op1} @-}
-- lawCommutativityEq :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
-- lawCommutativityEq x@(CausalTree (CausalTreeWeave ctAtom weaveChildren) pending) op1@(CausalTreeOp pid1 (CausalTreeAtom id1 l1)) op2@(CausalTreeOp pid2 (CausalTreeAtom id2 l2))
--   -- id1 /= id2
--   -- pid1 == pid2
--   | Nothing <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
--   =   lemmaInsertInWeaveNothingEq
--         (CausalTreeWeave ctAtom weaveChildren)
--         pid1
--         (CausalTreeAtom id1 l1)
--         (CausalTreeAtom id2 l2)
--   &&& lemmaInsertPendingTwice pid1 (CausalTreeAtom id1 l1) (CausalTreeAtom id2 l2) pending
--   &&& (apply (apply x op1) op2
--   ==. apply (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)) op2
--   ==. CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid2 (CausalTreeAtom id2 l2) (insertPending pid1 (CausalTreeAtom id1 l1) pending))
--   ==. CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id2 l2) (insertPending pid1 (CausalTreeAtom id1 l1) pending))
--   ==. apply (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid2 (CausalTreeAtom id2 l2) pending)) op1
--   ==. apply (apply x op2) op1
--   *** QED)
--   | Nothing <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
--   , Just _ <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
--   =  lemmaInsertInWeaveNothingEq
--         (CausalTreeWeave ctAtom weaveChildren)
--         pid2
--         (CausalTreeAtom id2 l2)
--         (CausalTreeAtom id1 l1)

--   | Just wop1 <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
--   , Just wop2 <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
--   , Nothing <- id1pendingM
--   , Nothing <- id2pendingM
--   =    (Map.updateLookupWithKey constConstNothing id1 pending
--       ? lemmaLookupDelete2 pending id1 id2
--       ? lemmaLookupDelete2 pending id2 id1
--   ==. (Nothing, pending)
--   *** QED) &&&
--     ( apply x op1
--   ==. applyAtom x pid1 (CausalTreeAtom id1 l1)
--   ==. CausalTree wop1 pending
--   ==. List.foldl' (applyAtomHelper id1) (CausalTree wop1 pending) []
--   *** QED) &&&
--   ( Map.updateLookupWithKey constConstNothing id2 pending
--   ==. (Nothing, pending)
--   *** QED) &&&
--     ( apply x op2
--   ==. applyAtom x pid2 (CausalTreeAtom id2 l2)
--   ==. CausalTree wop2 pending
--   ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2
--                                           pending)
--                                           []
--   *** QED) &&&
--     ( apply (apply x op1) op2
--     ? lemmaInsertInWeaveJustEq
--         (CausalTreeWeave ctAtom weaveChildren)
--         pid1
--         wop1
--         wop2
--         (CausalTreeAtom id1 l1)
--         (CausalTreeAtom id2 l2)
--   ==. (let Just wop1op2 = insertInWeave wop1 pid2 (CausalTreeAtom id2 l2)
--            Just wop2op1 = insertInWeave wop2 pid1 (CausalTreeAtom id1 l1) in
--       applyAtom (CausalTree wop1 pending) pid2 (CausalTreeAtom id2 l2)
--   ==. CausalTree wop1op2 pending
--   ==. CausalTree wop2op1 pending
--   ==. applyAtom (CausalTree wop2 pending) pid1 (CausalTreeAtom id1 l1))
--   *** QED)


--   | Just wop1 <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
--   , Just wop2 <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
--   , Just pops1 <- id1pendingM
--   , Nothing <- id2pendingM
--   =   (Map.updateLookupWithKey constConstNothing id1 pending
--       ? lemmaLookupDelete2 pending id1 id2
--       ? lemmaLookupDelete2 pending id2 id1
--   ==. (Nothing, pending)
--   *** QED) &&&
--     ( apply x op1
--   ==. applyAtom x pid1 (CausalTreeAtom id1 l1)
--   ==. List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1
--   *** QED) &&&
--   ( Map.updateLookupWithKey constConstNothing id2 pending
--   ==. (Nothing, pending)
--   *** QED) &&&
--     ( apply x op2
--   ==. applyAtom x pid2 (CausalTreeAtom id2 l2)
--   ==. CausalTree wop2 pending
--   ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2
--                                           pending)
--                                           []
--   *** QED) &&&
--     ( apply (apply x op1) op2
--     ? lemmaInsertInWeaveJustEq
--         (CausalTreeWeave ctAtom weaveChildren)
--         pid1
--         wop1
--         wop2
--         (CausalTreeAtom id1 l1)
--         (CausalTreeAtom id2 l2)
--   ==. (let Just wop1op2 = insertInWeave wop1 pid2 (CausalTreeAtom id2 l2)
--            Just wop2op1 = insertInWeave wop2 pid1 (CausalTreeAtom id1 l1)
--            -- CausalTree a b = apply (apply x op1) op2 
--        in
--       apply (apply x op1) op2
--       ? (List.foldl' (applyAtomHelper pid2) (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1) [CausalTreeAtom id2 l2]
--      ==. List.foldl' (applyAtomHelper pid2) (applyAtomHelper pid2 (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1) (CausalTreeAtom id2 l2)) []
--      ==. applyAtomHelper pid2 (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1) (CausalTreeAtom id2 l2)
--      *** QED)
--   ==. applyAtom (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1)
--         pid2 (CausalTreeAtom id2 l2)
--   ==. List.foldl' (applyAtomHelper pid2) (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1) [CausalTreeAtom id2 l2]
--       ? lemmaApplyAtomFoldNeq (CausalTree wop1 (Map.delete id1 pending)) id1 pid2 pops1 [CausalTreeAtom id2 l2]
--   ==. List.foldl' (applyAtomHelper id1) (List.foldl' (applyAtomHelper pid2) (CausalTree wop1 (Map.delete id1 pending)) [CausalTreeAtom id2 l2]) pops1
--   ==. List.foldl' (applyAtomHelper id1) (applyAtom (CausalTree wop1 (Map.delete id1 pending)) pid2 (CausalTreeAtom id2 l2)) pops1
--       ? (Map.lookup id2 (Map.delete id1 pending) === Nothing *** QED)
--       ? ( applyAtom (CausalTree wop1 (Map.delete id1 pending)) pid2 (CausalTreeAtom id2 l2)
--           ? assert (isJust $ insertInWeave wop1 pid2 (CausalTreeAtom id2 l2))
--           ? ( Map.updateLookupWithKey constConstNothing id2 (Map.delete id1 pending)
--           ==. (Nothing, Map.delete id1 pending)
--           *** QED)
--       ==. CausalTree wop1op2 (Map.delete id1 pending)
--       *** QED)
--   ==. List.foldl' (applyAtomHelper id1) (CausalTree wop1op2 (Map.delete id1 pending)) pops1
--       )
--   ==. apply (apply x op2) op1
--   *** QED)
--   | Just wop1 <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
--   , Just wop2 <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
--   , Nothing <- id1pendingM
--   , Just pops2 <- id2pendingM
--   =   (Map.updateLookupWithKey constConstNothing id2 pending
--       ? lemmaLookupDelete2 pending id2 id1
--       ? lemmaLookupDelete2 pending id1 id2
--   ==. (Nothing, pending)
--   *** QED) &&&
--     ( apply x op2
--   ==. applyAtom x pid2 (CausalTreeAtom id2 l2)
--   ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2
--   *** QED) &&&
--   ( Map.updateLookupWithKey constConstNothing id1 pending
--   ==. (Nothing, pending)
--   *** QED) &&&
--     ( apply x op1
--   ==. applyAtom x pid1 (CausalTreeAtom id1 l1)
--   ==. CausalTree wop1 pending
--   ==. List.foldl' (applyAtomHelper id1) (CausalTree wop1
--                                           pending)
--                                           []
--   *** QED) &&&
--     ( apply (apply x op2) op1
--     ? lemmaInsertInWeaveJustEq
--         (CausalTreeWeave ctAtom weaveChildren)
--         pid2
--         wop2
--         wop1
--         (CausalTreeAtom id2 l2)
--         (CausalTreeAtom id1 l1)
--   ==. (let Just wop2op1 = insertInWeave wop2 pid1 (CausalTreeAtom id1 l1)
--            Just wop1op2 = insertInWeave wop1 pid2 (CausalTreeAtom id2 l2)
--            -- CausalTree a b = apply (apply x op2) op1 
--        in
--       apply (apply x op2) op1
--       ? (List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
--      ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)) []
--      ==. applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)
--      *** QED)
--   ==. applyAtom (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2)
--         pid1 (CausalTreeAtom id1 l1)
--   ==. List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
--       ? lemmaApplyAtomFoldNeq (CausalTree wop2 (Map.delete id2 pending)) id2 pid1 pops2 [CausalTreeAtom id1 l1]
--   ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper pid1) (CausalTree wop2 (Map.delete id2 pending)) [CausalTreeAtom id1 l1]) pops2
--   ==. List.foldl' (applyAtomHelper id2) (applyAtom (CausalTree wop2 (Map.delete id2 pending)) pid1 (CausalTreeAtom id1 l1)) pops2
--       ? (Map.lookup id1 (Map.delete id2 pending) === Nothing *** QED)
--       ? ( applyAtom (CausalTree wop2 (Map.delete id2 pending)) pid1 (CausalTreeAtom id1 l1)
--           ? assert (isJust $ insertInWeave wop2 pid1 (CausalTreeAtom id1 l1))
--           ? ( Map.updateLookupWithKey constConstNothing id1 (Map.delete id2 pending)
--           ==. (Nothing, Map.delete id2 pending)
--           *** QED)
--       ==. CausalTree wop2op1 (Map.delete id2 pending)
--       *** QED)
--   ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2op1 (Map.delete id2 pending)) pops2
--       )
--   ==. apply (apply x op1) op2
--   *** QED)
--   | Just wop1 <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
--   , Just wop2 <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
--   , Just pops1 <- id1pendingM
--   , Just pops2 <- id2pendingM
--   =   (Map.updateLookupWithKey constConstNothing id2 pending
--       ? constConstNothing id2 pops2
--       ? lemmaLookupDelete2 pending id2 id1
--       ? lemmaLookupDelete2 pending id1 id2
--   ==. (Just pops2, Map.delete id2 pending)
--   *** QED) &&&
--     ( apply x op2
--   ==. applyAtom x pid2 (CausalTreeAtom id2 l2)
--   ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2
--   *** QED) &&&
--   ( Map.updateLookupWithKey constConstNothing id1 pending
--   ? constConstNothing id1 pops1
--   ==. (Just pops1, Map.delete id1 pending)
--   *** QED) &&&
--     ( apply x op1
--   ==. applyAtom x pid1 (CausalTreeAtom id1 l1)
--   ==. List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1
--   *** QED) &&&

--     ( apply (apply x op2) op1
--     ? lemmaInsertInWeaveJustEq
--         (CausalTreeWeave ctAtom weaveChildren)
--         pid2
--         wop2
--         wop1
--         (CausalTreeAtom id2 l2)
--         (CausalTreeAtom id1 l1)
--   ==. (let Just wop2op1 = insertInWeave wop2 pid1 (CausalTreeAtom id1 l1)
--            Just wop1op2 = insertInWeave wop1 pid2 (CausalTreeAtom id2 l2)
--            -- CausalTree a b = apply (apply x op2) op1 
--        in
--       apply (apply x op2) op1

--       -- explicit unfolding for foldl'
--       ? (List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
--      ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)) []
--      ==. applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)
--      *** QED)
      
--   ==. applyAtom (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2)
--         pid1 (CausalTreeAtom id1 l1)

--   ==. List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
--       ? lemmaApplyAtomFoldNeq (CausalTree wop2 (Map.delete id2 pending)) id2 pid1 pops2 [CausalTreeAtom id1 l1]
--   ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper pid1) (CausalTree wop2 (Map.delete id2 pending)) [CausalTreeAtom id1 l1]) pops2
--   ==. List.foldl' (applyAtomHelper id2)
--         (applyAtom (CausalTree wop2 (Map.delete id2 pending)) pid1 (CausalTreeAtom id1 l1)) pops2
--       ? (Map.lookup id1 (Map.delete id2 pending) ==. Just pops1 *** QED)
--       ? ( applyAtom (CausalTree wop2 (Map.delete id2 pending)) pid1 (CausalTreeAtom id1 l1)
--           ? assert (isJust $ insertInWeave wop2 pid1 (CausalTreeAtom id1 l1))
--           ? ( Map.updateLookupWithKey constConstNothing id1 (Map.delete id2 pending)
--           ==. (Just pops1, Map.delete id1 (Map.delete id2 pending))
--           *** QED)
--       ==. List.foldl'
--             (applyAtomHelper id1)
--             (CausalTree wop2op1 (Map.delete id1 (Map.delete id2 pending)))
--             pops1
--       *** QED)
--       ? lemmaDelete id1 id2 pending

--       ? (List.foldl' (applyAtomHelper pid2) (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1) [CausalTreeAtom id2 l2]
--      ==. List.foldl' (applyAtomHelper pid2) (applyAtomHelper pid2 (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1) (CausalTreeAtom id2 l2)) []
--      ==. applyAtomHelper pid2 (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1) (CausalTreeAtom id2 l2)
--      *** QED)

--       -- ? (wop1op2 === wop2op1 *** QED)
--       -- ? (Map.delete id2 (Map.delete id1 pending) === Map.delete id1 (Map.delete id2 pending) *** QED)

--       ? (Map.lookup id2 (Map.delete id1 pending) ==. Just pops2 *** QED)
--       ? ( applyAtom (CausalTree wop1 (Map.delete id1 pending)) pid2 (CausalTreeAtom id2 l2)
--           ? assert (isJust $ insertInWeave wop1 pid2 (CausalTreeAtom id2 l2))
--           ? ( Map.updateLookupWithKey constConstNothing id2 (Map.delete id1 pending)
--           ==. (Just pops2, Map.delete id2 (Map.delete id1 pending))
--           *** QED)
--       ==. List.foldl'
--             (applyAtomHelper id2)
--             (CausalTree wop1op2 (Map.delete id2 (Map.delete id1 pending)))
--             pops2
--       *** QED)

--       ? lemmaApplyAtomFoldNeq (CausalTree wop1 (Map.delete id1 pending)) id1 pid2 pops1 [CausalTreeAtom id2 l2]
--   ==. (List.foldl' (applyAtomHelper id2)
--         (List.foldl'
--           (applyAtomHelper id1)
--           (CausalTree wop2op1 (Map.delete id1 (Map.delete id2 pending)))
--           pops1) pops2

--       ? lemmaApplyAtomFoldNeq
--         (CausalTree wop2op1 (Map.delete id1 (Map.delete id2 pending))) id1 id2 pops1 pops2

--   ==. List.foldl' (applyAtomHelper id1)
--         (List.foldl'
--           (applyAtomHelper id2)
--           (CausalTree wop2op1 (Map.delete id1 (Map.delete id2 pending)))
--           pops2) pops1)

--   ==. List.foldl' (applyAtomHelper id1)
--         (List.foldl'
--           (applyAtomHelper id2)
--           (CausalTree wop1op2 (Map.delete id2 (Map.delete id1 pending)))
--           pops2) pops1

--   ==. List.foldl' (applyAtomHelper id1) (applyAtom (CausalTree wop1 (Map.delete id1 pending)) pid2 (CausalTreeAtom id2 l2)) pops1

--   ==. List.foldl' (applyAtomHelper id1) (List.foldl' (applyAtomHelper pid2) (CausalTree wop1 (Map.delete id1 pending)) [CausalTreeAtom id2 l2]) pops1

--   ==. List.foldl' (applyAtomHelper pid2) (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1) [CausalTreeAtom id2 l2]

--   ==. applyAtom (List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 pending)) pops1)
--         pid2 (CausalTreeAtom id2 l2)

--       )
    
--   ==. apply (apply x op1) op2
--   *** QED)
--   where id2pendingM = Map.lookup id2 pending
--         id1pendingM = Map.lookup id1 pending
