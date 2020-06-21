{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}
module VRDT.CausalTree.NEq where

import VRDT.CausalTree.Internal
import qualified Liquid.Data.List              as List
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Liquid.Data.Map.Props
import           VRDT.Internal
import           VRDT.CausalTree.Lemmas
import           Liquid.Data.Maybe
import           Prelude                 hiding ( Maybe(..)
                                                , empty
                                                )
import           Liquid.ProofCombinators
import           ProofCombinators
{-@ lemmaApplyAtomFoldNeq :: Ord id
 => ct:CausalTree id a
 -> opid1:id
 -> {opid2:id | opid1 /= opid2}
 -> atoms1:[CausalTreeAtom id a]
 -> atoms2:[CausalTreeAtom id a]
 -> {  (List.foldl' (applyAtomHelper opid2) (List.foldl' (applyAtomHelper opid1) ct atoms1) atoms2)
    == (List.foldl' (applyAtomHelper opid1) (List.foldl' (applyAtomHelper opid2) ct atoms2) atoms1)} @-}
lemmaApplyAtomFoldNeq :: Ord id
 => CausalTree id a
 -> id
  -> id
 -> [CausalTreeAtom id a]
 -> [CausalTreeAtom id a]
 -> ()
lemmaApplyAtomFoldNeq = undefined

{-@ lawCommutativityNEq :: Ord id => x : CausalTree id a -> op1 : CausalTreeOp id a -> {op2 : CausalTreeOp id a | causalTreeOpParent op1 /= causalTreeOpParent op2 && (compatible op1 op2 && compatibleState x op1 && compatibleState x op2)} -> {apply (apply x op1) op2 == apply (apply x op2) op1} @-}
lawCommutativityNEq :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEq 
  x@(CausalTree (CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 (CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 (CausalTreeAtom id2 l2))
  -- case when two operations are unrelated
  -- | Nothing <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  -- , Nothing <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  -- = ( apply x op1
  -- ==. CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)
  -- *** QED)
  -- &&& ( apply x op2
  -- ==. CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid2 (CausalTreeAtom id2 l2) pending)
  -- *** QED)
  -- &&& lemmaInsertPendingTwiceNEq pid1 pid2 (CausalTreeAtom id1 l1) (CausalTreeAtom id2 l2) pending
  -- | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  -- , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  -- , Nothing <- Map.lookup id2 pending
  -- , pid1 /= id2 && pid2 /= id1
  -- = ( apply x op1
  -- ==. CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)
  -- *** QED) &&&
  -- (   Map.updateLookupWithKey constConstNothing id2 pending
  -- ==. (Nothing, pending)
  -- *** QED) &&&
  -- ( apply x op2
  -- ==. applyAtom x pid2 (CausalTreeAtom id2 l2)
  -- ==. CausalTree wop2 pending
  -- *** QED) &&&
  -- lemmaLookupDelete2 pending id1 id2 &&&
  -- lemmaLookupDelete2 pending id2 id1 &&&
  -- (   apply (apply x op1) op2
  -- ==. apply (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)) op2
  --     ? lemmaInsertPendingLookup id2 pid1 (CausalTreeAtom id1 l1) pending
  --     ? (Map.lookup id2 (insertPending pid1 (CausalTreeAtom id1 l1) pending) ==. Nothing *** QED)
  -- ==. applyAtom (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)) pid2 (CausalTreeAtom id2 l2)
  --     ? (  Map.updateLookupWithKey constConstNothing id2
  --          (insertPending pid1 (CausalTreeAtom id1 l1) pending)
  --      ==. (Nothing, insertPending pid1 (CausalTreeAtom id1 l1) pending)
  --      *** QED)
  -- ==. CausalTree wop2 (insertPending pid1 (CausalTreeAtom id1 l1) pending)
  --     ? lemmaInsertInWeaveJustNEq (CausalTreeWeave ctAtom weaveChildren) pid1 pid2 wop2 (CausalTreeAtom id1 l1) (CausalTreeAtom id2 l2)
  -- ==. apply (CausalTree wop2 pending) op1
  -- ==. apply (apply x op2) op1
  -- *** QED)
  | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  , Just pops2 <- Map.lookup id2 pending
  , pid1 /= id2 && pid2 /= id1
  = (   Map.updateLookupWithKey constConstNothing id2 pending
    ? constConstNothing id2 pops2
  ==. (Just pops2, Map.delete id2 pending)
  *** QED) &&&
  ( apply x op2
  ==. applyAtom x pid2 (CausalTreeAtom id2 l2)
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2
  *** QED) &&&
  lemmaLookupDelete2 pending id1 id2 &&&
  lemmaLookupDelete2 pending id2 id1 &&&
  lemmaLookupDelete2 pending pid1 id2 &&&
  (      List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
     ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)) []
     ==. applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)
     ==.  apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) op1
     *** QED) &&&
  ( apply x op1
  ==. CausalTree
       (CausalTreeWeave ctAtom weaveChildren)
       (insertPending pid1 (CausalTreeAtom id1 l1) pending)
  *** QED) &&&
  lemmaLookupInsert2 pending id2 pid1 pid1pending' &&&
  lemmaInsertDelete pid1 pid1pending' id2 pending &&&
  (   apply (apply x op1) op2
  ==. apply (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)) op2
      -- prove this new lemma
      -- can be easily proved using the lemmas
      -- ? lemmaInsertDeletePending
  ==. applyAtom (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)) pid2 (CausalTreeAtom id2 l2)
      ? (  Map.updateLookupWithKey constConstNothing id2
           (    insertPending pid1 (CausalTreeAtom id1 l1) pending
            ==. Map.insert pid1 pid1pending' pending)
       ==. (Just pops2, Map.delete id2 (insertPending pid1 (CausalTreeAtom id1 l1) pending))
       ==. (Just pops2, insertPending pid1 (CausalTreeAtom id1 l1) (Map.delete id2 pending)
                    ==. Map.insert pid1 pid1pending' (Map.delete id2 pending))
       *** QED)
  ==.  List.foldl' (applyAtomHelper id2) (CausalTree wop2 (insertPending pid1 (CausalTreeAtom id1 l1) (Map.delete pid2 pending))) pops2
      ? lemmaInsertInWeaveJustNEq (CausalTreeWeave ctAtom weaveChildren) pid1 pid2 wop2 (CausalTreeAtom id1 l1) (CausalTreeAtom id2 l2)
      -- another delete/insert/lookup lemma

  ==.  List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
  ==.  List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper pid1) (CausalTree wop2 (Map.delete id2 pending)) [CausalTreeAtom id1 l1]) pops2
      ? lemmaApplyAtomFoldNeq (CausalTree wop2 (Map.delete id2 pending)) id2 pid1 pops2 [CausalTreeAtom id1 l1]
  ==.  apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) op1
  ==. apply (apply x op2) op1
  *** QED)
  | otherwise
  = undefined
  where id2pendingM = Map.lookup id2 pending
        id1pendingM = Map.lookup id1 pending
        pid1pending' = case Map.lookup pid1 pending of
                        Nothing -> [CausalTreeAtom id1 l1]
                        Just pops1 -> insertList (CausalTreeAtom id1 l1) pops1

