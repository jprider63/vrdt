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

{-@ lawCommutativityNEq :: Ord id => x : CausalTree id a -> op1 : CausalTreeOp id a -> {op2 : CausalTreeOp id a | causalTreeOpParent op1 /= causalTreeOpParent op2} -> {(compatible op1 op2 && compatibleState x op1 && compatibleState x op2) => apply (apply x op1) op2 == apply (apply x op2) op1} @-}
lawCommutativityNEq :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEq 
  x@(CausalTree (CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 (CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 (CausalTreeAtom id2 l2))
  -- case when two operations are unrelated
  | pid1 /= id2 && pid2 /= id1 && pid1 /= id1 && pid2 /= id2
  , Nothing <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Nothing <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  =    undefined -- lemmaInsertInWeaveNothingEq
  | otherwise
  = undefined
  where id2pendingM = Map.lookup id2 pending
        id1pendingM = Map.lookup id1 pending

