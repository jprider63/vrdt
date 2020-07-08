{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--noadt" @-}
module VRDT.CausalTree.NEq where

import VRDT.CausalTree.Internal
import qualified Liquid.Data.List              as List
import           Liquid.Data.List.Props
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
import qualified Data.Set as S

--{-@ ple lemmaApplyAtomFoldNeq @-}
{-@ lemmaApplyAtomFoldNeq :: Ord id
 => {ct:CausalTree id a | idUniqueCausalTree ct}
 -> {opid1:id | S.member opid1 (weaveIds (causalTreeWeave ct))}
 -> {opid2:id | S.member opid2 (weaveIds (causalTreeWeave ct)) && opid1 /= opid2}
 -> {atoms1:[CausalTreeAtom id a] | idUniqueList atoms1 && S.null (S.intersection (pendingListIds atoms1) (causalTreeIds ct))}
 -> {atoms2:[CausalTreeAtom id a] | idUniqueList atoms2 && S.null (S.intersection (pendingListIds atoms1) (pendingListIds atoms2)) && S.null (S.intersection (pendingListIds atoms2) (causalTreeIds ct))}
 -> {  ((List.foldl' (applyAtomHelper opid2) (List.foldl' (applyAtomHelper opid1) ct atoms1) atoms2)
   == (List.foldl' (applyAtomHelper opid1) (List.foldl' (applyAtomHelper opid2) ct atoms2) atoms1))
     } / [causalTreePendingSize ct, 1, List.length atoms1 + List.length atoms2]  @-}

lemmaApplyAtomFoldNeq :: forall id a. Ord id
 => CausalTree id a
 -> id
  -> id
 -> [CausalTreeAtom id a]
 -> [CausalTreeAtom id a]
 -> ()
lemmaApplyAtomFoldNeq ct opid1 opid2 atoms1 [] =
      List.foldl' (applyAtomHelper opid2) (List.foldl' (applyAtomHelper opid1) ct atoms1) []
  ==. (List.foldl' (applyAtomHelper opid1) ct atoms1)
  ==. List.foldl' (applyAtomHelper opid1) (List.foldl' (applyAtomHelper opid2) ct []) atoms1
  *** QED
lemmaApplyAtomFoldNeq ct opid1 opid2 [] atoms2 =
      List.foldl' (applyAtomHelper opid1) (List.foldl' (applyAtomHelper opid2) ct atoms2) []
  ==. (List.foldl' (applyAtomHelper opid2) ct atoms2)
  ==. List.foldl' (applyAtomHelper opid2) (List.foldl' (applyAtomHelper opid1) ct []) atoms2
  *** QED
lemmaApplyAtomFoldNeq ct@(CausalTree weave pending) opid1 opid2 (atom1@(CausalTreeAtom aid1 _):atoms1) [atom2@(CausalTreeAtom aid2 _)] =
 -- assert (List.length atoms1 + List.length [atom2] <= List.length atoms1 + List.length ) &&&
 (compatible (CausalTreeOp opid1 atom1) (CausalTreeOp opid2 atom2)
 ==. aid1 /= aid2
 *** QED) &&&
 (pendingListIds [atom2]
 `cast` pendingListIds ([] :: [CausalTreeAtom id a])
 *** QED) &&&
 (compatibleState ct (CausalTreeOp opid1 atom1)
 ==. (not (aid1 `S.member ` causalTreeIds ct) && idUniqueCausalTree ct)
 *** QED) &&&
 (compatibleState ct (CausalTreeOp opid2 atom2)
 ==. (not (aid2 `S.member ` causalTreeIds ct) && idUniqueCausalTree ct)
 *** QED) &&&
 toProof (insertInWeave weave opid1 atom1) &&&
 toProof (insertInWeave weave opid2 atom2) &&&
 (List.foldl' (applyAtomHelper opid2) (applyAtom ct opid1 atom1) [atom2]
 ==. List.foldl' (applyAtomHelper opid2) (applyAtomHelper opid2 (applyAtom ct opid1 atom1) atom2) []
 ==. applyAtomHelper opid2 (applyAtom ct opid1 atom1) atom2
 ==. applyAtom (applyAtom ct opid1 atom1 )  opid2 atom2
 ==. applyAtom (apply ct (CausalTreeOp opid1 atom1)) opid2 atom2
 ==. apply (apply ct (CausalTreeOp opid1 atom1)) (CausalTreeOp opid2 atom2)
 ==. apply (apply ct (CausalTreeOp opid2 atom2)) (CausalTreeOp opid1 atom1)
 ==. applyAtom (applyAtom ct opid2 atom2) opid1 atom1
 *** QED) &&&
  (List.foldl' (applyAtomHelper opid2) ct [atom2]
  ==. List.foldl' (applyAtomHelper opid2) (applyAtomHelper opid2 ct atom2) []
  ==. applyAtom ct opid2 atom2
  *** QED) &&&
  toProof (pendingListIds (atom1:atoms1) `cast` pendingListIds atoms1) &&&
  lemmaApplyAtomIds' ct opid1 atom1 &&&
  assert (causalTreePendingSize (applyAtom ct opid1 atom1) <= causalTreePendingSize ct) &&&
  toProof (idUniqueList (atom1:atoms1) `cast` idUniqueList atoms1) &&&
  (List.foldl' (applyAtomHelper opid2) (List.foldl' (applyAtomHelper opid1) ct (atom1:atoms1)) [atom2]
  ==. List.foldl' (applyAtomHelper opid2) (List.foldl' (applyAtomHelper opid1) (applyAtomHelper opid1 ct atom1) atoms1) [atom2]
  ==. List.foldl' (applyAtomHelper opid2) (List.foldl' (applyAtomHelper opid1) (applyAtom ct opid1 atom1) atoms1) [atom2]
    ? lemmaApplyAtomFoldNeq (applyAtom ct opid1 atom1) opid1 opid2 atoms1 [atom2]
  ==. List.foldl' (applyAtomHelper opid1) (List.foldl' (applyAtomHelper opid2) (applyAtom ct opid1 atom1) [atom2]) atoms1
  ==. List.foldl' (applyAtomHelper opid1) (applyAtom (applyAtom ct opid1 atom1 )  opid2 atom2) atoms1
    ? causalTreePendingSize ct
    ? lawCommutativityNEqJJ ct (CausalTreeOp opid1 atom1) (CausalTreeOp opid2 atom2)
  ==. List.foldl' (applyAtomHelper opid1) (applyAtom (applyAtom ct opid2 atom2 )  opid1 atom1) atoms1
  ==. List.foldl' (applyAtomHelper opid1) (applyAtomHelper opid1 (applyAtom ct opid2 atom2 ) atom1) atoms1
  ==. List.foldl' (applyAtomHelper opid1) (applyAtom ct opid2 atom2 ) (atom1:atoms1)
  *** QED)
lemmaApplyAtomFoldNeq ct opid1 opid2 atoms1 (atom2@(CausalTreeAtom aid2 _):atoms2@(_:_)) =
  (atom2:atoms2
  ==. atom2:List.concat [] atoms2
  ==. List.concat [atom2] atoms2
  *** QED) &&&
  toProof (causalTreePendingSize ct >=
           causalTreePendingSize (List.foldl' (applyAtomHelper opid2) ct [atom2])) &&&
  toProof (List.length atoms1 + List.length atoms2) &&&
  toProof (List.length atoms1 + List.length [atom2] < List.length atoms1 + List.length (atom2:atoms2)) &&&
  toProof (List.length atoms1 + List.length [atom2] > 0) &&&
  toProof (pendingListIds [atom2] `cast` (pendingListIds ([] :: [CausalTreeAtom id a]))) &&&
  toProof (idUniqueList [atom2] `cast` idUniqueList ([] :: [CausalTreeAtom id a])) &&&
  toProof (idUniqueList (atom2:atoms2)) &&&
  toProof (idUniqueList atoms2) &&&
  toProof (idUniqueList atoms1) &&&
  toProof (pendingListIds (atom2:atoms2)) &&&
  toProof (pendingListIds atoms2) &&&
  toProof (causalTreeIds ct) &&&
  toProof (causalTreeIds (List.foldl' (applyAtomHelper opid2) ct [atom2])) &&&
  (
      List.foldl' (applyAtomHelper opid2) (List.foldl' (applyAtomHelper opid1) ct atoms1) (List.concat [atom2] atoms2)
      ? lemmaFoldlConcat (applyAtomHelper opid2) (List.foldl' (applyAtomHelper opid1) ct atoms1) [atom2] atoms2
  ==. List.foldl' (applyAtomHelper opid2)
       (List.foldl' (applyAtomHelper opid2) 
         (List.foldl' (applyAtomHelper opid1) ct atoms1) [atom2]) atoms2
      ? lemmaFoldlIds ct opid1 atoms1
      ? lemmaApplyAtomFoldNeq ct opid1 opid2 atoms1 [atom2]
  ==. List.foldl' (applyAtomHelper opid2)
       (List.foldl' (applyAtomHelper opid1) 
         (List.foldl' (applyAtomHelper opid2) ct [atom2]) atoms1) atoms2
      ? lemmaFoldlIds ct opid2 [atom2]
      ? applyAtomFoldlRespectsUniq ct opid2 [atom2]
      ? lemmaApplyAtomFoldNeq (List.foldl' (applyAtomHelper opid2) ct [atom2]) opid1 opid2 atoms1 atoms2
  ==. List.foldl' (applyAtomHelper opid1)
       (List.foldl' (applyAtomHelper opid2) 
         (List.foldl' (applyAtomHelper opid2) ct [atom2]) atoms2
      ? lemmaFoldlConcat (applyAtomHelper opid2) ct [atom2] atoms2
  ==. (List.foldl' (applyAtomHelper opid2) ct (List.concat [atom2] atoms2 === atom2:atoms2))) atoms1
  *** QED)
  

{-@ ple lawCommutativityNEqNN @-}
{-@ lawCommutativityNEqNN :: Ord id =>
     x : CausalTree id a
  -> op1 : CausalTreeOp id a
  -> {op2 : CausalTreeOp id a |
        causalTreeOpParent op1 /= causalTreeOpParent op2 &&
        (compatible op1 op2 && compatibleState x op1 && compatibleState x op2) &&
        (Nothing == (insertInWeave (causalTreeWeave x) (causalTreeOpParent op1) (causalTreeOpAtom op1))) &&
        (Nothing == (insertInWeave (causalTreeWeave x) (causalTreeOpParent op2) (causalTreeOpAtom op2)))}
  -> {apply (apply x op1) op2 == apply (apply x op2) op1} @-}
lawCommutativityNEqNN :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEqNN
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 (CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 (CausalTreeAtom id2 l2))
  -- case when two operations are unrelated
  | Nothing <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Nothing <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  = ( apply x op1
  ==. CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)
  *** QED)
  &&& ( apply x op2
  ==. CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid2 (CausalTreeAtom id2 l2) pending)
  *** QED)
  &&& lemmaInsertPendingTwiceNEq pid1 pid2 (CausalTreeAtom id1 l1) (CausalTreeAtom id2 l2) pending

{-@ reflect listLast @-}
{-@ ple listLast  @-}
{-@ listLast :: {x:[a] | List.length x > 0} -> (xs::[a],{y:a | List.concat xs (cons y []) == x}) @-}
listLast :: [a] -> ([a], a)
listLast [x] = ([],x)
listLast (x:xs@(_:_)) =
  let (xs', l) = listLast xs in
    (x:xs', l)
    
{-@ reflect cons @-}
cons :: a -> [a] -> [a]
cons x xs = x:xs

{-@ lawCommutatiityNEqNJFoldl :: Ord id =>
     x : CausalTree id a
  -> {pid1 : id | not (S.member pid1 (weaveIds (causalTreeWeave x)))}
  -> atom1 : {CausalTreeAtom id a | not (S.member (causalTreeAtomId atom1) (causalTreeIds x))}
  -> {pid2 : id  | pid1 /= pid2}
  -> atoms2 : {[CausalTreeAtom id a] | idUniqueList atoms2 && not (S.member (causalTreeAtomId atom1) (pendingListIds atoms2)) && (S.null (S.intersection (pendingListIds atoms2) (causalTreeIds x)))}
  -> {List.foldl' (applyAtomHelper pid2) (applyAtom x pid1 atom1) atoms2 == applyAtom (List.foldl' (applyAtomHelper pid2) x atoms2) pid1 atom1}
  / [causalTreePendingSize x, 1, List.length atoms2] @-}
lawCommutatiityNEqNJFoldl :: Ord id =>
     CausalTree id a
  -> id
  -> CausalTreeAtom id a
  -> id
  -> [CausalTreeAtom id a]
  -> ()
lawCommutatiityNEqNJFoldl
  ct@(CausalTree weave children)
  pid1
  atom1@(CausalTreeAtom id1 _)
  pid2 
  atoms2
  = undefined

{-@ lawCommutativityNEqNJBoth :: Ord id =>
     x : CausalTree id a
  -> op1 : CausalTreeOp id a
  -> {op2 : CausalTreeOp id a |
        causalTreeOpParent op1 /= causalTreeOpParent op2 &&
        (compatible op1 op2 && compatibleState x op1 && compatibleState x op2) &&
        (Nothing == (insertInWeave (causalTreeWeave x) (causalTreeOpParent op1) (causalTreeOpAtom op1))) &&
        (isJust (insertInWeave (causalTreeWeave x) (causalTreeOpParent op2) (causalTreeOpAtom op2)))}
  -> {apply (apply x op1) op2 == apply (apply x op2) op1}
  / [causalTreePendingSize x, 1] @-}
lawCommutativityNEqNJBoth :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEqNJBoth
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 atom1@(CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 atom2@(CausalTreeAtom id2 l2))
  | pid1 /= id2
  = lawCommutativityNEqNJ x op1 op2
  | otherwise
  = lawCommutativityNEqNJ' x op1 op2

--{-@ ple lawCommutativityNEqNJ @-}
{-@ lawCommutativityNEqNJ :: Ord id =>
     x : CausalTree id a
  -> op1 : CausalTreeOp id a
  -> {op2 : CausalTreeOp id a |
        causalTreeOpParent op1 /= causalTreeOpParent op2 &&
        (compatible op1 op2 && compatibleState x op1 && compatibleState x op2) &&
        (Nothing == (insertInWeave (causalTreeWeave x) (causalTreeOpParent op1) (causalTreeOpAtom op1))) &&
        (isJust (insertInWeave (causalTreeWeave x) (causalTreeOpParent op2) (causalTreeOpAtom op2))) &&
        (causalTreeOpParent op1 /= causalTreeAtomId (causalTreeOpAtom op2))}
  -> {apply (apply x op1) op2 == apply (apply x op2) op1}
  / [causalTreePendingSize x, 0] @-}
lawCommutativityNEqNJ :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEqNJ
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 atom1@(CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 atom2@(CausalTreeAtom id2 l2))
  | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  , Nothing <- Map.lookup id2 pending
  , pid1 /= id2
  = ( apply x op1
  ==. CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)
  *** QED) &&&
  (   Map.updateLookupWithKey constConstNothing id2 pending
  ==. (Nothing, pending)
  *** QED) &&&
  ( apply x op2
  ==. applyAtom x pid2 (CausalTreeAtom id2 l2)
  ==. CausalTree wop2 pending
  *** QED) &&&
  lemmaLookupDelete2 pending id1 id2 &&&
  lemmaLookupDelete2 pending id2 id1 &&&
  (   apply (apply x op1) op2
  ==. apply (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)) op2
      ? lemmaInsertPendingLookup id2 pid1 (CausalTreeAtom id1 l1) pending
      ? (Map.lookup id2 (insertPending pid1 (CausalTreeAtom id1 l1) pending) ==. Nothing *** QED)
  ==. applyAtom (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)) pid2 (CausalTreeAtom id2 l2)
      ? (  Map.updateLookupWithKey constConstNothing id2
           (insertPending pid1 (CausalTreeAtom id1 l1) pending)
       ==. (Nothing, insertPending pid1 (CausalTreeAtom id1 l1) pending)
       *** QED)
  ==. CausalTree wop2 (insertPending pid1 (CausalTreeAtom id1 l1) pending)
      ? lemmaInsertInWeaveJustNEq (CausalTreeWeave ctAtom weaveChildren) pid1 pid2 wop2 (CausalTreeAtom id1 l1) (CausalTreeAtom id2 l2)
  ==. apply (CausalTree wop2 pending) op1
  ==. apply (apply x op2) op1
  *** QED)

  | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  , Just [] <- Map.lookup id2 pending
  , pid1 /= id2
  = (Map.updateLookupWithKey constConstNothing id2 pending
     ? constConstNothing id2 []
    ==. (Just [], Map.delete id2 pending)
    *** QED) &&&
   (apply x op2
    ==. applyAtom x pid2 atom2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) []
    ==. CausalTree wop2 (Map.delete id2 pending)
    *** QED ) &&&
    (apply x op1
    ==. applyAtom x pid1 atom1
    ==. CausalTree ctw (insertPending pid1 atom1 pending)
    *** QED) &&&
    (case insertInWeave wop2 pid1 atom1 of
       Nothing -> ()
       Just _ -> ()) &&&
    (apply (apply x op2) op1
    ==. apply (CausalTree wop2 (Map.delete id2 pending)) op1
      -- ? assert (not (S.member pid1 (weaveIds wop2)))
      ? insertInWeave wop2 pid1 atom1
      -- ? toProo (isNothing (insertInWeave wop2 pid1 atom1))
    ==. applyAtom (CausalTree wop2 (Map.delete id2 pending)) pid1 atom1
    ==. CausalTree wop2 (insertPending pid1 atom1 (Map.delete id2 pending))
    *** QED) &&&
    let pops1 = case Map.lookup pid1 pending of
                  Nothing -> [atom1]
                  Just xs -> insertList atom1 xs in
    lemmaLookupDelete2 pending pid1 id2  &&&
    toProof (compatible op1 op2) &&&
    (Map.lookup pid1 pending ==. Map.lookup pid1 (Map.delete id2 pending) ***QED) &&&
    (insertPending pid1 atom1 pending
    ==. Map.insert pid1 pops1 pending
    *** QED) &&&
    (insertPending pid1 atom1 (Map.delete id2 pending)
    ==. Map.insert pid1 pops1 (Map.delete id2 pending)
    *** QED) &&&
    lemmaInsertDelete pid1 pops1 id2 pending &&&
    lemmaLookupInsert2 pending id2 pid1 pops1 &&& 
    (Map.updateLookupWithKey constConstNothing id2 (Map.insert pid1 pops1 pending)
     ? constConstNothing id2 []
    ==. (Just [], Map.delete id2 (Map.insert pid1 pops1 pending))
    *** QED) &&&
    (apply (apply x op1) op2
    ==. applyAtom (apply x op1) pid2 atom2
    ==. applyAtom (CausalTree ctw (insertPending pid1 atom1 pending)) pid2 atom2
    ==. applyAtom (CausalTree ctw (Map.insert pid1 pops1 pending)) pid2 atom2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 (insertPending pid1 atom1 pending))) []
    ==. CausalTree wop2 (Map.delete id2 (insertPending pid1 atom1 pending))
    *** QED)

  | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  , Just pops2@(_:_) <- Map.lookup id2 pending
  , pid1 /= id2
  = (Map.updateLookupWithKey constConstNothing id2 pending
     ? constConstNothing id2 pops2
    ==. (Just pops2, Map.delete id2 pending)
    *** QED) &&&
   (apply x op2
    ==. applyAtom x pid2 atom2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2
    *** QED ) &&&
    (apply x op1
    ==. applyAtom x pid1 atom1
    ==. CausalTree ctw (insertPending pid1 atom1 pending)
    *** QED) &&&
    (case insertInWeave wop2 pid1 atom1 of
       Nothing -> ()
       Just _ -> ()) &&&
    let pops1 = case Map.lookup pid1 pending of
                  Nothing -> [atom1]
                  Just xs -> insertList atom1 xs in
    lemmaLookupDelete2 pending pid1 id2  &&&
    toProof (compatible op1 op2) &&&
    (Map.lookup pid1 pending ==. Map.lookup pid1 (Map.delete id2 pending) ***QED) &&&
    (insertPending pid1 atom1 pending
    ==. Map.insert pid1 pops1 pending
    *** QED) &&&
    (insertPending pid1 atom1 (Map.delete id2 pending)
    ==. Map.insert pid1 pops1 (Map.delete id2 pending)
    *** QED) &&&
    lemmaInsertDelete pid1 pops1 id2 pending &&&
    lemmaLookupInsert2 pending id2 pid1 pops1 &&& 
    (Map.updateLookupWithKey constConstNothing id2 (Map.insert pid1 pops1 pending)
     ? constConstNothing id2 pops2
    ==. (Just pops2, Map.delete id2 (Map.insert pid1 pops1 pending))
    *** QED) &&&
    (apply (apply x op1) op2
    ==. applyAtom (apply x op1) pid2 atom2
    ==. applyAtom (CausalTree ctw (insertPending pid1 atom1 pending)) pid2 atom2
    ==. applyAtom (CausalTree ctw (Map.insert pid1 pops1 pending)) pid2 atom2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 (insertPending pid1 atom1 pending))) pops2
    *** QED) &&&

    let (pops2',pop2@(CausalTreeAtom pop2id _)) = listLast pops2 in
    (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) (List.concat pops2' (cons pop2 []))
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) (List.concat pops2' [pop2])
     ? lemmaFoldlConcat (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2' [pop2]
    ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2') [pop2]
    ==. List.foldl' (applyAtomHelper id2) (applyAtomHelper id2 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2') pop2) []
    ==. applyAtomHelper id2 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2') pop2
    ==. applyAtom (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2') id2 pop2
    *** QED) &&&
    
    (apply (apply x op2) op1
    ==. apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) op1
    ==. applyAtom (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) pid1 atom1
    ==. applyAtom (applyAtom (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2') id2 pop2) pid1 atom1
    *** QED) &&&
    let CausalTree weave' pending' = List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2' in
    (case insertInWeave weave' pid1 atom1 of{
       Nothing -> ();
       Just _ -> ()
       }) &&&
    -- prove this so we can do induction
  (CausalTree wop2 (Map.delete id2 (insertPending pid1 atom1 pending))
  ==. applyAtom (CausalTree wop2 (Map.delete id2 pending)) pid1 atom1
  *** QED) &&&
  lemmaLookupSubsetOf pending id2 pops2 &&&
  lemmaDeleteSubsetJust pending id2 pops2 (pendingListIds pops2) &&&
  toProof (pendingIds (Map.delete id2 pending) `cast` pendingIds pending) &&&
  (weaveIds wop2 ==. S.union (S.singleton id2) (weaveIds ctw) *** QED) &&&
  (compatibleState x op1
   ==. (idUniqueCausalTree x  && (not (id1 `S.member` causalTreeIds x)))
   *** QED) &&&
  (causalTreeIds x
  ==. S.union (weaveIds ctw) (pendingIds pending)
  *** QED) &&&
  toProof (not (S.member id1 (pendingIds pending))) &&&
  toProof (idUniqueMap pending) &&&
  toProof (not (S.member pid1 (weaveIds wop2))) &&&
  toProof (idUniqueList pops2) &&&
  -- need a more precise lemma: unique && delete => keys - deleted 
  assume (S.null (S.intersection (pendingListIds pops2) (causalTreeIds (CausalTree wop2 (Map.delete id2 pending))))) &&&
  assert (not (S.member id1 (pendingListIds pops2))) &&&
  lawCommutatiityNEqNJFoldl (CausalTree wop2 (Map.delete id2 pending)) pid1 atom1 id2 pops2
  | otherwise = undefined


{-@ lawCommutativityNEqJJ :: Ord id =>
     x : CausalTree id a
  -> op1 : CausalTreeOp id a
  -> {op2 : CausalTreeOp id a |
        causalTreeOpParent op1 /= causalTreeOpParent op2 &&
        (compatible op1 op2 && compatibleState x op1 && compatibleState x op2) &&
        (isJust (insertInWeave (causalTreeWeave x) (causalTreeOpParent op1) (causalTreeOpAtom op1))) &&
        (isJust (insertInWeave (causalTreeWeave x) (causalTreeOpParent op2) (causalTreeOpAtom op2)))}
  -> {apply (apply x op1) op2 == apply (apply x op2) op1}
  / [causalTreePendingSize x, 0, 0] @-}
lawCommutativityNEqJJ :: forall id a. Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEqJJ
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 atom1@(CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 atom2@(CausalTreeAtom id2 l2))
  | Just wop1 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  -- , Just pops2 <- Map.lookup id2 pending
  -- TODO: this precondition is not needed; it can be derived
  =
                 --  ? (Map.lookup id1 id2pending
                 --     ? lemmaLookupDelete2 pending id1 id2
                 --     ==. Map.lookup id1 (Map.delete id2 pending)
                 --     ? lemmaLookupDelete pending id1
                 --     ==. Nothing
                 --     ==. Map.lookup id1 (Map.delete id1 pending)
                 --     *** QED)
                 -- ==. (case Map.lookup id1 id2pending of
                 --        Nothing -> []
                 --        Just pops -> pops)

    toProof (idUniqueCausalTree x) &&&
    toProof (idUniqueWeave ctw) &&&
    toProof (causalTreeIds x
            ==. S.union (weaveIds ctw) (pendingIds pending)) &&&
    (compatible op1 op2
    ==. id1 /= id2
    *** QED) &&&
    (compatibleState x op1
    *** QED) &&&
    (compatibleState x op2
    *** QED) &&&
    toProof (id1 /= id2) &&&
    (id2pending ==. Map.delete id2 pending *** QED) &&&
    lemmaLookupDelete pending id1  &&&
    lemmaLookupDelete2 pending id1 id2  &&&
                      --   ? lemmaDelete id1 id2 pending
                      -- ==. (case Map.lookup id1 id2pending of
                      --        Nothing -> id2pending ==. Map.delete id1 id2pending
                      --        Just _ -> Map.delete id1 id2pending)
                      -- ==. Map.delete id2 (Map.delete id1 pending)

    lemmaDelete id1 id2 pending &&&
    (id1id2pending
    ==. id2id1pending
    *** QED) &&&
    (Map.lookup id1 id2pending
    ==. Map.lookup id1 (Map.delete id2 pending)
    ==. Map.lookup id1 pending
    *** QED) &&&
    lemmaLookupDelete2 pending id2 id1 &&&
    (Map.lookup id2 id1pending
    ==. Map.lookup id2 (Map.delete id1 pending)
    ==. Map.lookup id2 pending
    *** QED) &&&
    toProof (pid1 /= id2) &&&
    toProof (pid2 /= id1) &&&    
    lemmaInsertInWeaveJustEq2
        (CausalTreeWeave ctAtom weaveChildren)
        pid2
        pid1
        wop2
        wop1
        (CausalTreeAtom id2 l2)
        (CausalTreeAtom id1 l1)  &&&
  let Just wop2op1 = insertInWeave wop2 pid1 (CausalTreeAtom id1 l1)
      Just wop1op2 = insertInWeave wop1 pid2 (CausalTreeAtom id2 l2) in
  -- id1 
    ( List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) []
  ==. CausalTree wop1 id1pending
  *** QED) &&&

    (constConstNothing id1 pops1 ==. Nothing *** QED) &&&
    
    ( Map.updateLookupWithKey constConstNothing id1 pending
  ==. (id1pendingM, id1pending)
  *** QED) &&&
  
    ( apply x op1
  ==. applyAtom x pid1 atom1
  ==. List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1
  *** QED) &&&

  -- -- id2
    ( List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) []
  ==. CausalTree wop2 id2pending
  *** QED) &&&
  
    (constConstNothing id2 pops2 ==. Nothing *** QED) &&&
    
    ( Map.updateLookupWithKey constConstNothing id2 pending
  ==. (id2pendingM, id2pending)
  *** QED) &&&
  
    ( Map.updateLookupWithKey constConstNothing id1 id2pending
  ==. (id1pendingM, id1id2pending)
  *** QED) &&&

    ( apply x op2
  ==. applyAtom x pid2 atom2
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2
  *** QED) &&&


    ( Map.updateLookupWithKey constConstNothing id2 id1pending
  ==. (id2pendingM, id1id2pending)
  *** QED) &&&
  lemmaLookupDelete pending id2 &&&
  (Map.lookup id2 id2pending ==. Nothing *** QED) &&&
  
  (Map.updateLookupWithKey constConstNothing id2 id2pending
  ==. (Nothing, id2pending)
  *** QED) &&&

  (applyAtom (CausalTree ctw id2pending) pid2 atom2
  ==. CausalTree wop2 id2pending
  *** QED) &&&

  

  -- -- id2 then id1
  (      List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) [CausalTreeAtom id1 l1]
     ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) (CausalTreeAtom id1 l1)) []
     ==. applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) (CausalTreeAtom id1 l1)
     ==.  apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) op1
     *** QED) &&&
  (case id2pendingM of{
    Nothing -> ();
    Just xs -> lemmaDeleteSubsetJust pending id2 xs (pendingListIds xs)
      `cast` idUniqueMap id2pending
      `cast` weaveIds ctw
      `cast` idUniqueCausalTree (CausalTree ctw id2pending)
      `cast` lemmaLookupSubsetOf pending id2 xs
      `cast` pendingListIds xs
      `cast` (xs ==. pops2)
      `cast` ()
    }) &&&
  (case id1pendingM of{
    Nothing -> ();
    Just xs -> lemmaDeleteSubsetJust pending id1 xs (pendingListIds xs)
      `cast` idUniqueMap id1pending
      `cast` weaveIds ctw
      `cast` pendingIds id1pending
      `cast` idUniqueCausalTree (CausalTree ctw id1pending)
      `cast` lemmaLookupSubsetOf pending id1 xs
      `cast` lemmaLookupSubsetOf id2pending id1 xs
      `cast` pendingListIds xs
      `cast` (xs ==. pops1)
      `cast` ()
    }) &&&
  toProof (causalTreeIds (CausalTree ctw id2pending)
          `cast` pendingIds id2pending
          `cast` pendingIds pending) &&&
  toProof (not (S.member id2 (causalTreeIds (CausalTree ctw id2pending)))) &&&

  toProof (causalTreeIds (CausalTree ctw id1pending)
          `cast` pendingIds pending) &&&
  toProof (not (S.member id1 (causalTreeIds (CausalTree ctw id1pending)))) &&&

  lemmaApplyAtomIds' (CausalTree ctw id2pending) pid2 atom2 &&&
  (idUniqueList [CausalTreeAtom id1 l1]
  `cast` idUniqueList ([] :: [CausalTreeAtom id a])
  `cast` pendingListIds ([] :: [CausalTreeAtom id a])
  `cast` pendingListIds [CausalTreeAtom id1 l1]
  *** QED) &&&
    (idUniqueList [CausalTreeAtom id2 l2]
  `cast` idUniqueList ([] :: [CausalTreeAtom id a])
  `cast` pendingListIds ([] :: [CausalTreeAtom id a])
  `cast` pendingListIds [CausalTreeAtom id2 l2]
  *** QED) &&&
  toProof (pendingListIds pops2) &&&
  toProof (idUniqueList pops2) &&&
  (case pops2 of
     [] -> ()
     _ -> lemmaDeleteShrink pending id2 pops2 &&&
       toProof (List.length pops2 >= 1) &&&
       (causalTreePendingSize (CausalTree wop2 id2pending)
       ==. pendingSize id2pending
       *** QED) &&&
       (causalTreePendingSize x
        ==. pendingSize pending *** QED)  &&&
       lemmaApplyAtomFoldNeq (CausalTree wop2 id2pending) pid1 id2 [CausalTreeAtom id1 l1] pops2 ) &&&
  
  (   apply (apply x op2) op1
  ==. apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) op1
  ==. List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) [CausalTreeAtom id1 l1]
  ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper pid1) (CausalTree wop2 id2pending) [CausalTreeAtom id1 l1]) pops2
  ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (CausalTree wop2 id2pending) atom1) []) pops2
  ==. List.foldl' (applyAtomHelper id2) (applyAtomHelper pid1 (CausalTree wop2 id2pending) (CausalTreeAtom id1 l1)) pops2
  ==. List.foldl' (applyAtomHelper id2) (applyAtom (CausalTree wop2 id2pending) pid1 (CausalTreeAtom id1 l1)) pops2
  ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper id1) (CausalTree wop2op1 id1id2pending) pops1) pops2
  *** QED ) &&&

  -- -- -- id1 then id2
  (      List.foldl' (applyAtomHelper pid2) (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) [CausalTreeAtom id2 l2]
     ==. List.foldl' (applyAtomHelper pid2) (applyAtomHelper pid2 (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) (CausalTreeAtom id2 l2)) []
     ==. applyAtomHelper pid2 (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) (CausalTreeAtom id2 l2)
     ==.  apply (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) op2
     *** QED) &&&
  toProof (idUniqueMap id1pending) &&&
  toProof (S.isSubsetOf (pendingIds id1pending) (pendingIds pending)) &&&
  toProof (idUniqueWeave wop1) &&&
  toProof (S.null (S.intersection (pendingIds id1pending) (weaveIds wop1))) &&&
  toProof (idUniqueCausalTree (CausalTree wop1 id1pending)) &&&
  toProof (idUniqueList [CausalTreeAtom id2 l2]) &&&
  toProof (S.null (S.intersection (pendingListIds [CausalTreeAtom id2 l2]) (causalTreeIds (CausalTree wop1 id1pending)))) &&&

  (case pops1 of
     [] -> ()
     _ -> lemmaDeleteShrink pending id1 pops1 &&&
       toProof (List.length pops1 >= 1) &&&
       (causalTreePendingSize (CausalTree wop1 id1pending)
       ==. pendingSize id1pending
       *** QED) &&&
       toProof (causalTreePendingSize (CausalTree wop1 id1pending) < causalTreePendingSize x) &&&
       lemmaApplyAtomFoldNeq (CausalTree wop1 id1pending) pid2 id1 [CausalTreeAtom id2 l2] pops1 ) &&&


  toProof (weaveIds wop2op1 `cast` pendingIds id1id2pending) &&&
  (case Map.lookup id1 id2pending of
     { Nothing -> ();
       Just xs -> lemmaDeleteSubsetJust id2pending id1 xs (pendingListIds xs)
     }) &&&
  toProof (idUniqueMap id1id2pending) &&&
  toProof (idUniqueWeave wop2op1) &&&
  toProof (idUniqueCausalTree (CausalTree wop2op1 id1id2pending)) &&&
  toProof (causalTreeIds (CausalTree wop2op1 id1id2pending)) &&&
  toProof (S.isSubsetOf (pendingIds id1id2pending) (pendingIds pending)) &&&
  toProof (idUniqueList pops2) &&&
  toProof (idUniqueList pops1) &&&
  toProof (weaveIds wop2op1 == S.union (S.union (S.singleton id1) (S.singleton id2)) (weaveIds ctw)) &&&
  toProof (S.null (S.intersection (pendingListIds pops2) (pendingIds id1id2pending))) &&&
  toProof (S.null (S.intersection (pendingListIds pops2) (weaveIds wop2op1))) &&&
  toProof (S.null (S.intersection (pendingListIds pops1) (pendingIds id1id2pending))) &&&
  toProof (S.null (S.intersection (pendingListIds pops1) (weaveIds wop2op1))) &&&
  toProof (S.null (S.intersection (pendingListIds pops1) (pendingListIds pops2))) &&&

  (causalTreePendingSize (CausalTree wop2op1 id1id2pending)
  ==. pendingSize id1id2pending
  *** QED) &&&

  (if List.length pops1 >0 || List.length pops2 > 0
  then
     (if isJust id1pendingM
      then (lemmaDeleteShrink id2pending id1 pops1 &&& lemmaDeleteShrink pending id1 pops1)
      else ()) &&&
     (if isJust id2pendingM
      then (lemmaDeleteShrink id1pending id2 pops2 &&& lemmaDeleteShrink pending id2 pops2)
      else ()) &&&
     toProof (pendingSize id1id2pending < pendingSize pending) &&&
     lemmaApplyAtomFoldNeq (CausalTree wop2op1 id1id2pending) id2 id1  pops2 pops1
  else ()) &&&
  (   apply (apply x op1) op2
  ==. apply (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) op2
  ==. List.foldl' (applyAtomHelper pid2) (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) [CausalTreeAtom id2 l2]
  ==. List.foldl' (applyAtomHelper id1) (List.foldl' (applyAtomHelper pid2) (CausalTree wop1 id1pending) [CausalTreeAtom id2 l2]) pops1

  ==. List.foldl' (applyAtomHelper id1) (List.foldl' (applyAtomHelper pid2) (applyAtomHelper pid2 (CausalTree wop1 id1pending) atom2) []) pops1
  ==. List.foldl' (applyAtomHelper id1) (applyAtomHelper pid2 (CausalTree wop1 id1pending) (CausalTreeAtom id2 l2)) pops1

  ==. List.foldl' (applyAtomHelper id1) (applyAtom (CausalTree wop1 id1pending) pid2 (CausalTreeAtom id2 l2)) pops1
  
  ==. List.foldl' (applyAtomHelper id1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2op1 id1id2pending) pops2) pops1
  *** QED )
  where id2pendingM = Map.lookup id2 pending
        id1pendingM = Map.lookup id1 pending

        -- pending ops for id1 after applying op2

        id1pending = (case id1pendingM of
                       Nothing -> pending === Map.delete id1 pending
                       Just _ -> Map.delete id1 pending)
                     === Map.delete id1 pending
        id2pending = (case id2pendingM of
                        Nothing -> pending === Map.delete id2 pending
                        Just _ -> Map.delete id2 pending)
                     === Map.delete id2 pending

        pops1  = (case Map.lookup id1 pending of
                        Nothing -> []
                        Just xs -> xs)


        pops2  = (case Map.lookup id2 pending of
                        Nothing -> []
                        Just xs -> xs)

        id1id2pending = (case Map.lookup id2 id1pending of
                           Nothing -> id1pending ==. Map.delete id2 id1pending
                           Just _ -> Map.delete id2 id1pending)
        id2id1pending = (case Map.lookup id1 id2pending of
                           Nothing -> id2pending ==. Map.delete id1 id2pending
                           Just _ -> Map.delete id1 id2pending)


{-@ ple lawCommutativityNEqNJ' @-}
{-@ lawCommutativityNEqNJ' :: Ord id =>
     x : CausalTree id a
  -> op1 : CausalTreeOp id a
  -> {op2 : CausalTreeOp id a |
        causalTreeOpParent op1 /= causalTreeOpParent op2 &&
        (compatible op1 op2 && compatibleState x op1 && compatibleState x op2) &&
        (Nothing == (insertInWeave (causalTreeWeave x) (causalTreeOpParent op1) (causalTreeOpAtom op1))) &&
        (isJust (insertInWeave (causalTreeWeave x) (causalTreeOpParent op2) (causalTreeOpAtom op2))) &&
        (causalTreeOpParent op1 == causalTreeAtomId (causalTreeOpAtom op2))}
  -> {apply (apply x op1) op2 == apply (apply x op2) op1} @-}
lawCommutativityNEqNJ' :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEqNJ'
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 (CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 (CausalTreeAtom id2 l2))
  | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  , id2 == pid1
  = 
    assert (id1 /= pid2) &&&
    (constConstNothing id1 pops1 *** QED) &&&
  -- id2
    ( List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) []
  ==. CausalTree wop2 id2pending
  *** QED) &&&
  
    (constConstNothing id2 pops2 *** QED) &&&
    
    ( Map.updateLookupWithKey constConstNothing id2 pending
  ==. (id2pendingM, id2pending)
  *** QED) &&&
  

    ( apply x op2
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2
  *** QED) &&&


    ( Map.updateLookupWithKey constConstNothing id2 id1pending
  ==. (id2pendingM, id1id2pending)
  *** QED) &&&

  -- id1
    ( apply x op1
  ==. CausalTree ctw (insertPending id2 (CausalTreeAtom id1 l1) pending)
  ==. CausalTree ctw (Map.insert pid1 pid1pending' pending)
  *** QED) &&&

    (constConstNothing id2 pid1pending' *** QED) &&&

  -- id1 then id2
  -- (      List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
  --    ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)) []
  --    ==. applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)
  --    ==.  apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) op1
  --    *** QED) &&&

    ( apply (apply x op1) op2
  ==. apply (CausalTree ctw (Map.insert pid1 pid1pending' pending)) op2
      ? lemmaLookupInsert pending id2 pid1pending'
      ? lemmaDeleteInsert id2 pid1pending' pending
      ? (Map.lookup id2 (Map.insert pid1 pid1pending' pending) ==. Just pid1pending')
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 (Map.insert pid1 pid1pending' pending))) pid1pending'
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) pid1pending'
  *** QED) &&&

  -- id2 then id1
    ( apply (apply x op2) op1
  ==. apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) op1
      ? lemmaFoldlConcat (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2  [CausalTreeAtom id1 l1]
  ==. applyAtomHelper id2 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) (CausalTreeAtom id1 l1)
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending)
        (List.concat pops2 [CausalTreeAtom id1 l1])
  *** QED) &&&
    (List.foldl' (applyAtomHelper id2) (applyAtomHelper id2  (CausalTree wop2 (Map.delete pid1 pending)) (CausalTreeAtom id1 l1)) [] *** QED) &&&

  (case Map.lookup id2 pending of
    Nothing -> ()
    Just _ ->  let (lts, gts) = insertListDestruct (CausalTreeAtom id1 l1) pops2 in
               List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) (List.concat lts (CausalTreeAtom id1 l1:gts))
               ? lemmaFoldlConcat (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending))
                   lts (List.concat [CausalTreeAtom id1 l1] gts)
               ? lemmaFoldlConcat (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) lts [CausalTreeAtom id1 l1]
           ==. List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (List.foldl' (applyAtomHelper id2)
                     (CausalTree wop2 (Map.delete pid1 pending)) lts) [CausalTreeAtom id1 l1])
                 gts
              -- ? eq lemma
           ==! List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (List.foldl' (applyAtomHelper id2)
                     (CausalTree wop2 (Map.delete pid1 pending)) lts) gts)
                 [CausalTreeAtom id1 l1]
              -- ? fold lemma again, apply twice
               ? lemmaFoldlConcat (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) lts gts
           === List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (CausalTree wop2 (Map.delete pid1 pending)) (List.concat lts gts))
                 [CausalTreeAtom id1 l1]
           === List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (CausalTree wop2 (Map.delete pid1 pending)) pops2)
                 [CausalTreeAtom id1 l1]
           *** QED
   -- lemma: foldl' and ++
  )
  where id2pendingM = Map.lookup id2 pending
        id1pendingM = Map.lookup id1 pending
        
        pid1pending'= (case Map.lookup pid1 pending of
                        Nothing -> [CausalTreeAtom id1 l1]
                        -- the naming pops1 here is misleading
                        Just pops1 -> insertList (CausalTreeAtom id1 l1) pops1)

        pid2pending'= case Map.lookup pid2 pending of
                        Nothing -> [CausalTreeAtom id2 l2]
                        Just pops2 -> insertList (CausalTreeAtom id2 l2) pops2

        -- pending ops for id1 after applying op2

        id1pending = (case Map.lookup id1 pending of
                       Nothing -> pending ==. Map.delete id1 pending
                       Just _ -> Map.delete id1 pending)
                     ==. Map.delete id1 pending
        id2pending = (case Map.lookup id2 pending of
                        Nothing -> pending ==. Map.delete id2 pending
                        Just _ -> Map.delete id2 pending)
                     ==. Map.delete id2 pending

        pops1  = (case Map.lookup id1 pending of
                        Nothing -> []
                        Just xs -> xs)
                  ? lemmaLookupDelete2 pending id1 id2
                  ? (Map.lookup id1 id2pending ==. Map.lookup id1 (Map.delete id2 pending) ==. Map.lookup id1 pending *** QED)
                 ==. (case Map.lookup id1 id2pending of
                        Nothing -> []
                        Just pops -> pops)

        pops2  = (case Map.lookup id2 pending of
                        Nothing -> []
                        Just xs -> xs)
                  ? lemmaLookupDelete2 pending id2 id1
                 ==. (case Map.lookup id2 id1pending of
                        Nothing -> []
                        Just pops -> pops)

        id1id2pending = (case Map.lookup id2 id1pending of
                           Nothing -> id1pending ==. Map.delete id2 id1pending
                           Just _ -> Map.delete id2 id1pending)
                        ? lemmaDelete id1 id2 pending
                      ==. Map.delete id1 (Map.delete id2 pending)
                      ==. (case Map.lookup id1 id2pending of
                             Nothing -> id2pending ==. Map.delete id1 id2pending
                             Just _ -> Map.delete id1 id2pending)
                      ==. Map.delete id2 (Map.delete id1 pending)
        id2id1pending = (case Map.lookup id1 id2pending of
                             Nothing -> id2pending ==. Map.delete id1 id2pending
                             Just _ -> Map.delete id1 id2pending)
    



{-@ lawCommutativityNEq :: Ord id => x : CausalTree id a -> op1 : CausalTreeOp id a -> {op2 : CausalTreeOp id a | causalTreeOpParent op1 /= causalTreeOpParent op2 && (compatible op1 op2 && compatibleState x op1 && compatibleState x op2)} -> {apply (apply x op1) op2 == apply (apply x op2) op1} @-}
lawCommutativityNEq :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEq 
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 (CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 (CausalTreeAtom id2 l2))
  -- case when two operations are unrelated
  | Nothing <- i1
  , Nothing <- i2
  = lawCommutativityNEqNN x op1 op2
  | Nothing  <- i1
  , Just wop2 <-i2
  , pid1 /= id2
  = lawCommutativityNEqNJ x op1 op2
  | Just _  <- i1
  , Nothing <-i2
  , pid2 /= id1
  = lawCompatibilityCommutativity op1 op2
  &&& lawCommutativityNEqNJ x op2 op1
  | Just wop1 <-i1
  , Just wop2 <-i2
  = lawCommutativityNEqJJ x op1 op2
  | Nothing  <- i1
  , Just wop2 <-i2
  , id2 == pid1
  = lawCommutativityNEqNJ' x op1 op2
  | Just _  <- i1
  , Nothing <-i2
  , id1 == pid2
  = lawCompatibilityCommutativity op1 op2
  &&& lawCommutativityNEqNJ' x op2 op1
  where i1 = insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
        i2 = insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
