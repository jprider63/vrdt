{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

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
import           VRDT.CausalTree.Eq
import           VRDT.CausalTree.Lemmas
import           Liquid.Data.Maybe
import           Prelude                 hiding ( Maybe(..)
                                                , empty
                                                )
import           Liquid.ProofCombinators
import           ProofCombinators
import qualified Data.Set as S

--{-@ ple lemmaApplyAtomFoldNeq @-}
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
     {x : CausalTree id a | idUniqueCausalTree x}
  -> {pid1 : id | not (S.member pid1 (weaveIds (causalTreeWeave x)))}
  -> atom1 : {CausalTreeAtom id a | not (S.member (causalTreeAtomId atom1) (causalTreeIds x))}
  -> {pid2 : id  | pid1 /= pid2 && (S.member pid2 (weaveIds (causalTreeWeave x)))}
  -> atoms2 : {[CausalTreeAtom id a] | idUniqueList atoms2 && not (S.member (causalTreeAtomId atom1) (pendingListIds atoms2)) && (S.null (S.intersection (pendingListIds atoms2) (causalTreeIds x)))}
  -> {List.foldl' (applyAtomHelper pid2) (applyAtom x pid1 atom1) atoms2 == applyAtom (List.foldl' (applyAtomHelper pid2) x atoms2) pid1 atom1}
  / [causalTreePendingSize x, 1, List.length atoms2] @-}
lawCommutatiityNEqNJFoldl :: forall id a. Ord id =>
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
  []
  = List.foldl' (applyAtomHelper pid2) (applyAtom ct pid1 atom1) []
  === applyAtom ct pid1 atom1
  === applyAtom (List.foldl' (applyAtomHelper pid2) ct []) pid1 atom1
  *** QED
lawCommutatiityNEqNJFoldl
  ct@(CausalTree weave children)
  pid1
  atom1@(CausalTreeAtom id1 _)
  pid2 
  (atom2@(CausalTreeAtom id2 _):atoms2)
  | Nothing <- insertInWeave weave pid2 atom2
  = ()
  | CausalTree wop2 _ <- applyAtom ct pid2 atom2
  , Just wop2op1 <- insertInWeave wop2 pid1 atom1
  = (applyAtom ct pid1 atom1 ==. apply ct (CausalTreeOp pid1 atom1) *** QED) &&&
  (applyAtom ct pid2 atom2 ==. apply ct (CausalTreeOp pid2 atom2) *** QED) &&&
  toProof (pendingListIds (atom2:atoms2) `cast` pendingListIds atoms2) &&&
  toProof (compatible (CausalTreeOp pid1 atom1) (CausalTreeOp pid2 atom2)) &&&
  toProof (weaveIds wop2) &&&
  toProof (pendingListIds (atom2:atoms2)) &&&
  toProof (pendingListIds atoms2) &&&
  toProof (idUniqueList (atom2:atoms2)) &&&
  toProof (idUniqueList atoms2) &&&
  -- termination
  toProof (causalTreePendingSize ct
           `cast` List.length (atom2:atoms2)
           `cast` List.length atoms2) &&&
  (apply (applyAtom ct pid2 atom2) (CausalTreeOp pid1 atom1) ==. applyAtom (applyAtom ct pid2 atom2) pid1 atom1 *** QED) &&&
  (apply (applyAtom ct pid1 atom1) (CausalTreeOp pid2 atom2) ==. applyAtom (applyAtom ct pid1 atom1) pid2 atom2 *** QED) &&&
  toProof (compatibleState ct (CausalTreeOp pid1 atom1)
            ==. (not (S.member id1 (causalTreeIds ct)) && idUniqueCausalTree ct)) &&&
  toProof (compatibleState ct (CausalTreeOp pid2 atom2)) &&&
  (case insertInWeave weave pid1 atom1 of
           Nothing -> ()
           Just _ -> ()) &&&

  toProof (idUniqueList ([] :: [CausalTreeAtom id a])
           `cast` idUniqueList [atom1]) &&&
  (pendingListIds [atom1] `cast` pendingListIds ([] :: [CausalTreeAtom id a]) `cast` ()) &&&
  (applyAtom (applyAtom ct pid2 atom2) pid1 atom1
  ==. applyAtomHelper pid1 (applyAtom ct pid2 atom2) atom1
  ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (applyAtom ct pid2 atom2) atom1) []
  ==. List.foldl' (applyAtomHelper pid1) (applyAtom ct pid2 atom2) [atom1]
  *** QED) &&&
  (List.foldl' (applyAtomHelper pid2) (applyAtom ct pid1 atom1) (atom2:atoms2)
    ==. List.foldl' (applyAtomHelper pid2) (applyAtomHelper pid2 (applyAtom ct pid1 atom1) atom2) atoms2
    ==. List.foldl' (applyAtomHelper pid2) (applyAtom (applyAtom ct pid1 atom1) pid2 atom2) atoms2
      ? lawCommutativityNEqNJBoth ct (CausalTreeOp pid1 atom1) (CausalTreeOp pid2 atom2)
    ==. List.foldl' (applyAtomHelper pid2) (applyAtom (applyAtom ct pid2 atom2) pid1 atom1) atoms2
    ==. List.foldl' (applyAtomHelper pid2) (List.foldl' (applyAtomHelper pid1) (applyAtom ct pid2 atom2) [atom1]) atoms2
      ? lemmaApplyAtomIds' ct pid2 atom2
      -- a tiny lemma: insertInWeave = just weave', weave' subsetof applyatom
      -- ? assume (weaveIds wop2 `S.isSubsetOf` weaveIds (causalTreeWeave (applyAtom ct pid2 atom2)))
      ? lemmaApplyAtomFoldNeq (applyAtom ct pid2 atom2) pid1 pid2 [atom1] atoms2
    ==. List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper pid2) (applyAtom ct pid2 atom2) atoms2) [atom1]
    ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (List.foldl' (applyAtomHelper pid2) (applyAtom ct pid2 atom2) atoms2) atom1) []
    ==. applyAtomHelper pid1 (List.foldl' (applyAtomHelper pid2) (applyAtom ct pid2 atom2) atoms2) atom1
    ==. applyAtom (List.foldl' (applyAtomHelper pid2) (applyAtom ct pid2 atom2) atoms2) pid1 atom1
    ==. applyAtom (List.foldl' (applyAtomHelper pid2) (applyAtomHelper pid2 ct atom2) atoms2) pid1 atom1
    ==. applyAtom (List.foldl' (applyAtomHelper pid2) ct (atom2:atoms2)) pid1 atom1
    *** QED)
  | CausalTree wop2 childrenop2 <- applyAtom ct pid2 atom2
  , Nothing <- insertInWeave wop2 pid1 atom1
  = (applyAtom ct pid1 atom1 ==. apply ct (CausalTreeOp pid1 atom1) *** QED) &&&
  (applyAtom ct pid2 atom2 ==. apply ct (CausalTreeOp pid2 atom2) *** QED) &&&
  toProof (pendingListIds (atom2:atoms2) `cast` pendingListIds atoms2) &&&
  toProof (compatible (CausalTreeOp pid1 atom1) (CausalTreeOp pid2 atom2)) &&&
  toProof (weaveIds wop2) &&&
  toProof (pendingListIds (atom2:atoms2)) &&&
  toProof (pendingListIds atoms2) &&&
  toProof (idUniqueList (atom2:atoms2)) &&&
  toProof (idUniqueList atoms2) &&&
  -- termination
  toProof (causalTreePendingSize ct
           `cast` List.length (atom2:atoms2)
           `cast` List.length atoms2) &&&
  (apply (applyAtom ct pid2 atom2) (CausalTreeOp pid1 atom1) ==. applyAtom (applyAtom ct pid2 atom2) pid1 atom1 *** QED) &&&
  (apply (applyAtom ct pid1 atom1) (CausalTreeOp pid2 atom2) ==. applyAtom (applyAtom ct pid1 atom1) pid2 atom2 *** QED) &&&
  toProof (compatibleState ct (CausalTreeOp pid1 atom1)
            ==. (not (S.member id1 (causalTreeIds ct)) && idUniqueCausalTree ct)) &&&
  toProof (compatibleState ct (CausalTreeOp pid2 atom2)) &&&
  (case insertInWeave weave pid1 atom1 of
           Nothing -> ()
           Just _ -> ()) &&&

  toProof (idUniqueList ([] :: [CausalTreeAtom id a])
           `cast` idUniqueList [atom1]) &&&
  (pendingListIds [atom1] `cast` pendingListIds ([] :: [CausalTreeAtom id a]) `cast` ()) &&&
  (List.foldl' (applyAtomHelper pid2) (applyAtom ct pid1 atom1) (atom2:atoms2)
    ==. List.foldl' (applyAtomHelper pid2) (applyAtomHelper pid2 (applyAtom ct pid1 atom1) atom2) atoms2
    ==. List.foldl' (applyAtomHelper pid2) (applyAtom (applyAtom ct pid1 atom1) pid2 atom2) atoms2
      ? lawCommutativityNEqNJBoth ct (CausalTreeOp pid1 atom1) (CausalTreeOp pid2 atom2)
    ==. List.foldl' (applyAtomHelper pid2) (applyAtom (applyAtom ct pid2 atom2) pid1 atom1) atoms2
      ? lemmaApplyAtomIds' ct pid2 atom2
      ? (causalTreePendingSize (applyAtom ct pid2 atom2)  ==. pendingSize childrenop2)
      ? toProof (pendingSize childrenop2 <= (causalTreePendingSize ct ==. pendingSize children))
      ? lawCommutatiityNEqNJFoldl (applyAtom ct pid2 atom2) pid1 atom1 pid2 atoms2
    ==. applyAtom (List.foldl' (applyAtomHelper pid2) (applyAtom ct pid2 atom2) atoms2) pid1 atom1
    ==. applyAtom (List.foldl' (applyAtomHelper pid2) (applyAtomHelper pid2 ct atom2) atoms2) pid1 atom1
    ==. applyAtom (List.foldl' (applyAtomHelper pid2) ct (atom2:atoms2)) pid1 atom1
    *** QED)



{-@ lawCommutativityNEqNJBoth :: Ord id =>
     x : CausalTree id a
  -> op1 : CausalTreeOp id a
  -> {op2 : CausalTreeOp id a |
        causalTreeOpParent op1 /= causalTreeOpParent op2 &&
        (compatible op1 op2 && compatibleState x op1 && compatibleState x op2) &&
        (Nothing == (insertInWeave (causalTreeWeave x) (causalTreeOpParent op1) (causalTreeOpAtom op1))) &&
        (isJust (insertInWeave (causalTreeWeave x) (causalTreeOpParent op2) (causalTreeOpAtom op2)))}
  -> {apply (apply x op1) op2 == apply (apply x op2) op1}
  / [causalTreePendingSize x, 1, 0] @-}
lawCommutativityNEqNJBoth :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEqNJBoth
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 atom1@(CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 atom2@(CausalTreeAtom id2 l2))
  | pid1 /= id2
  = toProof (causalTreePendingSize x) &&& lawCommutativityNEqNJ x op1 op2
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
  / [causalTreePendingSize x, 0, 0] @-}
lawCommutativityNEqNJ :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEqNJ
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 atom1@(CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 atom2@(CausalTreeAtom id2 l2))
  | Just aaa <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  = Just aaa
    ==. insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
    ==. Nothing
    *** QED
  | Nothing <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  = Nothing
  ==. insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  *** QED
  | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  , Nothing <- Map.lookup id2 pending
  , pid1 /= id2
  = ( apply x op1
  ==. applyAtom x pid1 atom1
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
      ? compatible op1 op2
      -- ? assert (id1 /= id2)
      -- ? assert (pid1 /= id2)
      ? lemmaInsertInWeaveJustNEq (CausalTreeWeave ctAtom weaveChildren) pid1 pid2 wop2 (CausalTreeAtom id1 l1) (CausalTreeAtom id2 l2)
  ==. applyAtom (CausalTree wop2 pending) pid1 atom1
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
  (compatibleState x op2
   ==. (idUniqueCausalTree x  && (not (id2 `S.member` causalTreeIds x)))
  *** QED) &&&
  (causalTreeIds x
  ==. S.union (weaveIds ctw) (pendingIds pending)
  *** QED) &&&
  toProof (not (S.member id1 (pendingIds pending))) &&&
  toProof (idUniqueMap pending) &&&
  toProof (not (S.member pid1 (weaveIds wop2))) &&&
  toProof (idUniqueList pops2) &&&
  -- need a more precise lemma: unique && delete => keys - deleted
  toProof (not (S.member id2 (pendingListIds pops2))) &&&
  toProof (S.null (S.intersection (pendingListIds pops2) (weaveIds ctw))) &&&
  toProof (S.null (S.intersection (pendingListIds pops2) (weaveIds wop2))) &&&
  toProof (S.null (S.intersection (pendingListIds pops2) (pendingIds (Map.delete id2 pending)))) &&&
  toProof (S.null (S.intersection (pendingListIds pops2) (causalTreeIds (CausalTree wop2 (Map.delete id2 pending))))) &&&
  toProof (not (S.member id1 (pendingListIds pops2))) &&&
  lemmaDeleteShrink pending id2 pops2 &&&
  (causalTreePendingSize x ==. pendingSize pending *** QED) &&&
  (causalTreePendingSize (CausalTree wop2 (Map.delete id2 pending)) ==. pendingSize (Map.delete id2 pending) *** QED) &&&
  toProof (pendingSize (Map.delete id2 pending) < pendingSize pending) &&&
  toProof (idUniqueCausalTree (CausalTree wop2 (Map.delete id2 pending))
  `cast`(idUniqueWeave wop2 && idUniqueMap (Map.delete id2 pending))
  `cast` (pendingIds (Map.delete id2 pending))) &&&
  lawCommutatiityNEqNJFoldl (CausalTree wop2 (Map.delete id2 pending)) pid1 atom1 id2 pops2




--{-@ ple lawCommutativityNEqNJ' @-}
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
lawCommutativityNEqNJ' :: forall id a. Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCommutativityNEqNJ'
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
  op1@(CausalTreeOp pid1 atom1@(CausalTreeAtom id1 l1))
  op2@(CausalTreeOp pid2 atom2@(CausalTreeAtom id2 l2))
  | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  , id2 == pid1
  = (compatibleState x op1
    `cast` compatibleState x op2
    `cast` compatible op1 op2
    `cast` causalTreeIds x
    `cast` weaveIds ctw
    `cast` pendingIds pending
    `cast` ())&&&
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
  ==. applyAtom x pid2 atom2
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2
  *** QED) &&&


    ( Map.updateLookupWithKey constConstNothing id2 id1pending
  ==. (id2pendingM, id1id2pending)
  *** QED) &&&

  -- id1
    ( apply x op1
  ==. applyAtom x pid1 atom1
  ==. CausalTree ctw (insertPending id2 (CausalTreeAtom id1 l1) pending)
  ==. CausalTree ctw (Map.insert pid1 pid1pending' pending)
  *** QED) &&&

    (constConstNothing id2 pid1pending' ==. Nothing *** QED) &&&

  -- id1 then id2
  -- (      List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
  --    ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)) []
  --    ==. applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)
  --    ==.  apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) op1
  --    *** QED) &&&
   lemmaLookupInsert pending id2 pid1pending' &&&
   lemmaDeleteInsert id2 pid1pending' pending &&&
   (Map.lookup id2 (Map.insert pid1 pid1pending' pending) ==. Just pid1pending' *** QED) &&&


   (Map.updateLookupWithKey constConstNothing id2 (Map.insert pid1 pid1pending' pending)
   ==. (Just pid1pending', Map.delete pid1 (Map.insert pid1 pid1pending' pending))
   *** QED) &&&


    ( apply (apply x op1) op2
  ==. apply (CausalTree ctw (Map.insert pid1 pid1pending' pending)) op2
  ==. applyAtom (CausalTree ctw (Map.insert pid1 pid1pending' pending)) pid2 atom2
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 (Map.insert pid1 pid1pending' pending))) pid1pending'
  -- ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 (Map.insert pid1 pid1pending' pending))) pid1pending'
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) pid1pending'
  *** QED) &&&

  -- id2 then id1
    ( apply (apply x op2) op1
  ==. apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) op1
      ? lemmaFoldlConcat (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2  [CausalTreeAtom id1 l1]
  ==. applyAtom (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) pid1 atom1
  ==. applyAtomHelper id2 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) (CausalTreeAtom id1 l1)
  ==. List.foldl' (applyAtomHelper id2) (applyAtomHelper id2 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) (CausalTreeAtom id1 l1)) []
  ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) [atom1]
  ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending)
        (List.concat pops2 [CausalTreeAtom id1 l1])
  *** QED) &&&
    -- (List.foldl' (applyAtomHelper id2) (applyAtomHelper id2  (CausalTree wop2 (Map.delete pid1 pending)) (CausalTreeAtom id1 l1)) [] *** QED) &&&
  (case Map.lookup id2 pending of {
    Nothing -> ();
    Just _ -> let (lts, gts) = insertListDestruct (CausalTreeAtom id1 l1) pops2 in
               (causalTreeIds (CausalTree wop2 (Map.delete pid1 pending))
               `cast` idUniqueCausalTree (CausalTree wop2 (Map.delete pid1 pending))
               `cast` causalTreeIds x
               `cast` idUniqueCausalTree x
               `cast` weaveIds ctw
               `cast` weaveIds wop2
               `cast` idUniqueWeave wop2
               `cast` idUniqueWeave ctw
               `cast` pendingIds (Map.delete pid1 pending)
               `cast` pendingIds pending
               `cast` idUniqueMap (Map.delete pid1 pending)
               `cast` idUniqueMap pending
               `cast` idUniqueList [atom1]
               `cast` idUniqueList ([] @ (CausalTreeAtom id a))
               `cast` idUniqueList lts
               `cast` pendingListIds lts
               `cast` pendingListIds [atom1]
               `cast` pendingListIds ([] @ (CausalTreeAtom id a))
               `cast` ()) &&&
               insertListRespectsUniq atom1 pops2 &&&
               lemmaLookupSubsetOf pending id2 pops2 &&&
               lemmaDeleteSubsetJust pending id2 pops2 (pendingListIds pops2) &&&
               lemmaFoldlIds (CausalTree wop2 (Map.delete pid1 pending)) id2 lts &&&
               (atom1:gts ==. atom1:List.concat [] gts ==. List.concat [atom1] gts *** QED) &&&
               idUniqueListConcat lts (List.concat [atom1] gts) &&&
               idUniqueListConcat [atom1] gts &&&
               applyAtomFoldlRespectsUniq (CausalTree wop2 (Map.delete pid1 pending)) id2 lts &&&
    (          List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) (List.concat lts (List.concat [atom1] gts))
               ? lemmaFoldlConcat (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending))
                   lts (List.concat [CausalTreeAtom id1 l1] gts)
               -- ? lemmaFoldlConcat (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) lts [CausalTreeAtom id1 l1]
           ==. List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (CausalTree wop2 (Map.delete pid1 pending)) lts) (List.concat [atom1] gts)
               ? lemmaFoldlConcat (applyAtomHelper id2) (List.foldl' (applyAtomHelper id2)
                   (CausalTree wop2 (Map.delete pid1 pending)) lts) [atom1] gts
           ==. List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (List.foldl' (applyAtomHelper id2)
                     (CausalTree wop2 (Map.delete pid1 pending)) lts) [CausalTreeAtom id1 l1])
                 gts

               ? (S.union (pendingListIds lts) (pendingListIds gts) == pendingListIds pops2)
               ? (S.null (S.intersection (pendingListIds lts) (pendingListIds gts)))
               ? lemmaApplyAtomFoldEq
                      (List.foldl' (applyAtomHelper id2)
                        (CausalTree wop2 (Map.delete pid1 pending)) lts)
                      id2
                      [CausalTreeAtom id1 l1]
                      gts
           ==. List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (List.foldl' (applyAtomHelper id2)
                     (CausalTree wop2 (Map.delete pid1 pending)) lts) gts)
                 [CausalTreeAtom id1 l1]
              -- ? fold lemma again, apply twice
               ? lemmaFoldlConcat (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) lts gts
           ==. List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (CausalTree wop2 (Map.delete pid1 pending)) (List.concat lts gts))
                 [CausalTreeAtom id1 l1]
           ==. List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (CausalTree wop2 (Map.delete pid1 pending)) pops2)
                 [CausalTreeAtom id1 l1]
           *** QED
   -- lemma: foldl' and ++
  )})

  | Just x  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  = Just x === Nothing *** QED
  | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  = ()
  
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
                       Nothing -> pending === Map.delete id1 pending
                       Just _ -> Map.delete id1 pending)
                     === Map.delete id1 pending
        id2pending = (case Map.lookup id2 pending of
                        Nothing -> pending === Map.delete id2 pending
                        Just _ -> Map.delete id2 pending)
                     === Map.delete id2 pending

        pops1  = (case Map.lookup id1 pending of
                        Nothing -> []
                        Just xs -> xs)
                  ? lemmaLookupDelete2 pending id1 id2
                  ? compatible op1 op2
                  ? (Map.lookup id1 id2pending === Map.lookup id1 (Map.delete id2 pending) === Map.lookup id1 pending *** QED)
                 === (case Map.lookup id1 id2pending of
                        Nothing -> []
                        Just pops -> pops)

        pops2  = (case Map.lookup id2 pending of
                        Nothing -> []
                        Just xs -> xs)
                  ? lemmaLookupDelete2 pending id2 id1
                 === (case Map.lookup id2 id1pending of
                        Nothing -> []
                        Just pops -> pops)

        id1id2pending = (case Map.lookup id2 id1pending of
                           Nothing -> id1pending === Map.delete id2 id1pending
                           Just _ -> Map.delete id2 id1pending)
                        ? lemmaDelete id1 id2 pending
                      === Map.delete id1 (Map.delete id2 pending)
                      === (case Map.lookup id1 id2pending of
                             Nothing -> id2pending === Map.delete id1 id2pending
                             Just _ -> Map.delete id1 id2pending)
                      === Map.delete id2 (Map.delete id1 pending)
        id2id1pending = (case Map.lookup id1 id2pending of
                             Nothing -> id2pending === Map.delete id1 id2pending
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
