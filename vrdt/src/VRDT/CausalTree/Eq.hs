{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--noadt" @-}
module VRDT.CausalTree.Eq where

import VRDT.CausalTree.Internal
import qualified Liquid.Data.List              as List
import           Liquid.Data.List.Props
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
import           Liquid.ProofCombinators
import           ProofCombinators


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



{-@ lemmaApplyAtomFoldEq :: Ord id
 => {ct:CausalTree id a | idUniqueCausalTree ct}
 -> pid:id
 -> {atoms1:[CausalTreeAtom id a] | idUniqueList atoms1 && S.null (S.intersection (pendingListIds atoms1) (causalTreeIds ct))}
 -> {atoms2:[CausalTreeAtom id a] | idUniqueList atoms2 && S.null (S.intersection (pendingListIds atoms1) (pendingListIds atoms2)) && S.null (S.intersection (pendingListIds atoms2) (causalTreeIds ct))}
 -> {  ((List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) ct atoms1) atoms2)
   == (List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) ct atoms2) atoms1))
   }
/ [List.length atoms1 + List.length atoms2]@-}
lemmaApplyAtomFoldEq :: forall id a. Ord id
 => CausalTree id a
 -> id
 -> [CausalTreeAtom id a]
 -> [CausalTreeAtom id a]
 -> ()
lemmaApplyAtomFoldEq ct pid [] atoms2 =
  List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) ct []) atoms2
  ==. List.foldl' (applyAtomHelper pid) ct atoms2
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) ct atoms2) []
  *** QED

lemmaApplyAtomFoldEq ct pid atoms1 [] =
  List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) ct []) atoms1
  ==. List.foldl' (applyAtomHelper pid) ct atoms1
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) ct atoms1) []
  *** QED

lemmaApplyAtomFoldEq
  ct@(CausalTree w pending)
  pid
  atoms1@(atom1@(CausalTreeAtom id1 _):atoms1')
  atoms2@(atom2@(CausalTreeAtom id2 _):atoms2') =
  (causalTreeIds ct
  `cast` weaveIds w
  `cast` pendingIds pending
  `cast` ()) &&&
  (List.concat [atom1] atoms1'
  ==. (atom1:List.concat [] atoms1')
  ==. atom1:atoms1'
  *** QED) &&&
  (List.concat [atom2] atoms2'
  ==. (atom2:List.concat [] atoms2')
  ==. atom2:atoms2'
  *** QED) &&&
  (idUniqueList (atom1:atoms1')
  `cast` idUniqueList atoms1'
  `cast` idUniqueList (atom2:atoms2')
  `cast` idUniqueList atoms2'
  `cast` idUniqueList [atom1]
  `cast` idUniqueList ([] @ (CausalTreeAtom id a))
  `cast` pendingListIds (atom1:atoms1')
  `cast` pendingListIds atoms1'
  `cast` pendingListIds (atom2:atoms2')
  `cast` pendingListIds atoms2'
  `cast` pendingListIds [atom1]
  `cast` pendingListIds ([] @ (CausalTreeAtom id a))
  `cast` ()) &&&
  -- (pendingListIds [atom1] ==. S.singleton id1 *** QED) &&&
  lemmaApplyAtomIds ct pid atom1 &&&
  applyAtomRespectsUniq ct pid atom1 &&&
  lemmaApplyAtomIds ct pid atom2 &&&
  applyAtomRespectsUniq ct pid atom2 &&&

  lemmaFoldlConcat (applyAtomHelper pid) ct [atom1] atoms1' &&&
  lemmaFoldlConcat (applyAtomHelper pid) ct [atom2] atoms2' &&&

  (applyAtom (applyAtom ct pid atom2) pid atom1
  ==. applyAtomHelper pid (applyAtom ct pid atom2) atom1
  ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid (applyAtom ct pid atom2) atom1) []
  ==. List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom2) [atom1]
  *** QED) &&&
  (List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom2) atoms2'
  ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid ct atom2) atoms2'
  ==. List.foldl' (applyAtomHelper pid) ct (atom2:atoms2')
  *** QED) &&&

  -- termination
  (List.length atoms1
  `cast` List.length atoms2
  `cast` List.length atoms1'
  `cast` List.length atoms2'
  `cast` List.length [atom1]
  `cast` List.length ([] @(CausalTreeAtom id a))
  `cast` ()) &&&
--  assert (idUniqueList atoms1') &&&
  lemmaApplyAtomFoldEq (applyAtom ct pid atom1) pid atoms1' atoms2 &&&
  lemmaApplyAtomFoldEq (applyAtom ct pid atom2) pid [atom1] atoms2' &&&
  lawCommutativityEq' ct pid atom1 atom2 &&&
  -- assert (not (id1 `S.member` pendingListIds atoms2)) &&&
  lemmaFoldlConcat (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom2) atoms2') [atom1] atoms1' &&&
  (List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) ct atoms1) atoms2
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) ct (List.concat [atom1] atoms1')) atoms2
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtomHelper pid ct atom1) atoms1') atoms2
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom1) atoms1') atoms2
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom1) (atom2:atoms2')) atoms1'
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtomHelper pid (applyAtom ct pid atom1) atom2) atoms2') atoms1'
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtom (applyAtom ct pid atom1) pid atom2) atoms2') atoms1'
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtom (applyAtom ct pid atom2) pid atom1) atoms2') atoms1'
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom2) [atom1]) atoms2') atoms1'
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom2) atoms2') [atom1]) atoms1'
  ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom2) atoms2') (List.concat [atom1] atoms1')

  ==. (List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom2) atoms2') (atom1:atoms1')) 
  *** QED)



{-@ lawCommutativityEq' :: Ord id
  => {x:CausalTree id a | idUniqueCausalTree x}
  -> pid:id
  -> {atom1:CausalTreeAtom id a |  not (S.member (causalTreeAtomId atom1) (causalTreeIds x))}
  -> {atom2:CausalTreeAtom id a | not (S.member (causalTreeAtomId atom2) (causalTreeIds x)) && (causalTreeAtomId atom1 /= causalTreeAtomId atom2)}
  -> {applyAtom (applyAtom x pid atom1) pid atom2  == applyAtom (applyAtom x pid atom2) pid atom1}
@-}
lawCommutativityEq' :: forall id a. Ord id
  => CausalTree id a
  -> id
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lawCommutativityEq' x@(CausalTree weave _) pid atom1 atom2
  | Nothing <- insertInWeave weave pid atom1
  , Just _ <- insertInWeave weave pid atom2
  = ()
  | Just _ <- insertInWeave weave pid atom1
  , Nothing <- insertInWeave weave pid atom2
  = ()
  | Nothing <- insertInWeave weave pid atom1
  , Nothing <- insertInWeave weave pid atom2
  = lawCommutativityEqN x pid atom1 atom2
  | Just _ <- insertInWeave weave pid atom1
  , Just _ <- insertInWeave weave pid atom2
  = lawCommutativityEqJ x pid atom1 atom2


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


{-@ lawCommutativityEqJ :: Ord id
  => {x:CausalTree id a | idUniqueCausalTree x}
  -> pid:id
  -> {atom1:CausalTreeAtom id a | isJust (insertInWeave (causalTreeWeave x) pid atom1) && not (S.member (causalTreeAtomId atom1) (causalTreeIds x))}
  -> {atom2:CausalTreeAtom id a | isJust (insertInWeave (causalTreeWeave x) pid atom2)  && not (S.member (causalTreeAtomId atom2) (causalTreeIds x)) && (causalTreeAtomId atom1 /= causalTreeAtomId atom2)}
  -> {applyAtom (applyAtom x pid atom1) pid atom2  == applyAtom (applyAtom x pid atom2) pid atom1}
 / [if (isNothing (Map.lookup (causalTreeAtomId atom2) (causalTreePending x))) then 1 else 0] @-}
lawCommutativityEqJ :: forall id a. Ord id
  => CausalTree id a
  -> id
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lawCommutativityEqJ x@(CausalTree weave children) pid atom1@(CausalTreeAtom id1 _) atom2@(CausalTreeAtom id2 _)
  | Just wop1 <- insertInWeave weave pid atom1
  , Just wop2 <- insertInWeave weave pid atom2
  , Just pops1 <- Map.lookup id1 children
  , Nothing <- Map.lookup id2 children
  = (if (isNothing (Map.lookup id2 children)) then 1 else 0) `cast`
    (if (isNothing (Map.lookup id1 children)) then 1 else 0) `cast`
    lawCommutativityEqJ x pid atom2 atom1

  | Just wop1 <- insertInWeave weave pid atom1
  , Just wop2 <- insertInWeave weave pid atom2
  , Nothing <- Map.lookup id1 children
  , Just pops2 <- Map.lookup id2 children
  = (Map.updateLookupWithKey constConstNothing id1 children
    ==. (Nothing, children)
    *** QED) &&&
    ( List.foldl' (applyAtomHelper pid) x [atom1]
    ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid x atom1) []
    ==. List.foldl' (applyAtomHelper pid) (applyAtom x pid atom1) []
    ==. applyAtom x pid atom1
    ==. CausalTree wop1 children
    *** QED) &&&
    (List.foldl' (applyAtomHelper pid) (applyAtom x pid atom2) [atom1]
    ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid (applyAtom x pid atom2) atom1) []
    ==. List.foldl' (applyAtomHelper pid) (applyAtom (applyAtom x pid atom2) pid atom1) []
    ==. applyAtom (applyAtom x pid atom2) pid atom1
    *** QED) &&&
    (Map.updateLookupWithKey constConstNothing id2 children
     ? (constConstNothing id2 pops2 ==. Nothing *** QED)
    ==. (Just pops2, Map.delete id2 children)
    *** QED) &&&
    (applyAtom x pid atom2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 children)) pops2
    *** QED) &&&


    (idUniqueCausalTree (CausalTree wop2 (Map.delete id2 children))
    ==. (idUniqueWeave wop2 && idUniqueMap (Map.delete id2 children) && S.null (S.intersection (weaveIds wop2) (pendingIds (Map.delete id2 children))))
    *** QED) &&&
    (idUniqueCausalTree x
    `cast` idUniqueWeave weave
    `cast` idUniqueMap children
    `cast` ()) &&&

    (causalTreeIds x
    `cast` weaveIds weave
    `cast` pendingIds children
    `cast` ()) &&&

    (causalTreeIds (CausalTree wop2 (Map.delete id2 children))
    `cast` weaveIds wop2
    `cast` pendingIds (Map.delete id2 children)
    `cast` ()) &&&

    lemmaDeleteSubsetJust children id2 pops2 (pendingListIds pops2) &&&
    
    toProof (idUniqueWeave wop2) &&&
    toProof (idUniqueMap (Map.delete id2 children)) &&&
    -- toProof (S.null (S.intersection (weaveIds wop2) (pendingIds (Map.delete id2 children)))) &&&
    (causalTreeIds x
    ==. S.union (weaveIds weave) (pendingIds children)
    *** QED) &&&
    lemmaLookupSubsetOf children id2 pops2 &&&
    (pendingListIds [atom1]
    `cast` pendingListIds ([] @ (CausalTreeAtom id a) )
    `cast` pendingListIds pops2
    `cast` idUniqueList pops2
    `cast` idUniqueList [atom1]
    `cast` idUniqueList ([] @ (CausalTreeAtom id a))
    `cast` ()) &&&
    toProof (idUniqueList [atom1]) &&&
    
    lemmaApplyAtomFoldNeq (CausalTree wop2 (Map.delete id2 children)) pid id2 [atom1] pops2 &&&
    lemmaLookupDelete2 children id1 id2 &&&

    let Just wop2op1 = insertInWeave wop2 pid atom1
        Just wop1op2 = insertInWeave wop1 pid atom2 in
    (Map.updateLookupWithKey constConstNothing id1 (Map.delete id2 children)
    ==. (Nothing, Map.delete id2 children)
    *** QED) &&&
    (List.foldl' (applyAtomHelper pid) (CausalTree wop2 (Map.delete id2 children)) [atom1]
    ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid (CausalTree wop2 (Map.delete id2 children)) atom1) []
    ==. applyAtomHelper pid (CausalTree wop2 (Map.delete id2 children)) atom1
    ==. applyAtom (CausalTree wop2 (Map.delete id2 children)) pid atom1
    ==. CausalTree wop2op1 (Map.delete id2 children)
    *** QED) &&&
    lemmaInsertInWeaveJustEq weave pid wop1 wop2 atom1 atom2 &&&
    (Just wop1op2 ==. Just wop2op1 *** QED) &&&

    (applyAtom (applyAtom x pid atom2) pid atom1
    ==. List.foldl' (applyAtomHelper pid) (applyAtom x pid atom2) [atom1]
    ==. List.foldl' (applyAtomHelper pid) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 children)) pops2) [atom1]
    ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper pid) (CausalTree wop2 (Map.delete id2 children)) [atom1]) pops2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2op1 (Map.delete id2 children)) pops2
    *** QED ) &&&
    (applyAtom (applyAtom x pid atom1) pid atom2
    ==. applyAtom (CausalTree wop1 children) pid atom2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop1op2 (Map.delete id2 children)) pops2
    *** QED) 
  | Just wop1 <- insertInWeave weave pid atom1
  , Just wop2 <- insertInWeave weave pid atom2
  , Just pops1 <- Map.lookup id1 children
  , Just pops2 <- Map.lookup id2 children
  = (Map.updateLookupWithKey constConstNothing id2 children
     ? (constConstNothing id2 pops2 ==. Nothing *** QED)
    ==. (Just pops2, Map.delete id2 children)
    *** QED) &&&
    (applyAtom x pid atom2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 children)) pops2
    *** QED) &&&

    (Map.updateLookupWithKey constConstNothing id1 children
     ? (constConstNothing id1 pops1 ==. Nothing *** QED)
    ==. (Just pops1, Map.delete id1 children)
    *** QED) &&&
    (applyAtom x pid atom1
    ==. List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 children)) pops1
    *** QED) &&&

    (idUniqueCausalTree (CausalTree wop1 (Map.delete id1 children))
    ==. (idUniqueWeave wop1 && idUniqueMap (Map.delete id1 children) && S.null (S.intersection (weaveIds wop1) (pendingIds (Map.delete id1 children))))
    *** QED) &&&
    
    (idUniqueCausalTree (CausalTree wop2 (Map.delete id2 children))
    ==. (idUniqueWeave wop2 && idUniqueMap (Map.delete id2 children) && S.null (S.intersection (weaveIds wop2) (pendingIds (Map.delete id2 children))))
    *** QED) &&&
    
    (idUniqueCausalTree x
    `cast` idUniqueWeave weave
    `cast` idUniqueMap children
    `cast` ()) &&&

    (causalTreeIds x
    `cast` weaveIds weave
    `cast` pendingIds children
    `cast` ()) &&&

    (causalTreeIds (CausalTree wop2 (Map.delete id2 children))
    `cast` weaveIds wop2
    `cast` pendingIds (Map.delete id2 children)
    `cast` ()) &&&

    (causalTreeIds (CausalTree wop1 (Map.delete id1 children))
    `cast` weaveIds wop1
    `cast` pendingIds (Map.delete id1 children)
    `cast` ()) &&&

    lemmaLookupDelete2 children id1 id2 &&&
    lemmaLookupDelete2 children id2 id1 &&&    

    lemmaDeleteSubsetJust children id2 pops2 (pendingListIds pops2) &&&
    lemmaDeleteSubsetJust (Map.delete id2 children) id1 pops1 (pendingListIds pops1) &&&

    lemmaDeleteSubsetJust children id1 pops1 (pendingListIds pops1) &&&
    lemmaDeleteSubsetJust (Map.delete id1 children) id2 pops2 (pendingListIds pops2) &&&

    
    toProof (idUniqueWeave wop2) &&&
    toProof (idUniqueMap (Map.delete id2 children)) &&&

    toProof (idUniqueWeave wop1) &&&
    toProof (idUniqueMap (Map.delete id1 children)) &&&


    (causalTreeIds x
    ==. S.union (weaveIds weave) (pendingIds children)
    *** QED) &&&

    lemmaLookupSubsetOf children id2 pops2 &&&
    lemmaLookupSubsetOf (Map.delete id2 children) id1 pops1 &&&

    lemmaLookupSubsetOf children id1 pops1 &&&
    lemmaLookupSubsetOf (Map.delete id1 children) id2 pops2 &&&


    ( List.foldl' (applyAtomHelper pid) x [atom1]
    ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid x atom1) []
    ==. List.foldl' (applyAtomHelper pid) (applyAtom x pid atom1) []
    ==. applyAtom x pid atom1
    ==. List.foldl' (applyAtomHelper id1) (CausalTree wop1 (Map.delete id1 children)) pops1
    *** QED) &&&
    (List.foldl' (applyAtomHelper pid) (applyAtom x pid atom2) [atom1]
    ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid (applyAtom x pid atom2) atom1) []
    ==. List.foldl' (applyAtomHelper pid) (applyAtom (applyAtom x pid atom2) pid atom1) []
    ==. applyAtom (applyAtom x pid atom2) pid atom1
    *** QED) &&&


    ( List.foldl' (applyAtomHelper pid) x [atom2]
    ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid x atom2) []
    ==. List.foldl' (applyAtomHelper pid) (applyAtom x pid atom2) []
    ==. applyAtom x pid atom2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 children)) pops2
    *** QED) &&&

    (List.foldl' (applyAtomHelper pid) (applyAtom x pid atom1) [atom2]
    ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid (applyAtom x pid atom1) atom2) []
    ==. List.foldl' (applyAtomHelper pid) (applyAtom (applyAtom x pid atom1) pid atom2) []
    ==. applyAtom (applyAtom x pid atom1) pid atom2
    *** QED) &&&


    (pendingListIds pops1
    `cast` pendingListIds pops2
    `cast` pendingListIds [atom1]
    `cast` pendingListIds [atom2]
    `cast` pendingListIds ([] @ (CausalTreeAtom id a))
    `cast` idUniqueList pops2
    `cast` idUniqueList [atom1]
    `cast` idUniqueList [atom2]
    `cast` idUniqueList ([] @ (CausalTreeAtom id a))
    `cast` ()) &&&
    
    lemmaApplyAtomFoldNeq (CausalTree wop2 (Map.delete id2 children)) pid id2 [atom1] pops2 &&&
    lemmaApplyAtomFoldNeq (CausalTree wop1 (Map.delete id1 children)) pid id1 [atom2] pops1 &&&
    lemmaDelete id1 id2 children &&&

    let Just wop2op1 = insertInWeave wop2 pid atom1
        Just wop1op2 = insertInWeave wop1 pid atom2 in

    (causalTreeIds (CausalTree wop2op1 (Map.delete id1 (Map.delete id2 children)))
    ==. S.union (weaveIds wop2op1) (pendingIds (Map.delete id1 (Map.delete id2 children)))
    *** QED) &&&

    (idUniqueCausalTree (CausalTree wop2op1 (Map.delete id1 (Map.delete id2 children)))
    `cast` idUniqueMap (Map.delete id1 (Map.delete id2 children))
    `cast` idUniqueWeave wop2op1
    `cast` ()) &&&

    lemmaApplyAtomFoldNeq (CausalTree wop2op1 (Map.delete id1 (Map.delete id2 children))) id1 id2 pops1 pops2 &&&

    (Map.updateLookupWithKey constConstNothing id1 (Map.delete id2 children)
    ==. (Just pops1, Map.delete id1 (Map.delete id2 children))
    *** QED) &&&
    (List.foldl' (applyAtomHelper pid) (CausalTree wop2 (Map.delete id2 children)) [atom1]
    ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid (CausalTree wop2 (Map.delete id2 children)) atom1) []
    ==. applyAtomHelper pid (CausalTree wop2 (Map.delete id2 children)) atom1
    ==. applyAtom (CausalTree wop2 (Map.delete id2 children)) pid atom1
    ==. List.foldl' (applyAtomHelper id1) (CausalTree wop2op1 (Map.delete id1 (Map.delete id2 children))) pops1
    *** QED) &&&

    (Map.updateLookupWithKey constConstNothing id2 (Map.delete id1 children)
    ==. (Just pops2, Map.delete id2 (Map.delete id1 children))
    *** QED) &&&
    (List.foldl' (applyAtomHelper pid) (CausalTree wop1 (Map.delete id1 children)) [atom2]
    ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid (CausalTree wop1 (Map.delete id1 children)) atom2) []
    ==. applyAtomHelper pid (CausalTree wop1 (Map.delete id1 children)) atom2
    ==. applyAtom (CausalTree wop1 (Map.delete id1 children)) pid atom2
    ==. List.foldl' (applyAtomHelper id2) (CausalTree wop1op2 (Map.delete id2 (Map.delete id1 children))) pops2
    *** QED) &&&

    lemmaInsertInWeaveJustEq weave pid wop1 wop2 atom1 atom2 &&&
    (Just wop1op2 ==. Just wop2op1 *** QED)

  | Just wop1 <- insertInWeave weave pid atom1
  , Just wop2 <- insertInWeave weave pid atom2
  , Nothing <- Map.lookup id1 children
  , Nothing <- Map.lookup id2 children
  = (Map.updateLookupWithKey constConstNothing id1 children
    ==. (Nothing, children)
    *** QED) &&&
    (applyAtom x pid atom1
    ==. CausalTree wop1 children
    *** QED) &&&
    (Map.updateLookupWithKey constConstNothing id2 children
    ==. (Nothing, children)
    *** QED) &&&
    (applyAtom x pid atom2
    ==. CausalTree wop2 children
    *** QED) &&&
    let Just wop1op2 = insertInWeave wop1 pid atom2
        Just wop2op1 = insertInWeave wop2 pid atom1 in
    lemmaInsertInWeaveJustEq weave pid wop1 wop2 atom1 atom2 &&&
    (Just wop1op2 ==. Just wop2op1 *** QED) &&&
    (applyAtom (applyAtom x pid atom1) pid atom2
    ==. applyAtom (CausalTree wop1 children) pid atom2
    ==. CausalTree wop1op2 children
    ==. CausalTree wop2op1 children
    ==. applyAtom (CausalTree wop2 children) pid atom1
    ==. applyAtom (applyAtom x pid atom2) pid atom1
    *** QED)
  | Nothing <- insertInWeave weave pid atom1
  = Nothing ==. insertInWeave weave pid atom1 *** QED
  | Nothing <- insertInWeave weave pid atom2
  = Nothing ==. insertInWeave weave pid atom2  *** QED

