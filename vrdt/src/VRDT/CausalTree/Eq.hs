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
import           VRDT.CausalTree.NEq (lemmaApplyAtomFoldNeq)
import           Liquid.ProofCombinators
import           ProofCombinators

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

