{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
--{-@ LIQUID "--ple" @-}
{-@ LIQUID "--ple-local" @-}
{-@ LIQUID "--noadt" @-}
module VRDT.CausalTree.Lemmas where
import           Liquid.Data.Maybe
import           Liquid.Data.Map                ( Map )
import qualified Liquid.Data.Map               as Map
import qualified Data.Set                      as S
import           Liquid.Data.Map.Props
import           VRDT.Internal

import           VRDT.CausalTree.Internal
import           Prelude                 hiding ( Maybe(..)
                                                , empty
                                                , (++)
                                                )
import qualified Liquid.Data.List              as List
import Liquid.ProofCombinators
import ProofCombinators

{-@ ple atomGreaterThanAntiSym @-}
{-@ atomGreaterThanAntiSym :: Ord id => x:CausalTreeAtom id a -> {y:CausalTreeAtom id a | atomGreaterThan x y} -> {not (atomGreaterThan y x)} @-}
atomGreaterThanAntiSym :: Ord id => CausalTreeAtom id a -> CausalTreeAtom id a -> ()
atomGreaterThanAntiSym (CausalTreeAtom a1 CausalTreeLetterRoot) (CausalTreeAtom a2 CausalTreeLetterRoot)     = ()
atomGreaterThanAntiSym a1@(CausalTreeAtom _ CausalTreeLetterRoot) a2@(CausalTreeAtom _ CausalTreeLetterDelete)    = assert (atomGreaterThan a1 a2) &&& assert (not (atomGreaterThan a2 a1))
atomGreaterThanAntiSym (CausalTreeAtom _ CausalTreeLetterRoot) (CausalTreeAtom _ (CausalTreeLetter _))                          = ()
atomGreaterThanAntiSym (CausalTreeAtom a1 CausalTreeLetterDelete) (CausalTreeAtom a2 CausalTreeLetterDelete) = ()
atomGreaterThanAntiSym (CausalTreeAtom _ CausalTreeLetterDelete) (CausalTreeAtom _ CausalTreeLetterRoot)     = ()
atomGreaterThanAntiSym (CausalTreeAtom _ CausalTreeLetterDelete) (CausalTreeAtom _ _)                        = ()
atomGreaterThanAntiSym (CausalTreeAtom a1 (CausalTreeLetter _)) (CausalTreeAtom a2 (CausalTreeLetter _))     = ()
atomGreaterThanAntiSym (CausalTreeAtom a1 (CausalTreeLetter _)) (CausalTreeAtom a2 _)                        = ()

{-@ ple atomGreaterThanTotal @-}
{-@ atomGreaterThanTotal :: Ord id => x:CausalTreeAtom id a -> {y: CausalTreeAtom id a | causalTreeAtomId x /= causalTreeAtomId y} -> {atomGreaterThan x y || atomGreaterThan y x} @-}
atomGreaterThanTotal :: Ord id => CausalTreeAtom id a -> CausalTreeAtom id a -> ()
atomGreaterThanTotal (CausalTreeAtom a1 CausalTreeLetterRoot) (CausalTreeAtom a2 CausalTreeLetterRoot)     = ()
atomGreaterThanTotal a1@(CausalTreeAtom _ CausalTreeLetterRoot) a2@(CausalTreeAtom _ CausalTreeLetterDelete)    = assert (atomGreaterThan a1 a2) &&& assert (not (atomGreaterThan a2 a1))
atomGreaterThanTotal (CausalTreeAtom _ CausalTreeLetterRoot) (CausalTreeAtom _ (CausalTreeLetter _))                          = ()
atomGreaterThanTotal (CausalTreeAtom a1 CausalTreeLetterDelete) (CausalTreeAtom a2 CausalTreeLetterDelete) = ()
atomGreaterThanTotal (CausalTreeAtom _ CausalTreeLetterDelete) (CausalTreeAtom _ CausalTreeLetterRoot)     = ()
atomGreaterThanTotal (CausalTreeAtom _ CausalTreeLetterDelete) (CausalTreeAtom _ _)                        = ()
atomGreaterThanTotal (CausalTreeAtom a1 (CausalTreeLetter _)) (CausalTreeAtom a2 (CausalTreeLetter _))     = ()
atomGreaterThanTotal (CausalTreeAtom a1 (CausalTreeLetter _)) (CausalTreeAtom a2 _)                        = ()

{-@ ple lemmaInsertAtomTwice @-}
{-@ lemmaInsertAtomTwice :: Ord id => cts:[CausalTreeWeave id a] -> a1:CausalTreeAtom id a -> {a2:CausalTreeAtom id a | causalTreeAtomId a2 /= causalTreeAtomId a1} ->
   {insertAtom (insertAtom cts a1) a2 == insertAtom (insertAtom cts a2) a1} @-}
lemmaInsertAtomTwice
  :: Ord id => [CausalTreeWeave id a] -> CausalTreeAtom id a -> CausalTreeAtom id a -> ()
lemmaInsertAtomTwice xs a1 a2
  | a1 `atomGreaterThan` a2
  = lemmaInsertAtomTwice' xs a1 a2
  | otherwise
  = atomGreaterThanTotal a1 a2 &&& lemmaInsertAtomTwice' xs a2 a1

{-@ ple lemmaInsertAtomTwice' @-}
{-@ lemmaInsertAtomTwice' :: Ord id => cts:[CausalTreeWeave id a] -> a1:CausalTreeAtom id a -> {a2:CausalTreeAtom id a | causalTreeAtomId a2 /= causalTreeAtomId a1 && atomGreaterThan a1 a2} ->
   {insertAtom (insertAtom cts a1) a2 == insertAtom (insertAtom cts a2) a1} @-}
lemmaInsertAtomTwice'
  :: Ord id => [CausalTreeWeave id a] -> CausalTreeAtom id a -> CausalTreeAtom id a -> ()
lemmaInsertAtomTwice' [] a1 a2 =
  (insertAtom [] a1
  ==. [CausalTreeWeave a1 []]
  *** QED) &&&
  (insertAtom [] a2
  ==. [CausalTreeWeave a2 []]
  *** QED) &&&
  (causalTreeWeaveAtom (CausalTreeWeave a1 []) ==. a1 *** QED) &&&
  (insertAtom (insertAtom [] a1) a2
  ==. insertAtom ([CausalTreeWeave a1 []]) a2
    ? atomGreaterThanAntiSym a1 a2
  ==. CausalTreeWeave a1 [] : CausalTreeWeave a2 [] : []
  ==. insertAtom (insertAtom [] a2) a1
  *** QED)
lemmaInsertAtomTwice' (x:xs) a1 a2
  | a2 `atomGreaterThan` (causalTreeWeaveAtom x)
  = atomGreaterThanAntiSym a1 a2
  | a1 `atomGreaterThan` (causalTreeWeaveAtom x)
  = (insertAtom (x:xs) a2
    ==. x:insertAtom xs a2
    *** QED) &&&
    atomGreaterThanAntiSym a1 a2
  | otherwise
  = atomGreaterThanAntiSym a1 a2 &&&
    lemmaInsertAtomTwice' xs a1 a2


{-@ ple lemmaInsertInWeaveNothingEq  @-}
{-@ lemmaInsertInWeaveNothingEq :: Ord id => w:CausalTreeWeave id a -> pid:id ->
  {op1:CausalTreeAtom id a | insertInWeave w pid op1 == Nothing} -> op2:CausalTreeAtom id a ->
  {insertInWeave w pid op2 == Nothing} @-}
lemmaInsertInWeaveNothingEq
  :: Ord id
  => CausalTreeWeave id a
  -> id
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lemmaInsertInWeaveNothingEq w pid op1 op2
  | Nothing <- insertInWeave w pid op1
  , Nothing <- insertInWeave w pid op2
  = ()
  | Nothing <- insertInWeave w pid op1
  , Just _ <- insertInWeave w pid op2
  = ()


{-@ applyAtomFoldlRespectsUniq ::
  Ord id
=> {ct:CausalTree id a | idUniqueCausalTree ct}
-> {pid:id | S.member pid (weaveIds (causalTreeWeave ct))}
-> {atoms:[CausalTreeAtom id a] | idUniqueList atoms && S.null (S.intersection (pendingListIds atoms) (causalTreeIds ct))}
-> {idUniqueCausalTree (List.foldl' (applyAtomHelper pid) ct atoms)}
  / [causalTreePendingSize ct, 1, List.length atoms]
@-}
applyAtomFoldlRespectsUniq ::
    Ord id
 => CausalTree id a
 -> id
 -> [CausalTreeAtom id a]
 -> ()
applyAtomFoldlRespectsUniq ct@(CausalTree weave pending) pid [] =
  List.foldl' (applyAtomHelper pid) ct [] === ct *** QED
applyAtomFoldlRespectsUniq ct@(CausalTree weave pending) pid (atom@(CausalTreeAtom aid _):atoms) =
  let CausalTree weave' pending' = List.foldl' (applyAtomHelper pid) ct (atom:atoms) in
  (List.foldl' (applyAtomHelper pid) ct (atom:atoms)
  ==. List.foldl' (applyAtomHelper pid) (applyAtomHelper pid ct atom) atoms
  ==. List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom) atoms
  *** QED)     &&&
  (idUniqueCausalTree (List.foldl' (applyAtomHelper pid) ct (atom:atoms))
  ==. idUniqueCausalTree (List.foldl' (applyAtomHelper pid) (applyAtom ct pid atom) atoms)
  ==.   (idUniqueWeave weave' &&
         idUniqueMap pending' &&
         S.null (S.intersection (weaveIds weave') (pendingIds pending')))
  *** QED) &&&
  lemmaApplyAtomIds ct pid atom     &&&
  (idUniqueCausalTree ct
  ==. (idUniqueWeave weave &&
         idUniqueMap pending &&
         S.null (S.intersection (weaveIds weave) (pendingIds pending)))
  *** QED) &&&
  toProof (S.null (S.intersection (pendingListIds (atom:atoms)) (causalTreeIds ct))) &&&
  toProof (S.null (S.intersection (S.union (S.singleton (aid)) (pendingListIds atoms)) (causalTreeIds ct))) &&&
  (causalTreePendingSize ct *** QED) &&&
  applyAtomRespectsUniq ct pid atom &&&
  (causalTreeIds (applyAtom ct pid atom)
  ==. S.union (S.singleton (aid)) (causalTreeIds ct)
  *** QED) &&&
   (True
    ==. idUniqueList (atom:atoms)
    ==. (not (S.member (aid) (pendingListIds atoms)) && idUniqueList atoms)
    *** QED) &&&
  toProof (idUniqueList atoms) &&&
  (S.intersection (pendingListIds (atom:atoms) ) (causalTreeIds (applyAtom ct pid atom))
  ==. S.intersection (S.union (S.singleton (aid)) (pendingListIds atoms)) (causalTreeIds (applyAtom ct pid atom))
  *** QED) &&&
  toProof (not (S.member (aid) (pendingListIds atoms))) &&&
  (S.intersection (pendingListIds atoms) (causalTreeIds (applyAtom ct pid atom))
  ==. S.intersection (pendingListIds atoms) (S.union (S.singleton (aid)) (causalTreeIds ct))
  *** QED) &&&
  toProof (S.null (S.intersection (pendingListIds atoms) (causalTreeIds (applyAtom ct pid atom)))) &&&
  assert (causalTreePendingSize (applyAtom ct pid atom) <= causalTreePendingSize (applyAtom ct pid atom)) &&&
  assert (List.length atoms <= List.length (atom:atoms)) &&&
  applyAtomFoldlRespectsUniq (applyAtom ct pid atom) pid atoms


{-@ applyAtomRespectsUniq ::
   Ord id
=> {ct:CausalTree id a | idUniqueCausalTree ct}
-> pid:id
-> {atom:CausalTreeAtom id a | not (S.member (causalTreeAtomId atom) (causalTreeIds ct))}
-> {idUniqueCausalTree (applyAtom ct pid atom)}
 / [causalTreePendingSize ct, 0, 0]
@-}
applyAtomRespectsUniq :: forall id a. 
     Ord id
  => CausalTree id a
  -> id
  -> CausalTreeAtom id a
  -> ()
applyAtomRespectsUniq ct@(CausalTree weave pending) pid atom@(CausalTreeAtom aid _)
  | Nothing <- insertInWeave weave pid atom
  = (not (S.member pid (weaveIds weave)) *** QED) &&&
  insertPendingRespectsUniq pid atom pending &&&
  (applyAtom ct pid atom
  ==. CausalTree weave (insertPending pid atom pending)
  *** QED) &&&
  (idUniqueCausalTree (applyAtom ct pid atom)
  ==. idUniqueCausalTree (CausalTree weave (insertPending pid atom pending))
  ==.   (idUniqueWeave weave &&
   idUniqueMap (insertPending pid atom pending) &&
   S.null (S.intersection (weaveIds weave) (pendingIds (insertPending pid atom pending))))
  *** QED) &&&
  (True
  ==. idUniqueCausalTree ct
  ==. (idUniqueWeave weave && idUniqueMap pending && S.null (S.intersection (weaveIds weave) (pendingIds pending)))
  *** QED) &&&
  toProof (idUniqueWeave weave && not (S.member aid (causalTreeIds ct))) &&&
  toProof (idUniqueMap (insertPending pid atom pending))
  | Just weave' <- insertInWeave weave pid atom
  , Nothing <- Map.lookup aid pending
  = (Map.updateLookupWithKey constConstNothing aid pending
    ==. (Nothing, pending)
    *** QED)&&&
    (applyAtom ct pid atom
    ==. CausalTree weave' pending
    *** QED) &&&
  (idUniqueCausalTree (applyAtom ct pid atom)
  ==. idUniqueCausalTree (CausalTree weave' pending)
  ==.   (idUniqueWeave weave' &&
   idUniqueMap pending &&
   S.null (S.intersection (weaveIds weave) (pendingIds pending)))
  *** QED) &&&
  (True
  ==. idUniqueCausalTree ct
  ==. (idUniqueWeave weave && idUniqueMap pending && S.null (S.intersection (weaveIds weave) (pendingIds pending)))
  *** QED) &&&
  toProof (idUniqueWeave weave && not (S.member aid (causalTreeIds ct))) &&&
  toProof (idUniqueWeave weave') &&&
  toProof (idUniqueMap pending)

  | Just weave' <- insertInWeave weave pid atom
  , Just [] <- Map.lookup aid pending
  = (Map.updateLookupWithKey constConstNothing aid pending
     ? (constConstNothing aid [] ==. Nothing *** QED)
    ==. (Just [], Map.delete aid pending)
    *** QED) &&&
    (applyAtom ct pid atom
    ==. List.foldl' (applyAtomHelper aid) (CausalTree weave' (Map.delete aid pending)) []
    ==. CausalTree weave' (Map.delete aid pending)
    *** QED) &&&
  (idUniqueCausalTree (applyAtom ct pid atom)
  ==. idUniqueCausalTree (CausalTree weave' pending)
  ==.   (idUniqueWeave weave' &&
   idUniqueMap pending &&
   S.null (S.intersection (weaveIds weave) (pendingIds pending)))
  *** QED) &&&
  (True
  ==. idUniqueCausalTree ct
  ==. (idUniqueWeave weave && idUniqueMap pending && S.null (S.intersection (weaveIds weave) (pendingIds pending)))
  *** QED) &&&
  toProof (idUniqueWeave weave && not (S.member aid (causalTreeIds ct))) &&&
  toProof (idUniqueWeave weave') &&&
  (pendingListIds ([] :: [CausalTreeAtom id a]) === S.empty *** QED) &&&
  lemmaDeleteSubsetJust pending aid [] S.empty &&&
  toProof (idUniqueMap pending)
  | Just weave' <- insertInWeave weave pid atom
  , Just pops@(_:_) <- Map.lookup aid pending
  = (Map.updateLookupWithKey constConstNothing aid pending
     ? (constConstNothing aid pops ==. Nothing *** QED)
    ==. (Just pops, Map.delete aid pending)
    *** QED)&&&
    toProof (not (S.member aid (Map.keys (Map.delete aid pending)))) &&&
    (Map.lookup aid (Map.delete aid pending)
    ==. case Map.lookup aid (Map.delete aid pending) of
        Nothing -> Nothing
        Just _ -> Nothing ? toProof (S.member aid (Map.keys (Map.delete aid pending)))
    *** QED) &&&
    (Map.updateLookupWithKey constConstNothing aid (Map.delete aid pending)
    ==. (Nothing, Map.delete aid pending)
    *** QED)&&&
    (applyAtom ct pid atom
    ==. List.foldl' (applyAtomHelper aid) (CausalTree weave' (Map.delete aid pending)) pops
    *** QED) &&&
    (applyAtom (CausalTree weave (Map.delete aid pending)) pid atom
    ==. CausalTree weave' (Map.delete aid pending)
    *** QED) &&&
  (True
  ==. idUniqueCausalTree ct
  ==. (idUniqueWeave weave && idUniqueMap pending && S.null (S.intersection (weaveIds weave) (pendingIds pending)))
  *** QED) &&&
    lemmaDeleteSubsetJust pending aid pops (pendingListIds pops) &&&
    lemmaApplyAtomIds ct pid atom &&&
    lemmaApplyAtomIds (CausalTree weave (Map.delete aid pending)) pid atom &&&
    (causalTreeIds (CausalTree weave' (Map.delete aid pending)) ==. S.union (causalTreeIds (CausalTree weave (Map.delete aid pending))) (S.singleton aid) *** QED) &&&
    lemmaLookupSubsetOf pending aid pops &&&
    (Map.lookup aid pending ==. Just pops *** QED) &&&
    toProof (idUniqueList pops) &&&
    toProof (S.null (S.intersection (pendingListIds pops) (pendingIds (Map.delete aid pending)))) &&&
    toProof (S.isSubsetOf (pendingListIds pops)  (pendingIds pending)) &&&
    (weaveIds weave' ==. S.union (S.singleton aid) (weaveIds weave) *** QED) &&&
    (causalTreeIds ct
    ==. S.union (weaveIds weave) (pendingIds pending)
    *** QED) &&&
    toProof (not (S.member aid (pendingIds pending))) &&&
    toProof (S.null (S.intersection (pendingIds pending) (weaveIds weave'))) &&&
    toProof (S.null (S.intersection (pendingListIds pops) (causalTreeIds (CausalTree weave' (Map.delete aid pending))))) &&&
    (idUniqueCausalTree (CausalTree weave' (Map.delete aid pending))
    ==. True
    *** QED) &&&
    lemmaDeleteShrink pending aid pops &&&
    assert (causalTreePendingSize ct > causalTreePendingSize (CausalTree weave' (Map.delete aid pending))) &&&
    applyAtomFoldlRespectsUniq (CausalTree weave' (Map.delete aid pending)) aid pops


{-@ lemmaInsertInWeaveListJustEq :: Ord id =>
  ws:[CausalTreeWeave id a] ->
  pid:id ->
  wop1 : [CausalTreeWeave id a] ->
  wop2 : [CausalTreeWeave id a] -> 
  {op1:CausalTreeAtom id a | insertInWeaveChildren ws pid op1 == Just wop1} -> {op2:CausalTreeAtom id a | (insertInWeaveChildren ws pid op2 == Just wop2) && (causalTreeAtomId op1 /= causalTreeAtomId op2)} ->
  {insertInWeaveChildren wop1 pid op2 == insertInWeaveChildren wop2 pid op1 && isJust (insertInWeaveChildren wop1 pid op2)}
  / [causalTreeWeaveLengthList ws, List.length ws]@-}
lemmaInsertInWeaveListJustEq
  :: Ord id
  => [CausalTreeWeave id a]
  -> id
  -> [CausalTreeWeave id a]
  -> [CausalTreeWeave id a]
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lemmaInsertInWeaveListJustEq
  []
  pid
  wop1
  wop2
  atom1@(CausalTreeAtom id1 _)
  atom2@(CausalTreeAtom id2 _)
  =  (insertInWeaveChildren [] pid atom1
      === Just wop1
      *** QED) &&&
     (insertInWeaveChildren [] pid atom1
      === Nothing
      *** QED) 
lemmaInsertInWeaveListJustEq
  ws@(w@(CausalTreeWeave catom@(CausalTreeAtom cid _) children):ws')
  pid
  wop1
  wop2
  atom1@(CausalTreeAtom id1 _)
  atom2@(CausalTreeAtom id2 _)
  | Just wop1' <- insertInWeave w pid atom1
  , Just wop2' <- insertInWeave w pid atom2
  = (insertInWeaveChildren ws pid atom1
      ==. Just (wop1':ws')
      ==. Just wop1
      *** QED) &&&
     (insertInWeaveChildren ws pid atom2
      ==. Just (wop2':ws')
      ==. Just wop2
      *** QED) &&&
     let Just wop1op2' = insertInWeave wop1' pid atom2
         Just wop2op1' = insertInWeave wop2' pid atom1 in
     (causalTreeWeaveLengthList ws
     `cast` causalTreeWeaveLengthList ws'
     `cast` causalTreeWeaveLength w
     `cast` List.length ws
     `cast` List.length ws'
     `cast` ()) &&&
     toProof (causalTreeWeaveLengthList ws >= causalTreeWeaveLength w) &&&
     toProof (List.length ws > 0) &&&
     lemmaInsertInWeaveJustEq w pid wop1' wop2' atom1 atom2 &&&
     (wop1op2' ==. wop2op1' *** QED) &&&
     (insertInWeaveChildren (wop1':ws') pid atom2
     ==. Just (wop1op2':ws')
     *** QED) &&&
     (insertInWeaveChildren (wop2':ws') pid atom1
     ==. Just (wop2op1':ws')
     ==. Just (wop1op2':ws')
     *** QED)
  | Just _ <- insertInWeave w pid atom1
  , Nothing <- insertInWeave w pid atom2
  = ()
  | Nothing <- insertInWeave w pid atom1
  , Just _ <- insertInWeave w pid atom2
  = ()
  | Nothing <- insertInWeave w pid atom1
  , Nothing <- insertInWeave w pid atom2
  = (insertInWeaveChildren ws pid atom1
    -- ==. Just (w:wsop1')
    ==. Just wop1
    *** QED) &&&
    (insertInWeaveChildren ws pid atom2
    -- ==. Just (w:wsop2')
    ==. Just wop2
    *** QED) &&&
    let Just wsop1' = insertInWeaveChildren ws' pid atom1
        Just wsop2' = insertInWeaveChildren ws' pid atom2 in
    (insertInWeaveChildren ws pid atom1
    ==. Just (w:wsop1')
    *** QED) &&&
    (insertInWeaveChildren ws pid atom2
    ==. Just (w:wsop2')
    *** QED) &&&
     (causalTreeWeaveLengthList ws
     `cast` causalTreeWeaveLengthList ws'
     `cast` causalTreeWeaveLength w
     `cast` List.length ws
     `cast` List.length ws'
     `cast` ()) &&&
    let Just wsop1op2' = insertInWeaveChildren wsop1' pid atom2
        Just wsop2op1' = insertInWeaveChildren wsop2' pid atom1 in
    (insertInWeaveChildren (w:wsop1') pid atom2
    ==. Just (w:wsop1op2')
    *** QED) &&&
    (insertInWeaveChildren (w:wsop2') pid atom1
    ==. Just (w:wsop2op1')
    *** QED) &&&    
    lemmaInsertInWeaveListJustEq ws' pid wsop1' wsop2' atom1 atom2 &&&
    (Just (w:wsop1op2')
    ==. Just (w:wsop2op1')
    *** QED)
    
{-@ lemmaInsertInWeaveJustEq :: Ord id => w:CausalTreeWeave id a -> pid:id -> wop1 : CausalTreeWeave id a ->
  wop2 : CausalTreeWeave id a -> 
  {op1:CausalTreeAtom id a | insertInWeave w pid op1 == Just wop1} -> {op2:CausalTreeAtom id a | (insertInWeave w pid op2 == Just wop2) && (causalTreeAtomId op1 /= causalTreeAtomId op2)} ->
  {insertInWeave wop1 pid op2 == insertInWeave wop2 pid op1 && isJust (insertInWeave wop1 pid op2)} / [causalTreeWeaveLength w, 0] @-}
lemmaInsertInWeaveJustEq
  :: Ord id
  => CausalTreeWeave id a
  -> id
  -> CausalTreeWeave id a
  -> CausalTreeWeave id a
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lemmaInsertInWeaveJustEq
  w@(CausalTreeWeave catom@(CausalTreeAtom cid _) children)
  pid
  wop1
  wop2
  atom1@(CausalTreeAtom id1 _)
  atom2@(CausalTreeAtom id2 _)
  | Just _ <- insertInWeave w pid atom1
  , Just _ <- insertInWeave w pid atom2
  , cid == pid
  = assert (causalTreeAtomId catom == pid) &&&
    (insertInWeave w pid atom1
    ==. Just wop1
    ==. Just (CausalTreeWeave catom (insertAtom children atom1))
    *** QED) &&&

    (insertInWeave w pid atom2
    ==. Just wop2
    ==. Just (CausalTreeWeave catom (insertAtom children atom2))
    *** QED) &&&

    (insertInWeave wop1 pid atom2
    ==. Just (CausalTreeWeave catom (insertAtom (insertAtom children atom1) atom2))
    *** QED) &&&

    (insertInWeave wop2 pid atom1
    ==. Just (CausalTreeWeave catom (insertAtom (insertAtom children atom2) atom1))
    *** QED) &&&

  lemmaInsertAtomTwice children atom1 atom2
  
  | Just _ <- insertInWeave w pid atom1
  , Just _ <- insertInWeave w pid atom2
  = (causalTreeWeaveLength w
    === 1 + causalTreeWeaveLengthList children
    *** QED) &&&

    let Just childrenop1 = insertInWeaveChildren children pid atom1
        Just childrenop2 = insertInWeaveChildren children pid atom2 in

    let Just childrenop1op2 = insertInWeaveChildren childrenop1 pid atom2
        Just childrenop2op1 = insertInWeaveChildren childrenop2 pid atom1 in

    (insertInWeave w pid atom1
    ==. Just wop1
    === Just (CausalTreeWeave catom childrenop1)
    *** QED) &&&

    (insertInWeave w pid atom2
    ==. Just wop2
    === Just (CausalTreeWeave catom childrenop2)
    *** QED) &&&


    (insertInWeave wop1 pid atom2
    === Just (CausalTreeWeave catom childrenop1op2)
    *** QED) &&&

    (insertInWeave wop2 pid atom1
    ==. Just (CausalTreeWeave catom childrenop2op1)
    *** QED) &&&
    
    lemmaInsertInWeaveListJustEq children pid childrenop1 childrenop2 atom1 atom2
  | Nothing <- insertInWeave w pid atom1
  = insertInWeave w pid atom1 ==. Just wop1 *** QED
  | Nothing <- insertInWeave w pid atom2
  = ()

--{-@ ple lemmaInsertAtomInsertInWeaveChildren @-}
{-@ lemmaInsertAtomInsertInWeaveChildren :: Ord id
  => ws:[CausalTreeWeave id a]
  -> atom1:CausalTreeAtom id a
  -> {pid2:id | pid2 /= causalTreeAtomId atom1}
  -> {atom2:CausalTreeAtom id a | causalTreeAtomId atom1 /= causalTreeAtomId atom2}
  -> {wsop2:[CausalTreeWeave id a] | insertInWeaveChildren ws pid2 atom2 == Just wsop2}
  -> {Just (insertAtom wsop2 atom1) == insertInWeaveChildren (insertAtom ws atom1) pid2 atom2}
@-}
lemmaInsertAtomInsertInWeaveChildren :: Ord id
  => [CausalTreeWeave id a]
  -> CausalTreeAtom id a
  -> id
  -> CausalTreeAtom id a
  -> [CausalTreeWeave id a]
  -> ()
lemmaInsertAtomInsertInWeaveChildren [] atom1 pid2 atom2 wsop2 =
  Nothing === insertInWeaveChildren [] pid2 atom2 === Just wsop2 *** QED
lemmaInsertAtomInsertInWeaveChildren
  ws@(w@(CausalTreeWeave catom@(CausalTreeAtom cid _) cs):ws')
  atom1@(CausalTreeAtom id1 _)
  pid2
  atom2@(CausalTreeAtom id2 _)
  wsop2
  | Nothing <- insertInWeaveChildren ws pid2 atom2
  = insertInWeaveChildren ws pid2 atom2 === Just wsop2 *** QED
  | not (atom1 `atomGreaterThan` catom)
  , Just _ <- insertInWeaveChildren ws pid2 atom2
  , Nothing <- insertInWeave w pid2 atom2
  = (insertAtom ws atom1
    ==. w : insertAtom ws' atom1
    *** QED) &&&
    (insertInWeaveChildren ws pid2 atom2
    ==. Just wsop2
    *** QED) &&&
    let Just wsop2' = insertInWeaveChildren ws' pid2 atom2 in
    (Just wsop2
    ==. Just (w:wsop2')
    *** QED) &&&
    (insertAtom wsop2 atom1
    ==. w:insertAtom wsop2' atom1
    *** QED) &&&
    let Just ws'' = insertInWeaveChildren (insertAtom ws' atom1) pid2 atom2 in
    (insertInWeaveChildren (insertAtom ws atom1) pid2 atom2
    ==. insertInWeaveChildren (w:insertAtom ws' atom1) pid2 atom2
    ==. Just (w:ws'')
    *** QED) &&&
    lemmaInsertAtomInsertInWeaveChildren ws' atom1 pid2 atom2 wsop2' &&&
    (Just (insertAtom wsop2' atom1) ==. Just ws'' *** QED) &&&
    (Just (w:insertAtom wsop2' atom1) ==. Just (w:ws'') *** QED)

  | not (atom1 `atomGreaterThan` catom)
  , Just _ <- insertInWeaveChildren ws pid2 atom2
  , Just w' <- insertInWeave w pid2 atom2
  = (insertAtom ws atom1
    ==. w : insertAtom ws' atom1
    *** QED) &&&
    (insertInWeaveChildren ws pid2 atom2
    ==. Just wsop2
    ==. Just (w':ws')
    *** QED) &&&
    (insertInWeaveChildren (w : insertAtom ws' atom1) pid2 atom2
    ==. Just (w':insertAtom ws' atom1)
    *** QED) &&&
    (case cid == pid2 of
              True -> assert (causalTreeAtomId catom == cid) &&&
                      ( insertInWeave w pid2 atom2
                      ==. Just (CausalTreeWeave catom (insertAtom cs atom2))
                      *** QED) &&&
                      (Just wsop2
                       ==. Just (CausalTreeWeave catom (insertAtom cs atom2):ws')
                      *** QED) &&&
                        (insertAtom wsop2 atom1
                        ==. CausalTreeWeave catom (insertAtom cs atom2): insertAtom ws' atom1
                        *** QED)   ;
              False -> let Just ww = insertInWeaveChildren cs pid2 atom2 in
                       (insertInWeave w pid2 atom2
                       ==. Just (CausalTreeWeave catom ww)
                       *** QED) &&&
                      (Just wsop2
                       ==. Just (CausalTreeWeave catom ww:ws')
                      *** QED) &&&           
                       (insertAtom wsop2 atom1
                        ==. CausalTreeWeave catom ww:insertAtom ws' atom1
                        *** QED)) &&&
    ()
  | atom1 `atomGreaterThan` catom
  -- , Nothing <- insertInWeave w pid2 atom2
  , Just _ <- insertInWeaveChildren ws pid2 atom2
  = (insertAtom ws atom1
    ==. (CausalTreeWeave atom1 []) : ws
    *** QED) &&&
    (insertInWeaveChildren ws pid2 atom2
    ==. Just wsop2
    *** QED) &&&
    (insertInWeave (CausalTreeWeave atom1 []) pid2 atom2
      ? (insertInWeaveChildren [] pid2 atom2 ==. Nothing *** QED)
     ==. Nothing
     *** QED) &&&
    (insertInWeaveChildren (insertAtom ws atom1) pid2 atom2
    ==. insertInWeaveChildren ((CausalTreeWeave atom1 []) : ws) pid2 atom2
    ==. Just (CausalTreeWeave atom1 []:wsop2)
    *** QED) &&&

    (case insertInWeave w pid2 atom2 of{
       Nothing -> let Just wsop2' = insertInWeaveChildren ws' pid2 atom2 in
           Just wsop2
           ==. Just (w:wsop2')
           *** QED;
       Just w'@(CausalTreeWeave catom'@(CausalTreeAtom cid' _) _) ->
           (case cid == pid2 of
              True -> assert (causalTreeAtomId catom == cid) &&&
                      ( insertInWeave w pid2 atom2
                      ==. Just (CausalTreeWeave catom (insertAtom cs atom2))
                      *** QED) &&&
                      (Just wsop2
                       ==. Just (CausalTreeWeave catom (insertAtom cs atom2):ws')
                      *** QED) &&&
                        (insertAtom wsop2 atom1
                        ==. CausalTreeWeave atom1 []:wsop2
                        *** QED)   ;
              False -> let Just ww = insertInWeaveChildren cs pid2 atom2 in
                       (insertInWeave w pid2 atom2
                       ==. Just (CausalTreeWeave catom ww)
                       *** QED) &&&
                      (Just wsop2
                       ==. Just (CausalTreeWeave catom ww:ws')
                      *** QED) &&&           
                       (insertAtom wsop2 atom1
                        ==. CausalTreeWeave atom1 []:wsop2
                        *** QED))   
       }) &&&
       (Just (insertAtom wsop2 atom1) ==. insertInWeaveChildren (insertAtom ws atom1) pid2 atom2 *** QED)

  | Nothing <- insertInWeaveChildren ws pid2 atom2
  = Nothing === insertInWeaveChildren ws pid2 atom2 === Just wsop2 *** QED

{-@ lemmaInsertInWeaveChildrenJustEq2 :: Ord id
  => w:[CausalTreeWeave id a]
  -> pid1:id
  -> pid2:id
  -> wop1 : [CausalTreeWeave id a]
  -> wop2 : [CausalTreeWeave id a]
  -> {op1:CausalTreeAtom id a | (insertInWeaveChildren w pid1 op1 == Just wop1) && (causalTreeAtomId op1 /= pid2)}
  -> {op2:CausalTreeAtom id a | (insertInWeaveChildren w pid2 op2 == Just wop2) && (causalTreeAtomId op1 /= causalTreeAtomId op2) && (causalTreeAtomId op2 /= pid1)}
  -> {insertInWeaveChildren wop1 pid2 op2 == insertInWeaveChildren wop2 pid1 op1 && isJust (insertInWeaveChildren wop1 pid2 op2)}
/ [causalTreeWeaveLengthList w, List.length w, 0]@-}
lemmaInsertInWeaveChildrenJustEq2
  :: Ord id
  => [CausalTreeWeave id a]
  -> id
  -> id
  -> [CausalTreeWeave id a]
  -> [CausalTreeWeave id a]
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lemmaInsertInWeaveChildrenJustEq2
  []
  pid1
  pid2
  wsop1
  wsop2
  atom1
  atom2
  = Nothing === insertInWeaveChildren [] pid1 atom1 === Just wsop1 *** QED
lemmaInsertInWeaveChildrenJustEq2
  (w@(CausalTreeWeave catom@(CausalTreeAtom cid _) children):ws)
  pid1
  pid2
  wsop1
  wsop2
  atom1@(CausalTreeAtom id1 _)
  atom2@(CausalTreeAtom id2 _)
  | pid1 == pid2
  = lemmaInsertInWeaveListJustEq (w:ws) pid1 wsop1 wsop2 atom1 atom2
  | Just wop1 <- insertInWeave w pid1 atom1
  , Just wop2 <- insertInWeave w pid2 atom2
  = toProof (List.length (w:ws)
             `cast` List.length ws
             `cast` causalTreeWeaveLengthList (w:ws)
             `cast` causalTreeWeaveLengthList ws
             `cast` causalTreeWeaveLength w
             `cast` List.length (w:ws)) &&&
    
    (insertInWeaveChildren (w:ws) pid1 atom1
     ==. Just wsop1
     ==. Just (wop1:ws)
     *** QED) &&&
    (insertInWeaveChildren (w:ws) pid2 atom2
     ==. Just wsop2
     ==. Just (wop2:ws)
     *** QED) &&&
    let Just wop1op2 = insertInWeave wop1 pid2 atom2
        Just wop2op1 = insertInWeave wop2 pid1 atom1 in
    lemmaInsertInWeaveJustEq2 w pid1 pid2 wop1 wop2 atom1 atom2 &&&
    (Just wop1op2 ==. Just wop2op1 *** QED) &&&
    (insertInWeaveChildren (wop1:ws) pid2 atom2
    ==. Just (wop1op2:ws)
    *** QED) &&&
    (insertInWeaveChildren (wop2:ws) pid1 atom1
    ==. Just (wop2op1:ws)
    *** QED)
  | Nothing <- insertInWeave w pid1 atom1
  , Nothing <- insertInWeave w pid2 atom2
  = (insertInWeaveChildren (w:ws) pid1 atom1
     ==. Just wsop1
     -- ==. Just (wop1:ws)
     *** QED) &&&
    (insertInWeaveChildren (w:ws) pid2 atom2
     ==. Just wsop2
     -- ==. Just (wop2:ws)
     *** QED) &&&
    let Just wsop1' = insertInWeaveChildren ws pid1 atom1
        Just wsop2' = insertInWeaveChildren ws pid2 atom2 in
    (Just wsop1
    ==. Just (w:wsop1')
    *** QED) &&&
    (Just wsop2
    ==. Just (w:wsop2')
    *** QED) &&&
    let Just wsop2op1' = insertInWeaveChildren wsop2' pid1 atom1
        Just wsop1op2' = insertInWeaveChildren wsop1' pid2 atom2 in
    (insertInWeaveChildren wsop1 pid2 atom2
    ==. Just (w:wsop1op2')
    *** QED) &&&
    (insertInWeaveChildren wsop2 pid1 atom1
    ==. Just (w:wsop2op1')
    *** QED) &&&
    toProof (List.length (w:ws)
             `cast` List.length ws
             `cast` causalTreeWeaveLengthList (w:ws)
             `cast` causalTreeWeaveLengthList ws
             `cast` causalTreeWeaveLength w
             `cast` List.length (w:ws)) &&&
    lemmaInsertInWeaveChildrenJustEq2 ws pid1 pid2 wsop1' wsop2' atom1 atom2 &&&
    (Just wsop1op2' ==. Just wsop2op1' *** QED)
  | Just w' <- insertInWeave w pid1 atom1
  , Nothing <- insertInWeave w pid2 atom2
  = (insertInWeaveChildren (w:ws) pid1 atom1
     ==. Just wsop1
     ==. Just (w':ws)
     *** QED) &&&
    (insertInWeaveChildren (w:ws) pid2 atom2
     ==. Just wsop2
     -- ==. Just (wop2:ws)
     *** QED) &&&
    let Just wsop2' = insertInWeaveChildren ws pid2 atom2 in
    (Just wsop2
    ==. Just (w:wsop2')
    *** QED) &&&
    (case insertInWeave w' pid2 atom2 of
       Nothing -> ()
       Just _ -> ()) &&&
    (insertInWeaveChildren (w':ws) pid2 atom2
    ==. Just (w':wsop2')
    *** QED) &&&
    (insertInWeaveChildren (w:wsop2') pid1 atom1
    ==. Just (w':wsop2')
    *** QED)
  | Just w' <- insertInWeave w pid2 atom2
  , Nothing <- insertInWeave w pid1 atom1
  = (insertInWeaveChildren (w:ws) pid2 atom2
     ==. Just wsop2
     ==. Just (w':ws)
     *** QED) &&&
    (insertInWeaveChildren (w:ws) pid1 atom1
     ==. Just wsop1
     -- ==. Just (wop1:ws)
     *** QED) &&&
    let Just wsop1' = insertInWeaveChildren ws pid1 atom1 in
    (Just wsop1
    ==. Just (w:wsop1')
    *** QED) &&&
    (case insertInWeave w' pid1 atom1 of
       Nothing -> ()
       Just _ -> ()) &&&
    (insertInWeaveChildren (w':ws) pid1 atom1
    ==. Just (w':wsop1')
    *** QED) &&&
    (insertInWeaveChildren (w:wsop1') pid2 atom2
    ==. Just (w':wsop1')
    *** QED)

{-@ lemmaInsertInWeaveJustEq2 :: Ord id
  => w:CausalTreeWeave id a
  -> pid1:id
  -> pid2:id
  -> wop1 : CausalTreeWeave id a
  -> wop2 : CausalTreeWeave id a
  -> {op1:CausalTreeAtom id a | (insertInWeave w pid1 op1 == Just wop1) && (causalTreeAtomId op1 /= pid2)}
  -> {op2:CausalTreeAtom id a | (insertInWeave w pid2 op2 == Just wop2) && (causalTreeAtomId op1 /= causalTreeAtomId op2) && (causalTreeAtomId op2 /= pid1)}
  -> {insertInWeave wop1 pid2 op2 == insertInWeave wop2 pid1 op1 && isJust (insertInWeave wop1 pid2 op2)}
/ [causalTreeWeaveLength w, 0, if (pid1 == (causalTreeAtomId (causalTreeWeaveAtom w))) then 0 else 1]@-}
lemmaInsertInWeaveJustEq2
  :: Ord id
  => CausalTreeWeave id a
  -> id
  -> id
  -> CausalTreeWeave id a
  -> CausalTreeWeave id a
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lemmaInsertInWeaveJustEq2
  w@(CausalTreeWeave catom@(CausalTreeAtom cid _) children)
  pid1
  pid2
  wop1
  wop2
  atom1@(CausalTreeAtom id1 _)
  atom2@(CausalTreeAtom id2 _)
  | pid1 == pid2
  = lemmaInsertInWeaveJustEq w pid1 wop1 wop2 atom1 atom2
  | Just _ <- insertInWeave w pid1 atom1
  , Just _ <- insertInWeave w pid2 atom2
  , pid1 /= cid
  , pid2 /= cid
  = (insertInWeave w pid1 atom1
    === Just wop1
    *** QED) &&&
    (insertInWeave w pid2 atom2
    === Just wop2
    *** QED) &&&
    let Just childrenop1 = insertInWeaveChildren children pid1 atom1
        Just childrenop2 = insertInWeaveChildren children pid2 atom2 in
    (Just wop1
    === Just (CausalTreeWeave catom childrenop1)
    *** QED) &&&
    (Just wop2
    === Just (CausalTreeWeave catom childrenop2)
    *** QED) &&&
    let Just childrenop1op2 = insertInWeaveChildren childrenop1 pid2 atom2
        Just childrenop2op1 = insertInWeaveChildren childrenop2 pid1 atom1 in
    (insertInWeave wop1 pid2 atom2
    === Just (CausalTreeWeave catom childrenop1op2)
    *** QED) &&&
    (insertInWeave wop2 pid1 atom1
    === Just (CausalTreeWeave catom childrenop2op1)
    *** QED) &&&
    toProof (causalTreeWeaveLength w `cast` causalTreeWeaveLengthList children) &&&
    lemmaInsertInWeaveChildrenJustEq2 children pid1 pid2 childrenop1 childrenop2 atom1 atom2 &&&
    (Just childrenop1op2 === Just childrenop2op1 *** QED)
  | Nothing <- insertInWeave w pid1 atom1
  = insertInWeave w pid1 atom1 === Just wop1 *** QED
  | Nothing <- insertInWeave w pid2 atom2
  = insertInWeave w pid2 atom2 === Just wop2 *** QED
  | pid1 == cid
  , Just _ <- insertInWeave w pid1 atom1
  , Just _ <- insertInWeave w pid2 atom2
  = (insertInWeave w pid1 atom1
    ==. Just wop1
    *** QED) &&&
    (insertInWeave w pid2 atom2
    ==. Just wop2
    *** QED) &&&
    let Just childrenop2 = insertInWeaveChildren children pid2 atom2 in
    (Just wop2
    ==. Just (CausalTreeWeave catom childrenop2)
    *** QED) &&&
    (Just wop1
    ==. Just (CausalTreeWeave catom (insertAtom children atom1))
    *** QED) &&&
    (insertInWeave wop2 pid1 atom1
    ==. Just (CausalTreeWeave catom (insertAtom childrenop2 atom1))
    *** QED) &&&
    let Just childrenop1op2 = insertInWeaveChildren (insertAtom children atom1) pid2 atom2 in
    (insertInWeave wop1 pid2 atom2
    ==. Just (CausalTreeWeave catom childrenop1op2)
    *** QED) &&&
    lemmaInsertAtomInsertInWeaveChildren children atom1 pid2 atom2 childrenop2 &&&
    (Just childrenop1op2 ==. Just (insertAtom childrenop2 atom1) *** QED)
  | pid2 == cid -- && pid1 /= cid
  = (if (pid1 == cid) then 0 else 1) `cast`
    (if (pid2 == cid) then 0 else 1) `cast`
    (causalTreeWeaveLength w) `cast`
    lemmaInsertInWeaveJustEq2  w pid2 pid1 wop2 wop1 atom2 atom1

--{-@ ple lemmaInsertInWeaveJustNEq @-}
{-@ lemmaInsertInWeaveJustNEq :: Ord id
  => w:CausalTreeWeave id a
  -> pid1:id
  -> {pid2:id | pid1 /= pid2}
  -> wop2 : CausalTreeWeave id a
  -> {op1:CausalTreeAtom id a | (insertInWeave w pid1 op1 == Nothing) }
  -> {op2:CausalTreeAtom id a | (insertInWeave w pid2 op2 == Just wop2) && (causalTreeAtomId op1 /= causalTreeAtomId op2) && (pid1 /= causalTreeAtomId op2)}
  -> {insertInWeave wop2 pid1 op1 == Nothing}
   @-}
lemmaInsertInWeaveJustNEq
  :: Ord id
  => CausalTreeWeave id a
  -> id
  -> id
  -> CausalTreeWeave id a
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lemmaInsertInWeaveJustNEq w@(CausalTreeWeave catom@(CausalTreeAtom cid _) ws) pid1 pid2 wop2 atom1@(CausalTreeAtom id1 _) atom2@(CausalTreeAtom id2 _)
  | Nothing <- insertInWeave w pid1 atom1
  , Just _ <- insertInWeave w pid2 atom2
  = (insertInWeave w pid2 atom2
    ==. Just wop2
    *** QED) &&&
    (case insertInWeave wop2 pid1 atom1 of
       Nothing -> ()
       Just _ -> ())
  | Just _ <- insertInWeave w pid1 atom1
  = insertInWeave w pid1 atom1 === Nothing *** QED
  | Nothing <- insertInWeave w pid2 atom2
  = insertInWeave w pid2 atom2 === Just wop2 *** QED
  

-- -- 1 is dependent on 2
{-@ lemmaInsertInWeaveJustNEqRel :: Ord id
  => w:CausalTreeWeave id a
  -> pid1:id
  -> {pid2:id | pid1 /= pid2}
  -> wop2 : CausalTreeWeave id a
  -> {op1:CausalTreeAtom id a | (insertInWeave w pid1 op1 == Nothing)}
  -> {op2:CausalTreeAtom id a | (insertInWeave w pid2 op2 == Just wop2) &&
                                (causalTreeAtomId op1 /= causalTreeAtomId op2) &&
                                (pid1 == causalTreeAtomId op2)}
  -> {isJust (insertInWeave wop2 pid1 op1)}
   @-}
lemmaInsertInWeaveJustNEqRel
  :: Ord id
  => CausalTreeWeave id a
  -> id
  -> id
  -> CausalTreeWeave id a
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lemmaInsertInWeaveJustNEqRel w@(CausalTreeWeave catom@(CausalTreeAtom cid _) ws) pid1 pid2 wop2 atom1@(CausalTreeAtom id1 _) atom2@(CausalTreeAtom id2 _)
  | Nothing <- insertInWeave w pid1 atom1
  , Just _ <- insertInWeave w pid2 atom2
  = (insertInWeave w pid2 atom2
    ==. Just wop2
    *** QED) &&&
    (case insertInWeave wop2 pid1 atom1 of
       Nothing -> ()
       Just _ -> ())
  | Just _ <- insertInWeave w pid1 atom1
  = insertInWeave w pid1 atom1 === Nothing *** QED
  | Nothing <- insertInWeave w pid2 atom2
  = insertInWeave w pid2 atom2 === Just wop2 *** QED




-- i think i messed up this one. lemmaFoldIds is supposed to be trivial.
{-@ ple lemmaFoldlIds @-}
{-@ lemmaFoldlIds :: Ord id
  => ct:CausalTree id a
  -> {pid:id | S.member pid (weaveIds (causalTreeWeave ct))}
  -> atoms:[CausalTreeAtom id a]
  -> {causalTreeIds (List.foldl' (applyAtomHelper pid) ct atoms) == S.union (causalTreeIds ct) (pendingListIds atoms) && causalTreePendingSize (List.foldl' (applyAtomHelper pid) ct atoms) <= causalTreePendingSize ct && S.isSubsetOf (weaveIds (causalTreeWeave ct)) (weaveIds (causalTreeWeave (List.foldl' (applyAtomHelper pid) ct atoms)))}
  / [causalTreePendingSize ct, 1, List.length atoms]  @-}
lemmaFoldlIds :: Ord id => CausalTree id a -> id -> [CausalTreeAtom id a] -> ()
lemmaFoldlIds ct pid [] = ()

-- surprisingly, this explicit destruction is necessary
lemmaFoldlIds ct@(CausalTree weave pending) pid (a:_)
  | Nothing <- insertInWeave weave pid a
  = ()

lemmaFoldlIds ct@(CausalTree weave pending) pid (a:as)
  | Just weave' <- insertInWeave weave pid a
  =  case Map.lookup aid pending of {
      Nothing -> (Map.updateLookupWithKey constConstNothing aid pending
             ==. (Nothing, pending)
             *** QED) &&&
               ( applyAtomHelper pid ct a
             ==. applyAtom ct pid a
             ==. CausalTree weave' pending 
             *** QED) &&&
             assert (causalTreePendingSize (applyAtomHelper pid ct a) == causalTreePendingSize ct) &&&
             assert (S.member pid (weaveIds (causalTreeWeave (applyAtomHelper pid ct a))));
      Just [] -> (Map.updateLookupWithKey constConstNothing aid pending
                 ? constConstNothing aid []
             ==. (Just [], Map.delete aid pending)
             *** QED) &&&
               ( applyAtomHelper pid ct a
             ==. List.foldl' (applyAtomHelper aid) (CausalTree weave' (Map.delete aid pending)) []
             ==. CausalTree weave' (Map.delete aid pending)
             *** QED) &&&
             lemmaDeleteShrink pending aid [] &&&
             assert (causalTreePendingSize (applyAtomHelper pid ct a) == causalTreePendingSize ct) &&&
             assert (S.member pid (weaveIds (causalTreeWeave (applyAtomHelper pid ct a))));
      Just pops@(_:_) -> (Map.updateLookupWithKey constConstNothing aid pending
                         ? constConstNothing aid pops
             ==. (Just pops, Map.delete aid pending)
             *** QED) &&&
               ( applyAtomHelper pid ct a
             ==. List.foldl' (applyAtomHelper aid) (CausalTree weave' (Map.delete aid pending)) pops
             ==. applyAtom ct pid a
             *** QED) &&&
             lemmaDeleteShrink pending aid pops &&&
             assert (causalTreePendingSize (CausalTree weave' (Map.delete aid pending)) < causalTreePendingSize ct) &&&
             lemmaFoldlIds (CausalTree weave' (Map.delete aid pending)) aid pops &&&
             assert (causalTreePendingSize (applyAtomHelper pid ct a) <= causalTreePendingSize ct) &&&
             assert (S.member pid (weaveIds (causalTreeWeave (applyAtomHelper pid ct a))))
    } &&&

  -- common
  lemmaApplyAtomIds ct pid a &&&
  lemmaFoldlIds (applyAtomHelper pid ct a) pid as
  where aid = causalTreeAtomId a


-- {-@ lemmaDeleteSubset :: Ord id
--   => pending:Map.Map id [CausalTreeAtom id a]
--   -> k:id
--   -> {S.isSubsetOf (pendingIds (Map.delete k pending)) (pending) }@-}
-- jfioew

{-@ ple lemmaDeleteSubsetJust @-}
{-@ lemmaDeleteSubsetJust :: Ord id
  => pending:Map.Map id [CausalTreeAtom id a]
  -> k:id
  -> {atoms:[CausalTreeAtom id a] | Map.lookup k pending == Just atoms}
  -> {ids:S.Set id | S.isSubsetOf (pendingListIds atoms) ids}
  -> {(S.union ids (pendingIds (Map.delete k pending)) == S.union ids (pendingIds pending)) && (idUniqueMap pending => idUniqueMap (Map.delete k pending)) && (S.isSubsetOf (pendingIds (Map.delete k pending)) (pendingIds pending))}
@-}
lemmaDeleteSubsetJust :: Ord id
  => Map.Map id [CausalTreeAtom id a]
  -> id
  -> [CausalTreeAtom id a]
  -> S.Set id
  -> ()
lemmaDeleteSubsetJust Map.Tip _ _ _ = ()
lemmaDeleteSubsetJust m@(Map.Map k v t) pid atoms ids
  | pid < k
  = ()
  | pid == k
  = (Map.delete k m
    ==. t
    *** QED) &&&
    (Map.lookup k m
    ==. Just v
    ==. Just atoms
    *** QED) &&&
    (pendingIds (Map.delete k m)
    ==. pendingIds t
    *** QED) &&&
    (S.union ids (pendingIds t)
    ==. S.union (S.union ids (pendingListIds v)) (pendingIds t)
    ==. S.union ids (S.union (pendingListIds v) (pendingIds t))
    ==. S.union ids (pendingIds m)
    *** QED)
  | pid > k
  = (Map.delete pid m
    ==. Map.Map k v (Map.delete pid t)
    *** QED) &&&
    (Map.lookup pid m
    ==. Map.lookup pid t
    ==. Just atoms
    *** QED) &&&
    (idUniqueMap m
    ==. (idUniqueList v && S.null (S.intersection (pendingListIds v) (pendingIds t)) && idUniqueMap t)
    *** QED) &&&
    lemmaDeleteSubsetJust t pid atoms ids


{-@ ple lemmaApplyAtomIds' @-}
{-@ lemmaApplyAtomIds' :: Ord id
  => {ct:CausalTree id a | idUniqueCausalTree ct}
  -> {id:id | S.member id (weaveIds (causalTreeWeave ct))}
  -> {atom:CausalTreeAtom id a | not (S.member (causalTreeAtomId atom) (causalTreeIds ct))}
  -> {(causalTreePendingSize (applyAtom ct id atom) <= causalTreePendingSize ct) && (S.union (causalTreeIds ct) (S.singleton (causalTreeAtomId atom)) == causalTreeIds (applyAtom ct id atom)) && (S.isSubsetOf (weaveIds (causalTreeWeave ct)) (weaveIds (causalTreeWeave (applyAtom ct id atom)))) && (idUniqueCausalTree (applyAtom ct id atom))}
@-}
lemmaApplyAtomIds' :: Ord id => CausalTree id a -> id -> CausalTreeAtom id a -> ()
lemmaApplyAtomIds' ct parentId atom = lemmaApplyAtomIds ct parentId atom &&& applyAtomRespectsUniq ct parentId atom


{-@ ple lemmaApplyAtomIds  @-}
{-@ lemmaApplyAtomIds :: Ord id
  => ct:CausalTree id a
  -> id:id
  -> atom:CausalTreeAtom id a
  -> {S.union (causalTreeIds ct) (S.singleton (causalTreeAtomId atom)) == causalTreeIds (applyAtom ct id atom) && (S.isSubsetOf (weaveIds (causalTreeWeave ct)) (weaveIds (causalTreeWeave (applyAtom ct id atom)))) && (S.member id (weaveIds (causalTreeWeave ct)) => (causalTreePendingSize ct >= causalTreePendingSize (applyAtom ct id atom))) }
  / [causalTreePendingSize ct, 0, 0] @-}
lemmaApplyAtomIds :: Ord id => CausalTree id a -> id -> CausalTreeAtom id a -> ()
lemmaApplyAtomIds ct@(CausalTree weave pending) parentId atom
  | Nothing <- insertInWeave weave parentId atom
  = let pops = case Map.lookup parentId pending of
                 Nothing -> [atom]
                 Just xs -> insertList atom xs
        popsOld = case Map.lookup parentId pending of
                 Nothing -> []
                 Just xs -> xs  in
        -- pending' = case Map.lookup parentId pending of
        --              Nothing -> pending
        --              Just xs -> Map.delete parentId pending
        --            === Map.delete parentId pending in
      
    insertListRespectsUniq atom popsOld &&&
    
    -- (constConstNothing parentId popsOld *** QED)  &&&
    
    (   insertPending parentId atom pending
    === Map.insert parentId pops pending
    *** QED) &&&

    (   S.union (causalTreeIds ct) (S.singleton (causalTreeAtomId atom))
    === S.union (weaveIds weave) (S.union (pendingIds pending) (S.singleton (causalTreeAtomId atom)))
    *** QED) &&&

    (   applyAtom ct parentId atom
    === CausalTree weave (insertPending parentId atom pending)
    *** QED) &&&

    (applyAtom ct parentId atom *** QED) &&&

    insertPendingRespectsUniq parentId atom pending &&&
    
    (   case Map.lookup parentId pending of
          Nothing ->  -- lemmaInsertSubsetNothing pending parentId pops &&&
                     (   pendingListIds pops
                     === pendingListIds [atom]
                     === S.singleton (causalTreeAtomId atom)
                     *** QED)

          Just xs -> ((   pendingListIds pops
                     === pendingListIds (atom:popsOld)
                     === S.union (S.singleton (causalTreeAtomId atom)) (pendingListIds popsOld)
                     *** QED) &&&
                       lemmaLookupSubsetOf pending parentId popsOld))
  | Just weave' <- insertInWeave weave parentId atom
  , Nothing <- Map.lookup (causalTreeAtomId atom) pending
  = ( Map.updateLookupWithKey constConstNothing (causalTreeAtomId atom) pending
  ==. (Nothing, pending)
  *** QED) &&&
  (   applyAtom (CausalTree weave pending) parentId atom
  ==. CausalTree weave' pending
  *** QED
  )
  | Just weave' <- insertInWeave weave parentId atom
  , Just [] <- Map.lookup (causalTreeAtomId atom) pending
  = ( Map.updateLookupWithKey constConstNothing (causalTreeAtomId atom) pending
      ? constConstNothing (causalTreeAtomId atom) []
  ==. (Just [], Map.delete (causalTreeAtomId atom) pending)
  *** QED) &&&

  (   List.foldl' (applyAtomHelper (causalTreeAtomId atom)) (CausalTree weave' (Map.delete (causalTreeAtomId atom) pending)) []
  ==. CausalTree weave' (Map.delete (causalTreeAtomId atom) pending)
  *** QED) &&&
  
  (   applyAtom (CausalTree weave pending) parentId atom
  ==. CausalTree weave' (Map.delete (causalTreeAtomId atom) pending)
  *** QED
  ) &&&
  lemmaDeleteSubsetJust pending (causalTreeAtomId atom) [] S.empty &&&
  lemmaDeleteShrink pending (causalTreeAtomId atom) []
  | Just weave' <- insertInWeave weave parentId atom
  , Just pops@(_:_) <- Map.lookup (causalTreeAtomId atom) pending
  = let aid = causalTreeAtomId atom in
  ( Map.updateLookupWithKey constConstNothing (causalTreeAtomId atom) pending
      ? constConstNothing aid pops
  ==. (Just pops, Map.delete aid pending)
  *** QED) &&&
  lemmaDeleteShrink pending aid pops &&&
  lemmaDeleteSubsetJust pending aid pops (pendingListIds pops) &&&
  lemmaLookupSubsetOf pending aid pops &&&
  (causalTreePendingSize (CausalTree weave' (Map.delete aid pending)) < causalTreePendingSize ct
  *** QED) &&&
  lemmaFoldlIds (CausalTree weave' (Map.delete aid pending)) aid pops




{-@ ple lemmaDeleteShrink @-}
{-@ lemmaDeleteShrink :: Ord id
  => x:Map.Map id [a]
  -> k:id
  -> {pops:[a] | Just pops == Map.lookup k x }
  -> {if (List.length pops /= 0) then (pendingSize (Map.delete k x) < pendingSize x) else (pendingSize (Map.delete k x) == pendingSize x) }  @-}
lemmaDeleteShrink :: Ord id
  => Map.Map id [a]
  -> id
  -> [a]
  -> ()
lemmaDeleteShrink Map.Tip k pops = Just pops *** QED
lemmaDeleteShrink (Map.Map k' v t) k pops
  | k == k'
  = ( Map.delete k (Map.Map k' v t)
  ==. t
  *** QED) &&&
  ( Just v ==. Just pops *** QED) &&& 
  ( pendingSize (Map.Map k' v t)
  ==. List.length v + pendingSize t
  ==. List.length pops + pendingSize t
  *** QED) &&&
  ( pendingSize (Map.delete k (Map.Map k' v t))
  ==. pendingSize t
  *** QED) &&&
  ()
  | k > k'
  = lemmaDeleteShrink t k pops
  | otherwise
  = assert (k < k')
  ? Just pops
  ? Map.Map k' v t
  ? Map.delete k (Map.Map k' v t)
  ? Map.lookup k t
  ? Map.keyLeqLemma k k' v t


-- foldl 
