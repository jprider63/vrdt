{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
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

{-@ lemmaInsertAtomTwice :: cts:[CausalTreeWeave id a] -> a1:CausalTreeAtom id a -> {a2:CausalTreeAtom id a | causalTreeAtomId a2 /= causalTreeAtomId a1} ->
   {insertAtom (insertAtom cts a1) a2 == insertAtom (insertAtom cts a2) a1} @-}
lemmaInsertAtomTwice
  :: [CausalTreeWeave id a] -> CausalTreeAtom id a -> CausalTreeAtom id a -> ()
lemmaInsertAtomTwice _ _ _ = undefined


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
lemmaInsertInWeaveNothingEq _ _ _ _ = undefined


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

{-@ lemmaInsertInWeaveJustEq :: Ord id => w:CausalTreeWeave id a -> pid:id -> wop1 : CausalTreeWeave id a ->
  wop2 : CausalTreeWeave id a -> 
  {op1:CausalTreeAtom id a | insertInWeave w pid op1 == Just wop1} -> {op2:CausalTreeAtom id a | (insertInWeave w pid op2 == Just wop2) && (causalTreeAtomId op1 /= causalTreeAtomId op2)} ->
  {insertInWeave wop1 pid op2 == insertInWeave wop2 pid op1 && isJust (insertInWeave wop1 pid op2)} @-}
lemmaInsertInWeaveJustEq
  :: Ord id
  => CausalTreeWeave id a
  -> id
  -> CausalTreeWeave id a
  -> CausalTreeWeave id a
  -> CausalTreeAtom id a
  -> CausalTreeAtom id a
  -> ()
lemmaInsertInWeaveJustEq _ _ _ _ _ _ = undefined


{-@ lemmaInsertInWeaveJustEq2 :: Ord id
  => w:CausalTreeWeave id a
  -> pid1:id
  -> pid2:id
  -> wop1 : CausalTreeWeave id a
  -> wop2 : CausalTreeWeave id a
  -> {op1:CausalTreeAtom id a | insertInWeave w pid1 op1 == Just wop1}
  -> {op2:CausalTreeAtom id a | (insertInWeave w pid2 op2 == Just wop2) && (causalTreeAtomId op1 /= causalTreeAtomId op2)}
  -> {insertInWeave wop1 pid2 op2 == insertInWeave wop2 pid1 op1 && isJust (insertInWeave wop1 pid2 op2) && (pid2 /= causalTreeAtomId op1) && (pid1 /= causalTreeAtomId op2)} @-}
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
lemmaInsertInWeaveJustEq2 _ _ _ _ _ _ _ = undefined


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
lemmaInsertInWeaveJustNEq _ _ _ _ _ = undefined

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
  -> {isJust (insertInWeave wop2 pid1 op1) && (pid2 /= causalTreeAtomId op1)}
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
lemmaInsertInWeaveJustNEqRel _ _ _ _ _ = undefined




-- i think i messed up this one. lemmaFoldIds is supposed to be trivial.
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
  -- | Just weave' <- insertInWeave weave parentId atom
  -- , Nothing <- Map.lookup (causalTreeAtomId atom) pending
  -- = ( Map.updateLookupWithKey constConstNothing (causalTreeAtomId atom) pending
  -- ==. (Nothing, pending)
  -- *** QED) &&&
  -- (   applyAtom (CausalTree weave pending) parentId atom
  -- ==. CausalTree weave' pending
  -- *** QED
  -- )
  -- | Just weave' <- insertInWeave weave parentId atom
  -- , Just [] <- Map.lookup (causalTreeAtomId atom) pending
  -- = ( Map.updateLookupWithKey constConstNothing (causalTreeAtomId atom) pending
  --     ? constConstNothing (causalTreeAtomId atom) []
  -- ==. (Just [], Map.delete (causalTreeAtomId atom) pending)
  -- *** QED) &&&

  -- (   List.foldl' (applyAtomHelper (causalTreeAtomId atom)) (CausalTree weave' (Map.delete (causalTreeAtomId atom) pending)) []
  -- ==. CausalTree weave' (Map.delete (causalTreeAtomId atom) pending)
  -- *** QED) &&&
  
  -- (   applyAtom (CausalTree weave pending) parentId atom
  -- ==. CausalTree weave' (Map.delete (causalTreeAtomId atom) pending)
  -- *** QED
  -- ) &&&
  -- lemmaDeleteSubsetJust pending (causalTreeAtomId atom) [] S.empty &&&
  -- lemmaDeleteShrink pending (causalTreeAtomId atom) []
  -- | Just weave' <- insertInWeave weave parentId atom
  -- , Just pops@(_:_) <- Map.lookup (causalTreeAtomId atom) pending
  -- = let aid = causalTreeAtomId atom in
  -- ( Map.updateLookupWithKey constConstNothing (causalTreeAtomId atom) pending
  --     ? constConstNothing aid pops
  -- ==. (Just pops, Map.delete aid pending)
  -- *** QED) &&&
  -- lemmaDeleteShrink pending aid pops &&&
  -- lemmaDeleteSubsetJust pending aid pops (pendingListIds pops) &&&
  -- lemmaLookupSubsetOf pending aid pops &&&
  -- (causalTreePendingSize (CausalTree weave' (Map.delete aid pending)) < causalTreePendingSize ct
  -- *** QED) &&&
  -- lemmaFoldlIds (CausalTree weave' (Map.delete aid pending)) aid pops
  | otherwise = undefined




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
