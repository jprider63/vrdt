{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
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

{-@ lemmaInsertAtomTwice :: cts:[CausalTreeWeave id a] -> a1:CausalTreeAtom id a -> {a2:CausalTreeAtom id a | causalTreeAtomId a2 /= causalTreeAtomId a1} ->
   {insertAtom (insertAtom cts a1) a2 == insertAtom (insertAtom cts a2) a1} @-}
lemmaInsertAtomTwice
  :: [CausalTreeWeave id a] -> CausalTreeAtom id a -> CausalTreeAtom id a -> ()
lemmaInsertAtomTwice _ _ _ = undefined


-- {-@ lemmaInsertInWeaveNothingNEq :: Ord id => w:CausalTreeWeave id a -> pid1:id -> {pid2:id | pid1 /= pid2} ->
--   {op1:CausalTreeAtom id a | insertInWeave w pid op1 == Nothing} -> op2:CausalTreeAtom id a ->
--   {insertInWeave w pid op2 == Nothing} @-}
-- lemmaInsertInWeaveNothingNEq
--   :: Ord id
--   => CausalTreeWeave id a
--   -> id
--   -> CausalTreeAtom id a
--   -> CausalTreeAtom id a
--   -> ()
-- lemmaInsertInWeaveNothingNEq _ _ _ _ = undefined



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

{-@ lemmaFoldlIds :: Ord id
  => ct:CausalTree id a
  -> id:id
  -> atoms:[CausalTreeAtom id a]
  -> {causalTreeIds (List.foldl' (applyAtomHelper id) ct atoms) == S.union (causalTreeIds ct) (pendingListIds atoms)}
  / [causalTreePendingSize ct, 1, List.length atoms]  @-}
lemmaFoldlIds :: Ord id => CausalTree id a -> id -> [CausalTreeAtom id a] -> ()
lemmaFoldlIds ct pid [] = ()
lemmaFoldlIds ct pid (a:as) =
  (   applyAtomHelper pid ct a
  === applyAtom ct pid a
  *** QED) &&&
  assume (causalTreePendingSize (applyAtomHelper pid ct a) == causalTreePendingSize ct) &&&
  lemmaApplyAtomIds ct pid a &&&
  lemmaFoldlIds (applyAtomHelper pid ct a) pid as


{-@ lemmaInsertListId :: Ord id
  => x:CausalTreeAtom id a
  -> xs:[CausalTreeAtom id a]
  -> {pendingListIds (insertList x xs) == S.union (S.singleton (causalTreeAtomId x)) (pendingListIds xs)} @-}
lemmaInsertListId :: Ord id
  => CausalTreeAtom id a
  -> [CausalTreeAtom id a]
  -> ()  
lemmaInsertListId x [] = ()
lemmaInsertListId x (y:ys)
  | x <= y = ()
  | otherwise = lemmaInsertListId x ys

{-@ lemmaInsertSubsetNothing :: Ord id
  => pending:Map.Map id [CausalTreeAtom id a]
  -> {k:id | isNothing (Map.lookup k pending)}
  -> atoms:[CausalTreeAtom id a]
  -> {pendingIds (Map.insert k atoms pending) == S.union (pendingListIds atoms) (pendingIds pending)} @-}
lemmaInsertSubsetNothing :: Ord id
  => Map.Map id [CausalTreeAtom id a]
  -> id
  -> [CausalTreeAtom id a]
  -> ()
lemmaInsertSubsetNothing Map.Tip _ _ = ()
lemmaInsertSubsetNothing _ _ _ = ()

{-@ lemmaInsertSubsetJust :: Ord id
  => pending:Map.Map id [CausalTreeAtom id a]
  -> k:id
  -> {atoms:[CausalTreeAtom id a] | Map.lookup k pending == Just atoms}
  -> {atomsNew:[CausalTreeAtom id a] | S.isSubsetOf (pendingListIds atoms) (pendingListIds atomsNew)}
  -> {pendingIds (Map.insert k atomsNew pending) == S.union (pendingListIds atomsNew) (pendingIds pending)}
@-}
lemmaInsertSubsetJust :: Ord id
  => Map.Map id [CausalTreeAtom id a]
  -> id
  -> [CausalTreeAtom id a]
  -> [CausalTreeAtom id a]
  -> ()
lemmaInsertSubsetJust Map.Tip _ _ _ = ()
lemmaInsertSubsetJust _ _ _ _ = ()



{-@ lemmaDeleteSubsetJust :: Ord id
  => pending:Map.Map id [CausalTreeAtom id a]
  -> k:id
  -> {atoms:[CausalTreeAtom id a] | Map.lookup k pending == Just atoms}
  -> {ids:S.Set id | S.isSubsetOf (pendingListIds atoms) ids}
  -> {S.union ids (pendingIds (Map.delete k pending)) == S.union ids (pendingIds pending)}
@-}
lemmaDeleteSubsetJust :: Ord id
  => Map.Map id [CausalTreeAtom id a]
  -> id
  -> [CausalTreeAtom id a]
  -> S.Set id
  -> ()
lemmaDeleteSubsetJust Map.Tip _ _ _ = ()
lemmaDeleteSubsetJust _ _ _ _ = ()


{-@ lemmaLookupSubsetOf :: Ord id
  => pending:Map.Map id [CausalTreeAtom id a]
  -> k:id
  -> {atoms:[CausalTreeAtom id a] | Map.lookup k pending == Just atoms}
  -> {S.isSubsetOf (pendingListIds atoms) (pendingIds pending)} @-}
lemmaLookupSubsetOf :: Ord id
  => Map.Map id [CausalTreeAtom id a]
  -> id
  -> [CausalTreeAtom id a]
  -> ()
lemmaLookupSubsetOf _ _ _ = ()

{-@ lemmaApplyAtomIds :: Ord id
  => ct:CausalTree id a
  -> id:id
  -> atom:CausalTreeAtom id a
  -> {S.union (causalTreeIds ct) (S.singleton (causalTreeAtomId atom)) == causalTreeIds (applyAtom ct id atom)}
  / [causalTreePendingSize ct, 0, 0] @-}
lemmaApplyAtomIds :: Ord id => CausalTree id a -> id -> CausalTreeAtom id a -> ()
lemmaApplyAtomIds ct@(CausalTree weave pending) parentId atom
  | Nothing <- insertInWeave weave parentId atom
  = undefined -- let pops = case Map.lookup parentId pending of
    --              Nothing -> [atom]
    --              Just xs -> insertList atom xs
    --     popsOld = case Map.lookup parentId pending of
    --              Nothing -> []
    --              Just xs -> xs  in
    --     -- pending' = case Map.lookup parentId pending of
    --     --              Nothing -> pending
    --     --              Just xs -> Map.delete parentId pending
    --     --            === Map.delete parentId pending in
      
    -- lemmaInsertListId atom popsOld &&&
    
    -- -- (constConstNothing parentId popsOld *** QED)  &&&
    
    -- (   insertPending parentId atom pending
    -- ==. Map.insert parentId pops pending
    -- *** QED) &&&

    -- (   S.union (causalTreeIds ct) (S.singleton (causalTreeAtomId atom))
    -- ==. S.union (weaveIds weave) (S.union (pendingIds pending) (S.singleton (causalTreeAtomId atom)))
    -- *** QED) &&&

    -- (   applyAtom ct parentId atom
    -- ==. CausalTree weave (insertPending parentId atom pending)
    -- *** QED) &&&

    -- (applyAtom ct parentId atom *** QED) &&&
    
    -- (   case Map.lookup parentId pending of
    --       Nothing ->  lemmaInsertSubsetNothing pending parentId pops &&&
    --                  (   pendingListIds pops
    --                  ==. pendingListIds [atom]
    --                  ==. S.singleton (causalTreeAtomId atom)
    --                  *** QED)

    --       Just xs -> ((   pendingListIds pops
    --                  ==. pendingListIds (atom:popsOld)
    --                  ==. S.union (S.singleton (causalTreeAtomId atom)) (pendingListIds popsOld)
    --                  *** QED) &&&
    --                    lemmaInsertSubsetJust pending parentId popsOld pops) &&&
    --                    lemmaLookupSubsetOf pending parentId popsOld)
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
  -- lemmaDeleteSubsetJust pending (causalTreeAtomId atom) [] S.empty
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

  | otherwise
  = undefined
  -- = let pops = case Map.lookup parentId pending of
  --                Nothing -> []
  --                Just xs -> xs
  --       pending' = case Map.lookup parentId pending of
  --                    Nothing -> pending
  --                    Just xs -> Map.delete parentId pending
  --                  === Map.delete parentId pending
  --       aid = causalTreeAtomId atom in
  --   case pops of {
  --           -- Just, [] case: discharge with the lemma about lookup just
  --           -- Nothing case: trivial
  --     [] -> (   List.foldl' (applyAtomHelper aid) ct pops
  --           === ct
  --           *** QED)
      
  --   }




{-@ lemmaDeleteShrink :: Ord id
  => x:Map.Map id [a]
  -> k:id
  -> {pops:[a] | Just pops == Map.lookup k x && List.length pops /= 0}
  -> {pendingSize (Map.delete k x) < pendingSize x }  @-}
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
