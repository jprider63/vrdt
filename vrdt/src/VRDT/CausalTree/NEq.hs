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
  x@(CausalTree ctw@(CausalTreeWeave ctAtom weaveChildren) pending)
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
  -- | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  -- , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  -- , Just pops2 <- Map.lookup id2 pending
  -- , pid1 /= id2 && pid2 /= id1
  -- = (   Map.updateLookupWithKey constConstNothing id2 pending
  --   ? constConstNothing id2 pops2
  -- ==. (Just pops2, Map.delete id2 pending)
  -- *** QED) &&&
  -- ( apply x op2
  -- ==. applyAtom x pid2 (CausalTreeAtom id2 l2)
  -- ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2
  -- *** QED) &&&
  -- lemmaLookupDelete2 pending id1 id2 &&&
  -- lemmaLookupDelete2 pending id2 id1 &&&
  -- lemmaLookupDelete2 pending pid1 id2 &&&
  -- (      List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
  --    ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)) []
  --    ==. applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) (CausalTreeAtom id1 l1)
  --    ==.  apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) op1
  --    *** QED) &&&
  -- ( apply x op1
  -- ==. CausalTree
  --      (CausalTreeWeave ctAtom weaveChildren)
  --      (insertPending pid1 (CausalTreeAtom id1 l1) pending)
  -- *** QED) &&&
  -- lemmaLookupInsert2 pending id2 pid1 pid1pending' &&&
  -- lemmaInsertDelete pid1 pid1pending' id2 pending &&&
  -- (   apply (apply x op1) op2
  -- ==. apply (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)) op2
  --     -- prove this new lemma
  --     -- can be easily proved using the lemmas
  --     -- ? lemmaInsertDeletePending
  -- ==. applyAtom (CausalTree (CausalTreeWeave ctAtom weaveChildren) (insertPending pid1 (CausalTreeAtom id1 l1) pending)) pid2 (CausalTreeAtom id2 l2)
  --     ? (  Map.updateLookupWithKey constConstNothing id2
  --          (    insertPending pid1 (CausalTreeAtom id1 l1) pending
  --           ==. Map.insert pid1 pid1pending' pending)
  --      ==. (Just pops2, Map.delete id2 (insertPending pid1 (CausalTreeAtom id1 l1) pending))
  --      ==. (Just pops2, insertPending pid1 (CausalTreeAtom id1 l1) (Map.delete id2 pending)
  --                   ==. Map.insert pid1 pid1pending' (Map.delete id2 pending))
  --      *** QED)
  -- ==.  List.foldl' (applyAtomHelper id2) (CausalTree wop2 (insertPending pid1 (CausalTreeAtom id1 l1) (Map.delete pid2 pending))) pops2
  --     ? lemmaInsertInWeaveJustNEq (CausalTreeWeave ctAtom weaveChildren) pid1 pid2 wop2 (CausalTreeAtom id1 l1) (CausalTreeAtom id2 l2)
  --     -- another delete/insert/lookup lemma

  -- ==.  List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) [CausalTreeAtom id1 l1]
  -- ==.  List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper pid1) (CausalTree wop2 (Map.delete id2 pending)) [CausalTreeAtom id1 l1]) pops2
  --     ? lemmaApplyAtomFoldNeq (CausalTree wop2 (Map.delete id2 pending)) id2 pid1 pops2 [CausalTreeAtom id1 l1]
  -- ==.  apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete id2 pending)) pops2) op1
  -- ==. apply (apply x op2) op1
  -- *** QED)
  -- | Just wop1 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  -- , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  -- -- , Just pops2 <- Map.lookup id2 pending
  -- -- TODO: this precondition is not needed; it can be derived
  -- = lemmaInsertInWeaveJustEq2
  --       (CausalTreeWeave ctAtom weaveChildren)
  --       pid2
  --       pid1
  --       wop2
  --       wop1
  --       (CausalTreeAtom id2 l2)
  --       (CausalTreeAtom id1 l1) &&&
  -- let Just wop2op1 = insertInWeave wop2 pid1 (CausalTreeAtom id1 l1)
  --     Just wop1op2 = insertInWeave wop1 pid2 (CausalTreeAtom id2 l2) in
  -- -- id1 
  --   ( List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) []
  -- ==. CausalTree wop1 id1pending
  -- *** QED) &&&
  
  --   (constConstNothing id1 pops1 *** QED) &&&
    
  --   ( Map.updateLookupWithKey constConstNothing id1 pending
  -- ==. (id1pendingM, id1pending)
  -- *** QED) &&&
  
  --   ( apply x op1
  -- ==. List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1
  -- *** QED) &&&

  -- -- id2
  --   ( List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) []
  -- ==. CausalTree wop2 id2pending
  -- *** QED) &&&
  
  --   (constConstNothing id2 pops2 *** QED) &&&
    
  --   ( Map.updateLookupWithKey constConstNothing id2 pending
  -- ==. (id2pendingM, id2pending)
  -- *** QED) &&&
  
  --   ( Map.updateLookupWithKey constConstNothing id1 id2pending
  -- ==. (id1pendingM, id1id2pending)
  -- *** QED) &&&

  --   ( apply x op2
  -- ==. List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2
  -- *** QED) &&&


  --   ( Map.updateLookupWithKey constConstNothing id2 id1pending
  -- ==. (id2pendingM, id1id2pending)
  -- *** QED) &&&

  -- -- id2 then id1
  -- (      List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) [CausalTreeAtom id1 l1]
  --    ==. List.foldl' (applyAtomHelper pid1) (applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) (CausalTreeAtom id1 l1)) []
  --    ==. applyAtomHelper pid1 (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) (CausalTreeAtom id1 l1)
  --    ==.  apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) op1
  --    *** QED) &&&

  -- (   apply (apply x op2) op1
  -- ==. apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) op1
  -- ==. List.foldl' (applyAtomHelper pid1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) [CausalTreeAtom id1 l1]
  --   ? lemmaApplyAtomFoldNeq (CausalTree wop2 id2pending) pid1 id2 [CausalTreeAtom id1 l1] pops2
  -- ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper pid1) (CausalTree wop2 id2pending) [CausalTreeAtom id1 l1]) pops2
  -- ==. List.foldl' (applyAtomHelper id2) (applyAtom (CausalTree wop2 id2pending) pid1 (CausalTreeAtom id1 l1)) pops2
  -- ==. List.foldl' (applyAtomHelper id2) (List.foldl' (applyAtomHelper id1) (CausalTree wop2op1 id1id2pending) pops1) pops2
  -- *** QED ) &&&

  -- -- id1 then id2
  -- (      List.foldl' (applyAtomHelper pid2) (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) [CausalTreeAtom id2 l2]
  --    ==. List.foldl' (applyAtomHelper pid2) (applyAtomHelper pid2 (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) (CausalTreeAtom id2 l2)) []
  --    ==. applyAtomHelper pid2 (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) (CausalTreeAtom id2 l2)
  --    ==.  apply (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) op2
  --    *** QED) &&&

  -- (   apply (apply x op1) op2
  -- ==. apply (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) op2
  -- ==. List.foldl' (applyAtomHelper pid2) (List.foldl' (applyAtomHelper id1) (CausalTree wop1 id1pending) pops1) [CausalTreeAtom id2 l2]
  --   ? lemmaApplyAtomFoldNeq (CausalTree wop1 id1pending) pid2 id1 [CausalTreeAtom id2 l2] pops1
  -- ==. List.foldl' (applyAtomHelper id1) (List.foldl' (applyAtomHelper pid2) (CausalTree wop1 id1pending) [CausalTreeAtom id2 l2]) pops1
  -- ==. List.foldl' (applyAtomHelper id1) (applyAtom (CausalTree wop1 id1pending) pid2 (CausalTreeAtom id2 l2)) pops1
  -- ==. List.foldl' (applyAtomHelper id1) (List.foldl' (applyAtomHelper id2) (CausalTree wop1op2 id2id1pending) pops2) pops1
  -- ==. List.foldl' (applyAtomHelper id1) (List.foldl' (applyAtomHelper id2) (CausalTree wop2op1 id1id2pending) pops2) pops1
  -- *** QED )  &&&
  -- lemmaApplyAtomFoldNeq (CausalTree wop2op1 id1id2pending) id2 id1  pops2 pops1  
  | Nothing  <- insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid1 (CausalTreeAtom id1 l1)
  , Just wop2 <-insertInWeave (CausalTreeWeave ctAtom weaveChildren) pid2 (CausalTreeAtom id2 l2)
  , id2 == pid1
  = -- lemmaInsertInWeaveJustNEqRel ctw pid1 pid2 wop2 (CausalTreeAtom id1 l1) (CausalTreeAtom id2 l2) &&&
    assume (id1 /= pid2) &&&
    -- let Just wop2op1 = insertInWeave wop2 pid2 (CausalTreeAtom id2 l2) in
    -- assert (pid2 /= id1) &&&

  
    (constConstNothing id1 pops1 *** QED) &&&


  -- id2
    ( List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) []
  === CausalTree wop2 id2pending
  *** QED) &&&
  
    (constConstNothing id2 pops2 *** QED) &&&
    
    ( Map.updateLookupWithKey constConstNothing id2 pending
  === (id2pendingM, id2pending)
  *** QED) &&&
  

    ( apply x op2
  === List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2
  *** QED) &&&


    ( Map.updateLookupWithKey constConstNothing id2 id1pending
  === (id2pendingM, id1id2pending)
  *** QED) &&&

  -- id1
    ( apply x op1
  === CausalTree ctw (insertPending id2 (CausalTreeAtom id1 l1) pending)
  === CausalTree ctw (Map.insert pid1 pid1pending' pending)
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
  === apply (List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending) pops2) op1
  -- lemma about foldl'
  ==! List.foldl' (applyAtomHelper id2) (CausalTree wop2 id2pending)
        (List.concat pops2 [CausalTreeAtom id1 l1])
      -- lemma: insertList x ys = lts ++ [x] ++ gts where lts ++ gts == ys
  *** QED) &&&
    (List.foldl' (applyAtomHelper id2) (applyAtomHelper id2  (CausalTree wop2 (Map.delete pid1 pending)) (CausalTreeAtom id1 l1)) [] *** QED) &&&

  (case Map.lookup id2 pending of
    Nothing -> ()
    Just _ ->  let (lts, gts) = insertListDestruct (CausalTreeAtom id1 l1) pops2 in
               apply (apply x op1) op2
           === List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) pid1pending'
           === List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) (insertList (CausalTreeAtom id1 l1) pops2)
           === List.foldl' (applyAtomHelper id2) (CausalTree wop2 (Map.delete pid1 pending)) (List.concat lts (CausalTreeAtom id1 l1:gts))
           === List.foldl' (applyAtomHelper id2)
                 (CausalTree wop2 (Map.delete pid1 pending))
                 (List.concat lts (List.concat [CausalTreeAtom id1 l1] gts))
           ==! List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (CausalTree wop2 (Map.delete pid1 pending)) lts)
                 (List.concat [CausalTreeAtom id1 l1] gts)
           ==! List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (List.foldl' (applyAtomHelper id2)
                     (CausalTree wop2 (Map.delete pid1 pending)) lts) [CausalTreeAtom id1 l1])
                 gts
              -- ? neq lemma
              ? lemmaApplyAtomFoldNeq
           ==! List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (List.foldl' (applyAtomHelper id2)
                     (CausalTree wop2 (Map.delete pid1 pending)) [CausalTreeAtom id1 l1]) lts)
                 gts
              -- ? fold lemma again, apply twice
           ==! List.foldl' (applyAtomHelper id2)
                 (List.foldl' (applyAtomHelper id2)
                   (List.foldl' (applyAtomHelper id2)
                     (CausalTree wop2 (Map.delete pid1 pending)) [CausalTreeAtom id1 l1]) lts)
                 gts
           ==! List.foldl' (applyAtomHelper id2)
                 (CausalTree wop2 (Map.delete pid1 pending))
                 (List.concat lts (List.concat gts [CausalTreeAtom id1 l1]))
              -- concat assoc
           ==! List.foldl' (applyAtomHelper id2)
                 (CausalTree wop2 (Map.delete pid1 pending))
                 (List.concat pops2 [CausalTreeAtom id1 l1])
           === apply (apply x op2) op1
           *** QED
   -- lemma: foldl' and ++
  ) &&&
  ()
  
  | otherwise
  = undefined
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
