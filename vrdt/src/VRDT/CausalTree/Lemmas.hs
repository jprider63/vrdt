{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}
module VRDT.CausalTree.Lemmas where
import           Liquid.Data.Maybe
import           Liquid.Data.Map                ( Map )
import qualified Liquid.Data.Map               as Map
import           Liquid.Data.Map.Props

import           VRDT.CausalTree.Internal
import           Prelude                 hiding ( Maybe(..)
                                                , empty
                                                )
import qualified Liquid.Data.List              as List


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
  -> {insertInWeave wop1 pid2 op2 == insertInWeave wop2 pid1 op1 && isJust (insertInWeave wop1 pid2 op2)} @-}
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
  -> {op1:CausalTreeAtom id a | insertInWeave w pid1 op1 == Nothing}
  -> {op2:CausalTreeAtom id a | (insertInWeave w pid2 op2 == Just wop2) && (causalTreeAtomId op1 /= causalTreeAtomId op2)}
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
