{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module VRDT.TwoPMap.LemmaIA where

import VRDT.TwoPMap.Internal
import VRDT.TwoPMap.LemmaIANeq
import VRDT.TwoPMap.LemmaIAC
import VRDT.Class
import VRDT.Class.Proof
import Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Liquid.Data.List
import qualified Liquid.Data.List as List
import           Data.Set (Set)
import qualified Data.Set as Set
import           Liquid.Data.Map.Props
import           Liquid.ProofCombinators
import VRDT.Internal
import           Prelude hiding (Maybe(..), isJust, maybe, foldr, flip, const)
import           Liquid.Data.Maybe





{-@ lawCommutativityIA :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> k2:k -> {vop2:Operation v | (compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))} -> {  ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2))} @-}
lawCommutativityIA :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> k -> Operation v -> ()
lawCommutativityIA x@(TwoPMap m p t) k v k' vop'
  | not ((compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2))) = ()
  | k == k' = lawCommutativityIAEq x k v vop' &&& lawCommutativityIAEq' x k v vop'
  | otherwise = lawCommutativityIANeq x k v k' vop'

  where k1 = k
        k2 = k'
        vop2 = vop'
        v1 = v


{-@ ple lawCommutativityIAEq @-}
{-@ lawCommutativityIAEq :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k:k -> v1:v -> vop2:Operation v -> { (compatibleTwoPMap (TwoPMapInsert k v1) (TwoPMapApply k vop2) && compatibleStateTwoPMap x (TwoPMapInsert k v1) && compatibleStateTwoPMap x (TwoPMapApply k vop2)) => (applyTwoPMap (applyTwoPMap x (TwoPMapInsert k v1)) (TwoPMapApply k vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k vop2)) (TwoPMapInsert k v1))} @-}
lawCommutativityIAEq :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> Operation v -> ()
lawCommutativityIAEq x@(TwoPMap m p t) k v1 vop2
  | not (compatibleTwoPMap (TwoPMapInsert k v1) (TwoPMapApply k vop2)) = ()
  | not (compatibleStateTwoPMap x (TwoPMapInsert k v1)) = ()
  | not (compatibleStateTwoPMap x (TwoPMapApply k vop2)) = ()

  | isJust (Map.lookup k m)
  = undefined -- () -- TODO OK

  | (Set.member k t) 
  = undefined -- () -- TODO OK

  | not (Set.member k t)
  , Nothing <- Map.lookup k p
  = undefined -- TODO
   -- -- OK. Takes 4.5 minues...
   -- ( Map.lookup k m === Nothing *** QED) 
   -- &&&( let v1 = maybe v (foldr (flip apply) v) Nothing
   --        -- Just vv = Map.lookup k (Map.insert k v1 m)
   --          -- Just vvv = Map.lookup k  (Map.insert k [vop'] p)
   --          l2 = case Map.lookup k p of
   --                 Nothing -> [vop']
   --                 Just ops -> insertList vop' ops  in
   --         (maybe v (foldr (flip apply) v) (Just [vop'])
   --      ==.  foldr (flip apply) v [vop']
   --      ==.  (flip apply) vop' (foldr (flip apply) v [])
   --      ==.  (flip apply) vop' v
   --      ==.  apply v vop'
   --      ***  QED  )
   --      -- -- &&& lemmaLookupInsert2 p k k' l2
   --      -- -- &&& lemmaLookupDelete2 p k' k
   --      -- -- &&& lemmaInsert k v1 k' v2 m
   --      -- -- &&& lemmaInsertDelete k' l2 k p
   --      &&& (l2 ==. [vop']  *** QED)
   --      &&& (Map.lookup k (Map.insert k [vop'] p) ==. Just [vop'] *** QED)
   --      &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
   --          ? lemmaLookupInsert m k v1
   --          ? lemmaLookupInsert p k l2
   --          ? (Map.lookup k m ==. Nothing *** QED)
   --          ? lemmaDeleteInsert k [vop'] p
   --          ? lemmaInsertTwice k (apply v1 vop') v1 m
   --      ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
   --      ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
   --      ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k vop')
   --      ==.  TwoPMap (Map.insert k (apply v1 vop') (Map.insert k v1 m)) p t
   --          ? ((Map.insert k (apply v1 vop') (Map.insert k v1 m)) ==. Map.insert k (apply v1 vop')  m *** QED)
   --      ==.  TwoPMap (Map.insert k (apply v1 vop') m) p t
   --            ? assert (not (Map.member k p))
   --          ? (Map.delete k p ==. p *** QED)
   --      ==.  TwoPMap (Map.insert k (apply v1 vop') m) (Map.delete k p) t
   --      -- ==.  TwoPMap (Map.insert k v1 m) p  t
   --      === TwoPMap (Map.insert k (apply v1 vop') m) -- here
   --            (Map.delete k p) t
   --      ==.  TwoPMap (Map.insert k (maybe v (foldr (flip apply) v) (Just [vop'])) m)
   --            (Map.delete k (Map.insert k [vop'] p)) t
   --      ===  applyTwoPMap (TwoPMap m (Map.insert k [vop'] p) t) op1 -- here
   --      ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
   --      *** QED
   --      ) -- &&&
   --      -- ( applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2 === applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1 *** QED)
   --    )
  | not (Set.member k t)
  , Just ops <- Map.lookup k p
  = 
    let v1' = foldr (flip apply) v1 ops in
    let v1'' = apply v1' vop2 in

    let ops2 = insertList vop2 ops in
    let v2' = foldr (flip apply) v1 ops2 in

    (   applyTwoPMap (applyTwoPMap x (TwoPMapInsert k v1)) (TwoPMapApply k vop2) 
    === applyTwoPMap (TwoPMap (Map.insert k v1' m) (Map.delete k p) t) (TwoPMapApply k vop2)  -- OK
        ?   lemmaLookupInsert m k v1'
        &&& (Map.lookup k (Map.insert k v1' m) === Just v1' *** QED)
        &&& assert (isJust (Map.lookup k (Map.insert k v1' m)))
    === TwoPMap (Map.insert k v1'' (Map.insert k v1' m)) (Map.delete k p) t -- OK
        ?   lemmaInsertTwice k v1'' v1' m
    === TwoPMap (Map.insert k v1'' m) (Map.delete k p) t -- OK
        ?   lemmaPermutation vop2 ops ops2
        &&& assert (isPermutation (vop2:ops) ops2) -- OK
        &&& assert (allCompatibleState v1 ops) -- OK
        &&& assert (compatibleState v1 vop2) -- OK
        &&& assert (allCompatibleState v1 (vop2:ops)) -- OK
        &&& assert (allCompatible ops) -- OK
        &&& assert (allCompatible (vop2:ops)) -- OK
        &&& strongConvergence v1 (vop2:ops) ops2
        &&& (applyAll v1 (vop2:ops) === applyAll v1 ops2 *** QED)
        &&& lemmaApplyAll v1 (vop2:ops) -- OK
        &&& lemma1 vop2 ops v1 -- OK
        &&& lemma2 ops vop2 -- OK
        &&& lemmaApplyAll v1 ops2 -- OK
        &&& (v1'' === v2' *** QED) -- OK
        &&& lemmaDeleteInsert k ops2 p
    === TwoPMap (Map.insert k v2' m) (Map.delete k (Map.insert k ops2 p)) t -- OK
        ?   lemmaLookupInsert p k ops2
    === applyTwoPMap (TwoPMap m (Map.insert k ops2 p) t) (TwoPMapInsert k v1) -- OK
    === applyTwoPMap (applyTwoPMap x (TwoPMapApply k vop2)) (TwoPMapInsert k v1) -- OK
    *** QED)

  where op1 = TwoPMapInsert k v1
        op2 = TwoPMapApply k vop2


        vop' = vop2
        v = v1

        -- l1 = case Map.lookup k p of
        --        Nothing -> [vop']
        --        Just ops -> insertList vop' ops

{-@ ple lemma2 @-}
{-@ lemma2 :: (Ord (Operation a), VRDT a) => ops:[Operation a] -> op:Operation a -> {allCompatible' op ops => allCompatible (insertList op ops)} @-}
lemma2 :: (Ord (Operation a), VRDT a) => [Operation a] -> Operation a -> ()
lemma2 [] _ = ()
lemma2 (op:ops) vop
  | vop <= op = ()
  | otherwise =
    lawCompatibilityCommutativity op vop
    &&& lemmaAllCompatibleInsert ops op vop

{-@ lemmaApplyAll :: (Eq (Operation a), VRDT a) => v1:a -> ops:[Operation a] -> {(allCompatibleState v1 ops && allCompatible ops) => applyAll v1 ops == Liquid.Data.List.foldr (flip apply) v1 ops} @-}
lemmaApplyAll :: (Eq (Operation a), VRDT a) => a -> [Operation a] -> ()
lemmaApplyAll v1 ops | not (allCompatible ops) = ()
lemmaApplyAll v1 ops | not (allCompatibleState v1 ops) = ()
lemmaApplyAll v1 ops = 
        foldr (flip apply) v1 ops 
          ? lemmaApplyAllFoldr ops v1
    ==. applyAll v1 (List.reverse ops)
          ?   lemmaPermutationReverse ops
          &&& assert (allCompatibleState v1 ops)
          &&& assert (allCompatible ops)
          &&& strongConvergence v1 ops (List.reverse ops)
    ==. applyAll v1 ops
    *** QED

{-@ ple lemmaApplyAll' @-}
{-@ lemmaApplyAll' :: VRDT a => ops:[Operation a] -> ops':[Operation a] -> v:a ->
  {applyAll v (List.concat ops ops') == applyAll (applyAll v ops) ops'} @-}
lemmaApplyAll' :: VRDT a => [Operation a] -> [Operation a] -> a -> ()
lemmaApplyAll' [] _ _ = ()
lemmaApplyAll' (op':ops) ops'  v = lemmaApplyAll' ops ops' (apply v op')

{-@ ple lemmaApplyAllFoldr @-}
{-@ lemmaApplyAllFoldr :: VRDT a =>ops:[Operation a] -> v1:a ->  {applyAll v1 (List.reverse ops) == Liquid.Data.List.foldr (flip apply) v1 ops} @-}
lemmaApplyAllFoldr :: VRDT a => [Operation a] -> a -> ()
lemmaApplyAllFoldr [] _ = ()
lemmaApplyAllFoldr (op:ops) v =
      applyAll v (List.reverse (op:ops))
      ? lemmaApplyAllFoldr ops v
      ? lemmaApplyAll' (List.reverse ops) [op] v
  ==. applyAll v (List.concat (List.reverse ops) [op])
  ==. apply (applyAll v (List.reverse ops)) op
  ==. apply (List.foldr (flip apply) v ops) op
  ==. flip apply op (List.foldr (flip apply) v ops) 
  ==. List.foldr (flip apply) v (op:ops)
  *** QED
  

{-@ ple lemmaInsertRemoveFirst @-}
{-@ lemmaInsertRemoveFirst :: Ord a => x:a -> xs:[a] -> {removeFirst x (insertList x xs) == Just xs} @-}
lemmaInsertRemoveFirst :: Ord a => a -> [a] -> ()
lemmaInsertRemoveFirst x [] = ()
lemmaInsertRemoveFirst x (y:ys)
  | x < y = ()
  | x == y = ()
  | x > y = lemmaInsertRemoveFirst x ys

{-@ ple lemmaPermutationId @-}
{-@ lemmaPermutationId :: (Eq a) => x:[a] -> {isPermutation x x} @-}
lemmaPermutationId :: Eq a => [a] -> ()
lemmaPermutationId [] = ()
lemmaPermutationId (x:xs) = lemmaPermutationId xs

{-@ ple lemmaPermutation @-}
{-@ lemmaPermutation :: Ord a => vop2:a -> ops:[a] -> {ops2:[a] | insertList vop2 ops = ops2} -> {isPermutation (cons vop2 ops) ops2} @-}
lemmaPermutation :: Ord a => a -> [a] -> [a] -> ()
lemmaPermutation _ [] [] = ()
lemmaPermutation _ [] _ = ()
lemmaPermutation vop2 ops@(h:ops') ops2 
  | vop2 <= h = 
        -- insertList vop2 (h:ops')
        isPermutation (vop2:ops) ops2
    ==. isPermutation (vop2:ops) (insertList vop2 (h:ops'))
    ==. isPermutation (vop2:ops) (vop2:h:ops')
        -- ? assert (ops =)
    ==. isPermutation (ops) (h:ops')
        ? lemmaPermutationId ops
    ==. isPermutation (ops) (ops)
    *** QED
  | otherwise =
        isPermutation (vop2:ops) ops2
    ==. isPermutation (vop2:ops) (insertList vop2 (h:ops'))
        ? lemmaInsertRemoveFirst vop2 ops'
    ==. isPermutation (vop2:ops) (h:insertList vop2 ops')
    ==. isPermutation ops (h: ops')
        ? lemmaPermutationId ops
    *** QED

{-@ ple lemmaElemConcat @-}
{-@ lemmaElemConcat :: Eq a => x:a -> xs:[a] -> ys:[a] ->
  {((List.elem' x (List.concat xs ys)) <=> not (not (List.elem' x xs) && not (List.elem' x ys)))} @-}
lemmaElemConcat :: Eq a => a -> [a] -> [a] -> ()
lemmaElemConcat x [] _ = ()
lemmaElemConcat x (y:ys) zs
  | x /= y
  = lemmaElemConcat x ys zs
  | otherwise
  = ()

{-@ ple lemmaReverseElem @-}
{-@ lemmaReverseElem :: Eq a => x:a -> xs:[a] -> {List.elem' x xs == List.elem' x (List.reverse xs)}@-}
lemmaReverseElem  :: Eq a => a -> [a] -> ()
lemmaReverseElem x [] = ()
lemmaReverseElem x (y:ys)
  | x /= y = lemmaReverseElem x ys
           ? lemmaElemConcat x (List.reverse ys) [y]
  | otherwise = lemmaElemConcat x (List.reverse ys) [y]

{-@ ple lemmaPermutationHeadTailNotElem @-}
{-@ lemmaPermutationHeadTailNotElem :: Eq a => h:a -> {ops:[a] | not (List.elem' h ops)} ->
  {isPermutation (cons h ops) (List.concat ops (cons h List.empty)) } @-}
lemmaPermutationHeadTailNotElem :: Eq a => a -> [a] -> ()
lemmaPermutationHeadTailNotElem _ [] = ()
lemmaPermutationHeadTailNotElem h (x:xs) = lemmaPermutationHeadTailNotElem h xs


{-@ ple lemmaPermutationHeadTailElem @-}
{-@ lemmaPermutationHeadTailElem :: Eq a => h:a -> {ops:[a] | List.elem' h ops} ->
  {isPermutation (cons h ops) (List.concat ops (cons h List.empty)) } @-}
lemmaPermutationHeadTailElem :: Eq a => a -> [a] -> ()
lemmaPermutationHeadTailElem _ [] = ()
lemmaPermutationHeadTailElem h (op:ops)
  | h == op
  = if List.elem' h ops then lemmaPermutationHeadTailElem h ops else lemmaPermutationHeadTailNotElem h ops
  | otherwise
  = if List.elem' h ops then lemmaPermutationHeadTailElem h ops else lemmaPermutationHeadTailNotElem h ops


{-@ ple lemmaPReverse0 @-}
{-@ lemmaPReverse0 :: Eq a => h:a -> ops:[a] -> {ops':[a] | Just ops' == removeFirst h (List.concat ops (cons h List.empty))}
  -> {isPermutation ops ops'} @-}
lemmaPReverse0 :: Eq a => a -> [a] -> [a] -> ()
lemmaPReverse0 _ [] _ = ()
lemmaPReverse0 h (op:ops) []
  | Nothing <- removeFirst h (List.concat (op:ops) [h])
  = ()
  | Just _ <- removeFirst h (List.concat (op:ops) [h])
  = ()
lemmaPReverse0 h (op:ops) (op':ops')
  | Nothing <- removeFirst h (List.concat (op:ops) [h])
  = lemmaElemConcat h (op:ops) [h]
  | Just _ <- removeFirst h (List.concat (op:ops) [h])
  , h /= op
  = lemmaPReverse0 h ops ops'
  | List.elem' h ops
  = lemmaPermutationHeadTailElem h ops
  | otherwise
  = lemmaPermutationHeadTailNotElem h ops

{-@ ple lemmaPermutationReverse @-}
{-@ lemmaPermutationReverse :: Eq a => ops:[a] -> {isPermutation ops (List.reverse ops)} @-}
lemmaPermutationReverse :: Eq a => [a] -> ()
lemmaPermutationReverse [] = ()
lemmaPermutationReverse (h:t) = case removeFirst h (List.concat (List.reverse t) [h]) of
  Nothing -> lemmaReverseElem h (h:t)
  Just ops' ->
            lemmaPermutationReverse t
        &&& lemmaPReverse0 h (List.reverse t) ops'
        &&& lemmaPermutationTransitive t (List.reverse t) ops'

{-@ ple lemmaPermutationTransitive @-}
{-@ lemmaPermutationTransitive :: Eq a => ops1:[a] -> ops2:[a] -> ops3:[a] -> {(isPermutation ops1 ops2 && isPermutation ops2 ops3) => isPermutation ops1 ops3} @-}
lemmaPermutationTransitive :: Eq a => [a] -> [a] -> [a] -> ()
lemmaPermutationTransitive [] [] [] = ()
lemmaPermutationTransitive [] _  _  = ()
lemmaPermutationTransitive _  [] _  = ()
lemmaPermutationTransitive _  _  [] = ()
lemmaPermutationTransitive ops1 ops2 ops3 | not (isPermutation ops1 ops2) = ()
lemmaPermutationTransitive ops1 ops2 ops3 | not (isPermutation ops2 ops3) = ()
lemmaPermutationTransitive ops1@(h1:t1) ops2@(h2:t2) ops3 = case removeFirst h1 ops2 of
  Nothing -> ()
  Just ops2' -> case removeFirst h1 ops3 of
    Nothing ->
          assert (List.elem' h1 ops2) ? lemmaRemoveFirstElem h1 ops2 ops2'
      &&& assert (isPermutation ops2 ops3) ? lemmaPermutationContainsElem' h1 ops2 ops3
      &&& assert (List.elem' h1 ops3)
    Just ops3' -> 
          lemmaPermutationCommutative ops1 ops2
      &&& lemmaRemoveFirstPermutation h1 t1 ops2 ops2'
      &&& assert (isPermutation t1 ops2')
      &&& lemmaRemoveFirstPermutation' h1 ops2 ops2' ops3 ops3'
      &&& assert (isPermutation ops2' ops3')
      &&& lemmaPermutationTransitive t1 ops2' ops3'
      &&& assert (isPermutation t1 ops3')
      &&& assert (isPermutation ops1 ops3)
{-@ ple lemmaRemoveFirstPermutation' @-}
{-@ lemmaRemoveFirstPermutation' :: Eq a => v:a -> ops1:[a] -> {ops1':[a] | removeFirst v ops1 == Just ops1'} -> ops2:[a] -> {ops2':[a] | removeFirst v ops2 == Just ops2'} -> {isPermutation ops1 ops2 => isPermutation ops1' ops2'} @-}
lemmaRemoveFirstPermutation' :: Eq a => a -> [a] -> [a] -> [a] -> [a] -> ()
lemmaRemoveFirstPermutation' vd ops1 ops1' ops2 ops2'
  | not (isPermutation ops1 ops2) = ()
lemmaRemoveFirstPermutation' vd [] ops1' _ ops2' = ()
lemmaRemoveFirstPermutation' vd _ ops1' [] ops2' = ()
lemmaRemoveFirstPermutation' vd opsa1@(op1:ops1) ops1' opsa2@(op2:ops2) ops2'
  -- | Just _ <- removeFirst vd opsa1
  -- , Just _ <- removeFirst vd opsa2
  -- , vd == op1
  -- = ()
  -- | Just _ <- removeFirst vd opsa1
  -- , Just _ <- removeFirst vd opsa2
  -- , vd == op2
  -- = ()
  --   ? isPermutation opsa1 (cons op2 ops2)
  --   ? lemmaRemoveFirstPermutation op2 ops2 opsa1 ops1'
  -- | Just _ <- removeFirst vd opsa1
  -- , Just _ <- removeFirst vd opsa2
  -- , Nothing <- removeFirst vd ops1
  -- = ()
  -- | Just _ <- removeFirst vd opsa1
  -- , Just _ <- removeFirst vd opsa2
  -- , Nothing <- removeFirst vd ops2
  -- = ()
  -- | Just ops1'' <- removeFirst vd ops1
  -- , Just ops2'' <- removeFirst vd ops2
  -- , vd /= op1
  -- , vd /= op2
  -- , op1 == op2
  -- =   isPermutation opsa1 opsa2
  --   -- ? assert (op1:ops1'' == ops1')
  --   -- ? assert (op2:ops2'' == ops2')
  -- === isPermutation (op1:ops1) (op2:ops2)
  -- === isPermutation ops1 ops2
  -- ? lemmaRemoveFirstPermutation' vd ops1 ops1'' ops2 ops2''
  -- === isPermutation ops1' ops2'
  -- *** QED
  | Just _ <- removeFirst vd opsa1
  , Just _ <- removeFirst vd opsa2
  , Just ops1'' <- removeFirst vd ops1
  , Just ops2'' <- removeFirst vd ops2
  , Just ops2No1 <- removeFirst op1 ops2''
  -- , _            <- removeFirst op1 (op2:ops2'')
  , vd /= op1
  , vd /= op2
  , op1 /= op2
  =   isPermutation opsa1 opsa2
    -- ? assert (op1:ops1'' == ops1')
    -- ? assert (op2:ops2'' == ops2')
  === isPermutation (op1:ops1) (op2:ops2)
  ? lemmaRemoveFirstPermutation' vd ops1 ops1'' ops2 ops2''
  -- === isPermutation ()
  === isPermutation (op1:ops1'') (op2:ops2'')
  === isPermutation ops1' ops2'
  *** QED
  | otherwise = undefined
-- lemmaRemoveFirstPermutation' vd opsa1@(op1:ops1) ops1' opsa2@(op2:ops2) ops2'
--   | Just _ <- removeFirst vd opsa1
--   , Just _ <- removeFirst vd opsa2
--   = ()
{-@ lemmaPermutationContainsElem' :: Eq a => op:a -> ops1:[a] -> {ops2:[a] | isPermutation ops1 ops2} -> {List.elem' op ops1 => List.elem' op ops2} @-}
lemmaPermutationContainsElem' :: Eq a => a -> [a] -> [a] -> ()
lemmaPermutationContainsElem' _ _ _ = undefined -- TODO

{-@ lemmaPermutationContainsElem'' :: Eq a => op:a -> ops1:[a] -> {ops2:[a] | isPermutation ops1 ops2} -> {List.elem' op ops2 => List.elem' op ops1} @-}
lemmaPermutationContainsElem'' :: Eq a => a -> [a] -> [a] -> ()
lemmaPermutationContainsElem'' _ _ _ = undefined -- TODO


{-@ ple lemmaPermutationCommutative @-}
{-@ lemmaPermutationCommutative :: Eq a => ops1:[a] -> ops2:[a] -> {isPermutation ops1 ops2 => isPermutation ops2 ops1} / [len ops2] @-}
lemmaPermutationCommutative :: Eq a => [a] -> [a] -> ()
lemmaPermutationCommutative [] [] = ()
lemmaPermutationCommutative _  [] = ()
lemmaPermutationCommutative [] _  = ()
lemmaPermutationCommutative ops1 ops2 | not (isPermutation ops1 ops2) = ()
lemmaPermutationCommutative ops1 ops2@(h2:t2) = case removeFirst h2 ops1 of
  Nothing ->
        assert (List.elem' h2 ops2)
    &&& lemmaPermutationContainsElem'' h2 ops1 ops2
    &&& assert (List.elem' h2 ops1)

  Just ops1' -> 
        lemmaRemoveFirstPermutation h2 t2 ops1 ops1'
    &&& assert (isPermutation ops1 (h2:t2))
    &&& assert (isPermutation (h2:ops1') (h2:t2))
    &&& assert (isPermutation ops1' t2)
    &&& lemmaPermutationCommutative ops1' t2
    &&& assert (isPermutation t2 ops1')
    &&& assert (isPermutation ops2 ops1)




