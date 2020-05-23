{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.TwoPMap.LemmaIA where

import VRDT.TwoPMap.Internal
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

{-@ lawCommutativityIAEq' :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k:k -> v1:v -> vop2:Operation v -> {  (compatibleTwoPMap (TwoPMapInsert k v1) (TwoPMapApply k vop2) && compatibleStateTwoPMap x (TwoPMapInsert k v1) && compatibleStateTwoPMap x (TwoPMapApply k vop2)) => compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k v1)) (TwoPMapApply k vop2)} @-}
lawCommutativityIAEq' :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> Operation v -> ()
lawCommutativityIAEq' x@(TwoPMap m p t) k v  vop'
  | not ( (compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2))
  = ()
  | isJust (Map.lookup k m)
  = ()
  | Set.member k t
  = ()
  | Nothing <- Map.lookup k p
  = (applyTwoPMap x op1
  ==. (TwoPMap (Map.insert k (maybe v (foldr (flip apply) v) Nothing) m) p t)
  ==. (TwoPMap (Map.insert k v1 m) p t) *** QED)
  &&& (m1 === Map.insert k v1 m *** QED)
  &&& lemmaLookupInsert m k v1
  | Just ops <- Map.lookup k p
  = ( compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k v)) (TwoPMapApply k vop')
      ? lemmaLookupInsert m k v1
      ? (Map.lookup k m1 ==. Just v1 *** QED)
      ? (v1 ==. foldr (flip apply) v ops *** QED)
      ? lemma0 ops vop' v
  ==. compatibleStateTwoPMap (TwoPMap m1 p1 t1) (TwoPMapApply k vop')
  ==. compatibleState v1 vop'
  ==. compatibleState (foldr (flip apply) v ops) vop'
  *** QED)
  where op1 = TwoPMapInsert k v
        op2 = TwoPMapApply k vop'
        v1 = maybe v (foldr (flip apply) v) (Map.lookup k p)
        TwoPMap m1 p1 t1 = applyTwoPMap x op1


{-@ lemma0 :: (Ord (Operation v), VRDT v) => ops:[Operation v] -> vop:Operation v ->
  {v:v | allCompatibleState v ops && compatibleState v vop && allCompatible' vop ops} ->
  {compatibleState (List.foldr (flip apply) v ops) vop} @-}
lemma0 :: (Ord (Operation v), VRDT v) => [Operation v] -> Operation v -> v -> ()
lemma0 [] _ _ = ()
lemma0 (op:ops) vop v =
        lemma0 ops vop v
      ? lemma0 ops op v
      ? lawCompatibilityCommutativity op vop
      ? lawCommutativity (List.foldr (flip apply) v ops) op vop
      ? lawCommutativity (List.foldr (flip apply) v ops) vop op




{-@ lawCommutativityIANeq :: (Ord k, Ord (Operation v), VRDT v) => x : TwoPMap k v -> k1:k -> v1:v -> {k2:k | k1 /= k2} -> {vop2:Operation v | True} -> {  (compatibleTwoPMap (TwoPMapInsert k1 v1) (TwoPMapApply k2 vop2) && compatibleStateTwoPMap x (TwoPMapInsert k1 v1) && compatibleStateTwoPMap x (TwoPMapApply k2 vop2)) => ((applyTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2) == applyTwoPMap (applyTwoPMap x (TwoPMapApply k2 vop2)) (TwoPMapInsert k1 v1)) && compatibleStateTwoPMap (applyTwoPMap x (TwoPMapInsert k1 v1)) (TwoPMapApply k2 vop2))} @-}
lawCommutativityIANeq :: (Ord k, Ord (Operation v), VRDT v) => TwoPMap k v -> k -> v -> k -> Operation v -> ()
lawCommutativityIANeq x@(TwoPMap m p t) k v k' vop'
  -- lawCommutativity x@(TwoPMap m p t) op1@(TwoPMapInsert k v) op2@(TwoPMapApply k' vop')
  | not (compatibleTwoPMap op1 op2 && compatibleStateTwoPMap x op1 && compatibleStateTwoPMap x op2)
  = ()
  | Set.member k t
  = compatibleStateTwoPMap x op2 *** QED
  ? Set.member k (twoPMapTombstone (applyTwoPMap x op2))
  | Set.member k' t
  , Nothing <- Map.lookup k p
  = (Set.member k' (twoPMapTombstone (applyTwoPMap x op1)) *** QED)
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ===  applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
    &&& lemmaLookupInsert2 m k' k v1
  | Set.member k' t
  , Just _ <- Map.lookup k p
  = (Set.member k' (twoPMapTombstone (applyTwoPMap x op1)) *** QED)
    &&& (applyTwoPMap (applyTwoPMap x op1) op2 ===  applyTwoPMap (applyTwoPMap x op2) op1 *** QED)
    &&& lemmaLookupInsert2 m k' k v1
  | not (Set.member k t)
  , not (Set.member k' t)
  , Nothing <- Map.lookup k p
  , Nothing <- Map.lookup k' m
  =        lemmaDelete k k' p
        &&& lemmaLookupInsert2 m k' k v1
        &&& lemmaLookupInsert2 p k k' l2
        &&& lemmaLookupDelete2 p k' k
        &&& lemmaInsertDelete k' l2 k p
        &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
        ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
        ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
        *** QED
        )
  | not (Set.member k t)
  , not (Set.member k' t)
  , Just xx <- Map.lookup k p
  , Nothing <- Map.lookup k' m
  =   
            lemmaDelete k k' p
        &&& lemmaLookupInsert2 m k' k v1
        &&& lemmaLookupInsert2 p k k' l2
        &&& lemmaLookupDelete2 p k' k
        &&& lemmaInsertDelete k' l2 k p
        &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
        ==.  TwoPMap (Map.insert k v1 m) (Map.insert k' l2 p) t
        ==.  applyTwoPMap (TwoPMap m (Map.insert k' l2 p) t) op1
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
        *** QED
        )
  | not (Set.member k t)
  , not (Set.member k' t)
  , Just xx <- Map.lookup k p
  , Just vv <- Map.lookup k' m
  =   let v1 = maybe v (foldr (flip apply) v) (Just xx)
          v2 = apply vv vop' in
            lemmaLookupInsert2 m k' k v1
        &&& lemmaLookupInsert2 m k k' v2
        -- &&& lemmaLookupInsert2 p k k' l2
        &&& lemmaLookupDelete2 p k' k
        &&& lemmaInsert k v1 k' v2 m

        -- &&& lemmaInsertDelete k' l2 k p
        &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) (Map.delete k p) t) (TwoPMapApply k' vop')
        ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) (Map.delete k p) t
        ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) (Map.delete k p)  t
        ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
        *** QED
        )
  | not (Set.member k t)
  , not (Set.member k' t)
  , Nothing <- Map.lookup k p
  , Just vv <- Map.lookup k' m
  =   let v1 = maybe v (foldr (flip apply) v) Nothing
          v2 = apply vv vop' in
            lemmaLookupInsert2 m k' k v1
        &&& lemmaLookupInsert2 m k k' v2
        -- &&& lemmaLookupInsert2 p k k' l2
        &&& lemmaLookupDelete2 p k' k
        &&& lemmaInsert k v1 k' v2 m
        -- &&& lemmaInsertDelete k' l2 k p
        &&& (applyTwoPMap (applyTwoPMap (TwoPMap m p t) op1) op2
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) (TwoPMapInsert k v)) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) op2
        ==.  applyTwoPMap (TwoPMap (Map.insert k v1 m) p t) (TwoPMapApply k' vop')
        ==.  TwoPMap (Map.insert k' v2 (Map.insert k v1 m)) p t
        ==.  TwoPMap (Map.insert k v1 (Map.insert k' v2 m)) p  t
        ==.  applyTwoPMap (TwoPMap (Map.insert k' v2 m) p t) op1
        ==.  applyTwoPMap (applyTwoPMap (TwoPMap m p t) op2) op1
        *** QED
        )

  | otherwise = undefined
  where op1 = TwoPMapInsert k v
        op2 = TwoPMapApply k' vop'
        v1 = maybe v (foldr (flip apply) v) (Map.lookup k p)
        l2 = case Map.lookup k' p of
                 Nothing -> [vop']
                 Just ops -> insertList vop' ops 



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
    ==! applyTwoPMap (TwoPMap (Map.insert k v1' m) (Map.delete k p) t) (TwoPMapApply k vop2)  -- OK
        ?   lemmaLookupInsert m k v1'
        &&& (Map.lookup k (Map.insert k v1' m) === Just v1' *** QED)
        &&& assert (isJust (Map.lookup k (Map.insert k v1' m)))
    ==! TwoPMap (Map.insert k v1'' (Map.insert k v1' m)) (Map.delete k p) t -- OK
        ?   lemmaInsertTwice k v1'' v1' m
    ==! TwoPMap (Map.insert k v1'' m) (Map.delete k p) t -- OK
        ?   lemmaPermutation vop2 ops ops2
        &&& assert (isPermutation (vop2:ops) ops2) -- OK
        &&& assert (allCompatibleState v1 ops) -- OK
        &&& assert (compatibleState v1 vop2) -- OK
        &&& assert (allCompatibleState v1 (vop2:ops)) -- OK
        &&& assert (allCompatible ops) -- OK
        &&& assert (allCompatible (vop2:ops)) -- OK
        &&& strongConvergence v1 (vop2:ops) ops2
        &&& (applyAll v1 (vop2:ops) === applyAll v1 ops2 *** QED)
        &&& lemmaApplyAll v1 (vop2:ops) -- TODO
        &&& lemmaApplyAll v1 ops2 -- TODO
        &&& (v1'' === v2' *** QED) -- OK
        &&& lemmaDeleteInsert k ops2 p
    ==! TwoPMap (Map.insert k v2' m) (Map.delete k (Map.insert k ops2 p)) t -- OK
        ?   lemmaLookupInsert p k ops2
    ==! applyTwoPMap (TwoPMap m (Map.insert k ops2 p) t) (TwoPMapInsert k v1) -- OK
    ==! applyTwoPMap (applyTwoPMap x (TwoPMapApply k vop2)) (TwoPMapInsert k v1) -- OK
    *** QED)

  where op1 = TwoPMapInsert k v1
        op2 = TwoPMapApply k vop2


        vop' = vop2
        v = v1

        -- l1 = case Map.lookup k p of
        --        Nothing -> [vop']
        --        Just ops -> insertList vop' ops



{-@ lemmaApplyAll :: VRDT a => v1:a -> ops:[Operation a] -> {applyAll v1 ops == Liquid.Data.List.foldr (flip apply) v1 ops} @-}
lemmaApplyAll :: VRDT a => a -> [Operation a] -> ()
lemmaApplyAll v1 ops = undefined -- TODO


{-@ ple insertRemoveFirst @-}
{-@ insertRemoveFirst :: Ord a => x:a -> xs:[a] -> {removeFirst x (insertList x xs) == Just xs} @-}
insertRemoveFirst :: Ord a => a -> [a] -> ()
insertRemoveFirst x [] = ()
insertRemoveFirst x (y:ys)
  | x < y = ()
  | x == y = ()
  | x > y = insertRemoveFirst x ys

{-@ ple permutationId @-}
{-@ permutationId :: (Eq a) => x:[a] -> {isPermutation x x} @-}
permutationId :: Eq a => [a] -> ()
permutationId [] = ()
permutationId (x:xs) = permutationId xs

{-@ ple lemmaPermutation @-}
{-@ lemmaPermutation :: Ord a => vop2:a -> ops:[a] -> {ops2:[a] | insertList vop2 ops = ops2} -> {isPermutation (cons vop2 ops) ops2} @-}
lemmaPermutation :: Ord a => a -> [a] -> [a] -> ()
lemmaPermutation _ [] [] = ()
lemmaPermutation _ [] _ = ()
lemmaPermutation vop2 ops@(h:ops') ops2 
  | vop2 <= h = 
        -- insertList vop2 (h:ops')
        isPermutation (vop2:ops) ops2
    === isPermutation (vop2:ops) (insertList vop2 (h:ops'))
    === isPermutation (vop2:ops) (vop2:h:ops')
        -- ? assert (ops =)
    === isPermutation (ops) (h:ops')
        ? lemmaPermutation' ops
    === isPermutation (ops) (ops)
    *** QED
  | otherwise =
        isPermutation (vop2:ops) ops2
    === isPermutation (vop2:ops) (insertList vop2 (h:ops')) -- ? lemmaPermutation vop2 ops'
        ? insertRemoveFirst vop2 ops'
    === isPermutation (vop2:ops) (h:insertList vop2 ops')
    === isPermutation ops (h: ops')
        ? permutationId ops
    *** QED

{-@ ple lemmaPermutation' @-}
{-@ lemmaPermutation' :: Eq a => ops:[a] -> {isPermutation ops ops} @-}
lemmaPermutation' :: Eq a => [a] -> ()
lemmaPermutation' []    = ()
lemmaPermutation' (h:t) = lemmaPermutation' t
