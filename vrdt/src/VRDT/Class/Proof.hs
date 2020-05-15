{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--oldple" @-}
{-@ LIQUID "--ple-local" @-}

module VRDT.Class.Proof where

import           Liquid.Data.Maybe
import qualified Liquid.Data.List as List
import           Liquid.ProofCombinators
import           VRDT.Class
import           Prelude hiding (Maybe(..), length, fromJust, tail)
import qualified Data.Set as S

{-@ ple strongConvergence @-}
{-@ strongConvergence :: (Eq (Operation a), VRDT a) => s0:a -> ops1:[Operation a] -> ops2:[Operation a] -> {(isPermutation ops1 ops2 && allCompatibleState s0 ops1 && allCompatible ops1) => (applyAll s0 ops1 = applyAll s0 ops2)} @-}
strongConvergence :: (Eq (Operation a), VRDT a) => a -> [Operation a] -> [Operation a] -> ()
strongConvergence s0 [] [] = ()
strongConvergence s0 [] _ = ()
strongConvergence s0 _ [] = ()
strongConvergence s0 ops1 ops2 | not (isPermutation ops1 ops2) = ()
strongConvergence s0 ops1 ops2 | not (allCompatible ops1) = ()
strongConvergence s0 ops1 ops2 | not (allCompatibleState s0 ops1) = ()
strongConvergence s0 ops1@(op1:ops1') ops2@(op2:ops2') 
  | op1 == op2 = 
        lemmaAllCompatibleTail op1 ops1'
    &&& lemmaAllCompatibleStateTail s0 op1 ops1'
    &&& strongConvergence (apply s0 op1) ops1' ops2'
  | otherwise = case removeFirst op2 ops1 of
    Nothing ->
          assert (isPermutation ops1 ops2)
      &&& lemmaPermutationContainsElem op2 ops2' ops1
      &&& assert (List.elem' op2 ops1)
      -- &&& lemmaRemoveElemIsJust op2 ops1
    Just ops1'' ->
          -- lemmaPermutationSymmetric (op2:ops1) ops1''
          lemmaRemoveFirstAllCompatible op2 ops1 ops1''
      &&& (
          applyAll s0 ops1 ? lemmaRemoveFirstApplyAll s0 op2 ops1 ops1''
      === applyAll (apply s0 op2) ops1''
      *** QED
      ) &&& (
          applyAll s0 ops2
      === applyAll (apply s0 op2) ops2'
      *** QED
      )
      &&& lemmaRemoveFirstPermutation op2 ops2' ops1 ops1''
      &&& lemmaRemoveFirstAllCompatibleState s0 op2 ops1 ops1''
      -- &&& assert (allCompatibleState (apply s0 op2) ops1'')
      &&& strongConvergence (apply s0 op2) ops1'' ops2'

-- {-@ reflect elems @-}
-- elems :: 

{-@ reflect allCompatibleState @-}
{-@ ple allCompatibleState @-}
{-@ allCompatibleState :: VRDT a => x:a -> ops:[Operation a] -> {vv:Bool | (vv && len ops > 0) => allCompatibleState x (List.tail ops)} @-}
allCompatibleState :: VRDT a => a -> [Operation a] -> Bool
allCompatibleState _ [] = True
allCompatibleState x (h:t) = compatibleState x h && allCompatibleState x t

{-@ reflect allCompatible @-}
{-@ ple allCompatible @-}
{-@ allCompatible :: VRDT a => xs:[Operation a] ->
  {vv:Bool | (vv && len xs > 0) => allCompatible (List.tail xs)} @-}
allCompatible :: VRDT a => [Operation a] -> Bool
allCompatible [] = True
allCompatible (op1:ops) = allCompatible' op1 ops

{-@ reflect allCompatible' @-}
allCompatible' :: VRDT a => Operation a -> [Operation a] -> Bool
allCompatible' _  []        = True
-- allCompatible' op (op':ops) = compatible op op' && allCompatible' op ops
-- allCompatible' op (op':ops) = compatible op op' && compatible op' op && allCompatible' op ops && allCompatible' op' ops
allCompatible' op (op':ops) = compatible op op' && allCompatible' op ops && allCompatible' op' ops

{-@ reflect applyAll @-}
applyAll :: VRDT a => a -> [Operation a] -> a
applyAll s []       = s
applyAll s (op:ops) = applyAll (apply s op) ops

{-@ reflect isPermutation @-}
{-@ ple isPermutation @-}
{-@ isPermutation :: Eq o => xs:[o] -> ys:[o] -> {v:Bool | v => len xs == len ys} @-}
isPermutation :: Eq o => [o] -> [o] -> Bool
isPermutation []    []    = True
isPermutation (_:_) []    = False
isPermutation []    (_:_) = False
isPermutation (op1:ops1') ops2 = case removeFirst op1 ops2 of
    Nothing -> False
    Just ops2' -> isPermutation ops1' ops2'

{-@ reflect removeFirst @-}
{-@ ple removeFirst @-}
{-@ removeFirst :: Eq o => x:o -> xs:[o] ->
   {vv:Maybe [o] | (isJust vv => 1 + len (fromJust vv) == len xs) &&
                   (List.elem' x xs => isJust vv)} @-}
removeFirst :: Eq o => o -> [o] -> Maybe [o]
removeFirst o [] = Nothing
removeFirst o (h:t) = 
  if h == o then 
    Just t 
  else 
    -- (h:) <$> removeFirst o t
    case removeFirst o t of
        Nothing -> Nothing
        Just t' -> Just (h:t')



-- Lemmas

{-@ reflect cons @-}
cons :: a -> [a] -> [a]
cons a as = a:as

{-@ ple lemmaPermutationContainsElem @-}
{-@ lemmaPermutationContainsElem :: Eq a => op2:a -> ops2':[a] -> {ops1:[a] | isPermutation ops1 (cons op2 ops2')} -> {List.elem' op2 ops1} @-}
lemmaPermutationContainsElem :: Eq a => a -> [a] -> [a] -> ()

lemmaPermutationContainsElem op2 _ [] = ()
lemmaPermutationContainsElem op2 [] (op1:ops1)
  | op1 == op2 = ()
  | otherwise = ()
lemmaPermutationContainsElem op2 (op2':ops2) ops1@(op1:ops1') 
  | op1 == op2 = ()
  | otherwise  = case removeFirst op1 (op2:op2':ops2) of
      Nothing -> ()
      Just (op2'':ops2') -> lemmaPermutationContainsElem op2'' ops2' ops1'


{-@ ple lemmaAllCompatibleTail @-}
{-@ lemmaAllCompatibleTail :: VRDT a => op:Operation a -> {ops:[Operation a] | allCompatible (cons op ops)} -> {allCompatible ops} @-}
lemmaAllCompatibleTail :: VRDT a => Operation a -> [Operation a] -> ()
lemmaAllCompatibleTail op [] = ()
lemmaAllCompatibleTail op (_:ops) = lemmaAllCompatibleTail op ops

{-@ ple lemmaAllCompatibleStateTail @-}
{-@ lemmaAllCompatibleStateTail :: VRDT a => x:a -> op:Operation a -> {ops:[Operation a] | allCompatibleState x (cons op ops) && allCompatible (cons op ops)} -> {allCompatibleState (apply x op) ops} @-}
lemmaAllCompatibleStateTail :: VRDT a => a -> Operation a -> [Operation a] -> ()
lemmaAllCompatibleStateTail _ _ [] = ()
lemmaAllCompatibleStateTail x op1 (op2:ops) = 
      allCompatibleState x (op1:op2:ops)
  ==. (compatibleState x op1 && allCompatibleState x (op2:ops))
  ==. (compatibleState x op1 && compatibleState x op2 && allCompatibleState x ops) ?
            lemmaAllCompatibleStateTail x op1 ops
        &&& assert (compatibleState x op1)
        &&& assert (compatibleState x op2)
        &&& assert (compatible op1 op2)
        &&& lawCommutativity x op1 op2
  ==. (compatibleState (apply x op1) op2 && allCompatibleState (apply x op1) (op2:ops))
  ==. allCompatibleState (apply x op1) (op2:ops)
  *** QED



{-@ ple lemmaRemoveFirstPermutation @-}
{-@ lemmaRemoveFirstPermutation :: Eq a => op2:a -> ops2':[a] -> {ops1:[a] | isPermutation ops1 (cons op2 ops2')} -> {rs:[a] | removeFirst op2 ops1 == Just rs} -> {isPermutation rs ops2'} @-}
lemmaRemoveFirstPermutation :: Eq a => a -> [a] -> [a] -> [a] -> ()
lemmaRemoveFirstPermutation op2 ops2 [] rs = ()
lemmaRemoveFirstPermutation op2 [] (op1:ops1) rs
  | op1 == op2 = ()
  | otherwise = ()
lemmaRemoveFirstPermutation op2 ops2 (op1:ops1) rs
  | op1 == op2
  = ()
  | Just ops2_op1 <- removeFirst op1 ops2
  = assert (isPermutation ops1 (op2:ops2_op1))
    ? lemmaPermutationContainsElem op2 ops2_op1 ops1
    ? assert (isJust (removeFirst op2 ops1))
    ? case removeFirst op2 ops1 of
        Just ops1_op2 -> lemmaRemoveFirstPermutation op2 ops2_op1 ops1 ops1_op2
                         ? assert (isPermutation ops1_op2 ops2_op1)
                         ? (isPermutation (op1:ops1_op2) ops2 ==. isPermutation ops1_op2 ops2_op1)
  

-- lemmaRemoveFirstPermutation op2 _ [] rs = () -- TODO
-- lemmaRemoveFirstPermutation op2 [] _ rs = ()
-- lemmaRemoveFirstPermutation op2 ops2@(op2':ops2') ops1@(op1:ops1') (r:rs)  =
--   case removeFirst op2' rs of
--     Nothing -> ()
--     -- is permutation ops1'' ops2
--     Just ops1'' -> lemmaRemoveFirstPermutation op2' ops2' rs ops1''
-- lemmaRemoveFirstPermutation op2 _ _ [] = ()

{-@ ple lemmaRemoveFirstAllCompatible' @-}
{-@ lemmaRemoveFirstAllCompatible' :: (Eq (Operation a), VRDT a) => od:Operation a -> o:Operation a -> {os:[Operation a] | allCompatible' o os} -> {rs:[Operation a] | removeFirst od os == Just rs} -> {allCompatible' o rs} @-}
lemmaRemoveFirstAllCompatible' :: (Eq (Operation a), VRDT a) => Operation a -> Operation a -> [Operation a] -> [Operation a] -> ()
lemmaRemoveFirstAllCompatible' od o [] _ = ()
lemmaRemoveFirstAllCompatible' od o (op:ops) rs
  | od /= op
  , a:as <- rs 
  , Just rs' <- removeFirst od ops = lemmaRemoveFirstAllCompatible' od o ops rs'
                                     ? lemmaRemoveFirstAllCompatible' od a ops rs'
  | otherwise = ()


  
{-@ ple lemmaRemoveFirstAllCompatible @-}
{-@ lemmaRemoveFirstAllCompatible :: (Eq (Operation a), VRDT a) => op:Operation a -> {os:[Operation a] | allCompatible os} -> {rs:[Operation a] | removeFirst op os == Just rs} -> {allCompatible rs} @-}
lemmaRemoveFirstAllCompatible :: (Eq (Operation a), VRDT a) => Operation a -> [Operation a] -> [Operation a] -> ()
lemmaRemoveFirstAllCompatible _ [] _ = () 
lemmaRemoveFirstAllCompatible op (o:os) rs
  | o == op =   assert (os == rs)
              ? lemmaAllCompatibleTail o os
  | otherwise = case removeFirst op os of
      Just rs'  -> lemmaRemoveFirstAllCompatible' op o os rs'

{-@ ple lemmaRemoveFirstAllCompatibleState @-}
{-@ lemmaRemoveFirstAllCompatibleState :: (Eq (Operation a), VRDT a) => 
    x:a -> 
    op:Operation a -> 
    {os:[Operation a] | allCompatibleState x os && allCompatible os} -> 
    {rs:[Operation a] | removeFirst op os == Just rs} -> 
    {allCompatibleState (apply x op) rs} 
@-}
lemmaRemoveFirstAllCompatibleState :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> [Operation a] -> ()
lemmaRemoveFirstAllCompatibleState x op1 ops [] = ()
lemmaRemoveFirstAllCompatibleState x op1 (op2:ops) rs
  | op1 == op2 = 
        assert (allCompatibleState x ops)
    &&& lemmaAllCompatibleTail op2 ops
    &&& assert (allCompatible ops)
    &&& lemmaAllCompatibleStateTail x op1 ops
  | otherwise  = case removeFirst op1 ops of
      Nothing -> ()
      Just rs' -> 
            assert (allCompatibleState x (op2:ops))
        &&& assert (allCompatible (op2:ops))

        &&& assert (allCompatibleState x ops)
        &&& assert (allCompatible ops)

        &&& lemmaRemoveFirstAllCompatibleState x op1 ops rs'
        &&& assert (allCompatibleState (apply x op1) rs')
        &&& assert (rs == (op2:rs'))

        &&& lemmaRemoveFirstElem op1 (op2:ops) rs
        &&& lemmaAllCompatibleElem op1 op2 ops

        &&& assert (compatibleState x op2)

        &&& lawCompatibilityCommutativity op1 op2
        &&& assert (compatible op1 op2)
        &&& lemmaAllCompatibleStateElem x op1 (op2:ops)
        &&& assert (compatibleState x op1)

        &&& lawCommutativity x op1 op2
        &&& assert (compatibleState (apply x op1) op2)


        &&& assert (allCompatibleState (apply x op1) rs) -- Goal


{-@ ple lemmaRemoveFirstApplyAll @-}
{-@ lemmaRemoveFirstApplyAll :: (Eq (Operation a), VRDT a) => x:a -> op:Operation a -> {os:[Operation a] | allCompatible os} -> {rs:[Operation a] | removeFirst op os == Just rs} -> {applyAll x os = applyAll (apply x op) rs} @-}
lemmaRemoveFirstApplyAll :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> [Operation a] -> ()
lemmaRemoveFirstApplyAll x op [] [] = ()
lemmaRemoveFirstApplyAll x op _  [] = ()
lemmaRemoveFirstApplyAll x op ops _ | not (allCompatible ops) = ()
lemmaRemoveFirstApplyAll x op ops@(op1:ops') rs
  | op1 == op = ()
  | otherwise = case removeFirst op ops' of
    Nothing ->
      ()
    Just ops'' ->
          applyAll x ops
      ==. applyAll (apply x op1) ops'
        ?   lemmaAllCompatibleTail op1 ops'
        &&& lemmaRemoveFirstApplyAll (apply x op1) op ops' ops''
      ==. applyAll (apply (apply x op1) op) ops''
        ?   lemmaRemoveFirstElem op ops rs
        &&& lawCompatibilityCommutativity op op1
        &&& lemmaAllCompatibleElem op op1 ops'
        &&& lawCommutativity x op1 op
      ==. applyAll (apply (apply x op) op1) ops''
      ==. applyAll (apply x op) rs
      *** QED

{-@ ple lemmaAllCompatibleElem  @-}
{-@ lemmaAllCompatibleElem :: (Eq (Operation a), VRDT a) => op:Operation a -> op':Operation a -> {ops:[Operation a] | List.elem' op ops && allCompatible' op' ops} -> {compatible op' op} @-}
lemmaAllCompatibleElem :: (Eq (Operation a), VRDT a) => Operation a -> Operation a -> [Operation a] -> ()
lemmaAllCompatibleElem op op' [] =  ()
lemmaAllCompatibleElem op op' (op'':ops)
  | op == op'' = ()
  | otherwise = lemmaAllCompatibleElem op op' ops

{-@ ple lemmaAllCompatibleStateElem @-}
{-@ lemmaAllCompatibleStateElem :: (Eq (Operation a), VRDT a) => x:a -> op:Operation a -> {ops:[Operation a] | List.elem' op ops && allCompatibleState x ops} -> {compatibleState x op} @-}
lemmaAllCompatibleStateElem :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> ()
lemmaAllCompatibleStateElem _ _ [] = ()
lemmaAllCompatibleStateElem x op1 (op2:ops) 
  | op1 == op2 = ()
  | otherwise  = lemmaAllCompatibleStateElem x op1 ops


{-@ ple lemmaRemoveFirstElem @-}
{-@
lemmaRemoveFirstElem :: (Eq (Operation a), VRDT a)
 => op:Operation a 
 -> os:[Operation a]
 -> {rs:[Operation a] | removeFirst op os == Just rs}
 -> {List.elem' op os}
@-}
lemmaRemoveFirstElem :: (Eq (Operation a)) => Operation a -> [Operation a] -> [Operation a] -> ()
lemmaRemoveFirstElem op [] _ = ()
lemmaRemoveFirstElem op _ [] = ()
lemmaRemoveFirstElem op os@(_:t) rs@(r:rs')
  | op == r = ()
  | otherwise = case removeFirst op os of
    Nothing -> ()
    Just _rs -> case removeFirst op t of
      Nothing -> ()
      Just rs'' -> lemmaRemoveFirstElem op t rs''














-- 
-- -- JP: This definition differs from Shapiro's SEC since order doesn't matter for us.
-- {-@ ple commutativeStrongEventualConsistency @-}
-- {-@ commutativeStrongEventualConsistency :: (Eq (Operation a), VRDT a) => s0 : a -> {ops1 : [Operation a] | allEnabled s0 ops1} -> {ops2 : [Operation a] | allEnabled s0 ops2} -> {isPermutation ops1 ops2 => applyAll s0 ops1 = applyAll s0 ops2} @-}
-- commutativeStrongEventualConsistency :: (Eq (Operation a), VRDT a) => a -> [Operation a] -> [Operation a] -> ()
-- commutativeStrongEventualConsistency _ [] [] = ()
-- commutativeStrongEventualConsistency _ _ [] = ()
-- commutativeStrongEventualConsistency _ [] _ = ()
-- commutativeStrongEventualConsistency s0 ops1 ops2 | not (isPermutation ops1 ops2) = ()
-- -- commutativeStrongEventualConsistency s0 ops1@(op1:t1) ops2@(op2:t2) | op1 == op2 = commutativeStrongEventualConsistency (apply s0 op1) t1 t2
-- 
-- 
-- -- commutativeStrongEventualConsistency s0 (op1:ops1) (op2:ops2) = ()
-- commutativeStrongEventualConsistency s0 ops1@(op1:t1) ops2@(op2:t2) = case removeFirst op1 ops2 of
--   Nothing -> 
--     () -- unreachable
--   Just ops2' -> 
--   -- case removeFirst op2 ops1 of
--   --   Nothing ->
--   --     () -- unreachable
--   --   Just ops1' ->
--         --     commutativeStrongEventualConsistency (apply s0 op1) ops1 ops2
--         -- &&& commutativeStrongEventualConsistency (apply s0 op2) ops1 ops2
--           applyAll s0 (op1:t1)
--       ==. applyAll (apply s0 op1) t1
--             ?   lemmaRemoveFirstEnabled s0 op1 ops2 ops2'
--             &&& assert (allEnabled s0 ops2')
--             &&& assume (allEnabled (apply s0 op1) ops2') -- TODO XXX
--             &&& commutativeStrongEventualConsistency (apply s0 op1) t1 ops2'
--       ==. applyAll (apply s0 op1) ops2'
--       ==. applyAll s0 (op1:ops2')
--             ?   lemmaRemoveFirstApplied s0 op1 ops2 ops2'
--       ==. applyAll s0 ops2
--       *** QED
-- 
-- {-@ reflect allEnabled @-}
-- allEnabled :: VRDT a => a -> [Operation a] -> Bool
-- allEnabled s0 [] = True
-- allEnabled s0 ops@(op:ops') = enabled s0 op && allEnabled s0 ops' && allEnabled (apply s0 op) ops'
-- -- allEnabled s0 ops@(op:ops') = allEnabled' s0 ops && allEnabled (apply s0 op) ops'
-- -- 
-- -- {-@ reflect allEnabled' @-}
-- -- allEnabled' :: VRDT a => a -> [Operation a] -> Bool
-- -- allEnabled' _  []       = True
-- -- allEnabled' s0 (op:ops) = enabled s0 op && allEnabled' s0 ops

-- 
-- 
-- 
-- 
-- -- {-@ ple lemmaRemoveFirstEnabled @-}
-- {-@ lemmaRemoveFirstEnabled :: (Eq (Operation a), VRDT a) 
--  => x:a 
--  -> op:Operation a 
--  -> {os:[Operation a] | allEnabled x os} 
--  -> {rs:[Operation a] | removeFirst op os == Just rs} 
--  -> {allEnabled x rs}
-- @-}
-- lemmaRemoveFirstEnabled :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> [Operation a] -> ()
-- lemmaRemoveFirstEnabled x op os rs = undefined -- TODO XXX
-- 
-- {-@ ple lemmaRemoveFirstEnabled' @-}
-- {-@ lemmaRemoveFirstEnabled' :: (Eq (Operation a), VRDT a) 
--  => x:a 
--  -> op:Operation a 
--  -> {os:[Operation a] | allEnabled x os} 
--  -> {rs:[Operation a] | removeFirst op os == Just rs} 
--  -> {enabled x op}
-- @-}
-- lemmaRemoveFirstEnabled' :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> [Operation a] -> ()
-- lemmaRemoveFirstEnabled' x op [] _ = ()
-- lemmaRemoveFirstEnabled' x op _ [] = ()
-- lemmaRemoveFirstEnabled' x op os rs | not (allEnabled x os) = ()
-- lemmaRemoveFirstEnabled' x op os@(h:t) rs
--   | h == op   = ()
--   | otherwise = case removeFirst op os of
--       Nothing -> ()
--       Just _rs -> 
--             assert (rs == _rs)
--         &&& lemmaRemoveFirstElem op os rs
--         &&& lemmaElemEnabled' x op os
-- 
-- {-@ ple lemmaElemEnabled' @-}
-- {-@ lemmaElemEnabled' :: (Eq (Operation a), VRDT a) 
--  => x:a 
--  -> op:Operation a 
--  -> {os:[Operation a] | allEnabled x os && List.elem' op os}
--  -> {enabled x op}
-- @-}
-- lemmaElemEnabled' :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> ()
-- lemmaElemEnabled' x op [] = ()
-- lemmaElemEnabled' x op ops@(h:t) 
--   | op == h   = ()
--   | otherwise = 
--         assert (List.elem' op t)
--     &&& lemmaAllEnabled x h t
--     -- &&& assert (allEnabled x t)
--     &&& lemmaElemEnabled' x op t
-- -- case t of
-- --     [] -> lemmaElemEnabled' x op t
-- --     (h':t') ->
-- --           assert (List.elem' op t)
-- --       &&& (
-- --             allEnabled x ops
-- --         ==. (enabled x h && allEnabled' (apply x h) t)
-- --         *** QED
-- --       )
-- --       &&& assert (enabled x h)
-- --       &&& assert (allEnabled (apply x h) t)
-- --       &&& assert (enabled (apply x h) h')
-- --       &&& lawNonCausal x h h'
-- --       &&& assert (enabled (apply x h') h)
-- --       &&& (
-- --             allEnabled x t
-- --         ==. (enabled x h' && allEnabled (apply x h') t')
-- --         *** QED
-- --       )
-- --       &&& assert (enabled x h')
-- --       &&& assert (allEnabled (apply x h') t')
-- --       &&& assert (allEnabled x t)
-- --       &&& lemmaElemEnabled' x op t
-- 
-- {-@ ple lemmaElemEnabled'' @-}
-- {-@ lemmaElemEnabled'' :: (Eq (Operation a), VRDT a) 
--  => x:a 
--  -> op':Operation a 
--  -> {os:[Operation a] | allEnabled x (cons op' os)} 
--  -> op:Operation a
--  -> {List.elem' op os => enabled (apply x op) op'} 
-- @-}
--  -- -> {op:Operation a | List.elem' op os} 
-- lemmaElemEnabled'' :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> Operation a -> ()
-- lemmaElemEnabled'' x op' ops op | not (List.elem' op ops) = ()
-- lemmaElemEnabled'' x op' [] op = assert (List.elem' op [])
-- lemmaElemEnabled'' x op' ops@(h:t) op
--   | h == op   = 
--         assert (allEnabled x (op':op:t))
--     &&& assert (enabled x op' && allEnabled x (op:t) && allEnabled (apply x op') (op:t))
--     &&& assert (enabled (apply x op') op)
--     &&& lawNonCausal x op' op
--     &&& assert (enabled (apply x op) op') -- GOAL
--   | otherwise =
--         assert (allEnabled x (op':h:t))
--     &&& assert (enabled x op' && allEnabled x (h:t) && allEnabled (apply x op') (h:t))
--     -- &&& assert (enabled (apply x op') h && allEnabled (apply x op') t && allEnabled (apply (apply x op') h) t)
--     &&& assert (List.elem' op t)
--     &&& lemmaElemEnabled'' (apply x op') h t op
--     &&& assert (enabled (apply (apply x op') op) h)
--     -- &&& assert (enabled (apply x op') op)
--     -- &&& lawNonCausal x op' op
--     &&& lawCommutativity x op op'
--     &&& assert (enabled (apply (apply x op) op') h)
--     &&& assert (enabled (apply x op) op') -- GOAL
-- 
-- -- {-@ ple lemmaNonCausal @-}
-- -- {-@ lemmaNonCausal :: VRDT t 
-- --  => x : t 
-- --  -> {op1 : Operation t | enabled x op1} 
-- --  -> {op2 : Operation t | enabled (apply x op1) op2 && enabled (apply x op2) op1} 
-- --  -> {enabled x op2} 
-- -- @-}
-- -- lemmaNonCausal :: VRDT t => t -> Operation t -> Operation t -> ()
-- -- lemmaNonCausal x op1 op2 = lawNonCausal x op1 op2
-- -- 
-- -- (a && b && c) => d
-- -- This doesn't work. How do we go backwards up the enabled chain?
-- 
-- 
-- {-@ ple lemmaAllEnabled @-}
-- {-@ lemmaAllEnabled :: (Eq (Operation a), VRDT a) => x:a -> h:Operation a -> {t:[Operation a] | allEnabled x (cons h t)} -> {allEnabled x t} @-}
-- lemmaAllEnabled :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> ()
-- lemmaAllEnabled x op [] = ()
-- lemmaAllEnabled x op (h:t) = 
--         assert (allEnabled x (op:h:t))
--     &&& (
--         allEnabled x (op:h:t)
--     ==. (enabled x op && allEnabled x (h:t) && allEnabled (apply x op) (h:t))
--     *** QED
--     )
-- 
-- 
-- -- TODO: Precondition doesn't parse.
-- -- -> {op':Operation a | elem op' os && op /= op'}
-- 
-- {-@ ple lemmaElemEnabled @-}
-- {-@ lemmaElemEnabled :: (Eq (Operation a), VRDT a) 
--  => x:a 
--  -> {os:[Operation a] | allEnabled x os} 
--  -> op:Operation a
--  -> op':Operation a
--  -> {(List.elem' op os && List.elem' op' os && op /= op') => enabled (apply x op) op'}
-- @-}
-- lemmaElemEnabled :: (Eq (Operation a), VRDT a) => a -> [Operation a] -> Operation a -> Operation a -> ()
-- lemmaElemEnabled x os op op' | not (List.elem' op os && List.elem' op' os && op /= op') = ()
-- lemmaElemEnabled x [] op op' = () -- unreachable
-- --   assert (elem op []) &&&
-- --   (   elem op []
-- --   ==. False
-- --   *** QED
-- --   )
-- lemmaElemEnabled x (o:os) op op'
--   | o == op   = () -- TODO XXX
--   | o == op'  = -- lemmaElemEnabled x os op op'
--         (
--         allEnabled x (o:os)
--     ==. (enabled x o && allEnabled x os && allEnabled (apply x o) os)
--     *** QED
--     )
--     &&& assert (allEnabled (apply x op') os) 
--     &&& assert (allEnabled (apply x op') os) 
--     -- &&& lawNonCausal x op op'
--     -- &&& lemmaAllEnabled' (apply x o) os op'
--     &&& lemmaElemEnabled'' x op' os op
--     &&& assert (enabled (apply x op) op') -- GOAL
-- 
--   | otherwise = lemmaElemEnabled x os op op'
-- -- lemmaElemEnabled x os op op' = case removeFirst op os of
-- --   Nothing -> () -- unreachable
-- --   Just os' -> 
-- 
-- {-@ reflect cons @-}
-- cons :: a -> [a] -> [a]
-- cons a as = a:as
-- 
-- -- TODO: This is a tc parse error:
-- -- {-@ lemmaRemoveFirstApplied :: (Eq (Operation a), VRDT a) => x:a -> op:Operation a -> {os:[Operation a] | allEnabled x os} -> {rs:[Operation a] | removeFirst op os == Just rs} -> {applyAll x (op:rs) = applyAll x os} @-}
-- {-@ ple lemmaRemoveFirstApplied @-}
-- {-@ lemmaRemoveFirstApplied :: (Eq (Operation a), VRDT a) 
--  => x:a 
--  -> op:Operation a 
--  -> {os:[Operation a] | allEnabled x os} 
--  -> {rs:[Operation a] | removeFirst op os == Just rs} 
--  -> {applyAll x (cons op rs) = applyAll x os}
-- @-}
-- lemmaRemoveFirstApplied :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> [Operation a] -> ()
-- lemmaRemoveFirstApplied x op [] _  = ()
-- lemmaRemoveFirstApplied x op (op':os') rs | op == op' = ()
-- lemmaRemoveFirstApplied x op os@(op':os') rs = case removeFirst op os' of
--   Nothing -> ()
--   Just rs' ->
--         applyAll x (op:rs)
--     ==. applyAll (apply x op) rs
--         ?   lemmaRemoveFirstNeq op op' os' rs rs'
--     ==. applyAll (apply x op) (op':rs')
--     ==. applyAll (apply (apply x op) op') rs' 
--         ?   lemmaRemoveFirstEnabled' x op os rs
--         &&& assert (enabled x op)
--         &&& assert (enabled x op')
--         &&& lemmaRemoveFirstElem op os rs
--         &&& assert (List.elem' op os)
--         &&& assert (List.elem' op' os)
--         &&& lemmaElemEnabled x os op' op
--         &&& assert (enabled (apply x op') op)
--         &&& lemmaElemEnabled x os op op'
--         &&& assert (enabled (apply x op) op')
--         &&& lawCommutativity x op op'
--     ==. applyAll (apply (apply x op') op) rs'
--     ==. applyAll (apply x op') (op:rs')
--         ?   lemmaRemoveFirstApplied (apply x op') op os' rs'
--     ==. applyAll (apply x op') os'
--     ==. applyAll x (op':os')
--     ==. applyAll x os
--     *** QED
-- 
-- 
-- -- TODO: LH can't see this precondition?
-- --  -> {op':Operation a | op /= op'} 
-- 
-- {-@ ple lemmaRemoveFirstNeq @-}
-- {-@ lemmaRemoveFirstNeq :: Eq (Operation a) 
--  => op:Operation a 
--  -> op':Operation a
--  -> os':[Operation a] 
--  -> {rs:[Operation a] | removeFirst op (cons op' os') = Just rs} 
--  -> {rs':[Operation a] | (removeFirst op os') = (Just rs')} 
--  -> {op /= op' => rs = (cons op' rs')} @-}
-- lemmaRemoveFirstNeq :: Eq (Operation a) => Operation a -> Operation a -> [Operation a] -> [Operation a] -> [Operation a] -> ()
-- lemmaRemoveFirstNeq op op' os' rs rs' | op == op' = () -- assert (op == op') -- &&& assert (op /= op')
-- lemmaRemoveFirstNeq op op' os' rs rs' = 
--   -- case removeFirst op (op':os') of
--   --   Nothing -> ()
--   --   Just _rs ->
--   --     assert (rs == _rs) &&&
--   --     case removeFirst op os' of
--   --       Nothing -> ()
--   --       Just _rs' ->
--   --         assert (_rs' == rs') &&&
--   --         assert (op /= op') &&&
--           (   Just rs
--           ==. removeFirst op (op':os')
--           ==. Just (op':rs')
--           *** QED
--           )
-- 
-- 
-- 
