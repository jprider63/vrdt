{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.Class.Proof where

import VRDT.Class


-- JP: This definition differs from Shapiro's SEC since order doesn't matter for us.
{-@ commutativeStrongEventualConsistency :: (Eq (Operation a), VRDT a) => s0 : a -> {ops1 : [Operation a] | allEnabled s0 ops1} -> {ops2 : [Operation a] | allEnabled s0 ops2} -> {isPermutation ops1 ops2 => applyAll s0 ops1 = applyAll s0 ops2} @-}
commutativeStrongEventualConsistency :: (Eq (Operation a), VRDT a) => a -> [Operation a] -> [Operation a] -> ()
commutativeStrongEventualConsistency _ _ _ = ()

{-@ reflect allEnabled @-}
allEnabled :: VRDT a => a -> [Operation a] -> Bool
allEnabled _  []       = True
allEnabled s0 (op:ops) = enabled s0 op && allEnabled (apply s0 op) ops

{-@ reflect applyAll @-}
applyAll :: VRDT a => a -> [Operation a] -> a
applyAll s []       = s
applyAll s (op:ops) = applyAll (apply s op) ops

{-@ reflect isPermutation @-}
isPermutation :: Eq o => [o] -> [o] -> Bool
isPermutation []    []    = True
isPermutation (_:_) []    = False
isPermutation []    (_:_) = False
isPermutation (op1:ops1') ops2 = case removeFirst op1 ops2 of
    Nothing -> False
    Just ops2' -> isPermutation ops1' ops2'

{-@ reflect removeFirst @-}
removeFirst :: Eq o => o -> [o] -> Maybe [o]
removeFirst o [] = Nothing
removeFirst o (h:t) = 
  if h == o then 
    Just t 
  else 
    (h:) <$> removeFirst o t

