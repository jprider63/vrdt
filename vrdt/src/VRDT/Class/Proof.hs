{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module VRDT.Class.Proof where


import qualified Liquid.Data.List as List
import           Liquid.ProofCombinators
import           VRDT.Class


-- JP: This definition differs from Shapiro's SEC since order doesn't matter for us.
{-@ ple commutativeStrongEventualConsistency @-}
{-@ commutativeStrongEventualConsistency :: (Eq (Operation a), VRDT a) => s0 : a -> {ops1 : [Operation a] | allEnabled s0 ops1} -> {ops2 : [Operation a] | allEnabled s0 ops2} -> {isPermutation ops1 ops2 => applyAll s0 ops1 = applyAll s0 ops2} @-}
commutativeStrongEventualConsistency :: (Eq (Operation a), VRDT a) => a -> [Operation a] -> [Operation a] -> ()
commutativeStrongEventualConsistency _ [] [] = ()
commutativeStrongEventualConsistency _ _ [] = ()
commutativeStrongEventualConsistency _ [] _ = ()
commutativeStrongEventualConsistency s0 ops1 ops2 | not (isPermutation ops1 ops2) = ()
-- commutativeStrongEventualConsistency s0 ops1@(op1:t1) ops2@(op2:t2) | op1 == op2 = commutativeStrongEventualConsistency (apply s0 op1) t1 t2


-- commutativeStrongEventualConsistency s0 (op1:ops1) (op2:ops2) = ()
commutativeStrongEventualConsistency s0 ops1@(op1:t1) ops2@(op2:t2) = case removeFirst op1 ops2 of
  Nothing -> 
    () -- unreachable
  Just ops2' -> 
  -- case removeFirst op2 ops1 of
  --   Nothing ->
  --     () -- unreachable
  --   Just ops1' ->
        --     commutativeStrongEventualConsistency (apply s0 op1) ops1 ops2
        -- &&& commutativeStrongEventualConsistency (apply s0 op2) ops1 ops2
          applyAll s0 (op1:t1)
      === applyAll (apply s0 op1) t1
            ?   lemmaRemoveFirstEnabled s0 op1 ops2 ops2'
            &&& assert (allEnabled s0 ops2')
            &&& assume (allEnabled (apply s0 op1) ops2') -- TODO XXX
            &&& commutativeStrongEventualConsistency (apply s0 op1) t1 ops2'
      === applyAll (apply s0 op1) ops2'
      === applyAll s0 (op1:ops2')
            ?   lemmaRemoveFirstApplied s0 op1 ops2 ops2'
      === applyAll s0 ops2
      *** QED

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
    -- (h:) <$> removeFirst o t
    case removeFirst o t of
        Nothing -> Nothing
        Just t' -> Just (h:t')





-- {-@ ple lemmaRemoveFirstEnabled @-}
{-@ lemmaRemoveFirstEnabled :: (Eq (Operation a), VRDT a) 
 => x:a 
 -> op:Operation a 
 -> {os:[Operation a] | allEnabled x os} 
 -> {rs:[Operation a] | removeFirst op os == Just rs} 
 -> {allEnabled x rs}
@-}
lemmaRemoveFirstEnabled :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> [Operation a] -> ()
lemmaRemoveFirstEnabled x op os rs = undefined -- TODO XXX

{-@ lemmaRemoveFirstEnabled' :: (Eq (Operation a), VRDT a) 
 => x:a 
 -> op:Operation a 
 -> {os:[Operation a] | allEnabled x os} 
 -> {rs:[Operation a] | removeFirst op os == Just rs} 
 -> {enabled x op}
@-}
lemmaRemoveFirstEnabled' :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> [Operation a] -> ()
lemmaRemoveFirstEnabled' x op os rs = undefined -- TODO XXX

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



-- TODO: Precondition doesn't parse.
-- -> {op':Operation a | elem op' os && op /= op'}

-- {-@ ple lemmaElemEnabled @-}
{-@ lemmaElemEnabled :: (Eq (Operation a), VRDT a) 
 => x:a 
 -> {os:[Operation a] | allEnabled x os} 
 -> op:Operation a
 -> op':Operation a
 -> {(List.elem' op os && List.elem' op' os && op /= op') => enabled (apply x op) op'}
@-}
lemmaElemEnabled :: (Eq (Operation a), VRDT a) => a -> [Operation a] -> Operation a -> Operation a -> ()
lemmaElemEnabled x os op op' | not (List.elem' op os && List.elem' op' os && op /= op') = ()
lemmaElemEnabled x [] op op' = () -- unreachable
--   assert (elem op []) &&&
--   (   elem op []
--   === False
--   *** QED
--   )
lemmaElemEnabled x (o:os) op op' = undefined -- TODO XXX
--   | o == op   = ()
--   | o == op'  = ()
--   | otherwise = ()
-- lemmaElemEnabled x os op op' = case removeFirst op os of
--   Nothing -> () -- unreachable
--   Just os' -> 

{-@ reflect cons @-}
cons :: a -> [a] -> [a]
cons a as = a:as

-- TODO: This is a tc parse error:
-- {-@ lemmaRemoveFirstApplied :: (Eq (Operation a), VRDT a) => x:a -> op:Operation a -> {os:[Operation a] | allEnabled x os} -> {rs:[Operation a] | removeFirst op os == Just rs} -> {applyAll x (op:rs) = applyAll x os} @-}
{-@ ple lemmaRemoveFirstApplied @-}
{-@ lemmaRemoveFirstApplied :: (Eq (Operation a), VRDT a) 
 => x:a 
 -> op:Operation a 
 -> {os:[Operation a] | allEnabled x os} 
 -> {rs:[Operation a] | removeFirst op os == Just rs} 
 -> {applyAll x (cons op rs) = applyAll x os}
@-}
lemmaRemoveFirstApplied :: (Eq (Operation a), VRDT a) => a -> Operation a -> [Operation a] -> [Operation a] -> ()
lemmaRemoveFirstApplied x op [] _  = ()
lemmaRemoveFirstApplied x op (op':os') rs | op == op' = ()
lemmaRemoveFirstApplied x op os@(op':os') rs = case removeFirst op os' of
  Nothing -> ()
  Just rs' ->
        applyAll x (op:rs)
    ==. applyAll (apply x op) rs
        ?   lemmaRemoveFirstNeq op op' os' rs rs'
    ==. applyAll (apply x op) (op':rs')
    ==. applyAll (apply (apply x op) op') rs' 
        ?   lemmaRemoveFirstEnabled' x op os rs
        &&& assert (enabled x op)
        &&& assert (enabled x op')
        &&& lemmaRemoveFirstElem op os rs
        &&& assert (List.elem' op os)
        &&& assert (List.elem' op' os)
        &&& lemmaElemEnabled x os op' op
        &&& assert (enabled (apply x op') op)
        &&& lemmaElemEnabled x os op op'
        &&& assert (enabled (apply x op) op')
        &&& lawCommutativity x op op'
    ==. applyAll (apply (apply x op') op) rs'
    ==. applyAll (apply x op') (op:rs')
        ?   lemmaRemoveFirstApplied (apply x op') op os' rs'
    ==. applyAll (apply x op') os'
    ==. applyAll x (op':os')
    ==. applyAll x os
    *** QED


-- TODO: LH can't see this precondition?
--  -> {op':Operation a | op /= op'} 

{-@ ple lemmaRemoveFirstNeq @-}
{-@ lemmaRemoveFirstNeq :: Eq (Operation a) 
 => op:Operation a 
 -> op':Operation a
 -> os':[Operation a] 
 -> {rs:[Operation a] | removeFirst op (cons op' os') = Just rs} 
 -> {rs':[Operation a] | (removeFirst op os') = (Just rs')} 
 -> {op /= op' => rs = (cons op' rs')} @-}
lemmaRemoveFirstNeq :: Eq (Operation a) => Operation a -> Operation a -> [Operation a] -> [Operation a] -> [Operation a] -> ()
lemmaRemoveFirstNeq op op' os' rs rs' | op == op' = () -- assert (op == op') -- &&& assert (op /= op')
lemmaRemoveFirstNeq op op' os' rs rs' = 
  -- case removeFirst op (op':os') of
  --   Nothing -> ()
  --   Just _rs ->
  --     assert (rs == _rs) &&&
  --     case removeFirst op os' of
  --       Nothing -> ()
  --       Just _rs' ->
  --         assert (_rs' == rs') &&&
  --         assert (op /= op') &&&
          (   Just rs
          ==. removeFirst op (op':os')
          ==. Just (op':rs')
          *** QED
          )



