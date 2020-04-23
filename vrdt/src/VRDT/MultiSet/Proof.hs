{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local"  @-}
{-# LANGUAGE RecordWildCards #-}

module VRDT.MultiSet.Proof where

import qualified Liquid.Data.Map as Map
import           Liquid.Data.Maybe
import           Liquid.Data.Map.Props
-- import           Liquid.ProofCombinators
import           Prelude hiding ((++), Maybe(..))
import           VRDT.MultiSet (MultiSet(..), MultiSetOp(..), enabled, apply, multiSetOpOrder)
-- import qualified VRDT.MultiSet as MS
{-@ infix   ++ @-}

import Language.Haskell.Liquid.ProofCombinators

-- | Denotational representation of a MultiSet.
type DMultiSet a = (a -> Integer)

{-@ simulation :: x:MultiSet a 
               -> op:{MultiSetOp a | enabled x op} 
               -> t:a 
               -> { toDenotation (apply x op) t == dApply (toDenotation x) op t } 
               / [multiSetOpOrder op] @-}
simulation :: Ord a => MultiSet a -> MultiSetOp a -> a ->  ()

simulation x@(MultiSet p n) op@(MultiSetOpAdd e c) t 
  | Just c' <- Map.lookup e p 
  =   dApply (toDenotation x) op t
  === (if t == e then (toDenotation x t) + c else toDenotation x t) 
  === toDenotation x t + (if t == e then c else 0)  
      ? lemmaLookupInsert  p e (c' + c)
      ? lemmaLookupDelete  p e 
      ? lemmaLookupInsert  n e (c' + c)
      ? lemmaLookupDelete2 p t e 
      ? lemmaLookupInsert2 p t e (c' + c)
      ? lemmaLookupInsert2 n t e (c' + c)
  === toDenotation (if c'+c > 0 then MultiSet (Map.insert e (c'+c) p) n else MultiSet (Map.delete e p) (Map.insert e (c'+c) n)) t
  === toDenotation (apply x op) t 
  *** QED


simulation x@(MultiSet p n) op@(MultiSetOpAdd e c) t 
  | Just c' <- Map.lookup e n 
  =   dApply (toDenotation x) op t
  === (if t == e then (toDenotation x t) + c else toDenotation x t) 
  === toDenotation x t + (if t == e then c else 0)  
      ? lemmaLookupInsert  p e (c' + c)
      ? lemmaLookupDelete  n e 
      ? lemmaLookupInsert  n e (c' + c)
      ? lemmaLookupDelete2 n t e 
      ? lemmaLookupInsert2 p t e (c' + c)
      ? lemmaLookupInsert2 n t e (c' + c)
  === toDenotation (if c'+c > 0 then MultiSet (Map.insert e (c'+c) p) (Map.delete e n) else MultiSet p (Map.insert e (c'+c) n)) t
  === toDenotation (apply x op) t 
  *** QED

simulation x@(MultiSet p n) op@(MultiSetOpAdd e c) t 
  =   dApply (toDenotation x) op t
  === (if t == e then (toDenotation x t) + c else toDenotation x t) 
  === toDenotation x t + (if t == e then c else 0)  
      ? lemmaLookupInsert  p e c
      ? lemmaLookupInsert  n e c
      ? lemmaLookupInsert2 p t e c
      ? lemmaLookupInsert2 n t e c
  === toDenotation (if c > 0 then MultiSet (Map.insert e c p) n else MultiSet p (Map.insert e c n)) t
  === toDenotation (apply x op) t 
  *** QED


simulation x op@(MultiSetOpRemove e c) t 
  =   toDenotation (apply x (MultiSetOpRemove e c)) t 
  === toDenotation (apply x (MultiSetOpAdd e (-c))) t 
       ? enabled x (MultiSetOpAdd e (-c))
       ? simulation x (MultiSetOpAdd e (-c)) t 
  === dApply (toDenotation x) (MultiSetOpAdd e (-c)) t
      ? lemmaDApply (toDenotation x) e c t
  === dApply (toDenotation x) (MultiSetOpRemove e c) t 
  *** QED 





{-@ reflect toDenotation @-}
toDenotation :: Eq a => MultiSet a -> a -> Integer
toDenotation (MultiSet p n) t 
  | Just v <-  Map.lookup t p 
  = v 
toDenotation (MultiSet p n) t 
  | Just v <- Map.lookup t n 
  = v 
toDenotation _ _ 
  = 0 



{-@ reflect dApply @-}
dApply :: Eq a => (a -> Integer) -> MultiSetOp a -> a -> Integer
dApply f (MultiSetOpRemove v c) t 
  = if t == v then f t - c else f t
dApply f (MultiSetOpAdd v c) t 
  = if t == v then f t + c else f t

{-@ ple lemmaDApply @-}
{-@ lemmaDApply 
      :: f:(a -> Integer) 
      -> v:a -> c:Integer -> t:a 
      -> {dApply f (MultiSetOpRemove v c) t == dApply f (MultiSetOpAdd v (-c)) t} @-}
lemmaDApply :: Eq a => (a -> Integer) -> a -> Integer -> a -> () 
lemmaDApply _ _ _ _ = ()

