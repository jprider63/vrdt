module VRDT.MultiSet.Proof where

import qualified Data.Map as Map

import           VRDT.MultiSet (MultiSet(..), MultiSetOp(..))
-- import qualified VRDT.MultiSet as MS

-- | Denotational representation of a MultiSet.
newtype DMultiSet a = DMultiSet (a -> Integer)


{-@ simulation :: {x:MultiSet a} -> {op:MultiSetOp a | enabled x op} -> {toDenotation (apply x op) == dApply (toDenotation x) op)} @-}
simulation :: MultiSet a -> MultiSetOp a -> ()
simulation _ _ = ()

toDenotation :: Eq a => MultiSet a -> DMultiSet a
toDenotation MultiSet{..} = DMultiSet $ helper $ Map.toList posMultiSet ++ Map.toList negMultiSet
  where
    helper []         = const 0
    helper ((k,v):vs) = \t -> if k == t then v + helper vs t else helper vs t


dApply :: Eq a => DMultiSet a -> MultiSetOp a -> DMultiSet a
dApply (DMultiSet f) op = 
    let (v, c) = case op of
          MultiSetOpAdd v c -> (v, c)
          MultiSetOpRemove v c -> (v, -c)
    in
    DMultiSet $ \t -> if t == v then c + f t else f t

