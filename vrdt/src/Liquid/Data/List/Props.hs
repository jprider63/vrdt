{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple"        @-}

module Liquid.Data.List.Props where 
import Prelude hiding (concat, reverse, length, foldr, foldl, foldl', (++))
import Liquid.ProofCombinators
import Liquid.Data.List

{-@ lemmaFoldlConcat ::
     f:(b -> a -> b)
  -> acc:b
  -> xs:[a]
  -> ys:[a]
  -> {foldl' f (L.foldl' f acc xs) ys == foldl' f acc (concat xs ys)} @-}

lemmaFoldlConcat :: (b -> a -> b) -> b -> [a] -> [a] -> ()
lemmaFoldlConcat f acc [] _ = ()
lemmaFoldlConcat f acc (x:xs) ys = lemmaFoldlConcat f (f acc x) xs ys
