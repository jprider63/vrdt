{-# LANGUAGE TypeOperators #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Liquid.Data.List where 

import Prelude hiding (concat, reverse)

-- type List a = [a]

-- data List a = a : List a | []

{-@ reflect elem' @-}
elem' :: Eq a => a -> [a] -> Bool
elem' x [] = False
elem' x (h:t) 
  | x == h    = True
  | otherwise = elem' x t

-- {-@ length' :: ls:[a] -> {v:Int | v = length ls} @-}
{-@ reflect length' @-}
length' :: [a] -> Int
length' [] = 0
length' (h:t) = 1 + length' t

{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse [] = []
reverse (h:t) = concat (reverse t) [h]

{-@ reflect concat @-}
concat :: [a] -> [a] -> [a]
concat [] l = l
concat (h:t) l = h:(concat t l)

