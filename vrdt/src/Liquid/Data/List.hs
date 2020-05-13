{-# LANGUAGE TypeOperators #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module Liquid.Data.List where 

import Prelude hiding (concat, reverse, length)

-- type List a = [a]

-- data List a = a : List a | []

{-@ reflect elem' @-}
elem' :: Eq a => a -> [a] -> Bool
elem' x [] = False
elem' x (h:t) 
  | x == h    = True
  | otherwise = elem' x t

{-@ length :: ls:[a] -> {v:Int | v = len ls} @-}
{-@ measure length @-}
length :: [a] -> Int
length [] = 0
length (h:t) = 1 + length t

{-@ reflect reverse @-}
reverse :: [a] -> [a]
reverse [] = []
reverse (h:t) = concat (reverse t) [h]

{-@ reflect concat @-}
concat :: [a] -> [a] -> [a]
concat [] l = l
concat (h:t) l = h:(concat t l)

{-@ measure tail @-}
{-@ tail :: {x:[a] | length x > 0} -> [a] @-}
tail :: [a] -> [a]
tail (h:l) = l

{-@ measure head @-}
{-@ head :: {x:[a] | length x > 0} -> a @-}
head :: [a] -> a
head (h:l) = h

{-@ reflect empty @-}
empty :: [a]
empty = []
