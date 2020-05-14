{-@ LIQUID "--reflection" @-}

module Liquid.Data.Maybe where 

import Prelude hiding (Maybe(..))

data Maybe a = Just a | Nothing 
  deriving (Eq, Ord)

{-@ measure isJust @-}
isJust :: Maybe a -> Bool 
isJust (Just _) = True 
isJust _        = False 

{-@ reflect maybe @-}
maybe :: b -> (a -> b) -> Maybe a -> b
maybe d _ Nothing  = d
maybe _ f (Just v) = f v

{-@ measure fromJust @-}
{-@ fromJust :: vv:{Maybe a | isJust vv} -> a @-}
fromJust :: Maybe a -> a
fromJust (Just a) = a

{-@ reflect concat @-}
concat :: Maybe [a] -> [a]
concat Nothing = []
concat (Just xs) = xs

