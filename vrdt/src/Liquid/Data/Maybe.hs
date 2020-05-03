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
