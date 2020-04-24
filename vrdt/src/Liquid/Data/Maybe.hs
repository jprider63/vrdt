{-@ LIQUID "--reflection" @-}

module Liquid.Data.Maybe where 

import Prelude hiding (Maybe(..))

data Maybe a = Just a | Nothing 
  deriving (Eq, Ord)

{-@ measure isJust @-}
isJust :: Maybe a -> Bool 
isJust (Just _) = True 
isJust _        = False 
