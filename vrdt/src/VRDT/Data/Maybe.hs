{-@ LIQUID "--reflection" @-}

module Data.Maybe where 

import Prelude hiding (Maybe(..))

data Maybe a = Just a | Nothing 

{-@ measure isJust @-}
isJust :: Maybe a -> Bool 
isJust (Just _) = True 
isJust _        = False 
