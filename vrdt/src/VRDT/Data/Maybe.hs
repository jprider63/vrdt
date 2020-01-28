{-@ LIQUID "--reflection" @-}

module Data.Maybe where 

import Prelude hiding (Maybe(..))

data Maybe a = Just a | Nothing 
