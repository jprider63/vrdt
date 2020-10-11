module Types where

import Control.DeepSeq (NFData)
import System.Random

-- class VRDT t => Generator t where
--   type GenSt t = s | s -> t
-- 
--   init :: GenSt t
-- 
--   gen :: RandomGen g => g -> GenSt t -> (GenSt t, Operation t)
  
data Generator t op st = Generator {
    genInit :: !st
  , gen :: forall g . RandomGen g => g -> st -> (g, st, op)
  , initSt :: !t
  , app :: t -> op -> t
}

data LabeledGenerator = forall t op st . (Show t, Show op, NFData st, NFData t, NFData op) => LabeledGenerator {
    label :: String
  , lgen :: Generator t op st
  }

