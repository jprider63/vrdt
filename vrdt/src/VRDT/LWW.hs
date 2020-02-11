{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple-local" @-}

module VRDT.LWW where

import           Data.Aeson (FromJSON(..), ToJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson

-- import VRDT.Class
import           VRDT.Types

{-@
data LWW t a = LWW {
    lwwTime  :: t
  , lwwValue :: a
  }
@-}
data LWW t a = LWW {
    lwwTime  :: t
  , lwwValue :: a
  }

type LWWU a = LWW UTCTimestamp a

instance (FromJSON t, FromJSON a) => FromJSON (LWW t a) where
    parseJSON = Aeson.withObject "LWW" $ \o -> 
        LWW <$> o .: "time" <*> o .: "value"

instance (ToJSON t, ToJSON a) => ToJSON (LWW t a) where
    toJSON (LWW t a) = Aeson.object [
        "time" .= t
      , "value" .= a
      ]

-- instance Ord t => VRDT (LWW t a) where
--     type Operation (LWW t a) = LWW t a
-- 
--     apply l1@(LWW t1 _) l2@(LWW t2 _) 
--       | t1 > t2   = l1
--       | otherwise = l2
--     
--     lawCommutativity x op1 op2 = ()


{-@ reflect applyLWW @-}
applyLWW :: Ord t => LWW t a -> LWW t a -> LWW t a
applyLWW l1@(LWW t1 _) l2@(LWW t2 _) 
  | t1 > t2   = l1
  | otherwise = l2

{-@ reflect enabledLWW @-}
enabledLWW :: Eq t => LWW t a -> LWW t a -> Bool
enabledLWW (LWW t1 _) (LWW t2 _) = t1 /= t2

{-@ reflect enabled2LWW @-}
enabled2LWW :: Ord t => LWW t a -> LWW t a -> LWW t a -> Bool
enabled2LWW x op1 op2 = enabledLWW x op1 && enabledLWW x op2  && enabledLWW (applyLWW x op1) op2 && enabledLWW (applyLWW x op2) op1

{-@ ple lawCommutativityLWW @-}
{-@ lawCommutativityLWW :: x : LWW t a -> op1 : LWW t a -> op2 : LWW t a -> {enabled2LWW x op1 op2 => applyLWW op2 (applyLWW op1 x) == applyLWW op1 (applyLWW op2 x)} @-}
lawCommutativityLWW :: LWW t a -> LWW t a -> LWW t a -> ()
lawCommutativityLWW lww op1 op2 = ()

