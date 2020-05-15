{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.LWW where

#ifdef NotLiquid
import           Data.Aeson (FromJSON(..), ToJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
#endif

import           VRDT.Class
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

-- type LWWU a = LWW UTCTimestamp a

#ifdef NotLiquid
instance (FromJSON t, FromJSON a) => FromJSON (LWW t a) where
    parseJSON = Aeson.withObject "LWW" $ \o -> 
        LWW <$> o .: "time" <*> o .: "value"

instance (ToJSON t, ToJSON a) => ToJSON (LWW t a) where
    toJSON (LWW t a) = Aeson.object [
        "time" .= t
      , "value" .= a
      ]
#endif

instance Ord t => VRDT (LWW t a) where
  type Operation (LWW t a) = LWW t a
  apply l1 l2
    | lwwTime l1 > lwwTime l2 = l1
    | otherwise = l2
  compatible l1 l2 = lwwTime l1 /= lwwTime l2
  compatibleState l1 l2 = lwwTime l1 /= lwwTime l2
  lawCommutativity x y z = ()
  lawCompatibilityCommutativity _ _ = ()
