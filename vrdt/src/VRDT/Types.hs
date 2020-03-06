
module VRDT.Types
( ClientId, createClient
, UTCTimestamp(..)
) where

import           Data.Aeson (FromJSON(..), ToJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64.URL as B64U
import qualified Data.Text.Encoding as Text
import           Data.Time.Clock (UTCTime)
import           Kyowon.Core.Types (ClientId, createClient)

data UTCTimestamp = UTCTimestamp UTCTime ClientId
    deriving (Eq, Ord)

instance FromJSON UTCTimestamp where
    parseJSON = Aeson.withObject "UTCTimestamp" $ \o -> 
        UTCTimestamp <$> o .: "t" <*> o .: "c"

instance ToJSON UTCTimestamp where
    toJSON (UTCTimestamp t c) = Aeson.object [
        "t" .= t
      , "c" .= c
      ]

