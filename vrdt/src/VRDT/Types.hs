
module VRDT.Types where

import           Crypto.Random (createEntropyPool, cprgCreate, cprgGenerate, SystemRNG)
import           Data.Aeson (FromJSON(..), ToJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS
import qualified Data.ByteString.Base64.URL as B64U
import qualified Data.Text.Encoding as Text
import           Data.Time.Clock (UTCTime)
import           GHC.Generics (Generic)


{-@
data ClientId = ClientId {
    rawClientId :: {v : ByteString | BS.length v == 16}
  }
@-}
data ClientId = ClientId {
    rawClientId :: ByteString -- 128 bits
  }
    deriving (Show, Eq, Ord, Generic)

instance FromJSON ClientId where
    parseJSON = Aeson.withText "ClientId" $ either fail (return . ClientId) . B64U.decode . Text.encodeUtf8 
instance ToJSON ClientId where
    toJSON (ClientId c) = toJSON $ Text.decodeUtf8 $ B64U.encode c


-- | Randomly generate a `ClientId`.
generateClientId :: IO ClientId
generateClientId = do
    rng <- cprgCreate @SystemRNG <$> createEntropyPool -- TODO: grab from reader monad? Should we use cryptonite instead? We don't need the rest of the crypto functionality...
    let (cId, _rng) = cprgGenerate 16 rng
    return $ ClientId cId

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

