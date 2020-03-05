
module VRDT.Types where

-- TODO: Delete this module?
-- import           Data.Aeson (FromJSON(..), ToJSON(..), (.=), (.:))
-- import qualified Data.Aeson as Aeson
-- import           Data.ByteString (ByteString)
-- import qualified Data.ByteString as BS
-- import qualified Data.ByteString.Base64.URL as B64U
-- import qualified Data.Text.Encoding as Text
-- import           Data.Time.Clock (UTCTime)
-- 
-- 
-- {-@
-- data ClientId = ClientId {
--     rawClientId :: {v : ByteString | BS.length v == 16}
--   }
-- @-}
-- data ClientId = ClientId {
--     rawClientId :: ByteString -- 128 bits
--   }
--   deriving (Show, Eq, Ord)
-- 
-- instance FromJSON ClientId where
--     parseJSON = Aeson.withText "ClientId" $ either fail (return . ClientId) . B64U.decode . Text.encodeUtf8 
-- instance ToJSON ClientId where
--     toJSON (ClientId c) = toJSON $ Text.decodeUtf8 $ B64U.encode c

