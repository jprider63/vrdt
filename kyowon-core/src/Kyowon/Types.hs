module Kyowon.Types (
    module Kyowon.Types
  , ClientId(..)
  ) where

import           Data.Aeson (ToJSON, FromJSON)
import qualified Data.Aeson as Aeson
import           Data.Binary (Binary)
import qualified Data.Binary as Binary
import           Data.ByteString.Lazy (ByteString)
import qualified Data.ByteString as BS
import           Data.Serialize (Serialize)
import qualified Data.Serialize as Serialize
import           Data.Text (Text)
import           GHC.Generics (Generic)
import qualified Servant as Servant

import           VRDT.Types (ClientId(..))

-- TODO: 
-- Implement a typeclass that generates a unique AppId from a `Proxy a`.
-- Move most types to this module.
-- Create `Store` typeclass.

-- -- | Client's UUID.
-- -- 128 randomly generated bits. Should be printed as Base64Url encoded.
-- -- newtype ClientId = ClientId BS.ByteString deriving (Eq, Ord, Show, Generic) -- XXX ip addr?
-- newtype ClientId = ClientId Text deriving (Eq, Ord, Show, Generic) -- XXX ip addr?
-- 
-- instance Aeson.ToJSON ClientId
-- instance Aeson.FromJSON ClientId



-- TODO: extensions to reduce overcommunication:
--
--  1. identify each update with a client-generated uuid
--
--      * XXX: consider placing the new UpdateId directly in AppData
--
--  2. persist updates in both client and server
--  3. send a bloom-filter of persisted updates' uuids for those..
--
--      a. ..stored at client to the server, and
--      b. ..stored at server to the client
--
--  4. change server to filter its backlog dump of updates to exclude those the client has
--
--      * when sending the backlog, the server shouldn't filter out the ClientId of the recipient
--      * when sending the live updates, the server should filter out the ClientId of the recipient
--      
--  5. change client to send what it has when requested, excluding those in the server's bloom-filter
--
--      * XXX: should the client be trusted to resend updates which came from a different client?
--      * XXX: (correspondingly) should the server's bloom-filter only include updates from the client it's requested resends from?
--      * XXX: how can we use hashes, signatures, or encryption to validate resends? do we care?

newtype AppData
    = AppData ByteString
    deriving
    (Show, Eq, Ord, Generic)
instance Serialize AppData

-- newtype ClientId
--     = ClientId UUID
--     deriving
--     (Show, Eq, Ord, Generic)
-- instance ToJSON ClientId
-- instance FromJSON ClientId
instance Serialize ClientId

newtype StoreId
    = StoreId Text
    deriving
    (Show, Eq, Ord, Generic)
instance ToJSON StoreId
instance FromJSON StoreId
instance Servant.ToHttpApiData StoreId where toUrlPiece (StoreId t) = t
instance Servant.FromHttpApiData StoreId where parseUrlPiece = pure . StoreId

-- | A message sent by the server to a client.
--
-- XXX: what would a ClientMessage look like? It would have a
-- RequestResendUpdates, but its Update constructor would likely not have
-- ClientId unless we trust a client to resend anothers' updates
data ServerMessage
    = Update ClientId AppData -- sender and update
    | RequestResendUpdates -- TODO bloom-filter of entries the server already has
    deriving
    (Show, Eq, Ord, Generic)
instance Serialize ServerMessage

-- | All instances of 'Binary' are instances of 'Serialize'.
instance {-# OVERLAPPABLE #-} Binary a => Serialize a where
    put = Serialize.put <$> Binary.encode
    get = Binary.decode <$> Serialize.get

-- | All instances of 'Serialize' are instances of
-- 'Servant.MimeRender Servant.OctetStream'.
instance Serialize a => Servant.MimeRender Servant.OctetStream a where
    mimeRender _ = Serialize.encodeLazy
-- | All instances of 'Serialize' are instances of
-- 'Servant.MimeUnrender Servant.OctetStream'.
instance Serialize a => Servant.MimeUnrender Servant.OctetStream a where
    mimeUnrender _ = Serialize.decodeLazy
