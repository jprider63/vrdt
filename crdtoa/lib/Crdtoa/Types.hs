-- {-# LANGUAGE GeneralizedNewtypeDeriving #-} -- to derive instances for newtypes
{-# LANGUAGE DeriveGeneric #-} -- to leverage instances derivable from generics
{-# LANGUAGE MultiParamTypeClasses #-} -- to define instances of Mime(Un)Render
{-# LANGUAGE FlexibleInstances #-} -- to define all Binary to be Serialize
{-# LANGUAGE UndecidableInstances #-} -- to define all Serialize to be Mime(Un)Render OctetStream
{-# OPTIONS_GHC -Wno-orphans #-} -- to define overlapping instances Binary->Serialize->Mime(Un)Render
module Crdtoa.Types where

import Data.Aeson (ToJSON, FromJSON)
import Data.Binary (Binary)
import Data.ByteString.Lazy (ByteString)
import Data.Serialize (Serialize)
import Data.Text (Text)
import Data.UUID.Types (UUID)
import GHC.Generics (Generic)
import qualified Data.Binary as Binary hiding (Binary)
import qualified Data.Serialize as Serialize hiding (Serialize)
import qualified Servant as Servant

-- | TODO: extensions to reduce overcommunication:
--
--  1. identify each update with a client-generated uuid
--
--      * ??? consider placing the new UpdateId directly in AppData
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
--      * ??? should the client be trusted to resend updates which came from a different client?
--      * ??? (correspondingly) should the server's bloom-filter only include updates from the client it's requested resends from?
--      * ??? how can we use hashes, signatures, or encryption to validate resends? do we care?

newtype AppData
    = AppData ByteString
    deriving
    (Show, Eq, Ord, Generic)
instance Serialize AppData

newtype ClientId
    = ClientId UUID
    deriving
    (Show, Eq, Ord, Generic)
instance ToJSON ClientId
instance FromJSON ClientId
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
-- ??? what would a ClientMessage look like? It would have a
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
