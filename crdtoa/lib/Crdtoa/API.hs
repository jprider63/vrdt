{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}
module Crdtoa.API where

--import Web.HttpApiData (FromHttpApiData)
import Data.ByteString.Lazy (ByteString)
import Data.Map (Map)
import Data.Text (Text)
import GHC.Generics (Generic)
import Servant -- XXX all names unqualified
import qualified Data.Aeson as Aeson

-- XXX for generating URIs elsewhere, might want to not distribute over the v0,v1 prefixes
type API
    = "strm" :> ReqBody '[JSON] [String] :> StreamPost NewlineFraming JSON (SourceIO String)
    :<|> "v0" :> (CreateV0 :<|> SendV0 :<|> ListenV0)
--  :<|> "v1" :> (CreateV1 :<|> SendV1 :<|> ListenV1)
--  :<|> "v2" :> (CreateV2 :<|> SendV2 :<|> ListenV2)

type CreateV0 = "create" :> Capture "app-name" AppName :> Post '[JSON] StoreId
-- | The purpose of the app-name is to prevent two different apps from possibly
-- poisoning each others logs with messages that cannot be understood.
-- ... can we use this with namespaced uuids?
-- ... why not just use random uuids and forego app-name?
-- ... should app-name be provided in send or listen?
type CreateV1 = CreateV0
type CreateV2 = CreateV1

type SendV0 = "send" :> Capture "store-id" StoreId :> ReqBody '[OctetStream] AppData             :> Post '[JSON] NoContent
-- | V1 includes log-index so the server can store it at the right offset.
type SendV1 = "send" :> Capture "store-id" StoreId :> ReqBody '[OctetStream] (LogIndex, AppData) :> Post '[JSON] NoContent
type SendV2 = SendV1

type ListenV0 = "listen" :> Capture "store-id" StoreId                                             :> StreamPost NewlineFraming OctetStream (SourceIO AppData)
-- | V1 includes a log-offset for each client so the server can return only those portions of the logs which the client lacks.
type ListenV1 = "listen" :> Capture "store-id" StoreId :> ReqBody '[JSON] (Map ClientId LogOffset) :> StreamPost NewlineFraming OctetStream (SourceIO AppData)
-- | V2 includes the ability for the server to request specific log entries from clients.
type ListenV2 = "listen" :> Capture "store-id" StoreId :> ReqBody '[JSON] (Map ClientId LogOffset) :> StreamPost NewlineFraming OctetStream (SourceIO ServerMessage)

newtype AppName = AppName Text
newtype StoreId = StoreId Text deriving Generic
newtype AppData = AppData ByteString deriving Generic

instance FromHttpApiData AppName where parseUrlPiece = pure . AppName
instance ToHttpApiData AppName where toUrlPiece (AppName t) = t

instance Aeson.FromJSON StoreId
instance Aeson.ToJSON StoreId
instance FromHttpApiData StoreId where parseUrlPiece = pure . StoreId
instance ToHttpApiData StoreId where toUrlPiece (StoreId t) = t

-- FIXME: instead of this, look up how to use serializable and define a
-- typeclass instance so all serializable are mimeRender/Unrender to
-- OctetStream
instance Servant.MimeRender Servant.OctetStream AppData where mimeRender _ (AppData bs) = bs
instance Servant.MimeUnrender Servant.OctetStream AppData where mimeUnrender _ = pure . AppData

newtype ClientId = ClientId String -- XXX ip addr?
newtype LogIndex = LogIndex Int
newtype LogOffset = LogOffset Int

data ServerMessage
    = OpaqueAppData AppData
    | RequestLogEntries [LogIndex]
