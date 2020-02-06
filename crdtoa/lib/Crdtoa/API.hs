{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Crdtoa.API
( module Crdtoa.API
, module Crdtoa.Types
) where

import Crdtoa.Types -- XXX all names unqualified
import Servant -- XXX all names unqualified

-- XXX for generating URIs elsewhere, might want to not distribute over the v0,v1 prefixes
type API
    =    "v0" :> (CreateV0 :<|> SendV0 :<|> ListenV0 :<|> StreamV0)

type CreateV0 = "create"
    :> Post '[JSON] StoreId

type SendV0 = "send"
    :> Capture "store-id" StoreId
    :> ReqBody '[OctetStream] AppData
    :> Post '[JSON] NoContent

type ListenV0 = "listen"
    :> Capture "store-id" StoreId
    :> StreamPost NoFraming OctetStream (SourceIO AppData)

type StreamV0 = "stream"
    :> Capture "store-id" StoreId
    :> ReqBody '[JSON] ClientId
    :> StreamBody NoFraming OctetStream UpStream
    :> StreamPost NoFraming OctetStream DownStream

type UpStream = SourceIO AppData
type DownStream = SourceIO ServerMessage
