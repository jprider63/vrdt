{-# LANGUAGE DataKinds #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeOperators #-}
module Kyowon.Core.API
( module Kyowon.Core.API
, module Kyowon.Core.Types
) where

import Kyowon.Core.Types -- XXX all names unqualified
import Servant.API -- XXX all names unqualified

-- XXX for generating URIs elsewhere, might want to not distribute over the v0,v1 prefixes
type API
    =    "v0" :> (CreateV0 :<|> SendV0 :<|> ListenV0)

type CreateV0 = "create"
    :> Post '[JSON] StoreId

type SendV0 = "send"
    :> Capture "store-id" StoreId
    :> ReqBody '[OctetStream] (ClientId, AppData)
    :> Post '[JSON] NoContent
-- TODO: instead of a tuple, define an Update type to match ServerMessage(Update)

type ListenV0 = "listen"
    :> Capture "store-id" StoreId
    :> ReqBody '[OctetStream] ClientId
    :> StreamPost NetstringFraming OctetStream ServerStream

type ServerStream = SourceIO ServerMessage
