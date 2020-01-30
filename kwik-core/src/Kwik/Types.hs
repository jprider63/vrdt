module Kwik.Types where

import qualified Data.ByteString as BS

-- TODO: 
-- Implement a typeclass that generates a unique AppId from a `Proxy a`.
-- Move most types to this module.
-- Create `Store` typeclass.

-- | Client's UUID.
-- 128 randomly generated bits. Should be printed as Base64Url encoded.
newtype ClientId = ClientId BS.ByteString deriving (Eq, Ord)


