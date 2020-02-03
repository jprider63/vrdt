
module VRDT.Types where

import           Data.ByteString (ByteString)
import qualified Data.ByteString as BS

{-@
data ClientId = ClientId {
    rawClientId :: {v : ByteString | BS.length v == 16}
  }
@-}
data ClientId = ClientId {
    rawClientId :: ByteString -- 128 bits
  }
    deriving (Eq, Ord)

-- | Randomly generate a `ClientId`.
generateClientId :: m ClientId
generateClientId = undefined -- TODO XXX
