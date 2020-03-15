module Kyowon.Core.Types.Internal where

import           Data.Aeson (FromJSON(..), ToJSON(..), (.=), (.:))

newtype NextId = NextId Integer
    deriving (Eq, Ord)

zeroNextId :: NextId
zeroNextId = NextId 0


instance ToJSON NextId where
    toJSON (NextId n) = toJSON n

instance FromJSON NextId where
    parseJSON v = NextId <$> parseJSON v

