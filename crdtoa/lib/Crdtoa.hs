{-# LANGUAGE LambdaCase #-}
module Crdtoa where

import Data.String (fromString)
import System.Environment (getArgs, getProgName)
import Text.Printf (printf)

import qualified Crdtoa.API as API
import qualified Crdtoa.Application as Application
import qualified Crdtoa.Server as Server

main :: IO ()
main = getArgs >>= \case
    ["app", server, store] -> Application.main (Application.Server server) (API.StoreId $ fromString store)
    ["server", port] -> Server.main $ read port
    _ -> do
        name <- getProgName
        putStrLn $ unlines
            [ printf "Server usage: %s server PORT-NUM" name
            , printf "Demo usage: %s app SERVER-URL STORE-ID" name
            , "    Include mode argument 'server' or 'app' and associated arguments."
            ]
