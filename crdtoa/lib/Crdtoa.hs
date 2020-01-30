{-# LANGUAGE LambdaCase #-}
module Crdtoa where

import System.Environment (getArgs, getProgName)
import Text.Printf (printf)

import qualified Crdtoa.Server as Server
import qualified DemoApp as DemoApp

main :: IO ()
main = getArgs >>= \case
    ["app", server, store] -> DemoApp.main server (Just store)
    ["app", server] -> DemoApp.main server Nothing
    ["server", port] -> Server.main $ read port
    _ -> do
        name <- getProgName
        putStrLn $ unlines
            [ printf "Server usage: %s server PORT-NUM" name
            , printf "Demo usage: %s app SERVER-URL [STORE-ID]" name
            , "    Include mode argument 'server' or 'app' and associated arguments."
            ]
