{-# LANGUAGE LambdaCase #-}
module Crdtoa where

import System.Environment (getArgs, getProgName)
import Text.Printf (printf)

import qualified Crdtoa.Application as Application
import qualified Crdtoa.Server as Server

main :: IO ()
main = getArgs >>= \case
    ["app", port] -> Application.main $ read port
    ["application", port] -> Application.main $ read port
    ["server", port] -> Server.main $ read port
    _ -> do
        name <- getProgName
        putStrLn $ unlines
            [ printf "Usage: %s (application | server[ port-num])" name
            , "    Include server or demo app mode argument."
            ]
