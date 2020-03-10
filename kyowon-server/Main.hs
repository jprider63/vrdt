module Main where

import Data.Maybe (isJust)
import System.Environment (getArgs, getProgName)
import Text.Printf (printf)
import Text.Read (readMaybe)

import qualified Kyowon.Server as Server

main :: IO ()
main = getArgs >>= \argv -> case argv of
    [port] | isJust (readMaybe port :: Maybe Int)
        -> Server.main $ read port
    _
        -> do
        name <- getProgName
        putStrLn $ unlines
            [ printf "USAGE: %s port-num" name
            ]
