{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module Main where

import Data.String (fromString)
import GHC.Generics (Generic)
import System.Environment (getArgs, getProgName)
import Text.Printf (printf)

import qualified Kyowon.Client as Cli

main :: IO ()
main = getArgs >>= \argv -> case argv of
    [server, store] -> app server (Just store)
    [server] -> app server Nothing
    _ -> do
        name <- getProgName
        putStrLn $ unlines
            [ printf "USAGE: %s server-url [store-id]" name
            , "Start the demo with a URL and an optional store name."
            ]


data ChatMessage = ChatMessage
    { handle :: String
    , message :: String
    } deriving (Generic, Cli.Serialize)

-- | A demo application (barebones chat)
app :: String -> Maybe String -> IO ()
app server requestStore = do
    putStrLn "What is your name? "
    name <- getLine
    putStrLn "Type and press enter at any time. Say 'quit' to exit."
    Cli.withSer
        (Cli.Server server)
        (Cli.StoreId . fromString <$> requestStore)
        Nothing
        (Cli.Recv $ either
            (\e -> putStrLn $ "Serialization error: " <> e)
            (\m -> putStrLn $ "[" <> handle m <> "]: " <> message m))
        $ \client -> do
            putStrLn $ "Connected to store " <> show (Cli.store client)
            chat client name
  where
    chat client handle = do
        line <- getLine
        case line of
            "quit" -> putStrLn "Shutting down.."
            "" -> chat client handle
            _ -> do
                Cli.send client ChatMessage{handle=handle, message=line}
                chat client handle
