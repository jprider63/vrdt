{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module DemoApp where

import Data.String (fromString)
import GHC.Generics (Generic)
import qualified Crdtoa.Application as App

data ChatMessage = ChatMessage
    { handle :: String
    , message :: String
    } deriving (Generic, App.Serialize)

-- | A demo application (barebones chat)
main :: String -> Maybe String -> IO ()
main server requestStore = do
    putStrLn "What is your name? "
    name <- getLine
    putStrLn "Type and press enter at any time. Say 'quit' to exit."
    App.withSer
        (App.Server server)
        (App.StoreId . fromString <$> requestStore)
        Nothing
        (App.Recv $ either
            (\e -> putStrLn $ "Serialization error: " <> e)
            (\m -> putStrLn $ "[" <> handle m <> "]: " <> message m))
        $ \client -> do
            putStrLn $ "Connected to store " <> show (App.store client)
            chat client ChatMessage{handle=name, message=""}
  where
    chat client state = do
        line <- getLine
        case line of
            "quit" -> putStrLn "Shutting down.."
            "" -> chat client state
            _ -> do
                App.send client state{message=line}
                chat client state
