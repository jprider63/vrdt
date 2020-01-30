{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveAnyClass #-}
module DemoApp where

import Data.String (fromString)
import GHC.Generics (Generic)
import qualified Control.Monad as Mon
import qualified Crdtoa.Application as App

data ChatMessage = ChatMessage
    { handle :: String
    , message :: String
    } deriving (Generic, App.Serialize)

-- | A demo application (barebones chat)
main :: String -> Maybe String -> IO ()
main server requestStore = do
    putStrLn "Chat application demo"
    putStrLn "What is your name? "
    name <- getLine
    putStrLn "Type and press enter at any time. Say 'quit' to exit."
    (store, cancel, App.Send send) <- App.runSer
        (App.Server server)
        (App.StoreId . fromString <$> requestStore)
        (App.Recv $ either
            (\e -> putStrLn $ "Serialization error: " <> e)
            (\m -> putStrLn $ "[" <> handle m <> "]: " <> message m))
    putStrLn $ "Connected to store " <> show store
    Mon.forever $ do
        line <- getLine
        case line of
            "" -> return ()
            "quit" -> putStrLn "Shutting down.." >> cancel
            _ -> send ChatMessage{handle=name, message=line}
