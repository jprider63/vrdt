module Kyowon.Client.Log where

import Data.Time (getCurrentTime)
import Text.Printf (hPrintf)
import qualified System.IO as IO

data LogLevel = DEBUG | INFO | WARNING | ERROR deriving Show

-- | TODO: in the future return a log configuration and require it to emit a
-- log message
setupLogger :: IO ()
setupLogger = do
    IO.hSetBuffering IO.stderr IO.LineBuffering

-- | Slow logger.
slowLog :: LogLevel -> String -> IO ()
slowLog level message = do
    -- t <- getCurrentTime
    -- hPrintf IO.stderr "[%s, %s] %s\n" (show t) (show level) message
    return ()
