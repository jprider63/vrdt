module Crdtoa.Log where

import Data.Time (getCurrentTime)
import System.IO (stderr)
import Text.Printf (hPrintf)

data LogLevel = DEBUG | INFO | WARNING | ERROR deriving Show

-- | Slow logger.
slowLog :: LogLevel -> String -> IO ()
slowLog level message = do
    t <- getCurrentTime
    hPrintf stderr "[%s, %s] %s\n" (show t) (show level) message
