module Kyowon.Reflex.Time where

import           Control.Monad.IO.Class (liftIO, MonadIO(..))
import           Data.IORef
import           Data.Time.Clock
import           Reflex

import           Kyowon.Reflex.Common

-- | An event that samples the current time monotonically. 
-- The time will be greater than any time previously sampled.
sampleMonotonicTime :: (MonadIO (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m) 
                    => Event t () -> m (Event t UTCTime)
sampleMonotonicTime tickE = do

    -- Create IORef with initial time (once).
    latestTickE <- runOnLoad $ liftIO $ 
        getCurrentTime >>= newIORef
    mergedE <- zipEvents latestTickE tickE
    
    performEvent $ ffor mergedE $ \(latestTick, ()) -> liftIO $ do
        latest <- readIORef latestTick
        now <- getCurrentTime

        -- Add a picosecond to the latest time if time went backwards.
        let res = if now > latest then now else addUTCTime 1e-12 latest

        writeIORef latestTick res

        return res


    -- JP: Can we use `accum` so that we don't need to use IORef?
    -- now <- liftIO $ getCurrentTime

    -- accum () now tickE

