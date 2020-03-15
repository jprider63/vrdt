module Kyowon.Reflex.Time where

import           Control.Monad.IO.Class (liftIO, MonadIO(..))
import           Data.IORef
import           Data.Time.Clock
import           Reflex

import           Kyowon.Reflex.Common

sampleMonotonicTime :: (MonadIO m, MonadIO (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m) 
                    => Dynamic t () -> m (Dynamic t UTCTime)
sampleMonotonicTime t = fmap snd <$> zipSampleMonotonicTime (() <$ t)


-- | A dynamic that samples the current time monotonically. 
-- The time will be greater than any time previously sampled.
zipSampleMonotonicTime :: forall t m a . (MonadIO m, MonadIO (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m) 
                       => Dynamic t a -> m (Dynamic t (a,UTCTime))
zipSampleMonotonicTime tickD = do
    initTime <- liftIO getCurrentTime

    -- Create IORef with initial time (once).
    latestTick <- liftIO $ newIORef initTime
    
    nowE <- performEvent $ ffor (updated tickD) $ \_ -> liftIO $ do
        latest <- readIORef latestTick
        now <- getCurrentTime

        -- Add a picosecond to the latest time if time went backwards.
        let res = if now > latest then now else addUTCTime 1e-12 latest

        writeIORef latestTick res

        return res

    nowD <- holdDyn initTime nowE

    return ((,) <$> tickD <*> nowD)


    -- JP: Can we use `accum` so that we don't need to use IORef?
    -- now <- liftIO $ getCurrentTime

    -- accum () now tickE

sampleMonotonicTimeWith :: (MonadIO m, MonadIO (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m) 
                        => (a -> UTCTime -> b) -> Dynamic t a -> m (Dynamic t b)
sampleMonotonicTimeWith f e = fmap (\(a, t) -> f a t) <$> zipSampleMonotonicTime e

    

