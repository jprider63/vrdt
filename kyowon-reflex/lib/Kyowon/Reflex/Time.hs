module Kyowon.Reflex.Time where

import           Data.Time.Clock (UTCTime)
import           Reflex

import           Kyowon.Reflex.Client (KyowonMonad(..))

sampleMonotonicTime :: (KyowonMonad m, KyowonMonad (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m) 
                    => Dynamic t () -> m (Dynamic t UTCTime)
sampleMonotonicTime t = fmap snd <$> zipSampleMonotonicTime (() <$ t)


-- | A dynamic that samples the current time monotonically. 
-- The time will be greater than any time previously sampled.
zipSampleMonotonicTime :: forall t m a . (KyowonMonad m, KyowonMonad (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m) 
                       => Dynamic t a -> m (Dynamic t (a,UTCTime))
zipSampleMonotonicTime tickD = do
    initTime <- getMonotonicTime

    nowE <- performEvent $ ffor (updated tickD) $ \_ -> getMonotonicTime
    nowD <- holdDyn initTime nowE

    return ((,) <$> tickD <*> nowD)

    -- JP: Can we use `accum` so that we don't need to use IORef?
    -- now <- liftIO $ getCurrentTime

    -- accum () now tickE


zipSampleMonotonicTime' :: (PerformEvent t m, KyowonMonad (Performable m)) => Event t a -> m (Event t (a, UTCTime))
zipSampleMonotonicTime' tickE = do
    performEvent $ ffor tickE $ \tick -> do
        now <- getMonotonicTime
        return (tick, now)

sampleMonotonicTimeWith :: (KyowonMonad m, KyowonMonad (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m) 
                        => (a -> UTCTime -> b) -> Dynamic t a -> m (Dynamic t b)
sampleMonotonicTimeWith f e = fmap (uncurry f) <$> zipSampleMonotonicTime e

sampleMonotonicTimeWith' :: (PerformEvent t f, KyowonMonad (Performable f)) => (a -> UTCTime -> b) -> Event t a -> f (Event t b)
sampleMonotonicTimeWith' f e = fmap (uncurry f) <$> zipSampleMonotonicTime' e
    

