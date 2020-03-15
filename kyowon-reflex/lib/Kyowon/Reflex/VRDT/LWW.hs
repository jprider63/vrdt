module Kyowon.Reflex.VRDT.LWW where

import           Control.Monad.IO.Class (MonadIO)
import           Kyowon.Core.Types (UTCTimestamp(..), ClientId)
import           Reflex (Dynamic, Performable, PostBuild, MonadHold, PerformEvent)
import           VRDT.LWW (LWW(..))

import           Kyowon.Reflex.Time

toLWW' :: (MonadIO m, MonadIO (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m)
       => ClientId -> Dynamic t (Maybe a) -> m (Dynamic t (Maybe (LWW UTCTimestamp a)))
toLWW' cId = sampleMonotonicTimeWith (\a t -> LWW (UTCTimestamp t cId) <$> a)

