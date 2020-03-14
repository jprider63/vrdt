module Kyowon.Reflex.VRDT.LWW where

import           Control.Monad.IO.Class (MonadIO)
import           Kyowon.Core.Types (UTCTimestamp(..), ClientId)
import           Reflex (Event, Performable, PostBuild, MonadHold, PerformEvent)
import           VRDT.LWW (LWW(..))

import           Kyowon.Reflex.Time

toLWW' :: (MonadIO (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m)
       => ClientId -> Event t a -> m (Event t (LWW UTCTimestamp a))
toLWW' cId = sampleMonotonicTimeWith (\a t -> LWW (UTCTimestamp t cId) a)

