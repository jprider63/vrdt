module Kyowon.Reflex.VRDT.LWW where

import           Kyowon.Core.Types (UTCTimestamp(..), ClientId)
import           Reflex (Dynamic, Performable, PostBuild, MonadHold, PerformEvent)
import           VRDT.LWW (LWW(..))

import           Kyowon.Reflex.Client (KyowonMonad(..))
import           Kyowon.Reflex.Time (sampleMonotonicTimeWith)

toLWW' :: (KyowonMonad m, KyowonMonad (Performable m), PostBuild t m, MonadHold t m, PerformEvent t m)
       => ClientId -> Dynamic t (Maybe a) -> m (Dynamic t (Maybe (LWW UTCTimestamp a)))
toLWW' cId = sampleMonotonicTimeWith (\a t -> LWW (UTCTimestamp t cId) <$> a)

