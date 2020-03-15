module Kyowon.Reflex.Common where

import           Control.Applicative (liftA2)
import           Reflex

zipEvents :: (Reflex t, MonadHold t m) => Event t a -> Event t b -> m (Event t (a, b))
zipEvents a b = do
    dynA <- holdDyn Nothing (Just <$> a)
    dynB <- holdDyn Nothing (Just <$> b)
    pure $ fmapMaybe id $ updated $ (liftA2 . liftA2) (,) dynA dynB

runOnLoad :: (PostBuild t m, PerformEvent t m) => Performable m a -> m (Event t a)
runOnLoad m = do
    builtE <- getPostBuild
    performEvent $ ffor builtE $ \() -> m

runOnLoad_ :: (PostBuild t m, PerformEvent t m) => Performable m () -> m ()
runOnLoad_ m = do
    builtE <- getPostBuild
    performEvent_ $ ffor builtE $ \() -> m

