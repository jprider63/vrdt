module Kyowon.Reflex.Common where

import           Control.Applicative (liftA2)
import           Reflex


zipEvents a b = do
    dynA <- holdDyn Nothing (Just <$> a)
    dynB <- holdDyn Nothing (Just <$> b)
    pure $ fmapMaybe id $ updated $ (liftA2 . liftA2) (,) dynA dynB

runOnLoad m = do
    builtE <- getPostBuild
    performEvent $ ffor builtE $ \() -> m

runOnLoad_ m = do
    builtE <- getPostBuild
    performEvent_ $ ffor builtE $ \() -> m

