module Kyowon.Reflex.Next where

import           Reflex

import           Kyowon.Reflex.Client (KyowonMonad(..), NextId)

zipNextId :: (KyowonMonad (Performable m), PerformEvent t m) => Event t a -> m (Event t (a, NextId))
zipNextId e = performEvent $ ffor e $ \a -> do
    nextId <- getNextId
    return (a, nextId)

nextIdWith :: (KyowonMonad (Performable m), PerformEvent t m) => (a -> NextId -> b) -> Event t a -> m (Event t b)
nextIdWith f e = fmap (uncurry f) <$> zipNextId e

