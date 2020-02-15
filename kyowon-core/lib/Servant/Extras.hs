{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# OPTIONS_GHC -Wno-orphans #-} -- to define ToSourceIO for base & stm channels
module Servant.Extras where

import qualified Control.Concurrent.Chan as Chan
import qualified Control.Concurrent.STM as STM
import qualified Servant.API as Servant
import qualified Servant.Types.SourceT as SourceT

-- | General pattern applicable also for chan, tchan, tqueue, tqueue, ...
toStepT :: IO a -> SourceT.StepT IO a
toStepT get = SourceT.Effect $ SourceT.Yield <$> get <*> pure (toStepT get)
{-# INLINE toStepT #-}

toSourceT :: IO a -> Servant.SourceIO a
toSourceT = SourceT.fromStepT . toStepT
{-# INLINE toSourceT #-}

instance Servant.ToSourceIO a (Chan.Chan a) where
    toSourceIO = toSourceT . Chan.readChan

instance Servant.ToSourceIO a (STM.TChan a) where
    toSourceIO = toSourceT . STM.atomically . STM.readTChan

instance Servant.ToSourceIO a (STM.TQueue a) where
    toSourceIO = toSourceT . STM.atomically . STM.readTQueue

instance Servant.ToSourceIO a (STM.TBQueue a) where
    toSourceIO = toSourceT . STM.atomically . STM.readTBQueue

-- | Interlace an effect into each 'SourceT.StepT' in a stream.
--
-- >>> import Control.Monad.Except (runExceptT)
-- >>> import Servant.Types.SourceT (runSourceT, mapStepT, source, fromStepT, StepT(..))
-- >>> run = runExceptT . runSourceT
-- >>> run . mapStepT (interlaceStepT print) . fromStepT $ Stop
-- Right []
-- >>> run . mapStepT (interlaceStepT print) . fromStepT $ Error "oops"
-- Left "oops"
-- >>> run . mapStepT (interlaceStepT print) . fromStepT $ Skip Stop
-- Nothing
-- Right []
-- >>> run . mapStepT (interlaceStepT print) . fromStepT $ Effect (print 123 >> return Stop)
-- 123
-- Nothing
-- Right []
-- >>> run . mapStepT (interlaceStepT print) . source $ [1..4]
-- Just 1
-- Just 2
-- Just 3
-- Just 4
-- Right [1,2,3,4]
interlaceStepT :: Monad m => (Maybe a -> m ()) -> SourceT.StepT m a -> SourceT.StepT m a
interlaceStepT action step = case step of
    SourceT.Stop -> step
    SourceT.Error _ -> step
    SourceT.Skip next -> SourceT.Skip $ rec Nothing next
    SourceT.Yield item next -> SourceT.Yield item $ rec (Just item) next
    SourceT.Effect genNext -> SourceT.Effect $ genNext >>= return . rec Nothing
  where
    -- run our effect and inject interlace into the continuation
    rec item next = SourceT.Effect $ do
        action item
        return $ interlaceStepT action next
