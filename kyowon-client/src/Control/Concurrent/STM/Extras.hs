module Control.Concurrent.STM.Extras where

import Control.Concurrent.STM (STM)
import qualified Control.Concurrent.STM as STM hiding (STM)

-- * Preemptable sleep

type Wakeup = STM.TVar (STM.TVar Bool)

newWakeupIO :: IO Wakeup
newWakeupIO = STM.newTVarIO =<< STM.newTVarIO True

-- | Reset the alarm to some seconds in the future and go to sleep. If there
-- are other sleepers, their wakeups are all pushed out to the same duration
-- from now.
sleepSec :: Wakeup -> Float -> IO ()
sleepSec w sec = do
    -- Put a new TVar False, which turns True after a delay, in the outer TVar.
    STM.atomically . STM.writeTVar w =<< STM.registerDelay (round $ sec * 1e6)
    -- Check from the outer TVar until the inner TVar False becomes True.
    STM.atomically $ STM.check =<< STM.readTVar =<< STM.readTVar w

-- | Wake up all threads sleeping on this value.
wakeup :: Wakeup -> STM ()
wakeup w = (`STM.writeTVar` True) =<< STM.readTVar w

-- * Modify TMVar

-- | Take, apply, and put. The user function may modify the contents and/or
-- return a digest value. This will block when empty.
modifyTMVar :: STM.TMVar a -> (a -> STM (a, b)) -> STM b
modifyTMVar v f = do
    (a, b) <- f =<< STM.takeTMVar v
    STM.putTMVar v a
    return b

-- | Take, apply, and put. The user function may only modify the contents. This
-- will block when empty.
modifyTMVar_ :: STM.TMVar a -> (a -> STM a) -> STM ()
modifyTMVar_ v f = STM.putTMVar v =<< f =<< STM.takeTMVar v

-- | Take, apply, and put. The user function may only return a digest value.
-- This will block when empty.
queryTMVar :: STM.TMVar a -> (a -> STM b) -> STM b
queryTMVar v f = STM.readTMVar v >>= f
