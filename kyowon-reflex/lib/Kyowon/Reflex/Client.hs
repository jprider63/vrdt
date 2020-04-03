{-# LANGUAGE UndecidableInstances #-}

module Kyowon.Reflex.Client (
    StoreRef(..)
  , connectToStore
  , connectToStore'
  , runKyowonT
  , KyowonT
  , KyowonMonad(..)
  , NextId
  , zeroNextId
  ) where

import           Control.Concurrent (readChan, writeChan, newChan, forkIO)
import           Control.Monad (void)
import           Control.Monad.Fix (MonadFix(..))
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.NodeId (MonadNodeId(..))
import           Control.Monad.Trans.Class (MonadTrans(..))
import           Control.Monad.Trans.Reader (ReaderT(..), runReaderT, ask)
import           Control.Monad.Ref (MonadRef(..))
import qualified Data.Aeson as Aeson
import           Data.IORef (IORef, newIORef, atomicModifyIORef)
import           Data.Time.Clock (UTCTime, getCurrentTime, addUTCTime)
import           Reflex (
                    Adjustable(..)
                  , Event
                  , Dynamic
                  , MonadHold(..)
                  , MonadSample(..)
                  , Performable
                  , PerformEvent(..)
                  , PostBuild(..)
                  , Reflex
                  , ffor
                  -- , fmapMaybe
                  -- , getPostBuild
                  , holdDyn
                  , newTriggerEvent
                  , NotReady(..)
                  , TriggerEvent(..)
                  -- , performEvent
                  , performEvent_
                  -- , updated
                  )

import qualified Kyowon.Client as Client
import           Kyowon.Core.Types (ClientId)
import           Kyowon.Core.Types.Internal (NextId(..), zeroNextId)
import           VRDT.Class (VRDT(..))

import           Kyowon.Reflex.Common

data StoreRef a = StoreRef
    { storeRefServer :: Client.Server
    , storeRefStore  :: Client.StoreId
    }

-- loadStore :: IO (StoreRef a, a)
-- createStore :: Client.Server -> Proxy a -> IO (StoreRef a)
--     FilePath to store local state?

connectToStore :: (Aeson.FromJSON (Operation a), Aeson.ToJSON (Operation a), VRDT a, Reflex t, MonadHold t m, MonadIO m, MonadIO (Performable m), PostBuild t m, TriggerEvent t m, PerformEvent t m)
               => StoreRef a -> a -> Event t (Operation a) -> m (Dynamic t a)
connectToStore storeRef init opsE = connectToStore' storeRef init $ fmap (:[]) opsE

connectToStore' :: (Aeson.FromJSON (Operation a), Aeson.ToJSON (Operation a), VRDT a, Reflex t, MonadHold t m, MonadIO m, MonadIO (Performable m), PostBuild t m, TriggerEvent t m, PerformEvent t m, Foldable l)
               => StoreRef a -> a -> Event t (l (Operation a)) -> m (Dynamic t a)
connectToStore' storeRef init opsE = do
    (cE, cCallback) <- newTriggerEvent

    -- performEvent_ $ ffor opsE $ \op -> liftIO $ 
    --     print $ unMax op

    -- Create channel (once).
    opChan <- liftIO newChan
    performEvent_ $ ffor opsE $ \ops -> liftIO $ do
        mapM_ (writeChan opChan . Left) ops

    liftIO $ void $ forkIO $ do
      Client.withRaw
        (storeRefServer storeRef)-- "http://127.0.0.1:3000") 
        (Just $ storeRefStore storeRef) -- Client.StoreId "TODO") 
        Nothing
        (Client.Recv $ \(Client.AppData bs) -> do
            case Aeson.decode bs of
                Nothing -> 
                    error "TODO"
                Just op -> 
                    writeChan opChan $ Right op
          ) 
        $ run init opChan cCallback

    holdDyn init cE
  
  where
    -- init = Max 0 -- TODO

    -- run :: Max Integer -> Chan (Either (Max Integer) (Max Integer)) -> (Max Integer -> IO ()) -> Client.Client Client.AppData -> IO ()
    run st opChan cCallback client = do
        -- Wait for operations.
        opE <- readChan opChan
        
        op <- case opE of 
              Left op -> do
                -- Send operation over network.
                let serialized = Client.AppData $ Aeson.encode op
                Client.send client serialized

                return op
              Right op ->
                -- Don't send back over the network. 
                return op
          
        -- Update state.
        let st' = apply st op
        _ <- cCallback st'

        -- Loop.
        run st' opChan cCallback client


class KyowonMonad m where
    -- | Get (and increment) next unique id.
    getNextId :: m NextId

    -- | Get the client id.
    getClientId :: m ClientId

    -- | Get the current time monotonically.
    -- The time will be greater than any time previously returned.
    getMonotonicTime :: m UTCTime

data KyowonState = KyowonState {
    kyowonStateClient     :: ClientId
  , kyowonStateNextId     :: IORef NextId
  , kyowonStateLatestTime :: IORef UTCTime
  }

newtype KyowonT m a = KyowonT {unKyowonT :: ReaderT KyowonState m a}
-- JP: I think we need to use IORef's instead of StateT since the monadic computation is only run on initialization.

runKyowonT :: MonadIO m => ClientId -> NextId -> KyowonT m a -> m a
runKyowonT clientId nextId (KyowonT m) = do
    nextIdRef <- liftIO $ newIORef nextId
    latestTimeRef <- liftIO $ getCurrentTime >>= newIORef

    let s = KyowonState clientId nextIdRef latestTimeRef
    runReaderT m s

instance Functor m => Functor (KyowonT m) where
    fmap f (KyowonT m) = KyowonT $ fmap f m

instance Applicative m => Applicative (KyowonT m) where
    pure = KyowonT . pure
    KyowonT f <*> KyowonT m = KyowonT $ f <*> m

instance Monad m => Monad (KyowonT m) where
    KyowonT m >>= n = KyowonT $ m >>= (unKyowonT . n)

instance MonadIO m => MonadIO (KyowonT m) where
    liftIO m = KyowonT $ liftIO m

instance MonadIO m => KyowonMonad (KyowonT m) where
    getNextId = do
        nextRef <- kyowonStateNextId <$> KyowonT ask
        liftIO $ atomicModifyIORef nextRef $ \n0@(NextId n) ->
            let n' = NextId $ n + 1 in
            (n0, n')

    getClientId = kyowonStateClient <$> KyowonT ask

    getMonotonicTime = do
        latestRef <- kyowonStateLatestTime <$> KyowonT ask

        now <- liftIO getCurrentTime

        liftIO $ atomicModifyIORef latestRef $ \latest -> 
            -- Add a picosecond to the latest time if time went backwards.
            let res = if now > latest then now else addUTCTime 1e-12 latest in
            (res, res)

-- getNextUTCTimestamp :: KyowonMonad m => m UTCTimestamp
-- getNextUTCTimestamp =
--     UTCTimestamp <$> getMonotonicTime <*> getClientId

instance MonadRef m => MonadRef (KyowonT m) where
    type Ref (KyowonT m) = Ref m

    newRef = KyowonT . newRef
    
    readRef = KyowonT . readRef

    writeRef r = KyowonT . writeRef r

instance MonadNodeId m => MonadNodeId (KyowonT m) where
    getNextNodeId = KyowonT getNextNodeId

instance MonadSample t m => MonadSample t (KyowonT m) where
    sample = KyowonT . sample

instance MonadHold t m => MonadHold t (KyowonT m) where
    buildDynamic p e = KyowonT $ buildDynamic p e
    headE e = KyowonT $ headE e

instance MonadTrans KyowonT where
    lift = KyowonT . lift

instance MonadFix m => MonadFix (KyowonT m) where
    mfix m = KyowonT $ mfix $ \a -> unKyowonT $ m a

instance NotReady t m => NotReady t (KyowonT m) where
    notReadyUntil = KyowonT . notReadyUntil
    notReady = KyowonT notReady
    
instance TriggerEvent t m => TriggerEvent t (KyowonT m) where
    newTriggerEvent = KyowonT newTriggerEvent
    newTriggerEventWithOnComplete = KyowonT newTriggerEventWithOnComplete
    newEventWithLazyTriggerWithOnComplete = KyowonT . newEventWithLazyTriggerWithOnComplete

instance PostBuild t m => PostBuild t (KyowonT m) where
    getPostBuild = KyowonT getPostBuild

-- http://hackage.haskell.org/package/reflex-0.6.2.4/docs/src/Reflex.PerformEvent.Class.html#line-56
instance PerformEvent t m => PerformEvent t (KyowonT m) where
    type Performable (KyowonT m) = KyowonT (Performable m)

    performEvent_ e = do
      r <- KyowonT ask
      lift $ performEvent_ $ (\m -> runReaderT (unKyowonT m) r) <$> e
    performEvent e = do
      r <- KyowonT ask
      lift $ performEvent $ (\m -> runReaderT (unKyowonT m) r) <$> e


-- https://hackage.haskell.org/package/reflex-0.6.4/docs/src/Reflex.Adjustable.Class.html#line-89
instance Adjustable t m => Adjustable t (KyowonT m) where
    runWithReplace a0 a' = do
        r <- KyowonT ask
        lift $ runWithReplace (runReaderT (unKyowonT a0) r) $ fmap (\m -> runReaderT (unKyowonT m) r) a'

    traverseIntMapWithKeyWithAdjust f dm0 dm' = do
        r <- KyowonT ask
        lift $ traverseIntMapWithKeyWithAdjust (\k v -> runReaderT (unKyowonT $ f k v) r) dm0 dm'

    traverseDMapWithKeyWithAdjust f dm0 dm' = do
        r <- KyowonT ask
        lift $ traverseDMapWithKeyWithAdjust (\k v -> runReaderT (unKyowonT $ f k v) r) dm0 dm'
    traverseDMapWithKeyWithAdjustWithMove f dm0 dm' = do
        r <- KyowonT ask
        lift $ traverseDMapWithKeyWithAdjustWithMove (\k v -> runReaderT (unKyowonT $ f k v) r) dm0 dm'

