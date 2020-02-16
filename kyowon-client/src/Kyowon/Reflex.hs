-- JP: Should maybe be in a different package.
module Kyowon.Reflex where

import           Control.Applicative (liftA2)
import           Control.Concurrent (Chan, readChan, writeChan, newChan, forkIO)
import           Control.Monad (void)
import           Control.Monad.IO.Class (MonadIO(..))
import qualified Data.Aeson as Aeson
import           Reflex (
                    Event
                  , Dynamic
                  , MonadHold
                  , Performable
                  , PerformEvent
                  , PostBuild
                  , Reflex
                  , ffor
                  , fmapMaybe
                  , getPostBuild
                  , holdDyn
                  , newTriggerEvent
                  , TriggerEvent
                  , performEvent
                  , performEvent_
                  , updated
                  )

import           Kyowon.Client (StoreRef(..))
import qualified Kyowon.Client as Client
import           VRDT.Class (VRDT(..))
import           VRDT.Types (ClientId(..))


-- loadStore :: IO (StoreRef a, a)
-- createStore :: Client.Server -> Proxy a -> IO (StoreRef a)
--     FilePath to store local state?

connectToStore :: (Aeson.FromJSON (Operation a), Aeson.ToJSON (Operation a), VRDT a, Reflex t, MonadHold t m, MonadIO (Performable m), PostBuild t m, TriggerEvent t m, PerformEvent t m)
               => StoreRef a -> a -> Event t (Operation a) -> m (Dynamic t a)
connectToStore storeRef init opsE = do
    (cE, cCallback) <- newTriggerEvent

    -- performEvent_ $ ffor opsE $ \op -> liftIO $ 
    --     print $ unMax op

    -- Create channel (once).
    opChanE <- runOnLoad $ liftIO newChan
    opChanOpesE <- zipEvents opChanE opsE
    performEvent_ $ ffor opChanOpesE $ \(opChan, op) -> liftIO $ do
        writeChan opChan $ Left op

    performEvent_ $ ffor opChanE $ \opChan -> liftIO $ void $ forkIO $ do
      Client.withRaw
        (storeRefServer storeRef)-- "http://127.0.0.1:3000") 
        (Just $ storeRefStore storeRef) -- Client.StoreId "TODO") 
        (ClientId "TODO") -- TODO: grab from a reader monad
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
        cCallback st'

        -- Loop.
        run st' opChan cCallback client

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

