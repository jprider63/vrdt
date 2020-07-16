
module Main where

import           Control.Monad.Fix (MonadFix(..))
import           Control.Monad.IO.Class (MonadIO(..))
import           Control.Monad.Trans.Class (lift)
import           Data.Time.Calendar (Day(..))
import           Data.Time.Clock (UTCTime(..))
import qualified Data.UUID as UUID
import qualified Graphics.Vty as V
import qualified Kyowon.Client as Client
import           Kyowon.Core.Types ( UTCTimestamp(..)
                                   , zeroNextId
                                   , ClientId(..)
                                   , createClient)
import qualified Kyowon.Reflex.Client as Reflex
import           Kyowon.Reflex.Client (KyowonMonad)
import           Kyowon.Reflex.VRDT.CausalTree (CausalTreeInput(..), causalTreeInput)
import           Kyowon.Reflex.Vty.Widget (mainWidget)
import           Reflex.Vty ( input
                            , Adjustable
                            , MonadHold
                            , MonadNodeId
                            , NotReady
                            , Performable
                            , PerformEvent
                            , PostBuild
                            , TriggerEvent
                            , VtyWidget)
import           Reflex.Class (Reflex, fforMaybe)
import           VRDT.CausalTree (CausalTree)
import qualified VRDT.CausalTree as CT
import           VRDT.Class (VRDT(..), VRDTInitial(..))

type Widget t m a = (Reflex t, MonadHold t m, MonadFix m, Adjustable t m, NotReady t m, PostBuild t m, MonadNodeId m, TriggerEvent t m, PerformEvent t m, MonadIO (Performable m), PostBuild t m, MonadIO m, KyowonMonad m, KyowonMonad (Performable m)) => VtyWidget t m a
type State = CausalTree UTCTimestamp Char
type StateOp = Operation State

main :: IO ()
main = do
  -- TODO: Load these from the file system.
  clientId <- createClient
  let nextId = zeroNextId
  mainWidget clientId nextId $ do
    inp <- input
    app
    return $ fforMaybe inp $ \case
      V.EvKey (V.KChar 'c') [V.MCtrl] -> Just ()
      _ -> Nothing

app :: Widget t m ()
app = mdo
  st <- lift $ Reflex.connectToStore' storeRef initVRDT $ (:[]) <$> causalTreeInputOperations cti

  cti <- causalTreeInput st

  return ()


  where
    storeRef = Reflex.StoreRef (Client.Server "http://ent.jamesparker.me:3001") (Client.StoreId "TODO")




-- TODO: What should the init id be?
instance VRDTInitial (CausalTree UTCTimestamp a) where
    initVRDT = CT.CausalTree (CT.CausalTreeWeave (CT.CausalTreeAtom initId CT.CausalTreeLetterRoot) []) mempty
      where
        initId = UTCTimestamp (UTCTime (ModifiedJulianDay 0) 0) (ClientId $ UUID.nil)
    
