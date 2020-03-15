module Main where

import           Control.Monad
import           Control.Monad.Fix
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import qualified Data.Aeson as Aeson
import           Data.Bifunctor
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Time.Clock (UTCTime, getCurrentTime)
import           Data.Time.Format (parseTimeM, defaultTimeLocale)
import           GHC.Generics
import qualified Graphics.Vty as V
import           Reflex hiding (apply, Event)
import qualified Reflex
import           Reflex.Network
import           Reflex.Vty hiding (apply, Event)

import qualified Kyowon.Client as Client
import qualified Kyowon.Reflex.Client as Reflex
import qualified Kyowon.Reflex.VRDT.LWW as Reflex
import           Kyowon.Core.Types (UTCTimestamp(..), ClientId, createClient)
import           VRDT.Class
import           VRDT.Class.TH
import           VRDT.LWW (LWW(..))
import qualified VRDT.LWW as LWW
-- import           VRDT.MultiSet (MultiSet(..))
import           VRDT.TwoPMap (TwoPMap(..), TwoPMapOp(..))
import qualified VRDT.TwoPMap
import qualified VRDT.Types as VRDT

type LWWU a = LWW UTCTimestamp a
type Widget t m a = (Reflex t, MonadHold t m, MonadFix m, Adjustable t m, NotReady t m, PostBuild t m, MonadNodeId m, TriggerEvent t m, PerformEvent t m, MonadIO (Performable m), PostBuild t m, MonadIO m) => VtyWidget t m a


-- State is TwoPMap of EventState

data Event = Event {
    eventTitle :: LWWU Text
  , eventDescription :: LWWU Text
  , eventStartTime :: LWWU UTCTime
  , eventEndTime :: LWWU UTCTime
  , eventLocation :: LWWU Text
  -- , eventGuests :: MultiSet Text
  -- Messages?
  }
  deriving (Generic)

$(deriveVRDT ''Event)

instance Aeson.ToJSON Event
instance Aeson.FromJSON Event

-- data EventOp = 
--     EventTitleOp (Operation (LWWU Text))
--   | EventDescriptionOp (Operation (LWWU Text))
--   | EventStartTimeOp (Operation (LWWU UTCTime))
--   | EventEndTimeOp (Operation (LWWU UTCTime))
--   | EventLocationOp (Operation (LWWU Text))
--   deriving (Generic)
-- 
-- instance Aeson.ToJSON EventOp
-- instance Aeson.FromJSON EventOp

-- instance VRDT Event where
--     type Operation Event = EventOp
-- 
--     enabled e (EventTitleOp op)       = enabled (eventTitle e) op
--     enabled e (EventDescriptionOp op) = enabled (eventDescription e) op
--     enabled e (EventStartTimeOp op)     = enabled (eventStartTime e) op
--     enabled e (EventEndTimeOp op)       = enabled (eventEndTime e) op
--     enabled e (EventLocationOp op)      = enabled (eventLocation e) op
-- 
--     apply e (EventTitleOp op)       = e {eventTitle = apply (eventTitle e) op}
--     apply e (EventDescriptionOp op) = e {eventDescription = apply (eventDescription e) op}
--     apply e (EventStartTimeOp op)     = e {eventStartTime = apply (eventStartTime e) op}
--     apply e (EventEndTimeOp op)       = e {eventEndTime = apply (eventEndTime e) op}
--     apply e (EventLocationOp op)      = e {eventLocation = apply (eventLocation e) op}
-- 
--     lawCommutativity e (EventTitleOp op1) (EventTitleOp op2)             = lawCommutativity (eventTitle e) op1 op2
--     lawCommutativity e (EventDescriptionOp op1) (EventDescriptionOp op2) = lawCommutativity (eventDescription e) op1 op2
--     lawCommutativity e (EventStartTimeOp op1) (EventStartTimeOp op2)         = lawCommutativity (eventStartTime e) op1 op2
--     lawCommutativity e (EventEndTimeOp op1) (EventEndTimeOp op2)             = lawCommutativity (eventEndTime e) op1 op2
--     lawCommutativity e (EventLocationOp op1) (EventLocationOp op2)           = lawCommutativity (eventLocation e) op1 op2
--     lawCommutativity _ _ _                                               = ()
-- 
--     lawNonCausal e (EventTitleOp op1) (EventTitleOp op2)             = lawNonCausal (eventTitle e) op1 op2
--     lawNonCausal e (EventDescriptionOp op1) (EventDescriptionOp op2) = lawNonCausal (eventDescription e) op1 op2
--     lawNonCausal e (EventStartTimeOp op1) (EventStartTimeOp op2)         = lawNonCausal (eventStartTime e) op1 op2
--     lawNonCausal e (EventEndTimeOp op1) (EventEndTimeOp op2)             = lawNonCausal (eventEndTime e) op1 op2
--     lawNonCausal e (EventLocationOp op1) (EventLocationOp op2)           = lawNonCausal (eventLocation e) op1 op2
--     lawNonCausal _ _ _                                               = ()

instance Ord t => VRDT (LWW t a) where
    type Operation (LWW t a) = LWW t a
    enabled = LWW.enabledLWW
    apply = LWW.applyLWW


main :: IO ()
main = do
  clientId <- createClient
  mainWidget $ do
    now <- liftIO getCurrentTime
    inp <- input
    app clientId now
    return $ fforMaybe inp $ \case
      V.EvKey (V.KChar 'c') [V.MCtrl] -> Just ()
      _ -> Nothing

data View = 
    ViewEvents
  | ViewCreateEvent

app :: ClientId -> UTCTime -> Widget t m ()
app clientId now = do
  -- nav <- tabNavigation
  -- runLayout (pure Orientation_Column) 0 nav $ do
  rec 
      -- e <- lift $ Reflex.connectToStore storeRef initVRDT opsE
      -- let eB = current e

      -- let opsE = (undefined :: Reflex.Event (TwoPMapOp UTCTimestamp Event))


      out <- networkHold events $ ffor (switch (current out)) $ \case
          ViewCreateEvent -> do
            (view, operation) <- createEvent clientId
            return view
          ViewEvents -> events

  return ()


  where
    storeRef = Reflex.StoreRef (Client.Server "http://localhost:3000") (Client.StoreId "TODO")

events :: Widget t m (Reflex.Event t View)
events = col $ do
    createE <- fixed 5 $ textButtonStatic def "Create an event"
    return $ leftmost
        [ ViewCreateEvent <$ createE
        ]
        

createEvent :: forall t m . ClientId -> Widget t m (Reflex.Event t View, Reflex.Event t ())
createEvent clientId = do
  escapedE <- escapePressed
  col $ do
    rec
        title <- validateInput "Title" Right createE >>= toLWW
        description <- validateInput "Description" Right createE >>= toLWW
        startDate <- validateInput "Start Date" dateValidation createE >>= toLWW
        endDate <- validateInput "End Date" dateValidation createE >>= toLWW
        location <- validateInput "Location" Right createE >>= toLWW

        cancelE <- fixed 5 $ textButtonStatic def "Cancel"
        createE <- fixed 5 $ textButtonStatic def "Create event"

    let viewE = leftmost
          [ ViewEvents <$ cancelE
          , ViewEvents <$ escapedE
          -- TODO: send create event
          ]

    let eventM = (liftM5 . liftM5) Event title description startDate endDate location
    let insertE = () <$ createE

    return (viewE, insertE)

  where
    toLWW :: Dynamic t (Maybe a) -> Layout t m (Dynamic t (Maybe (LWW UTCTimestamp a)))
    toLWW = lift . Reflex.toLWW' clientId
        

validateInput label validation e = do
    rec
        let label' = addErr <$> current vE
        fixed 1 $ text label'
        t <- fixed 1 $ textInput def

        -- TODO: holdDyn on e
        let vE = validation <$> _textInput_value t

    return $ either (const Nothing) Just <$> vE

  where
    addErr (Left e) = label <> " (" <> e <> "):"
    addErr _        = label <> ":"

dateValidation :: Text -> Either Text UTCTime
dateValidation = maybe (Left "Invalid date") Right . parseTimeM True defaultTimeLocale "%Y-%-m-%-d %H:%M%p" . Text.unpack
    



escapePressed :: (Reflex t, Monad m, HasVtyInput t m) => m (Reflex.Event t ())
escapePressed = do
  i <- input
  return $ fforMaybe i $ \case
    V.EvKey V.KEsc [] -> Just ()
    _ -> Nothing











-- app' :: (Reflex t, MonadHold t m, MonadFix m, Adjustable t m, NotReady t m, PostBuild t m, MonadNodeId m, TriggerEvent t m, PerformEvent t m, MonadIO (Performable m), PostBuild t m)
--     => ClientId -> UTCTime -> VtyWidget t m ()
-- app' clientId now = do
--   nav <- tabNavigation
--   runLayout (pure Orientation_Column) 0 nav $ do
--     rec 
--         e <- lift $ Reflex.connectToStore storeRef e0 eOpE
--         let eB = current e
--         fixed 1 (text (lwwValue . eventTitle <$> eB))
--         fixed 1 (text (lwwValue . eventDescription <$> eB))
--         fixed 1 (text (lwwValue . eventLocation <$> eB))
-- 
--         locationE <- fixed 1 $ textInput $ def
-- 
--         eOpE <- (fmap EventLocationOp) <$> toLWW (updated (_textInput_value locationE))
-- 
--         -- buildE <- lift getPostBuild
--         -- let eOpE = (EventTitleOp $ l0 "Alice's birthday") <$ buildE
-- 
--     return ()
-- 
--   where
--     toLWW e = return $ l0 <$> e
-- 
-- 
--     storeRef = Reflex.StoreRef (Client.Server "http://localhost:3000") (Client.StoreId "TODO")
-- 
--     e0 = Event (l0 "Alice's birthday") (l0 "Let's celebrate Alice's birthday") (l0 now) (l0 now) (l0 "Someplace secret")
-- 
--     l0 :: a -> LWWU a
--     l0 = LWW (UTCTimestamp now clientId)
-- 
