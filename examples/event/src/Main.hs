module Main where

import           Control.Monad
import           Control.Monad.Fix
import           Control.Monad.IO.Class
import           Control.Monad.Trans.Class
import qualified Data.Aeson as Aeson
import           Data.Bifunctor
import qualified Data.Map as Map
import qualified Data.Maybe as Maybe
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Data.Text.Zipper as Zipper
import           Data.Time.Clock (UTCTime, getCurrentTime)
import           Data.Time.Format (parseTimeM, defaultTimeLocale, formatTime)
import           GHC.Generics
import qualified Graphics.Vty as V
import           Reflex hiding (apply, Event)
import qualified Reflex
import           Reflex.Network
import           Reflex.Vty hiding (apply, Event, mainWidget)

import qualified Kyowon.Client as Client
import           Kyowon.Core.Types (UTCTimestamp(..), ClientId, createClient, UniqueId(..))
import           Kyowon.Reflex.Client (KyowonT, runKyowonT, zeroNextId, KyowonMonad)
import qualified Kyowon.Reflex.Client as Reflex
import           Kyowon.Reflex.Common (catMaybes)
import           Kyowon.Reflex.Next (nextIdWith)
import           Kyowon.Reflex.Time (sampleMonotonicTimeWith)
import qualified Kyowon.Reflex.VRDT.LWW as Reflex
import           Kyowon.Reflex.Vty.Widget
import           VRDT.Class
import           VRDT.Class.TH
import           VRDT.LWW (LWW(..))
import qualified VRDT.LWW as LWW
-- import           VRDT.MultiSet (MultiSet(..))
import           VRDT.TwoPMap (TwoPMap(..), TwoPMapOp(..))
import qualified VRDT.TwoPMap
import qualified VRDT.Types as VRDT

type LWWU a = LWW UTCTimestamp a
type Widget t m a = (Reflex t, MonadHold t m, MonadFix m, Adjustable t m, NotReady t m, PostBuild t m, MonadNodeId m, TriggerEvent t m, PerformEvent t m, MonadIO (Performable m), PostBuild t m, MonadIO m, KyowonMonad m, KyowonMonad (Performable m)) => VtyWidget t m a
type State = TwoPMap UniqueId Event
type StateOp = TwoPMapOp UniqueId Event


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

-- TODO: 
--  Make JSON instance. 
--  Switch to EventId.
-- newtype EventId = EventId { unEventId :: UniqueId }
type EventId = UniqueId

instance Ord t => VRDT (LWW t a) where
    type Operation (LWW t a) = LWW t a
    enabled = LWW.enabledLWW
    apply = LWW.applyLWW


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

data View = 
    ViewEvents
  | ViewCreateEvent
  | ViewEvent EventId
  | ViewEditEvent EventId Event

app :: Widget t m ()
app = do
  -- nav <- tabNavigation
  -- runLayout (pure Orientation_Column) 0 nav $ do
  clientId <- lift Reflex.getClientId
  rec 
      st <- lift $ Reflex.connectToStore' storeRef initVRDT opsE
      -- let eB = current e

      -- let opsE = (undefined :: Reflex.Event (TwoPMapOp UTCTimestamp Event))


      -- out :: Dynamic t (Reflex.Event t View, Reflex.Event t (TwoPMapOp UniqueId Event))
      out <- networkHold (events st) $ ffor (switchDyn (fst <$> out)) $ \case
          ViewCreateEvent -> createEvent clientId
          ViewEvents -> events st
          ViewEvent eId -> event eId $ (Map.lookup eId . twoPMap) <$> st
          ViewEditEvent eId e -> editEvent eId e
      
      let opsE = switchDyn (snd <$> out)

  return ()

  where
    storeRef = Reflex.StoreRef (Client.Server "http://localhost:3000") (Client.StoreId "TODO")

editEvent :: forall t m . EventId -> Event -> Widget t m (Reflex.Event t View, Reflex.Event t [StateOp])
editEvent eId event = do
  nav <- tabNavigation
  runLayout (pure Orientation_Column) 0 nav $ do
    backE <- fixed 3 $ textButtonStatic def "Back"

    title <- validateInput' "Title" Right id EventTitleOp (lwwValue $ eventTitle event)
    description <- validateInput' "Description" Right id EventDescriptionOp (lwwValue $ eventDescription event)
    startDate <- validateInput' "Start Date" dateValidation displayDate EventStartTimeOp (lwwValue $ eventStartTime event)
    endDate <- validateInput' "End Date" dateValidation displayDate EventEndTimeOp (lwwValue $ eventEndTime event)
    location <- validateInput' "Location" Right id EventLocationOp (lwwValue $ eventLocation event)

    updateE <- fixed 3 $ textButtonStatic def "Update"

    -- If all fields are valid, propogate updates.
    let opsMD = (liftM5 . liftM5) (\a b c d e -> [a,b,c,d,e]) title description startDate endDate location
    let opsE = Maybe.catMaybes <$> (catMaybes $ sampleOn updateE opsMD)


    let viewE = leftmost [ ViewEvent eId <$ backE
                         , ViewEvent eId <$ opsE
                         ]

    return (viewE, opsE)

  where
    -- Validate input, check if the inputs changed, and create update operation.
    validateInput' :: (Eq a) => Text -> (Text -> Either Text a) -> (a -> Text) -> (LWW UTCTimestamp a -> EventOp) -> a -> Layout t m (Dynamic t (Maybe (Maybe StateOp)))
    validateInput' label validation render eventOp currentValue = do
        t <- validateInput label validation $ Just $ render currentValue
        clientId <- lift Reflex.getClientId
        lift $ sampleMonotonicTimeWith (\a t -> (\v -> 
            -- Don't update if the value hasn't changed.
            if v == currentValue then
                Nothing
            else
                Just $ TwoPMapApply eId $ eventOp $ LWW (UTCTimestamp t clientId) v
          ) <$> a) t

event :: EventId -> Dynamic t (Maybe Event) -> Widget t m (Reflex.Event t View, Reflex.Event t [StateOp])
event eId eventMD = do
  nav <- tabNavigation
  runLayout (pure Orientation_Column) 0 nav $ do
    backE <- fixed 3 $ textButtonStatic def "Back"

    editE' <- networkView $ ffor eventMD $ \case
        Nothing -> do
            fixed 1 $ text "Event does not exist."

            return never

        Just e -> do
            editE <- fixed 3 $ textButtonStatic def "Edit"

            fixed 1 $ text "Title:"
            fixed 1 $ text $ pure $ lwwValue $ eventTitle e
            
            fixed 1 $ text "Description:"
            fixed 1 $ text $ pure $ lwwValue $ eventDescription e

            fixed 1 $ text "Start time:"
            fixed 1 $ text $ pure $ displayDate $ lwwValue $ eventStartTime e

            fixed 1 $ text "End time:"
            fixed 1 $ text $ pure $ displayDate $ lwwValue $ eventEndTime e

            fixed 1 $ text "Location:"
            fixed 1 $ text $ pure $ lwwValue $ eventLocation e

            return $ const e <$> editE
    editE <- switchHold never editE'


    let viewE = leftmost [ ViewEvents <$ backE
                         , ViewEditEvent eId <$> editE
                         ]

    return (viewE, never)
    

events :: Dynamic t State -> Widget t m (Reflex.Event t View, Reflex.Event t [StateOp])
events st = do
  nav <- tabNavigation
  runLayout (pure Orientation_Column) 0 nav $ do

    -- Create event button.
    createE <- fixed 3 $ textButtonStatic def "Create an event"
    
    -- Display events.
    fixed 1 $ text $ pure "Events:"
    selectEventE <- simpleList (Map.assocs . twoPMap <$> st) displayEvent

    let view = leftmost
          [ ViewCreateEvent <$ createE
          , switchDyn (leftmost <$> selectEventE)
          ]
    return (view, never)

  where

    displayEvent eventD = do
        let eventText (_, e) = lwwValue (eventTitle e) <> " - " <> "TODO"
        clickedE <- fixed 1 $ link $ current $ eventText <$> eventD
        -- tile tileCfg $ do
        --     -- TODO: Can we set background color when focused?
        --     
        --     text $ current $ (lwwValue . eventTitle) <$> eventD
        --     click <- void <$> mouseDown V.BLeft
        --     let focusMe = leftmost [click] -- , sel, pb ]

        --     return (focusMe, ())



        -- Return selection event.
        let viewEventE = ViewEvent . fst <$> tag (current eventD) clickedE
        return viewEventE
        
    -- tileCfg = TileConfig { _tileConfig_constraint = pure $ Constraint_Fixed 1
    --                      , _tileConfig_focusable = pure $ True
    --                      }

createEvent :: forall t m . ClientId -> Widget t m (Reflex.Event t View, Reflex.Event t [StateOp])
createEvent clientId = do
  escapedE <- escapePressed
  col $ do
    rec
        title <- validateInput "Title" Right Nothing >>= toLWW
        description <- validateInput "Description" Right Nothing >>= toLWW
        startDate <- validateInput "Start Date" dateValidation Nothing >>= toLWW
        endDate <- validateInput "End Date" dateValidation Nothing >>= toLWW
        location <- validateInput "Location" Right Nothing >>= toLWW

        cancelE <- fixed 3 $ textButtonStatic def "Cancel"
        createE <- fixed 3 $ textButtonStatic def "Create event"

    let eventMD = (liftM5 . liftM5) Event title description startDate endDate location
    let insertEventE = catMaybes $ sampleOn createE eventMD
    insertE <- lift $ to2PMapInsert clientId insertEventE

    let viewE = leftmost
          [ ViewEvents <$ cancelE
          , ViewEvents <$ escapedE
          -- , ViewEvents <$ insertE
          , (\(TwoPMapInsert k _) -> ViewEvent k) <$> insertE
          ]


    return (viewE, pure <$> insertE)

  where
    toLWW :: Dynamic t (Maybe a) -> Layout t m (Dynamic t (Maybe (LWW UTCTimestamp a)))
    toLWW = lift . Reflex.toLWW' clientId

    to2PMapInsert clientId = nextIdWith $ \e nextId -> 
        let k = UniqueId clientId nextId in
        TwoPMapInsert k e

validateInput :: (Reflex t, MonadNodeId m, MonadHold t m, MonadFix m) => Text -> (Text -> Either Text a) -> Maybe Text -> Layout t m (Dynamic t (Maybe a))
validateInput label validation initTextM = do
    rec
        let label' = addErr <$> current vE
        fixed 1 $ text label'
        let setInit = maybe id (\v c -> c {_textInputConfig_initialValue = Zipper.fromText v}) initTextM
        t <- fixed 1 $ textInput $ setInit def

        -- TODO: holdDyn on e
        let vE = validation <$> _textInput_value t

    return $ either (const Nothing) Just <$> vE

  where
    addErr (Left e) = label <> " (" <> e <> "):"
    addErr _        = label <> ":"

dateValidation :: Text -> Either Text UTCTime
dateValidation = maybe (Left "Invalid date") Right . parseTimeM True defaultTimeLocale "%Y-%-m-%-d %l:%M%p" . Text.unpack
    
displayDate :: UTCTime -> Text
displayDate = Text.pack . formatTime defaultTimeLocale "%Y-%-m-%-d %l:%M%p"


sampleOn :: Reflex t => Reflex.Event t a -> Dynamic t b -> Reflex.Event t b
sampleOn event dyn = tag (current dyn) event

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
