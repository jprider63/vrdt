{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}
-- {-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE TemplateHaskell #-}

module Event.Types5 where

import           Data.Text (Text)
import           Data.Time.Clock (UTCTime)
import           GHC.Generics

#if NotLiquid
import           Kyowon.Core.Types (UTCTimestamp(..))
import           VRDT.Class.TH
import           VRDT.LWW (LWW(..))
import           VRDT.MultiSet (MultiSet(..))
#else
import           VRDT.Class
import qualified VRDT.MultiSet.Internal as Internal
import           VRDT.MultiSet.Internal (MultiSet(..), MultiSetOp(..))
import           VRDT.MultiSet
import           Liquid.Data.Maybe
import           Liquid.Data.Map
import           VRDT.LWW
import           ProofCombinators
import           Liquid.ProofCombinators
#endif

#ifndef NotLiquid
data UTCTimestamp = UTCTimestamp UTCTime ClientId
  deriving (Eq, Ord)
type ClientId = Integer
#endif

type LWWU a = LWW UTCTimestamp a

data Event = Event {
    eventTitle :: LWWU Text
  , eventDescription :: LWWU Text
  , eventStartTime :: LWWU UTCTime
  , eventEndTime :: LWWU UTCTime
  , eventLocation :: LWWU Text
  , eventRSVPs :: MultiSet Text
  -- Messages?
  }
#if NotLiquid
  deriving (Generic)
#endif

#if NotLiquid
$(deriveVRDT ''Event)
#else



-- Generated by $(deriveVRDT ''Event):
data EventOp
  = EventDescriptionOp (Operation (LWWU Text)) |
    EventEndTimeOp (Operation (LWWU UTCTime)) |
    EventLocationOp (Operation (LWWU Text)) |
    EventRSVPsOp (Operation (MultiSet Text)) |
    EventStartTimeOp (Operation (LWWU UTCTime)) |
    EventTitleOp (Operation (LWWU Text))
--   = EventDescriptionOp (Operation (LWWU Text)) |
--     EventEndTimeOp (Operation (LWWU UTCTime)) |
--     EventLocationOp (Operation (LWWU Text)) |
--     EventRSVPsOp (Operation (MultiSet Text)) |
--     EventStartTimeOp (Operation (LWWU UTCTime)) |
--     EventTitleOp (Operation (LWWU Text))
  -- deriving Generic

{-@ reflect compatibleEvent @-}
compatibleEvent :: EventOp -> EventOp -> Bool
compatibleEvent
    (EventDescriptionOp op1_adIw)
    (EventDescriptionOp op2_adIx)
    = (compatible op1_adIw) op2_adIx
compatibleEvent
    (EventEndTimeOp op1_adIy)
    (EventEndTimeOp op2_adIz)
    = (compatible op1_adIy) op2_adIz
compatibleEvent
    (EventLocationOp op1_adIA)
    (EventLocationOp op2_adIB)
    = (compatible op1_adIA) op2_adIB
compatibleEvent
    (EventRSVPsOp op1_adIC)
    (EventRSVPsOp op2_adID)
    = (compatible op1_adIC) op2_adID
compatibleEvent
    (EventStartTimeOp op1_adIE)
    (EventStartTimeOp op2_adIF)
    = (compatible op1_adIE) op2_adIF
compatibleEvent
    (EventTitleOp op1_adIG)
    (EventTitleOp op2_adIH)
    = (compatible op1_adIG) op2_adIH
compatibleEvent _ _ = True

{-@ reflect compatibleEventState @-}
compatibleEventState :: Event -> EventOp -> Bool
compatibleEventState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventTitleOp op) = compatibleState eventTitle op
compatibleEventState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventDescriptionOp op) = compatibleState eventDescription op
compatibleEventState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventStartTimeOp op) = compatibleState eventStartTime op
compatibleEventState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventEndTimeOp op) = compatibleState eventEndTime op
compatibleEventState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventLocationOp op) = compatibleState eventLocation op
compatibleEventState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventRSVPsOp op) = compatibleState eventRSVPs op


{-@ reflect applyEvent @-}
applyEvent :: Event -> EventOp -> Event
applyEvent v_adIk@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs) (EventDescriptionOp op_adIl)
    = Event _eventTitle (apply _eventDescription op_adIl) _eventStartTime _eventEndTime _eventLocation _eventRSVPs

applyEvent v_adIm@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs) (EventEndTimeOp op_adIn)
    = Event _eventTitle _eventDescription _eventStartTime (apply _eventEndTime op_adIn) _eventLocation _eventRSVPs 
applyEvent v_adIo (EventLocationOp op_adIp)
    = v_adIo
        {eventLocation = (apply (eventLocation v_adIo)) op_adIp}
applyEvent v_adIq (EventRSVPsOp op_adIr)
    = v_adIq
        {eventRSVPs = (apply (eventRSVPs v_adIq)) op_adIr}
applyEvent v_adIs (EventStartTimeOp op_adIt)
    = v_adIs
        {eventStartTime = (apply (eventStartTime v_adIs))
                            op_adIt}
applyEvent v_adIu (EventTitleOp op_adIv)
    = v_adIu
        {eventTitle = (apply (eventTitle v_adIu)) op_adIv}
{-@ lawCommutativityEvent :: x:Event -> op1:EventOp -> op2:EventOp -> {(compatibleEventState x op1 && compatibleEventState x op2 && compatibleEvent op1 op2) => (applyEvent (applyEvent x op1) op2 = applyEvent (applyEvent x op2) op1 && compatibleEventState (applyEvent x op1) op2)} @-}
lawCommutativityEvent :: Event -> EventOp -> EventOp -> ()
lawCommutativityEvent
    v_adII@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs)
    (EventDescriptionOp op1_adIJ)
    (EventDescriptionOp op2_adIK)
    =   ()
    -- &&& (  applyEvent (apply v_adII (EventDescriptionOp op1_adIJ)) (EventDescriptionOp op2_adIK)
    -- ===  apply (apply (Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs) (EventDescriptionOp op1_adIJ)) (EventDescriptionOp op2_adIK)
    -- ===  apply (v_adII{eventDescription = apply (eventDescription v_adII) op1_adIJ}) (EventDescriptionOp op2_adIK)
    -- ===  apply (v_adII{Event.Types5.eventDescription = (apply _eventDescription)
    --                           op1_adIJ}) (EventDescriptionOp op2_adIK)
    -- ===  apply (Event _eventTitle (apply _eventDescription op1_adIJ) _eventStartTime _eventEndTime _eventLocation _eventRSVPs) (EventDescriptionOp op2_adIK)
    -- ===  apply (apply v_adII (EventDescriptionOp op2_adIK)) (EventDescriptionOp op1_adIJ)
    -- ***  QED)
    -- `cast`
    --    ()

lawCommutativityEvent
    v_adIL@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs)
    (EventEndTimeOp op1_adIM)
    (EventEndTimeOp op2_adIN)
    = ()
-- lawCommutativityEvent
--     v_adIO
--     (EventLocationOp op1_adIP)
--     (EventLocationOp op2_adIQ)
--     = ((lawCommutativity (eventLocation v_adIO)) op1_adIP)
--         op2_adIQ
-- lawCommutativityEvent
--     v_adIR
--     (EventRSVPsOp op1_adIS)
--     (EventRSVPsOp op2_adIT)
--     = ((lawCommutativity (eventRSVPs v_adIR)) op1_adIS)
--         op2_adIT
-- lawCommutativityEvent
--     v_adIU
--     (EventStartTimeOp op1_adIV)
--     (EventStartTimeOp op2_adIW)
--     = ((lawCommutativity (eventStartTime v_adIU)) op1_adIV)
--         op2_adIW
-- lawCommutativityEvent
--     v_adIX
--     (EventTitleOp op1_adIY)
--     (EventTitleOp op2_adIZ)
--     = ((lawCommutativity (eventTitle v_adIX)) op1_adIY)
--         op2_adIZ
lawCommutativityEvent _ _ _ = undefined

{-@ lawCompatibilityEventCommutativity :: op1:EventOp -> op2:EventOp -> {compatibleEvent op1 op2 == compatibleEvent op2 op1} @-}
lawCompatibilityEventCommutativity :: EventOp -> EventOp -> ()
lawCompatibilityEventCommutativity
    (EventDescriptionOp op1_adJ0)
    (EventDescriptionOp op2_adJ1)
    = (lawCompatibilityCommutativity op1_adJ0) op2_adJ1
lawCompatibilityEventCommutativity
    (EventEndTimeOp op1_adJ2)
    (EventEndTimeOp op2_adJ3)
    = (lawCompatibilityCommutativity op1_adJ2) op2_adJ3
lawCompatibilityEventCommutativity
    (EventLocationOp op1_adJ4)
    (EventLocationOp op2_adJ5)
    = (lawCompatibilityCommutativity op1_adJ4) op2_adJ5
lawCompatibilityEventCommutativity
    (EventRSVPsOp op1_adJ6)
    (EventRSVPsOp op2_adJ7)
    = (lawCompatibilityCommutativity op1_adJ6) op2_adJ7
lawCompatibilityEventCommutativity
    (EventStartTimeOp op1_adJ8)
    (EventStartTimeOp op2_adJ9)
    = (lawCompatibilityCommutativity op1_adJ8) op2_adJ9
lawCompatibilityEventCommutativity
    (EventTitleOp op1_adJa)
    (EventTitleOp op2_adJb)
    -- = (lawCompatibilityCommutativity op1_adJa) op2_adJb
    = lawCompatibilityCommutativity op1_adJa op2_adJb
lawCompatibilityEventCommutativity _ _ = ()





-- instance VRDT Event where
--   type Operation Event = EventOp
--   compatible
--     (EventDescriptionOp op1_adIw)
--     (EventDescriptionOp op2_adIx)
--     = (compatible op1_adIw) op2_adIx
--   compatible
--     (EventEndTimeOp op1_adIy)
--     (EventEndTimeOp op2_adIz)
--     = (compatible op1_adIy) op2_adIz
--   compatible
--     (EventLocationOp op1_adIA)
--     (EventLocationOp op2_adIB)
--     = (compatible op1_adIA) op2_adIB
--   compatible
--     (EventRSVPsOp op1_adIC)
--     (EventRSVPsOp op2_adID)
--     = (compatible op1_adIC) op2_adID
--   compatible
--     (EventStartTimeOp op1_adIE)
--     (EventStartTimeOp op2_adIF)
--     = (compatible op1_adIE) op2_adIF
--   compatible
--     (EventTitleOp op1_adIG)
--     (EventTitleOp op2_adIH)
--     = (compatible op1_adIG) op2_adIH
--   compatible _ _ = True
--   compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventTitleOp op) = compatibleState eventTitle op
--   compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventDescriptionOp op) = compatibleState eventDescription op
--   compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventStartTimeOp op) = compatibleState eventStartTime op
--   compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventEndTimeOp op) = compatibleState eventEndTime op
--   compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventLocationOp op) = compatibleState eventLocation op
--   compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventRSVPsOp op) = compatibleState eventRSVPs op
--   apply v_adIk (EventDescriptionOp op_adIl)
--     = v_adIk
--         {eventDescription = (apply (eventDescription v_adIk))
--                               op_adIl}
--   apply v_adIm (EventEndTimeOp op_adIn)
--     = v_adIm
--         {eventEndTime = (apply (eventEndTime v_adIm)) op_adIn}
--   apply v_adIo (EventLocationOp op_adIp)
--     = v_adIo
--         {eventLocation = (apply (eventLocation v_adIo)) op_adIp}
--   apply v_adIq (EventRSVPsOp op_adIr)
--     = v_adIq
--         {eventRSVPs = (apply (eventRSVPs v_adIq)) op_adIr}
--   apply v_adIs (EventStartTimeOp op_adIt)
--     = v_adIs
--         {eventStartTime = (apply (eventStartTime v_adIs))
--                             op_adIt}
--   apply v_adIu (EventTitleOp op_adIv)
--     = v_adIu
--         {eventTitle = (apply (eventTitle v_adIu)) op_adIv}
--   -- lawCommutativity
--   --   v_adII@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs)
--   --   (EventDescriptionOp op1_adIJ)
--   --   (EventDescriptionOp op2_adIK)
--   --   =   (  apply v_adII (EventDescriptionOp op1_adIJ)
--   --      === v_adII{eventDescription = apply (eventDescription v_adII) op1_adIJ}
--   --     *** QED)
--   --   -- &&& (  apply (apply v_adII (EventDescriptionOp op1_adIJ)) (EventDescriptionOp op2_adIK)
--   --   -- ===  apply (apply (Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs) (EventDescriptionOp op1_adIJ)) (EventDescriptionOp op2_adIK)
--   --   -- ===  apply (v_adII{eventDescription = apply (eventDescription v_adII) op1_adIJ}) (EventDescriptionOp op2_adIK)
--   --   -- ===  apply (v_adII{Event.Types3.eventDescription = (apply _eventDescription)
--   --   --                           op1_adIJ}) (EventDescriptionOp op2_adIK)
--   --   -- ===  apply (Event _eventTitle (apply _eventDescription op1_adIJ) _eventStartTime _eventEndTime _eventLocation _eventRSVPs) (EventDescriptionOp op2_adIK)
--   --   -- ===  apply (apply v_adII (EventDescriptionOp op2_adIK)) (EventDescriptionOp op1_adIJ)
--   --   -- ***  QED)
--   --   `cast`
--   lawCommutativity
--     v_adII
--     (EventDescriptionOp op1_adIJ)
--     (EventDescriptionOp op2_adIK)

--     = ((lawCommutativity (Event.Types3.eventDescription v_adII))
--          op1_adIJ)
--         op2_adIK
--   lawCommutativity
--     v_adIL
--     (EventEndTimeOp op1_adIM)
--     (EventEndTimeOp op2_adIN)
--     = ((lawCommutativity (eventEndTime v_adIL)) op1_adIM)
--         op2_adIN
--   lawCommutativity
--     v_adIO
--     (EventLocationOp op1_adIP)
--     (EventLocationOp op2_adIQ)
--     = ((lawCommutativity (eventLocation v_adIO)) op1_adIP)
--         op2_adIQ
--   lawCommutativity
--     v_adIR
--     (EventRSVPsOp op1_adIS)
--     (EventRSVPsOp op2_adIT)
--     = ((lawCommutativity (eventRSVPs v_adIR)) op1_adIS)
--         op2_adIT
--   lawCommutativity
--     v_adIU
--     (EventStartTimeOp op1_adIV)
--     (EventStartTimeOp op2_adIW)
--     = ((lawCommutativity (eventStartTime v_adIU)) op1_adIV)
--         op2_adIW
--   lawCommutativity
--     v_adIX
--     (EventTitleOp op1_adIY)
--     (EventTitleOp op2_adIZ)
--     = ((lawCommutativity (eventTitle v_adIX)) op1_adIY)
--         op2_adIZ
--   lawCommutativity _ _ _ = ()
--   lawCompatibilityCommutativity
--     (EventDescriptionOp op1_adJ0)
--     (EventDescriptionOp op2_adJ1)
--     = (lawCompatibilityCommutativity op1_adJ0) op2_adJ1
--   lawCompatibilityCommutativity
--     (EventEndTimeOp op1_adJ2)
--     (EventEndTimeOp op2_adJ3)
--     = (lawCompatibilityCommutativity op1_adJ2) op2_adJ3
--   lawCompatibilityCommutativity
--     (EventLocationOp op1_adJ4)
--     (EventLocationOp op2_adJ5)
--     = (lawCompatibilityCommutativity op1_adJ4) op2_adJ5
--   lawCompatibilityCommutativity
--     (EventRSVPsOp op1_adJ6)
--     (EventRSVPsOp op2_adJ7)
--     = (lawCompatibilityCommutativity op1_adJ6) op2_adJ7
--   lawCompatibilityCommutativity
--     (EventStartTimeOp op1_adJ8)
--     (EventStartTimeOp op2_adJ9)
--     = (lawCompatibilityCommutativity op1_adJ8) op2_adJ9
--   lawCompatibilityCommutativity
--     (EventTitleOp op1_adJa)
--     (EventTitleOp op2_adJb)
--     -- = (lawCompatibilityCommutativity op1_adJa) op2_adJb
--     =
--         (lawCompatibilityCommutativity op1_adJa) op2_adJb
--     &&& assert (compatible op1_adJa op2_adJb == compatible op2_adJb op1_adJa)
--     &&& assume (compatible (EventTitleOp op1_adJa) (EventTitleOp op2_adJb) == compatible op1_adJa op2_adJb) -- Needed due to --noadt?
--     &&& assume (compatible (EventTitleOp op2_adJb) (EventTitleOp op1_adJa) == compatible op2_adJb op1_adJa) -- Needed due to --noadt?
--     &&& assert (compatible (EventTitleOp op1_adJa) (EventTitleOp op2_adJb) == compatible (EventTitleOp op2_adJb) (EventTitleOp op1_adJa))
--   lawCompatibilityCommutativity _ _ = ()
#endif


