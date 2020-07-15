{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}

{-# LANGUAGE TemplateHaskell #-}

module Event.Types where

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
import           VRDT.MultiSet
import           VRDT.LWW
import Liquid.Data.Maybe
import           Liquid.ProofCombinators
import Liquid.Data.Map
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


instance VRDT Event where
  type Operation Event = EventOp
  apply v_adIk@(Event _ _eventDescription _ _ _ _) (EventDescriptionOp op_adIl)
      = v_adIk{eventDescription = apply _eventDescription op_adIl}
  apply v_adIm@(Event _ _ _ _eventEndTime _ _) (EventEndTimeOp op_adIn)
      = v_adIm{eventEndTime = apply _eventEndTime op_adIn }
  
  apply v_adIo@(Event _ _ _ _ _eventLocation _) (EventLocationOp op_adIp)
      = v_adIo
          {eventLocation = (apply _eventLocation) op_adIp}
  apply v_adIq@(Event _ _ _ _ _ _eventRSVPs) (EventRSVPsOp op_adIr)
      = v_adIq
          {eventRSVPs = (apply _eventRSVPs) op_adIr}
  apply v_adIs@(Event _ _ _eventStartTime _ _ _) (EventStartTimeOp op_adIt)
      = v_adIs
          {eventStartTime = (apply _eventStartTime)
                              op_adIt}
  apply v_adIu@(Event _eventTitle _ _ _ _ _) (EventTitleOp op_adIv)
      = v_adIu
          {eventTitle = (apply _eventTitle) op_adIv}

  compatible
      (EventDescriptionOp op1_adIw)
      (EventDescriptionOp op2_adIx)
      = (compatible op1_adIw) op2_adIx
  compatible
      (EventEndTimeOp op1_adIy)
      (EventEndTimeOp op2_adIz)
      = (compatible op1_adIy) op2_adIz
  compatible
      (EventLocationOp op1_adIA)
      (EventLocationOp op2_adIB)
      = (compatible op1_adIA) op2_adIB
  compatible
      (EventRSVPsOp op1_adIC)
      (EventRSVPsOp op2_adID)
      = (compatible op1_adIC) op2_adID
  compatible
      (EventStartTimeOp op1_adIE)
      (EventStartTimeOp op2_adIF)
      = (compatible op1_adIE) op2_adIF
  compatible
      (EventTitleOp op1_adIG)
      (EventTitleOp op2_adIH)
      = (compatible op1_adIG) op2_adIH
  compatible _ _ = True

  compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventTitleOp op) = compatibleState eventTitle op
  compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventDescriptionOp op) = compatibleState eventDescription op
  compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventStartTimeOp op) = compatibleState eventStartTime op
  compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventEndTimeOp op) = compatibleState eventEndTime op
  compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventLocationOp op) = compatibleState eventLocation op
  compatibleState (Event eventTitle eventDescription eventStartTime eventEndTime eventLocation eventRSVPs) (EventRSVPsOp op) = compatibleState eventRSVPs op

  lawCommutativity
    v_adII@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs)
    op1@(EventDescriptionOp op1_adIJ)
    op2@(EventDescriptionOp op2_adIK)
    =  lawCommutativity _eventDescription op1_adIJ op2_adIK

  lawCommutativity
    v_adIL@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs)
    op1@(EventEndTimeOp op1_adIM)
    op2@(EventEndTimeOp op2_adIN)
    = lawCommutativity _eventEndTime op1_adIM op2_adIN


  lawCommutativity
    v_adIL@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs)
    op1@(EventLocationOp op1_adIM)
    op2@(EventLocationOp op2_adIN)
    = lawCommutativity _eventLocation op1_adIM op2_adIN 

  lawCommutativity
    v_adIL@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs)
    op1@(EventRSVPsOp op1_adIM)
    op2@(EventRSVPsOp op2_adIN)
    = lawCommutativity _eventRSVPs op1_adIM op2_adIN
  lawCommutativity
    v_adIL@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs)
    op1@(EventStartTimeOp op1_adIM)
    op2@(EventStartTimeOp op2_adIN)
    = lawCommutativity _eventStartTime op1_adIM op2_adIN
  lawCommutativity
    v_adIL@(Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs)
    op1@(EventTitleOp op1_adIM)
    op2@(EventTitleOp op2_adIN)
    = lawCommutativity _eventTitle op1_adIM op2_adIN
  lawCommutativity (Event _eventTitle _eventDescription _eventStartTime _eventEndTime _eventLocation _eventRSVPs) op1 op2 = ()
  
  lawCompatibilityCommutativity
    (EventDescriptionOp op1_adJ0)
    (EventDescriptionOp op2_adJ1)
    = (lawCompatibilityCommutativity op1_adJ0) op2_adJ1
  lawCompatibilityCommutativity
    (EventEndTimeOp op1_adJ2)
    (EventEndTimeOp op2_adJ3)
    = (lawCompatibilityCommutativity op1_adJ2) op2_adJ3
  lawCompatibilityCommutativity
    (EventLocationOp op1_adJ4)
    (EventLocationOp op2_adJ5)
    = (lawCompatibilityCommutativity op1_adJ4) op2_adJ5
  lawCompatibilityCommutativity
    (EventRSVPsOp op1_adJ6)
    (EventRSVPsOp op2_adJ7)
    = (lawCompatibilityCommutativity op1_adJ6) op2_adJ7
  lawCompatibilityCommutativity
    (EventStartTimeOp op1_adJ8)
    (EventStartTimeOp op2_adJ9)
    = (lawCompatibilityCommutativity op1_adJ8) op2_adJ9
  lawCompatibilityCommutativity
    (EventTitleOp op1_adJa)
    (EventTitleOp op2_adJb)
    = lawCompatibilityCommutativity op1_adJa op2_adJb
  lawCompatibilityCommutativity _ _ = ()

#endif



