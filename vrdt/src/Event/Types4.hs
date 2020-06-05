{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}
-- {-@ LIQUID "--prune-unsorted" @-}

{-# LANGUAGE TemplateHaskell #-}

module Event.Types4 where


import           VRDT.Class
import qualified VRDT.MultiSet.Internal as Internal
import           VRDT.MultiSet.Internal (MultiSet(..), MultiSetOp(..))
import           Liquid.Data.Maybe
import           Liquid.Data.Map
import           VRDT.LWW
import           ProofCombinators
import           Liquid.ProofCombinators



type LWWU a = LWW Int a

data Event = Event {
    eventTitle :: LWWU Int
  , eventDescription :: LWWU Int
  }

data EventOp
  = EventDescriptionOp ( (LWWU Int)) |
    EventTitleOp ( (LWWU Int))

{-@ reflect applyLWW @-}
applyLWW :: Ord t => LWW t a  -> LWW t a -> LWW t a
applyLWW x y  = x


{-@ reflect applyEvent @-}
applyEvent :: Event -> EventOp -> Event
applyEvent v_adIk@(Event _eventTitle _eventDescription) (EventDescriptionOp op_adIl)
    = Event _eventTitle (apply _eventDescription op_adIl)

applyEvent v_adIu (EventTitleOp op_adIv)
    = v_adIu
        {eventTitle = (apply (eventTitle v_adIu)) op_adIv}


{-@ lawCommutativityEvent :: x:Event -> op1:EventOp -> op2:EventOp -> {True} @-}
lawCommutativityEvent :: Event -> EventOp -> EventOp -> ()
lawCommutativityEvent
    v_adII@(Event _eventTitle _eventDescription)
    (EventDescriptionOp op1_adIJ)
    (EventDescriptionOp op2_adIK)
    =  applyEvent (Event _eventTitle _eventDescription) (EventDescriptionOp op1_adIJ)
       === Event _eventTitle (apply _eventDescription op1_adIJ)
       *** QED
lawCommutativityEvent _ _ _ = ()




