{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
module Event.Types4 where
import           VRDT.Class
import           Liquid.ProofCombinators
data LWW t a = LWW {
    lwwTime  :: t
  , lwwValue :: a
  }
instance Ord t => VRDT (LWW t a) where
  type Operation (LWW t a) = LWW t a
  apply l1 l2
    | lwwTime l1 > lwwTime l2 = l1
    | otherwise = l2
  compatible l1 l2 = lwwTime l1 /= lwwTime l2
  compatibleState l1 l2 = lwwTime l1 /= lwwTime l2
  lawCommutativity x y z = ()
  lawCompatibilityCommutativity _ _ = ()

{-@ reflect applyLWW @-}
applyLWW :: Ord t => LWW t a  -> LWW t a -> LWW t a
applyLWW x y  = x

data Event = Event {
    eventDescription :: LWW Int Int
  }

data EventOp
  = EventDescriptionOp (Operation (LWW Int Int))

{-@ reflect applyEvent @-}
applyEvent :: Event -> EventOp -> Event
applyEvent v_adIk@(Event _eventDescription) (EventDescriptionOp op_adIl)
    = Event (applyLWW _eventDescription op_adIl)

{-@ lawCommutativityEvent :: x:Event -> op1:EventOp -> op2:EventOp -> {True} @-}
lawCommutativityEvent :: Event -> EventOp -> EventOp -> ()
lawCommutativityEvent
    v_adII@(Event _eventDescription)
    (EventDescriptionOp op1_adIJ)
    (EventDescriptionOp op2_adIK)
    =  applyEvent (Event _eventDescription) (EventDescriptionOp op1_adIJ)
       === Event (apply _eventDescription op1_adIJ)
       *** QED
