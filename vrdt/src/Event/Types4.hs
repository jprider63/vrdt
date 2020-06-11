{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE TypeFamilies, TypeFamilyDependencies #-}
module Event.Types4 where
import           Liquid.ProofCombinators

class VRDT t where
    -- type Operation t = op | op -> t
    {-@ apply :: t ->  t -> t @-}
    apply :: t -> t -> t
    compatible ::  t ->  t -> Bool

data LWW t a = LWW {
    lwwTime  :: t
  , lwwValue :: a
  }

instance Ord t => VRDT (LWW t a) where
  -- type Operation (LWW t a) = LWW t a
  apply l1 l2
    | lwwTime l1 > lwwTime l2 = l1
    | otherwise = l2
  compatible l1 l2 = lwwTime l1 /= lwwTime l2

-- {-@ reflect applyLWW @-}
-- applyLWW :: Ord t => LWW t a  -> Operation (LWW t a) -> LWW t a
-- applyLWW l1 l2
--     | lwwTime l1 > lwwTime l2 = l1
--     | otherwise = l2
data Event = Event {
    eventDescription :: LWW Int Int
  }

data EventOp
  = EventDescriptionOp ( (LWW Int Int))

{-@ reflect applyEvent @-}
applyEvent :: Event -> EventOp -> Event
applyEvent v_adIk@(Event _eventDescription) (EventDescriptionOp op_adIl)
    = Event (apply _eventDescription op_adIl)

{-@ trivialEvent :: op: (LWW Int Int) -> ed:LWW Int Int -> {Event (apply ed op) == applyEvent (Event ed) (EventDescriptionOp op)} @-}
trivialEvent ::  (LWW Int Int) -> LWW Int Int -> ()
trivialEvent op ed = Event (apply ed op)
                 === applyEvent (Event ed) (EventDescriptionOp op)
                 *** QED

