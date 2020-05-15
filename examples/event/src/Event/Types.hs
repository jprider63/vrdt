{-# LANGUAGE TemplateHaskell #-}

module Event.Types where

import           Data.Text (Text)
import           Data.Time.Clock (UTCTime)
import           GHC.Generics

#if NotLiquid
import           Kyowon.Core.Types (UTCTimestamp(..))
#endif
import           VRDT.Class.TH
import           VRDT.LWW (LWW(..))
import           VRDT.MultiSet (MultiSet(..))

#ifndef NotLiquid
data UTCTimestamp = UTCTimestamp UTCTime ClientId
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

$(deriveVRDT ''Event)

