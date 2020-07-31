{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}

{-# LANGUAGE TemplateHaskell #-}

module Event.Types where

import           Data.Text (Text)
import           Data.Time.Clock (UTCTime)
import           GHC.Generics
import           VRDT.Class.TH


#if NotLiquid
import           Kyowon.Core.Types (UTCTimestamp(..))
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

$(deriveVRDT ''Event)
