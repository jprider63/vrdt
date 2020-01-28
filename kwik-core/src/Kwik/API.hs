
module Kwik.API where

import qualified Kwik.API.V0 as V0
import Servant ((:>))

type API = "v0" :> V0.API
