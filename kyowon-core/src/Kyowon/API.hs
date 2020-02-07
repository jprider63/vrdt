
module Kyowon.API where

import qualified Kyowon.API.V0 as V0
import Servant ((:>))

type API = "v0" :> V0.API
