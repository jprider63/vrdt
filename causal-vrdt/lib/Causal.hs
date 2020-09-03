{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
module Causal where

import VRDT.Class (VRDT)
import qualified VRDT.Class as VRDT

import Data.Map (Map)

import Data.UUID (UUID)
import qualified Data.UUID.V4 as UUID

import qualified Causal.VectorClock as VC -- dkvs@ac16eda
import qualified Causal.CBCAST as CBCAST -- dkvs@ac16eda

import Control.Monad.Identity (runIdentity)
import Control.Monad.State (runState, modify')

-- $setup
--
-- >>> import VRDT.LWW
-- >>> import VRDT.MultiSet
-- >>> :set -XStandaloneDeriving
-- >>> deriving instance (Show t, Show a) => Show (LWW t a)
-- >>> deriving instance Show a => Show (MultiSet a)
-- >>> deriving instance Show a => Show (MultiSetOp a)

type NodeId = UUID
type Time = Map NodeId Word

-- | Each instance of 'Causal' is to be regarded as a node, meaning that if an
-- operation is generated it must be broadcast to all other instances.
data Causal a = Causal
    { -- | roEnv is the local node-id
      roEnv :: CBCAST.Env NodeId
      -- | rwState is the current local vector-time and the local delay-queue
    , rwState :: CBCAST.State NodeId Time (VRDT.Operation a)
      -- | vrdt is the underlying CDRT
    , vrdt :: a
    }
deriving instance (Show a, Show (VRDT.Operation a)) => Show (Causal a)

-- | 'CausalOp' wraps the operations of the underlying 'VRDT' for reordering.
type CausalOp a = CBCAST.Message NodeId Time (VRDT.Operation a)

-- |
--
-- >>> v <- newCausal (LWW 1 "Hello")
-- >>> print v
-- Causal {roEnv = ...-...-...-...-..., rwState = (fromList [],DelayQueue (fromList [])), vrdt = LWW {lwwTime = 1, lwwValue = "Hello"}}
newCausal :: VRDT a => a -> IO (Causal a)
newCausal vrdt = do
    roEnv <- UUID.nextRandom
    return Causal{..}
  where
    rwState = (VC.new, CBCAST.dqEmpty)

newCausalOp :: VRDT a => VRDT.Operation a -> Causal a -> (Causal a, CausalOp a)
newCausalOp vrdtOp causal@Causal{..}
    -- Update the causal vrdt with the new CBCAST state; return the op to be broadcast
    = (causal{rwState=rwState'}, causalOp)
  where
    -- CBCAST.send doesn't throw an error, and only one message is sent
    (Right (), rwState', [causalOp])
        = runIdentity
        . CBCAST.runCBCAST roEnv rwState
        . CBCAST.send
        $ vrdtOp

applyCausalOp :: (VRDT a, Show (VRDT.Operation a)) => Causal a -> CausalOp a -> Causal a
applyCausalOp causal@Causal{..} receivedCausalOp
    -- Update the causal vrdt with the new CBCAST state and underlying VRDT
    = causal{rwState=rwState', vrdt=vrdt'}
  where
    -- CBCAST.fullLifecycle doesn't throw an error if the acceptDelivery function doesn't
    -- CBCAST.fullLifecycle doesn't send any messages if the acceptDelivery function doesn't
    ((Right (), rwState', []), vrdt')
        = flip runState vrdt
        . CBCAST.runCBCAST roEnv rwState
        . CBCAST.fullLifecycle (\deliveredCausalOp -> do
            -- Apply each delivered message to the underlying VRDT
            let vrdtOp = CBCAST.content deliveredCausalOp
            modify' (flip VRDT.apply vrdtOp))
        $ receivedCausalOp

instance (VRDT a, Show (VRDT.Operation a)) => VRDT (Causal a) where
    type Operation (Causal a) = CausalOp a
    apply = applyCausalOp

    -- TODO: according to the paper we need to define compatible to indicate
    -- when messages are concurrent? why?
    compatible = undefined
    -- TODO: according to the paper we need to define compatibleState to
    -- indicate when the "current state is compatible with the given operation"
    -- but it's not clear what that means; it's probably "always" since we
    -- buffer operations that cannot be applied
    compatibleState = undefined

    -- TODO: provide proofs
    lawCommutativity = undefined
    lawCompatibilityCommutativity = undefined
