module NonCausal where

data VectorClock clientId t = VectorClock (Map clientId t)

data NonCausal clientid t a = NonCausal {
    state :: a
  , pending :: [NonCausalOp clientid t a]
  , vc :: VectorClock clientid t
  }

data NonCausalOp clientid t a = NonCausalOp {
    op :: Operation a
  , vc :: VectorClock clientid t
  -- , client :: clientid -- Is this Needed?
  }

instance CRDT a => CRDT (NonCausal clientid t a) where
  type Operation (NonCausal clientid t a) = NonCausalOp clientid t a

  enabled (NonCausal state pending) (NonCausalOp op _) = enabled state op
  apply (NonCausal state pending) (NonCausalOp op vc) = 
    -- We need the clientid of the receiver to increment the receiver's time. We could stuff it in NonCausal, but that would break the Eq instance..

  lawCommutativity 
  
instance CRDT a => NonCausal (VRDT a) where

