module VRDT.Class where

-- | Class for verified conflict-free replicated datatypes.
class VRDT t where
    -- | Type that represents operations on `t`.
    type Operation t = op | op -> t

    -- | Apply an operation.
    apply :: Operation t -> t -> t

    -- TODO: CmCRDT laws.


-- JP: CRDT monad? 


