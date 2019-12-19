{-# LANGUAGE TypeFamilies, TypeFamilyDependencies #-}

module VRDT.Class where

-- | Class for verified conflict-free replicated datatypes.
class VRDT t where
    -- | Type that represents operations on `t`.
    type Operation t = op | op -> t

    -- | Apply an operation.
    apply :: Operation t -> t -> t

    -- | Commutativity law.
    {-@ lawCommutativity :: x : t -> op1 : Operation t -> op2 : Operation t -> {apply op2 (apply op1) == apply op1 (apply op2)} @-}
    lawCommutativity :: t -> Operation t -> Operation t -> ()


-- JP: CRDT monad? 


