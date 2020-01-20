{-@ LIQUID "--reflection" @-}

{-# LANGUAGE TypeFamilies, TypeFamilyDependencies #-}

module VRDT.Class where

-- | Class for verified (operation based) conflict-free replicated datatypes.
class VRDT t where
    -- | Type that represents operations on `t`.
    type Operation t = op | op -> t

    -- | Apply an operation.
    apply :: t -> Operation t -> t

    -- | Whether an operation is enabled.
    enabled :: t -> Operation t -> Bool

    -- | Commutativity law.
    {-@ lawCommutativity :: x : t -> op1 : Operation t -> op2 : Operation t -> {enabled2 x op1 op2 => apply (apply op1 x) op2 == apply (apply op2 x) op1} @-}
    lawCommutativity :: t -> Operation t -> Operation t -> ()

{-@ reflect enabled2 @-}
enabled2 :: VRDT t => t -> Operation t -> Operation t -> Bool
enabled2 x op1 op2 = enabled x op1 && enabled x op2  && enabled (apply x op1) op2 && enabled (apply x op2) op1


-- JP: CRDT monad? 


