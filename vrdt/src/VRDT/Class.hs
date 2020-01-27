{-@ LIQUID "--reflection" @-}

{-# LANGUAGE TypeFamilies, TypeFamilyDependencies #-}

module VRDT.Class where

-- | Class for (operation based) verified conflict-free replicated datatypes.
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

    {-@ lawNonCausal :: x : t -> op1 : Operation t -> op2 : Operation t -> {enabled (apply x op1) op2 <=> enabled (apply x op2) op1} @-}
    lawNonCausal :: t -> Operation t -> Operation t -> ()

{-@ reflect enabled2 @-}
enabled2 :: VRDT t => t -> Operation t -> Operation t -> Bool
enabled2 x op1 op2 = enabled x op1 && enabled x op2  && enabled (apply x op1) op2 && enabled (apply x op2) op1



-- | Class for (state based) verified conflict-free replicated datatypes.
-- Must be a monotonic semilattice.
class SVRDT t where
    canFlowTo :: t -> t -> Bool
    join :: t -> t -> t
    -- bot  :: t

    {-@ lawJoin :: z : t -> x : t -> y : t -> w : t -> {z == join x y => (canFlowTo x z && canFlowTo y z && ((canFlowTo x w && canFlowTo y w) => canFlowTo z w))} @-}
    lawJoin :: t -> t -> t -> t -> ()
    -- {-@ lawBot  :: x : t -> { canFlowTo Labels.bot x } @-}
    -- lawBot  :: t -> ()

    {-@ lawFlowReflexivity :: t : t -> {v : () | canFlowTo t t} @-}
    lawFlowReflexivity :: t -> ()
    {-@ lawFlowAntisymmetry :: a : t -> {b : t | canFlowTo a b && canFlowTo b a} -> {v : () | a == b} @-}
    lawFlowAntisymmetry :: t -> t -> ()
    {-@ lawFlowTransitivity :: a:t -> b:t -> c:t -> {(canFlowTo a b && canFlowTo b c) => canFlowTo a c} @-}
    lawFlowTransitivity :: t -> t -> t -> ()

    -- JP: monotonic? We should be able to derive from other laws?

-- JP: CRDT monad? 


