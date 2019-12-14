module VRDT.Class where

-- | Class for verified conflict-free replicated datatypes.
class VRDT t where
    type Operation t = op | op -> t

    apply :: t -> Operation t -> t


