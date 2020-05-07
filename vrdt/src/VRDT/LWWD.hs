{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}

module VRDT.LWW where

#ifdef NotLiquid
import           Data.Aeson (FromJSON(..), ToJSON(..), (.=), (.:))
import qualified Data.Aeson as Aeson
#endif

import           VRDT.ClassD
import           VRDT.Types

{-@
data LWW t a = LWW {
    lwwTime  :: t
  , lwwValue :: a
  }
@-}
data LWW t a = LWW {
    lwwTime  :: t
  , lwwValue :: a
  }

-- type LWWU a = LWW UTCTimestamp a

#ifdef NotLiquid
instance (FromJSON t, FromJSON a) => FromJSON (LWW t a) where
    parseJSON = Aeson.withObject "LWW" $ \o -> 
        LWW <$> o .: "time" <*> o .: "value"

instance (ToJSON t, ToJSON a) => ToJSON (LWW t a) where
    toJSON (LWW t a) = Aeson.object [
        "time" .= t
      , "value" .= a
      ]
#endif
type instance Operation (LWW t a) = LWW t a


{-@ reflect cenabledLWW @-}
cenabledLWW :: Ord t => LWW t a -> Operation (LWW t a) -> Bool
cenabledLWW (LWW t1 _) (LWW t2 _) = t1 /= t2


{-@ reflect capplyLWW @-}
capplyLWW :: Ord t => LWW t a -> Operation (LWW t a) -> LWW t a
capplyLWW l1@(LWW t1 _) l2@(LWW t2 _) 
     | t1 > t2   = l1
     | otherwise = l2

{-@ clawCommutativityLWW :: Ord t => x : (LWW t a) -> op1 : Operation (LWW t a) -> op2 : Operation (LWW t a) -> {(cenabledLWW x op1 && cenabledLWW x op2  && cenabledLWW (capplyLWW x op1) op2 && cenabledLWW (capplyLWW x op2) op1) => capplyLWW (capplyLWW x op1) op2 == capplyLWW (capplyLWW x op2) op1} @-}
clawCommutativityLWW :: Ord t => LWW t a -> Operation (LWW t a) -> Operation (LWW t a) -> ()
clawCommutativityLWW _ _ _ = ()


{-@ clawNonCausalLWW :: Ord t => x : (LWW t a) -> {op1 : Operation (LWW t a) | cenabledLWW x op1} -> {op2 : Operation (LWW t a) | cenabledLWW x op2} -> {cenabledLWW (capplyLWW x op1) op2 <=> cenabledLWW (capplyLWW x op2) op1} @-}
clawNonCausalLWW :: Ord t => LWW t a -> Operation (LWW t a) -> Operation (LWW t a) -> ()
clawNonCausalLWW _ _ _ =()

fVRDT_LWW :: Ord t => VRDT (LWW t a)
fVRDT_LWW = CVRDT capplyLWW cenabledLWW clawCommutativityLWW clawNonCausalLWW



-- {-@ reflect applyLWW @-}
-- applyLWW :: Ord t => LWW t a -> LWW t a -> LWW t a
-- applyLWW l1@(LWW t1 _) l2@(LWW t2 _) 
--   | t1 > t2   = l1
--   | otherwise = l2
-- 
-- {-@ reflect enabledLWW @-}
-- enabledLWW :: Eq t => LWW t a -> LWW t a -> Bool
-- enabledLWW (LWW t1 _) (LWW t2 _) = t1 /= t2
-- 
-- {-@ reflect enabled2LWW @-}
-- enabled2LWW :: Ord t => LWW t a -> LWW t a -> LWW t a -> Bool
-- enabled2LWW x op1 op2 = enabledLWW x op1 && enabledLWW x op2  && enabledLWW (applyLWW x op1) op2 && enabledLWW (applyLWW x op2) op1
-- 
-- {-@ ple lawCommutativityLWW @-}
-- {-@ lawCommutativityLWW :: Ord t => x : LWW t a -> op1 : LWW t a -> op2 : LWW t a -> {enabled2LWW x op1 op2 => applyLWW op2 (applyLWW op1 x) == applyLWW op1 (applyLWW op2 x)} @-}
-- lawCommutativityLWW :: Ord t => LWW t a -> LWW t a -> LWW t a -> ()
-- lawCommutativityLWW lww op1 op2 = ()
-- 
-- {-@ lawNonCausal :: Ord t => x : LWW t a -> {op1 : LWW t a | enabledLWW x op1} -> {op2 : LWW t a | enabledLWW x op2} -> {enabledLWW (applyLWW x op1) op2 <=> enabledLWW (applyLWW x op2) op1} @-}
-- lawNonCausal :: Ord t => LWW t a -> LWW t a -> LWW t a -> ()
-- lawNonCausal lww op1 op2 = ()
