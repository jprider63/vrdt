module Kyowon.Reflex.VRDT.CausalTree where

import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Fix (MonadFix)
-- import qualified Data.Text.Zipper as Z
import           Data.Align (align)
import qualified Data.List as List
import qualified Data.Text.Zipper as Z
import           Data.These (These(..))
import           Data.Witherable (catMaybes)
import qualified Graphics.Vty.Attributes as V
import qualified Graphics.Vty.Image as V
import qualified Graphics.Vty.Input as V
import           Reflex (
                          Event
                        , Reflex
                        , Dynamic
                        , MonadHold
                        , MonadSample
                        , Performable
                        , PerformEvent
                        , attach
                        , current
                        -- , ffor
                        , holdDyn
                        -- , holdUniqDyn
                        , sample
                        -- , traceEvent
                        , updated
                        )
import           Reflex.Vty.Widget ( VtyWidget
                                   , ImageWriter(..))
import qualified Reflex.Vty.Widget as V
-- import qualified Reflex.Vty.Widget.Input.Text as V
import           VRDT.CausalTree (CausalTree(..), preorder, extractLetter, CausalTreeAtom(..), CausalTreeWeave(..), CausalTreeLetter(..), CausalTreeOp(..))
-- import           VRDT.Class (VRDT(..))

import           Kyowon.Core.Types (UTCTimestamp(..))
import           Kyowon.Reflex.Client (KyowonMonad(..))
import           Kyowon.Reflex.Time (sampleMonotonicTimeWith')

data CausalTreeInput t id a = CausalTreeInput {
    causalTreeInputOperations :: Event t (CausalTreeOp id a)
    -- causalTreeInputOperations :: Event t (Operation (CausalTree id a))
  -- , Dynamic t (CausalTree id a)
  }


-- Every time the input dynamic fires, update the output dynamic (as a function of its previous value too).
-- Every time the event fires, update the output dynamic as a function of its current value and the event's value.

foldDyn' :: (a -> a -> a) -> Dynamic t a -> (a -> b -> a) -> Event t b -> Dynamic t a
foldDyn' = undefined


-- JP: I don't know if this works. Might need to use foldDyn of (,)
-- prevDyn d = holdDyn Nothing (Just <$> updated d)

-- eventToDynM d = holdDyn Nothing (Just <$> d)

-- JP: Should this take a dynamic of CausalTree?
causalTreeInput :: (MonadHold t m, MonadFix m, KyowonMonad m, KyowonMonad (Performable m), Reflex t, PerformEvent t m)
    => Dynamic t (CausalTree UTCTimestamp Char) -> VtyWidget t m (CausalTreeInput t UTCTimestamp Char)
causalTreeInput ct = do
    -- ct <- holdUniqDyn ct'

    i <- V.input
    -- iM <- eventToDynM i
    -- f <- V.focus
    -- dh <- V.displayHeight
    dw <- V.displayWidth

    -- ctInputD <- alignDynE ct i

    clientId <- lift getClientId

    -- rec
    --     let zipperOpPair = updateZipper <$> prevZipper <*> ctInputD <*> dh <*> dw
    --     let zipper = fst <$> zipperOpPair
    --     let opsE = catMaybes $ updated (snd <$> zipperOpPair)
    --     -- let cursorAtomId = zipperCursorIdentifier <$> zipper

    --     prevZipper <- prevDyn zipper

    -- let cursorAttrs = ffor f $ \x -> if x then V.cursorAttributes else V.defAttr

    -- let cursorAtomId = causalTreeAtomId . causalTreeWeaveAtom . causalTreeWeave <$> ct
    rec
      cursorAtomId <- (\a -> toAtomId <$> a <*> ct) <$> holdDyn Nothing (Just <$> opsE)
      opsE <- lift $ do
        let pairE = attach (current cursorAtomId) i
        catMaybes <$> sampleMonotonicTimeWith' (\(parentId, i) t -> toOperation parentId t clientId i) pairE



    let rows = (\ct w -> 
            let t = preorder ct in
            splitAtWidth w t
          ) <$> ct <*> dw
    let img = (pure . V.vertCat . fmap (V.horizCat . fmap (V.char V.defAttr . extractLetterUnsafe))) <$> rows

    -- tellImages $ pure $ map (V.char V.defAttr) "This is a causal tree input!!"
    tellImages $ current img

    -- return $ CausalTreeInput never -- TODO: Implement this XXX
    return $ CausalTreeInput opsE -- $ traceEvent "Operations" opsE

  where
    extractLetterUnsafe = maybe (error "extractLetterUnsafe: unreachable") id . extractLetter

    toAtomId Nothing ct = causalTreeAtomId $ causalTreeWeaveAtom $ causalTreeWeave ct -- Pull out the root id. Better way to do this?
    toAtomId (Just (CausalTreeOp _ (CausalTreeAtom atomId (CausalTreeLetter _)))) _ = atomId


    -- toSpan ct = ct

    -- JP: Do we need a zipper of the causal tree? So that we can delete backwards, etc?
    toOperation parentId t clientId action = 
        let atomLetterM = actionToLetter action in
        let atomId = UTCTimestamp t clientId in
        let atomM = CausalTreeAtom atomId <$> atomLetterM in
        CausalTreeOp parentId <$> atomM

    actionToLetter (V.EvKey (V.KChar c) []) = Just $ CausalTreeLetter c
    actionToLetter (V.EvKey V.KEnter [])    = Just $ CausalTreeLetter '\n'
    actionToLetter (V.EvKey V.KBS [])       = Just CausalTreeLetterDelete
    actionToLetter _                        = Nothing

    updateZipper Nothing ct h w = undefined
        -- JP: How do we tell if the ct updated here?
    updateZipper (Just prevZipper) ct h w = undefined

-- TODO: Improve this.
splitAtWidth :: Int -> [CausalTreeAtom t Char] -> [[CausalTreeAtom t Char]]
splitAtWidth n s = go [] s
  where
    go acc [] = List.reverse acc
    go acc s  = 
      let (line, s') = splitN 0 [] s in
      go (line:acc) s'

    -- splitN 0 [] = error "unreachable"
    splitN :: Int -> [CausalTreeAtom t Char] -> [CausalTreeAtom t Char] -> ([CausalTreeAtom t Char], [CausalTreeAtom t Char])
    splitN m acc []         = (List.reverse acc, [])
    splitN m acc s | m >= n = (List.reverse acc, s)
    splitN m acc (a:s)      = case extractLetter a of
      Nothing   -> splitN m acc s
      Just '\n' -> (List.reverse acc, s)
      Just c    -> splitN (m + Z.charWidth c) (a:acc) s

      
    
    
    


-- TODO: Move to Reflex?
alignDynE :: (Reflex t, MonadSample t m, MonadHold t m) => Dynamic t a -> Event t b -> m (Dynamic t (These a b))
alignDynE d e = do
    d0 <- sample (current d)
    let theseE = align (updated d) e

    holdDyn (This d0) theseE


        

