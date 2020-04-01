module Kyowon.Reflex.VRDT.CausalTree where

import           Control.Monad.Trans.Class (lift)
-- import qualified Data.Text.Zipper as Z
import           Data.Witherable (catMaybes)
import qualified Graphics.Vty.Attributes as V
import qualified Graphics.Vty.Image as V
import qualified Graphics.Vty.Input as V
import           Reflex (
                          Event
                        , Reflex
                        , Dynamic
                        , Performable
                        , PerformEvent
                        , attach
                        , current
                        -- , ffor
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



-- JP: Should this take a dynamic of CausalTree?
causalTreeInput :: (KyowonMonad m, KyowonMonad (Performable m), Reflex t, PerformEvent t m)
    => Dynamic t (CausalTree UTCTimestamp Char) -> VtyWidget t m (CausalTreeInput t UTCTimestamp Char)
causalTreeInput ct = do
    -- ct <- holdUniqDyn ct'

    i <- V.input
    -- f <- V.focus
    -- dh <- V.displayHeight
    -- dw <- V.displayWidth

    clientId <- lift getClientId

    -- let zipper = toZipper <$> ct <*> dh <*> dw
    -- let cursorAtomId = zipperCursorIdentifier <$> zipper
    let cursorAtomId = causalTreeAtomId . causalTreeWeaveAtom . causalTreeWeave <$> ct

    -- let cursorAttrs = ffor f $ \x -> if x then V.cursorAttributes else V.defAttr

    opsE <- lift $ do
        let pairE = attach (current cursorAtomId) i
        catMaybes <$> sampleMonotonicTimeWith' (\(parentId, i) t -> toOperation parentId t clientId i) pairE



    -- let rows = toSpan <$> ct
    let img = ((:[]) . V.horizCat . fmap (V.char V.defAttr) . extractLetter . preorder) <$> ct

    -- tellImages $ pure $ map (V.char V.defAttr) "This is a causal tree input!!"
    tellImages $ (:[]) . V.vertCat <$> current img

    -- return $ CausalTreeInput never -- TODO: Implement this XXX
    return $ CausalTreeInput opsE

  where
    -- toSpan ct = ct

    -- JP: Do we need a zipper of the causal tree? So that we can delete backwards, etc?
    toOperation parentId t clientId action = 
        let atomLetterM = actionToLetter action in
        let atomId = UTCTimestamp t clientId in
        let atomM = CausalTreeAtom atomId <$> atomLetterM in
        CausalTreeOp parentId <$> atomM

    actionToLetter (V.EvKey (V.KChar c) []) = Just $ CausalTreeLetter c
    actionToLetter (V.EvKey V.KBS [])       = Just CausalTreeLetterDelete
    actionToLetter _                        = Nothing


        

