module Kyowon.Reflex.VRDT.CausalTree (
    CausalTreeInput(..)
  , causalTreeInput
  ) where

import           Control.Monad.Trans.Class (lift)
import           Control.Monad.Fix (MonadFix)
-- import qualified Data.Text.Zipper as Z
import           Data.Align (align)
import qualified Data.List as List
import           Data.List.NonEmpty (NonEmpty(..))
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
                        , attachWith
                        , current
                        -- , ffor
                        , holdDyn
                        -- , holdUniqDyn
                        , sample
                        -- , traceEvent
                        , updated
                        )
import qualified Reflex.Vty.Host as V
import           Reflex.Vty.Widget ( VtyWidget
                                   , ImageWriter(..))
import qualified Reflex.Vty.Widget as V
-- import qualified Reflex.Vty.Widget.Input.Text as V
import           VRDT.CausalTree (CausalTree(..), preorder, extractLetter, CausalTreeAtom(..), CausalTreeWeave(..), CausalTreeLetter(..), CausalTreeOp(..), rootAtomId)
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

causalTreeInput :: (MonadHold t m, MonadFix m, KyowonMonad m, KyowonMonad (Performable m), Reflex t, PerformEvent t m)
    => Dynamic t (CausalTree UTCTimestamp Char) -> VtyWidget t m (CausalTreeInput t UTCTimestamp Char)
causalTreeInput ct = do
    -- ct <- holdUniqDyn ct'

    i <- V.input
    -- iM <- eventToDynM i
    -- f <- V.focus
    dh <- V.displayHeight
    dw <- V.displayWidth

    clientId <- lift getClientId

    let rows = (\ct w -> 
            let t = preorder ct in
            splitAtWidth w t
          ) <$> ct <*> dw
    let ctRootId = rootAtomId <$> ct

    -- rec
    --     let zipperOpPair = updateZipper <$> prevZipper <*> ctInputD <*> dh <*> dw
    --     let zipper = fst <$> zipperOpPair
    --     let opsE = catMaybes $ updated (snd <$> zipperOpPair)
    --     -- let cursorAtomId = zipperCursorIdentifier <$> zipper

    --     prevZipper <- prevDyn zipper

    -- let cursorAttrs = ffor f $ \x -> if x then V.cursorAttributes else V.defAttr

    let scrollTop = pure 0
    rec
      
      cursorAtomIdMD <- eventToDynM cursorAtomIdE
      let cursorAtomId = toAtomId <$> cursorAtomIdMD <*> ctRootId
      let rightOfId = rightOf <$> cursorAtomId <*> ctRootId <*> rows

      opsE <- lift $ do
        let pairE = attach (current cursorAtomId) i
        catMaybes <$> sampleMonotonicTimeWith' (\(parentId, i) t -> toOperation parentId t clientId i) pairE

      let cursorAndRowsAndCt = (,,,) <$> cursorAtomId <*> rows <*> ctRootId <*> rightOfId
      let opsAndInputE = align opsE i
      let cursorAtomIdE = attachWith toCursorId (current cursorAndRowsAndCt) opsAndInputE


    let img = (\rows dh rightOfId scrollTop -> 
            let rows' = take dh $ drop scrollTop rows in
            -- let rootId = rootAtomId ct in
            displayRows rightOfId rows
          ) <$> rows <*> dh <*> rightOfId <*> scrollTop

    tellImages $ current img

    return $ CausalTreeInput opsE -- $ traceEvent "Operations" opsE

  where
    toAtomId (Just cursorId) _ = cursorId
    toAtomId _ rootId          = rootId

    toCursorId :: (UTCTimestamp, [[(UTCTimestamp, Char)]], UTCTimestamp, Maybe UTCTimestamp) -> These (CausalTreeOp UTCTimestamp Char) V.VtyEvent -> UTCTimestamp
    toCursorId (currentCursorId, rows, rootId, rightOf) op = toCursorId' op currentCursorId rows rootId rightOf

    toCursorId' :: These (CausalTreeOp UTCTimestamp Char) V.VtyEvent -> UTCTimestamp -> [[(UTCTimestamp,Char)]] -> UTCTimestamp -> Maybe UTCTimestamp -> UTCTimestamp
    toCursorId' (This op) _ rows rootId _ = opToCursorId op rows rootId
    toCursorId' (These op _) _ rows rootId _ = opToCursorId op rows rootId
    toCursorId' (That i) currentCursorId rows rootId rightOf = inputToCursorId i currentCursorId rows rootId rightOf

    opToCursorId (CausalTreeOp parentId atom) rows rootId = case causalTreeAtomLetter atom of
      CausalTreeLetter _ -> causalTreeAtomId atom
      CausalTreeLetterRoot -> rootId
      CausalTreeLetterDelete -> leftOf parentId rows rootId

    inputToCursorId (V.EvKey V.KLeft []) currentCursorId rows rootId _ = leftOf currentCursorId rows rootId
    inputToCursorId (V.EvKey V.KRight []) currentCursorId rows rootId (Just rightId) = rightId
    inputToCursorId (V.EvKey V.KRight []) currentCursorId rows rootId Nothing = currentCursorId
    inputToCursorId (V.EvKey V.KUp []) currentCursorId rows rootId _ = upOf currentCursorId rows rootId
    inputToCursorId (V.EvKey V.KDown []) currentCursorId rows rootId _ = downOf currentCursorId rows rootId
    inputToCursorId _ currentCursorId rows rootId _ = currentCursorId
    
    downOf _ _ rootId = rootId -- TODO




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


leftOf :: UTCTimestamp -> [[(UTCTimestamp, a)]] -> UTCTimestamp -> UTCTimestamp
leftOf atomId rows rootId = leftOfRows rootId rows
  where
    leftOfRows _last [] = rootId
    leftOfRows last (row:rows) = case leftOfRow last row of
      Left last' -> leftOfRows last' rows
      Right left -> left
    
    leftOfRow last []    = Left last
    leftOfRow last (h:t) = 
      let hId = fst h in
      if hId == atomId then 
        Right last 
      else 
        leftOfRow hId t

rightOf :: UTCTimestamp -> UTCTimestamp -> [[(UTCTimestamp, a)]] -> Maybe UTCTimestamp
rightOf targetId rootId rows | targetId == rootId = nextOfRows rows
rightOf _ _ []                                    = Nothing
rightOf targetId rootId (row:rows)                = case rightOfRow row of
  Just remaining ->
    nextOfRows (remaining:rows)
  Nothing ->
    rightOf targetId rootId rows

  where
    rightOfRow []    = Nothing
    rightOfRow (h:t) = if fst h == targetId then Just t else rightOfRow t

nextOfRows []          = Nothing
nextOfRows ([]:t)      = nextOfRows t
nextOfRows ((h:_):_)   = Just $ fst h
  
-- upOf :: UTCTimestamp -> 
upOf targetId rows rootId = upOfRows rootId (targetId:|[]) rows
  where
    upOfRows _ _ [] = rootId -- targetId
    upOfRows lastId prevRow (row:rows) = 
      let row' = lastId:|(map fst row) in
      case findIndexOrLast (\c -> c == targetId) row' of
        Left tail ->
          upOfRows tail row' rows
        Right i ->
          takeAtOrSecondToLast i prevRow
          
          
takeAtOrSecondToLast i (x:|xs) = go i x xs
  where
    go c prev []     = prev
    go 0 prev [x]    = x
    go c prev [_]    = prev
    go 0 prev (x:_)  = x
    go c prev (x:xs) = go (c-1) x xs

findIndexOrLast f (x:|xs) = go 0 x xs
  where
    go c prev [] = Left prev
    go c prev (x:xs) = if f x then Right c else go (c+1) x xs
        




-- TODO: Improve this.
splitAtWidth :: Int -> [CausalTreeAtom t Char] -> [[(t, Char)]]
splitAtWidth n s = go [] s
  where
    go acc [] = List.reverse acc
    go acc s  = 
      let (line, s') = splitN 0 [] s in
      go (line:acc) s'

    -- splitN 0 [] = error "unreachable"
    splitN :: Int -> [(t, Char)] -> [CausalTreeAtom t Char] -> ([(t, Char)], [CausalTreeAtom t Char])
    splitN m acc []         = (List.reverse acc, [])
    splitN m acc s | m >= n = (List.reverse acc, s)
    splitN m acc (a:s)      = case extractLetter a of
      Nothing   -> splitN m acc s
      Just '\n' -> (List.reverse ((t, ' '):acc), s) -- JP: How should we handle newlines?
      Just c    -> splitN (m + Z.charWidth c) ((t, c):acc) s

      where
        t = causalTreeAtomId a


eventToDynM :: (Reflex t, MonadHold t m) => Event t a -> m (Dynamic t (Maybe a))
eventToDynM e = holdDyn Nothing (Just <$> e)
      
    
    
    


-- -- TODO: Move to Reflex?
-- alignDynE :: (Reflex t, MonadSample t m, MonadHold t m) => Dynamic t a -> Event t b -> m (Dynamic t (These a b))
-- alignDynE d e = do
--     d0 <- sample (current d)
--     let theseE = align (updated d) e
-- 
--     holdDyn (This d0) theseE


        
-- displayRows :: 
displayRows hoverIdM rows = 
  pure $ V.vertCat $ fmap (V.horizCat . fmap displayChar) rows

-- displayRows cursorAtomId lastId rows = 
--   List.foldl' displayRows' (lastId, [])
-- 
-- 
-- 
  where
    displayChar (atomId, c) = 
      let attr = if Just atomId == hoverIdM then 
              V.withStyle V.defAttr V.reverseVideo 
            else 
              V.defAttr 
      in
      V.char attr c
--     displayRows' cursorAtomId lastId rows = 
-- 

      -- let attr = V.defAttr in
      -- let i = V.char attr c in
      -- if atomId == cursorAtomId then
      --     V.char attr c `V.horizJoin` V.char attr '|'
      --   else
      --     i


