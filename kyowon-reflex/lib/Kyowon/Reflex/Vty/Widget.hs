module Kyowon.Reflex.Vty.Widget where

import           Control.Monad.NodeId
import qualified Graphics.Vty as V
import           Kyowon.Core.Types (ClientId)
import           Reflex
import           Reflex.Vty.Host
import           Reflex.Vty.Widget (VtyWidgetCtx(..), VtyWidget(..), runVtyWidget, tellImages)

import           Kyowon.Reflex.Client (NextId, runKyowonT, KyowonMonad)

-- http://hackage.haskell.org/package/reflex-vty-0.1.2.0/docs/src/Reflex.Vty.Widget.html#mainWidgetWithHandle
-- | Sets up the top-level context for a 'VtyWidget' and runs it with that context
mainWidgetWithHandle
  :: V.Vty
  -> ClientId
  -> NextId
  -> (forall t m. (MonadVtyApp t m, MonadNodeId m, KyowonMonad m, KyowonMonad (Performable m)) => VtyWidget t m (Event t ()))
  -- -> (forall t m. (MonadVtyApp t (KyowonT m), MonadNodeId (KyowonT m)) => VtyWidget t m (Event t ()))
  -> IO ()
mainWidgetWithHandle vty clientId nextId child =
  runVtyAppWithHandle vty $ \dr0 inp -> do
    size <- holdDyn dr0 $ fforMaybe inp $ \case
      V.EvResize w h -> Just (w, h)
      _ -> Nothing
    let inp' = fforMaybe inp $ \case
          V.EvResize {} -> Nothing
          x -> Just x
    let ctx = VtyWidgetCtx
          { _vtyWidgetCtx_width = fmap fst size
          , _vtyWidgetCtx_height = fmap snd size
          , _vtyWidgetCtx_input = inp'
          , _vtyWidgetCtx_focus = constDyn True
          }
    (shutdown, images) <- runNodeIdT $ runKyowonT clientId nextId $ runVtyWidget ctx $ do
      tellImages . ffor (current size) $ \(w, h) -> [V.charFill V.defAttr ' ' w h]
      child
    return $ VtyResult
      { _vtyResult_picture = fmap (V.picForLayers . reverse) images
      , _vtyResult_shutdown = shutdown
      }

-- | Like 'mainWidgetWithHandle', but uses a default vty configuration
mainWidget
  :: ClientId
  -> NextId
  -> (forall t m. (MonadVtyApp t m, MonadNodeId m, KyowonMonad m, KyowonMonad (Performable m)) => VtyWidget t m (Event t ()))
  -> IO ()
mainWidget clientId nextId child = do
  vty <- getDefaultVty
  mainWidgetWithHandle vty clientId nextId child


