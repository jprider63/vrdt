
module VRDT.CausalTree where

import           Data.List (foldl')
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Maybe (maybeToList)
import           Data.Time.Clock (UTCTime)

import           VRDT.Types

data CausalTree a = CausalTree {
    causalTreeWeave   :: CausalTreeWeave a
  -- , CausalTreeList :: [a] -- JP: Should we add this field to cache the list representation?
  , causalTreePending :: Map AtomId [CausalTreeAtom a]
  }

data CausalTreeOp a = CausalTreeOp {
    causalTreeOpParent :: AtomId
  , causalTreeOpId     :: AtomId
  , causalTreeLetter   :: CausalTreeLetter a    -- Invariant: Cannot be CausalTreeLetterRoot
  }

data AtomId = AtomId UTCTime ClientId

data CausalTreeAtom a = CausalTreeAtom {
    causalTreeAtomId     :: AtomId
  , causalTreeAtomLetter :: CausalTreeLetter a
  }

data CausalTreeLetter a = 
    CausalTreeLetter a
  | CausalTreeLetterDelete
  | CausalTreeLetterRoot -- | Root node. Should only be used as the initial node on creation.

data CausalTreeWeave a = 
    CausalTreeWeaveNode (CausalTreeAtom a) [CausalTreeWeave a]

apply :: CausalTree a -> CausalTreeOp a -> CausalTree a
apply ct (CausalTreeOp parentId opId letter) = 
    let atom = CausalTreeAtom opId letter in
    applyAtom ct parentId atom

  where

    applyAtom :: CausalTree a -> AtomId -> CausalTreeAtom a -> CausalTree a
    applyAtom (CausalTree weave pending) parentId atom = case insertInWeave weave parentId atom of
        Nothing -> 
            -- ParentId not seen yet, so mark as pending.
            let pending' = Map.insertWith (++) parentId [atom] pending in
            CausalTree weave pending'
        Just weave' -> 
            -- Inserted, so apply any pending operations that may depend on this atom.
            let opId = causalTreeAtomId atom in
            let (pendingAtomsM, pending') = Map.updateLookupWithKey (\_ _ -> Nothing) opId pending in
            let ct = CausalTree weave' pending' in
            foldl' (\ct atom -> applyAtom ct opId atom) ct $ maybeToList pendingAtomsM

