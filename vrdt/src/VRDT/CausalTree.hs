
module VRDT.CausalTree where

import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Time.Clock (UTCTime)

import           VRDT.Types

data CausalTree a = CausalTree {
    causalTreeWeave   :: CausalTreeWeave a
  -- , CausalTreeList :: [a] -- JP: Should we add this field to cache the list representation?
  , causalTreePending :: Map AtomId [CausalTreeAtom a]
  }

data CausalTreeOp a = CausalTreeOp {
    causalTreeOpParent :: AtomId
  , causalTreeOpAtom   :: CausalTreeAtom a    -- Invariant: Cannot be CausalTreeLetterRoot
  }

data AtomId = AtomId UTCTime ClientId
    deriving (Eq, Ord)

data CausalTreeAtom a = CausalTreeAtom {
    causalTreeAtomId     :: AtomId
  , causalTreeAtomLetter :: CausalTreeLetter a
  }

data CausalTreeLetter a = 
    CausalTreeLetter a
  | CausalTreeLetterDelete
  | CausalTreeLetterRoot -- | Root node. Should only be used as the initial node on creation.

data CausalTreeWeave a = CausalTreeWeave {
    causalTreeWeaveAtom     :: CausalTreeAtom a
  , causalTreeWeaveChildren :: [CausalTreeWeave a]
  }

apply :: CausalTree a -> CausalTreeOp a -> CausalTree a
apply ct (CausalTreeOp parentId atom) = applyAtom ct parentId atom

  where

    applyAtom :: CausalTree a -> AtomId -> CausalTreeAtom a -> CausalTree a
    applyAtom (CausalTree !weave !pending) parentId atom = case insertInWeave weave parentId atom of
        Nothing -> 
            -- ParentId not seen yet, so mark as pending.
            let pending' = Map.insertWith (++) parentId [atom] pending in
            CausalTree weave pending'

        Just weave' -> 
            -- Inserted, so apply any pending operations that may depend on this atom.
            let opId = causalTreeAtomId atom in
            let (pendingAtomsM, pending') = Map.updateLookupWithKey (\_ _ -> Nothing) opId pending in
            let ct = CausalTree weave' pending' in
            List.foldl' (\ct atom -> applyAtom ct opId atom) ct $ concat pendingAtomsM


    insertInWeave :: CausalTreeWeave a -> AtomId -> CausalTreeAtom a -> Maybe (CausalTreeWeave a)
    insertInWeave (CausalTreeWeave currentAtom currentChildren) parentId atom
        -- Is the current atom the target parent?
        | causalTreeAtomId currentAtom == parentId = 
            let children = insertAtom currentChildren atom in
            Just $ CausalTreeWeave currentAtom children
        | otherwise = 
            let childrenM = insertInWeaveChildren currentChildren parentId atom in
            CausalTreeWeave currentAtom <$> childrenM


    insertInWeaveChildren :: [CausalTreeWeave a] -> AtomId -> CausalTreeAtom a -> Maybe [CausalTreeWeave a]
    insertInWeaveChildren [] _ _ = Nothing
    insertInWeaveChildren (w:ws) parentId atom = case insertInWeave w parentId atom of
        Nothing ->
            (w:) <$> insertInWeaveChildren ws parentId atom
        Just w' ->
            Just $ w':ws

    insertAtom :: [CausalTreeWeave a] -> CausalTreeAtom a -> [CausalTreeWeave a]
    insertAtom [] atom = [CausalTreeWeave atom []]
    insertAtom l@(w:ws) atom 
      | atom `atomGreaterThan` causalTreeWeaveAtom w = CausalTreeWeave atom []:l
      | otherwise                                    = w:insertAtom ws atom


-- Compare whether an atom is greater than another atom, prioritizing CausalTreeLetterDelete.
atomGreaterThan :: CausalTreeAtom a -> CausalTreeAtom a -> Bool
atomGreaterThan (CausalTreeAtom a1 CausalTreeLetterRoot) (CausalTreeAtom a2 CausalTreeLetterRoot) = a1 > a2
atomGreaterThan (CausalTreeAtom _ CausalTreeLetterRoot) (CausalTreeAtom _ _) = True
atomGreaterThan (CausalTreeAtom a1 CausalTreeLetterDelete) (CausalTreeAtom a2 CausalTreeLetterDelete) = a1 > a2
atomGreaterThan (CausalTreeAtom _ CausalTreeLetterDelete) (CausalTreeAtom _ _) = True
atomGreaterThan (CausalTreeAtom a1 (CausalTreeLetter _)) (CausalTreeAtom a2 (CausalTreeLetter _)) = a1 > a2


