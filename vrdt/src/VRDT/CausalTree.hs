
module VRDT.CausalTree where

import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
import           Data.Time.Clock (UTCTime)

import           VRDT.Types

-- Identifier for `CausalTree` is abstract, but you probably want to use `UTCTimestamp`.
data CausalTree id a = CausalTree {
    causalTreeWeave   :: CausalTreeWeave id a
  -- , CausalTreeList :: [a] -- JP: Should we add this field to cache the list representation?
  , causalTreePending :: Map id [CausalTreeAtom id a]
  }
  deriving (Show)

data CausalTreeOp id a = CausalTreeOp {
    causalTreeOpParent :: id
  , causalTreeOpAtom   :: CausalTreeAtom id a    -- Invariant: Cannot be CausalTreeLetterRoot
  }
  deriving (Show)

-- -- JP: Maybe we should leave this abstract.
-- data AtomId = AtomId UTCTime ClientId
--   deriving (Show, Eq, Ord)

data CausalTreeAtom id a = CausalTreeAtom {
    causalTreeAtomId     :: id
  , causalTreeAtomLetter :: CausalTreeLetter a
  }
  deriving (Show)

data CausalTreeLetter a = 
    CausalTreeLetter a
  | CausalTreeLetterDelete
  | CausalTreeLetterRoot -- | Root node. Should only be used as the initial node on creation.
  deriving (Show)

data CausalTreeWeave id a = CausalTreeWeave {
    causalTreeWeaveAtom     :: CausalTreeAtom id a
  , causalTreeWeaveChildren :: [CausalTreeWeave id a]
  }
  deriving (Show)

apply :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTree id a
apply ct (CausalTreeOp parentId atom) = applyAtom ct parentId atom

  where

    -- applyAtom :: CausalTree a -> AtomId -> CausalTreeAtom a -> CausalTree a
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


    -- insertInWeave :: CausalTreeWeave a -> AtomId -> CausalTreeAtom a -> Maybe (CausalTreeWeave a)
    insertInWeave (CausalTreeWeave currentAtom currentChildren) parentId atom
        -- Is the current atom the target parent?
        | causalTreeAtomId currentAtom == parentId = 
            let children = insertAtom currentChildren atom in
            Just $ CausalTreeWeave currentAtom children
        | otherwise = 
            let childrenM = insertInWeaveChildren currentChildren parentId atom in
            CausalTreeWeave currentAtom <$> childrenM


    -- insertInWeaveChildren :: [CausalTreeWeave a] -> AtomId -> CausalTreeAtom a -> Maybe [CausalTreeWeave a]
    insertInWeaveChildren [] _ _ = Nothing
    insertInWeaveChildren (w:ws) parentId atom = case insertInWeave w parentId atom of
        Nothing ->
            (w:) <$> insertInWeaveChildren ws parentId atom
        Just w' ->
            Just $ w':ws

    -- insertAtom :: [CausalTreeWeave a] -> CausalTreeAtom a -> [CausalTreeWeave a]
    insertAtom [] atom = [CausalTreeWeave atom []]
    insertAtom l@(w:ws) atom 
      | atom `atomGreaterThan` causalTreeWeaveAtom w = CausalTreeWeave atom []:l
      | otherwise                                    = w:insertAtom ws atom


-- | Preorder traversal of a `CausalTree`. Returns atoms in reverse order.
-- Invariant: `CausalTreeLetter` is the only constructor in the returned list.
-- O(n)
--
-- JP: Can we efficiently return results in the correct order by doing a foldr?
preorder :: CausalTree id a -> [CausalTreeAtom id a]
preorder = go [] . causalTreeWeave
 where
  go acc (CausalTreeWeave _atom ws) = 
    let (_, acc') = List.foldl' visitor (False, acc) ws in
    List.foldl' go acc' ws 

  visitor (deleted, acc) (CausalTreeWeave atom _ws) = case causalTreeAtomLetter atom of
    CausalTreeLetterDelete ->
      -- Skip if already deleted.
      if deleted then
        (deleted, acc)
      else
        (True, pop acc)
    
    CausalTreeLetterRoot ->
      -- Should be unreachable.
      (deleted, acc)

    CausalTreeLetter _ ->
      (deleted, atom:acc)
  
  pop = List.drop 1
      


-- Compare whether an atom is greater than another atom, prioritizing CausalTreeLetterDelete.
atomGreaterThan :: Ord id => CausalTreeAtom id a -> CausalTreeAtom id a -> Bool
atomGreaterThan (CausalTreeAtom a1 CausalTreeLetterRoot) (CausalTreeAtom a2 CausalTreeLetterRoot)     = a1 > a2
atomGreaterThan (CausalTreeAtom _ CausalTreeLetterRoot) (CausalTreeAtom _ _)                          = True
atomGreaterThan (CausalTreeAtom a1 CausalTreeLetterDelete) (CausalTreeAtom a2 CausalTreeLetterDelete) = a1 > a2
atomGreaterThan (CausalTreeAtom _ CausalTreeLetterDelete) (CausalTreeAtom _ _)                        = True
atomGreaterThan (CausalTreeAtom a1 (CausalTreeLetter _)) (CausalTreeAtom a2 (CausalTreeLetter _))     = a1 > a2
atomGreaterThan (CausalTreeAtom a1 (CausalTreeLetter _)) (CausalTreeAtom a2 _)                        = False


