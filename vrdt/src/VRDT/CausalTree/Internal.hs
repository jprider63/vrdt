{-# LANGUAGE ScopedTypeVariables #-}

{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-@ LIQUID "--noadt" @-}
{-@ LIQUID "--no-termination" @-}
module VRDT.CausalTree.Internal where

#if NotLiquid
import           Data.Aeson (ToJSON(..), FromJSON(..), (.:), (.=))
import qualified Data.Aeson as Aeson
#endif

#if NotLiquid
import qualified Data.List as List
import           Data.Map (Map)
import qualified Data.Map as Map
#else
import qualified Liquid.Data.List as List
import           Liquid.Data.Maybe
import           Liquid.Data.Map (Map)
import qualified Liquid.Data.Map as Map
import           Liquid.Data.Map.Props
import           Prelude hiding (Maybe(..))
#endif
import           Data.Maybe (mapMaybe)
import           Data.Time.Clock (UTCTime)
import           VRDT.Types
import           VRDT.Internal
import           ProofCombinators
import           Liquid.ProofCombinators

-- Identifier for `CausalTree` is abstract, but you probably want to use `UTCTimestamp`.
{-@ data CausalTree id a = CausalTree {
    causalTreeWeave   :: CausalTreeWeave id a
  , causalTreePending :: Map id [CausalTreeAtom id a]
  }
@-}

data CausalTree id a = CausalTree {
    causalTreeWeave   :: CausalTreeWeave id a
  -- , CausalTreeList :: [a] -- JP: Should we add this field to cache the list representation?
  , causalTreePending :: Map id [CausalTreeAtom id a]
  }
  deriving (Show)

{-@ data CausalTreeOp id a = CausalTreeOp {
    causalTreeOpParent :: id
  , causalTreeOpAtom   :: CausalTreeAtom id a
}
@-}

data CausalTreeOp id a = CausalTreeOp {
    causalTreeOpParent :: id
  , causalTreeOpAtom   :: CausalTreeAtom id a    -- Invariant: Cannot be CausalTreeLetterRoot
  }
  deriving (Show)

-- -- JP: Maybe we should leave this abstract.
-- data AtomId = AtomId UTCTime ClientId
--   deriving (Show, Eq, Ord)
-- JP: Don't really need id if CausalTreeLetterRoot or CausalTreeLetterDelete?

{-@ data CausalTreeAtom id a = CausalTreeAtom {
    causalTreeAtomId     :: id
  , causalTreeAtomLetter :: CausalTreeLetter a
  }
@-}


data CausalTreeAtom id a = CausalTreeAtom {
    causalTreeAtomId     :: id
  , causalTreeAtomLetter :: CausalTreeLetter a
  }
  deriving (Show)

instance Eq id => Eq (CausalTreeAtom id a) where
    (CausalTreeAtom id _) == (CausalTreeAtom id' _) = id == id'
  
instance Ord id => Ord (CausalTreeAtom id a) where
    compare (CausalTreeAtom id _) (CausalTreeAtom id' _) = compare id id'

data CausalTreeLetter a = 
    CausalTreeLetter a
  | CausalTreeLetterDelete
  | CausalTreeLetterRoot -- | Root node. Should only be used as the initial node on creation.
  deriving (Show)



{-@
data CausalTreeWeave id a = CausalTreeWeave {
    causalTreeWeaveAtom     :: CausalTreeAtom id a
  , causalTreeWeaveChildren :: [CausalTreeWeave id a]
  }

@-}

data CausalTreeWeave id a = CausalTreeWeave {
    causalTreeWeaveAtom     :: CausalTreeAtom id a
  , causalTreeWeaveChildren :: [CausalTreeWeave id a]
  }
  deriving (Show)

{-@ measure causalTreeWeaveLength @-}
{-@ causalTreeWeaveLength :: CausalTreeWeave id a -> {v:Int | v > 0} @-}
causalTreeWeaveLength :: CausalTreeWeave id a -> Int
causalTreeWeaveLength (CausalTreeWeave id xs) = 1 + causalTreeWeaveLengthList xs

{-@ causalTreeWeaveLengthList :: [CausalTreeWeave id a] -> Nat @-}
{-@ measure causalTreeWeaveLengthList @-}
causalTreeWeaveLengthList :: [CausalTreeWeave id a] -> Int
causalTreeWeaveLengthList [] = 0
causalTreeWeaveLengthList (x:xs) = causalTreeWeaveLength x + causalTreeWeaveLengthList xs

-- {-@ reflect enabled @-}
-- -- Enabled if the id is unique (doesn't appear in the CausalTree).
-- enabled :: Ord id => CausalTree id a -> CausalTreeOp id a -> Bool
-- enabled (CausalTree weave pending) (CausalTreeOp _ (CausalTreeAtom id _)) = enabledWeave weave id && enabledLists (Map.toList pending) id
-- 
-- {-@ reflect enabledWeave @-}
-- enabledWeave :: Eq id => CausalTreeWeave id a -> id -> Bool
-- enabledWeave (CausalTreeWeave atom children) id = enabledAtom atom id && enabledChildren children id
-- 
-- {-@ reflect enabledAtom @-}
-- enabledAtom :: Eq id => CausalTreeAtom id a -> id -> Bool
-- enabledAtom (CausalTreeAtom id _) id' = id /= id'
-- 
-- {-@ reflect enabledChildren @-}
-- enabledChildren :: Eq id => [CausalTreeWeave id a] -> id -> Bool
-- enabledChildren [] _ = True
-- enabledChildren (h:t) id = enabledWeave h id && enabledChildren t id
-- 
-- {-@ reflect enabledLists @-}
-- enabledLists :: Eq id => [(id, [CausalTreeAtom id a])] -> id -> Bool
-- enabledLists [] _ = True
-- enabledLists ((_,h):t) id = enabledAtoms h id && enabledLists t id
-- 
-- {-@ reflect enabledAtoms @-}
-- enabledAtoms :: Eq id => [CausalTreeAtom id a] -> id -> Bool
-- enabledAtoms [] _ = True
-- enabledAtoms (h:t) id = enabledAtom h id && enabledAtoms t id

{-@ reflect compatibleList @-}
compatibleList :: Eq id => id -> [CausalTreeAtom id a] -> Bool
compatibleList opid [] = True
compatibleList opid (CausalTreeAtom opid' _:xs) = opid /= opid' && compatibleList opid xs

{-@ reflect compatibleState @-}
--{-@ compatibleState :: CausalTree id a -> CausalTreeOp id a -> Bool @-}
compatibleState :: Ord id => CausalTree id a -> CausalTreeOp id a -> Bool
compatibleState (CausalTree _ m) (CausalTreeOp pid (CausalTreeAtom id _))
  | Nothing <- pendingM
  = pid /= id
  | Just pending <- pendingM
  = pid /= id && compatibleList id pending
  where pendingM = Map.lookup id m
  


{-@ reflect compatible @-}
compatible :: Eq id => CausalTreeOp id a -> CausalTreeOp id a -> Bool
compatible (CausalTreeOp pid (CausalTreeAtom id _)) (CausalTreeOp pid' (CausalTreeAtom id' _)) =
  id /= id'
  -- maybe not necessary:
  -- && not (pid == id' && pid' == id) 


{-@ reflect apply @-}
apply :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTree id a
apply ct (CausalTreeOp parentId atom) = applyAtom ct parentId atom

{-@ reflect causalTreeSize @-}
{-@ causalTreeSize :: Ord id => CausalTree id a -> Nat @-}
causalTreeSize :: Ord id => CausalTree id a -> Int
causalTreeSize (CausalTree weave pending) = causalTreeWeaveLength weave + pendingSize pending 

{-@ reflect pendingSize @-}
{-@ pendingSize :: Ord id => Map id [CausalTreeAtom id a]-> Nat @-}
pendingSize :: Ord id => Map id [CausalTreeAtom id a] -> Int
-- TODO:
pendingSize Map.Tip = 0
pendingSize (Map.Map _ v t) = List.length v + pendingSize t

{-@ reflect pendingAtomSize @-}
{-@ pendingAtomSize :: Ord id => CausalTree id a -> id -> Nat @-}
pendingAtomSize :: Ord id => CausalTree id a -> id -> Int
pendingAtomSize (CausalTree _ pending) id
  | Just x <- Map.lookup id pending
  = List.length x
  | otherwise
  = 0


{-@ reflect constConstNothing @-}
constConstNothing :: a -> b -> Maybe c
constConstNothing _ _ = Nothing

{-@ reflect applyAtomHelper @-}
{-@ applyAtomHelper :: Ord id => id:id -> ct:CausalTree id a -> CausalTreeAtom id a -> CausalTree id a / [causalTreeSize ct, pendingSize (causalTreePending ct), 1] @-}
applyAtomHelper :: Ord id => id -> CausalTree id a -> CausalTreeAtom id a -> CausalTree id a
applyAtomHelper opId ct atom =
-- #ifndef NotLiquid  
--   pendingAtomSize ct opId `cast`
-- #endif
  applyAtom ct opId atom


-- termination metric: 
{-@ reflect applyAtom @-}
{-@ applyAtom :: Ord id => ct:CausalTree id a -> id:id -> CausalTreeAtom id a -> CausalTree id a / [causalTreeSize ct, pendingSize (causalTreePending ct), 0] @-}
applyAtom :: Ord id => CausalTree id a -> id -> CausalTreeAtom id a -> CausalTree id a
applyAtom (CausalTree !weave !pending) parentId atom = case insertInWeave weave parentId atom of
    Nothing -> 
        -- ParentId not seen yet, so mark as pending.
        let pending' = insertPending parentId atom pending in
        CausalTree weave pending'

    Just weave' -> 
        -- Inserted, so apply any pending operations that may depend on this atom.
        let opId = causalTreeAtomId atom in
        let (pendingAtomsM, pending') = Map.updateLookupWithKey constConstNothing opId pending in
        let ct = CausalTree weave' pending' in
        pendingAtomSize ct opId `cast`
        case pendingAtomsM of
          Nothing -> ct
          Just pendingAtoms -> List.foldl' (applyAtomHelper opId) ct pendingAtoms


{-@ reflect insertInWeave @-}
{-@ insertInWeave :: Ord id => w:CausalTreeWeave id a -> id -> CausalTreeAtom id a -> Maybe (CausalTreeWeave id a) / [causalTreeWeaveLength w, 0]@-}
insertInWeave :: Ord id => CausalTreeWeave id a -> id -> CausalTreeAtom id a -> Maybe (CausalTreeWeave id a)
insertInWeave (CausalTreeWeave currentAtom currentChildren) parentId atom
    -- Is the current atom the target parent?
    | causalTreeAtomId currentAtom == parentId = 
        let children = insertAtom currentChildren atom in
        Just $ CausalTreeWeave currentAtom children
    | otherwise = 
        let childrenM = insertInWeaveChildren currentChildren parentId atom in
        -- CausalTreeWeave currentAtom <$> childrenM
        case childrenM of
          Nothing -> Nothing
          Just children -> Just $ CausalTreeWeave currentAtom children

{-@ reflect insertInWeaveChildren  @-}
{-@ insertInWeaveChildren :: Ord id => w:[CausalTreeWeave id a] ->  id -> CausalTreeAtom id a -> Maybe [CausalTreeWeave id a] / [causalTreeWeaveLengthList w, len w] @-}
insertInWeaveChildren :: Ord id => [CausalTreeWeave id a] ->  id -> CausalTreeAtom id a -> Maybe [CausalTreeWeave id a]
insertInWeaveChildren [] _ _ = Nothing
insertInWeaveChildren (w:ws) parentId atom = case insertInWeave w parentId atom of
    Nothing ->
        -- (w:) <$> insertInWeaveChildren ws parentId atom
        case insertInWeaveChildren ws parentId atom of
          Nothing ->
            Nothing
          Just ws ->
            Just (w:ws)
    Just w' ->
        Just $ w':ws



{-@ reflect insertAtom @-}
insertAtom :: Ord id => [CausalTreeWeave id a] -> CausalTreeAtom id a -> [CausalTreeWeave id a]
insertAtom [] atom = [CausalTreeWeave atom []]
insertAtom l@(w:ws) atom 
  | atom `atomGreaterThan` causalTreeWeaveAtom w = CausalTreeWeave atom []:l
  | otherwise                                    = w:insertAtom ws atom
-- Compare whether an atom is greater than another atom, prioritizing CausalTreeLetterDelete.
{-@ reflect atomGreaterThan @-}
atomGreaterThan :: Ord id => CausalTreeAtom id a -> CausalTreeAtom id a -> Bool
atomGreaterThan (CausalTreeAtom a1 CausalTreeLetterRoot) (CausalTreeAtom a2 CausalTreeLetterRoot)     = a1 > a2
atomGreaterThan (CausalTreeAtom _ CausalTreeLetterRoot) (CausalTreeAtom _ _)                          = True
atomGreaterThan (CausalTreeAtom a1 CausalTreeLetterDelete) (CausalTreeAtom a2 CausalTreeLetterDelete) = a1 > a2
atomGreaterThan (CausalTreeAtom _ CausalTreeLetterDelete) (CausalTreeAtom _ _)                        = True
atomGreaterThan (CausalTreeAtom a1 (CausalTreeLetter _)) (CausalTreeAtom a2 (CausalTreeLetter _))     = a1 > a2
atomGreaterThan (CausalTreeAtom a1 (CausalTreeLetter _)) (CausalTreeAtom a2 _)                        = False







-- TODO: move to CausalTree.hs
-- {-@ lawCommutativity :: Ord id => x : CausalTree id a -> op1 : CausalTreeOp id a -> op2 : CausalTreeOp id a -> {(compatible op1 op2 && compatibleState x op1 && compatibleState x op2) => apply (apply x op1) op2 == apply (apply x op2) op1} @-}
-- lawCommutativity :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
-- lawCommutativity ct op1@(CausalTreeOp pid1 (CausalTreeAtom id1 l1)) op2@(CausalTreeOp pid2 (CausalTreeAtom id2 l2))
--   | id1 == id2
--   = ()
--   | pid1 == pid2
--   = lawCommutativityEq ct op1 op2
--   | otherwise
--   = lawCommutativityNEq ct op1 op2


{-@ ple lawCompatibilityCommutativity @-}
{-@ lawCompatibilityCommutativity :: Eq id => op1:CausalTreeOp id a -> op2:CausalTreeOp id a -> {compatible op1 op2 = compatible op2 op1} @-}
lawCompatibilityCommutativity :: Eq id => CausalTreeOp id a -> CausalTreeOp id a -> ()
lawCompatibilityCommutativity _ _ = ()



-- -- {-@ lawNonCausal :: Ord id => x : CausalTree id a -> {op1 : CausalTreeOp id a | enabled x op1} -> {op2 : CausalTreeOp id a | enabled x op2} -> {enabled (apply x op1) op2 <=> enabled (apply x op2) op1} @-}
-- -- lawNonCausal :: Ord id => CausalTree id a -> CausalTreeOp id a -> CausalTreeOp id a -> ()
-- -- lawNonCausal _ _ _ = ()

#ifdef NotLiquid


-- extractLetter :: t (CausalTreeAtom id a) -> t a
-- extractLetter :: [CausalTreeAtom id a] -> [a]
-- extractLetter = mapMaybe $ \a -> case causalTreeAtomLetter a of
extractLetter :: CausalTreeAtom id a -> Maybe a
extractLetter a = case causalTreeAtomLetter a of
    CausalTreeLetter a -> Just a
    CausalTreeLetterDelete -> Nothing
    CausalTreeLetterRoot -> Nothing

rootAtomId :: CausalTree id a -> id
rootAtomId = causalTreeAtomId . causalTreeWeaveAtom . causalTreeWeave

preorder :: CausalTree id a -> [CausalTreeAtom id a]
preorder = reverse . preorder'

-- | Preorder traversal of a `CausalTree`. Returns atoms in reverse order.
-- Invariant: `CausalTreeLetter` is the only constructor in the returned list.
-- O(n)
--
-- JP: Can we efficiently return results in the correct order by doing a foldr?
preorder' :: CausalTree id a -> [CausalTreeAtom id a]
preorder' = snd . go False [] . causalTreeWeave
  where
    go !deleted !acc (CausalTreeWeave atom ws) = 
      let (deleted', acc') = case causalTreeAtomLetter atom of
            CausalTreeLetterDelete ->
              if deleted then
                (deleted, acc)
              else
                (True, pop acc)
            CausalTreeLetterRoot ->
              (deleted, acc)
            CausalTreeLetter _ ->
              (deleted, atom:acc)
      in
      let acc'' = snd $ List.foldl' (uncurry go) (False, acc') ws in
      (deleted', acc'')

    pop = List.drop 1

-- JP: This does a version does a BFS.
-- preorder' :: CausalTree id a -> [CausalTreeAtom id a]
-- preorder' = go [] . causalTreeWeave
--  where
--   -- go deleted acc (CausalTreeWeave _atom ws) = 
--   go acc (CausalTreeWeave _atom ws) = 
--     let (_, acc') = List.foldl' visitor (False, acc) ws in
--     List.foldl' go acc' ws 
-- 
--   visitor (deleted, acc) (CausalTreeWeave atom _ws) = case causalTreeAtomLetter atom of
--     CausalTreeLetterDelete ->
--       -- Skip if already deleted.
--       if deleted then
--         (deleted, acc)
--       else
--         (True, pop acc)
--     
--     CausalTreeLetterRoot ->
--       -- Should be unreachable.
--       (deleted, acc)
-- 
--     CausalTreeLetter _ ->
--       (deleted, atom:acc)
--   
--   pop = List.drop 1
      


instance (FromJSON id, FromJSON a) => FromJSON (CausalTreeOp id a) where
    parseJSON = Aeson.withObject "CausalTreeOp" $ \o -> 
        CausalTreeOp <$> o .: "parent" <*> o .: "atom"

instance (ToJSON id, ToJSON a) => ToJSON (CausalTreeOp id a) where
    toJSON (CausalTreeOp id a) = Aeson.object [
        "parent" .= id
      , "atom" .= a
      ]

instance (FromJSON id, FromJSON a) => FromJSON (CausalTreeAtom id a) where
    parseJSON = Aeson.withObject "CausalTreeAtom" $ \o ->
        CausalTreeAtom <$> o .: "id" <*> o .: "letter"

instance (ToJSON id, ToJSON a) => ToJSON (CausalTreeAtom id a) where
    toJSON (CausalTreeAtom id letter) = Aeson.object [
        "id" .= id
      , "letter" .= letter
      ]

instance (FromJSON a) => FromJSON (CausalTreeLetter a) where
    parseJSON = Aeson.withObject "CausalTreeLetter" $ \o -> do
        c <- o .: "c"
        case (c :: String) of
            "letter" -> CausalTreeLetter <$> o .: "letter"
            "delete" -> return CausalTreeLetterDelete
            "root" -> return CausalTreeLetterRoot

instance (ToJSON a) => ToJSON (CausalTreeLetter a) where
    toJSON (CausalTreeLetter letter) = Aeson.object [
        "c" .= ("letter" :: String)
      , "letter" .= letter
      ]
    toJSON CausalTreeLetterDelete = Aeson.object [
        "c" .= ("delete" :: String)
      ]
    toJSON CausalTreeLetterRoot = Aeson.object [
        "c" .= ("root" :: String)
      ]

#endif