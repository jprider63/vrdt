{-@ LIQUID "--reflection" @-}
{-@ LIQUID "--ple" @-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE LambdaCase #-}

module VRDT.Class.TH where

import           Control.Monad (foldM)
-- import qualified Data.Aeson as Aeson
import qualified Data.Maybe as Maybe
import qualified Data.List as List
-- import           Data.Map (Map)
-- import qualified Data.Map as Map
import           GHC.Generics (Generic)
import           Language.Haskell.TH

import           VRDT.Class (VRDT(..), Operation)


-- -- | 'mkVRDTPat' decorates a name value pair with (as pattern name,
-- -- field name, pattern) really should use a more sophisticated
-- -- recursion scheme but I don't want any extra dependencies
-- mkVRDTPat :: [(Name, v)] -> Q [(Name, v, (Name, Name, Pat))]
-- mkVRDTPat = mapM f
--   where f (name, v) = do
--           vName <- newName "v"
--           fieldName <- newName "f"
--           let prevNames' = name:prevNames
          


insertLookupWithKey :: Eq k => (k -> a -> a -> a) -> k -> a -> [(k, a)] -> (Maybe a, [(k, a)])
insertLookupWithKey f k v xs
  | Just vOld <- maybeV
  = let vNew = f k v vOld in
      (maybeV, fmap (\a@(x,v) -> if x == k then (x, vNew) else a) xs)
  | Nothing <- maybeV
  = (maybeV, (k, v):xs)
  where maybeV = lookup k xs

-- | Creates the `Operation` datatype and derives a `VRDT` instance for the given type.
deriveVRDT :: Name -> Q [Dec]
deriveVRDT n = reify n >>= \case 
    TyConI dec -> do
        -- Extract type information.
        (vrdtName, tvars, cons) <- extractTypeInfo dec

        -- Get Operation datatype name.
        let opName = getOperationName vrdtName

        -- Get operation field names map.
        varMap <- foldM toVarTypeMap mempty cons

        -- Create operation type.
        opD <- mkOperationType opName tvars varMap

        -- Derive VRDT instance.
        vrdtInstD <- mkVRDTInstance vrdtName opName tvars varMap
        
        -- Derive JSON instance for operation type.
        -- let toJSOND = InstanceD Nothing [] (AppT (ConT ''Aeson.ToJSON) (ConT opName)) []
        -- let fromJSOND = InstanceD Nothing [] (AppT (ConT ''Aeson.FromJSON) (ConT opName)) []


        return [opD, vrdtInstD] -- , toJSOND, fromJSOND] -- :aesonD
    _ -> fail "deriveVRDT: Must be a type."

  where
    extractTypeInfo (DataD _ name tvars _ cons _)   = return (name, tvars, cons)
    extractTypeInfo (NewtypeD _ name tvars _ con _) = return (name, tvars, [con])
    extractTypeInfo _                               = fail "deriveVRDT: Must be a data or newtype."

    mkOperationType opName tvars varMap = do
        let opCons = varTypeMapToOpCons varMap
        return $ DataD [] opName tvars Nothing opCons [DerivClause Nothing [ConT ''Generic]]

    varTypeMapToOpCons :: [(Name, (a,b, Type))] -> [Con]
    varTypeMapToOpCons = map (\(fName, (_,_,ty)) -> do
        -- Make operation constructor name.
        let opName = fieldToOpConName fName

        -- Make operation type.
        let opTy = fieldTypeToOpType ty

        NormalC opName [(Bang NoSourceUnpackedness NoSourceStrictness, opTy)]
      ) 

    toVarTypeMap :: [(Name, (Name, Pat, Type))] -> Con -> Q ([(Name, (Name, Pat, Type))])
    toVarTypeMap acc con = do
        nameTys <- toVarTypeMapHelper con
        -- pats <- mapM toVarTypeMapHelper'' nameTys
        foldM (\acc (fName, fTy) -> 
            -- Insert field and its type.
            let (oldM, acc') = insertLookupWithKey (\_ a _ -> a) fName fTy acc
            in

            -- Check if name is already in acc and type's are different.
            case oldM of
                Just fTy' | fTy /= fTy' ->
                    fail $ "Field `" <> nameBase fName <> "` appears multiple times with different types."-- JP: This should be impossible?
                _ ->
                    return acc'
          ) acc nameTys

    toVarTypeMapHelper :: Con -> Q [(Name, (Name, Pat, Type))]
    toVarTypeMapHelper (RecC _name rArgs) = do
      patNames <- mapM (\_ -> newName "f") rArgs
      let pat = ConP _name (fmap VarP patNames)
      pure $ zipWith3 (\pname p (n,ty) -> (n, (pname,p,ty))) patNames (repeat pat) (toVarTypeMapHelper' rArgs)
    toVarTypeMapHelper _                 = fail "Not a record type."
    -- toVarTypeMapHelper (NormalC name args) = toVarTypeMapHelper'' name args
    -- toVarTypeMapHelper (InfixC arg1 name arg2) = toVarTypeMapHelper'' name [arg1, arg2]

    toVarTypeMapHelper' = map (\(name, _, ty) -> (name, ty))
    -- toVarTypeMapHelper'' name = map (\(n, (_, ty)) -> (nameBase name <> show n, ty)) . zip [1..]


    getOperationName name = mkName $ nameBase name <> "Op"

    fieldToOpConName fName = mkName $ headToUpper (nameBase fName) <> "Op"
    fieldTypeToOpType ty = AppT (ConT ''Operation) ty

    lowerUpper = zip ['a'..'z'] ['A' .. 'Z']

    toUpper x = Maybe.fromMaybe x $ lookup x lowerUpper


    headToUpper []    = []
    headToUpper (h:t) = toUpper h:t

    tyVarBndrToType :: TyVarBndr -> Type
    tyVarBndrToType (PlainTV n)    = ConT n
    tyVarBndrToType (KindedTV n _) = ConT n


    mkVRDTInstance :: Name -> Name -> [TyVarBndr] -> [(Name, (Name, Pat, Type))] -> Q Dec
    mkVRDTInstance vrdtName opName tvars varMap = do
        let ctx = [] -- JP: Should we add VRDT instances of fields' types to context (if they contain free tvars)?

        -- Create type.
        let ty = List.foldl' (\acc tvar -> AppT acc $ tyVarBndrToType tvar) (ConT vrdtName) tvars

        -- Assign `Operation` type family.
#if MIN_VERSION_template_haskell(2,15,0)
        let operationD = TySynInstD $ TySynEqn Nothing (AppT (ConT ''Operation) ty) (ConT opName)
#else
        let operationD = TySynInstD ''Operation $ TySynEqn [ty] (ConT opName)
#endif

        applyD <- mkApply varMap
        -- enabledD <- mkEnabled varMap
        compatibleD <- mkCompatible varMap
        compatibleStateD <- mkCompatibleState varMap
        lawCommutativityD <- mkCommutativity varMap
        lawCommutativityD' <- mkCommutativity' varMap
        -- lawNonCausalD <- mkNonCausal varMap

        -- fail $ show $ ppr lawNonCausalD

        return $ InstanceD Nothing ctx (AppT (ConT ''VRDT) ty) [operationD, compatibleD, compatibleStateD, applyD, lawCommutativityD, lawCommutativityD'] -- enabledD, lawNonCausalD]

    mkApply :: [(Name, (Name, Pat, Type))] -> Q Dec
    mkApply varMap = do
      clss <- mapM (\(fName, (patName, pat, _)) -> do
          vName <- newName "v"
          let fcName = fieldToOpConName fName
          opName <- newName "op"
          
          let pats = [AsP vName pat, ConP fcName [VarP opName]]

          let e = NormalB $ RecUpdE (VarE vName) [(fName, (AppE (AppE (VarE 'apply) (VarE patName)) (VarE opName)))]

          return $ Clause pats e []
        
        ) varMap
      return $ FunD 'apply clss

    -- mkEnabled :: [(Name, Type)] -> Q Dec
    -- mkEnabled varMap = do
    --   clss <- mapM (\(fName, ty) -> do
    --       vName <- newName "v"
    --       let fcName = fieldToOpConName fName
    --       opName <- newName "op"
    --       
    --       let pats = [VarP vName, ConP fcName [VarP opName]]

    --       let e = NormalB $ AppE (AppE (VarE 'enabled) (AppE (VarE fName) (VarE vName))) (VarE opName)

    --       return $ Clause pats e []
    --     ) $ Map.toList varMap
    --     
    --   return $ FunD 'enabled clss

    mkCommutativity :: [(Name, (Name, Pat, Type))] -> Q Dec
    mkCommutativity varMap = do
      clss' <- mapM (\(fName, (patName, pat, _)) -> do
          vName <- newName "v"
          let fcName = fieldToOpConName fName
          op1Name <- newName "op1"
          op2Name <- newName "op2"
        
          let pats = [AsP vName pat, ConP fcName [VarP op1Name], ConP fcName [VarP op2Name]]

          let e = NormalB $ AppE (AppE (AppE (VarE 'lawCommutativity) (VarE patName)) (VarE op1Name)) (VarE op2Name)

          return $ Clause pats e []
        ) varMap
      let clss = clss' ++ [Clause [WildP, WildP, WildP] (NormalB $ TupE []) []]

      return $ FunD 'lawCommutativity clss

    mkCompatible :: [(Name, (Name, Pat, Type))] -> Q Dec
    mkCompatible varMap = do
      clss' <- mapM (\(fName, ty) -> do
          let fcName = fieldToOpConName fName
          op1Name <- newName "op1"
          op2Name <- newName "op2"
        
          let pats = [ConP fcName [VarP op1Name], ConP fcName [VarP op2Name]]

          let e = NormalB $ AppE (AppE (VarE 'compatible) (VarE op1Name)) (VarE op2Name)

          return $ Clause pats e []
        ) varMap
      let clss = clss' ++ [Clause [WildP, WildP] (NormalB $ ConE 'True) []]

      return $ FunD 'compatible clss

    mkCompatibleState :: [(Name, (Name, Pat, Type))] -> Q Dec
    mkCompatibleState varMap = do
      clss <- mapM (\(fName, (patName, pat, _)) -> do
          vName <- newName "v"
          let fcName = fieldToOpConName fName
          opName <- newName "op"
          
          let pats = [AsP vName pat, ConP fcName [VarP opName]]

          let e = NormalB $ AppE (AppE (VarE 'compatibleState) (VarE patName)) (VarE opName)
          return $ Clause pats e []
        ) varMap
      return $ FunD 'compatibleState clss

    mkCommutativity' :: [(Name, (Name, Pat, Type))] -> Q Dec
    mkCommutativity' varMap = do
      clss' <- mapM (\(fName, ty) -> do
          let fcName = fieldToOpConName fName
          op1Name <- newName "op1"
          op2Name <- newName "op2"

          let pats = [ConP fcName [VarP op1Name], ConP fcName [VarP op2Name]]

          let e = NormalB $ AppE (AppE (VarE 'lawCompatibilityCommutativity) (VarE op1Name)) (VarE op2Name)

          return $ Clause pats e []
        ) varMap
      let clss = clss' ++ [Clause [WildP, WildP] (NormalB $ TupE []) []]
      return $ FunD 'lawCompatibilityCommutativity clss

    -- mkNonCausal :: [(Name, Type)] -> Q Dec
    -- mkNonCausal varMap = do
    --   clss' <- mapM (\(fName, ty) -> do
    --       vName <- newName "v"
    --       let fcName = fieldToOpConName fName
    --       op1Name <- newName "op1"
    --       op2Name <- newName "op2"
    --     
    --       let pats = [VarP vName, ConP fcName [VarP op1Name], ConP fcName [VarP op2Name]]

    --       let e = NormalB $ AppE (AppE (AppE (VarE 'lawNonCausal) (AppE (VarE fName) (VarE vName))) (VarE op1Name)) (VarE op2Name)

    --       return $ Clause pats e []
    --     ) $ Map.toList varMap
    --   let clss = clss' ++ [Clause [WildP, WildP, WildP] (NormalB $ TupE []) []]

    --   return $ FunD 'lawNonCausal clss


