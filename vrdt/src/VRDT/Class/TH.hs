{-# LANGUAGE TemplateHaskell #-}

module VRDT.Class.TH where

import           Control.Monad (foldM)
import qualified Data.Aeson as Aeson
import qualified Data.Char as Char
import           Data.Map (Map)
import qualified Data.Map as Map
import           GHC.Generics (Generic)
import           Language.Haskell.TH

import           VRDT.Class (Operation)

-- | Creates the `Operation` datatype and derives a `VRDT` instance for the given type.
deriveVRDT :: Name -> Q [Dec]
deriveVRDT n = reify n >>= \case 
    TyConI dec -> do
        -- Extract type information.
        tInfo <- extractTypeInfo dec

        -- Get Operation datatype name.
        let opName = getOperationName tInfo

        -- -- Get operation field names map.
        -- let opFieldNames = getOperationFieldNames tInfo

        -- Create operation type.
        opD <- mkOperationType opName tInfo

        -- Derive VRDT instance.
        vrdtInstD <- mkVRDTInstance tInfo
        
        -- Derive JSON instance for operation type.
        -- aesonD <- Aeson.deriveJSON Aeson.defaultOptions opName
        let toJSOND = InstanceD Nothing [] (AppT (ConT ''Aeson.ToJSON) (ConT opName)) []
        let fromJSOND = InstanceD Nothing [] (AppT (ConT ''Aeson.FromJSON) (ConT opName)) []


        -- return $ opD:vrdtInstD:aesonD
        return $ [opD, vrdtInstD, toJSOND, fromJSOND] -- :aesonD
    _ -> fail "deriveVRDT: Must be a type."

  where
    extractTypeInfo (DataD _ name tvars _ cons _)   = return (name, tvars, cons)
    extractTypeInfo (NewtypeD _ name tvars _ con _) = return (name, tvars, [con])
    extractTypeInfo _                               = fail "deriveVRDT: Must be a data or newtype."

    mkVRDTInstance = undefined

    mkOperationType opName (_name, tvars, cons) = do
        varMap <- foldM toVarTypeMap mempty cons
        let opCons = varTypeMapToOpCons varMap
        return $ DataD [] opName tvars Nothing opCons [DerivClause Nothing [ConT ''Generic]]

    varTypeMapToOpCons :: Map String Type -> [Con]
    varTypeMapToOpCons = map (\(fName, ty) -> 
        -- Make operation constructor name.
        let opName = mkName $ headToUpper fName <> "Op" in

        -- Make operation type.
        let opTy = AppT (ConT ''Operation) ty in

        NormalC opName [(Bang NoSourceUnpackedness NoSourceStrictness, opTy)]
      ) . Map.toList

    toVarTypeMap acc con = 
        let nameTys = toVarTypeMapHelper con in
        foldM (\acc (fName, fTy) -> 
            -- Insert field and its type.
            let (oldM, acc') = Map.insertLookupWithKey (\_ a _ -> a) fName fTy acc in

            -- Check if name is already in acc and type's are different.
            case oldM of
                Just fTy' | fTy /= fTy' ->
                    fail $ "Field `" <> fName <> "` appears multiple times with different types."-- JP: This should be impossible?
                _ ->
                    return acc'
          ) acc nameTys

    toVarTypeMapHelper (NormalC name args) = toVarTypeMapHelper'' name args
    toVarTypeMapHelper (RecC name rArgs)   = toVarTypeMapHelper' rArgs
    toVarTypeMapHelper (InfixC arg1 name arg2) = toVarTypeMapHelper'' name [arg1, arg2]

    toVarTypeMapHelper' = map (\(name, _, ty) -> (nameBase name, ty))
    toVarTypeMapHelper'' name = map (\(n, (_, ty)) -> (nameBase name <> show n, ty)) . zip [1..]

    getOperationName (name, _, _) = mkName $ nameBase name <> "Op"


    headToUpper []    = []
    headToUpper (h:t) = Char.toUpper h:t





