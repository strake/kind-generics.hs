{-# language ExplicitNamespaces #-}
{-# language MultiWayIf #-}
{-# language TemplateHaskellQuotes #-}
{-# language CPP #-}

-- | Main module of @kind-generics-th@.
-- Please refer to the @README@ file for documentation on how to use this package.
module Generics.Kind.TH (deriveGenericK) where

import Control.Applicative
import Control.Monad
import qualified Data.Kind as Kind
import Data.List
import Data.Maybe
import Data.Type.Equality (type (~~))
import Generics.Kind
import GHC.Generics as Generics hiding (conIsRecord, conName, datatypeName)
import Language.Haskell.TH as TH
import Language.Haskell.TH.Datatype as THAbs

-- | Given the 'Name' of a data type (or, the 'Name' of a constructor belonging
-- to a data type), generate 'GenericK' instances for that data type. You will
-- likely need to enable most of these language extensions in order for GHC to
-- accept the generated code:
--
-- * @DataKinds@
--
-- * @EmptyCase@ (if using an empty data type)
--
-- * @FlexibleInstances@
--
-- * @MultiParamTypeClasses@
--
-- * @PolyKinds@ (if using a poly-kinded data type)
--
-- * @TemplateHaskell@
--
-- * @TypeFamilies@
deriveGenericK :: Name -> Q [Dec]
deriveGenericK n = do
  DatatypeInfo{ datatypeName    = dataName
#if MIN_VERSION_th_abstraction(0,3,0)
              , datatypeInstTypes = univVars
#else
              , datatypeVars    = univVars
#endif
              , datatypeVariant = variant
              , datatypeCons    = cons
              } <- reifyDatatype n
  cons' <- traverse resolveConSynonyms cons
  let deriveInsts :: [Type] -> [Type] -> Q [Dec]
      deriveInsts argsToKeep argsToDrop = do
        inst <- deriveGenericKFor argsToKeep argsToDrop
        case argsToKeep of
          [] -> pure [inst]
          (argToDrop:argsToKeep') -> do
            argToDrop' <- resolveTypeSynonyms argToDrop
            if |  -- Can the argument to drop be eta-reduced?
                  Just argNameToDrop <- distinctTyVarType (freeVariables argsToKeep')
                                                          argToDrop'
                  -- Check for dependent quantification, which we currently can't handle.
               ,  argNameToDrop `notElem`
                    freeVariables (map typeKind argsToDrop
                                ++ map tvKind (gatherExistentials cons'))
               -> do let allInnerTypes  = gatherConstraints cons' ++ gatherFields cons'
                     -- Check if the argument appears in a type family application.
                     inTyFamApp <- or <$> traverse (isInTypeFamilyApp argNameToDrop)
                                                   allInnerTypes
                     if inTyFamApp
                        then pure [inst]
                        else (inst:) <$> deriveInsts argsToKeep' (argToDrop':argsToDrop)
               |  otherwise
               -> pure [inst]

      -- Generate a single GenericK instance for a given set of data type
      -- arguments and indexed arguments.
      deriveGenericKFor :: [Type] -> [Type] -> Q Dec
      deriveGenericKFor argsToKeep argsToDrop = do
        let argNamesToDrop = map varTToName argsToDrop
            kind = foldr (\x y -> ArrowT `AppT` x `AppT` y)
                         (ConT ''Kind.Type) (map typeKind argsToDrop)
            dataApp = pure $ SigT (foldr (flip AppT) (ConT dataName) argsToKeep) kind
        instanceD (pure [])
                  (conT ''GenericK `appT` dataApp `appT`
                        foldr (\x y -> infixT x '(:&&:) y)
                              (promotedT 'LoT0) (map varT argNamesToDrop))
                  [ tySynInstD ''RepK $ tySynEqn [dataApp] $
                      deriveRepK dataName argNamesToDrop variant cons'
                  , deriveFromK cons'
                  , deriveToK cons'
                  ]

  deriveInsts (reverse univVars) []

-- | @'distinctTyVarType' tvSet ty@ returns @'Just' tvTy@ if @ty@:
--
-- a. Is a type variable named @tvTy@, and
-- b. @tvTy@ is not an element of @tvSet@.
--
-- Otherwise, returns 'Nothing'.
distinctTyVarType :: [Name] -> Type -> Maybe Name
distinctTyVarType tvSet ty = do
  tvTy <- varTToName_maybe ty
  guard $ tvTy `notElem` tvSet
  pure tvTy

deriveRepK :: Name -> [Name]
           -> DatatypeVariant -> [ConstructorInfo] -> Q Type
deriveRepK dataName univVarNames dataVariant cons = do
  cons' <- traverse constructor cons
  metaData $ foldBal (\x y -> InfixT x ''(:+:) y) (ConT ''V1) cons'
  where
    metaData :: Type -> Q Type
    metaData t = do
      m   <- maybe (fail "Cannot fetch module name!")  pure (nameModule dataName)
      pkg <- maybe (fail "Cannot fetch package name!") pure (namePackage dataName)
      conT ''D1
        `appT` (promotedT 'MetaData `appT`
                litT (strTyLit (nameBase dataName)) `appT`
                litT (strTyLit m) `appT`
                litT (strTyLit pkg) `appT`
                promoteBool (isNewtypeVariant dataVariant))
        `appT` pure t

    constructor :: ConstructorInfo -> Q Type
    constructor ConstructorInfo{ constructorName       = conName
                               , constructorVars       = exTvbs
                               , constructorContext    = conCtxt
                               , constructorFields     = fields
                               , constructorStrictness = fieldStricts
                               , constructorVariant    = conVariant
                               } = do
      mbFi <- reifyFixity conName
      conT ''C1
        `appT` (promotedT 'MetaCons `appT`
                litT (strTyLit (nameBase conName)) `appT`
                fixityIPromotedType mbFi conIsInfix `appT`
                promoteBool conIsRecord)
        `appT` do prod <- foldBal (\x y -> InfixT x ''(:*:) y) (ConT ''U1) <$> selectors
                  ctxtProd <- context prod
                  existentials ctxtProd
      where
        conIsRecord :: Bool
        conIsRecord =
          case conVariant of
            NormalConstructor   -> False
            InfixConstructor    -> False
            RecordConstructor{} -> True

        conIsInfix :: Bool
        conIsInfix =
          case conVariant of
            NormalConstructor   -> False
            InfixConstructor    -> True
            RecordConstructor{} -> False

        context :: Type -> Q Type
        context ty =
          case conCtxt of
            [] -> pure ty -- Don't use (:=>:) if there are no constraints
            _  -> infixT (atomizeContext conCtxt) ''(:=>:) (pure ty)

        existentials :: Type -> Q Type
        existentials ty =
          foldl' (\x tvb -> conT ''Exists `appT` pure (tvKind tvb) `appT` x)
                 (pure ty) exTvbs

        selectors :: Q [Type]
        selectors =
          case conVariant of
            NormalConstructor         -> nonRecordCase
            InfixConstructor          -> nonRecordCase
            RecordConstructor records -> recordCase records
          where
            nonRecordCase :: Q [Type]
            nonRecordCase = mkCase (map (const Nothing) fields)

            recordCase :: [Name] -> Q [Type]
            recordCase records = mkCase (map Just records)

            mkCase :: [Maybe Name] -> Q [Type]
            mkCase mbRecords = do
              dcdStricts <- reifyConStrictness conName
              zipWith4M selector mbRecords fieldStricts dcdStricts fields

        selector :: Maybe Name -> FieldStrictness -> TH.DecidedStrictness -> Type -> Q Type
        selector mbRecord (FieldStrictness fu fs) ds field = do
          let mbSelNameT =
                case mbRecord of
                  Just record -> promotedT 'Just `appT` litT (strTyLit (nameBase record))
                  Nothing     -> promotedT 'Nothing
          conT ''S1
            `appT` (promotedT 'MetaSel `appT`
                    mbSelNameT `appT`
                    promoteSourceUnpackedness (generifyUnpackedness fu) `appT`
                    promoteSourceStrictness (generifyStrictness fs) `appT`
                    promoteDecidedStrictness (generifyDecidedStrictness ds))
            `appT` (conT ''Field `appT` atomize field)

        atomizeContext :: Cxt -> Q Type
        atomizeContext = foldBal (\x y -> infixT x '(:&:) y)
                                 (promotedT 'Kon `appT` tupleT 0)
                       . map atomize

        atomize :: Type -> Q Type
        atomize = go
          where
            go :: Type -> Q Type
            -- Var case
            go ty@(VarT n) =
              case elemIndex n allTvbNames of
                Just idx -> pure $ enumerateTyVar idx
                Nothing  -> kon ty

            -- Kon cases
            go ty@ConT{}           = kon ty
            go ty@PromotedT{}      = kon ty
            go ty@TupleT{}         = kon ty
            go ty@ArrowT           = kon ty
            go ty@ListT            = kon ty
            go ty@PromotedTupleT{} = kon ty
            go ty@PromotedNilT     = kon ty
            go ty@PromotedConsT    = kon ty
            go ty@StarT            = kon ty
            go ty@ConstraintT      = kon ty
            go ty@LitT{}           = kon ty
            go ty@WildCardT        = kon ty
            go ty@UnboxedTupleT{}  = kon ty
            go ty@UnboxedSumT{}    = kon ty
            go EqualityT           = kon (ConT ''(~~))
                                       -- EqualityT can refer to both homogeneous
                                       -- and heterogeneous equality, but TH always
                                       -- splices EqualityT back in as if it were
                                       -- homogeneous. To be on the safe side, always
                                       -- conservatively assume that the equality it
                                       -- heterogeneous, since it is more permissive.

            -- Recursive cases
            go (AppT ty1 ty2) = do ty1' <- go ty1
                                   ty2' <- go ty2
                                   case (ty1', ty2') of
                                     (PromotedT kon1 `AppT` tyArg1,
                                      PromotedT kon2 `AppT` tyArg2)
                                            |  kon1 == 'Kon, kon2 == 'Kon
                                            -> kon (AppT tyArg1 tyArg2)
                                     (_, _) -> pure $ InfixT ty1' '(:@:) ty2'
            go (InfixT ty1 n ty2)  = go (ConT n `AppT` ty1 `AppT` ty2)
            go (UInfixT ty1 n ty2) = go (ConT n `AppT` ty1 `AppT` ty2)
            go (SigT ty _)         = go ty
            go (ParensT ty)        = ParensT <$> go ty

            -- Failure case
            go ty@ForallT{}       = can'tRepresent "rank-n type" ty

            kon :: Type -> Q Type
            kon ty = promotedT 'Kon `appT` pure ty

            can'tRepresent :: String -> Type -> Q a
            can'tRepresent thing ty = fail $ "Unsupported " ++ thing ++ ": " ++ pprint ty

        allTvbNames :: [Name]
        allTvbNames = map tvName exTvbs ++ univVarNames

    fixityIPromotedType :: Maybe TH.Fixity -> Bool -> Q Type
    fixityIPromotedType mbFi True =
               promotedT 'InfixI
        `appT` promoteAssociativity (fdToAssociativity fd)
        `appT` litT (numTyLit (toInteger n))
      where
        Fixity n fd = fromMaybe defaultFixity mbFi
    fixityIPromotedType _ False = promotedT 'PrefixI

deriveFromK :: [ConstructorInfo] -> Q Dec
deriveFromK cons = do
  x <- newName "x"
  funD 'fromK
       [clause [varP x]
               (normalB $ conE 'M1 `appE` caseE (varE x) cases)
               []]
  where
    cases :: [Q Match]
    cases = zipWith (fromCon (length cons)) [1..] cons

    fromCon :: Int -- Total number of constructors
            -> Int -- Constructor index
            -> ConstructorInfo -> Q Match
    fromCon n i (ConstructorInfo{ constructorName    = conName
                                , constructorVars    = exTvbs
                                , constructorContext = conCtxt
                                , constructorFields  = fields
                                }) = do
      fNames <- newNameList "f" $ length fields
      match (conP conName (map varP fNames))
            (normalB $ lrE i n $ conE 'M1 `appE`
              do prod <- foldBal (\x y -> infixE (Just x) (conE '(:*:)) (Just y))
                           (conE 'U1)
                           (map fromField fNames)
                 ctxtProd <- context prod
                 existentials ctxtProd)
            []
      where
        fromField :: Name -> Q Exp
        fromField fName = conE 'M1 `appE` (conE 'Field `appE` varE fName)

        context :: Exp -> Q Exp
        context e =
          case conCtxt of
            [] -> pure e
            _  -> conE 'SuchThat `appE` pure e

        existentials :: Exp -> Q Exp
        existentials e = foldl' (\x _ -> conE 'Exists `appE` x) (pure e) exTvbs

deriveToK :: [ConstructorInfo] -> Q Dec
deriveToK cons = do
  x <- newName "x"
  funD 'toK
       [clause [conP 'M1 [varP x]]
               (normalB $ caseE (varE x) cases)
               []]
  where
    cases :: [Q Match]
    cases = zipWith (toCon (length cons)) [1..] cons

    toCon :: Int -- Total number of constructors
          -> Int -- Constructor index
          -> ConstructorInfo -> Q Match
    toCon n i (ConstructorInfo{ constructorName    = conName
                              , constructorVars    = exTvbs
                              , constructorContext = conCtxt
                              , constructorFields  = fields
                              }) = do
      fNames <- newNameList "f" $ length fields
      match (lrP i n $ conP 'M1
              [ do prod <- foldBal (\x y -> infixP x '(:*:) y)
                                  (conP 'U1 [])
                                  (map toField fNames)
                   ctxtProd <- context prod
                   existentials ctxtProd
              ] )
            (normalB $ foldl' appE (conE conName) (map varE fNames))
            []
        where
          toField :: Name -> Q Pat
          toField fName = conP 'M1 [conP 'Field [varP fName]]

          context :: Pat -> Q Pat
          context p =
            case conCtxt of
              [] -> pure p
              _  -> conP 'SuchThat [pure p]

          existentials :: Pat -> Q Pat
          existentials p = foldl' (\x _ -> conP 'Exists [x]) (pure p) exTvbs

-- | If a Type is a SigT, returns its kind signature. Otherwise, return Type.
typeKind :: Type -> Kind
typeKind (SigT _ k) = k
typeKind _          = ConT ''Kind.Type

fdToAssociativity :: FixityDirection -> Associativity
fdToAssociativity InfixL = LeftAssociative
fdToAssociativity InfixR = RightAssociative
fdToAssociativity InfixN = NotAssociative

generifyUnpackedness :: Unpackedness -> Generics.SourceUnpackedness
generifyUnpackedness UnspecifiedUnpackedness = Generics.NoSourceUnpackedness
generifyUnpackedness NoUnpack                = Generics.SourceNoUnpack
generifyUnpackedness Unpack                  = Generics.SourceUnpack

generifyStrictness :: Strictness -> Generics.SourceStrictness
generifyStrictness UnspecifiedStrictness = Generics.NoSourceStrictness
generifyStrictness Lazy                  = Generics.SourceLazy
generifyStrictness THAbs.Strict          = Generics.SourceStrict

generifyDecidedStrictness :: TH.DecidedStrictness -> Generics.DecidedStrictness
generifyDecidedStrictness TH.DecidedLazy   = Generics.DecidedLazy
generifyDecidedStrictness TH.DecidedStrict = Generics.DecidedStrict
generifyDecidedStrictness TH.DecidedUnpack = Generics.DecidedUnpack

promoteSourceUnpackedness :: Generics.SourceUnpackedness -> Q Type
promoteSourceUnpackedness Generics.NoSourceUnpackedness = promotedT 'Generics.NoSourceUnpackedness
promoteSourceUnpackedness Generics.SourceNoUnpack       = promotedT 'Generics.SourceNoUnpack
promoteSourceUnpackedness Generics.SourceUnpack         = promotedT 'Generics.SourceUnpack

promoteSourceStrictness :: Generics.SourceStrictness -> Q Type
promoteSourceStrictness Generics.NoSourceStrictness = promotedT 'Generics.NoSourceStrictness
promoteSourceStrictness Generics.SourceLazy         = promotedT 'Generics.SourceLazy
promoteSourceStrictness Generics.SourceStrict       = promotedT 'Generics.SourceStrict

promoteDecidedStrictness :: Generics.DecidedStrictness -> Q Type
promoteDecidedStrictness Generics.DecidedLazy   = promotedT 'Generics.DecidedLazy
promoteDecidedStrictness Generics.DecidedStrict = promotedT 'Generics.DecidedStrict
promoteDecidedStrictness Generics.DecidedUnpack = promotedT 'Generics.DecidedUnpack

promoteAssociativity :: Associativity -> Q Type
promoteAssociativity LeftAssociative  = promotedT 'LeftAssociative
promoteAssociativity RightAssociative = promotedT 'RightAssociative
promoteAssociativity NotAssociative   = promotedT 'NotAssociative

promoteBool :: Bool -> Q Type
promoteBool True  = promotedT 'True
promoteBool False = promotedT 'False

enumerateTyVar :: Int -> Type
-- Special-case the first 10, if only to generate more compact code
enumerateTyVar 0 = ConT ''Var0
enumerateTyVar 1 = ConT ''Var1
enumerateTyVar 2 = ConT ''Var2
enumerateTyVar 3 = ConT ''Var3
enumerateTyVar 4 = ConT ''Var4
enumerateTyVar 5 = ConT ''Var5
enumerateTyVar 6 = ConT ''Var6
enumerateTyVar 7 = ConT ''Var7
enumerateTyVar 8 = ConT ''Var8
enumerateTyVar 9 = ConT ''Var9
enumerateTyVar n = PromotedT 'Var `AppT` nTimes n (AppT (PromotedT 'VS)) (PromotedT 'VZ)

-- | Variant of foldr for producing balanced lists
foldBal :: (a -> a -> a) -> a -> [a] -> a
foldBal _  x []  = x
foldBal _  _ [y] = y
foldBal op x l   = let (a,b) = splitAt (length l `div` 2) l
                   in foldBal op x a `op` foldBal op x b

lrP :: Int -- Constructor index
    -> Int -- Total number of constructors
    -> Q Pat -> Q Pat
lrP i n p
  | n == 0       = fail "lrP: impossible"
  | n == 1       = p
  | i <= div n 2 = conP 'L1 [lrP i     (div n 2) p]
  | otherwise    = conP 'R1 [lrP (i-m) (n-m)     p]
                     where m = div n 2

lrE :: Int -- Constructor index
    -> Int -- Total number of constructors
    -> Q Exp -> Q Exp
lrE i n e
  | n == 0       = fail "lrE: impossible"
  | n == 1       = e
  | i <= div n 2 = conE 'L1 `appE` lrE i     (div n 2) e
  | otherwise    = conE 'R1 `appE` lrE (i-m) (n-m)     e
                     where m = div n 2

isNewtypeVariant :: DatatypeVariant -> Bool
isNewtypeVariant Datatype        = False
isNewtypeVariant Newtype         = True
isNewtypeVariant DataInstance    = False
isNewtypeVariant NewtypeInstance = True

-- | Extract 'Just' the 'Name' from a type variable. If the argument 'Type' is
-- not a type variable, return 'Nothing'.
varTToName_maybe :: Type -> Maybe Name
varTToName_maybe (VarT n)   = Just n
varTToName_maybe (SigT t _) = varTToName_maybe t
varTToName_maybe _          = Nothing

-- | Extract the 'Name' from a type variable. If the argument 'Type' is not a
-- type variable, throw an error.
varTToName :: Type -> Name
varTToName = fromMaybe (error "Not a type variable!") . varTToName_maybe

zipWith4M :: Monad m => (a -> b -> c -> d -> m e)
          -> [a] -> [b] -> [c] -> [d] -> m [e]
zipWith4M _ []     _      _      _      = pure []
zipWith4M _ _      []     _      _      = pure []
zipWith4M _ _      _      []     _      = pure []
zipWith4M _ _      _      _      []     = pure []
zipWith4M f (x:xs) (y:ys) (z:zs) (a:as)
  = do r  <- f x y z a
       rs <- zipWith4M f xs ys zs as
       pure $ r:rs

-- | Compose a function with itself n times.  (nth rather than twice)
nTimes :: Int -> (a -> a) -> (a -> a)
nTimes 0 _ = id
nTimes 1 f = f
nTimes n f = f . nTimes (n-1) f

-- | Generate a list of fresh names with a common prefix, and numbered suffixes.
newNameList :: String -> Int -> Q [Name]
newNameList prefix n = traverse (newName . (prefix ++) . show) [1..n]

gatherExistentials :: [ConstructorInfo] -> [TyVarBndr]
gatherExistentials = concatMap constructorVars

gatherConstraints :: [ConstructorInfo] -> [Pred]
gatherConstraints = concatMap constructorContext

gatherFields :: [ConstructorInfo] -> [Type]
gatherFields = concatMap constructorFields

-- | Detect if a name occurs as an argument to some type family.
isInTypeFamilyApp :: Name -> Type -> Q Bool
isInTypeFamilyApp name = go
  where
    go :: Type -> Q Bool
    go ty@AppT{}          = case splitAppTs ty of
                              (tyFun, tyArgs)
                                |  ConT tcName <- tyFun
                                -> goTyConApp tcName tyArgs
                                |  otherwise
                                -> or <$> traverse go (tyFun:tyArgs)
    go (InfixT ty1 n ty2) = go (ConT n `AppT` ty1 `AppT` ty2)
    go (SigT ty ki)       = liftA2 (||) (go ty) (go ki)
    go (ParensT ty)       = go ty
    go _                  = pure False

    goTyConApp :: Name -> [Type] -> Q Bool
    goTyConApp tcName tcArgs = do
      info <- reify tcName
      case info of
        FamilyI (OpenTypeFamilyD (TypeFamilyHead _ bndrs _ _)) _
          -> withinFirstArgs bndrs
        FamilyI (ClosedTypeFamilyD (TypeFamilyHead _ bndrs _ _) _) _
          -> withinFirstArgs bndrs
        _ -> pure False
      where
        withinFirstArgs :: [a] -> Q Bool
        withinFirstArgs bndrs =
          let firstArgs = take (length bndrs) tcArgs
          in pure $ name `elem` freeVariables firstArgs

-- | Split a chain of 'AppT's to a linear chain of arguments.
splitAppTs :: Type -> (Type, [Type])
splitAppTs ty = split ty ty []
  where
    split :: Type -> Type -> [Type] -> (Type, [Type])
    split _      (AppT ty1 ty2)     args = split ty1 ty1 (ty2:args)
    split origTy (InfixT ty1 n ty2) args = split origTy (ConT n `AppT` ty1 `AppT` ty2) args
    split origTy (SigT ty' _)       args = split origTy ty' args
    split origTy (ParensT ty')      args = split origTy ty' args
    split origTy _                  args = (origTy, args)

-- | Resolve all of the type synonyms in a 'ConstructorInfo'.
resolveConSynonyms :: ConstructorInfo -> Q ConstructorInfo
resolveConSynonyms con@(ConstructorInfo{ constructorVars    = vars
                                       , constructorContext = context
                                       , constructorFields  = fields
                                       }) = do
  vars'    <- traverse (\tvb ->
                         case tvb of
                           PlainTV{} -> pure tvb
                           KindedTV n k -> KindedTV n <$> resolveTypeSynonyms k) vars
  context' <- traverse resolveTypeSynonyms context
  fields'  <- traverse resolveTypeSynonyms fields
  pure $ con{ constructorVars = vars'
            , constructorContext = context'
            , constructorFields  = fields'
            }
