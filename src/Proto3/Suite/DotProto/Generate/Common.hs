{-# LANGUAGE CPP               #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MultiWayIf        #-}
{-# LANGUAGE NamedFieldPuns    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE QuasiQuotes       #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}
{-# LANGUAGE ViewPatterns      #-}

module Proto3.Suite.DotProto.Generate.Common where
import           Control.Applicative
import           Control.Arrow                  ((&&&))
import           Control.Monad.Except
import           Control.Lens                   (ix, over)
import           Data.Bifunctor                 (first)
import           Data.Char
import           Data.Coerce
import           Data.Either                    (partitionEithers)
import           Data.List                      (find, intercalate, nub, sortBy,
                                                 stripPrefix)
import qualified Data.Map                       as M
import           Data.Maybe                     (catMaybes, fromMaybe)
import           Data.Monoid
import           Data.Ord                       (comparing)
import qualified Data.Set                       as S
import           Data.String                    (fromString)
import qualified Data.Text                      as T
import           Data.Tuple                     (swap)
import           Filesystem.Path.CurrentOS      ((</>), (<.>))
import qualified Filesystem.Path.CurrentOS      as FP
import           Language.Haskell.Pretty
import           Language.Haskell.Syntax
import           Language.Haskell.Parser        (ParseResult(..), parseModule)
import qualified NeatInterpolation              as Neat
import           Prelude                        hiding (FilePath)
import           Proto3.Suite.DotProto
import           Proto3.Suite.DotProto.Rendering (Pretty(..))
import           Proto3.Suite.DotProto.Internal
import           Proto3.Wire.Types              (FieldNumber (..))
import           System.IO                      (writeFile, readFile)
import           Text.Parsec                    (ParseError)
import           Turtle                         (FilePath)
import qualified Turtle
import           Turtle.Format                  ((%))
import qualified Turtle.Format                  as F

#if !(MIN_VERSION_mtl(2,2,2))
liftEither :: MonadError e m => Either e a -> m a
liftEither x =
    case x of
        Left  e -> throwError e
        Right a -> return a
#endif

foldMapM :: (Foldable t, Monad m, Monoid b) => (a -> m b) -> t a -> m b
foldMapM f = fmap fold . traverse f

mapKeysM :: (Monad m) => (k1 -> m k2) -> M.Map k1 a -> m (M.Map k2 a)
mapKeysM f = fmap M.fromList . traverse (fmap swap . traverse f . swap) . M.assocs

data CompileError
  = CircularImport          FilePath
  | CompileParseError       ParseError
  | InternalEmptyModulePath
  | InternalError           String
  | InvalidMethodName       DotProtoIdentifier
  | InvalidTypeName         String
  | InvalidMapKeyType       String
  | NoPackageDeclaration
  | NoSuchType              DotProtoIdentifier
  | Unimplemented           String
  deriving (Show, Eq)


-- * Type-tracking data structures

-- | Whether a definition is an enumeration or a message
data DotProtoKind = DotProtoKindEnum
                  | DotProtoKindMessage
                  deriving (Show, Eq, Ord, Enum, Bounded)

-- | Information about messages and enumerations
data DotProtoTypeInfo = DotProtoTypeInfo
  { dotProtoTypeInfoPackage    :: DotProtoPackageSpec
     -- ^ The package this type is defined in
  , dotProtoTypeInfoParent     :: DotProtoIdentifier
    -- ^ The message this type is nested under, or 'Anonymous' if it's top-level
  , dotProtoTypeChildContext   :: TypeContext
    -- ^ The context that should be used for declarations within the
    --   scope of this type
  , dotProtoTypeInfoKind       :: DotProtoKind
    -- ^ Whether this type is an enumeration or message
  , dotProtoTypeInfoModulePath :: Path
    -- ^ The include-relative module path used when importing this module
  } deriving Show

-- | A mapping from .proto type identifiers to their type information
type TypeContext = M.Map DotProtoIdentifier DotProtoTypeInfo

-- ** Generating type contexts from ASTs

dotProtoTypeContext :: MonadError CompileError m => DotProto -> m TypeContext
dotProtoTypeContext DotProto { protoDefinitions
                             , protoMeta = DotProtoMeta modulePath
                             }
  = foldMapM (definitionTypeContext modulePath) protoDefinitions

definitionTypeContext
    :: MonadError CompileError m => Path -> DotProtoDefinition -> m TypeContext
definitionTypeContext modulePath (DotProtoMessage msgIdent parts) = do
  let updateDotProtoTypeInfoParent =
          fmap (\p -> tyInfo { dotProtoTypeInfoParent = p })
          . concatDotProtoIdentifier msgIdent
          . dotProtoTypeInfoParent

  childTyContext <-
      mapM updateDotProtoTypeInfoParent =<<
        foldMapM (definitionTypeContext modulePath)
                 [def | DotProtoMessageDefinition def <- parts]

  qualifiedChildTyContext <- mapKeysM (concatDotProtoIdentifier msgIdent) childTyContext

  let tyInfo = DotProtoTypeInfo { dotProtoTypeInfoPackage = DotProtoNoPackage
                                , dotProtoTypeInfoParent =  Anonymous
                                , dotProtoTypeChildContext = childTyContext
                                , dotProtoTypeInfoKind = DotProtoKindMessage
                                , dotProtoTypeInfoModulePath = modulePath
                                }

  pure $ M.singleton msgIdent tyInfo <> qualifiedChildTyContext

definitionTypeContext modulePath (DotProtoEnum enumIdent _) = do
  let tyInfo = DotProtoTypeInfo { dotProtoTypeInfoPackage = DotProtoNoPackage
                                , dotProtoTypeInfoParent =  Anonymous
                                , dotProtoTypeChildContext = mempty
                                , dotProtoTypeInfoKind = DotProtoKindEnum
                                , dotProtoTypeInfoModulePath = modulePath
                                }
  pure (M.singleton enumIdent tyInfo)
definitionTypeContext _ _ = pure mempty

concatDotProtoIdentifier :: MonadError CompileError m
                         => DotProtoIdentifier -> DotProtoIdentifier -> m DotProtoIdentifier
concatDotProtoIdentifier i1 i2 = case (i1, i2) of
  (Qualified{} ,  _          ) -> internalError "concatDotProtoIdentifier: Qualified"
  (_           , Qualified{} ) -> internalError "concatDotProtoIdentifier Qualified"
  (Anonymous   , Anonymous   ) -> pure Anonymous
  (Anonymous   , b           ) -> pure b
  (a           , Anonymous   ) -> pure a
  (Single a    , b           ) -> concatDotProtoIdentifier (Dots (Path [a])) b
  (a           , Single b    ) -> concatDotProtoIdentifier a (Dots (Path [b]))

concatDotProtoIdentifier (Dots (Path a)) (Dots (Path b)) = pure . Dots . Path $ a ++ b

camelCased :: String -> String
camelCased s = do
  (prev, cur) <- zip (Nothing:map Just s) (map Just s ++ [Nothing])
  case (prev, cur) of
    (Just '_', Just x)
      | isAlpha x        -> pure (toUpper x)
    (Just '_', Nothing)  -> pure '_'
    (Just '_', Just '_') -> pure '_'
    (_, Just '_')        -> empty
    (_, Just x)          -> pure x
    (_, _)               -> empty

typeLikeName :: MonadError CompileError m => String -> m String
typeLikeName ident@(c:cs)
  | isUpper c = pure (camelCased ident)
  | isLower c = pure (camelCased (toUpper c : cs))
  | '_'  == c = pure (camelCased ('X':ident))
typeLikeName ident = invalidTypeNameError ident

fieldLikeName :: String -> String
fieldLikeName ident@(c:_)
  | isUpper c = let (prefix, suffix) = span isUpper ident
                in map toLower prefix ++ suffix
fieldLikeName ident = ident

prefixedEnumFieldName :: String -> String -> String
prefixedEnumFieldName enumName fieldName = enumName <> fieldName

prefixedConName :: MonadError CompileError m => String -> String -> m String
prefixedConName msgName conName =
  (msgName ++) <$> typeLikeName conName

-- TODO: This should be ~:: MessageName -> FieldName -> ...; same elsewhere, the
-- String types are a bit of a hassle.
prefixedFieldName :: MonadError CompileError m => String -> String -> m String
prefixedFieldName msgName fieldName =
  (fieldLikeName msgName ++) <$> typeLikeName fieldName

dpIdentUnqualName :: MonadError CompileError m => DotProtoIdentifier -> m String
dpIdentUnqualName (Single name)       = pure name
dpIdentUnqualName (Dots (Path names)) = pure (last names)
dpIdentUnqualName (Qualified _ next)  = dpIdentUnqualName next
dpIdentUnqualName Anonymous           = internalError "dpIdentUnqualName: Anonymous"

dpIdentQualName :: MonadError CompileError m => DotProtoIdentifier -> m String
dpIdentQualName (Single name)       = pure name
dpIdentQualName (Dots (Path names)) = pure (intercalate "." names)
dpIdentQualName (Qualified _ _)     = internalError "dpIdentQualName: Qualified"
dpIdentQualName Anonymous           = internalError "dpIdentQualName: Anonymous"

-- ** Codegen bookkeeping helpers

-- | Bookeeping for qualified fields
data QualifiedField = QualifiedField
  { recordFieldName :: FieldName
  , fieldInfo       :: FieldInfo
  } deriving Show

-- | Bookkeeping for fields
data FieldInfo
  = FieldOneOf OneofField
  | FieldNormal FieldName FieldNumber DotProtoType [DotProtoOption]
  deriving Show

-- | Bookkeeping for oneof fields
data OneofField = OneofField
  { oneofType :: String
  , subfields :: [OneofSubfield]
  } deriving Show

-- | Bookkeeping for oneof subfields
data OneofSubfield = OneofSubfield
  { subfieldNumber   :: FieldNumber
  , subfieldConsName :: String
  , subfieldName     :: FieldName
  , subfieldType     :: DotProtoType
  , subfieldOptions  :: [DotProtoOption]
  } deriving Show

getQualifiedFields :: MonadError CompileError m
                   => String -> [DotProtoMessagePart] -> m [QualifiedField]
getQualifiedFields msgName msgParts = fmap catMaybes . forM msgParts $ \case
  DotProtoMessageField (DotProtoField fieldNum dpType fieldIdent options _) -> do
    fieldName <- dpIdentUnqualName fieldIdent
    qualName  <- prefixedFieldName msgName fieldName
    pure $ Just $ QualifiedField { recordFieldName = coerce qualName
                                 , fieldInfo = FieldNormal (coerce fieldName) fieldNum dpType options
                                 }

  DotProtoMessageOneOf _ [] ->
    throwError (InternalError "getQualifiedFields: encountered oneof with no oneof fields")

  DotProtoMessageOneOf oneofIdent fields -> do
    ident <- dpIdentUnqualName oneofIdent
    oneofName <- prefixedFieldName msgName ident
    oneofTypeName <- prefixedConName msgName ident
    fieldElems <- sequence
                    [ do s <- dpIdentUnqualName subFieldName
                         c <- prefixedConName oneofTypeName s
                         pure (OneofSubfield fieldNum c (coerce s) dpType options)
                    | DotProtoField fieldNum dpType subFieldName options _ <- fields
                    ]
    pure $ Just $ QualifiedField { recordFieldName = coerce oneofName
                                 , fieldInfo = FieldOneOf (OneofField ident fieldElems)
                                 }
  _ ->
    pure Nothing

-- | Project qualified fields, given a projection function per field type.
onQF :: (FieldName -> FieldNumber -> a) -- ^ projection for normal fields
     -> (OneofField -> a)               -- ^ projection for oneof fields
     -> QualifiedField
     -> a
onQF f _ (QualifiedField _ (FieldNormal fldName fldNum _ _)) = f fldName fldNum
onQF _ g (QualifiedField _ (FieldOneOf fld))                 = g fld

fieldBinder :: FieldNumber -> String
fieldBinder = ("f" ++) . show

oneofSubBinder :: OneofSubfield -> String
oneofSubBinder = fieldBinder . subfieldNumber

oneofSubDisjunctBinder :: [OneofSubfield] -> String
oneofSubDisjunctBinder = intercalate "_or_" . fmap oneofSubBinder

isMap :: DotProtoType -> Bool
isMap Map{} = True
isMap _ = False

internalError :: MonadError CompileError m => String -> m a
internalError = throwError . InternalError

invalidTypeNameError :: MonadError CompileError m => String -> m a
invalidTypeNameError = throwError . InvalidTypeName

_unimplementedError :: MonadError CompileError m => String -> m a
_unimplementedError = throwError . Unimplemented

invalidMethodNameError :: MonadError CompileError m => DotProtoIdentifier -> m a
invalidMethodNameError = throwError . InvalidMethodName

noSuchTypeError :: MonadError CompileError m => DotProtoIdentifier -> m a
noSuchTypeError = throwError . NoSuchType

protoPackageName :: MonadError CompileError m => DotProtoPackageSpec -> m DotProtoIdentifier
protoPackageName (DotProtoPackageSpec name) = pure name
protoPackageName DotProtoNoPackage = throwError NoPackageDeclaration
