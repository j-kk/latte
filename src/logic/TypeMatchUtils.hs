{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}

module TypeMatchUtils where

import qualified AbsLatte as Abs
import AbsLatte
    ( BNFC'Position,
      Ident,
      Type,
      Stmt',
      Block'(..),
      Arg'(..),
      TopDef'(..), ClMember, ClassExt)
import qualified Prelude as C
import PrintLatte (Print (prt), prPrec, concatD, doc)
import GHC.Show
import Data.Maybe (Maybe (Just, Nothing))

isInt :: Abs.Type -> C.Bool
isInt (Abs.Int _) = C.True
isInt _ = C.False

isStr :: Abs.Type -> C.Bool
isStr (Abs.Str _) = C.True
isStr _ = C.False

isBool :: Abs.Type -> C.Bool
isBool (Abs.Bool _) = C.True
isBool _ = C.False

isVoid :: Abs.Type -> C.Bool
isVoid (Abs.Void _) = C.True
isVoid _ = C.False

isFun :: Abs.Type -> C.Bool
isFun Abs.Fun {} = C.True
isFun _ = C.False

isArray :: Abs.Type -> C.Bool
isArray (Abs.Array _ _) = C.True
isArray _ = C.False

intNP :: Abs.Type' BNFC'Position
intNP = Abs.Int Abs.BNFC'NoPosition

strNP :: Abs.Type' BNFC'Position
strNP = Abs.Str Abs.BNFC'NoPosition

boolNP :: Abs.Type' BNFC'Position
boolNP = Abs.Bool Abs.BNFC'NoPosition

voidNP :: Abs.Type' BNFC'Position
voidNP = Abs.Void Abs.BNFC'NoPosition

funNP :: Abs.Type' BNFC'Position -> [Abs.Type' BNFC'Position] -> Abs.Type' BNFC'Position
funNP = Abs.Fun Abs.BNFC'NoPosition

fnDefNP :: Abs.Type' BNFC'Position
    -> Ident
    -> [Arg' BNFC'Position]
    -> Block' BNFC'Position
    -> TopDef' BNFC'Position
fnDefNP = Abs.FnDef Abs.BNFC'NoPosition

blockNP :: [Stmt' BNFC'Position] -> Block' BNFC'Position
blockNP = Abs.Block Abs.BNFC'NoPosition

argNP :: Abs.Type' BNFC'Position -> Ident -> Arg' BNFC'Position
argNP = Abs.Arg Abs.BNFC'NoPosition

isFnDef :: Abs.TopDef -> C.Bool
isFnDef = \case
  Abs.FnDef {} -> C.True
  _ -> C.False

noInitNP :: Ident -> Abs.Item' BNFC'Position
noInitNP = Abs.NoInit Abs.BNFC'NoPosition

initNP :: Ident -> Abs.Expr' BNFC'Position -> Abs.Item' BNFC'Position
initNP = Abs.Init Abs.BNFC'NoPosition

noPosition :: BNFC'Position
noPosition = Abs.BNFC'NoPosition
data BaseType
    = Int | Str | Bool | Void | Fun BaseType [BaseType] | Array BaseType | Cls Ident
  deriving (C.Eq, C.Ord, C.Show, C.Read)

typeToBase :: Type -> BaseType
typeToBase t = case t of
    (Abs.Int _) -> Int
    (Abs.Bool _) -> Bool
    (Abs.Str _) -> Str
    (Abs.Void _) -> Void
    (Abs.Fun _ ret args) -> Fun (typeToBase ret) (C.map typeToBase args)
    (Abs.Array _ atype) -> Array C.$ typeToBase atype
    (Abs.Cls _ ident) -> Cls ident

baseToType :: BaseType -> Type
baseToType bt = case bt of
  Int -> Abs.Int Abs.BNFC'NoPosition
  Str -> Abs.Str Abs.BNFC'NoPosition
  Bool -> Abs.Bool Abs.BNFC'NoPosition
  Void -> Abs.Void Abs.BNFC'NoPosition
  Fun bt' bts -> Abs.Fun Abs.BNFC'NoPosition (baseToType bt') (C.map baseToType bts)
  Array bt' -> Abs.Array Abs.BNFC'NoPosition (baseToType bt')
  Cls id -> Abs.Cls Abs.BNFC'NoPosition id

extractIdentStr :: Ident -> C.String
extractIdentStr (Abs.Ident s) = s

getArrayItemType :: BaseType -> Maybe BaseType
getArrayItemType (Array bt) = Just bt
getArrayItemType _ = Nothing
instance Print BaseType where
  prt i = \case
    Int -> prPrec i 0 (concatD [doc (showString "int")])
    Str -> prPrec i 0 (concatD [doc (showString "string")])
    Bool -> prPrec i 0 (doc (showString "boolean"))
    Void -> prPrec i 0 (doc (showString "void"))
    Fun type_ types -> prPrec i 0 (concatD [prt 0 type_, doc (showString "("), prt 0 types, doc (showString ")")])
    Array dtype -> prPrec i 0 (concatD [prt i dtype, doc (showString "[]")])
    Cls ident -> prPrec i 0 (concatD [doc (showString (show ident))])

class HasIdent a where
  hasIdent :: a -> Ident

instance HasIdent ClMember where
  hasIdent (Abs.Attr _ _ ident) = ident
  hasIdent (Abs.Meth _ _ ident _ _) = ident

instance HasIdent Abs.TopDef where
  hasIdent (Abs.ClDef _ ident _ _) = ident
  hasIdent (Abs.FnDef _ _ ident _ _) = ident

class MaybeIdent a where
  maybeIdent :: a -> Maybe Ident

instance MaybeIdent ClassExt where
  maybeIdent (Abs.NoExt _ ) = Nothing
  maybeIdent (Abs.Ext _ ident) = Just ident

isMeth :: ClMember -> C.Bool
isMeth Abs.Meth {} = C.True
isMeth Abs.Attr {} = C.False

isAttr :: ClMember  -> C.Bool
isAttr = C.not C.. isMeth


isEq :: Abs.RelOp -> C.Bool
isEq = \case 
  Abs.EQU ma -> C.True
  _ -> C.False

isNEq :: Abs.RelOp -> C.Bool
isNEq = \case 
  Abs.NE ma -> C.True
  _ -> C.False
