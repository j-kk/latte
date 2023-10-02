{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module Common where
import qualified TypeMatchUtils as TM
import AbsLatte (TopDef, Ident (Ident))

builtInFunctions :: [TopDef]
builtInFunctions = [
    TM.fnDefNP TM.voidNP (Ident "printInt") [TM.argNP TM.intNP (Ident "x")] (TM.blockNP []),
    TM.fnDefNP TM.voidNP (Ident "printString") [TM.argNP TM.strNP (Ident "x")] (TM.blockNP []),
    TM.fnDefNP TM.voidNP (Ident "error") [] (TM.blockNP []),
    TM.fnDefNP TM.intNP (Ident "readInt") [] (TM.blockNP []),
    TM.fnDefNP TM.strNP (Ident "readString") [] (TM.blockNP []),
    TM.fnDefNP TM.strNP (Ident "____concatStr") [TM.argNP TM.strNP (Ident "x"), TM.argNP TM.strNP (Ident "y")] (TM.blockNP []),
    TM.fnDefNP TM.intNP (Ident "____compareStr") [TM.argNP TM.strNP (Ident "x"), TM.argNP TM.strNP (Ident "y")] (TM.blockNP []),
    TM.fnDefNP TM.voidNP (Ident "____calloc") [TM.argNP TM.intNP (Ident "a"), TM.argNP TM.intNP (Ident "b")] (TM.blockNP [])
    ]