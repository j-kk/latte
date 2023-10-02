{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
module PrintUtils where
import PrintLatte (Doc, Print (prt), prPrec, concatD, doc)
import AbsLatte (BNFC'Position)

prettyPrt :: Print a => a -> ShowS
prettyPrt a = foldr ((\x acc -> showString x . acc) . ($ "")) (showString "") (prt 0 a [])

prettyPrt' :: Print a => a -> String 
prettyPrt' a = prettyPrt a ""

docS :: String -> Doc
docS = doc . showString

instance Print BNFC'Position where
  prt i = \case
    Nothing -> prPrec i 0 $ concatD [doc (showString "Unknown position: ")]
    Just (line, position) -> prPrec i 0 $ concatD [docS "Line: ", doc . shows $ line, docS " position: ", doc . shows $  position, docS "   "]






