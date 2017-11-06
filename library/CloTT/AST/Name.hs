{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.AST.Name where

import Data.Data
import Data.String (IsString(..))
import Data.List (genericLength)
import Data.Text.Prettyprint.Doc
import Data.Char (isUpper, isLower)

data Name 
  = UName String
  | MName Integer
  | DeBruijn Integer
  deriving (Ord, Eq, Data, Typeable)

instance Show Name where
  show x = 
    case x of
      UName s -> s
      MName i -> '`' : intToString i where
      DeBruijn i -> '`' : show i

instance Pretty Name where
  pretty = fromString . show

intToString :: Integer -> String
intToString i = (chars !! (fromIntegral $ i `mod` chrlen)) : suffix where
  suffix | i - chrlen >= 0 = show ((i - chrlen) `div` chrlen)
         | otherwise      = ""
  chars = ['a'..'z']
  chrlen = genericLength chars

instance IsString Name where
  fromString = UName

mname :: Integer -> Name
mname = MName

isVarNm, isConstrNm :: Name -> Bool
isVarNm (UName (x:xs)) = isLower x
isVarNm _              = False

isConstrNm (UName (x:xs)) = isUpper x
isConstrNm _              = False
