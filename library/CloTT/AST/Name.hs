{-# LANGUAGE DeriveDataTypeable #-}

module CloTT.AST.Name where

import Data.Data
import Data.String (IsString(..))
import Data.List (genericLength)
import Data.Text.Prettyprint.Doc

data Name 
  = UName String
  | MName Integer
  deriving (Ord, Eq, Data, Typeable)

instance Show Name where
  show x = 
    case x of
      UName x -> x
      MName i -> '`' : intToString i where

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