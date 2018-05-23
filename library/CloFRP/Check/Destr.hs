{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE DataKinds #-}

module CloFRP.Check.Destr where

import CloFRP.AST
import Data.Data
import Data.Text.Prettyprint.Doc
import Data.String (fromString)

-- A destructor which is elaborated from a pattern
data Destr a = Destr
  { name   :: Name
  , typ    :: PolyType a
  , bound  :: [(Name, Kind)]
  , args   :: [PolyType a]
  } deriving (Show, Eq, Data, Typeable)

unannDestr :: Destr a -> Destr ()
unannDestr (Destr n t b a) = 
  Destr n (unann t) b (map unann a)

instance Pretty (Destr a) where
  pretty = fromString . show . unannDestr