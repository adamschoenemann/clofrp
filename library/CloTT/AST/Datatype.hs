{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module CloTT.AST.Datatype 
( module CloTT.AST.Datatype
, module CloTT.AST.Constr
) where

import Data.Data (Data, Typeable)
import Data.Text.Prettyprint.Doc

import CloTT.Annotated 
import CloTT.AST.Name
import CloTT.AST.Type
import CloTT.AST.Kind
import CloTT.AST.Constr

data Datatype a = 
  Datatype
    { dtName    :: Name
    , dtBound   :: [(Name, Kind)]
    , dtConstrs :: [Constr a]
    , dtDeriving :: [String]
    } deriving (Show, Eq, Data, Typeable)


instance Pretty (Datatype a) where
  pretty (Datatype {dtName = nm, dtBound = b, dtConstrs = cs, dtDeriving = ds}) =
     "data" <+> pretty nm <+> (sep $ map pretty b) <+> "=" <+> (encloseSep "" "" " | " $ map pretty cs)
     <> line <> "deriving" <+> tupled (map pretty ds)

instance Unann (Datatype a) (Datatype ()) where
  unann dt@(Datatype {dtConstrs = cstrs}) =
     dt {dtConstrs = map unannConstr cstrs}

dtKind :: Datatype a -> Kind
dtKind (Datatype {dtBound = bs}) = foldr (\k acc -> k :->*: acc) Star (map snd bs)