{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE DeriveDataTypeable #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE DuplicateRecordFields #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}

module CloTT.AST.Parsed ( 
    module CloTT.AST.Parsed
  , module CloTT.AST.Name
  , P.Prim(..)
  , Unann(..)
) where

import CloTT.Annotated 
import CloTT.AST.Name
import Data.String (IsString(..))
import qualified Data.Set as S
import Data.Data (Data, Typeable)
import Data.Char (isUpper)
import qualified CloTT.AST.Prim as P
import Data.Text.Prettyprint.Doc

type Type a s = Annotated a (Type' a s)

data TySort = Mono | Poly deriving (Show, Eq)

data Type' :: * -> TySort -> * where
  TFree   :: Name                       -> Type' a s
  TVar    :: Name                       -> Type' a s
  TExists :: Name                       -> Type' a s
  TApp    :: Type a s    -> Type a s    -> Type' a s
  (:->:)  :: Type a s    -> Type a s    -> Type' a s
  Forall  :: Name        -> Type a Poly -> Type' a Poly

deriving instance Eq a       => Eq (Type' a s)
deriving instance Data a     => Data (Type' a Poly)
deriving instance Typeable a => Typeable (Type' a Poly)

prettyT' :: Bool -> Type' a s -> Doc ann
prettyT' pars = \case 
  TFree n    -> fromString . show $ n
  TVar n     -> fromString . show $ n
  TExists n  -> "∃" <> fromString (show n)
  TApp x y   -> parensIf $ prettyT False x <+> prettyT True y
  x :->: y   -> parensIf $ prettyT True x  <> softline <> "->" <+> prettyT False y

  Forall n t -> 
    let (ns, t') = collect t
        bound = hsep $ map (fromString . show) (n:ns)
    in  parensIf $ "∀" <> bound <> dot <+> prettyT False t'
  where
    collect :: Type a s -> ([Name], Type a s)
    collect (A _ (Forall n t)) = 
      let (ns, t') = collect t
      in  (n:ns, t')
    collect t                  = ([], t)

    parensIf = if pars then parens else id


prettyT :: Bool -> Type a s -> Doc ann
prettyT n (A _ t) = prettyT' n t

instance Pretty (Type' a s) where
  pretty = prettyT' False

instance Pretty (Type a s) where
  pretty (A _ t) = prettyT' False t

-- instance Show (Type' a s) where
--   show = show . pretty

deriving instance Show a => Show (Type' a s)

nameToType' :: Name -> Type' a s
nameToType' nm@(UName (c:cs)) | isUpper c = TFree nm
nameToType' nm = TVar nm

  
instance IsString (Type () s) where
  fromString [] = error "empty string not expected" 
  fromString (c:cs) 
    | isUpper c = A () . TFree . UName $ (c:cs)
    | otherwise = A () . TVar . UName  $ (c:cs)

infixl 9 @@:
(@@:) :: Type () Poly -> Type () Poly -> Type () Poly
a @@: b = A () $ a `TApp` b

infixr 2 @->:
(@->:) :: Type () s -> Type () s -> Type () s 
a @->: b = A () $ a :->: b

freeVars :: Type a s -> S.Set Name
freeVars (A _ ty) =
  case ty of
    TFree n -> S.singleton n
    TVar n  -> S.singleton n
    TExists n -> S.singleton n
    TApp x y -> freeVars x `S.union` freeVars y
    x :->: y  -> freeVars x `S.union` freeVars y
    Forall n t -> freeVars t `S.difference` S.singleton n

inFreeVars :: Name -> Type a s -> Bool
inFreeVars nm t = nm `S.member` freeVars t

asPolytype :: Type a s -> Type a Poly
asPolytype (A a ty) = A a $ 
  case ty of
    TFree x      -> TFree x
    TVar x       -> TVar x
    TExists x    -> TExists x
    t1 `TApp` t2 -> asPolytype t1 `TApp` asPolytype t2
    t1 :->:    t2 -> asPolytype t1 :->: asPolytype t2
    Forall x t   -> Forall x (asPolytype t) 

asMonotype :: Type a s -> Maybe (Type a Mono)
asMonotype (A a ty) = 
  case ty of
    TFree x -> pure (A a $ TFree x)
    TVar  x -> pure (A a $ TVar x)

    TExists x -> pure (A a $ TExists x)

    t1 `TApp` t2 -> (\x y -> A a $ TApp x y) <$> asMonotype t1 <*> asMonotype t2
    
    t1 :->: t2 -> (\x y -> A a (x :->: y)) <$> asMonotype t1 <*> asMonotype t2
    
    Forall _ _ -> Nothing


type Expr a = Annotated a (Expr' a)

data Expr' a
  = Var Name
  | Ann (Expr a) (Type a Poly)
  | App (Expr a) (Expr a)
  | Lam Name (Maybe (Type a Poly)) (Expr a)
  | Tuple (Expr a) (Expr a)
  | Case (Expr a) [(Pat a, Expr a)]
  | Prim P.Prim
 
deriving instance Eq a       => Eq (Expr' a)
deriving instance Data a     => Data (Expr' a)
deriving instance Typeable a => Typeable (Expr' a)
-- deriving instance Show a     => Show (Expr' a)

prettyE' :: Bool -> Expr' a -> Doc ann
prettyE' pars = \case 
  Var nm -> pretty nm
  Ann e t -> parensIf $ "the" <+> parens (pretty t) <+> prettyE False e
  App e1 e2 -> parensIf $ prettyE False e1 <+> prettyE True e2

  Lam nm mty e -> 
    let tyann = maybe "" (\t -> space <> ":" <+> pretty t) mty
    in  parensIf $ "λ" <> pretty nm <> tyann <+> "->" <+> prettyE False e

  Tuple e1 e2 -> parens (prettyE False e1 <> comma <+> prettyE False e2)

  Case e clauses ->
    "case" <+> prettyE False e <+> "of" <> softline <> (align $ sep $ map prettyC clauses)

  Prim p -> fromString . show $ p
  where
    prettyC (p, e) = "|" <+> pretty p <+> "->" <+> pretty e
    parensIf = if pars then parens else id

prettyE :: Bool -> Expr a -> Doc ann
prettyE n (A _ t) = prettyE' n t

instance Pretty (Expr' a) where
  pretty = prettyE' False

instance Pretty (Expr a) where
  pretty (A _ t) = prettyE' False t

instance Show (Expr' a) where
  show = show . pretty

infixr 2 :->*:

type Pat a = Annotated a (Pat' a)

data Pat' a  
  = Bind Name 
  | Match Name [Pat a]
  deriving (Eq, Data, Typeable)

prettyP :: Bool -> Pat a -> Doc ann
prettyP n (A _ t) = prettyP' n t

prettyP' :: Bool -> Pat' a -> Doc ann
prettyP' pars = \case
  Bind nm -> pretty nm
  Match nm pats -> parensIf $ pretty nm <> hsep (map (prettyP False) pats)
  where
    parensIf = if pars then parens else id

instance Pretty (Pat' a) where
  pretty = prettyP' False

instance Pretty (Pat a) where
  pretty (A _ t) = prettyP' False t

instance Show (Pat' a) where
  show = show . pretty

data Kind
  = Star
  | Kind :->*: Kind
  deriving (Show, Eq, Data, Typeable)

instance Pretty Kind where
  pretty = rndr False where
    rndr p = \case 
      Star -> "*"
      k1 :->*: k2 -> parensIf $ rndr True k1 <+> "->" <+> rndr False k2
      where
        parensIf = if p then parens else id
    


type Decl a = Annotated a (Decl' a)
data Decl' a
  = FunD Name (Expr a)
  -- |    name kind tvars  constructors
  | DataD Name Kind [Name] [Constr a]
  | SigD Name (Type a Poly)

deriving instance Show a     => Show (Decl' a)
deriving instance Eq a       => Eq (Decl' a)
deriving instance Data a     => Data (Decl' a)
deriving instance Typeable a => Typeable (Decl' a)

type Constr a = Annotated a (Constr' a)
data Constr' a
  = Constr Name [Type a Poly]

deriving instance Show a     => Show (Constr' a)
deriving instance Eq a       => Eq (Constr' a)
deriving instance Data a     => Data (Constr' a)
deriving instance Typeable a => Typeable (Constr' a)

data Prog a = Prog [Decl a]
  deriving (Show, Eq, Data, Typeable)

-- Here are some combinators for creating un-annotated expressions easily

var :: String -> Expr ()
var = A () . Var . UName

free :: Name -> Type () Poly
free nm = A () $ TFree nm

unit :: Expr ()
unit = A () . Prim $ P.Unit

nat :: Integer -> Expr ()
nat = A () . Prim . P.Nat

true :: Expr ()
true = A () . Prim . P.Bool $ True

false :: Expr ()
false = A () . Prim . P.Bool $ False

the :: Type () Poly -> Expr () -> Expr ()
the t e = A () $ Ann e t

constr :: Name -> [Type () Poly] -> Constr ()
constr nm ts = A () $ Constr nm ts

datad :: Name -> Kind -> [Name] -> [Constr ()] -> Decl ()
datad nm k b cs = A () $ DataD nm k b cs

fund :: Name -> Expr () -> Decl ()
fund nm e =  A () $ FunD nm e

sigd :: Name -> Type () Poly -> Decl ()
sigd nm t =  A () $ SigD nm t

prog :: [Decl ()] -> Prog ()
prog = Prog

forAll :: [String] -> Type () Poly -> Type () Poly
forAll nms t = foldr fn t $ map UName nms where
  fn nm acc = A () $ Forall nm acc

exists :: Name -> Type () a
exists nm = A () $ TExists nm

caseof :: Expr () -> [(Pat (), Expr ())] -> Expr ()
caseof expr clauses = A () $ Case expr clauses

match :: Name -> [Pat ()] -> Pat ()
match nm ps = A () $ Match nm ps

infixr 2 @->
infixr 2 @:->
infixl 9 @@
infixl 8 @*
infixl 3 @::

class IsString a => LamCalc a t | a -> t where
  (@->) :: String -> a -> a
  (@:->) :: (String, t) -> a -> a
  (@@) :: a -> a -> a
  (@*) :: a -> a -> a
  (@::) :: a -> t -> a


instance IsString (Pat ()) where
  fromString nm 
    | isUpper $ head nm = error "Pat.fromString must be given a lower-chase string"
    | otherwise         = A () . Bind . UName $ nm

instance IsString (Expr ()) where
  fromString = A () . Var . UName

instance LamCalc (Expr ()) (Type () Poly) where
  nm @-> e = A () $ Lam (UName nm) Nothing e
  (nm, t) @:-> e = A () $ Lam (UName nm) (Just t) e

  e1 @@ e2 = A () $ App e1 e2

  e1 @* e2 = A () $ Tuple e1 e2
  e @:: t = A () $ Ann e t

-- helper
conv :: (a -> t -> b) -> Annotated a t -> b
conv fn (A a e) = fn a e

conv' :: (a -> c) -> (t a -> t c) -> Annotated a (t a) -> Annotated c (t c)
conv' an fn (A a e) = A (an a) (fn e)

instance Unann (Type a s) (Type () s) where
  unann = unannT

unannT :: Type a s -> Type () s
unannT (A _ t) = A () $ unannT' t

instance Unann (Type' a s) (Type' () s) where
  unann = unannT'

unannT' :: Type' a s -> Type' () s
unannT' = \case 
  TFree x       -> TFree x
  TVar x        -> TVar x
  TExists x     -> TExists x
  t1 `TApp` t2  -> unannT t1 `TApp` unannT t2
  t1 :->: t2    -> unannT t1 :->: unannT t2
  Forall ts tau -> Forall ts (unannT tau)

instance Unann (Decl a) (Decl ()) where
  unann = unannD
  
unannD :: Decl a -> Decl ()
unannD = help go where
  help = conv' (const ())
  go = \case 
    FunD nm c -> FunD nm (unannE c) 
    DataD nm k b cstrs -> DataD nm k b (map unannConstr cstrs)
    SigD nm t  -> SigD nm (unannT t)

instance Unann (Prog a) (Prog ()) where
  unann = unannP

unannP :: Prog a -> Prog ()
unannP (Prog ds) = Prog (map unannD ds)

instance Unann (Constr a) (Constr ()) where
  unann = unannConstr

unannConstr :: Constr a -> Constr ()
unannConstr (A _ c) =
  case c of
    Constr nm ts -> A () $ Constr nm (map unannT ts)

instance Unann (Expr a) (Expr ()) where
  unann = unannE

unannE :: Expr a -> Expr ()
unannE (A _ expr0) = A () (unannE' expr0)

instance Unann (Expr' a) (Expr' ()) where
  unann = unannE'

unannE' :: Expr' a -> Expr' ()
unannE' = \case
  Var nm -> Var nm
  Ann e t -> Ann (unannE e) (unannT t)
  App e1 e2 -> App (unannE e1) (unannE e2)
  Lam nm mty e -> Lam nm (unannT <$> mty) (unannE e)
  Tuple e1 e2 -> Tuple (unannE e1) (unannE e2)
  Case e clauses -> Case (unannE e) $ map (\(p,c) -> (unannPat p, unannE c)) clauses
  Prim p -> Prim p
    
instance Unann (Pat a) (Pat ()) where
  unann = unannPat

unannPat :: Pat a -> Pat ()
unannPat (A _ p) = A () $ unannPat' p

instance Unann (Pat' a) (Pat' ()) where
  unann = unannPat'

unannPat' :: Pat' a -> Pat' ()
unannPat' p = case p of
  Bind nm -> Bind nm
  Match nm ps ->  Match nm (map unannPat ps)