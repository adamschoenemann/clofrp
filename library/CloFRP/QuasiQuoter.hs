{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE OverloadedStrings #-}

module CloFRP.QuasiQuoter where

import qualified CloFRP.Parser.Expr as P
import qualified CloFRP.Parser.Decl as P
import qualified CloFRP.Parser.Type as P
import qualified CloFRP.Parser.Prog as P
import qualified CloFRP.Parser.Lang as P

import CloFRP.AST.Name
import CloFRP.Interop
import CloFRP.Utils (findMap)
import CloFRP.Eval (progToEval, initEvalState)
import CloFRP.Check.Prog (runCheckProg)
import CloFRP.Check.TypingM (runTypingM0, prettyTree)
import CloFRP.Annotated
import CloFRP.Pretty 
import CloFRP.Utils ()
import CloFRP.Compiler

import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Language.Haskell.TH.Syntax
import Text.Parsec (parse, SourcePos)
import Text.Parsec.Combinator (eof)
import Text.Parsec.String (Parser)

liftParse :: Monad m => Parser p -> String -> m p
liftParse p s = either (fail . show) pure $ parse (P.ws *> p <* eof) "" s

unsafeExpr :: QuasiQuoter
unsafeExpr = QuasiQuoter 
  { quoteExp  = unsafeQuoteExpr
  , quotePat  = undefined
  , quoteDec  = undefined
  , quoteType = undefined
  } where
    unsafeQuoteExpr s = do
      ast <- liftParse P.expr s
      liftData ast

unsafeType :: QuasiQuoter
unsafeType = QuasiQuoter 
  { quoteExp  = unsafeQuoteType
  , quotePat  = undefined
  , quoteDec  = undefined
  , quoteType = undefined
  } where
    unsafeQuoteType s = do
      ast <- liftParse P.typep s
      liftData ast

unsafeDecl :: QuasiQuoter
unsafeDecl = QuasiQuoter 
  { quoteExp  = unsafeQuoteDecl
  , quotePat  = undefined
  , quoteDec  = undefined
  , quoteType = undefined
  } where
    unsafeQuoteDecl s = do
      ast <- liftParse P.decl s
      liftData ast

unsafeProg :: QuasiQuoter
unsafeProg = QuasiQuoter 
  { quoteExp  = unsafeQuoteProg
  , quotePat  = undefined
  , quoteDec  = undefined
  , quoteType = undefined
  } where
    unsafeQuoteProg s = do
      ast <- liftParse P.prog s
      liftData ast

clofrp :: QuasiQuoter
clofrp = QuasiQuoter
  { quoteExp  = quoteclofrp
  , quotePat  = undefined
  , quoteDec  = undefined
  , quoteType = undefined
  } where
    quoteclofrp :: String -> Q Exp
    quoteclofrp s = do
      prog <- liftParse P.prog s
      checkProgQExp prog
      (expr, ty, rd) <- progToEvalQExp prog 
      let sing  = typeToSingExp ty
      let exprQ = liftData expr
      let rdQ   = liftData rd
      let stQ   = liftData (initEvalState @(SourcePos))
      [|CloFRP $(rdQ) $(stQ) $(exprQ) $(sing)|]
    
    checkProgQExp prog =
      case runCheckProg mempty prog of
        (Left err, _, tree) -> fail (showW 200 (pretty err <> line <> "progres:" <> line <> prettyTree tree))
        (Right _, _, _)  -> pure ()
    
    progToEvalQExp prog =
      case runTypingM0 (progToEval @(SourcePos) (UName "main") prog) mempty of
        (Right (expr, ty, rd), _, _) -> pure (expr, ty, rd)
        (Left (err,_), _, _) -> fail (pps err)

hsclofrp :: QuasiQuoter
hsclofrp = QuasiQuoter
  { quoteExp  = quoteCloFRPExpr
  , quotePat  = undefined
  , quoteDec  = quoteclofrp
  , quoteType = undefined
  } where
    quoteCloFRPExpr :: String -> Q Exp
    quoteCloFRPExpr s = do
      ast <- liftParse P.expr s
      exprToHaskExpQ ast

    quoteclofrp :: String -> Q [Dec]
    quoteclofrp s = do
      prog <- liftParse P.prog s
      checkProgQExp prog
      progToHaskDecls prog

    checkProgQExp prog =
      case runCheckProg mempty prog of
        (Left err, _, tree) -> fail (showW 200 (pretty err <> line <> "progres:" <> line <> prettyTree tree))
        (Right _, _, _)  -> pure ()
