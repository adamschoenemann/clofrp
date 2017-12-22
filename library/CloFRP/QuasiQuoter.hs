{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}

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
import CloFRP.Check.TypingM (runTypingM0)
import CloFRP.Annotated
import CloFRP.Pretty (ppsw, pps)
import CloFRP.Utils ()

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

clott :: QuasiQuoter
clott = QuasiQuoter
  { quoteExp  = quoteClott
  , quotePat  = undefined
  , quoteDec  = undefined
  , quoteType = undefined
  } where
    quoteClott :: String -> Q Exp
    quoteClott s = do
      prog <- liftParse P.prog s
      case runCheckProg mempty prog of
        (Left err, _, _) -> fail (ppsw 200 err)
        (Right _,  _, _) -> 
          case runTypingM0 (progToEval @(SourcePos) (UName "main") prog) mempty of
            (Right (expr, ty, rd), _, _) -> do
              let sing = typeToSingExp ty
              let exprQ = liftData expr
              let rdQ = liftData rd
              let stQ = liftData (initEvalState @(SourcePos))
              [|CloFRP $(rdQ) $(stQ) $(exprQ) $(sing)|]
            (Left (err,_), _, _) -> fail (pps err)
