{-# LANGUAGE TemplateHaskell #-}

module CloTT.QuasiQuoter where

import qualified CloTT.Parser.Expr as P
import qualified CloTT.Parser.Decl as P
import qualified CloTT.Parser.Type as P
import qualified CloTT.Parser.Prog as P
import qualified CloTT.Parser.Lang as P

import CloTT.AST.Name
import CloTT.Interop
import CloTT.Utils (findMap)
import CloTT.Eval (progToEval)
import CloTT.Check.Prog (runCheckProg)
import CloTT.Annotated
import CloTT.Pretty (ppsw)

import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Language.Haskell.TH.Syntax
import Text.Parsec (parse)
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
          case progToEval (UName "main") prog of
            Right (expr, ty, rd, st) -> do
              let sing = typeToSingExp ty
              let exprQ = liftData expr
              let rdQ = liftData rd
              let stQ = liftData st
              [|CloTT $(rdQ) $(stQ) $(exprQ) $(sing)|]
            Left err -> fail err
