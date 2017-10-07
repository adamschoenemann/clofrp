{-# LANGUAGE TemplateHaskell #-}

module CloTT.QuasiQuoter where

import qualified CloTT.Parser.Expr as P
import qualified CloTT.Parser.Decl as P
import qualified CloTT.Parser.Type as P
import qualified CloTT.Parser.Prog as P
import qualified CloTT.Parser.Lang as P

import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Language.Haskell.TH.Syntax
import Text.Parsec (parse)
import Text.Parsec.Combinator (eof)
import Text.Parsec.String (Parser)


liftParse :: Monad m => Parser p -> String -> m p
liftParse p s = either (fail . show) pure $ parse (P.ws *> p <* eof) "quasi" s

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
