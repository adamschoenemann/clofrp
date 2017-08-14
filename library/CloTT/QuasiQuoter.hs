{-# LANGUAGE TemplateHaskell #-}

module CloTT.QuasiQuoter where

import qualified CloTT.Parser.Expr as P
import qualified CloTT.Parser.Type as P

import Language.Haskell.TH.Quote (QuasiQuoter(..))
import Language.Haskell.TH.Syntax
import Text.Parsec (parse, spaces)
import Text.Parsec.String (Parser)


liftParse :: Monad m => Parser p -> String -> m p
liftParse p s = either (fail . show) return $ parse (spaces >> p) "quasi" s

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
