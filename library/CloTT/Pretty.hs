
module CloTT.Pretty where

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Util
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text

ppln :: Pretty a => a -> IO ()
ppln = putDocW 80 . pretty 

pps :: Pretty a => a -> String
pps = show . pretty

ppsw :: Pretty a => Int -> a -> String
ppsw w x = showW w (pretty x)

showW :: Int -> Doc a -> String
showW w x = unpack $ renderStrict (layoutPretty layoutOptions (unAnnotate x))
  where
    layoutOptions = LayoutOptions { layoutPageWidth = AvailablePerLine w 1 }

