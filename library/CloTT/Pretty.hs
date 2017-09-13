
module CloTT.Pretty where

import Data.Text.Prettyprint.Doc
import Data.Text.Prettyprint.Doc.Util
import Data.Text.Prettyprint.Doc.Render.Text
import Data.Text

ppln :: Pretty a => a -> IO ()
ppln = putDocW 80 . pretty 

pps :: Pretty a => a -> String
pps = show . pretty

ppsw :: Pretty a => Int -> a -> Text
ppsw w x = renderStrict (layoutPretty layoutOptions (unAnnotate (pretty x)))
  where
    layoutOptions = LayoutOptions { layoutPageWidth = AvailablePerLine w 1 }
