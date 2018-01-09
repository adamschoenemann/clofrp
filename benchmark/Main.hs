
module Main where

import qualified ReplaceMin as RepMin
import qualified EveryOther as EO
import qualified CoNats
import qualified BenchEval
import qualified ScaryConst 

main :: IO ()
main = do
  -- putStrLn . show $ RepMin.main
  -- putStrLn . show . take 1000000 $ EO.trans [0..]
  -- putStrLn . show . take 1000000 $ EO.exec
  -- BenchEval.bench_everyOtherExec
  -- putStrLn . show . take 1000000 $ CoNats.main
  putStrLn . show . map (take 2500000) . take 3 $ ScaryConst.main