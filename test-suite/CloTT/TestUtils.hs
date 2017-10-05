
module CloTT.TestUtils where

import Test.Tasty.Hspec

success :: Expectation
success = pure ()

failure :: String -> Expectation
failure = expectationFailure
