
module CloTT.Utils where

-- total definition of last
safeLast :: a -> [a] -> a
safeLast d [] = d
safeLast d [x] = x
safeLast d (x:xs) = safeLast d xs

-- total def of init
safeInit :: [a] -> [a]
safeInit [] = []
safeInit [x] = []
safeInit (x:xs) = x : safeInit xs

safeHead :: a -> [a] -> a
safeHead d [] = d
safeHead d (x:xs) = x
