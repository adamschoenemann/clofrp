
module CloFRP.Utils where

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

findMap :: (a -> Maybe b) -> [a] -> Maybe b
findMap fn = foldr fun Nothing where
  fun x acc = 
    case fn x of
      Just x' -> Just x'
      Nothing -> acc

infix 1 |->
(|->) :: a -> b -> (a,b)
x |-> y = (x,y)