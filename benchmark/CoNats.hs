module CoNats (main) where

import CloFRP.Examples 
import CloFRP.Compiler

main :: [Int]
main = stream2lst nats 
  where
    stream2lst :: Stream k a -> [a]
    stream2lst (Fold (Cons x xs)) = x : stream2lst (xs ())

    -- strmap' :: (a -> b) -> Stream k a -> Stream k b
    -- strmap' f (Fold (Cons x xs)) = Fold (Cons (f x) (\_ -> strmap' f (xs ())))

    -- listmap :: (a -> b) -> List a -> List b
    -- listmap f (Fold l) = Fold $
    --   case l of
    --     Nil -> Nil
    --     LCons x xs -> LCons (f x) (listmap f xs)

    -- listnats :: List Integer
    -- listnats = fix (\g -> Fold (LCons 0 (listmap (+1) g)))

    -- listtake :: Integer -> List a -> [a]
    -- listtake _ (Fold Nil) = []
    -- listtake n (Fold (LCons x xs))
    --   | n <= 0    = []
    --   | otherwise = x : listtake (n-1) xs

    -- hasknats :: Stream k Integer
    -- hasknats = Fold (Cons 0 (\_ -> strmap' (+1) hasknats))
    -- -- hasknats = gfix (\g -> Fold (Cons 0 (\_ -> strmap' (+1) $ g ())))

    -- strtake :: Integer -> Stream k a -> [a]
    -- strtake n (Fold (Cons x xs))
    --   | n <= 0    = []
    --   | otherwise = x : strtake (n-1) (xs ())
