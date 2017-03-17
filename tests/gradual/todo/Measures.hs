-- | Sec 8 from Gradual Refinement Types 

module Measures where
{-@ LIQUID "--gradual" @-}

-- This does not work because I need the special locality treatment for measures
{-@ f :: x:{v:[a] | ?? } -> {v:Int | ?? } -> a -> Bool @-}
f :: Eq a => [a] -> Int -> a -> Bool  
f xs i y= xs!!i == y 

{-@ dotProd :: x:[Int] -> y:{[Int]| ??} -> Int @-}
dotProd :: [Int] -> [Int] -> Int
dotProd xs ys = go (length xs)
  where
  	{-@ go :: Nat -> Int @-}
  	go i | i < 0 = 0 
  	go i = xs!!i * ys!!i + go (i-1)

{-@ assume (!!) :: xs:[a] -> {v:Int | 0 <= v && v < len xs } -> a  @-}

