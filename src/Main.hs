module Main where

import SimdLlvm

fi :: Fractional a => a -> a
fi x = 2 * (-x) + (4 / x) ^ 3

f :: Floating a => a -> a
f t = sin (pi * t / 2) * (1 + sqrt t) ^ 2

main :: IO ()
main = do
  putStrLn "Hellow, simd haskell"
  printExpr ((f 3.0) :: Expr Double)
  printCodegen ((f 3.0) :: Expr Double)
  printExpr ((fi 5) :: Expr Int)
  printCodegen ((fi 5) :: Expr Int)
