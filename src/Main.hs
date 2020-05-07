module Main where

import SimdLlvm

fi :: Fractional a => a -> a
fi t = 2 * (-t) + (4 / t) ^ 3

fv :: Expr Int32x4 -> Expr Int32x4
fv t = 3 * (-t) + (4 / t) * t ^ 3

f :: Floating a => a -> a
f t = sin (pi * t / 2) * (1 + sqrt t) ^ 2

main :: IO ()
main = do
  putStrLn "Hellow, simd haskell"
  printExpr ((f x) :: Expr Double)
  printCodegen ((f x) :: Expr Double)
  printExpr ((fi zx) :: Expr Int)
  printCodegen ((fi zx) :: Expr Int)
  printExpr ((fv vx) :: Expr Int32x4)
  printCodegen ((fv vx) :: Expr Int32x4)
