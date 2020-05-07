{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE TypeInType #-}
{-# LANGUAGE TypeSynonymInstances #-}

module SimdLlvm where

import Control.DeepSeq (NFData, force)
import Control.Exception
import Control.Monad
import Control.Monad.IO.Class
import GHC.TypeLits
import Data.Kind
import Data.Proxy
import Data.Int
import Data.Word
import Data.ByteString (ByteString)
import qualified Data.ByteString.Char8 as BS
import Data.Foldable
import Data.Functor.Foldable hiding (fold)
import Data.IORef
import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import Data.Monoid
import qualified Data.Set as Set
import Data.Text.Lazy (Text)
import qualified Data.Text.Lazy.IO as Text
import Foreign.Ptr
import qualified LLVM.AST as LLVM
import qualified LLVM.AST.Constant as LLVM
import qualified LLVM.AST.Float as LLVM
import qualified LLVM.AST.Type as LLVM
import qualified LLVM.CodeGenOpt as CodeGenOpt
import qualified LLVM.CodeModel as CodeModel
import qualified LLVM.Context as JIT
import qualified LLVM.IRBuilder.Instruction as LLVMIR
import qualified LLVM.IRBuilder.Module as LLVMIR
import qualified LLVM.IRBuilder.Monad as LLVMIR
import qualified LLVM.Internal.OrcJIT.CompileLayer as JIT
import qualified LLVM.Linking as JIT
import qualified LLVM.Module as JIT
import qualified LLVM.OrcJIT as JIT
import qualified LLVM.Pretty as LLVMPretty
import qualified LLVM.Relocation as Reloc
import qualified LLVM.Target as JIT

import FixedVector as V

-- * Core expression type

-- | An expression will be any value of type @'Fix' 'ExprF'@, which
--   has as values arbitrarily nested applications of constructors from
--   'ExprF'. This is equivalent to just having an 'Expr type with no type
--   parameter and all @a@s replaced by 'Expr', but the 'Functor' and 'Foldable'
--   instances are quite handy, especially combined with the /recursion-schemes/
--   library.
--
--   This type allows us to express the body of a @Double -> Double@ function,
--   where 'Var' allows us to refer to the (only) argument of the function.
data ExprF a e
  = -- | a 'Int' literal
    LitI Int
  | -- | @a+b@
    AddI e e
  | -- | @a-b@
    SubI e e
  | -- | @a*b@
    MulI e e
  | -- | @a/b@
    DivI e e
  | -- | @-a@
    NegI e
  | -- | @'x'@
    VarI
  | -- | a 'Int32x4' literal
    LitVI Int32x4
  | -- | @a+b@
    AddVI e e
  | -- | @a-b@
    SubVI e e
  | -- | @a*b@
    MulVI e e
  | -- | @a/b@
    DivVI e e
  | -- | @-a@
    NegVI e
  | -- | @'x'@
    VarVI
  | -- | a 'Double' literal
    LitF Double
  | -- | @a+b@
    AddF e e
  | -- | @a-b@
    SubF e e
  | -- | @a*b@
    MulF e e
  | -- | @a/b@
    DivF e e
  | -- | @-a@
    NegF e
  | -- | @'exp' a@
    Exp e
  | -- | @'log' a@
    Log e
  | -- | @'sqrt' a@
    Sqrt e
  | -- | @'sin' a@
    Sin e
  | -- | @'cos' a@
    Cos e
  | -- | @'x'@
    VarF
  deriving (Functor, Foldable, Traversable)

type Expr a = Fix (ExprF a)

-- * Helpers for building expressions

x :: Expr a
x = Fix VarF

zx :: Expr a
zx = Fix VarI

vx :: Expr a
vx = Fix VarVI

liti :: Int -> Expr Int
liti i = Fix (LitI i)

addi :: Expr a -> Expr a -> Expr a
addi a b = Fix (AddI a b)

subi :: Expr a -> Expr a -> Expr a
subi a b = Fix (SubI a b)

muli :: Expr a -> Expr a -> Expr a
muli a b = Fix (MulI a b)

divi :: Expr a -> Expr a -> Expr a
divi a b = Fix (DivI a b)

negi :: Expr a -> Expr a
negi a = Fix (NegI a)

litvi :: Int32x4 -> Expr Int32x4
litvi i = Fix (LitVI i)

cvec :: [Int32] -> Expr Int32x4
cvec = litvi . fromList

addvi :: Expr a -> Expr a -> Expr a
addvi a b = Fix (AddVI a b)

subvi :: Expr a -> Expr a -> Expr a
subvi a b = Fix (SubVI a b)

mulvi :: Expr a -> Expr a -> Expr a
mulvi a b = Fix (MulVI a b)

divvi :: Expr a -> Expr a -> Expr a
divvi a b = Fix (DivVI a b)

negvi :: Expr a -> Expr a
negvi a = Fix (NegVI a)

litf :: Double -> Expr Double
litf d = Fix (LitF d)

addf :: Expr a -> Expr a -> Expr a
addf a b = Fix (AddF a b)

subf :: Expr a -> Expr a -> Expr a
subf a b = Fix (SubF a b)

mulf :: Expr a -> Expr a -> Expr a
mulf a b = Fix (MulF a b)

divf :: Expr a -> Expr a -> Expr a
divf a b = Fix (DivF a b)

negf :: Expr a -> Expr a
negf a = Fix (NegF a)

instance Num (Expr Int) where
  fromInteger = liti . fromInteger
  (+) = addi
  (-) = subi
  (*) = muli
  negate = negi
  abs = notImplemented "Expr.abs"
  signum = notImplemented "Expr.signum"

instance Fractional (Expr Int) where
  (/) = divi
  recip = notImplemented "Expr.recip"
  fromRational = notImplemented "Expr.intRatioinal"

type Int16x4 = Vec 4 Int16
type Int32x4 = Vec 4 Int32

instance Num (Expr Int32x4) where
  fromInteger = litvi . replicateVec . fromInteger
  (+) = addvi
  (-) = subvi
  (*) = mulvi
  negate = negvi
  abs = notImplemented "Expr.abs"
  signum = notImplemented "Expr.signum"

instance Fractional (Expr Int32x4) where
  (/) = divvi
  recip = notImplemented "Expr.recip"
  fromRational = notImplemented "Expr.intRatioinal"

instance Num (Expr Double) where
  fromInteger = litf . fromInteger
  (+) = addf
  (-) = subf
  (*) = mulf
  negate = negf
  abs = notImplemented "Expr.abs"
  signum = notImplemented "Expr.signum"

instance Fractional (Expr Double) where
  (/) = divf
  recip = divf 1
  fromRational = litf . fromRational

instance Floating (Expr Double) where
  pi = litf pi
  exp = Fix . Exp
  log = Fix . Log
  sqrt = Fix . Sqrt
  sin = Fix . Sin
  cos = Fix . Cos
  asin = notImplemented "Expr.asin"
  acos = notImplemented "Expr.acos"
  atan = notImplemented "Expr.atan"
  sinh = notImplemented "Expr.sinh"
  cosh = notImplemented "Expr.cosh"
  asinh = notImplemented "Expr.asinh"
  acosh = notImplemented "Expr.acosh"
  atanh = notImplemented "Expr.atanh"

notImplemented :: String -> a
notImplemented = error . (++ " is not implemented")

-- * Pretty printing

-- | Pretty print an 'Expr'
pp :: Expr a -> String
pp e = funprefix ++ para ppExpAlg e
  where
    funprefix = "\\x -> "

printExpr :: MonadIO m => Expr a -> m ()
printExpr expr = liftIO $ do
  putStrLn "*** Expression ***\n"
  putStrLn (pp expr)

-- | Core pretty printing function. For each
--   constructor that contains sub expressions,
--   we get the string for the sub expression as
--   well as the original 'Expr' value, to help us
--   decide when to use parens.
ppExpAlg :: ExprF a (Expr a, String) -> String
ppExpAlg (LitI i) = show i
ppExpAlg (AddI (_, a) (_, b)) = a ++ " + " ++ b
ppExpAlg (SubI (_, a) (e2, b)) =
  a ++ " - " ++ paren (isAdd e2 || isSub e2) b
ppExpAlg (MulI (e1, a) (e2, b)) =
  paren (isAdd e1 || isSub e1) a ++ " * " ++ paren (isAdd e2 || isSub e2) b
ppExpAlg (DivI (e1, a) (e2, b)) =
  paren (isAdd e1 || isSub e1) a ++ " / " ++ paren (isComplex e2) b
ppExpAlg (NegI (_, a)) = paren True ("-" ++ a)
ppExpAlg (LitVI i32) = show i32
ppExpAlg (AddVI (_, a) (_, b)) = a ++ " + " ++ b
ppExpAlg (SubVI (_, a) (e2, b)) =
  a ++ " - " ++ paren (isAdd e2 || isSub e2) b
ppExpAlg (MulVI (e1, a) (e2, b)) =
  paren (isAdd e1 || isSub e1) a ++ " * " ++ paren (isAdd e2 || isSub e2) b
ppExpAlg (DivVI (e1, a) (e2, b)) =
  paren (isAdd e1 || isSub e1) a ++ " / " ++ paren (isComplex e2) b
ppExpAlg (NegVI (_, a)) = paren True ("-" ++ a)
ppExpAlg (LitF d) = show d
ppExpAlg (AddF (_, a) (_, b)) = a ++ " + " ++ b
ppExpAlg (SubF (_, a) (e2, b)) =
  a ++ " - " ++ paren (isAdd e2 || isSub e2) b
ppExpAlg (MulF (e1, a) (e2, b)) =
  paren (isAdd e1 || isSub e1) a ++ " * " ++ paren (isAdd e2 || isSub e2) b
ppExpAlg (DivF (e1, a) (e2, b)) =
  paren (isAdd e1 || isSub e1) a ++ " / " ++ paren (isComplex e2) b
ppExpAlg (NegF (_, a)) = function "negate" a
ppExpAlg (Exp (_, a)) = function "exp" a
ppExpAlg (Log (_, a)) = function "log" a
ppExpAlg (Sqrt (_, a)) = function "sqrt" a
ppExpAlg (Sin (_, a)) = function "sin" a
ppExpAlg (Cos (_, a)) = function "cos" a
ppExpAlg VarF = "x"
ppExpAlg VarI = "zx"
ppExpAlg VarVI = "vx"

paren :: Bool -> String -> String
paren b x
  | b = "(" ++ x ++ ")"
  | otherwise = x

function name arg =
  name ++ paren True arg

isAdd :: Expr a -> Bool
isAdd (Fix (AddI _ _)) = True
isAdd (Fix (AddVI _ _)) = True
isAdd (Fix (AddF _ _)) = True
isAdd _ = False

isSub :: Expr a -> Bool
isSub (Fix (SubI _ _)) = True
isSub (Fix (SubVI _ _)) = True
isSub (Fix (SubF _ _)) = True
isSub _ = False

isLit :: Expr a -> Bool
isLit (Fix (LitI _)) = True
isLit (Fix (LitVI _)) = True
isLit (Fix (LitF _)) = True
isLit _ = False

isVar :: Expr a -> Bool
isVar (Fix VarI) = True
isVar (Fix VarVI) = True
isVar (Fix VarF) = True
isVar _ = False

isComplex :: Expr a -> Bool
isComplex (Fix (AddI _ _)) = True
isComplex (Fix (SubI _ _)) = True
isComplex (Fix (MulI _ _)) = True
isComplex (Fix (DivI _ _)) = True
isComplex (Fix (AddVI _ _)) = True
isComplex (Fix (SubVI _ _)) = True
isComplex (Fix (MulVI _ _)) = True
isComplex (Fix (DivVI _ _)) = True
isComplex (Fix (AddF _ _)) = True
isComplex (Fix (SubF _ _)) = True
isComplex (Fix (MulF _ _)) = True
isComplex (Fix (DivF _ _)) = True
isComplex _ = False

-- * Simple evaluator

-- | Evaluate an 'Expr'ession using standard
--   'Num', 'Fractional' and 'Floating' operations.
eval :: Expr a -> (Double -> Double)
eval fexpr x = cata alg fexpr
  where
    alg e = case e of
      VarF -> x
      LitF d -> d
      AddF a b -> a + b
      SubF a b -> a - b
      MulF a b -> a * b
      DivF a b -> a / b
      NegF a -> negate a
      Exp a -> exp a
      Log a -> log a
      Sqrt a -> sqrt a
      Sin a -> sin a
      Cos a -> cos a

-- | Monadic catamorphism.
{-
cataM :: (Applicative m, Monad m, Traversable t)
    => (t a -> m a) -> Fix t -> m a
cataM f = (f =<<) . traverse (cataM f) . unfix
-}

cataM ::
  (Monad m, Traversable (Base t), Recursive t) =>
  (Base t a -> m a) ->
  t ->
  m a
cataM alg = c
  where
    c = alg <=< traverse c . project

-- * Code generation

-- | Helper for calling intrinsics for 'exp', 'log' and friends.
callDblfun ::
  LLVMIR.MonadIRBuilder m => LLVM.Operand -> LLVM.Operand -> m LLVM.Operand
callDblfun fun arg = LLVMIR.call fun [(arg, [])]

xparam :: LLVMIR.ParameterName
xparam = LLVMIR.ParameterName "x"

-- | Generate @declare@ statements for all the intrinsics required for
--   executing the given expression and return a mapping from function
--   name to 'Operand' so that we can very easily refer to those functions
--   for calling them, when generating the code for the expression itself.
declarePrimitives ::
  LLVMIR.MonadModuleBuilder m => Expr a -> m (Map String LLVM.Operand)
declarePrimitives expr = fmap Map.fromList
  $ forM primitives
  $ \primName -> do
    f <-
      LLVMIR.extern
        (LLVM.mkName ("llvm." <> primName <> ".f64"))
        [LLVM.double]
        LLVM.double
    return (primName, f)
  where
    primitives = Set.toList (cata alg expr)
    alg (Exp  ps) = Set.insert "exp"  ps
    alg (Log  ps) = Set.insert "log"  ps
    alg (Sqrt ps) = Set.insert "sqrt" ps
    alg (Sin  ps) = Set.insert "sin"  ps
    alg (Cos  ps) = Set.insert "cos"  ps
    alg e = fold e

-- | Generate an LLVM IR module for the given expression,
--   including @declare@ statements for the intrinsics and
--   a function, always called @f@, that will perform the copoutations
--   described by the 'Expr'ession.
codegen :: Expr a -> LLVM.Module
codegen fexpr = LLVMIR.buildModule "arith.ll" $ do
  prims <- declarePrimitives fexpr
  -- _ <- LLVMIR.function "f" [(LLVM.double, xparam)] LLVM.double $ \[arg] -> do
  _ <- LLVMIR.function "fv" [(LLVM.VectorType 4 LLVM.i32, xparam)] (LLVM.VectorType 4 LLVM.i32) $ \[arg] -> do
    res <- cataM (alg arg prims) fexpr
    LLVMIR.ret res
  return ()
  where
    alg arg _ (LitI i) =
      return (LLVM.ConstantOperand $ LLVM.Int 32 (toInteger i))
    alg arg _ (LitVI i32) =
      return (LLVM.ConstantOperand $ LLVM.Vector (fmap (LLVM.Int 32 . toInteger) $ V.toList i32))
    alg arg _ VarI = return arg
    alg arg _ VarVI = return arg
    alg arg _ (AddI a b) = LLVMIR.add a b `LLVMIR.named` "x"
    alg arg _ (SubI a b) = LLVMIR.sub a b `LLVMIR.named` "x"
    alg arg _ (MulI a b) = LLVMIR.mul a b `LLVMIR.named` "x"
    alg arg _ (DivI a b) = LLVMIR.sdiv a b `LLVMIR.named` "x"
    alg arg _ (AddVI a b) = LLVMIR.add a b `LLVMIR.named` "x"
    alg arg _ (SubVI a b) = LLVMIR.sub a b `LLVMIR.named` "x"
    alg arg _ (MulVI a b) = LLVMIR.mul a b `LLVMIR.named` "x"
    alg arg _ (DivVI a b) = LLVMIR.sdiv a b `LLVMIR.named` "x"
    alg arg ps (NegI a) = do
      z <- alg arg ps (LitI 0)
      LLVMIR.sub z a `LLVMIR.named` "x"
    alg arg ps (NegVI a) = do
      z <- alg arg ps (LitVI (replicateVec 0))
      LLVMIR.sub z a `LLVMIR.named` "x"
    alg arg _ (LitF d) =
      return (LLVM.ConstantOperand $ LLVM.Float $ LLVM.Double d)
    alg arg _ VarF = return arg
    alg arg _ (AddF a b) = LLVMIR.fadd a b `LLVMIR.named` "x"
    alg arg _ (SubF a b) = LLVMIR.fsub a b `LLVMIR.named` "x"
    alg arg _ (MulF a b) = LLVMIR.fmul a b `LLVMIR.named` "x"
    alg arg _ (DivF a b) = LLVMIR.fdiv a b `LLVMIR.named` "x"
    alg arg ps (NegF a) = do
      z <- alg arg ps (LitF 0)
      LLVMIR.fsub z a `LLVMIR.named` "x"
    alg arg ps (Exp a) = callDblfun (ps Map.! "exp") a `LLVMIR.named` "x"
    alg arg ps (Log a) = callDblfun (ps Map.! "log") a `LLVMIR.named` "x"
    alg arg ps (Sqrt a) = callDblfun (ps Map.! "sqrt") a `LLVMIR.named` "x"
    alg arg ps (Sin a) = callDblfun (ps Map.! "sin") a `LLVMIR.named` "x"
    alg arg ps (Cos a) = callDblfun (ps Map.! "cos") a `LLVMIR.named` "x"

codegenText :: Expr a -> Text
codegenText = LLVMPretty.ppllvm . codegen

printCodegen :: Expr a -> IO ()
printCodegen = Text.putStrLn . codegenText

