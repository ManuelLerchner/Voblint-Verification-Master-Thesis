-- Regression driver for the generated Voblint_Analyse Haskell module.
-- Constructs a VIMP program purely through the exported AST constructors
-- (never touching Isabelle), runs it through the exported `analyse`
-- dispatcher for both domains, and checks the result against the values
-- already proved inside Isabelle by
-- src/Examples/Mixed/Example_Analysis_Dispatch.thy's
-- dispatch_demo_sign_unknown / dispatch_demo_interval_precise lemmas.
--
-- Do not hand-edit codegen/generated/Voblint_Analyse.hs; regenerate it with
-- `make codegen` instead.
module Main (main) where

import Data.Bits (testBit)
import Prelude hiding (Char, Int, Num)
import qualified Prelude
import System.Exit (exitFailure)
import Voblint_Analyse

-- Isabelle's `Num`/`Int`/`Nat` are unbounded unary/binary encodings with no
-- `fromInteger` bridge in the generated code, so small literals are built by
-- hand here rather than exported from Isabelle (which already exports
-- `int_zero`/`nat_zero` as the base cases, since `Zero_int`/`Zero_nat` are
-- code-level artifacts of the numeral `code_datatype` setup, not directly
-- citable Isabelle constants).
mkNum :: Integer -> Num
mkNum 1 = One
mkNum n
  | even n = Bit0 (mkNum (n `div` 2))
  | otherwise = Bit1 (mkNum (n `div` 2))

mkInt :: Integer -> Int
mkInt 0 = int_zero
mkInt n
  | n > 0 = Pos (mkNum n)
  | otherwise = Neg (mkNum (negate n))

mkNat :: Integer -> Nat
mkNat 0 = nat_zero
mkNat n = Suc (mkNat (n - 1))

-- `vname = char list` uses Isabelle's own bit-vector `Char`, not Prelude's,
-- with bit 0 (`Char b0 ...`) as the least-significant bit -- confirmed by
-- decoding the generated `ret_var` constant (`Char True True False False
-- False True False False, ...`) to "#ret".
mkChar :: Prelude.Char -> Char
mkChar c = Char (bit 0) (bit 1) (bit 2) (bit 3) (bit 4) (bit 5) (bit 6) (bit 7)
  where
    n = fromEnum c
    bit i = testBit n i

mkString :: Prelude.String -> [Char]
mkString = map mkChar

unChar :: Char -> Prelude.Char
unChar (Char b0 b1 b2 b3 b4 b5 b6 b7) =
  toEnum (sum [2 ^ i | (i, b) <- zip [0 :: Prelude.Int ..] [b0, b1, b2, b3, b4, b5, b6, b7], b])

unString :: [Char] -> Prelude.String
unString = map unChar

-- y := 1; check(0 < y); y := 0 - 1; check(0 < y)
-- Same program as dispatch_demo_prog in Example_Analysis_Dispatch.thy.
demoProg :: Imp_prog_ext ()
demoProg =
  make
    []
    ( Seq
        ( Seq
            (Seq (Assign (mkString "y") (N (mkInt 1))) (Check checkCond))
            (Assign (mkString "y") (Minus (N (mkInt 0)) (N (mkInt 1))))
        )
        (Check checkCond)
    )
    []
  where
    checkCond = Less (N (mkInt 0)) (V (mkString "y"))

expectedSign :: [(Cfg_node, (Bexp, Check_result))]
expectedSign =
  [ (Statement (mkNat 1), (Less (N (mkInt 0)) (V (mkString "y")), Check_Unknown)),
    (Statement (mkNat 3), (Less (N (mkInt 0)) (V (mkString "y")), Check_Unknown))
  ]

expectedInterval :: [(Cfg_node, (Bexp, Check_result))]
expectedInterval =
  [ (Statement (mkNat 1), (Less (N (mkInt 0)) (V (mkString "y")), Check_Proved)),
    (Statement (mkNat 3), (Less (N (mkInt 0)) (V (mkString "y")), Check_Refuted))
  ]

checkCase :: (Eq a, Show a) => Prelude.String -> a -> a -> IO Prelude.Bool
checkCase label actual expected
  | actual == expected = do
      putStrLn ("OK   " ++ label)
      return Prelude.True
  | otherwise = do
      putStrLn ("FAIL " ++ label)
      putStrLn ("  expected: " ++ show expected)
      putStrLn ("  actual:   " ++ show actual)
      return Prelude.False

instance Show Nat where
  show n = show (toIntegerNat n)
    where
      toIntegerNat Zero_nat = 0 :: Integer
      toIntegerNat (Suc m) = 1 + toIntegerNat m

instance Show Cfg_node where
  show (Statement n) = "Statement " ++ show n
  show (FunctionEntry s) = "FunctionEntry " ++ unString s
  show (FunctionResult s) = "FunctionResult " ++ unString s

instance Show Check_result where
  show Check_Proved = "Check_Proved"
  show Check_Refuted = "Check_Refuted"
  show Check_Unknown = "Check_Unknown"

-- Generated code omits `instance Eq Check_result`/`instance Eq Bexp`, since
-- nothing in the exported closure itself compares them; the driver needs
-- both to compare `analyse`'s output against the expected report.
instance Eq Check_result where
  Check_Proved == Check_Proved = Prelude.True
  Check_Refuted == Check_Refuted = Prelude.True
  Check_Unknown == Check_Unknown = Prelude.True
  _ == _ = Prelude.False

instance Eq Bexp where
  Bc a == Bc b = a Prelude.== b
  Not a == Not b = a == b
  And a1 a2 == And b1 b2 = a1 == b1 Prelude.&& a2 == b2
  Or a1 a2 == Or b1 b2 = a1 == b1 Prelude.&& a2 == b2
  Less a1 a2 == Less b1 b2 = a1 Prelude.== b1 Prelude.&& a2 Prelude.== b2
  Eqb a1 a2 == Eqb b1 b2 = a1 Prelude.== b1 Prelude.&& a2 Prelude.== b2
  _ == _ = Prelude.False

instance Show Num where
  show n = show (toIntegerNum n)
    where
      toIntegerNum One = 1 :: Integer
      toIntegerNum (Bit0 m) = 2 * toIntegerNum m
      toIntegerNum (Bit1 m) = 2 * toIntegerNum m + 1

instance Show Int where
  show Zero_int = "0"
  show (Pos n) = show n
  show (Neg n) = "-" ++ show n

instance Show Aexp where
  show (N i) = show i
  show (V s) = unString s
  show (Plus a b) = "(" ++ show a ++ " + " ++ show b ++ ")"
  show (Minus a b) = "(" ++ show a ++ " - " ++ show b ++ ")"
  show (Times a b) = "(" ++ show a ++ " * " ++ show b ++ ")"

instance Show Bexp where
  show (Bc b) = show b
  show (Not b) = "!" ++ show b
  show (And a b) = "(" ++ show a ++ " && " ++ show b ++ ")"
  show (Or a b) = "(" ++ show a ++ " || " ++ show b ++ ")"
  show (Less a b) = "(" ++ show a ++ " < " ++ show b ++ ")"
  show (Eqb a b) = "(" ++ show a ++ " == " ++ show b ++ ")"

main :: IO ()
main = do
  let actualSign = analyse Sign_Analysis demoProg
      actualInterval = analyse Interval_Analysis demoProg
  okSign <- checkCase "Sign_Analysis demo report" actualSign expectedSign
  okInterval <- checkCase "Interval_Analysis demo report" actualInterval expectedInterval
  if okSign && okInterval
    then putStrLn "All regression checks passed."
    else exitFailure
