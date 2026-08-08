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

import Prelude hiding (Char, Int, Num)
import qualified Prelude
import System.Exit (exitFailure)
import Voblint_Analyse

-- `HOL-Library.Code_Target_Numeral` (imported by Example_Analysis_Dispatch)
-- backs Isabelle's `int`/`nat` by the target language's native
-- arbitrary-precision integer, so construction/inspection go through
-- `Int_of_integer`/`nat_of_integer` and their inverses rather than walking a
-- `Num`/Peano-successor term.
mkInt :: Integer -> Int
mkInt = Int_of_integer

mkNat :: Integer -> Nat
mkNat = nat_of_integer

-- `vname = char list` uses Isabelle's own `Char` (opaque under
-- Code_Abstract_Char, imported by Example_Analysis_Dispatch), bridged to a
-- native integer by `char_of_integer`/`integer_of_char`.
mkChar :: Prelude.Char -> Char
mkChar = char_of_integer . toInteger . fromEnum

mkString :: Prelude.String -> [Char]
mkString = map mkChar

unChar :: Char -> Prelude.Char
unChar = toEnum . fromInteger . integer_of_char

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
  show n = show (integer_of_nat n)

instance Show Int where
  show i = show (integer_of_int i)

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
