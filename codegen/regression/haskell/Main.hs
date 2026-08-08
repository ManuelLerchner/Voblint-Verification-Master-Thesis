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

import Prelude hiding (Int, Num)
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

-- `vname`/`pname` are Isabelle's `String.literal`, which is already the
-- target language's native `String` (see Example_Analysis_Dispatch.thy), so
-- variable/procedure names need no conversion at all.

-- y := 1; check(0 < y); y := 0 - 1; check(0 < y)
-- Same program as dispatch_demo_prog in Example_Analysis_Dispatch.thy.
demoProg :: Imp_prog_ext ()
demoProg =
  make
    []
    ( Seq
        ( Seq
            (Seq (Assign "y" (N (mkInt 1))) (Check checkCond))
            (Assign "y" (Minus (N (mkInt 0)) (N (mkInt 1))))
        )
        (Check checkCond)
    )
    []
  where
    checkCond = Less (N (mkInt 0)) (V "y")

expectedSign :: [(Cfg_node, (Bexp, Check_result))]
expectedSign =
  [ (Statement (mkNat 1), (Less (N (mkInt 0)) (V "y"), Check_Unknown)),
    (Statement (mkNat 3), (Less (N (mkInt 0)) (V "y"), Check_Unknown))
  ]

expectedInterval :: [(Cfg_node, (Bexp, Check_result))]
expectedInterval =
  [ (Statement (mkNat 1), (Less (N (mkInt 0)) (V "y"), Check_Proved)),
    (Statement (mkNat 3), (Less (N (mkInt 0)) (V "y"), Check_Refuted))
  ]

-- global `total`, procedure `inc` with formal `n`, two calls, two checks.
-- Exercises `make`'s procedure list, `proc_decl_of`'s formals, and `Call`
-- together -- not just straight-line assignment/check.
-- Same program as proc_demo_prog in Example_Analysis_Dispatch.thy; checked
-- against proc_demo_sign_unknown / proc_demo_cfg_intra / proc_demo_cfg_calls.
-- (Interval is not exercised here: analyse Interval_Analysis on this
-- procedure/call program does not terminate -- a pre-existing bug in
-- Interval's call handling, unrelated to this driver's String-based
-- construction, tracked separately in Example_Analysis_Dispatch.thy.)
procDemoProg :: Imp_prog_ext ()
procDemoProg =
  make
    [("inc", proc_decl_of ["n"] (Assign "total" (Plus (V "total") (V "n"))))]
    ( Seq
        ( Seq
            ( Seq
                (Seq (Assign "total" (N (mkInt 0))) (Call Nothing "inc" [N (mkInt 3)]))
                (Call Nothing "inc" [N (mkInt 4)])
            )
            (Check (Less (N (mkInt 0)) (V "total")))
        )
        (Check (Less (V "total") (N (mkInt 100))))
    )
    ["total"]

expectedProcDemoSign :: [(Cfg_node, (Bexp, Check_result))]
expectedProcDemoSign =
  [ (Statement (mkNat 5), (Less (N (mkInt 0)) (V "total"), Check_Unknown)),
    (Statement (mkNat 6), (Less (V "total") (N (mkInt 100)), Check_Unknown))
  ]

-- Compact renderers matching string_of_cfg_node/string_of_action/
-- string_of_call_action in Analysis_GraphViz.thy exactly (no spaces around
-- infix operators, "pp"/"entry_"/"result_" node prefixes) -- deliberately
-- not the driver's own verbose `Show` instances above, which render
-- constructor names for the straight-line demo's own display purposes.
joinWith :: Prelude.String -> [Prelude.String] -> Prelude.String
joinWith _ [] = ""
joinWith _ [s] = s
joinWith sep (s : ss) = s ++ sep ++ joinWith sep ss

showCfgNodeCompact :: Cfg_node -> Prelude.String
showCfgNodeCompact (Statement n) = "pp" ++ show n
showCfgNodeCompact (FunctionEntry s) = "entry_" ++ s
showCfgNodeCompact (FunctionResult s) = "result_" ++ s

showAexpCompact :: Aexp -> Prelude.String
showAexpCompact (N i) = show i
showAexpCompact (V s) = s
showAexpCompact (Plus a b) = "(" ++ showAexpCompact a ++ "+" ++ showAexpCompact b ++ ")"
showAexpCompact (Minus a b) = "(" ++ showAexpCompact a ++ "-" ++ showAexpCompact b ++ ")"
showAexpCompact (Times a b) = "(" ++ showAexpCompact a ++ "*" ++ showAexpCompact b ++ ")"

showBexpCompact :: Bexp -> Prelude.String
showBexpCompact (Bc b) = show b
showBexpCompact (Not b) = "!(" ++ showBexpCompact b ++ ")"
showBexpCompact (And a b) = "(" ++ showBexpCompact a ++ "&&" ++ showBexpCompact b ++ ")"
showBexpCompact (Or a b) = "(" ++ showBexpCompact a ++ "||" ++ showBexpCompact b ++ ")"
showBexpCompact (Less a b) = showAexpCompact a ++ "<" ++ showAexpCompact b
showBexpCompact (Eqb a b) = showAexpCompact a ++ "==" ++ showAexpCompact b

showEdgeAction :: Edge_action -> Prelude.String
showEdgeAction EA_Nop = "nop"
showEdgeAction (EA_Assign x a) = x ++ " := " ++ showAexpCompact a
showEdgeAction (EA_Random x) = x ++ " := random()"
showEdgeAction (EA_Assume b) = "[" ++ showBexpCompact b ++ "]"
showEdgeAction (EA_AssumeNot b) = "![" ++ showBexpCompact b ++ "]"
showEdgeAction (EA_Ret Prelude.Nothing _) = "return"
showEdgeAction (EA_Ret (Prelude.Just e) _) = "return " ++ showAexpCompact e
showEdgeAction (EA_Check b) = "check(" ++ showBexpCompact b ++ ")"

showCallAction :: Call_action -> Prelude.String
showCallAction (CallEdge Prelude.Nothing _ es) = "call(" ++ concatMap showAexpCompact es ++ ")"
showCallAction (CallEdge (Prelude.Just x) _ es) = x ++ " := call(" ++ concatMap showAexpCompact es ++ ")"

showIntraList :: [(Cfg_node, (Edge_action, Cfg_node))] -> Prelude.String
showIntraList es =
  joinWith
    "; "
    [ showCfgNodeCompact u ++ " --[" ++ showEdgeAction a ++ "]--> " ++ showCfgNodeCompact v
      | (u, (a, v)) <- es
    ]

showCallsList :: [(Cfg_node, (Call_action, (Cfg_node, Cfg_node)))] -> Prelude.String
showCallsList es =
  joinWith
    "; "
    [ showCfgNodeCompact call ++ " --[" ++ showCallAction ca ++ "]--> " ++ showCfgNodeCompact entry
        ++ " ~cont~> "
        ++ showCfgNodeCompact cont
      | (call, (ca, (entry, cont))) <- es
    ]

expectedProcDemoIntra :: Prelude.String
expectedProcDemoIntra =
  "pp0 --[total := (total+n)]--> pp1; pp1 --[return]--> result_inc; "
    ++ "pp2 --[total := 0]--> pp3; pp5 --[check(0<total)]--> pp6; "
    ++ "pp6 --[check(total<100)]--> pp7; pp7 --[return]--> result_main; "
    ++ "entry_inc --[nop]--> pp0; entry_main --[nop]--> pp2"

expectedProcDemoCalls :: Prelude.String
expectedProcDemoCalls =
  "pp3 --[call(3)]--> entry_inc ~cont~> pp4; pp4 --[call(4)]--> entry_inc ~cont~> pp5"

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
  show (FunctionEntry s) = "FunctionEntry " ++ s
  show (FunctionResult s) = "FunctionResult " ++ s

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
  show (V s) = s
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
      actualProcDemoSign = analyse Sign_Analysis procDemoProg
      procDemoCfg = prog_cfg prog_main_name procDemoProg
      actualProcDemoIntra = showIntraList (cfg_intra_list procDemoCfg)
      actualProcDemoCalls = showCallsList (cfg_calls_list procDemoCfg)
  okSign <- checkCase "Sign_Analysis demo report" actualSign expectedSign
  okInterval <- checkCase "Interval_Analysis demo report" actualInterval expectedInterval
  okProcDemoSign <- checkCase "Sign_Analysis proc_demo report" actualProcDemoSign expectedProcDemoSign
  okProcDemoIntra <- checkCase "proc_demo CFG intra edges" actualProcDemoIntra expectedProcDemoIntra
  okProcDemoCalls <- checkCase "proc_demo CFG calls edges" actualProcDemoCalls expectedProcDemoCalls
  if okSign && okInterval && okProcDemoSign && okProcDemoIntra && okProcDemoCalls
    then putStrLn "All regression checks passed."
    else exitFailure
