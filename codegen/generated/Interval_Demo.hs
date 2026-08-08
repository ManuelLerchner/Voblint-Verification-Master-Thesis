{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Interval_Demo(Num, Nat, Char, Sum, Cfg_node, Ivl, Resolved_st_q, Set, Cfg_ext,
                 Strategy_tree, loop_ivl_sol, loop_ivl_td_sol)
  where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;

data Num = One | Bit0 Num | Bit1 Num;

equal_num :: Num -> Num -> Bool;
equal_num (Bit0 x2) (Bit1 x3) = False;
equal_num (Bit1 x3) (Bit0 x2) = False;
equal_num One (Bit1 x3) = False;
equal_num (Bit1 x3) One = False;
equal_num One (Bit0 x2) = False;
equal_num (Bit0 x2) One = False;
equal_num (Bit1 x3) (Bit1 y3) = equal_num x3 y3;
equal_num (Bit0 x2) (Bit0 y2) = equal_num x2 y2;
equal_num One One = True;

data Int = Zero_int | Pos Num | Neg Num;

equal_int :: Int -> Int -> Bool;
equal_int Zero_int Zero_int = True;
equal_int Zero_int (Pos l) = False;
equal_int Zero_int (Neg l) = False;
equal_int (Pos k) Zero_int = False;
equal_int (Pos k) (Pos l) = equal_num k l;
equal_int (Pos k) (Neg l) = False;
equal_int (Neg k) Zero_int = False;
equal_int (Neg k) (Pos l) = False;
equal_int (Neg k) (Neg l) = equal_num k l;

instance Eq Int where {
  a == b = equal_int a b;
};

less_eq_num :: Num -> Num -> Bool;
less_eq_num One n = True;
less_eq_num (Bit0 m) One = False;
less_eq_num (Bit1 m) One = False;
less_eq_num (Bit0 m) (Bit0 n) = less_eq_num m n;
less_eq_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit1 m) (Bit1 n) = less_eq_num m n;
less_eq_num (Bit1 m) (Bit0 n) = less_num m n;

less_num :: Num -> Num -> Bool;
less_num m One = False;
less_num One (Bit0 n) = True;
less_num One (Bit1 n) = True;
less_num (Bit0 m) (Bit0 n) = less_num m n;
less_num (Bit0 m) (Bit1 n) = less_eq_num m n;
less_num (Bit1 m) (Bit1 n) = less_num m n;
less_num (Bit1 m) (Bit0 n) = less_num m n;

less_eq_int :: Int -> Int -> Bool;
less_eq_int Zero_int Zero_int = True;
less_eq_int Zero_int (Pos l) = True;
less_eq_int Zero_int (Neg l) = False;
less_eq_int (Pos k) Zero_int = False;
less_eq_int (Pos k) (Pos l) = less_eq_num k l;
less_eq_int (Pos k) (Neg l) = False;
less_eq_int (Neg k) Zero_int = True;
less_eq_int (Neg k) (Pos l) = True;
less_eq_int (Neg k) (Neg l) = less_eq_num l k;

class Ord a where {
  less_eq :: a -> a -> Bool;
  less :: a -> a -> Bool;
};

less_int :: Int -> Int -> Bool;
less_int Zero_int Zero_int = False;
less_int Zero_int (Pos l) = True;
less_int Zero_int (Neg l) = False;
less_int (Pos k) Zero_int = False;
less_int (Pos k) (Pos l) = less_num k l;
less_int (Pos k) (Neg l) = False;
less_int (Neg k) Zero_int = True;
less_int (Neg k) (Pos l) = True;
less_int (Neg k) (Neg l) = less_num l k;

instance Ord Int where {
  less_eq = less_eq_int;
  less = less_int;
};

class (Ord a) => Preorder a where {
};

class (Preorder a) => Order a where {
};

instance Preorder Int where {
};

instance Order Int where {
};

class (Order a) => Linorder a where {
};

instance Linorder Int where {
};

data Nat = Zero_nat | Suc Nat;

equal_nat :: Nat -> Nat -> Bool;
equal_nat Zero_nat (Suc x2) = False;
equal_nat (Suc x2) Zero_nat = False;
equal_nat (Suc x2) (Suc y2) = equal_nat x2 y2;
equal_nat Zero_nat Zero_nat = True;

instance Eq Nat where {
  a == b = equal_nat a b;
};

less_eq_nat :: Nat -> Nat -> Bool;
less_eq_nat Zero_nat n = True;
less_eq_nat (Suc m) n = less_nat m n;

less_nat :: Nat -> Nat -> Bool;
less_nat n Zero_nat = False;
less_nat m (Suc n) = less_eq_nat m n;

instance Ord Nat where {
  less_eq = less_eq_nat;
  less = less_nat;
};

instance Preorder Nat where {
};

instance Order Nat where {
};

instance Linorder Nat where {
};

less_eq_bool :: Bool -> Bool -> Bool;
less_eq_bool False b = True;
less_eq_bool True b = b;

less_bool :: Bool -> Bool -> Bool;
less_bool False b = b;
less_bool True b = False;

instance Ord Bool where {
  less_eq = less_eq_bool;
  less = less_bool;
};

data Char = Char Bool Bool Bool Bool Bool Bool Bool Bool;

equal_char :: Char -> Char -> Bool;
equal_char (Char x1 x2 x3 x4 x5 x6 x7 x8) (Char y1 y2 y3 y4 y5 y6 y7 y8) =
  x1 == y1 &&
    x2 == y2 &&
      x3 == y3 && x4 == y4 && x5 == y5 && x6 == y6 && x7 == y7 && x8 == y8;

instance Eq Char where {
  a == b = equal_char a b;
};

lexordp_eq :: forall a. (Ord a) => [a] -> [a] -> Bool;
lexordp_eq [] ys = True;
lexordp_eq xs [] = null xs;
lexordp_eq (x : xs) (y : ys) = less x y || not (less y x) && lexordp_eq xs ys;

less_eq_char :: Char -> Char -> Bool;
less_eq_char (Char b0 b1 b2 b3 b4 b5 b6 b7) (Char c0 c1 c2 c3 c4 c5 c6 c7) =
  lexordp_eq [b7, b6, b5, b4, b3, b2, b1, b0] [c7, c6, c5, c4, c3, c2, c1, c0];

lexordp :: forall a. (Ord a) => [a] -> [a] -> Bool;
lexordp [] ys = not (null ys);
lexordp xs [] = False;
lexordp (x : xs) (y : ys) = less x y || not (less y x) && lexordp xs ys;

less_char :: Char -> Char -> Bool;
less_char (Char b0 b1 b2 b3 b4 b5 b6 b7) (Char c0 c1 c2 c3 c4 c5 c6 c7) =
  lexordp [b7, b6, b5, b4, b3, b2, b1, b0] [c7, c6, c5, c4, c3, c2, c1, c0];

instance Ord Char where {
  less_eq = less_eq_char;
  less = less_char;
};

instance Preorder Char where {
};

instance Order Char where {
};

instance Linorder Char where {
};

data Sum a b = Inl a | Inr b;

equal_sum :: forall a b. (Eq a, Eq b) => Sum a b -> Sum a b -> Bool;
equal_sum (Inl x1) (Inr x2) = False;
equal_sum (Inr x2) (Inl x1) = False;
equal_sum (Inr x2) (Inr y2) = x2 == y2;
equal_sum (Inl x1) (Inl y1) = x1 == y1;

instance (Eq a, Eq b) => Eq (Sum a b) where {
  a == b = equal_sum a b;
};

data Cfg_node = Statement Nat | FunctionEntry [Char] | FunctionResult [Char];

equal_cfg_node :: Cfg_node -> Cfg_node -> Bool;
equal_cfg_node (FunctionEntry x2) (FunctionResult x3) = False;
equal_cfg_node (FunctionResult x3) (FunctionEntry x2) = False;
equal_cfg_node (Statement x1) (FunctionResult x3) = False;
equal_cfg_node (FunctionResult x3) (Statement x1) = False;
equal_cfg_node (Statement x1) (FunctionEntry x2) = False;
equal_cfg_node (FunctionEntry x2) (Statement x1) = False;
equal_cfg_node (FunctionResult x3) (FunctionResult y3) = x3 == y3;
equal_cfg_node (FunctionEntry x2) (FunctionEntry y2) = x2 == y2;
equal_cfg_node (Statement x1) (Statement y1) = equal_nat x1 y1;

instance Eq Cfg_node where {
  a == b = equal_cfg_node a b;
};

data Ordera = Eqa | Lt | Gt;

comparator_of :: forall a. (Eq a, Linorder a) => a -> a -> Ordera;
comparator_of x y = (if less x y then Lt else (if x == y then Eqa else Gt));

comparator_list :: forall a. (a -> a -> Ordera) -> [a] -> [a] -> Ordera;
comparator_list comp_a [] [] = Eqa;
comparator_list comp_a [] (y : ya) = Lt;
comparator_list comp_a (x : xa) [] = Gt;
comparator_list comp_a (x : xa) (y : ya) =
  (case comp_a x y of {
    Eqa -> comparator_list comp_a xa ya;
    Lt -> Lt;
    Gt -> Gt;
  });

comparator_cfg_node :: Cfg_node -> Cfg_node -> Ordera;
comparator_cfg_node (Statement x) (Statement y) = comparator_of x y;
comparator_cfg_node (Statement x) (FunctionEntry ya) = Lt;
comparator_cfg_node (Statement x) (FunctionResult yb) = Lt;
comparator_cfg_node (FunctionEntry x) (Statement y) = Gt;
comparator_cfg_node (FunctionEntry x) (FunctionEntry ya) =
  comparator_list comparator_of x ya;
comparator_cfg_node (FunctionEntry x) (FunctionResult yb) = Lt;
comparator_cfg_node (FunctionResult x) (Statement y) = Gt;
comparator_cfg_node (FunctionResult x) (FunctionEntry ya) = Gt;
comparator_cfg_node (FunctionResult x) (FunctionResult yb) =
  comparator_list comparator_of x yb;

le_of_comp :: forall a. (a -> a -> Ordera) -> a -> a -> Bool;
le_of_comp acomp x y = (case acomp x y of {
                         Eqa -> True;
                         Lt -> True;
                         Gt -> False;
                       });

less_eq_cfg_node :: Cfg_node -> Cfg_node -> Bool;
less_eq_cfg_node = le_of_comp comparator_cfg_node;

lt_of_comp :: forall a. (a -> a -> Ordera) -> a -> a -> Bool;
lt_of_comp acomp x y = (case acomp x y of {
                         Eqa -> False;
                         Lt -> True;
                         Gt -> False;
                       });

less_cfg_node :: Cfg_node -> Cfg_node -> Bool;
less_cfg_node = lt_of_comp comparator_cfg_node;

instance Ord Cfg_node where {
  less_eq = less_eq_cfg_node;
  less = less_cfg_node;
};

instance Preorder Cfg_node where {
};

instance Order Cfg_node where {
};

instance Linorder Cfg_node where {
};

data Location = Local_Location [Char] | Global_Location [Char];

equal_location :: Location -> Location -> Bool;
equal_location (Local_Location x1) (Global_Location x2) = False;
equal_location (Global_Location x2) (Local_Location x1) = False;
equal_location (Global_Location x2) (Global_Location y2) = x2 == y2;
equal_location (Local_Location x1) (Local_Location y1) = x1 == y1;

instance Eq Location where {
  a == b = equal_location a b;
};

data Aexp = N Int | V [Char] | Plus Aexp Aexp | Minus Aexp Aexp
  | Times Aexp Aexp;

equal_aexp :: Aexp -> Aexp -> Bool;
equal_aexp (Minus x41 x42) (Times x51 x52) = False;
equal_aexp (Times x51 x52) (Minus x41 x42) = False;
equal_aexp (Plus x31 x32) (Times x51 x52) = False;
equal_aexp (Times x51 x52) (Plus x31 x32) = False;
equal_aexp (Plus x31 x32) (Minus x41 x42) = False;
equal_aexp (Minus x41 x42) (Plus x31 x32) = False;
equal_aexp (V x2) (Times x51 x52) = False;
equal_aexp (Times x51 x52) (V x2) = False;
equal_aexp (V x2) (Minus x41 x42) = False;
equal_aexp (Minus x41 x42) (V x2) = False;
equal_aexp (V x2) (Plus x31 x32) = False;
equal_aexp (Plus x31 x32) (V x2) = False;
equal_aexp (N x1) (Times x51 x52) = False;
equal_aexp (Times x51 x52) (N x1) = False;
equal_aexp (N x1) (Minus x41 x42) = False;
equal_aexp (Minus x41 x42) (N x1) = False;
equal_aexp (N x1) (Plus x31 x32) = False;
equal_aexp (Plus x31 x32) (N x1) = False;
equal_aexp (N x1) (V x2) = False;
equal_aexp (V x2) (N x1) = False;
equal_aexp (Times x51 x52) (Times y51 y52) =
  equal_aexp x51 y51 && equal_aexp x52 y52;
equal_aexp (Minus x41 x42) (Minus y41 y42) =
  equal_aexp x41 y41 && equal_aexp x42 y42;
equal_aexp (Plus x31 x32) (Plus y31 y32) =
  equal_aexp x31 y31 && equal_aexp x32 y32;
equal_aexp (V x2) (V y2) = x2 == y2;
equal_aexp (N x1) (N y1) = equal_int x1 y1;

instance Eq Aexp where {
  a == b = equal_aexp a b;
};

less_eq_prod :: forall a b. (Ord a, Ord b) => (a, b) -> (a, b) -> Bool;
less_eq_prod (x1, y1) (x2, y2) = less x1 x2 || less_eq x1 x2 && less_eq y1 y2;

less_prod :: forall a b. (Ord a, Ord b) => (a, b) -> (a, b) -> Bool;
less_prod (x1, y1) (x2, y2) = less x1 x2 || less_eq x1 x2 && less y1 y2;

instance (Ord a, Ord b) => Ord (a, b) where {
  less_eq = less_eq_prod;
  less = less_prod;
};

instance (Preorder a, Preorder b) => Preorder (a, b) where {
};

instance (Order a, Order b) => Order (a, b) where {
};

instance (Linorder a, Linorder b) => Linorder (a, b) where {
};

data Call_action = CallEdge (Maybe [Char]) [[Char]] [Aexp];

equal_call_action :: Call_action -> Call_action -> Bool;
equal_call_action (CallEdge x1 x2 x3) (CallEdge y1 y2 y3) =
  x1 == y1 && x2 == y2 && x3 == y3;

instance Eq Call_action where {
  a == b = equal_call_action a b;
};

comparator_option ::
  forall a. (a -> a -> Ordera) -> Maybe a -> Maybe a -> Ordera;
comparator_option comp_a Nothing Nothing = Eqa;
comparator_option comp_a Nothing (Just y) = Lt;
comparator_option comp_a (Just x) Nothing = Gt;
comparator_option comp_a (Just x) (Just y) = comp_a x y;

comparator_aexp :: Aexp -> Aexp -> Ordera;
comparator_aexp (N x) (N y) = comparator_of x y;
comparator_aexp (N x) (V ya) = Lt;
comparator_aexp (N x) (Plus yb yc) = Lt;
comparator_aexp (N x) (Minus yd ye) = Lt;
comparator_aexp (N x) (Times yf yg) = Lt;
comparator_aexp (V x) (N y) = Gt;
comparator_aexp (V x) (V ya) = comparator_list comparator_of x ya;
comparator_aexp (V x) (Plus yb yc) = Lt;
comparator_aexp (V x) (Minus yd ye) = Lt;
comparator_aexp (V x) (Times yf yg) = Lt;
comparator_aexp (Plus x xa) (N y) = Gt;
comparator_aexp (Plus x xa) (V ya) = Gt;
comparator_aexp (Plus x xa) (Plus yb yc) = (case comparator_aexp x yb of {
     Eqa -> comparator_aexp xa yc;
     Lt -> Lt;
     Gt -> Gt;
   });
comparator_aexp (Plus x xa) (Minus yd ye) = Lt;
comparator_aexp (Plus x xa) (Times yf yg) = Lt;
comparator_aexp (Minus x xa) (N y) = Gt;
comparator_aexp (Minus x xa) (V ya) = Gt;
comparator_aexp (Minus x xa) (Plus yb yc) = Gt;
comparator_aexp (Minus x xa) (Minus yd ye) = (case comparator_aexp x yd of {
       Eqa -> comparator_aexp xa ye;
       Lt -> Lt;
       Gt -> Gt;
     });
comparator_aexp (Minus x xa) (Times yf yg) = Lt;
comparator_aexp (Times x xa) (N y) = Gt;
comparator_aexp (Times x xa) (V ya) = Gt;
comparator_aexp (Times x xa) (Plus yb yc) = Gt;
comparator_aexp (Times x xa) (Minus yd ye) = Gt;
comparator_aexp (Times x xa) (Times yf yg) = (case comparator_aexp x yf of {
       Eqa -> comparator_aexp xa yg;
       Lt -> Lt;
       Gt -> Gt;
     });

comparator_call_action :: Call_action -> Call_action -> Ordera;
comparator_call_action (CallEdge x xa xb) (CallEdge y ya yb) =
  (case comparator_option (comparator_list comparator_of) x y of {
    Eqa -> (case comparator_list (comparator_list comparator_of) xa ya of {
             Eqa -> comparator_list comparator_aexp xb yb;
             Lt -> Lt;
             Gt -> Gt;
           });
    Lt -> Lt;
    Gt -> Gt;
  });

less_eq_call_action :: Call_action -> Call_action -> Bool;
less_eq_call_action = le_of_comp comparator_call_action;

less_call_action :: Call_action -> Call_action -> Bool;
less_call_action = lt_of_comp comparator_call_action;

instance Ord Call_action where {
  less_eq = less_eq_call_action;
  less = less_call_action;
};

instance Preorder Call_action where {
};

instance Order Call_action where {
};

instance Linorder Call_action where {
};

data Bexp = Bc Bool | Not Bexp | And Bexp Bexp | Or Bexp Bexp | Less Aexp Aexp
  | Eqb Aexp Aexp;

equal_bexp :: Bexp -> Bexp -> Bool;
equal_bexp (Less x51 x52) (Eqb x61 x62) = False;
equal_bexp (Eqb x61 x62) (Less x51 x52) = False;
equal_bexp (Or x41 x42) (Eqb x61 x62) = False;
equal_bexp (Eqb x61 x62) (Or x41 x42) = False;
equal_bexp (Or x41 x42) (Less x51 x52) = False;
equal_bexp (Less x51 x52) (Or x41 x42) = False;
equal_bexp (And x31 x32) (Eqb x61 x62) = False;
equal_bexp (Eqb x61 x62) (And x31 x32) = False;
equal_bexp (And x31 x32) (Less x51 x52) = False;
equal_bexp (Less x51 x52) (And x31 x32) = False;
equal_bexp (And x31 x32) (Or x41 x42) = False;
equal_bexp (Or x41 x42) (And x31 x32) = False;
equal_bexp (Not x2) (Eqb x61 x62) = False;
equal_bexp (Eqb x61 x62) (Not x2) = False;
equal_bexp (Not x2) (Less x51 x52) = False;
equal_bexp (Less x51 x52) (Not x2) = False;
equal_bexp (Not x2) (Or x41 x42) = False;
equal_bexp (Or x41 x42) (Not x2) = False;
equal_bexp (Not x2) (And x31 x32) = False;
equal_bexp (And x31 x32) (Not x2) = False;
equal_bexp (Bc x1) (Eqb x61 x62) = False;
equal_bexp (Eqb x61 x62) (Bc x1) = False;
equal_bexp (Bc x1) (Less x51 x52) = False;
equal_bexp (Less x51 x52) (Bc x1) = False;
equal_bexp (Bc x1) (Or x41 x42) = False;
equal_bexp (Or x41 x42) (Bc x1) = False;
equal_bexp (Bc x1) (And x31 x32) = False;
equal_bexp (And x31 x32) (Bc x1) = False;
equal_bexp (Bc x1) (Not x2) = False;
equal_bexp (Not x2) (Bc x1) = False;
equal_bexp (Eqb x61 x62) (Eqb y61 y62) =
  equal_aexp x61 y61 && equal_aexp x62 y62;
equal_bexp (Less x51 x52) (Less y51 y52) =
  equal_aexp x51 y51 && equal_aexp x52 y52;
equal_bexp (Or x41 x42) (Or y41 y42) = equal_bexp x41 y41 && equal_bexp x42 y42;
equal_bexp (And x31 x32) (And y31 y32) =
  equal_bexp x31 y31 && equal_bexp x32 y32;
equal_bexp (Not x2) (Not y2) = equal_bexp x2 y2;
equal_bexp (Bc x1) (Bc y1) = x1 == y1;

data Edge_action = EA_Nop | EA_Assign [Char] Aexp | EA_Random [Char]
  | EA_Assume Bexp | EA_AssumeNot Bexp | EA_Ret (Maybe Aexp) [Char]
  | EA_Check Bexp;

equal_edge_action :: Edge_action -> Edge_action -> Bool;
equal_edge_action (EA_Ret x61 x62) (EA_Check x7) = False;
equal_edge_action (EA_Check x7) (EA_Ret x61 x62) = False;
equal_edge_action (EA_AssumeNot x5) (EA_Check x7) = False;
equal_edge_action (EA_Check x7) (EA_AssumeNot x5) = False;
equal_edge_action (EA_AssumeNot x5) (EA_Ret x61 x62) = False;
equal_edge_action (EA_Ret x61 x62) (EA_AssumeNot x5) = False;
equal_edge_action (EA_Assume x4) (EA_Check x7) = False;
equal_edge_action (EA_Check x7) (EA_Assume x4) = False;
equal_edge_action (EA_Assume x4) (EA_Ret x61 x62) = False;
equal_edge_action (EA_Ret x61 x62) (EA_Assume x4) = False;
equal_edge_action (EA_Assume x4) (EA_AssumeNot x5) = False;
equal_edge_action (EA_AssumeNot x5) (EA_Assume x4) = False;
equal_edge_action (EA_Random x3) (EA_Check x7) = False;
equal_edge_action (EA_Check x7) (EA_Random x3) = False;
equal_edge_action (EA_Random x3) (EA_Ret x61 x62) = False;
equal_edge_action (EA_Ret x61 x62) (EA_Random x3) = False;
equal_edge_action (EA_Random x3) (EA_AssumeNot x5) = False;
equal_edge_action (EA_AssumeNot x5) (EA_Random x3) = False;
equal_edge_action (EA_Random x3) (EA_Assume x4) = False;
equal_edge_action (EA_Assume x4) (EA_Random x3) = False;
equal_edge_action (EA_Assign x21 x22) (EA_Check x7) = False;
equal_edge_action (EA_Check x7) (EA_Assign x21 x22) = False;
equal_edge_action (EA_Assign x21 x22) (EA_Ret x61 x62) = False;
equal_edge_action (EA_Ret x61 x62) (EA_Assign x21 x22) = False;
equal_edge_action (EA_Assign x21 x22) (EA_AssumeNot x5) = False;
equal_edge_action (EA_AssumeNot x5) (EA_Assign x21 x22) = False;
equal_edge_action (EA_Assign x21 x22) (EA_Assume x4) = False;
equal_edge_action (EA_Assume x4) (EA_Assign x21 x22) = False;
equal_edge_action (EA_Assign x21 x22) (EA_Random x3) = False;
equal_edge_action (EA_Random x3) (EA_Assign x21 x22) = False;
equal_edge_action EA_Nop (EA_Check x7) = False;
equal_edge_action (EA_Check x7) EA_Nop = False;
equal_edge_action EA_Nop (EA_Ret x61 x62) = False;
equal_edge_action (EA_Ret x61 x62) EA_Nop = False;
equal_edge_action EA_Nop (EA_AssumeNot x5) = False;
equal_edge_action (EA_AssumeNot x5) EA_Nop = False;
equal_edge_action EA_Nop (EA_Assume x4) = False;
equal_edge_action (EA_Assume x4) EA_Nop = False;
equal_edge_action EA_Nop (EA_Random x3) = False;
equal_edge_action (EA_Random x3) EA_Nop = False;
equal_edge_action EA_Nop (EA_Assign x21 x22) = False;
equal_edge_action (EA_Assign x21 x22) EA_Nop = False;
equal_edge_action (EA_Check x7) (EA_Check y7) = equal_bexp x7 y7;
equal_edge_action (EA_Ret x61 x62) (EA_Ret y61 y62) = x61 == y61 && x62 == y62;
equal_edge_action (EA_AssumeNot x5) (EA_AssumeNot y5) = equal_bexp x5 y5;
equal_edge_action (EA_Assume x4) (EA_Assume y4) = equal_bexp x4 y4;
equal_edge_action (EA_Random x3) (EA_Random y3) = x3 == y3;
equal_edge_action (EA_Assign x21 x22) (EA_Assign y21 y22) =
  x21 == y21 && equal_aexp x22 y22;
equal_edge_action EA_Nop EA_Nop = True;

instance Eq Edge_action where {
  a == b = equal_edge_action a b;
};

comparator_bool :: Bool -> Bool -> Ordera;
comparator_bool False False = Eqa;
comparator_bool False True = Lt;
comparator_bool True True = Eqa;
comparator_bool True False = Gt;

comparator_bexp :: Bexp -> Bexp -> Ordera;
comparator_bexp (Bc x) (Bc y) = comparator_bool x y;
comparator_bexp (Bc x) (Not ya) = Lt;
comparator_bexp (Bc x) (And yb yc) = Lt;
comparator_bexp (Bc x) (Or yd ye) = Lt;
comparator_bexp (Bc x) (Less yf yg) = Lt;
comparator_bexp (Bc x) (Eqb yh yi) = Lt;
comparator_bexp (Not x) (Bc y) = Gt;
comparator_bexp (Not x) (Not ya) = comparator_bexp x ya;
comparator_bexp (Not x) (And yb yc) = Lt;
comparator_bexp (Not x) (Or yd ye) = Lt;
comparator_bexp (Not x) (Less yf yg) = Lt;
comparator_bexp (Not x) (Eqb yh yi) = Lt;
comparator_bexp (And x xa) (Bc y) = Gt;
comparator_bexp (And x xa) (Not ya) = Gt;
comparator_bexp (And x xa) (And yb yc) = (case comparator_bexp x yb of {
   Eqa -> comparator_bexp xa yc;
   Lt -> Lt;
   Gt -> Gt;
 });
comparator_bexp (And x xa) (Or yd ye) = Lt;
comparator_bexp (And x xa) (Less yf yg) = Lt;
comparator_bexp (And x xa) (Eqb yh yi) = Lt;
comparator_bexp (Or x xa) (Bc y) = Gt;
comparator_bexp (Or x xa) (Not ya) = Gt;
comparator_bexp (Or x xa) (And yb yc) = Gt;
comparator_bexp (Or x xa) (Or yd ye) = (case comparator_bexp x yd of {
 Eqa -> comparator_bexp xa ye;
 Lt -> Lt;
 Gt -> Gt;
                                       });
comparator_bexp (Or x xa) (Less yf yg) = Lt;
comparator_bexp (Or x xa) (Eqb yh yi) = Lt;
comparator_bexp (Less x xa) (Bc y) = Gt;
comparator_bexp (Less x xa) (Not ya) = Gt;
comparator_bexp (Less x xa) (And yb yc) = Gt;
comparator_bexp (Less x xa) (Or yd ye) = Gt;
comparator_bexp (Less x xa) (Less yf yg) = (case comparator_aexp x yf of {
     Eqa -> comparator_aexp xa yg;
     Lt -> Lt;
     Gt -> Gt;
   });
comparator_bexp (Less x xa) (Eqb yh yi) = Lt;
comparator_bexp (Eqb x xa) (Bc y) = Gt;
comparator_bexp (Eqb x xa) (Not ya) = Gt;
comparator_bexp (Eqb x xa) (And yb yc) = Gt;
comparator_bexp (Eqb x xa) (Or yd ye) = Gt;
comparator_bexp (Eqb x xa) (Less yf yg) = Gt;
comparator_bexp (Eqb x xa) (Eqb yh yi) = (case comparator_aexp x yh of {
   Eqa -> comparator_aexp xa yi;
   Lt -> Lt;
   Gt -> Gt;
 });

comparator_edge_action :: Edge_action -> Edge_action -> Ordera;
comparator_edge_action EA_Nop EA_Nop = Eqa;
comparator_edge_action EA_Nop (EA_Assign y ya) = Lt;
comparator_edge_action EA_Nop (EA_Random yb) = Lt;
comparator_edge_action EA_Nop (EA_Assume yc) = Lt;
comparator_edge_action EA_Nop (EA_AssumeNot yd) = Lt;
comparator_edge_action EA_Nop (EA_Ret ye yf) = Lt;
comparator_edge_action EA_Nop (EA_Check yg) = Lt;
comparator_edge_action (EA_Assign x xa) EA_Nop = Gt;
comparator_edge_action (EA_Assign x xa) (EA_Assign y ya) =
  (case comparator_list comparator_of x y of {
    Eqa -> comparator_aexp xa ya;
    Lt -> Lt;
    Gt -> Gt;
  });
comparator_edge_action (EA_Assign x xa) (EA_Random yb) = Lt;
comparator_edge_action (EA_Assign x xa) (EA_Assume yc) = Lt;
comparator_edge_action (EA_Assign x xa) (EA_AssumeNot yd) = Lt;
comparator_edge_action (EA_Assign x xa) (EA_Ret ye yf) = Lt;
comparator_edge_action (EA_Assign x xa) (EA_Check yg) = Lt;
comparator_edge_action (EA_Random x) EA_Nop = Gt;
comparator_edge_action (EA_Random x) (EA_Assign y ya) = Gt;
comparator_edge_action (EA_Random x) (EA_Random yb) =
  comparator_list comparator_of x yb;
comparator_edge_action (EA_Random x) (EA_Assume yc) = Lt;
comparator_edge_action (EA_Random x) (EA_AssumeNot yd) = Lt;
comparator_edge_action (EA_Random x) (EA_Ret ye yf) = Lt;
comparator_edge_action (EA_Random x) (EA_Check yg) = Lt;
comparator_edge_action (EA_Assume x) EA_Nop = Gt;
comparator_edge_action (EA_Assume x) (EA_Assign y ya) = Gt;
comparator_edge_action (EA_Assume x) (EA_Random yb) = Gt;
comparator_edge_action (EA_Assume x) (EA_Assume yc) = comparator_bexp x yc;
comparator_edge_action (EA_Assume x) (EA_AssumeNot yd) = Lt;
comparator_edge_action (EA_Assume x) (EA_Ret ye yf) = Lt;
comparator_edge_action (EA_Assume x) (EA_Check yg) = Lt;
comparator_edge_action (EA_AssumeNot x) EA_Nop = Gt;
comparator_edge_action (EA_AssumeNot x) (EA_Assign y ya) = Gt;
comparator_edge_action (EA_AssumeNot x) (EA_Random yb) = Gt;
comparator_edge_action (EA_AssumeNot x) (EA_Assume yc) = Gt;
comparator_edge_action (EA_AssumeNot x) (EA_AssumeNot yd) =
  comparator_bexp x yd;
comparator_edge_action (EA_AssumeNot x) (EA_Ret ye yf) = Lt;
comparator_edge_action (EA_AssumeNot x) (EA_Check yg) = Lt;
comparator_edge_action (EA_Ret x xa) EA_Nop = Gt;
comparator_edge_action (EA_Ret x xa) (EA_Assign y ya) = Gt;
comparator_edge_action (EA_Ret x xa) (EA_Random yb) = Gt;
comparator_edge_action (EA_Ret x xa) (EA_Assume yc) = Gt;
comparator_edge_action (EA_Ret x xa) (EA_AssumeNot yd) = Gt;
comparator_edge_action (EA_Ret x xa) (EA_Ret ye yf) =
  (case comparator_option comparator_aexp x ye of {
    Eqa -> comparator_list comparator_of xa yf;
    Lt -> Lt;
    Gt -> Gt;
  });
comparator_edge_action (EA_Ret x xa) (EA_Check yg) = Lt;
comparator_edge_action (EA_Check x) EA_Nop = Gt;
comparator_edge_action (EA_Check x) (EA_Assign y ya) = Gt;
comparator_edge_action (EA_Check x) (EA_Random yb) = Gt;
comparator_edge_action (EA_Check x) (EA_Assume yc) = Gt;
comparator_edge_action (EA_Check x) (EA_AssumeNot yd) = Gt;
comparator_edge_action (EA_Check x) (EA_Ret ye yf) = Gt;
comparator_edge_action (EA_Check x) (EA_Check yg) = comparator_bexp x yg;

less_eq_edge_action :: Edge_action -> Edge_action -> Bool;
less_eq_edge_action = le_of_comp comparator_edge_action;

less_edge_action :: Edge_action -> Edge_action -> Bool;
less_edge_action = lt_of_comp comparator_edge_action;

instance Ord Edge_action where {
  less_eq = less_eq_edge_action;
  less = less_edge_action;
};

instance Preorder Edge_action where {
};

instance Order Edge_action where {
};

instance Linorder Edge_action where {
};

data Eint = MinInf | Fin Int | PlusInf;

equal_eint :: Eint -> Eint -> Bool;
equal_eint (Fin x2) PlusInf = False;
equal_eint PlusInf (Fin x2) = False;
equal_eint MinInf PlusInf = False;
equal_eint PlusInf MinInf = False;
equal_eint MinInf (Fin x2) = False;
equal_eint (Fin x2) MinInf = False;
equal_eint (Fin x2) (Fin y2) = equal_int x2 y2;
equal_eint PlusInf PlusInf = True;
equal_eint MinInf MinInf = True;

data Ivl = Ivl Eint Eint;

equal_ivl :: Ivl -> Ivl -> Bool;
equal_ivl (Ivl x1 x2) (Ivl y1 y2) = equal_eint x1 y1 && equal_eint x2 y2;

instance Eq Ivl where {
  a == b = equal_ivl a b;
};

eint_le :: Eint -> Eint -> Bool;
eint_le MinInf uu = True;
eint_le (Fin v) PlusInf = True;
eint_le PlusInf PlusInf = True;
eint_le (Fin n) (Fin m) = less_eq_int n m;
eint_le (Fin v) MinInf = False;
eint_le PlusInf MinInf = False;
eint_le PlusInf (Fin v) = False;

less_eq_eint :: Eint -> Eint -> Bool;
less_eq_eint = eint_le;

join_ivl :: Ivl -> Ivl -> Ivl;
join_ivl (Ivl l1 u1) (Ivl l2 u2) =
  Ivl (if less_eq_eint l1 l2 then l1 else l2)
    (if less_eq_eint u2 u1 then u1 else u2);

sup_ivl :: Ivl -> Ivl -> Ivl;
sup_ivl = join_ivl;

class Sup a where {
  sup :: a -> a -> a;
};

instance Sup Ivl where {
  sup = sup_ivl;
};

bot_ivl :: Ivl;
bot_ivl = Ivl PlusInf MinInf;

class Bot a where {
  bot :: a;
};

instance Bot Ivl where {
  bot = bot_ivl;
};

less_eq_ivl :: Ivl -> Ivl -> Bool;
less_eq_ivl a b =
  (case (a, b) of {
    (Ivl l1 u1, Ivl l2 u2) -> less_eq_eint l2 l1 && less_eq_eint u1 u2;
  });

less_ivl :: Ivl -> Ivl -> Bool;
less_ivl a b = less_eq_ivl a b && not (less_eq_ivl b a);

instance Ord Ivl where {
  less_eq = less_eq_ivl;
  less = less_ivl;
};

instance Preorder Ivl where {
};

instance Order Ivl where {
};

class (Bot a, Order a) => Order_bot a where {
};

instance Order_bot Ivl where {
};

widen_ivl_core :: Ivl -> Ivl -> Ivl;
widen_ivl_core (Ivl l1 u1) (Ivl l2 u2) =
  Ivl (if less_eq_eint l1 l2 then l1 else MinInf)
    (if less_eq_eint u2 u1 then u1 else PlusInf);

widen_ivl :: Ivl -> Ivl -> Ivl;
widen_ivl a b =
  (if equal_ivl a bot_ivl then b
    else (if equal_ivl b bot_ivl then a else widen_ivl_core a b));

class (Order a) => Widening a where {
  widen :: a -> a -> a;
};

instance Widening Ivl where {
  widen = widen_ivl;
};

narrow_ivl_td :: Ivl -> Ivl -> Ivl;
narrow_ivl_td (Ivl l1 u1) (Ivl l2 u2) =
  Ivl (if equal_eint l1 MinInf then l2 else l1)
    (if equal_eint u1 PlusInf then u2 else u1);

narrow_ivl :: Ivl -> Ivl -> Ivl;
narrow_ivl a b = narrow_ivl_td a b;

class (Order a) => Narrowing a where {
  narrow :: a -> a -> a;
};

instance Narrowing Ivl where {
  narrow = narrow_ivl;
};

class (Narrowing a, Widening a) => Warrowing a where {
};

instance Warrowing Ivl where {
};

class (Sup a, Order a) => Semilattice_sup a where {
};

instance Semilattice_sup Ivl where {
};

class (Semilattice_sup a, Order_bot a) => Bounded_semilattice_sup_bot a where {
};

class (Bounded_semilattice_sup_bot a,
        Warrowing a) => Bounded_warrowing a where {
};

instance Bounded_semilattice_sup_bot Ivl where {
};

instance Bounded_warrowing Ivl where {
};

map_of :: forall a b. (Eq a) => [(a, b)] -> a -> Maybe b;
map_of [] k = Nothing;
map_of ((l, v) : ps) k = (if l == k then Just v else map_of ps k);

lookup_resolved_st ::
  forall a. (Bot a) => (a, (a, [(Location, a)])) -> Location -> a;
lookup_resolved_st (dl, (dg, ps)) loc =
  (case map_of ps loc of {
    Nothing -> (case loc of {
                 Local_Location _ -> dl;
                 Global_Location _ -> dg;
               });
    Just a -> a;
  });

le_resolved_st_code ::
  forall a.
    (Order_bot a) => (a, (a, [(Location, a)])) ->
                       (a, (a, [(Location, a)])) -> Bool;
le_resolved_st_code s t =
  (case s of {
    (dl, (dg, ps)) ->
      (case t of {
        (el, (eg, qs)) ->
          less_eq dl el &&
            less_eq dg eg &&
              all (\ loc ->
                    less_eq (lookup_resolved_st (dl, (dg, ps)) loc)
                      (lookup_resolved_st (el, (eg, qs)) loc))
                (map fst ps ++ map fst qs);
      });
  });

newtype Resolved_st_q a = Abs_resolved_st (a, (a, [(Location, a)]));

less_eq_resolved_st_q ::
  forall a. (Order_bot a) => Resolved_st_q a -> Resolved_st_q a -> Bool;
less_eq_resolved_st_q (Abs_resolved_st xb) (Abs_resolved_st x) =
  le_resolved_st_code xb x;

equal_resolved_st_q ::
  forall a. (Eq a, Order_bot a) => Resolved_st_q a -> Resolved_st_q a -> Bool;
equal_resolved_st_q s t =
  less_eq_resolved_st_q s t && less_eq_resolved_st_q t s;

instance (Eq a, Order_bot a) => Eq (Resolved_st_q a) where {
  a == b = equal_resolved_st_q a b;
};

merge_resolved_st ::
  forall a.
    (Bounded_semilattice_sup_bot a) => (a, (a, [(Location, a)])) ->
 (a, (a, [(Location, a)])) -> (a, (a, [(Location, a)]));
merge_resolved_st (dl1, (dg1, ps1)) (dl2, (dg2, ps2)) =
  (sup dl1 dl2,
    (sup dg1 dg2,
      map (\ (loc, _) ->
            (loc, sup (lookup_resolved_st (dl1, (dg1, ps1)) loc)
                    (lookup_resolved_st (dl2, (dg2, ps2)) loc)))
        (ps1 ++ ps2)));

sup_resolved_st_q ::
  forall a.
    (Bounded_semilattice_sup_bot a) => Resolved_st_q a ->
 Resolved_st_q a -> Resolved_st_q a;
sup_resolved_st_q (Abs_resolved_st xa) (Abs_resolved_st x) =
  Abs_resolved_st (merge_resolved_st xa x);

instance (Bounded_semilattice_sup_bot a) => Sup (Resolved_st_q a) where {
  sup = sup_resolved_st_q;
};

bot_resolved_st_q :: forall a. (Bot a) => Resolved_st_q a;
bot_resolved_st_q = Abs_resolved_st (bot, (bot, []));

instance (Bot a) => Bot (Resolved_st_q a) where {
  bot = bot_resolved_st_q;
};

less_resolved_st_q ::
  forall a. (Order_bot a) => Resolved_st_q a -> Resolved_st_q a -> Bool;
less_resolved_st_q s t =
  less_eq_resolved_st_q s t && not (less_eq_resolved_st_q t s);

instance (Order_bot a) => Ord (Resolved_st_q a) where {
  less_eq = less_eq_resolved_st_q;
  less = less_resolved_st_q;
};

instance (Order_bot a) => Preorder (Resolved_st_q a) where {
};

instance (Order_bot a) => Order (Resolved_st_q a) where {
};

instance (Order_bot a) => Order_bot (Resolved_st_q a) where {
};

widen_resolved_st ::
  forall a.
    (Bounded_warrowing a) => (a, (a, [(Location, a)])) ->
                               (a, (a, [(Location, a)])) ->
                                 (a, (a, [(Location, a)]));
widen_resolved_st (dl1, (dg1, ps1)) (dl2, (dg2, ps2)) =
  (widen dl1 dl2,
    (widen dg1 dg2,
      map (\ (loc, _) ->
            (loc, widen (lookup_resolved_st (dl1, (dg1, ps1)) loc)
                    (lookup_resolved_st (dl2, (dg2, ps2)) loc)))
        (ps1 ++ ps2)));

widen_on_resolved_st_q ::
  forall a.
    (Bounded_warrowing a) => Resolved_st_q a ->
                               Resolved_st_q a -> Resolved_st_q a;
widen_on_resolved_st_q (Abs_resolved_st xa) (Abs_resolved_st x) =
  Abs_resolved_st (widen_resolved_st xa x);

widen_resolved_st_q ::
  forall a.
    (Bounded_warrowing a) => Resolved_st_q a ->
                               Resolved_st_q a -> Resolved_st_q a;
widen_resolved_st_q s t = widen_on_resolved_st_q s t;

instance (Bounded_warrowing a) => Widening (Resolved_st_q a) where {
  widen = widen_resolved_st_q;
};

narrow_resolved_st ::
  forall a.
    (Bounded_warrowing a) => (a, (a, [(Location, a)])) ->
                               (a, (a, [(Location, a)])) ->
                                 (a, (a, [(Location, a)]));
narrow_resolved_st (dl1, (dg1, ps1)) (dl2, (dg2, ps2)) =
  (narrow dl1 dl2,
    (narrow dg1 dg2,
      map (\ (loc, _) ->
            (loc, narrow (lookup_resolved_st (dl1, (dg1, ps1)) loc)
                    (lookup_resolved_st (dl2, (dg2, ps2)) loc)))
        (ps1 ++ ps2)));

narrow_on_resolved_st_q ::
  forall a.
    (Bounded_warrowing a) => Resolved_st_q a ->
                               Resolved_st_q a -> Resolved_st_q a;
narrow_on_resolved_st_q (Abs_resolved_st xa) (Abs_resolved_st x) =
  Abs_resolved_st (narrow_resolved_st xa x);

narrow_resolved_st_q ::
  forall a.
    (Bounded_warrowing a) => Resolved_st_q a ->
                               Resolved_st_q a -> Resolved_st_q a;
narrow_resolved_st_q s t = narrow_on_resolved_st_q s t;

instance (Bounded_warrowing a) => Narrowing (Resolved_st_q a) where {
  narrow = narrow_resolved_st_q;
};

instance (Bounded_warrowing a) => Warrowing (Resolved_st_q a) where {
};

instance (Bounded_semilattice_sup_bot a) => Semilattice_sup (Resolved_st_q
                      a) where {
};

instance (Bounded_semilattice_sup_bot a) => Bounded_semilattice_sup_bot (Resolved_st_q
                                  a) where {
};

data Set a = Set [a] | Coset [a];

newtype Fset a = Abs_fset (Set a);

data Com = SKIP | Assign [Char] Aexp | Random [Char] | Check Bexp | Seq Com Com
  | If Bexp Com Com | While Bexp Com | Call (Maybe [Char]) [Char] [Aexp]
  | Return (Maybe Aexp) | Restore | Unwind;

newtype Fmap a b = Fmap_of_list [(a, b)];

data Cfg_ext a =
  Cfg_ext (Set (Cfg_node, (Edge_action, Cfg_node)))
    (Set (Cfg_node, (Call_action, (Cfg_node, Cfg_node)))) Cfg_node
    (Set (Cfg_node, Bexp)) a;

data State_ext a b c d =
  State_ext (Set a) (Fmap (Sum a b) [a]) (Set a) (Sum a b -> c) d;

data Strategy_tree a b c = Answer c | QueryL a (c -> Strategy_tree a b c)
  | QueryG b (c -> Strategy_tree a b c) | Side b c (Strategy_tree a b c);

data State_exta a b = State_exta (Set a) b;

data Proc_decl_ext a = Proc_decl_ext [[Char]] Com a;

data Ug_state_ext a b c d = Ug_state_ext (b -> Fmap a c) d;

data Imp_prog_ext a = Imp_prog_ext [([Char], Proc_decl_ext ())] Com [[Char]] a;

data Func_state a b c d =
  Q (a, (a, (State_ext a b c (State_exta a ()), Ug_state_ext a b c d)))
  | I (a, (State_ext a b c (State_exta a ()), Ug_state_ext a b c d))
  | R (a, (State_ext a b c (State_exta a ()), Ug_state_ext a b c d))
  | E (a, (Strategy_tree a b c,
            (b -> c,
              (State_ext a b c (State_exta a ()), Ug_state_ext a b c d))));

data Effectful_st_transfer_ext a b c =
  Effectful_st_transfer_ext (Cfg_node -> Strategy_tree Cfg_node a b)
    ([Char] -> Aexp -> Cfg_node -> Strategy_tree Cfg_node a b)
    ([Char] -> Cfg_node -> Strategy_tree Cfg_node a b)
    (Bexp -> Cfg_node -> Strategy_tree Cfg_node a b)
    (Bexp -> Cfg_node -> Strategy_tree Cfg_node a b)
    ([[Char]] -> [Aexp] -> Cfg_node -> Strategy_tree Cfg_node a b)
    (Maybe [Char] -> Cfg_node -> Cfg_node -> Strategy_tree Cfg_node a b) c;

dup :: Int -> Int;
dup Zero_int = Zero_int;
dup (Pos n) = Pos (Bit0 n);
dup (Neg n) = Neg (Bit0 n);

uminus_int :: Int -> Int;
uminus_int Zero_int = Zero_int;
uminus_int (Pos m) = Neg m;
uminus_int (Neg m) = Pos m;

plus_num :: Num -> Num -> Num;
plus_num One One = Bit0 One;
plus_num One (Bit0 n) = Bit1 n;
plus_num One (Bit1 n) = Bit0 (plus_num n One);
plus_num (Bit0 m) One = Bit1 m;
plus_num (Bit0 m) (Bit0 n) = Bit0 (plus_num m n);
plus_num (Bit0 m) (Bit1 n) = Bit1 (plus_num m n);
plus_num (Bit1 m) One = Bit0 (plus_num m One);
plus_num (Bit1 m) (Bit0 n) = Bit1 (plus_num m n);
plus_num (Bit1 m) (Bit1 n) = Bit0 (plus_num (plus_num m n) One);

one_int :: Int;
one_int = Pos One;

bitM :: Num -> Num;
bitM One = One;
bitM (Bit0 n) = Bit1 (bitM n);
bitM (Bit1 n) = Bit1 (Bit0 n);

sub :: Num -> Num -> Int;
sub One One = Zero_int;
sub (Bit0 m) One = Pos (bitM m);
sub (Bit1 m) One = Pos (Bit0 m);
sub One (Bit0 n) = Neg (bitM n);
sub One (Bit1 n) = Neg (Bit0 n);
sub (Bit0 m) (Bit0 n) = dup (sub m n);
sub (Bit1 m) (Bit1 n) = dup (sub m n);
sub (Bit1 m) (Bit0 n) = plus_int (dup (sub m n)) one_int;
sub (Bit0 m) (Bit1 n) = minus_int (dup (sub m n)) one_int;

plus_int :: Int -> Int -> Int;
plus_int k Zero_int = k;
plus_int Zero_int l = l;
plus_int (Pos m) (Pos n) = Pos (plus_num m n);
plus_int (Pos m) (Neg n) = sub m n;
plus_int (Neg m) (Pos n) = sub n m;
plus_int (Neg m) (Neg n) = Neg (plus_num m n);

minus_int :: Int -> Int -> Int;
minus_int k Zero_int = k;
minus_int Zero_int l = uminus_int l;
minus_int (Pos m) (Pos n) = sub m n;
minus_int (Pos m) (Neg n) = Pos (plus_num m n);
minus_int (Neg m) (Pos n) = Neg (plus_num m n);
minus_int (Neg m) (Neg n) = sub n m;

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f [] s = s;
fold f (x : xs) s = fold f xs (f x s);

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

removeAll :: forall a. (Eq a) => a -> [a] -> [a];
removeAll x [] = [];
removeAll x (y : xs) = (if x == y then removeAll x xs else y : removeAll x xs);

membera :: forall a. (Eq a) => [a] -> a -> Bool;
membera [] y = False;
membera (x : xs) y = x == y || membera xs y;

inserta :: forall a. (Eq a) => a -> [a] -> [a];
inserta x xs = (if membera xs x then xs else x : xs);

insert :: forall a. (Eq a) => a -> Set a -> Set a;
insert x (Set xs) = Set (inserta x xs);
insert x (Coset xs) = Coset (removeAll x xs);

member :: forall a. (Eq a) => a -> Set a -> Bool;
member x (Set xs) = membera xs x;
member x (Coset xs) = not (membera xs x);

remove :: forall a. (Eq a) => a -> Set a -> Set a;
remove x (Set xs) = Set (removeAll x xs);
remove x (Coset xs) = Coset (inserta x xs);

update :: forall a b. (Eq a) => a -> b -> [(a, b)] -> [(a, b)];
update k v [] = [(k, v)];
update k v (p : ps) = (if fst p == k then (k, v) : ps else p : update k v ps);

merge :: forall a b. (Eq a) => [(a, b)] -> [(a, b)] -> [(a, b)];
merge qs ps = foldr (\ (a, b) -> update a b) ps qs;

fset :: forall a. Fset a -> Set a;
fset (Abs_fset x) = x;

fimage :: forall b a. (b -> a) -> Fset b -> Fset a;
fimage xb xc = Abs_fset (image xb (fset xc));

fun_upd :: forall a b. (Eq a) => (a -> b) -> a -> b -> a -> b;
fun_upd f a b = (\ x -> (if x == a then b else f x));

bind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b;
bind Nothing f = Nothing;
bind (Just x) f = f x;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

plus_nat :: Nat -> Nat -> Nat;
plus_nat Zero_nat n = n;
plus_nat (Suc m) n = plus_nat m (Suc n);

one_nat :: Nat;
one_nat = Suc Zero_nat;

nat_of_num :: Num -> Nat;
nat_of_num One = one_nat;
nat_of_num (Bit0 n) = let {
                        m = nat_of_num n;
                      } in plus_nat m m;
nat_of_num (Bit1 n) = let {
                        m = nat_of_num n;
                      } in Suc (plus_nat m m);

map_filter :: forall a b. (a -> Maybe b) -> [a] -> [b];
map_filter f [] = [];
map_filter f (x : xs) = (case f x of {
                          Nothing -> map_filter f xs;
                          Just y -> y : map_filter f xs;
                        });

c :: forall a b c d. State_ext a b c d -> Set a;
c (State_ext c infl stabl sigma more) = c;

fmadd :: forall a b. (Eq a) => Fmap a b -> Fmap a b -> Fmap a b;
fmadd (Fmap_of_list m) (Fmap_of_list n) = Fmap_of_list (merge m n);

fset_of_list :: forall a. [a] -> Fset a;
fset_of_list xa = Abs_fset (Set xa);

fmdom :: forall a b. Fmap a b -> Fset a;
fmdom (Fmap_of_list m) = fimage fst (fset_of_list m);

fmupd :: forall a b. (Eq a) => a -> b -> Fmap a b -> Fmap a b;
fmupd k v m = fmadd m (Fmap_of_list [(k, v)]);

calls ::
  forall a. Cfg_ext a -> Set (Cfg_node, (Call_action, (Cfg_node, Cfg_node)));
calls (Cfg_ext intra calls cfg_entry checks more) = calls;

intra :: forall a. Cfg_ext a -> Set (Cfg_node, (Edge_action, Cfg_node));
intra (Cfg_ext intra calls cfg_entry checks more) = intra;

fmfilter :: forall a b. (a -> Bool) -> Fmap a b -> Fmap a b;
fmfilter p (Fmap_of_list m) = Fmap_of_list (filter (\ (k, _) -> p k) m);

fmdrop :: forall a b. (Eq a) => a -> Fmap a b -> Fmap a b;
fmdrop a = fmfilter (\ aa -> not (aa == a));

ret_var :: [Char];
ret_var =
  [Char True True False False False True False False,
    Char False True False False True True True False,
    Char True False True False False True True False,
    Char False False True False True True True False];

cfg_entry :: forall a. Cfg_ext a -> Cfg_node;
cfg_entry (Cfg_ext intra calls cfg_entry checks more) = cfg_entry;

cfg_exit :: Cfg_ext () -> Cfg_node;
cfg_exit g = (case cfg_entry g of {
               Statement a -> Statement a;
               FunctionEntry a -> FunctionResult a;
               FunctionResult a -> FunctionResult a;
             });

fmempty :: forall a b. Fmap a b;
fmempty = Fmap_of_list [];

infl :: forall a b c d. State_ext a b c d -> Fmap (Sum a b) [a];
infl (State_ext c infl stabl sigma more) = infl;

location_of :: ([Char] -> Bool) -> [Char] -> Location;
location_of gs x = (if gs x then Global_Location x else Local_Location x);

stabl :: forall a b c d. State_ext a b c d -> Set a;
stabl (State_ext c infl stabl sigma more) = stabl;

fmlookup :: forall a b. (Eq a) => Fmap a b -> a -> Maybe b;
fmlookup (Fmap_of_list m) = map_of m;

fmlookup_default :: forall a b. (Eq a) => Fmap a b -> b -> a -> b;
fmlookup_default m d x = (case fmlookup m x of {
                           Nothing -> d;
                           Just v -> v;
                         });

fminsert :: forall a b. (Eq a) => Fmap a [b] -> a -> b -> Fmap a [b];
fminsert infl x y = fmupd x (y : fmlookup_default infl [] x) infl;

abort_empty_set :: forall a. (Set a -> a) -> a;
abort_empty_set _ = error "List.abort_empty_set";

bot_set :: forall a. Set a;
bot_set = Set [];

loop_cfg :: Cfg_ext ();
loop_cfg =
  Cfg_ext
    (insert
      (FunctionEntry
         [Char True False True True False True True False,
           Char True False False False False True True False,
           Char True False False True False True True False,
           Char False True True True False True True False],
        (EA_Nop, Statement Zero_nat))
      (insert
        (Statement Zero_nat,
          (EA_Assign [Char False False False True True True True False]
             (N Zero_int),
            Statement one_nat))
        (insert
          (Statement one_nat,
            (EA_Assume
               (Less (V [Char False False False True True True True False])
                 (N (Pos (Bit0 (Bit0 (Bit1 (Bit0 One))))))),
              Statement (nat_of_num (Bit0 One))))
          (insert
            (Statement one_nat,
              (EA_AssumeNot
                 (Less (V [Char False False False True True True True False])
                   (N (Pos (Bit0 (Bit0 (Bit1 (Bit0 One))))))),
                Statement (nat_of_num (Bit1 One))))
            (insert
              (Statement (nat_of_num (Bit0 One)),
                (EA_Assign [Char False False False True True True True False]
                   (Plus (V [Char False False False True True True True False])
                     (N one_int)),
                  Statement one_nat))
              (insert
                (Statement (nat_of_num (Bit1 One)),
                  (EA_Ret Nothing
                     [Char True False True True False True True False,
                       Char True False False False False True True False,
                       Char True False False True False True True False,
                       Char False True True True False True True False],
                    FunctionResult
                      [Char True False True True False True True False,
                        Char True False False False False True True False,
                        Char True False False True False True True False,
                        Char False True True True False True True False]))
                bot_set))))))
    bot_set
    (FunctionEntry
      [Char True False True True False True True False,
        Char True False False False False True True False,
        Char True False False True False True True False,
        Char False True True True False True True False])
    bot_set ();

cinit_ivl_st :: Resolved_st_q Ivl;
cinit_ivl_st =
  Abs_resolved_st (Ivl MinInf PlusInf, (Ivl (Fin Zero_int) (Fin Zero_int), []));

sup_fin :: forall a. (Semilattice_sup a) => Set a -> a;
sup_fin (Set []) = abort_empty_set sup_fin;
sup_fin (Set (x : xs)) = fold sup xs x;

sup_fset :: forall a. (Semilattice_sup a) => Fset a -> a;
sup_fset s = sup_fin (fset s);

make :: [([Char], Proc_decl_ext ())] -> Com -> [[Char]] -> Imp_prog_ext ();
make proc_rep prog_main declared_global_vars =
  Imp_prog_ext proc_rep prog_main declared_global_vars ();

loop_prog :: Imp_prog_ext ();
loop_prog =
  make []
    (Seq (Assign [Char False False False True True True True False]
           (N Zero_int))
      (While
        (Less (V [Char False False False True True True True False])
          (N (Pos (Bit0 (Bit0 (Bit1 (Bit0 One)))))))
        (Assign [Char False False False True True True True False]
          (Plus (V [Char False False False True True True True False])
            (N one_int)))))
    [];

location_is_global :: Location -> Bool;
location_is_global (Local_Location x) = False;
location_is_global (Global_Location x) = True;

restrict_global_resolved ::
  forall a. (Bot a) => (a, (a, [(Location, a)])) -> (a, (a, [(Location, a)]));
restrict_global_resolved s =
  (case s of {
    (_, (dg, ps)) -> (bot, (dg, filter (\ p -> location_is_global (fst p)) ps));
  });

restrict_global_resolved_q ::
  forall a. (Bot a) => Resolved_st_q a -> Resolved_st_q a;
restrict_global_resolved_q (Abs_resolved_st x) =
  Abs_resolved_st (restrict_global_resolved x);

loop_sig0 :: Sum Cfg_node () -> Resolved_st_q Ivl;
loop_sig0 k = (case k of {
                Inl _ -> bot_resolved_st_q;
                Inr () -> restrict_global_resolved_q cinit_ivl_st;
              });

lookup_resolved_st_q :: forall a. (Bot a) => Resolved_st_q a -> Location -> a;
lookup_resolved_st_q (Abs_resolved_st x) = lookup_resolved_st x;

fun_of_resolved_st_q_for ::
  forall a. (Bot a) => ([Char] -> Bool) -> Resolved_st_q a -> [Char] -> a;
fun_of_resolved_st_q_for gs s x = lookup_resolved_st_q s (location_of gs x);

inv_conservative :: forall a. a -> a -> a -> (a, a);
inv_conservative r a1 a2 = (a1, a2);

remove_resolved_key :: forall a. Location -> [(Location, a)] -> [(Location, a)];
remove_resolved_key loc [] = [];
remove_resolved_key loca ((loc, a) : ps) =
  (if equal_location loca loc then remove_resolved_key loca ps
    else (loc, a) : remove_resolved_key loca ps);

update_resolved_st ::
  forall a.
    (Bot a) => (a, (a, [(Location, a)])) ->
                 Location -> a -> (a, (a, [(Location, a)]));
update_resolved_st (dl, (dg, ps)) loc a =
  (dl, (dg, (loc, a) : remove_resolved_key loc ps));

update_resolved_st_q ::
  forall a. (Bot a) => Resolved_st_q a -> Location -> a -> Resolved_st_q a;
update_resolved_st_q (Abs_resolved_st xb) xa x =
  Abs_resolved_st (update_resolved_st xb xa x);

times_num :: Num -> Num -> Num;
times_num m One = m;
times_num One n = n;
times_num (Bit0 m) (Bit0 n) = Bit0 (Bit0 (times_num m n));
times_num (Bit0 m) (Bit1 n) = Bit0 (times_num m (Bit1 n));
times_num (Bit1 m) (Bit0 n) = Bit0 (times_num (Bit1 m) n);
times_num (Bit1 m) (Bit1 n) =
  Bit1 (plus_num (plus_num m n) (Bit0 (times_num m n)));

times_int :: Int -> Int -> Int;
times_int k Zero_int = Zero_int;
times_int Zero_int l = Zero_int;
times_int (Pos m) (Pos n) = Pos (times_num m n);
times_int (Pos m) (Neg n) = Neg (times_num m n);
times_int (Neg m) (Pos n) = Neg (times_num m n);
times_int (Neg m) (Neg n) = Pos (times_num m n);

ivl_top :: Ivl;
ivl_top = Ivl MinInf PlusInf;

min :: forall a. (Ord a) => a -> a -> a;
min a b = (if less_eq a b then a else b);

max :: forall a. (Ord a) => a -> a -> a;
max a b = (if less_eq a b then b else a);

ivl_times_core :: Ivl -> Ivl -> Ivl;
ivl_times_core (Ivl (Fin l1) (Fin u1)) (Ivl (Fin l2) (Fin u2)) =
  Ivl (Fin (min (times_int l1 l2)
             (min (times_int l1 u2) (min (times_int u1 l2) (times_int u1 u2)))))
    (Fin (max (times_int l1 l2)
           (max (times_int l1 u2) (max (times_int u1 l2) (times_int u1 u2)))));
ivl_times_core (Ivl MinInf va) uv = ivl_top;
ivl_times_core (Ivl PlusInf va) uv = ivl_top;
ivl_times_core (Ivl v MinInf) uv = ivl_top;
ivl_times_core (Ivl v PlusInf) uv = ivl_top;
ivl_times_core uu (Ivl MinInf va) = ivl_top;
ivl_times_core uu (Ivl PlusInf va) = ivl_top;
ivl_times_core uu (Ivl v MinInf) = ivl_top;
ivl_times_core uu (Ivl v PlusInf) = ivl_top;

ivl_nonempty :: Ivl -> Bool;
ivl_nonempty (Ivl l u) =
  less_eq_eint l u && not (equal_eint l PlusInf) && not (equal_eint u MinInf);

times_ivl :: Ivl -> Ivl -> Ivl;
times_ivl a b =
  (if ivl_nonempty a && ivl_nonempty b then ivl_times_core a b else bot_ivl);

minus_eint :: Eint -> Eint -> Eint;
minus_eint (Fin n) (Fin m) = Fin (minus_int n m);
minus_eint (Fin uu) MinInf = PlusInf;
minus_eint (Fin uv) PlusInf = MinInf;
minus_eint MinInf MinInf = MinInf;
minus_eint MinInf (Fin uw) = MinInf;
minus_eint MinInf PlusInf = MinInf;
minus_eint PlusInf MinInf = PlusInf;
minus_eint PlusInf (Fin ux) = PlusInf;
minus_eint PlusInf PlusInf = PlusInf;

normalize_ivl :: Ivl -> Ivl;
normalize_ivl v =
  (case v of {
    Ivl l u ->
      (if less_eq_eint l u &&
            not (equal_eint l PlusInf) && not (equal_eint u MinInf)
        then v else bot_ivl);
  });

minus_ivl :: Ivl -> Ivl -> Ivl;
minus_ivl (Ivl l1 u1) (Ivl l2 u2) =
  (case (normalize_ivl (Ivl l1 u1), normalize_ivl (Ivl l2 u2)) of {
    (Ivl a b, Ivl c d) -> normalize_ivl (Ivl (minus_eint a d) (minus_eint b c));
  });

plus_eint :: Eint -> Eint -> Eint;
plus_eint (Fin n) (Fin m) = Fin (plus_int n m);
plus_eint (Fin uu) MinInf = MinInf;
plus_eint (Fin uv) PlusInf = PlusInf;
plus_eint MinInf MinInf = MinInf;
plus_eint MinInf (Fin uw) = MinInf;
plus_eint MinInf PlusInf = MinInf;
plus_eint PlusInf MinInf = PlusInf;
plus_eint PlusInf (Fin ux) = PlusInf;
plus_eint PlusInf PlusInf = PlusInf;

plus_ivl :: Ivl -> Ivl -> Ivl;
plus_ivl (Ivl l1 u1) (Ivl l2 u2) =
  (case (normalize_ivl (Ivl l1 u1), normalize_ivl (Ivl l2 u2)) of {
    (Ivl a b, Ivl c d) -> normalize_ivl (Ivl (plus_eint a c) (plus_eint b d));
  });

aval_ivl :: Aexp -> ([Char] -> Ivl) -> Ivl;
aval_ivl (N n) sigma = Ivl (Fin n) (Fin n);
aval_ivl (V x) sigma = sigma x;
aval_ivl (Plus a b) sigma = plus_ivl (aval_ivl a sigma) (aval_ivl b sigma);
aval_ivl (Minus a b) sigma = minus_ivl (aval_ivl a sigma) (aval_ivl b sigma);
aval_ivl (Times a b) sigma = times_ivl (aval_ivl a sigma) (aval_ivl b sigma);

meet_ivl :: Ivl -> Ivl -> Ivl;
meet_ivl (Ivl l1 u1) (Ivl l2 u2) =
  Ivl (if less_eq_eint l2 l1 then l1 else l2)
    (if less_eq_eint u1 u2 then u1 else u2);

afilter_ivl_st ::
  ([Char] -> Bool) -> Aexp -> Ivl -> Resolved_st_q Ivl -> Resolved_st_q Ivl;
afilter_ivl_st gs (V x) a s =
  update_resolved_st_q s (location_of gs x)
    (meet_ivl a (fun_of_resolved_st_q_for gs s x));
afilter_ivl_st gs (Plus e1 e2) a s =
  (case inv_conservative a (aval_ivl e1 (fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
afilter_ivl_st gs (Minus e1 e2) a s =
  (case inv_conservative a (aval_ivl e1 (fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
afilter_ivl_st gs (Times e1 e2) a s =
  (case inv_conservative a (aval_ivl e1 (fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
afilter_ivl_st gs (N v) a s = s;

inf_ivl :: Ivl -> Ivl -> Ivl;
inf_ivl = meet_ivl;

inv_less_ivl :: Bool -> Ivl -> Ivl -> (Ivl, Ivl);
inv_less_ivl True (Ivl l1 u1) (Ivl l2 u2) =
  (inf_ivl (Ivl l1 u1) (Ivl MinInf (minus_eint u2 (Fin one_int))),
    inf_ivl (Ivl l2 u2) (Ivl (plus_eint l1 (Fin one_int)) PlusInf));
inv_less_ivl False (Ivl l1 u1) (Ivl l2 u2) =
  (inf_ivl (Ivl l1 u1) (Ivl l2 PlusInf), inf_ivl (Ivl l2 u2) (Ivl MinInf u1));

inv_eq_ivl :: Bool -> Ivl -> Ivl -> (Ivl, Ivl);
inv_eq_ivl True a1 a2 = (meet_ivl a1 a2, meet_ivl a1 a2);
inv_eq_ivl False a1 a2 = (a1, a2);

bfilter_ivl_st ::
  ([Char] -> Bool) -> Bexp -> Bool -> Resolved_st_q Ivl -> Resolved_st_q Ivl;
bfilter_ivl_st gs (Less e1 e2) res s =
  (case inv_less_ivl res (aval_ivl e1 (fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
bfilter_ivl_st gs (Not b) res s = bfilter_ivl_st gs b (not res) s;
bfilter_ivl_st gs (And b1 b2) True s =
  bfilter_ivl_st gs b1 True (bfilter_ivl_st gs b2 True s);
bfilter_ivl_st gs (And b1 b2) False s =
  sup_resolved_st_q (bfilter_ivl_st gs b1 False s)
    (bfilter_ivl_st gs b2 False s);
bfilter_ivl_st gs (Or b1 b2) True s =
  sup_resolved_st_q (bfilter_ivl_st gs b1 True s) (bfilter_ivl_st gs b2 True s);
bfilter_ivl_st gs (Or b1 b2) False s =
  bfilter_ivl_st gs b1 False (bfilter_ivl_st gs b2 False s);
bfilter_ivl_st gs (Eqb e1 e2) res s =
  (case inv_eq_ivl res (aval_ivl e1 (fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
bfilter_ivl_st gs (Bc v) uv s = s;

assume_not_ivl_st_for ::
  ([Char] -> Bool) -> Bexp -> Resolved_st_q Ivl -> Resolved_st_q Ivl;
assume_not_ivl_st_for source_global b s =
  bfilter_ivl_st source_global b False s;

assume_ivl_st_for ::
  ([Char] -> Bool) -> Bexp -> Resolved_st_q Ivl -> Resolved_st_q Ivl;
assume_ivl_st_for source_global b s = bfilter_ivl_st source_global b True s;

ivl_tf_st_for ::
  ([Char] -> Bool) -> Edge_action -> Resolved_st_q Ivl -> Resolved_st_q Ivl;
ivl_tf_st_for source_global EA_Nop s = s;
ivl_tf_st_for source_global (EA_Assign x a) s =
  update_resolved_st_q s (location_of source_global x)
    (aval_ivl a (fun_of_resolved_st_q_for source_global s));
ivl_tf_st_for source_global (EA_Random x) s =
  update_resolved_st_q s (location_of source_global x) ivl_top;
ivl_tf_st_for source_global (EA_Assume b) s =
  assume_ivl_st_for source_global b s;
ivl_tf_st_for source_global (EA_AssumeNot b) s =
  assume_not_ivl_st_for source_global b s;
ivl_tf_st_for source_global (EA_Ret Nothing p) s = s;
ivl_tf_st_for source_global (EA_Ret (Just a) p) s =
  update_resolved_st_q s (location_of source_global ret_var)
    (aval_ivl a (fun_of_resolved_st_q_for source_global s));
ivl_tf_st_for source_global (EA_Check cnd) s = s;

sigma :: forall a b c d. State_ext a b c d -> Sum a b -> c;
sigma (State_ext c infl stabl sigma more) = sigma;

c_update ::
  forall a b c d. (Set a -> Set a) -> State_ext a b c d -> State_ext a b c d;
c_update ca (State_ext c infl stabl sigma more) =
  State_ext (ca c) infl stabl sigma more;

combine_assign_resolved ::
  forall a.
    (Bot a) => ([Char] -> Bool) ->
                 Maybe [Char] ->
                   a -> (a, (a, [(Location, a)])) -> (a, (a, [(Location, a)]));
combine_assign_resolved gs dst v s =
  (case dst of {
    Nothing -> s;
    Just x -> update_resolved_st s (location_of gs x) v;
  });

location_is_local :: Location -> Bool;
location_is_local (Local_Location x) = True;
location_is_local (Global_Location x) = False;

combine_resolved_st ::
  forall a.
    (Bot a) => (a, (a, [(Location, a)])) ->
                 (a, (a, [(Location, a)])) -> (a, (a, [(Location, a)]));
combine_resolved_st sc se =
  (case sc of {
    (dlc, (_, psc)) ->
      (case se of {
        (_, (dge, pse)) ->
          (dlc, (dge, filter (\ p -> location_is_local (fst p)) psc ++
                        filter (\ p -> location_is_global (fst p)) pse));
      });
  });

combine_collect_resolved_for ::
  forall a.
    (Bot a) => ([Char] -> Bool) ->
                 Maybe [Char] ->
                   (a, (a, [(Location, a)])) ->
                     (a, (a, [(Location, a)])) -> (a, (a, [(Location, a)]));
combine_collect_resolved_for gs dst sc se =
  combine_assign_resolved gs dst
    (lookup_resolved_st se (location_of gs ret_var))
    (combine_resolved_st sc se);

combine_collect_resolved_for_q ::
  forall a.
    (Bot a) => ([Char] -> Bool) ->
                 Maybe [Char] ->
                   Resolved_st_q a -> Resolved_st_q a -> Resolved_st_q a;
combine_collect_resolved_for_q xc xb (Abs_resolved_st xa) (Abs_resolved_st x) =
  Abs_resolved_st (combine_collect_resolved_for xc xb xa x);

restrict_local_resolved ::
  forall a. (Bot a) => (a, (a, [(Location, a)])) -> (a, (a, [(Location, a)]));
restrict_local_resolved s =
  (case s of {
    (dl, (_, ps)) -> (dl, (bot, filter (\ p -> location_is_local (fst p)) ps));
  });

restrict_local_resolved_q ::
  forall a. (Bot a) => Resolved_st_q a -> Resolved_st_q a;
restrict_local_resolved_q (Abs_resolved_st x) =
  Abs_resolved_st (restrict_local_resolved x);

unit_combine_tree_st ::
  forall a.
    (Bounded_semilattice_sup_bot a) => ([Char] -> Bool) ->
 Maybe [Char] ->
   Cfg_node -> Cfg_node -> Strategy_tree Cfg_node () (Resolved_st_q a);
unit_combine_tree_st gs dst cc ex =
  QueryL cc
    (\ sc ->
      QueryL ex
        (\ se ->
          QueryG ()
            (\ g ->
              let {
                res = combine_collect_resolved_for_q gs dst
                        (sup_resolved_st_q sc g) (sup_resolved_st_q se g);
              } in Side () (restrict_global_resolved_q res)
                     (Answer (restrict_local_resolved_q res)))));

unit_edge_tree_st ::
  forall a.
    (Bounded_semilattice_sup_bot a) => (Resolved_st_q a -> Resolved_st_q a) ->
 Cfg_node -> Strategy_tree Cfg_node () (Resolved_st_q a);
unit_edge_tree_st f u =
  QueryL u
    (\ su ->
      QueryG ()
        (\ g ->
          let {
            res = f (sup_resolved_st_q su g);
          } in Side () (restrict_global_resolved_q res)
                 (Answer (restrict_local_resolved_q res))));

unit_etf_st_of_transfer ::
  forall a.
    (Bounded_semilattice_sup_bot a) => ([Char] -> Bool) ->
 (Edge_action -> Resolved_st_q a -> Resolved_st_q a) ->
   ([[Char]] -> [Aexp] -> Resolved_st_q a -> Resolved_st_q a) ->
     Effectful_st_transfer_ext () (Resolved_st_q a) ();
unit_etf_st_of_transfer gs tf_st enter_st =
  Effectful_st_transfer_ext (unit_edge_tree_st (tf_st EA_Nop))
    (\ x e -> unit_edge_tree_st (tf_st (EA_Assign x e)))
    (\ x -> unit_edge_tree_st (tf_st (EA_Random x)))
    (\ b -> unit_edge_tree_st (tf_st (EA_Assume b)))
    (\ b -> unit_edge_tree_st (tf_st (EA_AssumeNot b)))
    (\ xs es -> unit_edge_tree_st (enter_st xs es)) (unit_combine_tree_st gs)
    ();

enter_frame_D_resolved ::
  forall a.
    (Bot a) => a -> (a, (a, [(Location, a)])) -> (a, (a, [(Location, a)]));
enter_frame_D_resolved top_val s =
  (case s of {
    (_, (dg, ps)) ->
      (top_val, (dg, filter (\ p -> location_is_global (fst p)) ps));
  });

enter_frame_D_resolved_q ::
  forall a. (Bot a) => a -> Resolved_st_q a -> Resolved_st_q a;
enter_frame_D_resolved_q xa (Abs_resolved_st x) =
  Abs_resolved_st (enter_frame_D_resolved xa x);

bind_formals_resolved ::
  forall a.
    (Bot a) => ([Char] -> Bool) ->
                 [[Char]] ->
                   [a] ->
                     (a, (a, [(Location, a)])) -> (a, (a, [(Location, a)]));
bind_formals_resolved gs xs avs s =
  fold (\ (x, a) t -> update_resolved_st t (location_of gs x) a) (zip xs avs) s;

bind_formals_resolved_q ::
  forall a.
    (Bot a) => ([Char] -> Bool) ->
                 [[Char]] -> [a] -> Resolved_st_q a -> Resolved_st_q a;
bind_formals_resolved_q xc xb xa (Abs_resolved_st x) =
  Abs_resolved_st (bind_formals_resolved xc xb xa x);

ivl_enter_st_for ::
  ([Char] -> Bool) ->
    [[Char]] -> [Aexp] -> Resolved_st_q Ivl -> Resolved_st_q Ivl;
ivl_enter_st_for source_global xs es s =
  bind_formals_resolved_q source_global xs
    (map (\ e -> aval_ivl e (fun_of_resolved_st_q_for source_global s)) es)
    (enter_frame_D_resolved_q ivl_top s);

ivl_etf_st_for ::
  ([Char] -> Bool) -> Effectful_st_transfer_ext () (Resolved_st_q Ivl) ();
ivl_etf_st_for gs =
  unit_etf_st_of_transfer gs (ivl_tf_st_for gs) (ivl_enter_st_for gs);

traverse_rhs ::
  forall a b c. (Bot c) => Strategy_tree a b c -> (Sum a b -> c) -> c;
traverse_rhs (Answer d) uu = d;
traverse_rhs (QueryL x f) sigma = traverse_rhs (f (sigma (Inl x))) sigma;
traverse_rhs (QueryG x f) sigma = traverse_rhs (f (sigma (Inr x))) sigma;
traverse_rhs (Side x d t) sigma = traverse_rhs t sigma;

etf_st_assume_not ::
  forall a b c.
    Effectful_st_transfer_ext a b c ->
      Bexp -> Cfg_node -> Strategy_tree Cfg_node a b;
etf_st_assume_not
  (Effectful_st_transfer_ext etf_st_nop etf_st_assign etf_st_random
    etf_st_assume etf_st_assume_not etf_st_enter etf_st_combine more)
  = etf_st_assume_not;

etf_st_random ::
  forall a b c.
    Effectful_st_transfer_ext a b c ->
      [Char] -> Cfg_node -> Strategy_tree Cfg_node a b;
etf_st_random
  (Effectful_st_transfer_ext etf_st_nop etf_st_assign etf_st_random
    etf_st_assume etf_st_assume_not etf_st_enter etf_st_combine more)
  = etf_st_random;

etf_st_assume ::
  forall a b c.
    Effectful_st_transfer_ext a b c ->
      Bexp -> Cfg_node -> Strategy_tree Cfg_node a b;
etf_st_assume
  (Effectful_st_transfer_ext etf_st_nop etf_st_assign etf_st_random
    etf_st_assume etf_st_assume_not etf_st_enter etf_st_combine more)
  = etf_st_assume;

etf_st_assign ::
  forall a b c.
    Effectful_st_transfer_ext a b c ->
      [Char] -> Aexp -> Cfg_node -> Strategy_tree Cfg_node a b;
etf_st_assign
  (Effectful_st_transfer_ext etf_st_nop etf_st_assign etf_st_random
    etf_st_assume etf_st_assume_not etf_st_enter etf_st_combine more)
  = etf_st_assign;

etf_st_nop ::
  forall a b c.
    Effectful_st_transfer_ext a b c -> Cfg_node -> Strategy_tree Cfg_node a b;
etf_st_nop
  (Effectful_st_transfer_ext etf_st_nop etf_st_assign etf_st_random
    etf_st_assume etf_st_assume_not etf_st_enter etf_st_combine more)
  = etf_st_nop;

apply_etf_st ::
  forall a b.
    Effectful_st_transfer_ext a b () ->
      Edge_action -> Cfg_node -> Strategy_tree Cfg_node a b;
apply_etf_st etf EA_Nop u = etf_st_nop etf u;
apply_etf_st etf (EA_Assign x a) u = etf_st_assign etf x a u;
apply_etf_st etf (EA_Random x) u = etf_st_random etf x u;
apply_etf_st etf (EA_Assume b) u = etf_st_assume etf b u;
apply_etf_st etf (EA_AssumeNot b) u = etf_st_assume_not etf b u;
apply_etf_st etf (EA_Ret e p) u = (case e of {
                                    Nothing -> etf_st_nop etf u;
                                    Just a -> etf_st_assign etf ret_var a u;
                                  });
apply_etf_st etf (EA_Check cnd) u = etf_st_nop etf u;

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Set xs) a = fold insert xs a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);

declared_global_vars :: forall a. Imp_prog_ext a -> [[Char]];
declared_global_vars (Imp_prog_ext proc_rep prog_main declared_global_vars more)
  = declared_global_vars;

declared_global :: Imp_prog_ext () -> [Char] -> Bool;
declared_global p x = membera (declared_global_vars p) x;

insort_key :: forall a b. (Linorder b) => (a -> b) -> a -> [a] -> [a];
insort_key f x [] = [x];
insort_key f x (y : ys) =
  (if less_eq (f x) (f y) then x : y : ys else y : insort_key f x ys);

sort_key :: forall a b. (Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs = foldr (insort_key f) xs [];

sorted_list_of_set :: forall a. (Eq a, Linorder a) => Set a -> [a];
sorted_list_of_set (Set xs) = sort_key (\ x -> x) (remdups xs);

cfg_intra_list :: Cfg_ext () -> [(Cfg_node, (Edge_action, Cfg_node))];
cfg_intra_list g = sorted_list_of_set (intra g);

intra_predecessor_list :: Cfg_ext () -> Cfg_node -> [(Cfg_node, Edge_action)];
intra_predecessor_list g v =
  map_filter
    (\ x ->
      (if (case x of {
            (_, (_, w)) -> equal_cfg_node w v;
          })
        then Just (case x of {
                    (u, (a, _)) -> (u, a);
                  })
        else Nothing))
    (cfg_intra_list g);

etf_st_enter ::
  forall a b c.
    Effectful_st_transfer_ext a b c ->
      [[Char]] -> [Aexp] -> Cfg_node -> Strategy_tree Cfg_node a b;
etf_st_enter
  (Effectful_st_transfer_ext etf_st_nop etf_st_assign etf_st_random
    etf_st_assume etf_st_assume_not etf_st_enter etf_st_combine more)
  = etf_st_enter;

etf_st_combine ::
  forall a b c.
    Effectful_st_transfer_ext a b c ->
      Maybe [Char] -> Cfg_node -> Cfg_node -> Strategy_tree Cfg_node a b;
etf_st_combine
  (Effectful_st_transfer_ext etf_st_nop etf_st_assign etf_st_random
    etf_st_assume etf_st_assume_not etf_st_enter etf_st_combine more)
  = etf_st_combine;

etf_combine_st ::
  forall a b.
    Effectful_st_transfer_ext a b () ->
      Maybe [Char] -> Cfg_node -> Cfg_node -> Strategy_tree Cfg_node a b;
etf_combine_st etf dst cc ex = etf_st_combine etf dst cc ex;

side_contribution_trees_st ::
  forall a b.
    (Bounded_semilattice_sup_bot b) => Effectful_st_transfer_ext a
 (Resolved_st_q b) () ->
 [(Cfg_node, Edge_action)] ->
   [(Cfg_node, ([[Char]], [Aexp]))] ->
     [(Cfg_node, (Maybe [Char], Cfg_node))] ->
       [Strategy_tree Cfg_node a (Resolved_st_q b)];
side_contribution_trees_st etf es ens cs =
  map (\ (u, a) -> apply_etf_st etf a u) es ++
    map (\ (cl, (fs, asa)) -> etf_st_enter etf fs asa cl) ens ++
      map (\ (cc, (dst, a)) -> etf_combine_st etf dst cc a) cs;

seqcomp_tree ::
  forall a b c.
    Strategy_tree a b c -> (c -> Strategy_tree a b c) -> Strategy_tree a b c;
seqcomp_tree (Answer v) k = k v;
seqcomp_tree (QueryL u f) k = QueryL u (\ d -> seqcomp_tree (f d) k);
seqcomp_tree (QueryG g f) k = QueryG g (\ d -> seqcomp_tree (f d) k);
seqcomp_tree (Side g v t) k = Side g v (seqcomp_tree t k);

fold_rhs_trees ::
  forall a b c.
    (Bounded_semilattice_sup_bot a) => a ->
 [Strategy_tree b c a] -> Strategy_tree b c a;
fold_rhs_trees acc [] = Answer acc;
fold_rhs_trees acc (t : ts) =
  seqcomp_tree t (\ res -> fold_rhs_trees (sup acc res) ts);

side_rhs_fold_eff_st ::
  forall a b.
    (Bounded_semilattice_sup_bot b) => Effectful_st_transfer_ext a
 (Resolved_st_q b) () ->
 Resolved_st_q b ->
   [(Cfg_node, Edge_action)] ->
     [(Cfg_node, ([[Char]], [Aexp]))] ->
       [(Cfg_node, (Maybe [Char], Cfg_node))] ->
         Strategy_tree Cfg_node a (Resolved_st_q b);
side_rhs_fold_eff_st etf acc es ens cs =
  fold_rhs_trees acc (side_contribution_trees_st etf es ens cs);

cfg_calls_list ::
  Cfg_ext () -> [(Cfg_node, (Call_action, (Cfg_node, Cfg_node)))];
cfg_calls_list g = sorted_list_of_set (calls g);

return_call_list ::
  Cfg_ext () -> Cfg_node -> [(Cfg_node, (Maybe [Char], Cfg_node))];
return_call_list g v =
  map_filter
    (\ x ->
      (if (case x of {
            (_, (_, (ce, k))) ->
              equal_cfg_node k v && (case ce of {
                                      Statement _ -> False;
                                      FunctionEntry _ -> True;
                                      FunctionResult _ -> False;
                                    });
          })
        then Just (case x of {
                    (c, (ca, (ce, _))) ->
                      (c, ((case ca of {
                             CallEdge dst _ _ -> dst;
                           }),
                            (case ce of {
                              Statement _ -> ce;
                              FunctionEntry a -> FunctionResult a;
                              FunctionResult _ -> ce;
                            })));
                  })
        else Nothing))
    (cfg_calls_list g);

entry_call_list :: Cfg_ext () -> Cfg_node -> [(Cfg_node, Call_action)];
entry_call_list g v =
  map_filter
    (\ x ->
      (if (case x of {
            (_, (_, (ce, _))) -> equal_cfg_node ce v;
          })
        then Just (case x of {
                    (c, (ca, (_, _))) -> (c, ca);
                  })
        else Nothing))
    (cfg_calls_list g);

entry_seed_list :: Cfg_ext () -> Cfg_node -> [(Cfg_node, ([[Char]], [Aexp]))];
entry_seed_list g v =
  map (\ (c, CallEdge _ fs asa) -> (c, (fs, asa))) (entry_call_list g v);

make_side_rhs_tree_eff_st ::
  forall a b.
    (Bounded_semilattice_sup_bot b) => Cfg_ext () ->
 Effectful_st_transfer_ext a (Resolved_st_q b) () ->
   Resolved_st_q b ->
     Resolved_st_q b ->
       a -> Cfg_node -> Strategy_tree Cfg_node a (Resolved_st_q b);
make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed v =
  let {
    acc0 =
      (if equal_cfg_node v (cfg_entry g)
        then sup_resolved_st_q bot0_st (restrict_local_resolved_q s0_st)
        else bot0_st);
    t = side_rhs_fold_eff_st etf acc0 (intra_predecessor_list g v)
          (entry_seed_list g v) (return_call_list g v);
  } in (if equal_cfg_node v (cfg_entry g)
         then Side gseed (restrict_global_resolved_q s0_st) t else t);

side_cfg_T_eff_st ::
  forall a b.
    (Bounded_semilattice_sup_bot b) => Cfg_ext () ->
 Effectful_st_transfer_ext a (Resolved_st_q b) () ->
   Resolved_st_q b ->
     Resolved_st_q b ->
       a -> Cfg_node -> Strategy_tree Cfg_node a (Resolved_st_q b);
side_cfg_T_eff_st g etf bot0_st s0_st gseed =
  make_side_rhs_tree_eff_st g etf bot0_st s0_st gseed;

loop_ivl_eqs :: Cfg_node -> Strategy_tree Cfg_node () (Resolved_st_q Ivl);
loop_ivl_eqs =
  side_cfg_T_eff_st loop_cfg (ivl_etf_st_for (declared_global loop_prog))
    bot_resolved_st_q cinit_ivl_st ();

loop_kleene_step ::
  (Sum Cfg_node () -> Resolved_st_q Ivl) ->
    Sum Cfg_node () -> Resolved_st_q Ivl;
loop_kleene_step sig = (\ a -> (case a of {
                                 Inl v -> traverse_rhs (loop_ivl_eqs v) sig;
                                 Inr () -> sig (Inr ());
                               }));

loop_iter_sig ::
  Nat ->
    (Sum Cfg_node () -> Resolved_st_q Ivl) ->
      Sum Cfg_node () -> Resolved_st_q Ivl;
loop_iter_sig Zero_nat sig = sig;
loop_iter_sig (Suc n) sig = loop_iter_sig n (loop_kleene_step sig);

loop_ivl_sol :: (Set Cfg_node, Sum Cfg_node () -> Resolved_st_q Ivl);
loop_ivl_sol =
  (sup_set
     (insert
       (FunctionEntry
         [Char True False True True False True True False,
           Char True False False False False True True False,
           Char True False False True False True True False,
           Char False True True True False True True False])
       (insert
         (FunctionResult
           [Char True False True True False True True False,
             Char True False False False False True True False,
             Char True False False True False True True False,
             Char False True True True False True True False])
         bot_set))
     (image Statement
       (insert Zero_nat
         (insert one_nat
           (insert (nat_of_num (Bit0 One))
             (insert (nat_of_num (Bit1 One)) bot_set))))),
    loop_iter_sig (nat_of_num (Bit0 (Bit0 (Bit1 (Bit0 (Bit0 (Bit1 One)))))))
      loop_sig0);

infl_update ::
  forall a b c d.
    (Fmap (Sum a b) [a] -> Fmap (Sum a b) [a]) ->
      State_ext a b c d -> State_ext a b c d;
infl_update infla (State_ext c infl stabl sigma more) =
  State_ext c (infla infl) stabl sigma more;

stabl_update ::
  forall a b c d. (Set a -> Set a) -> State_ext a b c d -> State_ext a b c d;
stabl_update stabla (State_ext c infl stabl sigma more) =
  State_ext c infl (stabla stabl) sigma more;

warrow :: forall a. (Warrowing a) => a -> a -> a;
warrow a b = (if less_eq b a then narrow a b else widen a b);

rho_update ::
  forall a b c d.
    ((a -> Fmap b c) -> a -> Fmap b c) ->
      Ug_state_ext b a c d -> Ug_state_ext b a c d;
rho_update rhoa (Ug_state_ext rho more) = Ug_state_ext (rhoa rho) more;

rho :: forall a b c d. Ug_state_ext a b c d -> b -> Fmap a c;
rho (Ug_state_ext rho more) = rho;

sup_over_origins ::
  forall a b c d.
    (Eq a, Bounded_semilattice_sup_bot c) => Ug_state_ext a b c d -> b -> c;
sup_over_origins state g =
  sup_fset (fimage (fmlookup_default (rho state g) bot) (fmdom (rho state g)));

update_global_warrowing_apinis ::
  forall a b c.
    (Eq a, Bounded_semilattice_sup_bot a, Warrowing a, Eq b,
      Eq c) => a -> b -> c -> a -> Ug_state_ext b c a () ->
                                     (Maybe a, Ug_state_ext b c a ());
update_global_warrowing_apinis da orig g d state =
  (if fmlookup_default (rho state g) bot orig == d then (Nothing, state)
    else let {
           statea =
             rho_update
               (\ _ -> fun_upd (rho state) g (fmupd orig d (rho state g)))
               state;
           db = warrow da (sup_over_origins statea g);
         } in (Just db, statea));

point_update ::
  forall a b c d.
    (Set a -> Set a) ->
      State_ext a b c (State_exta a d) -> State_ext a b c (State_exta a d);
point_update pointa (State_ext c infl stabl sigma (State_exta point more)) =
  State_ext c infl stabl sigma (State_exta (pointa point) more);

destab_opt ::
  forall a b.
    (Eq a,
      Eq b) => Sum a b ->
                 Fmap (Sum a b) [a] ->
                   Set a -> Set a -> (Fmap (Sum a b) [a], Set a);
destab_opt x i s c = destab_iter_opt (fmlookup_default i [] x) (fmdrop x i) s c;

destab_iter_opt ::
  forall a b.
    (Eq a,
      Eq b) => [a] ->
                 Fmap (Sum a b) [a] ->
                   Set a -> Set a -> (Fmap (Sum a b) [a], Set a);
destab_iter_opt [] i s c = (i, s);
destab_iter_opt (y : ys) i s c =
  (case (if member y c then (i, remove y s)
          else destab_opt (Inl y) i (remove y s) c)
    of {
    (ia, sa) -> destab_iter_opt ys ia sa c;
  });

sigma_update ::
  forall a b c d.
    ((Sum a b -> c) -> Sum a b -> c) -> State_ext a b c d -> State_ext a b c d;
sigma_update sigmaa (State_ext c infl stabl sigma more) =
  State_ext c infl stabl (sigmaa sigma) more;

point :: forall a b c d. State_ext a b c (State_exta a d) -> Set a;
point (State_ext c infl stabl sigma (State_exta point more)) = point;

tD_side_warrowing_apinis_Interp_solve_rec_c ::
  forall a b c.
    (Eq a, Eq b, Eq c, Bounded_semilattice_sup_bot c,
      Warrowing c) => (a -> Strategy_tree a b c) ->
                        Func_state a b c () ->
                          Maybe (c, (State_ext a b c (State_exta a ()),
                                      Ug_state_ext a b c ()));
tD_side_warrowing_apinis_Interp_solve_rec_c t s =
  (case s of {
    Q (y, (x, (state, ug_state))) ->
      bind (if member x (c state)
             then Just (sigma state (Inl x),
                         (point_update (\ _ -> insert x (point state)) state,
                           ug_state))
             else tD_side_warrowing_apinis_Interp_solve_rec_c t
                    (I (x, (c_update (\ _ -> insert x (c state)) state,
                             ug_state))))
        (\ (xd, (statea, ug_statea)) ->
          Just (xd, (infl_update (\ _ -> fminsert (infl statea) (Inl x) y)
                       statea,
                      ug_statea)));
    I (x, (state, ug_state)) ->
      (if not (member x (stabl state))
        then bind (tD_side_warrowing_apinis_Interp_solve_rec_c t
                    (R (x, (state, ug_state))))
               (\ (d_new, (state1, ug_state1)) ->
                 let {
                   d_newa =
                     (if member x (point state)
                       then warrow (sigma state1 (Inl x)) d_new else d_new);
                 } in (if sigma state1 (Inl x) == d_newa
                        then Just (d_newa,
                                    (point_update
                                       (\ _ -> remove x (point state1))
                                       (c_update (\ _ -> remove x (c state1))
 state1),
                                      ug_state1))
                        else (case destab_opt (Inl x) (infl state1)
                                     (stabl state1) (c state1)
                               of {
                               (infl1, stabl1) ->
                                 tD_side_warrowing_apinis_Interp_solve_rec_c t
                                   (I (x,
(sigma_update (\ _ -> fun_upd (sigma state1) (Inl x) d_newa)
   (stabl_update (\ _ -> stabl1) (infl_update (\ _ -> infl1) state1)),
  ug_state1)));
                             })))
        else Just (sigma state (Inl x),
                    (point_update (\ _ -> remove x (point state))
                       (c_update (\ _ -> remove x (c state)) state),
                      ug_state)));
    R (x, (state, ug_state)) ->
      bind (tD_side_warrowing_apinis_Interp_solve_rec_c t
             (E (x, (t x, ((\ _ -> bot),
                            (stabl_update (\ _ -> insert x (stabl state)) state,
                              ug_state))))))
        (\ (xd, (statea, ug_statea)) ->
          (if member x (stabl statea) then Just (xd, (statea, ug_statea))
            else tD_side_warrowing_apinis_Interp_solve_rec_c t
                   (R (x, (statea, ug_statea)))));
    E (_, (Answer d, (_, (state, ug_state)))) -> Just (d, (state, ug_state));
    E (x, (QueryL y g, (sides_a_c_c, (state, ug_state)))) ->
      bind (tD_side_warrowing_apinis_Interp_solve_rec_c t
             (Q (x, (y, (state, ug_state)))))
        (\ (yd, (statea, ug_statea)) ->
          tD_side_warrowing_apinis_Interp_solve_rec_c t
            (E (x, (g yd, (sides_a_c_c, (statea, ug_statea))))));
    E (x, (QueryG y g, (sides_a_c_c, (state, ug_state)))) ->
      tD_side_warrowing_apinis_Interp_solve_rec_c t
        (E (x, (g (sigma state (Inr y)),
                 (sides_a_c_c,
                   (infl_update (\ _ -> fminsert (infl state) (Inr y) x) state,
                     ug_state)))));
    E (x, (Side y d ta, (sides_a_c_c, (state, ug_state)))) ->
      let {
        da = sup (sides_a_c_c y) d;
        sides_a_c_ca = fun_upd sides_a_c_c y da;
      } in (case update_global_warrowing_apinis (sigma state (Inr y)) x y da
                   ug_state
             of {
             (Nothing, ug_statea) ->
               tD_side_warrowing_apinis_Interp_solve_rec_c t
                 (E (x, (ta, (sides_a_c_ca, (state, ug_statea)))));
             (Just db, ug_statea) ->
               (case destab_opt (Inr y) (infl state) (stabl state) (c state) of
                 {
                 (infla, stabla) ->
                   tD_side_warrowing_apinis_Interp_solve_rec_c t
                     (E (x, (ta, (sides_a_c_ca,
                                   (sigma_update
                                      (\ _ -> fun_upd (sigma state) (Inr y) db)
                                      (stabl_update (\ _ -> stabla)
(infl_update (\ _ -> infla) state)),
                                     ug_statea)))));
               });
           });
  });

init_state ::
  forall a b c.
    (Bounded_semilattice_sup_bot c,
      Warrowing c) => State_ext a b c (State_exta a ());
init_state =
  State_ext bot_set fmempty bot_set (\ _ -> bot) (State_exta bot_set ());

init_basic_ug_state :: forall a b c. (Order_bot c) => Ug_state_ext a b c ();
init_basic_ug_state = Ug_state_ext (\ _ -> fmempty) ();

tD_side_warrowing_apinis_Interp_solve_c ::
  forall a b c.
    (Eq a, Eq b, Eq c, Bounded_semilattice_sup_bot c,
      Warrowing c) => (a -> Strategy_tree a b c) ->
                        a -> Maybe (Set a, Sum a b -> c);
tD_side_warrowing_apinis_Interp_solve_c t x =
  bind (tD_side_warrowing_apinis_Interp_solve_rec_c t
         (I (x, (c_update
                   (\ _ ->
                     insert x
                       (c (init_state :: State_ext a b c (State_exta a ()))))
                   init_state,
                  init_basic_ug_state))))
    (\ (_, (state, _)) -> Just (stabl state, sigma state));

tD_side_warrowing_apinis_Interp_solve ::
  forall a b c.
    (Eq a, Eq b, Eq c, Bounded_semilattice_sup_bot c,
      Warrowing c) => (a -> Strategy_tree a b c) -> a -> (Set a, Sum a b -> c);
tD_side_warrowing_apinis_Interp_solve t x =
  (case tD_side_warrowing_apinis_Interp_solve_c t x of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "Input not in domain"
        (\ _ -> tD_side_warrowing_apinis_Interp_solve t x);
    Just r -> r;
  });

loop_ivl_td_sol :: (Set Cfg_node, Sum Cfg_node () -> Resolved_st_q Ivl);
loop_ivl_td_sol =
  tD_side_warrowing_apinis_Interp_solve loop_ivl_eqs (cfg_exit loop_cfg);

}
