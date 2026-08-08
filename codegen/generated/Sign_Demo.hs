{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module
  Sign_Demo(Char, Sum, Cfg_node, Sign, Bexp, Dg_state, Resolved_st_q, Set,
             Cfg_ext, Strategy_tree, Check_result, Imp_prog_ext, dgEx_sol,
             analyse_sign_for, analyse_sign, analyse_sign_report)
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

data Sign = SBot | SNeg | SNonPos | SZero | SNonNeg | SPos | STop;

equal_sign :: Sign -> Sign -> Bool;
equal_sign SPos STop = False;
equal_sign STop SPos = False;
equal_sign SNonNeg STop = False;
equal_sign STop SNonNeg = False;
equal_sign SNonNeg SPos = False;
equal_sign SPos SNonNeg = False;
equal_sign SZero STop = False;
equal_sign STop SZero = False;
equal_sign SZero SPos = False;
equal_sign SPos SZero = False;
equal_sign SZero SNonNeg = False;
equal_sign SNonNeg SZero = False;
equal_sign SNonPos STop = False;
equal_sign STop SNonPos = False;
equal_sign SNonPos SPos = False;
equal_sign SPos SNonPos = False;
equal_sign SNonPos SNonNeg = False;
equal_sign SNonNeg SNonPos = False;
equal_sign SNonPos SZero = False;
equal_sign SZero SNonPos = False;
equal_sign SNeg STop = False;
equal_sign STop SNeg = False;
equal_sign SNeg SPos = False;
equal_sign SPos SNeg = False;
equal_sign SNeg SNonNeg = False;
equal_sign SNonNeg SNeg = False;
equal_sign SNeg SZero = False;
equal_sign SZero SNeg = False;
equal_sign SNeg SNonPos = False;
equal_sign SNonPos SNeg = False;
equal_sign SBot STop = False;
equal_sign STop SBot = False;
equal_sign SBot SPos = False;
equal_sign SPos SBot = False;
equal_sign SBot SNonNeg = False;
equal_sign SNonNeg SBot = False;
equal_sign SBot SZero = False;
equal_sign SZero SBot = False;
equal_sign SBot SNonPos = False;
equal_sign SNonPos SBot = False;
equal_sign SBot SNeg = False;
equal_sign SNeg SBot = False;
equal_sign STop STop = True;
equal_sign SPos SPos = True;
equal_sign SNonNeg SNonNeg = True;
equal_sign SZero SZero = True;
equal_sign SNonPos SNonPos = True;
equal_sign SNeg SNeg = True;
equal_sign SBot SBot = True;

instance Eq Sign where {
  a == b = equal_sign a b;
};

join_sign :: Sign -> Sign -> Sign;
join_sign SBot b = b;
join_sign SNeg SBot = SNeg;
join_sign SNonPos SBot = SNonPos;
join_sign SZero SBot = SZero;
join_sign SNonNeg SBot = SNonNeg;
join_sign SPos SBot = SPos;
join_sign STop SBot = STop;
join_sign STop SNeg = STop;
join_sign STop SNonPos = STop;
join_sign STop SZero = STop;
join_sign STop SNonNeg = STop;
join_sign STop SPos = STop;
join_sign STop STop = STop;
join_sign SNeg STop = STop;
join_sign SNonPos STop = STop;
join_sign SZero STop = STop;
join_sign SNonNeg STop = STop;
join_sign SPos STop = STop;
join_sign SNeg SNeg = SNeg;
join_sign SNeg SZero = SNonPos;
join_sign SNeg SNonPos = SNonPos;
join_sign SZero SNeg = SNonPos;
join_sign SZero SZero = SZero;
join_sign SZero SPos = SNonNeg;
join_sign SZero SNonPos = SNonPos;
join_sign SZero SNonNeg = SNonNeg;
join_sign SNonPos SNeg = SNonPos;
join_sign SNonPos SZero = SNonPos;
join_sign SNonPos SNonPos = SNonPos;
join_sign SNonNeg SZero = SNonNeg;
join_sign SNonNeg SPos = SNonNeg;
join_sign SNonNeg SNonNeg = SNonNeg;
join_sign SPos SZero = SNonNeg;
join_sign SPos SNonNeg = SNonNeg;
join_sign SPos SPos = SPos;
join_sign SNeg SNonNeg = STop;
join_sign SNeg SPos = STop;
join_sign SNonPos SNonNeg = STop;
join_sign SNonPos SPos = STop;
join_sign SNonNeg SNeg = STop;
join_sign SNonNeg SNonPos = STop;
join_sign SPos SNeg = STop;
join_sign SPos SNonPos = STop;

sup_sign :: Sign -> Sign -> Sign;
sup_sign = join_sign;

class Sup a where {
  sup :: a -> a -> a;
};

instance Sup Sign where {
  sup = sup_sign;
};

bot_sign :: Sign;
bot_sign = SBot;

class Bot a where {
  bot :: a;
};

instance Bot Sign where {
  bot = bot_sign;
};

sign_le :: Sign -> Sign -> Bool;
sign_le SBot uu = True;
sign_le SNeg STop = True;
sign_le SNonPos STop = True;
sign_le SZero STop = True;
sign_le SNonNeg STop = True;
sign_le SPos STop = True;
sign_le STop STop = True;
sign_le SNeg SNeg = True;
sign_le SNeg SNonPos = True;
sign_le SNonPos SNonPos = True;
sign_le SZero SZero = True;
sign_le SZero SNonPos = True;
sign_le SZero SNonNeg = True;
sign_le SNonNeg SNonNeg = True;
sign_le SPos SPos = True;
sign_le SPos SNonNeg = True;
sign_le SNeg SBot = False;
sign_le SNeg SZero = False;
sign_le SNeg SNonNeg = False;
sign_le SNeg SPos = False;
sign_le SNonPos SBot = False;
sign_le SNonPos SNeg = False;
sign_le SNonPos SZero = False;
sign_le SNonPos SNonNeg = False;
sign_le SNonPos SPos = False;
sign_le SZero SBot = False;
sign_le SZero SNeg = False;
sign_le SZero SPos = False;
sign_le SNonNeg SBot = False;
sign_le SNonNeg SNeg = False;
sign_le SNonNeg SNonPos = False;
sign_le SNonNeg SZero = False;
sign_le SNonNeg SPos = False;
sign_le SPos SBot = False;
sign_le SPos SNeg = False;
sign_le SPos SNonPos = False;
sign_le SPos SZero = False;
sign_le STop SBot = False;
sign_le STop SNeg = False;
sign_le STop SNonPos = False;
sign_le STop SZero = False;
sign_le STop SNonNeg = False;
sign_le STop SPos = False;

less_eq_sign :: Sign -> Sign -> Bool;
less_eq_sign a b = sign_le a b;

less_sign :: Sign -> Sign -> Bool;
less_sign a b = sign_le a b && not (sign_le b a);

instance Ord Sign where {
  less_eq = less_eq_sign;
  less = less_sign;
};

instance Preorder Sign where {
};

instance Order Sign where {
};

class (Bot a, Order a) => Order_bot a where {
};

instance Order_bot Sign where {
};

widen_sign :: Sign -> Sign -> Sign;
widen_sign a b = join_sign a b;

class (Order a) => Widening a where {
  widen :: a -> a -> a;
};

instance Widening Sign where {
  widen = widen_sign;
};

narrow_sign_td :: Sign -> Sign -> Sign;
narrow_sign_td a b = a;

narrow_sign :: Sign -> Sign -> Sign;
narrow_sign a b = narrow_sign_td a b;

class (Order a) => Narrowing a where {
  narrow :: a -> a -> a;
};

instance Narrowing Sign where {
  narrow = narrow_sign;
};

class (Narrowing a, Widening a) => Warrowing a where {
};

instance Warrowing Sign where {
};

class (Sup a, Order a) => Semilattice_sup a where {
};

instance Semilattice_sup Sign where {
};

class (Semilattice_sup a, Order_bot a) => Bounded_semilattice_sup_bot a where {
};

class (Bounded_semilattice_sup_bot a,
        Warrowing a) => Bounded_warrowing a where {
};

instance Bounded_semilattice_sup_bot Sign where {
};

instance Bounded_warrowing Sign where {
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

data Dg_state a b = DG a b;

equal_dg_state ::
  forall a b. (Eq a, Eq b) => Dg_state a b -> Dg_state a b -> Bool;
equal_dg_state (DG x1 x2) (DG y1 y2) = x1 == y1 && x2 == y2;

instance (Eq a, Eq b) => Eq (Dg_state a b) where {
  a == b = equal_dg_state a b;
};

locals :: forall a b. Dg_state a b -> a;
locals (DG x1 x2) = x1;

globs :: forall a b. Dg_state a b -> b;
globs (DG x1 x2) = x2;

sup_dg_state ::
  forall a b.
    (Semilattice_sup a,
      Semilattice_sup b) => Dg_state a b -> Dg_state a b -> Dg_state a b;
sup_dg_state d1 d2 =
  DG (sup (locals d1) (locals d2)) (sup (globs d1) (globs d2));

instance (Semilattice_sup a, Semilattice_sup b) => Sup (Dg_state a b) where {
  sup = sup_dg_state;
};

bot_dg_state :: forall a b. (Order_bot a, Order_bot b) => Dg_state a b;
bot_dg_state = DG bot bot;

instance (Order_bot a, Order_bot b) => Bot (Dg_state a b) where {
  bot = bot_dg_state;
};

less_eq_dg_state ::
  forall a b. (Ord a, Ord b) => Dg_state a b -> Dg_state a b -> Bool;
less_eq_dg_state d1 d2 =
  less_eq (locals d1) (locals d2) && less_eq (globs d1) (globs d2);

less_dg_state ::
  forall a b. (Ord a, Ord b) => Dg_state a b -> Dg_state a b -> Bool;
less_dg_state d1 d2 = less_eq_dg_state d1 d2 && not (less_eq_dg_state d2 d1);

instance (Ord a, Ord b) => Ord (Dg_state a b) where {
  less_eq = less_eq_dg_state;
  less = less_dg_state;
};

instance (Order a, Order b) => Preorder (Dg_state a b) where {
};

instance (Order a, Order b) => Order (Dg_state a b) where {
};

instance (Order_bot a, Order_bot b) => Order_bot (Dg_state a b) where {
};

widen_dg_state ::
  forall a b.
    (Bounded_warrowing a,
      Bounded_warrowing b) => Dg_state a b -> Dg_state a b -> Dg_state a b;
widen_dg_state a b =
  DG (widen (locals a) (locals b)) (widen (globs a) (globs b));

instance (Bounded_warrowing a,
           Bounded_warrowing b) => Widening (Dg_state a b) where {
  widen = widen_dg_state;
};

narrow_dg_state ::
  forall a b.
    (Bounded_warrowing a,
      Bounded_warrowing b) => Dg_state a b -> Dg_state a b -> Dg_state a b;
narrow_dg_state a b =
  DG (narrow (locals a) (locals b)) (narrow (globs a) (globs b));

instance (Bounded_warrowing a,
           Bounded_warrowing b) => Narrowing (Dg_state a b) where {
  narrow = narrow_dg_state;
};

instance (Bounded_warrowing a,
           Bounded_warrowing b) => Warrowing (Dg_state a b) where {
};

instance (Semilattice_sup a,
           Semilattice_sup b) => Semilattice_sup (Dg_state a b) where {
};

instance (Bounded_semilattice_sup_bot a,
           Bounded_semilattice_sup_bot b) => Bounded_semilattice_sup_bot (Dg_state
                                   a b) where {
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

instance (Bounded_warrowing a) => Bounded_warrowing (Resolved_st_q a) where {
};

data Set a = Set [a] | Coset [a];

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

data Check_result = Check_Proved | Check_Refuted | Check_Unknown;

data Dg_spec_ext a b c =
  Dg_spec_ext (a -> b -> (b, a)) ([Char] -> Aexp -> a -> b -> (b, a))
    ([Char] -> a -> b -> (b, a)) (Bexp -> a -> b -> (b, a))
    (Bexp -> a -> b -> (b, a)) ([[Char]] -> [Aexp] -> a -> b -> (b, a))
    (a -> a -> b -> (b, a)) (Maybe [Char] -> a -> b -> (b, a) -> (b, a)) c;

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

fold :: forall a b. (a -> b -> b) -> [a] -> b -> b;
fold f [] s = s;
fold f (x : xs) s = fold f xs (f x s);

image :: forall a b. (a -> b) -> Set a -> Set b;
image f (Set xs) = Set (map f xs);

foldr :: forall a b. (a -> b -> b) -> [a] -> b -> b;
foldr f [] = id;
foldr f (x : xs) = f x . foldr f xs;

filtera :: forall a. (a -> Bool) -> Set a -> Set a;
filtera p (Set xs) = Set (filter p xs);

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

fun_upd :: forall a b. (Eq a) => (a -> b) -> a -> b -> a -> b;
fun_upd f a b = (\ x -> (if x == a then b else f x));

bind :: forall a b. Maybe a -> (a -> Maybe b) -> Maybe b;
bind Nothing f = Nothing;
bind (Just x) f = f x;

remdups :: forall a. (Eq a) => [a] -> [a];
remdups [] = [];
remdups (x : xs) = (if membera xs x then remdups xs else x : remdups xs);

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

prog_main :: forall a. Imp_prog_ext a -> Com;
prog_main (Imp_prog_ext proc_rep prog_main declared_global_vars more) =
  prog_main;

ea_check_cond :: Edge_action -> Bexp;
ea_check_cond (EA_Check x7) = x7;

is_EA_Check :: Edge_action -> Bool;
is_EA_Check EA_Nop = False;
is_EA_Check (EA_Assign x21 x22) = False;
is_EA_Check (EA_Random x3) = False;
is_EA_Check (EA_Assume x4) = False;
is_EA_Check (EA_AssumeNot x5) = False;
is_EA_Check (EA_Ret x61 x62) = False;
is_EA_Check (EA_Check x7) = True;

falls_through :: Com -> Bool;
falls_through SKIP = True;
falls_through (Assign x a) = True;
falls_through (Random x) = True;
falls_through (Check c) = True;
falls_through (Seq c1 c2) = falls_through c1 && falls_through c2;
falls_through (If b c1 c2) = falls_through c1 || falls_through c2;
falls_through (While b c) = True;
falls_through (Call dst q actuals) = True;
falls_through (Return e) = False;
falls_through Restore = True;
falls_through Unwind = True;

plus_nat :: Nat -> Nat -> Nat;
plus_nat Zero_nat n = n;
plus_nat (Suc m) n = plus_nat m (Suc n);

formals :: forall a. Proc_decl_ext a -> [[Char]];
formals (Proc_decl_ext formals body more) = formals;

sup_set :: forall a. (Eq a) => Set a -> Set a -> Set a;
sup_set (Set xs) a = fold insert xs a;
sup_set (Coset xs) a = Coset (filter (\ x -> not (member x a)) xs);

bot_set :: forall a. Set a;
bot_set = Set [];

one_nat :: Nat;
one_nat = Suc Zero_nat;

csize :: Com -> Nat;
csize SKIP = one_nat;
csize (Assign x a) = one_nat;
csize (Random x) = one_nat;
csize (Check c) = one_nat;
csize (Seq c1 c2) = plus_nat (csize c1) (csize c2);
csize (If b c1 c2) = plus_nat (plus_nat one_nat (csize c1)) (csize c2);
csize (While b c) = plus_nat one_nat (csize c);
csize (Call dst q actuals) = one_nat;
csize (Return e) = one_nat;
csize Restore = one_nat;
csize Unwind = one_nat;

compile ::
  ([Char] -> Maybe (Proc_decl_ext ())) ->
    [Char] ->
      Com ->
        Cfg_node ->
          Nat ->
            (Nat, (Cfg_node,
                    (Set (Cfg_node, (Edge_action, Cfg_node)),
                      Set (Cfg_node, (Call_action, (Cfg_node, Cfg_node))))));
compile pi p SKIP k n =
  (Suc n, (Statement n, (insert (Statement n, (EA_Nop, k)) bot_set, bot_set)));
compile pi p (Assign x a) k n =
  (Suc n,
    (Statement n, (insert (Statement n, (EA_Assign x a, k)) bot_set, bot_set)));
compile pi p (Random x) k n =
  (Suc n,
    (Statement n, (insert (Statement n, (EA_Random x, k)) bot_set, bot_set)));
compile pi p (Check c) k n =
  (Suc n,
    (Statement n, (insert (Statement n, (EA_Check c, k)) bot_set, bot_set)));
compile pi p (Seq c1 c2) k n =
  (case compile pi p c1 (Statement (plus_nat n (csize c1))) n of {
    (_, (en1, (e1, k1))) ->
      (case compile pi p c2 k (plus_nat n (csize c1)) of {
        (n2, (_, (e2, k2))) -> (n2, (en1, (sup_set e1 e2, sup_set k1 k2)));
      });
  });
compile pi p (If b c1 c2) k n =
  (case compile pi p c1 k (Suc n) of {
    (n1, (en1, (e1, k1))) ->
      (case compile pi p c2 k n1 of {
        (n2, (en2, (e2, k2))) ->
          (n2, (Statement n,
                 (sup_set
                    (sup_set
                      (insert (Statement n, (EA_Assume b, en1))
                        (insert (Statement n, (EA_AssumeNot b, en2)) bot_set))
                      e1)
                    e2,
                   sup_set k1 k2)));
      });
  });
compile pi p (While b c) k n =
  (case compile pi p c (Statement n) (Suc n) of {
    (n1, (en1, (e1, k1))) ->
      (n1, (Statement n,
             (sup_set
                (insert (Statement n, (EA_Assume b, en1))
                  (insert (Statement n, (EA_AssumeNot b, k)) bot_set))
                e1,
               k1)));
  });
compile pi p (Call dst q actuals) k n =
  (Suc n,
    (Statement n,
      (bot_set,
        insert
          (Statement n,
            (CallEdge dst (case pi q of {
                            Nothing -> [];
                            Just a -> formals a;
                          })
               actuals,
              (FunctionEntry q, k)))
          bot_set)));
compile pi p (Return e) k n =
  (Suc n,
    (Statement n,
      (insert (Statement n, (EA_Ret e p, FunctionResult p)) bot_set, bot_set)));
compile pi p Restore k n =
  (Suc n, (Statement n, (insert (Statement n, (EA_Nop, k)) bot_set, bot_set)));
compile pi p Unwind k n =
  (Suc n, (Statement n, (insert (Statement n, (EA_Nop, k)) bot_set, bot_set)));

body :: forall a. Proc_decl_ext a -> Com;
body (Proc_decl_ext formals body more) = body;

compile_proc ::
  ([Char] -> Maybe (Proc_decl_ext ())) ->
    [Char] ->
      Proc_decl_ext () ->
        Nat ->
          (Nat, (Set (Cfg_node, (Edge_action, Cfg_node)),
                  Set (Cfg_node, (Call_action, (Cfg_node, Cfg_node)))));
compile_proc pi p decl n =
  let {
    r = plus_nat n (csize (body decl));
  } in (case compile pi p (body decl) (Statement r) n of {
         (_, (ben, (e, k))) ->
           (Suc r,
             (insert (FunctionEntry p, (EA_Nop, ben))
                (if falls_through (body decl)
                  then insert
                         (Statement r, (EA_Ret Nothing p, FunctionResult p)) e
                  else e),
               k));
       });

compile_procs ::
  ([Char] -> Maybe (Proc_decl_ext ())) ->
    [[Char]] ->
      Nat ->
        (Nat, (Set (Cfg_node, (Edge_action, Cfg_node)),
                Set (Cfg_node, (Call_action, (Cfg_node, Cfg_node)))));
compile_procs pi [] n = (n, (bot_set, bot_set));
compile_procs pi (p : ps) n =
  (case pi p of {
    Nothing -> compile_procs pi ps n;
    Just decl ->
      (case compile_proc pi p decl n of {
        (n1, (e, k)) -> (case compile_procs pi ps n1 of {
                          (n2, (ea, ka)) -> (n2, (sup_set e ea, sup_set k ka));
                        });
      });
  });

proc_decl_of :: [[Char]] -> Com -> Proc_decl_ext ();
proc_decl_of xs bdy = Proc_decl_ext xs bdy ();

compile_prog ::
  ([Char] -> Maybe (Proc_decl_ext ())) ->
    [[Char]] -> [Char] -> Com -> Cfg_ext ();
compile_prog pi ps mnm main =
  (case compile_procs pi ps Zero_nat of {
    (n1, (eprocs, kprocs)) ->
      (case compile_proc pi mnm (proc_decl_of [] main) n1 of {
        (_, (emain, kmain)) ->
          Cfg_ext (sup_set eprocs emain) (sup_set kprocs kmain)
            (FunctionEntry mnm)
            (image (\ (u, (a, _)) -> (u, ea_check_cond a))
              (filtera (\ (_, (a, _)) -> is_EA_Check a) (sup_set eprocs emain)))
            ();
      });
  });

make :: [([Char], Proc_decl_ext ())] -> Com -> [[Char]] -> Imp_prog_ext ();
make proc_rep prog_main declared_global_vars =
  Imp_prog_ext proc_rep prog_main declared_global_vars ();

one_int :: Int;
one_int = Pos One;

sign_ex_prog :: Imp_prog_ext ();
sign_ex_prog =
  make []
    (Seq (Assign [Char False False False True True True True False] (N one_int))
      (Assign [Char True False False True True True True False]
        (V [Char False False False True True True True False])))
    [];

prog_main_name :: [Char];
prog_main_name =
  [Char True False True True False True True False,
    Char True False False False False True True False,
    Char True False False True False True True False,
    Char False True True True False True True False];

proc_rep :: forall a. Imp_prog_ext a -> [([Char], Proc_decl_ext ())];
proc_rep (Imp_prog_ext proc_rep prog_main declared_global_vars more) = proc_rep;

prog_table :: Imp_prog_ext () -> [Char] -> Maybe (Proc_decl_ext ());
prog_table p =
  fun_upd (map_of (proc_rep p)) prog_main_name
    (Just (proc_decl_of [] (prog_main p)));

sign_ex_pi :: [Char] -> Maybe (Proc_decl_ext ());
sign_ex_pi = prog_table sign_ex_prog;

prog_procs :: Imp_prog_ext () -> [[Char]];
prog_procs p = map fst (proc_rep p);

gEx :: Cfg_ext ();
gEx = compile_prog sign_ex_pi (prog_procs sign_ex_prog) prog_main_name
        (prog_main sign_ex_prog);

map_ltree ::
  forall a b c d. (a -> b) -> Strategy_tree a c d -> Strategy_tree b c d;
map_ltree h (Answer d) = Answer d;
map_ltree h (QueryL y f) = QueryL (h y) (\ d -> map_ltree h (f d));
map_ltree h (QueryG y f) = QueryG y (\ d -> map_ltree h (f d));
map_ltree h (Side y d t) = Side y d (map_ltree h t);

sigma :: forall a b c d. State_ext a b c d -> Sum a b -> c;
sigma (State_ext c infl stabl sigma more) = sigma;

c_update ::
  forall a b c d. (Set a -> Set a) -> State_ext a b c d -> State_ext a b c d;
c_update ca (State_ext c infl stabl sigma more) =
  State_ext (ca c) infl stabl sigma more;

meet_sign :: Sign -> Sign -> Sign;
meet_sign SBot uu = SBot;
meet_sign SNeg SBot = SBot;
meet_sign SNonPos SBot = SBot;
meet_sign SZero SBot = SBot;
meet_sign SNonNeg SBot = SBot;
meet_sign SPos SBot = SBot;
meet_sign STop SBot = SBot;
meet_sign STop SNeg = SNeg;
meet_sign STop SNonPos = SNonPos;
meet_sign STop SZero = SZero;
meet_sign STop SNonNeg = SNonNeg;
meet_sign STop SPos = SPos;
meet_sign STop STop = STop;
meet_sign SNeg STop = SNeg;
meet_sign SNonPos STop = SNonPos;
meet_sign SZero STop = SZero;
meet_sign SNonNeg STop = SNonNeg;
meet_sign SPos STop = SPos;
meet_sign SNeg SNeg = SNeg;
meet_sign SNeg SNonPos = SNeg;
meet_sign SNonPos SNeg = SNeg;
meet_sign SNonPos SNonPos = SNonPos;
meet_sign SNonPos SZero = SZero;
meet_sign SZero SNonPos = SZero;
meet_sign SNonPos SNonNeg = SZero;
meet_sign SNonNeg SNonPos = SZero;
meet_sign SZero SZero = SZero;
meet_sign SZero SNonNeg = SZero;
meet_sign SNonNeg SZero = SZero;
meet_sign SNonNeg SNonNeg = SNonNeg;
meet_sign SNonNeg SPos = SPos;
meet_sign SPos SNonNeg = SPos;
meet_sign SPos SPos = SPos;
meet_sign SNeg SZero = SBot;
meet_sign SNeg SNonNeg = SBot;
meet_sign SNeg SPos = SBot;
meet_sign SNonPos SPos = SBot;
meet_sign SZero SNeg = SBot;
meet_sign SZero SPos = SBot;
meet_sign SNonNeg SNeg = SBot;
meet_sign SPos SNeg = SBot;
meet_sign SPos SNonPos = SBot;
meet_sign SPos SZero = SBot;

cinit_sign_st :: Resolved_st_q Sign;
cinit_sign_st = Abs_resolved_st (STop, (SZero, []));

dgs_combine_assign ::
  forall a b c. Dg_spec_ext a b c -> Maybe [Char] -> a -> b -> (b, a) -> (b, a);
dgs_combine_assign
  (Dg_spec_ext dgs_nop dgs_assign dgs_random dgs_assume dgs_assume_not dgs_enter
    dgs_combine_env dgs_combine_assign more)
  = dgs_combine_assign;

dgs_combine_env :: forall a b c. Dg_spec_ext a b c -> a -> a -> b -> (b, a);
dgs_combine_env
  (Dg_spec_ext dgs_nop dgs_assign dgs_random dgs_assume dgs_assume_not dgs_enter
    dgs_combine_env dgs_combine_assign more)
  = dgs_combine_env;

dgs_combine ::
  forall a b. Dg_spec_ext a b () -> Maybe [Char] -> a -> a -> b -> (b, a);
dgs_combine s dst dc de g =
  dgs_combine_assign s dst de g (dgs_combine_env s dc de g);

dg_combine_tree ::
  forall a b.
    (Bounded_semilattice_sup_bot a,
      Bounded_semilattice_sup_bot b) => (Maybe [Char] ->
  a -> a -> b -> (b, a)) ->
  Maybe [Char] ->
    Cfg_node -> Cfg_node -> Strategy_tree Cfg_node () (Dg_state a b);
dg_combine_tree comb dst cc ex =
  QueryL cc
    (\ dc ->
      QueryL ex
        (\ de ->
          QueryG ()
            (\ g ->
              Side ()
                (DG bot (fst (comb dst (locals dc) (locals de) (globs g))))
                (Answer
                  (DG (snd (comb dst (locals dc) (locals de) (globs g)))
                    bot)))));

dg_spec_combine_tree ::
  forall a b.
    (Bounded_semilattice_sup_bot a,
      Bounded_semilattice_sup_bot b) => Dg_spec_ext a b () ->
  Maybe [Char] ->
    Cfg_node -> Cfg_node -> Strategy_tree Cfg_node () (Dg_state a b);
dg_spec_combine_tree s dst cc ex = dg_combine_tree (dgs_combine s) dst cc ex;

map_gtree ::
  forall a b c d. (a -> b) -> Strategy_tree c a d -> Strategy_tree c b d;
map_gtree r (Answer d) = Answer d;
map_gtree r (QueryL y f) = QueryL y (\ d -> map_gtree r (f d));
map_gtree r (QueryG y f) = QueryG (r y) (\ d -> map_gtree r (f d));
map_gtree r (Side y d t) = Side (r y) d (map_gtree r t);

dg_cmb_of ::
  forall a b.
    (Bounded_semilattice_sup_bot a,
      Bounded_semilattice_sup_bot b) => Dg_spec_ext a b () ->
  (Cfg_node -> () -> a -> Call_action -> ()) ->
    () -> Call_action ->
            Cfg_node ->
              Cfg_node -> Strategy_tree (Cfg_node, ()) () (Dg_state a b);
dg_cmb_of s route ctx ca cc ex =
  (case ca of {
    CallEdge dst _ _ ->
      map_gtree (\ _ -> ())
        (map_ltree (\ w -> (w, ctx)) (dg_spec_combine_tree s dst cc ex));
  });

insort_key :: forall a b. (Linorder b) => (a -> b) -> a -> [a] -> [a];
insort_key f x [] = [x];
insort_key f x (y : ys) =
  (if less_eq (f x) (f y) then x : y : ys else y : insort_key f x ys);

sort_key :: forall a b. (Linorder b) => (a -> b) -> [a] -> [a];
sort_key f xs = foldr (insort_key f) xs [];

sorted_list_of_set :: forall a. (Eq a, Linorder a) => Set a -> [a];
sorted_list_of_set (Set xs) = sort_key (\ x -> x) (remdups xs);

cfg_calls_list ::
  Cfg_ext () -> [(Cfg_node, (Call_action, (Cfg_node, Cfg_node)))];
cfg_calls_list g = sorted_list_of_set (calls g);

return_call_action_list ::
  Cfg_ext () -> Cfg_node -> [(Cfg_node, (Call_action, Cfg_node))];
return_call_action_list g v =
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
                      (c, (ca, (case ce of {
                                 Statement _ -> ce;
                                 FunctionEntry a -> FunctionResult a;
                                 FunctionResult _ -> ce;
                               })));
                  })
        else Nothing))
    (cfg_calls_list g);

seqcomp_tree ::
  forall a b c.
    Strategy_tree a b c -> (c -> Strategy_tree a b c) -> Strategy_tree a b c;
seqcomp_tree (Answer v) k = k v;
seqcomp_tree (QueryL u f) k = QueryL u (\ d -> seqcomp_tree (f d) k);
seqcomp_tree (QueryG g f) k = QueryG g (\ d -> seqcomp_tree (f d) k);
seqcomp_tree (Side g v t) k = Side g v (seqcomp_tree t k);

side_rhs_fold_dg ::
  forall a b c d.
    (Bounded_semilattice_sup_bot a,
      Bounded_semilattice_sup_bot d) => a ->
  [Strategy_tree b c (Dg_state a d)] -> Strategy_tree b c (Dg_state a d);
side_rhs_fold_dg acc [] = Answer (DG acc bot);
side_rhs_fold_dg acc (t : ts) =
  seqcomp_tree t (\ res -> side_rhs_fold_dg (sup acc (locals res)) ts);

dgs_assume_not :: forall a b c. Dg_spec_ext a b c -> Bexp -> a -> b -> (b, a);
dgs_assume_not
  (Dg_spec_ext dgs_nop dgs_assign dgs_random dgs_assume dgs_assume_not dgs_enter
    dgs_combine_env dgs_combine_assign more)
  = dgs_assume_not;

dgs_random :: forall a b c. Dg_spec_ext a b c -> [Char] -> a -> b -> (b, a);
dgs_random
  (Dg_spec_ext dgs_nop dgs_assign dgs_random dgs_assume dgs_assume_not dgs_enter
    dgs_combine_env dgs_combine_assign more)
  = dgs_random;

dgs_assume :: forall a b c. Dg_spec_ext a b c -> Bexp -> a -> b -> (b, a);
dgs_assume
  (Dg_spec_ext dgs_nop dgs_assign dgs_random dgs_assume dgs_assume_not dgs_enter
    dgs_combine_env dgs_combine_assign more)
  = dgs_assume;

dgs_assign ::
  forall a b c. Dg_spec_ext a b c -> [Char] -> Aexp -> a -> b -> (b, a);
dgs_assign
  (Dg_spec_ext dgs_nop dgs_assign dgs_random dgs_assume dgs_assume_not dgs_enter
    dgs_combine_env dgs_combine_assign more)
  = dgs_assign;

dgs_nop :: forall a b c. Dg_spec_ext a b c -> a -> b -> (b, a);
dgs_nop
  (Dg_spec_ext dgs_nop dgs_assign dgs_random dgs_assume dgs_assume_not dgs_enter
    dgs_combine_env dgs_combine_assign more)
  = dgs_nop;

dg_spec_step ::
  forall a b c. Dg_spec_ext a b c -> Edge_action -> a -> b -> (b, a);
dg_spec_step s EA_Nop = dgs_nop s;
dg_spec_step s (EA_Assign x e) = dgs_assign s x e;
dg_spec_step s (EA_Random x) = dgs_random s x;
dg_spec_step s (EA_Assume b) = dgs_assume s b;
dg_spec_step s (EA_AssumeNot b) = dgs_assume_not s b;
dg_spec_step s (EA_Ret e p) = (case e of {
                                Nothing -> dgs_nop s;
                                Just a -> dgs_assign s ret_var a;
                              });
dg_spec_step s (EA_Check cnd) = dgs_nop s;

dg_edge_tree ::
  forall a b.
    (Bounded_semilattice_sup_bot a,
      Bounded_semilattice_sup_bot b) => (a -> b -> (b, a)) ->
  Cfg_node -> Strategy_tree Cfg_node () (Dg_state a b);
dg_edge_tree step u =
  QueryL u
    (\ d ->
      QueryG ()
        (\ g ->
          Side () (DG bot (fst (step (locals d) (globs g))))
            (Answer (DG (snd (step (locals d) (globs g))) bot))));

apply_dg_spec ::
  forall a b.
    (Bounded_semilattice_sup_bot a,
      Bounded_semilattice_sup_bot b) => Dg_spec_ext a b () ->
  Edge_action -> Cfg_node -> Strategy_tree Cfg_node () (Dg_state a b);
apply_dg_spec s a u = dg_edge_tree (dg_spec_step s a) u;

side_cfg_T_eff_keyed_seed_dg ::
  forall a b c d.
    (Bounded_semilattice_sup_bot c,
      Bounded_semilattice_sup_bot d) => (Cfg_ext () ->
  Cfg_node -> [(Cfg_node, Edge_action)]) ->
  (a -> b) ->
    (Cfg_node -> a -> c -> Call_action -> a) ->
      ((Cfg_node -> a -> c -> Call_action -> a) ->
        a -> Call_action ->
               Cfg_node ->
                 Cfg_node -> Strategy_tree (Cfg_node, a) b (Dg_state c d)) ->
        ((Cfg_node -> a -> c -> Call_action -> a) ->
          a -> Cfg_node -> [Strategy_tree (Cfg_node, a) b (Dg_state c d)]) ->
          Cfg_ext () ->
            Dg_spec_ext c d () ->
              c -> c -> d -> (Cfg_node, a) ->
                               Strategy_tree (Cfg_node, a) b (Dg_state c d);
side_cfg_T_eff_keyed_seed_dg pred_sel gkey route cmb extra g s bot0 s0d s0g =
  (\ (v, c) ->
    let {
      acc0 = (if equal_cfg_node v (cfg_entry g) then sup bot0 s0d else bot0);
      intra =
        map (\ (u, a) ->
              map_gtree (\ _ -> gkey c)
                (map_ltree (\ w -> (w, c)) (apply_dg_spec s a u)))
          (pred_sel g v);
      comb =
        map (\ (cc, (ca, a)) -> cmb route c ca cc a)
          (return_call_action_list g v);
      t = side_rhs_fold_dg acc0 (intra ++ comb ++ extra route c v);
    } in (if equal_cfg_node v (cfg_entry g) then Side (gkey c) (DG bot s0g) t
           else t));

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

dgs_enter ::
  forall a b c. Dg_spec_ext a b c -> [[Char]] -> [Aexp] -> a -> b -> (b, a);
dgs_enter
  (Dg_spec_ext dgs_nop dgs_assign dgs_random dgs_assume dgs_assume_not dgs_enter
    dgs_combine_env dgs_combine_assign more)
  = dgs_enter;

dg_extra_of ::
  forall a b.
    (Bounded_semilattice_sup_bot a,
      Bounded_semilattice_sup_bot b) => Dg_spec_ext a b () ->
  Cfg_ext () ->
    (Cfg_node -> () -> a -> Call_action -> ()) ->
      () -> Cfg_node -> [Strategy_tree (Cfg_node, ()) () (Dg_state a b)];
dg_extra_of s g route ctx v =
  map (\ (cl, CallEdge _ fs asa) ->
        map_gtree (\ _ -> ())
          (map_ltree (\ w -> (w, ctx)) (dg_edge_tree (dgs_enter s fs asa) cl)))
    (entry_call_list g v);

dg_gen_of ::
  forall a b.
    (Bounded_semilattice_sup_bot a,
      Bounded_semilattice_sup_bot b) => Dg_spec_ext a b () ->
  Cfg_ext () ->
    a -> a -> b -> (Cfg_node, ()) ->
                     Strategy_tree (Cfg_node, ()) () (Dg_state a b);
dg_gen_of s g bot0 s0d s0g =
  side_cfg_T_eff_keyed_seed_dg intra_predecessor_list (\ _ -> ())
    (\ _ _ _ _ -> ()) (dg_cmb_of s) (dg_extra_of s g) g s bot0 s0d s0g;

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

times_sign :: Sign -> Sign -> Sign;
times_sign SBot uu = SBot;
times_sign SNeg SBot = SBot;
times_sign SNonPos SBot = SBot;
times_sign SZero SBot = SBot;
times_sign SNonNeg SBot = SBot;
times_sign SPos SBot = SBot;
times_sign STop SBot = SBot;
times_sign SZero SNeg = SZero;
times_sign SZero SNonPos = SZero;
times_sign SZero SZero = SZero;
times_sign SZero SNonNeg = SZero;
times_sign SZero SPos = SZero;
times_sign SZero STop = SZero;
times_sign SNeg SZero = SZero;
times_sign SNonPos SZero = SZero;
times_sign SNonNeg SZero = SZero;
times_sign SPos SZero = SZero;
times_sign STop SZero = SZero;
times_sign SNeg SNeg = SPos;
times_sign SPos SPos = SPos;
times_sign SNeg SPos = SNeg;
times_sign SPos SNeg = SNeg;
times_sign SNeg SNonPos = SNonNeg;
times_sign SNonPos SNeg = SNonNeg;
times_sign SNeg SNonNeg = SNonPos;
times_sign SNonNeg SNeg = SNonPos;
times_sign SPos SNonNeg = SNonNeg;
times_sign SNonNeg SPos = SNonNeg;
times_sign SPos SNonPos = SNonPos;
times_sign SNonPos SPos = SNonPos;
times_sign SNonNeg SNonNeg = SNonNeg;
times_sign SNonNeg SNonPos = SNonPos;
times_sign SNonPos SNonNeg = SNonPos;
times_sign SNonPos SNonPos = SNonNeg;
times_sign SNeg STop = STop;
times_sign SNonPos STop = STop;
times_sign SNonNeg STop = STop;
times_sign SPos STop = STop;
times_sign STop SNeg = STop;
times_sign STop SNonPos = STop;
times_sign STop SNonNeg = STop;
times_sign STop SPos = STop;
times_sign STop STop = STop;

minus_sign :: Sign -> Sign -> Sign;
minus_sign SBot uu = SBot;
minus_sign SNeg SBot = SBot;
minus_sign SNonPos SBot = SBot;
minus_sign SZero SBot = SBot;
minus_sign SNonNeg SBot = SBot;
minus_sign SPos SBot = SBot;
minus_sign STop SBot = SBot;
minus_sign SNeg SPos = SNeg;
minus_sign SNeg SNonNeg = SNeg;
minus_sign SPos SNeg = SPos;
minus_sign SPos SNonPos = SPos;
minus_sign SNeg SZero = SNeg;
minus_sign SPos SZero = SPos;
minus_sign SZero SZero = SZero;
minus_sign SZero SNeg = SPos;
minus_sign SZero SPos = SNeg;
minus_sign SZero SNonNeg = SNonPos;
minus_sign SZero SNonPos = SNonNeg;
minus_sign SNonNeg SZero = SNonNeg;
minus_sign SNonNeg SNeg = SPos;
minus_sign SNonNeg SNonPos = SNonNeg;
minus_sign SNonPos SZero = SNonPos;
minus_sign SNonPos SPos = SNeg;
minus_sign SNonPos SNonNeg = SNonPos;
minus_sign SNeg SNeg = STop;
minus_sign SNeg SNonPos = STop;
minus_sign SNeg STop = STop;
minus_sign SNonPos SNeg = STop;
minus_sign SNonPos SNonPos = STop;
minus_sign SNonPos STop = STop;
minus_sign SZero STop = STop;
minus_sign SNonNeg SNonNeg = STop;
minus_sign SNonNeg SPos = STop;
minus_sign SNonNeg STop = STop;
minus_sign SPos SNonNeg = STop;
minus_sign SPos SPos = STop;
minus_sign SPos STop = STop;
minus_sign STop SNeg = STop;
minus_sign STop SNonPos = STop;
minus_sign STop SZero = STop;
minus_sign STop SNonNeg = STop;
minus_sign STop SPos = STop;
minus_sign STop STop = STop;

plus_sign :: Sign -> Sign -> Sign;
plus_sign SBot uu = SBot;
plus_sign SNeg SBot = SBot;
plus_sign SNonPos SBot = SBot;
plus_sign SZero SBot = SBot;
plus_sign SNonNeg SBot = SBot;
plus_sign SPos SBot = SBot;
plus_sign STop SBot = SBot;
plus_sign SNeg SNeg = SNeg;
plus_sign SNeg SNonPos = SNeg;
plus_sign SNonPos SNeg = SNeg;
plus_sign SNonPos SNonPos = SNonPos;
plus_sign SPos SPos = SPos;
plus_sign SPos SNonNeg = SPos;
plus_sign SNonNeg SPos = SPos;
plus_sign SNonNeg SNonNeg = SNonNeg;
plus_sign SZero SNeg = SNeg;
plus_sign SZero SNonPos = SNonPos;
plus_sign SZero SZero = SZero;
plus_sign SZero SNonNeg = SNonNeg;
plus_sign SZero SPos = SPos;
plus_sign SZero STop = STop;
plus_sign SNeg SZero = SNeg;
plus_sign SNonPos SZero = SNonPos;
plus_sign SNonNeg SZero = SNonNeg;
plus_sign SPos SZero = SPos;
plus_sign STop SZero = STop;
plus_sign SNeg SNonNeg = STop;
plus_sign SNeg SPos = STop;
plus_sign SNeg STop = STop;
plus_sign SNonPos SNonNeg = STop;
plus_sign SNonPos SPos = STop;
plus_sign SNonPos STop = STop;
plus_sign SNonNeg SNeg = STop;
plus_sign SNonNeg SNonPos = STop;
plus_sign SNonNeg STop = STop;
plus_sign SPos SNeg = STop;
plus_sign SPos SNonPos = STop;
plus_sign SPos STop = STop;
plus_sign STop SNeg = STop;
plus_sign STop SNonPos = STop;
plus_sign STop SNonNeg = STop;
plus_sign STop SPos = STop;
plus_sign STop STop = STop;

sign_of_int :: Int -> Sign;
sign_of_int n =
  (if less_int n Zero_int then SNeg
    else (if equal_int n Zero_int then SZero else SPos));

aval_sign :: Aexp -> ([Char] -> Sign) -> Sign;
aval_sign (N n) sigma = sign_of_int n;
aval_sign (V x) sigma = sigma x;
aval_sign (Plus a b) sigma = plus_sign (aval_sign a sigma) (aval_sign b sigma);
aval_sign (Minus a b) sigma =
  minus_sign (aval_sign a sigma) (aval_sign b sigma);
aval_sign (Times a b) sigma =
  times_sign (aval_sign a sigma) (aval_sign b sigma);

afilter_sign_st ::
  ([Char] -> Bool) -> Aexp -> Sign -> Resolved_st_q Sign -> Resolved_st_q Sign;
afilter_sign_st gs (V x) a s =
  update_resolved_st_q s (location_of gs x)
    (meet_sign a (fun_of_resolved_st_q_for gs s x));
afilter_sign_st gs (Plus e1 e2) a s =
  (case inv_conservative a (aval_sign e1 (fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
afilter_sign_st gs (Minus e1 e2) a s =
  (case inv_conservative a (aval_sign e1 (fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
afilter_sign_st gs (Times e1 e2) a s =
  (case inv_conservative a (aval_sign e1 (fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
afilter_sign_st gs (N v) a s = s;

inv_less_sign :: Bool -> Sign -> Sign -> (Sign, Sign);
inv_less_sign True a1 a2 =
  let {
    a1a = (if sign_le a2 SNonPos then meet_sign a1 SNeg else a1);
    a = (if sign_le a1 SNonNeg then meet_sign a2 SPos else a2);
  } in (a1a, a);
inv_less_sign False a1 a2 =
  let {
    a1a = (if sign_le a2 SPos then meet_sign a1 SPos
            else (if sign_le a2 SNonNeg then meet_sign a1 SNonNeg else a1));
    a = (if sign_le a1 SNeg then meet_sign a2 SNeg
          else (if sign_le a1 SNonPos then meet_sign a2 SNonPos else a2));
  } in (a1a, a);

inv_eq_sign :: Bool -> Sign -> Sign -> (Sign, Sign);
inv_eq_sign True a1 a2 = (meet_sign a1 a2, meet_sign a1 a2);
inv_eq_sign False a1 a2 =
  let {
    a1a = (if sign_le a1 SZero && sign_le a2 SZero then SBot
            else (if sign_le a2 SZero && sign_le a1 SNonNeg
                   then meet_sign a1 SPos
                   else (if sign_le a2 SZero && sign_le a1 SNonPos
                          then meet_sign a1 SNeg else a1)));
    a = (if sign_le a1 SZero && sign_le a2 SZero then SBot
          else (if sign_le a1 SZero && sign_le a2 SNonNeg then meet_sign a2 SPos
                 else (if sign_le a1 SZero && sign_le a2 SNonPos
                        then meet_sign a2 SNeg else a2)));
  } in (a1a, a);

bfilter_sign_st ::
  ([Char] -> Bool) -> Bexp -> Bool -> Resolved_st_q Sign -> Resolved_st_q Sign;
bfilter_sign_st gs (Less e1 e2) res s =
  (case inv_less_sign res (aval_sign e1 (fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
bfilter_sign_st gs (Not b) res s = bfilter_sign_st gs b (not res) s;
bfilter_sign_st gs (And b1 b2) True s =
  bfilter_sign_st gs b1 True (bfilter_sign_st gs b2 True s);
bfilter_sign_st gs (And b1 b2) False s =
  sup_resolved_st_q (bfilter_sign_st gs b1 False s)
    (bfilter_sign_st gs b2 False s);
bfilter_sign_st gs (Or b1 b2) True s =
  sup_resolved_st_q (bfilter_sign_st gs b1 True s)
    (bfilter_sign_st gs b2 True s);
bfilter_sign_st gs (Or b1 b2) False s =
  bfilter_sign_st gs b1 False (bfilter_sign_st gs b2 False s);
bfilter_sign_st gs (Eqb e1 e2) res s =
  (case inv_eq_sign res (aval_sign e1 (fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
bfilter_sign_st gs (Bc v) uv s = s;

assume_not_sign_st_for ::
  ([Char] -> Bool) -> Bexp -> Resolved_st_q Sign -> Resolved_st_q Sign;
assume_not_sign_st_for source_global b s =
  bfilter_sign_st source_global b False s;

assume_sign_st_for ::
  ([Char] -> Bool) -> Bexp -> Resolved_st_q Sign -> Resolved_st_q Sign;
assume_sign_st_for source_global b s = bfilter_sign_st source_global b True s;

sign_tf_st_for ::
  ([Char] -> Bool) -> Edge_action -> Resolved_st_q Sign -> Resolved_st_q Sign;
sign_tf_st_for source_global EA_Nop s = s;
sign_tf_st_for source_global (EA_Assign x a) s =
  update_resolved_st_q s (location_of source_global x)
    (aval_sign a (fun_of_resolved_st_q_for source_global s));
sign_tf_st_for source_global (EA_Random x) s =
  update_resolved_st_q s (location_of source_global x) STop;
sign_tf_st_for source_global (EA_Assume b) s =
  assume_sign_st_for source_global b s;
sign_tf_st_for source_global (EA_AssumeNot b) s =
  assume_not_sign_st_for source_global b s;
sign_tf_st_for source_global (EA_Ret Nothing p) s = s;
sign_tf_st_for source_global (EA_Ret (Just a) p) s =
  update_resolved_st_q s (location_of source_global ret_var)
    (aval_sign a (fun_of_resolved_st_q_for source_global s));
sign_tf_st_for source_global (EA_Check cnd) s = s;

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

location_is_local :: Location -> Bool;
location_is_local (Local_Location x) = True;
location_is_local (Global_Location x) = False;

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

combine_assign_resolved_q ::
  forall a.
    (Bot a) => ([Char] -> Bool) ->
                 Maybe [Char] -> a -> Resolved_st_q a -> Resolved_st_q a;
combine_assign_resolved_q xc xb xa (Abs_resolved_st x) =
  Abs_resolved_st (combine_assign_resolved xc xb xa x);

unit_combine_step_st_assign_for ::
  forall a.
    (Bounded_semilattice_sup_bot a) => ([Char] -> Bool) ->
 Maybe [Char] ->
   Resolved_st_q a ->
     Resolved_st_q a ->
       (Resolved_st_q a, Resolved_st_q a) -> (Resolved_st_q a, Resolved_st_q a);
unit_combine_step_st_assign_for gs dst de g merged =
  let {
    res = combine_assign_resolved_q gs dst
            (lookup_resolved_st_q (sup_resolved_st_q de g)
              (location_of gs ret_var))
            (sup_resolved_st_q (fst merged) (snd merged));
  } in (restrict_global_resolved_q res, restrict_local_resolved_q res);

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

combine_resolved_st_q ::
  forall a. (Bot a) => Resolved_st_q a -> Resolved_st_q a -> Resolved_st_q a;
combine_resolved_st_q (Abs_resolved_st xa) (Abs_resolved_st x) =
  Abs_resolved_st (combine_resolved_st xa x);

unit_combine_step_st_env ::
  forall a.
    (Bounded_semilattice_sup_bot a) => Resolved_st_q a ->
 Resolved_st_q a -> Resolved_st_q a -> (Resolved_st_q a, Resolved_st_q a);
unit_combine_step_st_env dc de g =
  let {
    m = combine_resolved_st_q (sup_resolved_st_q dc g) (sup_resolved_st_q de g);
  } in (restrict_global_resolved_q m, restrict_local_resolved_q m);

unit_step_st ::
  forall a.
    (Bounded_semilattice_sup_bot a) => (Resolved_st_q a -> Resolved_st_q a) ->
 Resolved_st_q a -> Resolved_st_q a -> (Resolved_st_q a, Resolved_st_q a);
unit_step_st f d g =
  let {
    res = f (sup_resolved_st_q d g);
  } in (restrict_global_resolved_q res, restrict_local_resolved_q res);

unit_dg_spec_st_for ::
  forall a.
    (Bounded_semilattice_sup_bot a) => ([Char] -> Bool) ->
 (Edge_action -> Resolved_st_q a -> Resolved_st_q a) ->
   ([[Char]] -> [Aexp] -> Resolved_st_q a -> Resolved_st_q a) ->
     Dg_spec_ext (Resolved_st_q a) (Resolved_st_q a) ();
unit_dg_spec_st_for gs tf_st enter_st =
  Dg_spec_ext (unit_step_st (tf_st EA_Nop))
    (\ x e -> unit_step_st (tf_st (EA_Assign x e)))
    (\ x -> unit_step_st (tf_st (EA_Random x)))
    (\ b -> unit_step_st (tf_st (EA_Assume b)))
    (\ b -> unit_step_st (tf_st (EA_AssumeNot b)))
    (\ xs es -> unit_step_st (enter_st xs es)) unit_combine_step_st_env
    (unit_combine_step_st_assign_for gs) ();

declared_global_vars :: forall a. Imp_prog_ext a -> [[Char]];
declared_global_vars (Imp_prog_ext proc_rep prog_main declared_global_vars more)
  = declared_global_vars;

declared_global :: Imp_prog_ext () -> [Char] -> Bool;
declared_global p x = membera (declared_global_vars p) x;

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

sign_enter_st_for ::
  ([Char] -> Bool) ->
    [[Char]] -> [Aexp] -> Resolved_st_q Sign -> Resolved_st_q Sign;
sign_enter_st_for source_global xs es s =
  bind_formals_resolved_q source_global xs
    (map (\ e -> aval_sign e (fun_of_resolved_st_q_for source_global s)) es)
    (enter_frame_D_resolved_q STop s);

dgEx_eqs ::
  (Cfg_node, ()) ->
    Strategy_tree (Cfg_node, ()) ()
      (Dg_state (Resolved_st_q Sign) (Resolved_st_q Sign));
dgEx_eqs =
  dg_gen_of
    (unit_dg_spec_st_for (declared_global sign_ex_prog)
      (sign_tf_st_for (declared_global sign_ex_prog))
      (sign_enter_st_for (declared_global sign_ex_prog)))
    gEx bot_resolved_st_q cinit_sign_st cinit_sign_st;

rho_update ::
  forall a b c d.
    ((a -> Fmap b c) -> a -> Fmap b c) ->
      Ug_state_ext b a c d -> Ug_state_ext b a c d;
rho_update rhoa (Ug_state_ext rho more) = Ug_state_ext (rhoa rho) more;

rho :: forall a b c d. Ug_state_ext a b c d -> b -> Fmap a c;
rho (Ug_state_ext rho more) = rho;

update_global_always_join ::
  forall a b c.
    (Eq a, Bounded_semilattice_sup_bot a, Eq b,
      Eq c) => a -> b -> c -> a -> Ug_state_ext b c a () ->
                                     (Maybe a, Ug_state_ext b c a ());
update_global_always_join da orig g d state =
  let {
    statea =
      rho_update (\ _ -> fun_upd (rho state) g (fmupd orig d (rho state g)))
        state;
    db = sup da d;
  } in (if db == da then (Nothing, statea) else (Just db, statea));

warrow :: forall a. (Warrowing a) => a -> a -> a;
warrow a b = (if less_eq b a then narrow a b else widen a b);

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

stabl_update ::
  forall a b c d. (Set a -> Set a) -> State_ext a b c d -> State_ext a b c d;
stabl_update stabla (State_ext c infl stabl sigma more) =
  State_ext c infl (stabla stabl) sigma more;

infl_update ::
  forall a b c d.
    (Fmap (Sum a b) [a] -> Fmap (Sum a b) [a]) ->
      State_ext a b c d -> State_ext a b c d;
infl_update infla (State_ext c infl stabl sigma more) =
  State_ext c (infla infl) stabl sigma more;

tD_side_always_join_Interp_solve_rec_c ::
  forall a b c.
    (Eq a, Eq b, Eq c, Bounded_semilattice_sup_bot c,
      Warrowing c) => (a -> Strategy_tree a b c) ->
                        Func_state a b c () ->
                          Maybe (c, (State_ext a b c (State_exta a ()),
                                      Ug_state_ext a b c ()));
tD_side_always_join_Interp_solve_rec_c t s =
  (case s of {
    Q (y, (x, (state, ug_state))) ->
      bind (if member x (c state)
             then Just (sigma state (Inl x),
                         (point_update (\ _ -> insert x (point state)) state,
                           ug_state))
             else tD_side_always_join_Interp_solve_rec_c t
                    (I (x, (c_update (\ _ -> insert x (c state)) state,
                             ug_state))))
        (\ (xd, (statea, ug_statea)) ->
          Just (xd, (infl_update (\ _ -> fminsert (infl statea) (Inl x) y)
                       statea,
                      ug_statea)));
    I (x, (state, ug_state)) ->
      (if not (member x (stabl state))
        then bind (tD_side_always_join_Interp_solve_rec_c t
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
                                 tD_side_always_join_Interp_solve_rec_c t
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
      bind (tD_side_always_join_Interp_solve_rec_c t
             (E (x, (t x, ((\ _ -> bot),
                            (stabl_update (\ _ -> insert x (stabl state)) state,
                              ug_state))))))
        (\ (xd, (statea, ug_statea)) ->
          (if member x (stabl statea) then Just (xd, (statea, ug_statea))
            else tD_side_always_join_Interp_solve_rec_c t
                   (R (x, (statea, ug_statea)))));
    E (_, (Answer d, (_, (state, ug_state)))) -> Just (d, (state, ug_state));
    E (x, (QueryL y g, (sides_a_c_c, (state, ug_state)))) ->
      bind (tD_side_always_join_Interp_solve_rec_c t
             (Q (x, (y, (state, ug_state)))))
        (\ (yd, (statea, ug_statea)) ->
          tD_side_always_join_Interp_solve_rec_c t
            (E (x, (g yd, (sides_a_c_c, (statea, ug_statea))))));
    E (x, (QueryG y g, (sides_a_c_c, (state, ug_state)))) ->
      tD_side_always_join_Interp_solve_rec_c t
        (E (x, (g (sigma state (Inr y)),
                 (sides_a_c_c,
                   (infl_update (\ _ -> fminsert (infl state) (Inr y) x) state,
                     ug_state)))));
    E (x, (Side y d ta, (sides_a_c_c, (state, ug_state)))) ->
      let {
        da = sup (sides_a_c_c y) d;
        sides_a_c_ca = fun_upd sides_a_c_c y da;
      } in (case update_global_always_join (sigma state (Inr y)) x y da ug_state
             of {
             (Nothing, ug_statea) ->
               tD_side_always_join_Interp_solve_rec_c t
                 (E (x, (ta, (sides_a_c_ca, (state, ug_statea)))));
             (Just db, ug_statea) ->
               (case destab_opt (Inr y) (infl state) (stabl state) (c state) of
                 {
                 (infla, stabla) ->
                   tD_side_always_join_Interp_solve_rec_c t
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

tD_side_always_join_Interp_solve_c ::
  forall a b c.
    (Eq a, Eq b, Eq c, Bounded_semilattice_sup_bot c,
      Warrowing c) => (a -> Strategy_tree a b c) ->
                        a -> Maybe (Set a, Sum a b -> c);
tD_side_always_join_Interp_solve_c t x =
  bind (tD_side_always_join_Interp_solve_rec_c t
         (I (x, (c_update
                   (\ _ ->
                     insert x
                       (c (init_state :: State_ext a b c (State_exta a ()))))
                   init_state,
                  init_basic_ug_state))))
    (\ (_, (state, _)) -> Just (stabl state, sigma state));

tD_side_always_join_Interp_solve ::
  forall a b c.
    (Eq a, Eq b, Eq c, Bounded_semilattice_sup_bot c,
      Warrowing c) => (a -> Strategy_tree a b c) -> a -> (Set a, Sum a b -> c);
tD_side_always_join_Interp_solve t x =
  (case tD_side_always_join_Interp_solve_c t x of {
    Nothing ->
      (error :: forall a. String -> (() -> a) -> a) "Input not in domain"
        (\ _ -> tD_side_always_join_Interp_solve t x);
    Just r -> r;
  });

dgEx_sol ::
  (Set (Cfg_node, ()),
    Sum (Cfg_node, ()) () ->
      Dg_state (Resolved_st_q Sign) (Resolved_st_q Sign));
dgEx_sol = tD_side_always_join_Interp_solve dgEx_eqs (cfg_exit gEx, ());

prog_cfg :: [Char] -> Imp_prog_ext () -> Cfg_ext ();
prog_cfg mnm p = compile_prog (prog_table p) (prog_procs p) mnm (prog_main p);

sign_less_true_of_inv :: Sign -> Sign -> Bool;
sign_less_true_of_inv a b =
  equal_sign (fst (inv_less_sign False a b)) bot_sign ||
    equal_sign (snd (inv_less_sign False a b)) bot_sign;

sign_less_true :: Sign -> Sign -> Bool;
sign_less_true = sign_less_true_of_inv;

sign_less_false_of_inv :: Sign -> Sign -> Bool;
sign_less_false_of_inv a b =
  equal_sign (fst (inv_less_sign True a b)) bot_sign ||
    equal_sign (snd (inv_less_sign True a b)) bot_sign;

sign_eq_true_of_less :: Sign -> Sign -> Bool;
sign_eq_true_of_less a b =
  sign_less_false_of_inv a b && sign_less_false_of_inv b a;

sign_eq_true :: Sign -> Sign -> Bool;
sign_eq_true = sign_eq_true_of_less;

sign_less_false :: Sign -> Sign -> Bool;
sign_less_false = sign_less_false_of_inv;

sign_eq_false_of_meet :: Sign -> Sign -> Bool;
sign_eq_false_of_meet a b = equal_sign (meet_sign a b) bot_sign;

sign_eq_false :: Sign -> Sign -> Bool;
sign_eq_false = sign_eq_false_of_meet;

sign_check_true :: Bexp -> ([Char] -> Sign) -> Bool;
sign_check_true (Bc v) d = v;
sign_check_true (Not b) d = sign_check_false b d;
sign_check_true (And b1 b2) d = sign_check_true b1 d && sign_check_true b2 d;
sign_check_true (Or b1 b2) d = sign_check_true b1 d || sign_check_true b2 d;
sign_check_true (Less a b) d = sign_less_true (aval_sign a d) (aval_sign b d);
sign_check_true (Eqb a b) d = sign_eq_true (aval_sign a d) (aval_sign b d);

sign_check_false :: Bexp -> ([Char] -> Sign) -> Bool;
sign_check_false (Bc v) d = not v;
sign_check_false (Not b) d = sign_check_true b d;
sign_check_false (And b1 b2) d = sign_check_false b1 d || sign_check_false b2 d;
sign_check_false (Or b1 b2) d = sign_check_false b1 d && sign_check_false b2 d;
sign_check_false (Less a b) d = sign_less_false (aval_sign a d) (aval_sign b d);
sign_check_false (Eqb a b) d = sign_eq_false (aval_sign a d) (aval_sign b d);

sup_fun :: forall a b. (Semilattice_sup b) => (a -> b) -> (a -> b) -> a -> b;
sup_fun f g x = sup (f x) (g x);

classify_checks ::
  forall a.
    Cfg_ext () ->
      (Cfg_node -> a) ->
        (Bexp -> a -> Check_result) -> [(Cfg_node, (Bexp, Check_result))];
classify_checks g env classify =
  map_filter
    (\ x ->
      (if (case x of {
            (_, (a, _)) -> is_EA_Check a;
          })
        then Just (case x of {
                    (u, (a, _)) ->
                      (u, (ea_check_cond a,
                            classify (ea_check_cond a) (env u)));
                  })
        else Nothing))
    (cfg_intra_list g);

sign_classify_check :: Bexp -> ([Char] -> Sign) -> Check_result;
sign_classify_check c d =
  (if sign_check_true c d then Check_Proved
    else (if sign_check_false c d then Check_Refuted else Check_Unknown));

analyse_sign_eqs_for ::
  ([Char] -> Bool) ->
    Imp_prog_ext () ->
      (Cfg_node, ()) ->
        Strategy_tree (Cfg_node, ()) ()
          (Dg_state (Resolved_st_q Sign) (Resolved_st_q Sign));
analyse_sign_eqs_for gs p =
  dg_gen_of (unit_dg_spec_st_for gs (sign_tf_st_for gs) (sign_enter_st_for gs))
    (prog_cfg prog_main_name p) bot_resolved_st_q cinit_sign_st cinit_sign_st;

analyse_sign_for ::
  ([Char] -> Bool) ->
    Imp_prog_ext () ->
      (Set (Cfg_node, ()),
        Sum (Cfg_node, ()) () ->
          Dg_state (Resolved_st_q Sign) (Resolved_st_q Sign));
analyse_sign_for gs p =
  tD_side_always_join_Interp_solve (analyse_sign_eqs_for gs p)
    (cfg_exit (prog_cfg prog_main_name p), ());

analyse_sign ::
  Imp_prog_ext () ->
    (Set (Cfg_node, ()),
      Sum (Cfg_node, ()) () ->
        Dg_state (Resolved_st_q Sign) (Resolved_st_q Sign));
analyse_sign p = analyse_sign_for (declared_global p) p;

fun_of_exec_dg_st_for ::
  forall a. (Bot a) => ([Char] -> Bool) -> Resolved_st_q a -> [Char] -> a;
fun_of_exec_dg_st_for gs = fun_of_resolved_st_q_for gs;

analyse_sign_report_for ::
  ([Char] -> Bool) -> Imp_prog_ext () -> [(Cfg_node, (Bexp, Check_result))];
analyse_sign_report_for gs p =
  let {
    sol = snd (analyse_sign_for gs p);
  } in classify_checks (prog_cfg prog_main_name p)
         (\ v ->
           sup_fun (fun_of_exec_dg_st_for gs (locals (sol (Inl (v, ())))))
             (fun_of_exec_dg_st_for gs (globs (sol (Inr ())))))
         sign_classify_check;

analyse_sign_report :: Imp_prog_ext () -> [(Cfg_node, (Bexp, Check_result))];
analyse_sign_report p = analyse_sign_report_for (declared_global p) p;

}
