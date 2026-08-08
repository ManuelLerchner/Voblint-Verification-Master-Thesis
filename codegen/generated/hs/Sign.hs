{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Sign(Sign, analyse_sign_report, analyse_sign_report_with_state) where {

import Prelude ((==), (/=), (<), (<=), (>=), (>), (+), (-), (*), (/), (**),
  (>>=), (>>), (=<<), (&&), (||), (^), (^^), (.), ($), ($!), (++), (!!), Eq,
  error, id, return, not, fst, snd, map, filter, concat, concatMap, reverse,
  zip, null, takeWhile, dropWhile, all, any, Integer, negate, abs, divMod,
  String, Bool(True, False), Maybe(Nothing, Just));
import Data.Bits ((.&.), (.|.), (.^.));
import qualified Prelude;
import qualified Data.Bits;
import qualified Str_Literal;
import qualified HOL;
import qualified Core;

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

instance Core.Sup Sign where {
  sup = sup_sign;
};

bot_sign :: Sign;
bot_sign = SBot;

instance Core.Bot Sign where {
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

instance Core.Ord Sign where {
  less_eq = less_eq_sign;
  less = less_sign;
};

instance Core.Preorder Sign where {
};

instance Core.Order Sign where {
};

instance Core.Order_bot Sign where {
};

widen_sign :: Sign -> Sign -> Sign;
widen_sign a b = join_sign a b;

instance Core.Widening Sign where {
  widen = widen_sign;
};

narrow_sign_td :: Sign -> Sign -> Sign;
narrow_sign_td a b = a;

narrow_sign :: Sign -> Sign -> Sign;
narrow_sign a b = narrow_sign_td a b;

instance Core.Narrowing Sign where {
  narrow = narrow_sign;
};

instance Core.Warrowing Sign where {
};

instance Core.Semilattice_sup Sign where {
};

instance Core.Bounded_semilattice_sup_bot Sign where {
};

instance Core.Bounded_warrowing Sign where {
};

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

cinit_sign_st :: Core.Resolved_st_q Sign;
cinit_sign_st = Core.Abs_resolved_st (STop, (SZero, []));

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

sign_of_int :: Core.Int -> Sign;
sign_of_int n =
  (if Core.less_int n Core.zero_int then SNeg
    else (if Core.equal_int n Core.zero_int then SZero else SPos));

aval_sign :: Core.Aexp -> (String -> Sign) -> Sign;
aval_sign (Core.N n) sigma = sign_of_int n;
aval_sign (Core.V x) sigma = sigma x;
aval_sign (Core.Plus a b) sigma =
  plus_sign (aval_sign a sigma) (aval_sign b sigma);
aval_sign (Core.Minus a b) sigma =
  minus_sign (aval_sign a sigma) (aval_sign b sigma);
aval_sign (Core.Times a b) sigma =
  times_sign (aval_sign a sigma) (aval_sign b sigma);

afilter_sign_st ::
  (String -> Bool) ->
    Core.Aexp -> Sign -> Core.Resolved_st_q Sign -> Core.Resolved_st_q Sign;
afilter_sign_st gs (Core.V x) a s =
  Core.update_resolved_st_q s (Core.location_of gs x)
    (meet_sign a (Core.fun_of_resolved_st_q_for gs s x));
afilter_sign_st gs (Core.Plus e1 e2) a s =
  (case Core.inv_conservative a
          (aval_sign e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
afilter_sign_st gs (Core.Minus e1 e2) a s =
  (case Core.inv_conservative a
          (aval_sign e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
afilter_sign_st gs (Core.Times e1 e2) a s =
  (case Core.inv_conservative a
          (aval_sign e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
afilter_sign_st gs (Core.N v) a s = s;

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
  (String -> Bool) ->
    Core.Bexp -> Bool -> Core.Resolved_st_q Sign -> Core.Resolved_st_q Sign;
bfilter_sign_st gs (Core.Less e1 e2) res s =
  (case inv_less_sign res (aval_sign e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
bfilter_sign_st gs (Core.Not b) res s = bfilter_sign_st gs b (not res) s;
bfilter_sign_st gs (Core.And b1 b2) True s =
  bfilter_sign_st gs b1 True (bfilter_sign_st gs b2 True s);
bfilter_sign_st gs (Core.And b1 b2) False s =
  Core.sup_resolved_st_q (bfilter_sign_st gs b1 False s)
    (bfilter_sign_st gs b2 False s);
bfilter_sign_st gs (Core.Or b1 b2) True s =
  Core.sup_resolved_st_q (bfilter_sign_st gs b1 True s)
    (bfilter_sign_st gs b2 True s);
bfilter_sign_st gs (Core.Or b1 b2) False s =
  bfilter_sign_st gs b1 False (bfilter_sign_st gs b2 False s);
bfilter_sign_st gs (Core.Eqb e1 e2) res s =
  (case inv_eq_sign res (aval_sign e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_sign e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_sign_st gs e1 a1 (afilter_sign_st gs e2 a2 s);
  });
bfilter_sign_st gs (Core.Bc v) uv s = s;

assume_not_sign_st_for ::
  (String -> Bool) ->
    Core.Bexp -> Core.Resolved_st_q Sign -> Core.Resolved_st_q Sign;
assume_not_sign_st_for source_global b s =
  bfilter_sign_st source_global b False s;

assume_sign_st_for ::
  (String -> Bool) ->
    Core.Bexp -> Core.Resolved_st_q Sign -> Core.Resolved_st_q Sign;
assume_sign_st_for source_global b s = bfilter_sign_st source_global b True s;

sign_tf_st_for ::
  (String -> Bool) ->
    Core.Edge_action -> Core.Resolved_st_q Sign -> Core.Resolved_st_q Sign;
sign_tf_st_for source_global Core.EA_Nop s = s;
sign_tf_st_for source_global (Core.EA_Assign x a) s =
  Core.update_resolved_st_q s (Core.location_of source_global x)
    (aval_sign a (Core.fun_of_resolved_st_q_for source_global s));
sign_tf_st_for source_global (Core.EA_Random x) s =
  Core.update_resolved_st_q s (Core.location_of source_global x) STop;
sign_tf_st_for source_global (Core.EA_Assume b) s =
  assume_sign_st_for source_global b s;
sign_tf_st_for source_global (Core.EA_AssumeNot b) s =
  assume_not_sign_st_for source_global b s;
sign_tf_st_for source_global (Core.EA_Ret Nothing p) s = s;
sign_tf_st_for source_global (Core.EA_Ret (Just a) p) s =
  Core.update_resolved_st_q s (Core.location_of source_global Core.ret_var)
    (aval_sign a (Core.fun_of_resolved_st_q_for source_global s));
sign_tf_st_for source_global (Core.EA_Check cnd) s = s;

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

sign_check_true :: Core.Bexp -> (String -> Sign) -> Bool;
sign_check_true (Core.Bc v) d = v;
sign_check_true (Core.Not b) d = sign_check_false b d;
sign_check_true (Core.And b1 b2) d =
  sign_check_true b1 d && sign_check_true b2 d;
sign_check_true (Core.Or b1 b2) d =
  sign_check_true b1 d || sign_check_true b2 d;
sign_check_true (Core.Less a b) d =
  sign_less_true (aval_sign a d) (aval_sign b d);
sign_check_true (Core.Eqb a b) d = sign_eq_true (aval_sign a d) (aval_sign b d);

sign_check_false :: Core.Bexp -> (String -> Sign) -> Bool;
sign_check_false (Core.Bc v) d = not v;
sign_check_false (Core.Not b) d = sign_check_true b d;
sign_check_false (Core.And b1 b2) d =
  sign_check_false b1 d || sign_check_false b2 d;
sign_check_false (Core.Or b1 b2) d =
  sign_check_false b1 d && sign_check_false b2 d;
sign_check_false (Core.Less a b) d =
  sign_less_false (aval_sign a d) (aval_sign b d);
sign_check_false (Core.Eqb a b) d =
  sign_eq_false (aval_sign a d) (aval_sign b d);

sign_enter_st_for ::
  (String -> Bool) ->
    [String] ->
      [Core.Aexp] -> Core.Resolved_st_q Sign -> Core.Resolved_st_q Sign;
sign_enter_st_for source_global xs es s =
  Core.bind_formals_resolved_q source_global xs
    (map (\ e -> aval_sign e (Core.fun_of_resolved_st_q_for source_global s))
      es)
    (Core.enter_frame_D_resolved_q STop s);

analyse_sign_eqs_for ::
  (String -> Bool) ->
    Core.Imp_prog_ext () ->
      (Core.Cfg_node, ()) ->
        Core.Strategy_tree (Core.Cfg_node, ()) ()
          (Core.Dg_state (Core.Resolved_st_q Sign) (Core.Resolved_st_q Sign));
analyse_sign_eqs_for gs p =
  Core.dg_gen_of
    (Core.unit_dg_spec_st_for gs (sign_tf_st_for gs) (sign_enter_st_for gs))
    (Core.prog_cfg Core.prog_main_name p) Core.bot_resolved_st_q cinit_sign_st
    cinit_sign_st;

analyse_sign_for ::
  (String -> Bool) ->
    Core.Imp_prog_ext () ->
      (Core.Set (Core.Cfg_node, ()),
        Core.Sum (Core.Cfg_node, ()) () ->
          Core.Dg_state (Core.Resolved_st_q Sign) (Core.Resolved_st_q Sign));
analyse_sign_for gs p =
  Core.tD_side_always_join_Interp_solve (analyse_sign_eqs_for gs p)
    (Core.cfg_exit (Core.prog_cfg Core.prog_main_name p), ());

sign_classify_check :: Core.Bexp -> (String -> Sign) -> Core.Check_result;
sign_classify_check c d =
  (if sign_check_true c d then Core.Check_Proved
    else (if sign_check_false c d then Core.Check_Refuted
           else Core.Check_Unknown));

analyse_sign_report_for ::
  (String -> Bool) ->
    Core.Imp_prog_ext () -> [(Core.Cfg_node, (Core.Bexp, Core.Check_result))];
analyse_sign_report_for gs p =
  let {
    sol = snd (analyse_sign_for gs p);
  } in Core.classify_checks (Core.prog_cfg Core.prog_main_name p)
         (\ v ->
           Core.sup_fun
             (Core.fun_of_exec_dg_st_for gs
               (Core.locals (sol (Core.Inl (v, ())))))
             (Core.fun_of_exec_dg_st_for gs (Core.globs (sol (Core.Inr ())))))
         sign_classify_check;

analyse_sign_report ::
  Core.Imp_prog_ext () -> [(Core.Cfg_node, (Core.Bexp, Core.Check_result))];
analyse_sign_report p = analyse_sign_report_for (Core.declared_global p) p;

analyse_sign_report_for_with_state ::
  (String -> Bool) ->
    Core.Imp_prog_ext () ->
      [(Core.Cfg_node, (Core.Bexp, (Core.Check_result, String -> Sign)))];
analyse_sign_report_for_with_state gs p =
  let {
    sol = snd (analyse_sign_for gs p);
  } in Core.classify_checks_with_state (Core.prog_cfg Core.prog_main_name p)
         (\ v ->
           Core.sup_fun
             (Core.fun_of_exec_dg_st_for gs
               (Core.locals (sol (Core.Inl (v, ())))))
             (Core.fun_of_exec_dg_st_for gs (Core.globs (sol (Core.Inr ())))))
         sign_classify_check;

analyse_sign_report_with_state ::
  Core.Imp_prog_ext () ->
    [(Core.Cfg_node, (Core.Bexp, (Core.Check_result, String -> Sign)))];
analyse_sign_report_with_state p =
  analyse_sign_report_for_with_state (Core.declared_global p) p;

}
