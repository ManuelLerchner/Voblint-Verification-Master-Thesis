{-# LANGUAGE EmptyDataDecls, RankNTypes, ScopedTypeVariables #-}

module Interval(analyse_interval_td_report) where {

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

data Eint = MinInf | Fin Core.Int | PlusInf;

equal_eint :: Eint -> Eint -> Bool;
equal_eint (Fin x2) PlusInf = False;
equal_eint PlusInf (Fin x2) = False;
equal_eint MinInf PlusInf = False;
equal_eint PlusInf MinInf = False;
equal_eint MinInf (Fin x2) = False;
equal_eint (Fin x2) MinInf = False;
equal_eint (Fin x2) (Fin y2) = Core.equal_int x2 y2;
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
eint_le (Fin n) (Fin m) = Core.less_eq_int n m;
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

instance Core.Sup Ivl where {
  sup = sup_ivl;
};

bot_ivl :: Ivl;
bot_ivl = Ivl PlusInf MinInf;

instance Core.Bot Ivl where {
  bot = bot_ivl;
};

less_eq_ivl :: Ivl -> Ivl -> Bool;
less_eq_ivl a b =
  (case (a, b) of {
    (Ivl l1 u1, Ivl l2 u2) -> less_eq_eint l2 l1 && less_eq_eint u1 u2;
  });

less_ivl :: Ivl -> Ivl -> Bool;
less_ivl a b = less_eq_ivl a b && not (less_eq_ivl b a);

instance Core.Ord Ivl where {
  less_eq = less_eq_ivl;
  less = less_ivl;
};

instance Core.Preorder Ivl where {
};

instance Core.Order Ivl where {
};

instance Core.Order_bot Ivl where {
};

widen_ivl_core :: Ivl -> Ivl -> Ivl;
widen_ivl_core (Ivl l1 u1) (Ivl l2 u2) =
  Ivl (if less_eq_eint l1 l2 then l1 else MinInf)
    (if less_eq_eint u2 u1 then u1 else PlusInf);

widen_ivl :: Ivl -> Ivl -> Ivl;
widen_ivl a b =
  (if equal_ivl a bot_ivl then b
    else (if equal_ivl b bot_ivl then a else widen_ivl_core a b));

instance Core.Widening Ivl where {
  widen = widen_ivl;
};

narrow_ivl_td :: Ivl -> Ivl -> Ivl;
narrow_ivl_td (Ivl l1 u1) (Ivl l2 u2) =
  Ivl (if equal_eint l1 MinInf then l2 else l1)
    (if equal_eint u1 PlusInf then u2 else u1);

narrow_ivl :: Ivl -> Ivl -> Ivl;
narrow_ivl a b = narrow_ivl_td a b;

instance Core.Narrowing Ivl where {
  narrow = narrow_ivl;
};

instance Core.Warrowing Ivl where {
};

instance Core.Semilattice_sup Ivl where {
};

instance Core.Bounded_semilattice_sup_bot Ivl where {
};

instance Core.Bounded_warrowing Ivl where {
};

cinit_ivl_st :: Core.Resolved_st_q Ivl;
cinit_ivl_st =
  Core.Abs_resolved_st
    (Ivl MinInf PlusInf, (Ivl (Fin Core.zero_int) (Fin Core.zero_int), []));

ivl_top :: Ivl;
ivl_top = Ivl MinInf PlusInf;

ivl_times_core :: Ivl -> Ivl -> Ivl;
ivl_times_core (Ivl (Fin l1) (Fin u1)) (Ivl (Fin l2) (Fin u2)) =
  Ivl (Fin (Core.min (Core.times_int l1 l2)
             (Core.min (Core.times_int l1 u2)
               (Core.min (Core.times_int u1 l2) (Core.times_int u1 u2)))))
    (Fin (Core.max (Core.times_int l1 l2)
           (Core.max (Core.times_int l1 u2)
             (Core.max (Core.times_int u1 l2) (Core.times_int u1 u2)))));
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
minus_eint (Fin n) (Fin m) = Fin (Core.minus_int n m);
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
plus_eint (Fin n) (Fin m) = Fin (Core.plus_int n m);
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

aval_ivl :: Core.Aexp -> (String -> Ivl) -> Ivl;
aval_ivl (Core.N n) sigma = Ivl (Fin n) (Fin n);
aval_ivl (Core.V x) sigma = sigma x;
aval_ivl (Core.Plus a b) sigma = plus_ivl (aval_ivl a sigma) (aval_ivl b sigma);
aval_ivl (Core.Minus a b) sigma =
  minus_ivl (aval_ivl a sigma) (aval_ivl b sigma);
aval_ivl (Core.Times a b) sigma =
  times_ivl (aval_ivl a sigma) (aval_ivl b sigma);

meet_ivl :: Ivl -> Ivl -> Ivl;
meet_ivl (Ivl l1 u1) (Ivl l2 u2) =
  Ivl (if less_eq_eint l2 l1 then l1 else l2)
    (if less_eq_eint u1 u2 then u1 else u2);

afilter_ivl_st ::
  (String -> Bool) ->
    Core.Aexp -> Ivl -> Core.Resolved_st_q Ivl -> Core.Resolved_st_q Ivl;
afilter_ivl_st gs (Core.V x) a s =
  Core.update_resolved_st_q s (Core.location_of gs x)
    (meet_ivl a (Core.fun_of_resolved_st_q_for gs s x));
afilter_ivl_st gs (Core.Plus e1 e2) a s =
  (case Core.inv_conservative a
          (aval_ivl e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
afilter_ivl_st gs (Core.Minus e1 e2) a s =
  (case Core.inv_conservative a
          (aval_ivl e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
afilter_ivl_st gs (Core.Times e1 e2) a s =
  (case Core.inv_conservative a
          (aval_ivl e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
afilter_ivl_st gs (Core.N v) a s = s;

inf_ivl :: Ivl -> Ivl -> Ivl;
inf_ivl = meet_ivl;

inv_less_ivl :: Bool -> Ivl -> Ivl -> (Ivl, Ivl);
inv_less_ivl True (Ivl l1 u1) (Ivl l2 u2) =
  (inf_ivl (Ivl l1 u1) (Ivl MinInf (minus_eint u2 (Fin Core.one_int))),
    inf_ivl (Ivl l2 u2) (Ivl (plus_eint l1 (Fin Core.one_int)) PlusInf));
inv_less_ivl False (Ivl l1 u1) (Ivl l2 u2) =
  (inf_ivl (Ivl l1 u1) (Ivl l2 PlusInf), inf_ivl (Ivl l2 u2) (Ivl MinInf u1));

inv_eq_ivl :: Bool -> Ivl -> Ivl -> (Ivl, Ivl);
inv_eq_ivl True a1 a2 = (meet_ivl a1 a2, meet_ivl a1 a2);
inv_eq_ivl False a1 a2 = (a1, a2);

bfilter_ivl_st ::
  (String -> Bool) ->
    Core.Bexp -> Bool -> Core.Resolved_st_q Ivl -> Core.Resolved_st_q Ivl;
bfilter_ivl_st gs (Core.Less e1 e2) res s =
  (case inv_less_ivl res (aval_ivl e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
bfilter_ivl_st gs (Core.Not b) res s = bfilter_ivl_st gs b (not res) s;
bfilter_ivl_st gs (Core.And b1 b2) True s =
  bfilter_ivl_st gs b1 True (bfilter_ivl_st gs b2 True s);
bfilter_ivl_st gs (Core.And b1 b2) False s =
  Core.sup_resolved_st_q (bfilter_ivl_st gs b1 False s)
    (bfilter_ivl_st gs b2 False s);
bfilter_ivl_st gs (Core.Or b1 b2) True s =
  Core.sup_resolved_st_q (bfilter_ivl_st gs b1 True s)
    (bfilter_ivl_st gs b2 True s);
bfilter_ivl_st gs (Core.Or b1 b2) False s =
  bfilter_ivl_st gs b1 False (bfilter_ivl_st gs b2 False s);
bfilter_ivl_st gs (Core.Eqb e1 e2) res s =
  (case inv_eq_ivl res (aval_ivl e1 (Core.fun_of_resolved_st_q_for gs s))
          (aval_ivl e2 (Core.fun_of_resolved_st_q_for gs s))
    of {
    (a1, a2) -> afilter_ivl_st gs e1 a1 (afilter_ivl_st gs e2 a2 s);
  });
bfilter_ivl_st gs (Core.Bc v) uv s = s;

assume_not_ivl_st_for ::
  (String -> Bool) ->
    Core.Bexp -> Core.Resolved_st_q Ivl -> Core.Resolved_st_q Ivl;
assume_not_ivl_st_for source_global b s =
  bfilter_ivl_st source_global b False s;

assume_ivl_st_for ::
  (String -> Bool) ->
    Core.Bexp -> Core.Resolved_st_q Ivl -> Core.Resolved_st_q Ivl;
assume_ivl_st_for source_global b s = bfilter_ivl_st source_global b True s;

ivl_tf_st_for ::
  (String -> Bool) ->
    Core.Edge_action -> Core.Resolved_st_q Ivl -> Core.Resolved_st_q Ivl;
ivl_tf_st_for source_global Core.EA_Nop s = s;
ivl_tf_st_for source_global (Core.EA_Assign x a) s =
  Core.update_resolved_st_q s (Core.location_of source_global x)
    (aval_ivl a (Core.fun_of_resolved_st_q_for source_global s));
ivl_tf_st_for source_global (Core.EA_Random x) s =
  Core.update_resolved_st_q s (Core.location_of source_global x) ivl_top;
ivl_tf_st_for source_global (Core.EA_Assume b) s =
  assume_ivl_st_for source_global b s;
ivl_tf_st_for source_global (Core.EA_AssumeNot b) s =
  assume_not_ivl_st_for source_global b s;
ivl_tf_st_for source_global (Core.EA_Ret Nothing p) s = s;
ivl_tf_st_for source_global (Core.EA_Ret (Just a) p) s =
  Core.update_resolved_st_q s (Core.location_of source_global Core.ret_var)
    (aval_ivl a (Core.fun_of_resolved_st_q_for source_global s));
ivl_tf_st_for source_global (Core.EA_Check cnd) s = s;

ivl_enter_st_for ::
  (String -> Bool) ->
    [String] -> [Core.Aexp] -> Core.Resolved_st_q Ivl -> Core.Resolved_st_q Ivl;
ivl_enter_st_for source_global xs es s =
  Core.bind_formals_resolved_q source_global xs
    (map (\ e -> aval_ivl e (Core.fun_of_resolved_st_q_for source_global s)) es)
    (Core.enter_frame_D_resolved_q ivl_top s);

ivl_etf_st_for ::
  (String -> Bool) ->
    Core.Effectful_st_transfer_ext () (Core.Resolved_st_q Ivl) ();
ivl_etf_st_for gs =
  Core.unit_etf_st_of_transfer gs (ivl_tf_st_for gs) (ivl_enter_st_for gs);

ivl_exec_eqs ::
  (String -> Bool) ->
    (String -> Maybe (Core.Proc_decl_ext ())) ->
      [String] ->
        String ->
          Core.Com ->
            Core.Cfg_node ->
              Core.Strategy_tree Core.Cfg_node () (Core.Resolved_st_q Ivl);
ivl_exec_eqs gs pi ps mnm main =
  Core.side_cfg_T_eff_st (Core.compile_prog pi ps mnm main) (ivl_etf_st_for gs)
    Core.bot_resolved_st_q cinit_ivl_st ();

less_eint :: Eint -> Eint -> Bool;
less_eint a b = eint_le a b && not (eint_le b a);

interval_less_true :: Ivl -> Ivl -> Bool;
interval_less_true (Ivl l1 u1) (Ivl l2 u2) =
  not (less_eq_eint l1 u1) || (not (less_eq_eint l2 u2) || less_eint u1 l2);

interval_eq_true :: Ivl -> Ivl -> Bool;
interval_eq_true (Ivl l1 u1) (Ivl l2 u2) =
  not (less_eq_eint l1 u1) ||
    (not (less_eq_eint l2 u2) ||
      equal_eint l1 u1 && equal_eint l2 u2 && equal_eint l1 l2);

interval_less_false :: Ivl -> Ivl -> Bool;
interval_less_false (Ivl l1 u1) (Ivl l2 u2) =
  not (less_eq_eint l1 u1) || (not (less_eq_eint l2 u2) || less_eint u2 l1);

interval_eq_false :: Ivl -> Ivl -> Bool;
interval_eq_false (Ivl l1 u1) (Ivl l2 u2) =
  not (less_eq_eint l1 u1) ||
    (not (less_eq_eint l2 u2) || (less_eint u1 l2 || less_eint u2 l1));

interval_check_true :: Core.Bexp -> (String -> Ivl) -> Bool;
interval_check_true (Core.Bc v) d = v;
interval_check_true (Core.Not b) d = interval_check_false b d;
interval_check_true (Core.And b1 b2) d =
  interval_check_true b1 d && interval_check_true b2 d;
interval_check_true (Core.Or b1 b2) d =
  interval_check_true b1 d || interval_check_true b2 d;
interval_check_true (Core.Less a b) d =
  interval_less_true (aval_ivl a d) (aval_ivl b d);
interval_check_true (Core.Eqb a b) d =
  interval_eq_true (aval_ivl a d) (aval_ivl b d);

interval_check_false :: Core.Bexp -> (String -> Ivl) -> Bool;
interval_check_false (Core.Bc v) d = not v;
interval_check_false (Core.Not b) d = interval_check_true b d;
interval_check_false (Core.And b1 b2) d =
  interval_check_false b1 d || interval_check_false b2 d;
interval_check_false (Core.Or b1 b2) d =
  interval_check_false b1 d && interval_check_false b2 d;
interval_check_false (Core.Less a b) d =
  interval_less_false (aval_ivl a d) (aval_ivl b d);
interval_check_false (Core.Eqb a b) d =
  interval_eq_false (aval_ivl a d) (aval_ivl b d);

interval_classify_check :: Core.Bexp -> (String -> Ivl) -> Core.Check_result;
interval_classify_check c d =
  (if interval_check_true c d then Core.Check_Proved
    else (if interval_check_false c d then Core.Check_Refuted
           else Core.Check_Unknown));

analyse_interval_td_raw ::
  (String -> Bool) ->
    (String -> Maybe (Core.Proc_decl_ext ())) ->
      [String] ->
        String ->
          Core.Com -> Core.Sum Core.Cfg_node () -> Core.Resolved_st_q Ivl;
analyse_interval_td_raw gs pi ps mnm main =
  snd (Core.tD_side_warrowing_apinis_Interp_solve
        (ivl_exec_eqs gs pi ps mnm main)
        (Core.cfg_exit (Core.compile_prog pi ps mnm main)));

interval_td_check_report ::
  (String -> Bool) ->
    String ->
      Core.Imp_prog_ext () -> [(Core.Cfg_node, (Core.Bexp, Core.Check_result))];
interval_td_check_report gs mnm p =
  let {
    raw = analyse_interval_td_raw gs (Core.prog_table p) (Core.prog_procs p) mnm
            (Core.prog_main p);
  } in Core.classify_checks (Core.prog_cfg mnm p)
         (Core.side_env (Core.fun_of_resolved_st_q_for gs . raw))
         interval_classify_check;

analyse_interval_td_report ::
  Core.Imp_prog_ext () -> [(Core.Cfg_node, (Core.Bexp, Core.Check_result))];
analyse_interval_td_report p =
  interval_td_check_report (Core.declared_global p) Core.prog_main_name p;

}
