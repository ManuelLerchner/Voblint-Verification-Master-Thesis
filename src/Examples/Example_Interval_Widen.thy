section \<open>Example: Interval Widening on a Diverging Loop\<close>

text \<open>\label{sec:example-interval-widen}\<close>

theory Example_Interval_Widen
  imports Interval_Domain TD_Widen_Interface
begin

text \<open>
  Widening demo for \<^verbatim>\<open>x := 0; while True do x := x + 1\<close>.

  Join-only TD (see @{text TD_Interface}) would not stabilise at the loop header;
  @{const TD_plain_widen} (vendored widen-at-dynamic-points solver) applies
  interval widening so the fixpoint computation terminates.

  This instantiates the widen-only backend from @{text TD_Widen_Interface}, not
  the full widen/narrow @{text TD_WN_Interface} solver.
\<close>

definition incr_loop_prog :: com where
  "incr_loop_prog =
     (''x'' ::= N 0) ;; WHILE (Bc True) DO (''x'' ::= Plus (V ''x'') (N 1))"


definition sigma_x :: "ivl \<Rightarrow> vname \<Rightarrow> ivl" where
  "sigma_x s v = (if v = ''x'' then s else ivl_bot)"

definition tf_init :: "ivl \<Rightarrow> ivl" where
  "tf_init s = assign_ivl ''x'' (N 0) (sigma_x s) ''x''"

definition tf_step :: "ivl \<Rightarrow> ivl" where
  "tf_step s = assign_ivl ''x'' (Plus (V ''x'') (N 1)) (sigma_x s) ''x''"

definition ivl_head :: ivl where
  "ivl_head = Ivl (Fin 0) PlusInf"

definition ivl_body :: ivl where
  "ivl_body = Ivl (Fin 1) PlusInf"

value "tf_init ivl_top"
value "tf_step (Ivl (Fin 0) (Fin 0))"


datatype LP = LInit | LAfter | LHead | LBody

fun constr_sys :: "LP \<Rightarrow> (LP, ivl) strategy_tree" where
  "constr_sys LInit = Answer ivl_top"
| "constr_sys LAfter = Query LInit (\<lambda>s. Answer (tf_init s))"
| "constr_sys LHead =
     Query LBody (\<lambda>s_body. Query LAfter (\<lambda>s_after. Answer (s_body \<squnion> s_after)))"
| "constr_sys LBody = Query LHead (\<lambda>s. Answer (tf_step s))"


interpretation loop_widen: TD_plain_widen constr_sys widen_ivl
proof
  fix a b :: ivl
  show "a \<squnion> b \<le> widen_ivl a b" by (rule sup_le_widen_ivl)
next
  fix a b :: ivl
  assume "b \<le> a"
  show "widen_ivl a b = a" by (rule widen_ivl_id[OF \<open>b \<le> a\<close>])
qed

definition widen_solution :: "LP \<Rightarrow> ivl" where
  "widen_solution pp =
     (case loop_widen.solve LHead pp of None \<Rightarrow> bot | Some v \<Rightarrow> v)"

term "widen_solution LHead"

\<comment> \<open>
  @{const TD_plain_widen.solve} has no code equations yet (unlike the
  executable join-only solver in @{text TD_Interface}).  Spot-check
  widening and transfer functions directly:
\<close>

value "widen_ivl (Ivl (Fin 0) (Fin 2)) (Ivl (Fin 0) (Fin 3))"
\<comment> \<open>upper bound grows \<Rightarrow> widen to \<^verbatim>\<open>[0, +inf)\<close>\<close>

value "widen_ivl ivl_head (tf_step ivl_head)"
\<comment> \<open>loop body step from \<^verbatim>\<open>[0, +inf)\<close> stays stable under widen\<close>

end

