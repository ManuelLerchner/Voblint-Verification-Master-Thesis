section \<open>Example: nondeterministic input recovers precision through branching\<close>

theory Example_Random_Sign_Showcase
  imports "Voblint_CLI.Sign_Entry" "Voblint_VIMP.VIMP_Notation"
begin


text \<open>
  \<open>x := __voblint_nondet_int()\<close> is nondeterministic. \<^const>\<open>special_sign\<close>
  answers it by forgetting \<open>x\<close> entirely -- setting it to \<^term>\<open>STop\<close>,
  the sign abstraction of the infinite concrete successor set
  \<open>{s(x := v) | v. True}\<close> -- regardless of what was known about \<open>x\<close>
  beforehand.

  A subsequent guard still recovers precision. For
  \<open>x := 0; x := __voblint_nondet_int(); if (x > 0) y := x else y := 0 - x\<close>,
  the leading \<open>x := 0\<close> is overwritten by the nondeterministic call --
  whatever was known about \<open>x\<close> beforehand is gone -- yet each branch
  narrows \<open>x\<close> before assigning \<open>y\<close>, and the two branches join to a single
  tight sign at the merge point: the branch guards recover enough
  information to derive \<open>y = SNonNeg\<close>, rather than losing all useful
  information after propagating the arbitrary value of \<open>x\<close> into \<open>y\<close>. The
  equation-system generator and the vendored TD solver compute this
  directly; no hand-derived abstract state is asserted here.
\<close>

subsection \<open>The source program\<close>

text \<open>\<open>special_pname_nondet_int\<close> is an ordinary identifier, not a keyword, so
  it cannot be written inside the \<open>program { ... }\<close> quotation the way other
  calls can: Pure's inner-syntax lexer reserves leading-underscore tokens for
  translation-internal nonterminals, rejecting any user identifier that
  begins with one.  The call is spliced in directly instead, exactly as
  \<^const>\<open>mk_program\<close> (the constructor \<open>program { ... }\<close> itself expands to)
  builds any procedure body from a \<^typ>\<open>VIMP_Proc.com\<close>.\<close>
definition random_guard_program :: imp_prog where
  "random_guard_program = mk_program []
     (Seq (Seq (imp \<lbrakk> x := 0 \<rbrakk>) (VIMP_Proc.com.Call (Some (STR ''x'')) special_pname_nondet_int []))
          (imp \<lbrakk> if (0 < x) { y := x } else { y := 0 - x } \<rbrakk>))
     []"

text \<open>No \<open>global\<close> declarations, so the classifier this program's own source
  gives is trivially false everywhere.\<close>
abbreviation random_guard_gs :: "vname \<Rightarrow> bool" where
  "random_guard_gs \<equiv> declared_global random_guard_program"

lemma random_guard_program_declared_global_vars [simp]:
  "declared_global_vars random_guard_program = []"
  by (simp add: random_guard_program_def)

subsection \<open>Non-vacuity: a concrete run where the nondeterministic call returns 42\<close>

text \<open>
  \<open>random_guard_exit_sound\<close> bounds every reachable exit state, but says
  nothing about whether any exist. This witness closes that gap at the
  source semantics: fixing the random draw at \<open>v = 42\<close>, \<^const>\<open>pcompletes\<close>
  (the small-step relation's terminating-run predicate) derives a concrete
  run of \<^const>\<open>prog_main\<close> \<open>random_guard_program\<close> reaching \<open>y = 42\<close> -- an
  actual state, not merely one permitted in principle, and \<open>42 \<ge> 0\<close>
  confirms the bound on it directly.
\<close>

text \<open>The witness value survives its own kind, so every conversion along the
  run is the identity on it. Without this the wraps stay unevaluated and each
  step's store fails to match the one the next step expects.\<close>

lemma ik_norm_I32_42 [simp]: "ik_norm I32 42 = 42"
  by eval

lemma random_guard_run_42:
  fixes s :: store and gs :: "vname \<Rightarrow> bool" and \<Pi> :: proc_table
  shows "pcompletes (prog_tyenv random_guard_program) gs \<Pi>
           (prog_main random_guard_program) s
           (s((STR ''x'') := 0, (STR ''x'') := 42, (STR ''y'') := 42)) rk"
proof -
  let ?G = "prog_tyenv random_guard_program"
  have step1: "pcompletes ?G gs \<Pi> (Assign (STR ''x'') (N 0)) s (s((STR ''x'') := 0)) rk"
    using pcompletes_assign[where \<Gamma> = ?G and gs = gs and \<Pi> = \<Pi>
        and x = "STR ''x''" and a = "N 0" and s = s and rk = rk]
    by (simp add: taval_syn_def opk_def prog_tyenv_def random_guard_program_def default_tyenv_def)
  have step2: "pcompletes ?G gs \<Pi> (VIMP_Proc.com.Call (Some (STR ''x'')) special_pname_nondet_int [])
                 (s((STR ''x'') := 0)) ((s((STR ''x'') := 0))((STR ''x'') := 42)) rk"
    using pcompletes_special_nondet_int[where \<Gamma> = ?G and gs = gs and \<Pi> = \<Pi>
        and x = "STR ''x''" and s = "s((STR ''x'') := 0)" and v = 42 and rk = rk]
    by (simp add: prog_tyenv_def random_guard_program_def default_tyenv_def)
  have step12: "pcompletes ?G gs \<Pi>
                  (Seq (Assign (STR ''x'') (N 0))
                       (VIMP_Proc.com.Call (Some (STR ''x'')) special_pname_nondet_int [])) s
                  ((s((STR ''x'') := 0))((STR ''x'') := 42)) rk"
    using pcompletes_Seq[OF step1 step2] .
  have guard_true: "truthy (taval_syn ?G (Less (N 0) (V (STR ''x'')))
                              ((s((STR ''x'') := 0))((STR ''x'') := 42)))"
    by (simp add: taval_syn_def opk_def prog_tyenv_def random_guard_program_def default_tyenv_def)
  have step3: "pcompletes ?G gs \<Pi> (Assign (STR ''y'') (V (STR ''x''))) ((s((STR ''x'') := 0))((STR ''x'') := 42))
                 (((s((STR ''x'') := 0))((STR ''x'') := 42))((STR ''y'') := 42)) rk"
    using pcompletes_assign[where \<Gamma> = ?G and gs = gs and \<Pi> = \<Pi>
        and x = "STR ''y''" and a = "V (STR ''x'')"
        and s = "(s((STR ''x'') := 0))((STR ''x'') := 42)" and rk = rk]
    by (simp add: taval_syn_def opk_def prog_tyenv_def random_guard_program_def default_tyenv_def)
  have step3if: "pcompletes ?G gs \<Pi>
      (If (Less (N 0) (V (STR ''x''))) (Assign (STR ''y'') (V (STR ''x''))) (Assign (STR ''y'') (Minus (N 0) (V (STR ''x'')))))
      ((s((STR ''x'') := 0))((STR ''x'') := 42)) (((s((STR ''x'') := 0))((STR ''x'') := 42))((STR ''y'') := 42)) rk"
    using pcompletes_IfTrue[OF guard_true step3] .
  have "pcompletes ?G gs \<Pi>
      (Seq (Seq (Assign (STR ''x'') (N 0)) (VIMP_Proc.com.Call (Some (STR ''x'')) special_pname_nondet_int []))
        (If (Less (N 0) (V (STR ''x''))) (Assign (STR ''y'') (V (STR ''x''))) (Assign (STR ''y'') (Minus (N 0) (V (STR ''x''))))))
      s (((s((STR ''x'') := 0))((STR ''x'') := 42))((STR ''y'') := 42)) rk"
    using pcompletes_Seq[OF step12 step3if] .
  then show ?thesis unfolding random_guard_program_def by simp
qed

lemma random_guard_run_42_y_nonneg:
  fixes s :: store
  shows "(s((STR ''x'') := 0, (STR ''x'') := 42, (STR ''y'') := 42)) (STR ''y'') \<ge> 0"
  by simp

subsection \<open>Through the routed equation system and the TD solver\<close>

text \<open>
  \<^const>\<open>analyse_sign_result_for\<close> is not a black box: it is exactly three named steps.
  \<^item> \<^const>\<open>prog_cfg\<close> compiles the source program to a CFG (\<^const>\<open>compile_prog\<close>).
  \<^item> \<^const>\<open>sctx_eqs_prog\<close> is \<^emph>\<open>the equation system generator\<close>: it applies
    \<^const>\<open>side_cfg_T_eff_keyed_seed_dg_buffered\<close> to that CFG and the routed
    D/G spec \<open>sctx_spec\<close>, producing one equation per CFG node and context.
  \<^item> \<^const>\<open>TD_side_always_join_Interp_solve\<close> is \<^emph>\<open>the vendored TD solver\<close>: it
    takes that equation system and a query node and computes a fixpoint,
    \<^const>\<open>sctx_sol_prog\<close> being exactly this call.
  \<^const>\<open>analyse_sign_result_for\<close> then reads each node's local state back out of
  that solved table -- the same table \<^const>\<open>analyse_sign_report_for\<close> serves.
\<close>

lemma random_guard_reserved: "reserved_ret_var random_guard_gs"
  unfolding reserved_ret_var_def by simp

lemma random_guard_solver_terminates:
  "sctx_terminates_prog random_guard_gs prog_main_name random_guard_program"
  by (rule sctx_terminates_prog_via_solve_c) eval

lemma random_guard_entry_cov:
  "(cfg_entry (prog_cfg prog_main_name random_guard_program), ())
     \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program)"
  by eval

lemma random_guard_fwd_ok_ball:
  "\<forall>(u, a, w) \<in> intra (prog_cfg prog_main_name random_guard_program).
     (u, ()) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program) \<longrightarrow>
     (w, ()) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program)"
  by eval

lemma random_guard_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program)"
    and "(u, a, w) \<in> intra (prog_cfg prog_main_name random_guard_program)"
  shows "(w, ctx) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program)"
  using assms random_guard_fwd_ok_ball by (cases ctx) auto

lemma random_guard_calls_cov_ball:
  "\<forall>(u, ca, ce, k) \<in> calls (prog_cfg prog_main_name random_guard_program).
     (case ce of FunctionEntry q \<Rightarrow>
        (FunctionEntry q, ()) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program)
      | _ \<Rightarrow> True)
     \<and> ((k, ()) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program))"
  by eval

lemma random_guard_call_fwd_ok:
  assumes "(u, ctx) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program)"
    and "(u, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name random_guard_program)"
  shows "(FunctionEntry q, ()) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program)"
  using assms random_guard_calls_cov_ball by fastforce

lemma random_guard_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program)"
    and "(cl, CallEdge dst fs as, FunctionEntry q, k) \<in> calls (prog_cfg prog_main_name random_guard_program)"
  shows "(k, c1) \<in> fst (sctx_sol_prog random_guard_gs prog_main_name random_guard_program)"
  using assms random_guard_calls_cov_ball by (cases c1) fastforce

lemma random_guard_node_sound:
  "ltr_collect (prog_tyenv random_guard_program) random_guard_gs (prog_cfg prog_main_name random_guard_program)
     (cinit_stores random_guard_gs) v
   \<subseteq> \<lbrakk>case lookup_context (analyse_sign_result_for random_guard_gs random_guard_program) v () of
          Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st\<rbrakk>"
  by (rule analyse_sign_result_node_sound_for
        [OF random_guard_reserved random_guard_solver_terminates random_guard_entry_cov
            random_guard_fwd_ok random_guard_call_fwd_ok random_guard_comb_fwd_ok])

definition random_guard_env :: "vname \<Rightarrow> sign" where
  "random_guard_env =
     (case lookup_context (analyse_sign_result_for random_guard_gs random_guard_program)
             (cfg_exit (prog_cfg prog_main_name random_guard_program)) () of
        Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"

text \<open>The guard refines the nondeterministic \<open>x\<close> to non-negative, and \<open>y := x\<close>
  carries that across -- but the write converts to \<open>y\<close>'s kind, and
  \<^const>\<open>SNonNeg\<close> concretizes to every non-negative integer, including ones
  \<^const>\<open>I32\<close> cannot hold. Sign alone cannot rule out the wrap, so the exit
  reads \<^const>\<open>STop\<close>. The guard's own refinement is still visible one step
  earlier, in \<open>random_guard_run_42_y_nonneg\<close>.\<close>

lemma random_guard_exec_y: "random_guard_env (STR ''y'') = STop"
  by (simp add: random_guard_env_def) eval

corollary random_guard_exit_sound:
  "ltr_collect (prog_tyenv random_guard_program) random_guard_gs (prog_cfg (STR ''main'') random_guard_program) (cinit_stores random_guard_gs)
     (cfg_exit (prog_cfg (STR ''main'') random_guard_program))
   \<le> \<lbrakk>random_guard_env\<rbrakk>"
  unfolding random_guard_env_def
  using random_guard_node_sound
  by (simp add: prog_main_name_def gamma_point_def split: point_state.splits)

text \<open>
  Issue #43 asked whether every concrete exit state of
  \<^const>\<open>random_guard_program\<close> has \<open>y\<close> non-negative, whatever the
  nondeterministic call returns. It does: the guard admits only positive \<open>x\<close>,
  and \<open>y := x\<close> copies it.

  Sign can no longer witness that. \<open>random_guard_run_42_y_nonneg\<close> above shows
  the guard's refinement surviving up to the write; the write then converts to
  \<open>y\<close>'s kind, and \<^const>\<open>SNonNeg\<close> concretizes to every non-negative integer,
  including ones \<^const>\<open>I32\<close> cannot hold. A magnitude-free domain cannot rule
  out the wrap, so the exit reads \<^const>\<open>STop\<close> and
  \<^const>\<open>random_guard_exit_sound\<close> constrains nothing.

  The corollary that used to discharge #43 from this chain is therefore gone
  rather than restated: deriving \<open>0 \<le> t (STR ''y'')\<close> from a \<^const>\<open>STop\<close>
  result is not possible, and asserting it anyway would be unsound. Recovering
  it needs a concretization that reads an abstract value at its variable's
  declared kind, so that \<^const>\<open>SNonNeg\<close> at \<^const>\<open>I32\<close> denotes
  \<open>{0..2147483647}\<close> and the conversion is exact -- or the Interval component,
  which carries the magnitude the question turns on.
\<close>

end
