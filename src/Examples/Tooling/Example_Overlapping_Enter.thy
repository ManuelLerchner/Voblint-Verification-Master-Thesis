theory Example_Overlapping_Enter
  imports
    "Voblint_Analysis_Interval.Interval_Kind"
    "Voblint_Nonrelational.Nonrelational_Analysis"
    "Voblint_VIMP.VIMP_Notation"
begin

unbundle default_st_syntax

section \<open>One concrete call, two overlapping entry alternatives, two contexts\<close>

text \<open>
  A call's entry transfer answers a \<^emph>\<open>list\<close> of (continuation, callee entry)
  alternatives, and an entry-state route selects one context per alternative. When two
  alternatives both cover the same concrete call, that call is represented under two
  contexts at once. This theory builds that situation on the core VIMP non-relational
  analysis at the Interval domain, all variables at \<^const>\<open>I32\<close>, by overriding the
  component's entry alone. Alternative 1 is the stock entry: the formal \<open>a\<close> holds
  \<open>[1, 1]\<close> and the continuation is the caller's state. Alternative 2 forgets the formals
  on entry \<^emph>\<open>and\<close> forgets the caller's own \<open>x\<close> in its continuation, both to
  \<^const>\<open>KTop\<close>. The concrete call with \<open>x = 1\<close> lies in both entries and both
  continuations, and the entry-state route sends the two entries to the contexts
  \<open>[KD I32 [1, 1]]\<close> and \<open>[KTop]\<close>.

  Forgetting \<open>x\<close> itself, rather than an artificial marker, keeps the pairing of a
  continuation with its entry observable per alternative, while each continuation stays a
  sound description of the caller: \<^const>\<open>KTop\<close> describes every value.

  The executable half pins the solved equations: the two alternatives stay
  distinguishable through the call and return programs, and each is read back and joined.
  The relational half interprets the routed context locale at this instance, so the
  generic routed soundness argument covers a list-valued entry without change, and shows
  the one concrete caller activation admitted under both contexts. The negative half
  replaces the entry by one answering no alternative: then no callee context is solved,
  the continuation stays \<^const>\<open>Bot\<close>, and the entry law fails.
\<close>

subsection \<open>The program and its graph\<close>

definition ov_program :: imp_prog where
  "ov_program = program {
     fun p(a) { return a; }
     fun main() { x = 1; y = p(x); }
   }"

definition ov_cfg :: "(var_id, exp) gcfg" where
  "ov_cfg = elab_cfg ov_program []"

abbreviation ov_kenv :: kenv where "ov_kenv \<equiv> kenv_of []"

abbreviation x_id :: var_id where "x_id \<equiv> ScopedId (STR ''main'') (STR ''x'')"
abbreviation y_id :: var_id where "y_id \<equiv> ScopedId (STR ''main'') (STR ''y'')"
abbreviation a_id :: var_id where "a_id \<equiv> ScopedId (STR ''p'') (STR ''a'')"

abbreviation p_entry :: cfg_node where "p_entry \<equiv> FunctionEntry (STR ''p'')"
abbreviation p_result :: cfg_node where "p_result \<equiv> FunctionResult (STR ''p'')"

abbreviation ov_ca :: "(var_id, exp) gcall_action" where
  "ov_ca \<equiv> CallEdge (Some y_id) [a_id] [TVar I32 x_id]"

abbreviation ov_ci :: "(var_id, exp) gcall_info" where
  "ov_ci \<equiv> call_info_of ov_ca (STR ''p'')"

text \<open>Node layout, computed rather than assumed: \<open>main\<close> assigns at \<open>Statement 2\<close>,
  calls at \<open>Statement 3\<close> and continues at \<open>Statement 4\<close>.\<close>

lemma ov_calls: "calls ov_cfg = {(Statement 3, ov_ca, p_entry, Statement 4)}"
  by eval

lemma ov_cfg_finite: "finite (intra ov_cfg)" "finite (calls ov_cfg)"
  by (simp_all add: ov_cfg_def elab_cfg_def compile_prog_finite)

subsection \<open>The overriding entry\<close>

text \<open>\<open>forget_vars vs\<close> sets every variable of \<open>vs\<close> to \<^const>\<open>KTop\<close>, so it only
  enlarges what a state describes.\<close>

definition forget_vars :: "var_id list \<Rightarrow> 'a::kind_int_domain tst lifted \<Rightarrow> 'a tst lifted" where
  "forget_vars vs = map_lift (\<lambda>st. fold (\<lambda>v st. st\<langle>nonrel_loc v := KTop\<rangle>) vs st)"

lemma nonrel_rd_forget:
  "nonrel_rd (fold (\<lambda>v st. st\<langle>nonrel_loc v := KTop\<rangle>) vs st)
     = (\<lambda>v. if v \<in> set vs then KTop else nonrel_rd (st :: 'a::kind_int_domain tst) v)"
  by (induction vs arbitrary: st) (auto simp: fun_eq_iff)

lemma gamma_exec_forget_vars: "gamma_exec \<kappa> d \<subseteq> gamma_exec \<kappa> (forget_vars vs d)"
  by (cases d) (auto simp: forget_vars_def nonrel_rd_forget gamma_tabs_def)

text \<open>The stock alternatives, followed by each with \<open>x\<close> forgotten in the continuation and
  the formals forgotten in the entry.\<close>

definition ov_enter ::
  "sem_conf \<Rightarrow> kenv \<Rightarrow> exp gchannel \<Rightarrow> (var_id, exp) gcall_info
   \<Rightarrow> 'a::kind_int_domain tst lifted \<times> 'a tst lifted \<Rightarrow> ('a tst lifted \<times> 'a tst lifted) list" where
  "ov_enter sem \<kappa> ch ci p =
     (let alts = ls_enter (nonrel_exec_spec sem \<kappa>) ch ci p
      in alts @ map (\<lambda>(c, e). (forget_vars [x_id] c, forget_vars (ci_formals ci) e)) alts)"

definition ov_comp :: "(var_id, exp, ivl tst lifted) glocal_spec" where
  "ov_comp = (nonrel_exec_spec default_sem_conf ov_kenv)\<lparr>ls_enter := ov_enter default_sem_conf ov_kenv\<rparr>"

definition ov_spec :: "(var_id, exp, pp \<times> ivl kd list, (unit, ivl kd list) global_unknown, unit,
    ivl tst lifted, ivl tst lifted) gdg_spec" where
  "ov_spec = dg_spec_of ov_comp"

text \<open>The alternatives the specification's entry answers at a caller state.\<close>

definition ov_alts :: "(var_id, exp) gcall_info \<Rightarrow> ivl tst lifted
    \<Rightarrow> (ivl tst lifted \<times> ivl tst lifted) list" where
  "ov_alts ci d = ls_enter ov_comp (ls_channel ov_comp d) ci (d, d)"

lemma enter_ov_spec: "enter\<^sup>\<sharp> ov_spec ci = local_enter_transfer (ov_alts ci)"
  by (simp add: ov_spec_def ov_alts_def[abs_def])

text \<open>The entry-state route of \<^const>\<open>nonrel_es_ctx\<close>: a context is the formals'
  values in the entered state.\<close>

definition ov_route ::
  "pp \<Rightarrow> ivl kd list \<Rightarrow> ivl tst lifted \<Rightarrow> (var_id, exp) gcall_action \<Rightarrow> ivl kd list" where
  "ov_route u ctx d ca = nonrel_es_ctx is_global d ca"

subsection \<open>The override is sound\<close>

text \<open>The stock alternatives are among the override's, so the entry law carries over;
  every other field is the stock component's.\<close>

lemma ov_enter_sound:
  "mcp_sem.gsound_enter eval (kind_conv \<kappa>) is_global (gamma_exec \<kappa>)
     (ov_enter sem \<kappa> :: _ \<Rightarrow> _ \<Rightarrow> 'a::kind_int_domain tst lifted \<times> _ \<Rightarrow> _)"
proof -
  note stock = mcp_sem.sound_local_spec_enterD[OF nonrel_exec_spec_sound[of \<kappa> sem, where 'a = 'a]]
  have sub: "\<And>ch ci p. set (ls_enter (nonrel_exec_spec sem \<kappa>) ch ci p)
      \<subseteq> set (ov_enter sem \<kappa> ch ci (p :: 'a tst lifted \<times> 'a tst lifted))"
    by (auto simp: ov_enter_def Let_def)
  show ?thesis
    using stock sub unfolding mcp_sem.gsound_enter_def by blast
qed

lemma ov_comp_sound:
  "mcp_sem.gsound_local_spec eval ReturnVar (kind_conv ov_kenv) is_global (gamma_exec ov_kenv) ov_comp"
  unfolding ov_comp_def
  by (rule mcp_sem.sound_local_spec_update_enter[OF nonrel_exec_spec_sound ov_enter_sound])

lemma analysis_contract_ov_spec:
  "ganalysis_contract eval ReturnVar (kind_conv ov_kenv) is_global ov_spec
     (\<lambda>d _. gamma_exec ov_kenv d)"
  unfolding ov_spec_def by (rule mcp_sem.dg_spec_of_contract[OF ov_comp_sound])

subsection \<open>The routed equation system, solved\<close>

text \<open>The equations the non-relational pipeline builds with entry-state contexts, at the
  overriding specification: same generator, route, buffered seed protocol and solver.\<close>

definition ov_eqs :: "(pp \<times> ivl kd list, (unit, ivl kd list) global_unknown,
    (ivl tst lifted, ivl tst lifted) dg_state) eqsT" where
  "ov_eqs = compiled_routed_eqs_for (Analysis_Global ()) Analysis_Global Activation_Seed ov_route
     ov_spec ov_cfg (Lifted (nonrel_init_st [])) Bot"

definition ov_sol :: "(pp \<times> ivl kd list) set
    \<times> (pp \<times> ivl kd list + (unit, ivl kd list) global_unknown
         \<Rightarrow> (ivl tst lifted, ivl tst lifted) dg_state)" where
  "ov_sol = TD_side_rule_Interp_solve Globals_Join ov_eqs (cfg_exit ov_cfg, [])"

abbreviation ov_contexts :: "pp \<Rightarrow> ivl kd list set" where
  "ov_contexts v \<equiv> snd ` Set.filter (\<lambda>(v', _). v' = v) (fst ov_sol)"

abbreviation ov_read :: "pp \<Rightarrow> ivl kd list \<Rightarrow> var_id \<Rightarrow> ivl kd lifted" where
  "ov_read v ctx x \<equiv> map_lift (\<lambda>st. nonrel_rd st x) (dg_local (snd ov_sol (Inl (v, ctx))))"

abbreviation ov_seed :: "ivl kd list \<Rightarrow> var_id \<Rightarrow> ivl kd lifted" where
  "ov_seed ctx x \<equiv> map_lift (\<lambda>st. nonrel_rd st x)
     (dg_local (snd ov_sol (Inr (Activation_Seed p_entry ctx))))"

abbreviation ov_caller :: "ivl tst lifted" where
  "ov_caller \<equiv> dg_local (snd ov_sol (Inl (Statement 3, [])))"

text \<open>What alternative \<open>i\<close> contributes at the continuation, traversed on its own
  against the solution.\<close>

definition ov_alt_answer :: "nat \<Rightarrow> ivl tst lifted" where
  "ov_alt_answer i =
     dg_local (traverse_program
       (routed_call_alternative_program ov_spec Analysis_Global Activation_Seed ov_route
          (\<lambda>d. d = Bot) [] ov_ca (Statement 3) (STR ''p'') (ov_alts ov_ci ov_caller ! i))
       (snd ov_sol))"

abbreviation ov_alt_read :: "nat \<Rightarrow> var_id \<Rightarrow> ivl kd lifted" where
  "ov_alt_read i x \<equiv> map_lift (\<lambda>st. nonrel_rd st x) (ov_alt_answer i)"

abbreviation ov_ctx_exact :: "ivl kd list" where "ov_ctx_exact \<equiv> [KD I32 (Ivl (Fin 1) (Fin 1))]"
abbreviation ov_ctx_top :: "ivl kd list" where "ov_ctx_top \<equiv> [KTop]"

text \<open>The full range of \<^const>\<open>I32\<close>: what the callee returns from an unknown argument.\<close>

abbreviation i32_range :: "ivl kd" where
  "i32_range \<equiv> KD I32 (Ivl (Fin (- 2147483648)) (Fin 2147483647))"

text \<open>The solver runs once. Every executable observation below is a projection of this
  snapshot.\<close>

lemma ov_solution_snapshot:
  "TD_side_rule_Interp_solve_c Globals_Join ov_eqs (cfg_exit ov_cfg, []) \<noteq> None
   \<and> ov_contexts p_entry = {ov_ctx_exact, ov_ctx_top}
   \<and> ov_contexts (Statement 3) = {[]}
   \<and> (cfg_entry ov_cfg, []) \<in> fst ov_sol
   \<and> ov_seed ov_ctx_exact a_id = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))
   \<and> ov_seed ov_ctx_top a_id = Lifted KTop
   \<and> ov_read p_entry ov_ctx_exact a_id = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))
   \<and> ov_read p_entry ov_ctx_top a_id = Lifted KTop
   \<and> ov_read p_result ov_ctx_exact ReturnVar = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))
   \<and> ov_read p_result ov_ctx_top ReturnVar = Lifted i32_range
   \<and> ov_alt_read 0 x_id = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))
   \<and> ov_alt_read 0 y_id = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))
   \<and> ov_alt_read 1 x_id = Lifted KTop
   \<and> ov_alt_read 1 y_id = Lifted i32_range
   \<and> ov_read (Statement 4) [] x_id = Lifted KTop
   \<and> ov_read (Statement 4) [] y_id = Lifted i32_range
   \<and> ov_caller = Lifted ((nonrel_init_st [])\<langle>nonrel_loc x_id := KD I32 (Ivl (Fin 1) (Fin 1))\<rangle>)
   \<and> map (\<lambda>(c, e). ov_route (Statement 3) [] e ov_ca) (ov_alts ov_ci ov_caller)
       = [ov_ctx_exact, ov_ctx_top]
   \<and> (\<forall>(u, ctx) \<in> fst ov_sol. \<forall>(u', a, v) \<in> intra ov_cfg. u = u' \<longrightarrow> (v, ctx) \<in> fst ov_sol)
   \<and> (\<forall>(cl, ctx) \<in> fst ov_sol. \<forall>(cl', ca, ce, cont) \<in> calls ov_cfg.
        cl = cl' \<longrightarrow> (cont, ctx) \<in> fst ov_sol)
   \<and> (\<forall>(u, ctx) \<in> fst ov_sol. u = Statement 3 \<longrightarrow>
        (\<forall>(c, e) \<in> set (ov_alts ov_ci (dg_local (snd ov_sol (Inl (u, ctx))))).
          (p_entry, ov_route u ctx e ov_ca) \<in> fst ov_sol))"
  by eval

lemma ov_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join ov_eqs (cfg_exit ov_cfg, []) \<noteq> None"
  by (insert ov_solution_snapshot, elim conjE, assumption)

lemma ov_entry_solved: "(cfg_entry ov_cfg, []) \<in> fst ov_sol"
  by (insert ov_solution_snapshot, elim conjE, assumption)

lemma ov_caller_eq:
  "ov_caller = Lifted ((nonrel_init_st [])\<langle>nonrel_loc x_id := KD I32 (Ivl (Fin 1) (Fin 1))\<rangle>)"
  by (insert ov_solution_snapshot, elim conjE, assumption)

lemma ov_route_alts:
  "map (\<lambda>(c, e). ov_route (Statement 3) [] e ov_ca) (ov_alts ov_ci ov_caller)
     = [ov_ctx_exact, ov_ctx_top]"
  by (insert ov_solution_snapshot, elim conjE, assumption)

lemma ov_fwd_closed:
  "\<forall>(u, ctx) \<in> fst ov_sol. \<forall>(u', a, v) \<in> intra ov_cfg. u = u' \<longrightarrow> (v, ctx) \<in> fst ov_sol"
  by (insert ov_solution_snapshot, elim conjE, assumption)

lemma ov_comb_fwd_closed:
  "\<forall>(cl, ctx) \<in> fst ov_sol. \<forall>(cl', ca, ce, cont) \<in> calls ov_cfg.
     cl = cl' \<longrightarrow> (cont, ctx) \<in> fst ov_sol"
  by (insert ov_solution_snapshot, elim conjE, assumption)

lemma ov_enter_fwd_at_call:
  "\<forall>(u, ctx) \<in> fst ov_sol. u = Statement 3 \<longrightarrow>
     (\<forall>(c, e) \<in> set (ov_alts ov_ci (dg_local (snd ov_sol (Inl (u, ctx))))).
       (p_entry, ov_route u ctx e ov_ca) \<in> fst ov_sol)"
  by (insert ov_solution_snapshot, elim conjE, assumption)

subsubsection \<open>1. One call, two contexts\<close>

text \<open>The single call to \<open>p\<close> reaches two callee contexts, one per alternative, while
  \<open>main\<close> runs only under the root context.\<close>

lemma ov_two_contexts: "ov_contexts p_entry = {ov_ctx_exact, ov_ctx_top}"
  by (insert ov_solution_snapshot, elim conjE, assumption)

lemma ov_caller_root_only: "ov_contexts (Statement 3) = {[]}"
  by (insert ov_solution_snapshot, elim conjE, assumption)

subsubsection \<open>2. Each seed carries its own alternative's entry\<close>

text \<open>The exact alternative seeds its context with the argument \<open>1\<close>; the forgetful one seeds
  its context with the formal forgotten.\<close>

lemma ov_seed_exact: "ov_seed ov_ctx_exact a_id = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))"
  by (insert ov_solution_snapshot, elim conjE, assumption)

lemma ov_seed_forgotten: "ov_seed ov_ctx_top a_id = Lifted KTop"
  by (insert ov_solution_snapshot, elim conjE, assumption)

text \<open>The callee's entry unknown is its seed: the seed read-back is its only
  contribution.\<close>

lemma ov_entry_reads_seed:
  "ov_read p_entry ov_ctx_exact a_id = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))"
  "ov_read p_entry ov_ctx_top a_id = Lifted KTop"
  by (insert ov_solution_snapshot, elim conjE, assumption)+

subsubsection \<open>3. Each activation returns what it was entered with, and stays paired\<close>

text \<open>The exact context returns the exact argument; the forgetful one returns the whole
  range of the result's kind.\<close>

lemma ov_result_exact:
  "ov_read p_result ov_ctx_exact ReturnVar = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))"
  by (insert ov_solution_snapshot, elim conjE, assumption)

lemma ov_result_forgotten: "ov_read p_result ov_ctx_top ReturnVar = Lifted i32_range"
  by (insert ov_solution_snapshot, elim conjE, assumption)

text \<open>
  Continuation and entry stay correlated per alternative. The joined continuation cannot
  show it, since the domain is non-relational. Traversing each alternative's own program
  against the solution does: alternative 1's return writes \<open>y\<close> from the exact callee into
  its untouched continuation, alternative 2's writes the callee's unknown result into its
  continuation with \<open>x\<close> forgotten.
\<close>

lemma ov_alt1_pairing:
  "ov_alt_read 0 x_id = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))"
  "ov_alt_read 0 y_id = Lifted (KD I32 (Ivl (Fin 1) (Fin 1)))"
  by (insert ov_solution_snapshot, elim conjE, assumption)+

lemma ov_alt2_pairing:
  "ov_alt_read 1 x_id = Lifted KTop"
  "ov_alt_read 1 y_id = Lifted i32_range"
  by (insert ov_solution_snapshot, elim conjE, assumption)+

subsubsection \<open>4. The continuation holds the join of both alternatives\<close>

text \<open>The caller's continuation joins what both alternatives return, so it keeps neither
  alternative's precision.\<close>

lemma ov_continuation_join:
  "ov_read (Statement 4) [] x_id = Lifted KTop"
  "ov_read (Statement 4) [] y_id = Lifted i32_range"
  by (insert ov_solution_snapshot, elim conjE, assumption)+

subsection \<open>Soundness through the routed context layer\<close>

text \<open>
  \<^const>\<open>routed_entry_context_rel\<close> at the override's alternatives is the context policy
  this instance keys its collecting semantics by. It admits a context for a concrete call
  whenever some alternative covers the caller store in its continuation and the entered
  store in its entry, and routes to that context.
\<close>

abbreviation ov_R :: "(var_id, exp, ivl kd list) gcontext_policy" where
  "ov_R \<equiv> routed_entry_context_rel ov_alts (\<lambda>d _. gamma_exec ov_kenv d) (snd ov_sol)
            Analysis_Global ov_route"

abbreviation ov_call_enter :: "store \<Rightarrow> store" where
  "ov_call_enter \<equiv> vimp.gcall_enter ov_kenv ov_ca"

text \<open>The concrete caller store at the call site: \<open>x = 1\<close>, everything else \<open>0\<close>.\<close>

definition ov_caller_store :: store where
  "ov_caller_store = (\<lambda>_. 0)(x_id := 1)"

lemma ov_caller_store_covered: "ov_caller_store \<in> gamma_exec ov_kenv ov_caller"
proof -
  have z: "(\<lambda>_. 0) \<in> gamma_tabs ov_kenv (nonrel_rd (nonrel_init_st [] :: ivl tst))"
    by (rule subsetD[OF nonrel_init_sound])
       (simp add: init_stores_def all_in_kinds_def)
  have "ov_caller_store \<in> gamma_tabs ov_kenv
      ((nonrel_rd (nonrel_init_st [] :: ivl tst))(x_id := KD I32 (Ivl (Fin 1) (Fin 1))))"
  proof (rule gamma_tabsI, goal_cases Kinds Values)
    case Kinds show ?case
      by (auto simp: in_kinds_def ov_caller_store_def kenv_of_def simp del: ik_range_iff)
  next
    case (Values v) show ?case
      using gamma_tabsD(2)[OF z, of v]
      by (auto simp: ov_caller_store_def kenv_of_def simp del: ik_range_iff)
  qed
  then show ?thesis by (simp add: ov_caller_eq)
qed

text \<open>The stock alternative is first, so the stock entry law covers the entered store.\<close>

definition ov_entry1 :: "ivl tst lifted" where
  "ov_entry1 = transfer_lift st_is_bot
     (enter_st default_sem_conf ov_kenv (ls_channel ov_comp ov_caller) [a_id] [TVar I32 x_id])
     ov_caller"

lemma ov_alts_caller:
  "ov_alts ov_ci ov_caller
     = [(ov_caller, ov_entry1), (forget_vars [x_id] ov_caller, forget_vars [a_id] ov_entry1)]"
  by (simp add: ov_alts_def ov_comp_def ov_enter_def nonrel_exec_spec_def ov_entry1_def)

lemma ov_routes:
  "ov_route (Statement 3) [] ov_entry1 ov_ca = ov_ctx_exact"
  "ov_route (Statement 3) [] (forget_vars [a_id] ov_entry1) ov_ca = ov_ctx_top"
  using ov_route_alts by (simp_all add: ov_alts_caller)

lemma ov_entry1_covered:
  "ov_call_enter ov_caller_store \<in> gamma_exec ov_kenv ov_entry1"
proof -
  have ch: "geval_query.channel_holds eval (ls_channel ov_comp ov_caller) ov_caller_store"
    by (rule mcp_sem.ls_channel_sound[OF ov_comp_sound ov_caller_store_covered])
  note law = mcp_sem.sound_local_spec_enterD[OF nonrel_exec_spec_sound[of ov_kenv default_sem_conf,
      where 'a = ivl], unfolded mcp_sem.gsound_enter_def, rule_format]
  from law[where s = ov_caller_store and p = "(ov_caller, ov_caller)"
      and ch = "ls_channel ov_comp ov_caller" and ci = ov_ci] ov_caller_store_covered ch
  show ?thesis by (simp add: nonrel_exec_spec_def ov_entry1_def)
qed

lemma ov_ci_edge: "CallEdge (ci_dst ov_ci) (ci_formals ov_ci) (ci_args ov_ci) = ov_ca"
  by simp

lemma ov_exact_context_admitted:
  "ov_ctx_exact \<in> ov_R (Statement 3) [] ov_ci ov_caller_store (ov_call_enter ov_caller_store)"
  unfolding routed_entry_context_rel_def ov_alts_caller
  using ov_caller_store_covered ov_entry1_covered ov_routes
  by (simp add: ov_ci_edge, intro exI[of _ ov_caller] exI[of _ ov_entry1], simp)

lemma ov_top_context_admitted:
  "ov_ctx_top \<in> ov_R (Statement 3) [] ov_ci ov_caller_store (ov_call_enter ov_caller_store)"
  unfolding routed_entry_context_rel_def ov_alts_caller
  using subsetD[OF gamma_exec_forget_vars ov_caller_store_covered, of "[x_id]"]
    subsetD[OF gamma_exec_forget_vars ov_entry1_covered, of "[a_id]"] ov_routes
  by (simp add: ov_ci_edge,
      intro exI[of _ "forget_vars [x_id] ov_caller"] exI[of _ "forget_vars [a_id] ov_entry1"], simp)

text \<open>The one concrete call admits its callee activation under both contexts. The caller
  itself stays at the root context.\<close>

lemma ov_two_contexts_admitted:
  "ov_ctx_exact \<in> ov_R (Statement 3) [] ov_ci ov_caller_store (ov_call_enter ov_caller_store)
   \<and> ov_ctx_top \<in> ov_R (Statement 3) [] ov_ci ov_caller_store (ov_call_enter ov_caller_store)
   \<and> ov_ctx_exact \<noteq> ov_ctx_top"
  using ov_exact_context_admitted ov_top_context_admitted by simp

subsubsection \<open>The routed context locale at this instance\<close>

text \<open>The buffered post-solution, reconciled with the unbuffered generator the routed
  locale is stated over. The reconciliation inspects only that the entry is a pure
  function of the caller state, not how many alternatives it answers.\<close>

lemma ov_pp_routed:
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. Analysis_Global ()) ov_route
        (\<lambda>ctx' src a. dg_spec_edge_program ov_spec a src Analysis_Global)
        (routed_call_program ov_spec Analysis_Global Activation_Seed (static_resolve ov_cfg)
           (\<lambda>d. d = Bot))
        (routed_entry_seed_programs Activation_Seed)
        ov_cfg Bot (Lifted (nonrel_init_st [])) Bot)
     (cfg_exit ov_cfg, []) (snd ov_sol) (fst ov_sol)"
proof -
  have pp: "part_post_solution ov_eqs (cfg_exit ov_cfg, []) (snd ov_sol) (fst ov_sol)"
    unfolding ov_sol_def
    by (rule TD_side_rule_Interp.part_post_solution_of_solve_c[OF ov_terminates_c])
  have wf: "dg_spec_wf ov_spec"
    unfolding ov_spec_def by (rule dg_spec_wf_dg_spec_of)
  show ?thesis
    by (rule pp_routed_of_buffered[OF wf _
          pp[unfolded ov_eqs_def compiled_routed_eqs_for_def bot_lifted_eq]]) simp
qed

lemma ov_dg_base:
  "dg_context_base ov_spec (\<lambda>d _. gamma_exec ov_kenv d) ov_cfg (Analysis_Global ()) Analysis_Global
     ov_route (routed_call_program ov_spec Analysis_Global Activation_Seed (static_resolve ov_cfg)
       (\<lambda>d. d = Bot))
     (routed_entry_seed_programs Activation_Seed) Bot (Lifted (nonrel_init_st [])) Bot
     (snd ov_sol) (fst ov_sol) (cfg_exit ov_cfg, []) (solved_local_reader (fst ov_sol) (snd ov_sol))
     (gamma_exec ov_kenv)"
proof (unfold_locales, goal_cases CmbWf ExtraWf FinE PP SgCov SgUncov Fwd)
  case CmbWf show ?case
    unfolding ov_spec_def by (rule sp_wf_routed_call_program[OF dg_spec_wf_dg_spec_of])
next
  case ExtraWf then show ?case by (rule sp_wf_routed_entry_seed_programs)
next
  case FinE show ?case by (rule ov_cfg_finite(1))
next
  case PP show ?case by (rule post_bounded_of_part_post_solution[OF ov_pp_routed])
next
  case (SgCov v c) then show ?case by simp
next
  case (SgUncov v c) then show ?case by simp
next
  case (Fwd u a v c) then show ?case using ov_fwd_closed by blast
qed

text \<open>Adequacy, totality and return forwarding: every alternative the relation admits
  is one the entry ran, its context is solved, and the stock alternative covers every
  covered caller.\<close>

interpretation ov_routed: grouted_context eval ReturnVar "kind_conv ov_kenv" is_global ov_spec
  "\<lambda>d _. gamma_exec ov_kenv d" ov_cfg "Analysis_Global ()" Analysis_Global ov_route
  Bot "Lifted (nonrel_init_st [])" Bot "snd ov_sol" "fst ov_sol" "(cfg_exit ov_cfg, [])"
  "solved_local_reader (fst ov_sol) (snd ov_sol)" Activation_Seed "static_resolve ov_cfg"
  "\<lambda>d. d = Bot" "gamma_exec ov_kenv" ov_R
proof (rule grouted_context.intro, goal_cases Act Base Ax)
  case Act
  show ?case by (rule gdg_context_activation.intro[OF analysis_contract_ov_spec ov_dg_base])
next
  case Base
  show ?case
  proof (rule routed_context_base.intro[OF ov_dg_base], unfold_locales,
      goal_cases FinC CallsUnique SeedNeBuf SeedNeGlobal IsBotBot IsBotSound ResolveSound)
    case FinC show ?case by (rule ov_cfg_finite(2))
  next
    case CallsUnique show ?case
      unfolding ov_cfg_def by (rule elab_cfg_calls_source_unique)
  next
    case (SeedNeBuf p ctx) show ?case by simp
  next
    case (SeedNeGlobal p ctx v) show ?case by simp
  next
    case IsBotBot show ?case by simp
  next
    case (IsBotSound d g) then show ?case by simp
  next
    case (ResolveSound u ctx dst pars args p cont s)
    then show ?case by (simp add: ov_cfg_finite(2))
  qed
next
  case Ax
  show ?case
  proof (unfold_locales, goal_cases Adequate Total CombFwd)
    case (Adequate u ctx dst pars args p cont s ctx')
    let ?ci = "call_info_of (CallEdge dst pars args) p"
    let ?d = "dg_local (snd ov_sol (Inl (u, ctx)))"
    obtain cont' entry where mem: "(cont', entry) \<in> set (ov_alts ?ci ?d)"
        and ccov: "s \<in> gamma_exec ov_kenv cont'"
        and ecov: "vimp.gcall_enter ov_kenv (CallEdge dst pars args) s \<in> gamma_exec ov_kenv entry"
        and req: "ctx' = ov_route u ctx entry (CallEdge dst pars args)"
      using Adequate(4) unfolding routed_entry_context_rel_def by auto
    have edge: "u = Statement 3" "CallEdge dst pars args = ov_ca" "p = STR ''p''"
      using Adequate(2) by (simp_all add: ov_calls)
    have "(FunctionEntry p, ctx') \<in> fst ov_sol"
      using ov_enter_fwd_at_call Adequate(1) mem req unfolding edge by fastforce
    then show ?case
      using mem ccov ecov req
        enter_runs_local_enter_transfer_mk_dg_man[of "ov_alts ?ci" ?d Analysis_Global "snd ov_sol"]
        enter_deps_local_enter_transfer_mk_dg_man[of "ov_alts ?ci" ?d Analysis_Global "snd ov_sol"]
      by (fastforce simp: enter_ov_spec)
  next
    case (Total u ctx dst pars args p cont s)
    let ?ci = "call_info_of (CallEdge dst pars args) p"
    let ?d = "dg_local (snd ov_sol (Inl (u, ctx)))"
    have ch: "geval_query.channel_holds eval (ls_channel ov_comp ?d) s"
      by (rule mcp_sem.ls_channel_sound[OF ov_comp_sound Total(3)])
    note law = mcp_sem.sound_local_spec_enterD[OF ov_comp_sound,
        unfolded mcp_sem.gsound_enter_def, rule_format]
    have "entry_pairs_cover (gamma_exec ov_kenv) s
        (vimp.gcall_enter ov_kenv (CallEdge dst pars args) s) (ov_alts ?ci ?d)"
      using law[where s = s and p = "(?d, ?d)" and ch = "ls_channel ov_comp ?d" and ci = ?ci]
        Total(3) ch
      unfolding entry_pairs_cover_def ov_alts_def by fastforce
    then show ?case by (rule routed_entry_context_rel_total)
  next
    case (CombFwd cl c1 dst pars args p cont)
    then show ?case using ov_comb_fwd_closed by auto
  qed
qed

text \<open>The payoff of the interpretation: every store the activation-indexed collecting
  semantics reaches under \<open>ov_R\<close> is described by the solved state at its context.\<close>

lemma ov_activation_collect_sound:
  "\<A>\<^bsub>ov_kenv,ov_R,[],ov_cfg,init_stores ov_kenv\<^esub> v c
   \<subseteq> gamma_exec ov_kenv (solved_local_reader (fst ov_sol) (snd ov_sol) (Inl (v, c)))"
  unfolding activation_collect_def
proof (rule ov_routed.activation_collect_dg_sound)
  show "(cfg_entry ov_cfg, []) \<in> fst ov_sol" by (rule ov_entry_solved)
  show "init_stores ov_kenv \<subseteq> gamma_exec ov_kenv (Lifted (nonrel_init_st []))"
    using nonrel_init_sound by simp
  show "bot \<le> genv Analysis_Global (snd ov_sol)" by simp
qed

subsection \<open>Negative: an empty entry list cannot cover a live caller\<close>

text \<open>The entry law asks for an alternative covering every covered caller, so an entry
  answering no alternative violates it at the caller store above.\<close>

lemma ov_empty_pairs_never_cover:
  "\<not> entry_pairs_cover (gamma_exec ov_kenv) ov_caller_store (ov_call_enter ov_caller_store) []"
  by simp

definition ov_empty_comp :: "(var_id, exp, ivl tst lifted) glocal_spec" where
  "ov_empty_comp = (nonrel_exec_spec default_sem_conf ov_kenv)\<lparr>ls_enter := (\<lambda>ch ci p. [])\<rparr>"

lemma ov_empty_enter_unsound:
  "\<not> mcp_sem.gsound_enter eval (kind_conv ov_kenv) is_global (gamma_exec ov_kenv)
       (ls_enter ov_empty_comp)"
  unfolding mcp_sem.gsound_enter_def ov_empty_comp_def
  using ov_caller_store_covered
    mcp_sem.ls_channel_sound[OF ov_comp_sound ov_caller_store_covered]
  by fastforce

text \<open>What the missing obligation would let through. With the entry answering \<open>[]\<close>, the
  solver seeds no callee, solves no context at \<open>p\<close>, and leaves the continuation
  \<^const>\<open>Bot\<close>, although the concrete run reaches it.\<close>

definition ov_empty_eqs :: "(pp \<times> ivl kd list, (unit, ivl kd list) global_unknown,
    (ivl tst lifted, ivl tst lifted) dg_state) eqsT" where
  "ov_empty_eqs = compiled_routed_eqs_for (Analysis_Global ()) Analysis_Global Activation_Seed
     ov_route (dg_spec_of ov_empty_comp) ov_cfg (Lifted (nonrel_init_st [])) Bot"

definition ov_empty_sol :: "(pp \<times> ivl kd list) set
    \<times> (pp \<times> ivl kd list + (unit, ivl kd list) global_unknown
         \<Rightarrow> (ivl tst lifted, ivl tst lifted) dg_state)" where
  "ov_empty_sol = TD_side_rule_Interp_solve Globals_Join ov_empty_eqs (cfg_exit ov_cfg, [])"

lemma ov_empty_solution_snapshot:
  "TD_side_rule_Interp_solve_c Globals_Join ov_empty_eqs (cfg_exit ov_cfg, []) \<noteq> None
   \<and> (\<forall>(v, ctx) \<in> fst ov_empty_sol. v \<noteq> p_entry)
   \<and> dg_local (snd ov_empty_sol (Inl (Statement 4, []))) = Bot"
  by eval

lemma ov_empty_terminates_c:
  "TD_side_rule_Interp_solve_c Globals_Join ov_empty_eqs (cfg_exit ov_cfg, []) \<noteq> None"
  by (insert ov_empty_solution_snapshot, elim conjE, assumption)

lemma ov_empty_no_callee_context:
  "\<forall>(v, ctx) \<in> fst ov_empty_sol. v \<noteq> p_entry"
  by (insert ov_empty_solution_snapshot, elim conjE, assumption)

lemma ov_empty_continuation_bot:
  "dg_local (snd ov_empty_sol (Inl (Statement 4, []))) = Bot"
  by (insert ov_empty_solution_snapshot, elim conjE, assumption)

unbundle no default_st_syntax

end
