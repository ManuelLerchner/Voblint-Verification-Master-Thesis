theory Example_Sign_DG_Overlapping_Enter
  imports
    "Voblint_Analysis_Sign.Sign_Analyses"
    "Voblint_VIMP.VIMP_Notation"
begin

section \<open>One concrete call, two overlapping entry alternatives, two contexts\<close>

text \<open>
  A call's entry transfer answers a \<^emph>\<open>list\<close> of (continuation, callee entry)
  alternatives, and the entry-state route selects one context per alternative. When two
  alternatives both cover the same concrete call, that call is represented under two
  contexts at once. This theory builds exactly that situation on the stock executable Sign
  specification by overriding \<^const>\<open>dgs_enter\<close> alone: alternative 1 enters the callee
  exactly (the formal \<open>a\<close> is \<^const>\<open>SPos\<close>, the continuation's \<open>x\<close> untouched), alternative 2
  enters it with every formal forgotten to \<^const>\<open>STop\<close> \<^emph>\<open>and\<close> forgets the continuation's
  own \<open>x\<close> to \<^const>\<open>STop\<close> too. The concrete call with \<open>x = 1\<close> lies in both entries and both
  continuations, and the route sends the two entries to \<open>[SPos]\<close> and \<open>[STop]\<close>.

  Reusing \<open>x\<close> itself (rather than an artificial marker) keeps the pairing of a continuation
  with its entry observable per alternative --- alternative 1 answers \<open>(x, y) = (SPos, SPos)\<close>,
  alternative 2 answers \<open>(STop, STop)\<close> --- while also making each alternative's continuation
  a genuine, sound description of the caller's state: \<open>STop\<close> covers whatever \<open>x\<close> actually is,
  so both alternatives cover the one real caller store, and the routed context locale's
  totality obligation holds honestly rather than vacuously.

  The executable half pins the solved table: two alternatives stay distinguishable through
  the whole call/combine machinery, and each is read back and joined correctly. The
  soundness half shows the same thing relationally: the existing generic routed soundness
  bridge (\<^theory>\<open>Voblint_Exec.Routed_Exec_Refinement\<close>) already supports list-valued,
  non-deterministic entry without any change to it --- this example is what supplies and
  discharges the corresponding non-deterministic entry obligations for the first time, and
  goes on to show the one concrete caller activation genuinely admitted under both
  \<open>[SPos]\<close> and \<open>[STop]\<close> via \<open>ov_R\<close>.
\<close>

subsection \<open>The program and its graph\<close>

definition ov_program :: imp_prog where
  "ov_program = program {
     fun p(a) { return a; }
     fun main() { x = 1; y = p(x); }
   }"

abbreviation ov_gs :: "vname \<Rightarrow> bool" where
  "ov_gs \<equiv> declared_global ov_program"

definition ov_pi :: proc_table where "ov_pi = prog_table ov_program"
definition ov_procs :: "pname list" where "ov_procs = prog_procs ov_program"

definition ov_cfg :: cfg where
  "ov_cfg = compile_prog ov_pi ov_procs"

definition ov_ep :: "sign exec_dg_st \<Rightarrow> bool" where
  "ov_ep = resolved_st_q_is_bot_for (declared_global_vars ov_program)"

abbreviation p_entry :: cfg_node where "p_entry \<equiv> FunctionEntry (STR ''p'')"
abbreviation p_result :: cfg_node where "p_result \<equiv> FunctionResult (STR ''p'')"

abbreviation ov_ca :: call_action where
  "ov_ca \<equiv> CallEdge (Some (STR ''y'')) [(STR ''a'')] [V (STR ''x'')]"

text \<open>Node layout, computed rather than assumed: \<open>p\<close>'s \<open>return a\<close> is \<open>Statement 0\<close>;
  \<open>main\<close> assigns at \<open>Statement 2\<close>, calls at \<open>Statement 3\<close>, continues at \<open>Statement 4\<close>.\<close>

lemma ov_calls_shape:
  "\<forall>(u, ca, ce, cont) \<in> calls ov_cfg.
     u = Statement 3 \<and> ca = ov_ca \<and> ce = p_entry \<and> cont = Statement 4"
  unfolding ov_cfg_def ov_pi_def ov_procs_def ov_program_def by eval

lemma ov_call_edge:
  "(Statement 3, ov_ca, p_entry, Statement 4) \<in> calls ov_cfg"
  unfolding ov_cfg_def ov_pi_def ov_procs_def ov_program_def by eval

subsection \<open>The overriding entry transfer\<close>

definition forget_formals ::
  "(vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> sign exec_dg_st \<Rightarrow> sign exec_dg_st" where
  "forget_formals \<G> ci s =
     foldl (\<lambda>s f. update_resolved_st_q s (location_of \<G> f) STop) s (ci_formals ci)"

definition forget_var ::
  "(vname \<Rightarrow> bool) \<Rightarrow> vname \<Rightarrow> sign \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> sign exec_dg_st lifted" where
  "forget_var \<G> v w = map_lift (\<lambda>s. update_resolved_st_q s (location_of \<G> v) w)"

text \<open>Alternative 1 is the stock singleton entry, continuation untouched. Alternative 2
  forgets the formals on entry \<^emph>\<open>and\<close> forgets the caller's own \<open>x\<close> in its continuation to
  \<^const>\<open>STop\<close>: a real, sound weakening (\<open>STop\<close> covers whatever \<open>x\<close> actually was), not an
  artificial tag on a name the program never uses. Every store in alternative 1's entry is
  in alternative 2's, so the two overlap; every store covered by alternative 1's
  continuation is covered by alternative 2's too (\<open>STop\<close> is the top of the lattice), so both
  continuations cover the one real caller state --- the totality this override must satisfy
  is not vacuous.\<close>

definition ov_enter ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool) \<Rightarrow> call_info
   \<Rightarrow> sign exec_dg_st lifted \<Rightarrow> sign exec_dg_st lifted enter_result list" where
  "ov_enter \<G> ep ci d =
     (let entered = transfer_lift ep (sign_enter_st_for \<G> ci) d
      in [(d, entered),
          (forget_var \<G> (STR ''x'') STop d, map_lift (forget_formals \<G> ci) entered)])"

definition ov_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (sign exec_dg_st \<Rightarrow> bool)
   \<Rightarrow> (pp \<times> sign list, (unit, sign list) routed_gk, unit,
        sign exec_dg_st lifted, sign exec_dg_st lifted) dg_spec" where
  "ov_spec \<G> ep = (sign_conf_spec \<G> ep)
     \<lparr> dgs_enter := (\<lambda>ci. local_enter_transfer (ov_enter \<G> ep ci)) \<rparr>"

declare ov_spec_def [code_unfold]

text \<open>Only the entry differs; every other field is \<^const>\<open>sign_conf_spec\<close>'s.\<close>

lemma dg_spec_step_ov_spec [simp]:
  "dg_spec_step (ov_spec \<G> ep) a = dg_spec_step (sign_conf_spec \<G> ep) a"
  by (cases a) (simp_all add: ov_spec_def)

lemma dgs_combine_env_ov_spec [simp]:
  "combine_env\<^sup># (ov_spec \<G> ep) = combine_env\<^sup># (sign_conf_spec \<G> ep)"
  by (simp add: ov_spec_def)

lemma dgs_combine_assign_ov_spec [simp]:
  "combine_assign\<^sup># (ov_spec \<G> ep) = combine_assign\<^sup># (sign_conf_spec \<G> ep)"
  by (simp add: ov_spec_def)

lemma dgs_enter_ov_spec [simp]:
  "enter\<^sup># (ov_spec \<G> ep) ci = local_enter_transfer (ov_enter \<G> ep ci)"
  by (simp add: ov_spec_def)

lemma dgs_query_ov_spec [simp]:
  "dgs_query (ov_spec \<G> ep) = dgs_query (sign_conf_spec \<G> ep)"
  by (simp add: ov_spec_def)

text \<open>The override runs its continuation once wherever the stock specification
  does: only the entry changed, and it answers its alternatives outright.\<close>

lemma dg_spec_wf_ov_spec [intro, simp]: "dg_spec_wf (ov_spec \<G> ep)"
proof (unfold dg_spec_wf_def, intro conjI allI impI)
  show "sp_wf (dg_spec_step (ov_spec \<G> ep) a ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>))"
    if "\<forall>q. sp_wf (A q)" for a d key A
    using that by (simp add: dg_spec_wf_step_ask[OF dg_spec_wf_sign_conf_spec])
next
  show "sp_wf (dgs_query (ov_spec \<G> ep) ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>) q)"
    if "\<forall>q. sp_wf (A q)" for d key A q
    using that by (simp add: dg_spec_wf_query[OF dg_spec_wf_sign_conf_spec])
next
  fix ci d key
  show "sp_wf (enter\<^sup># (ov_spec \<G> ep) ci (mk_dg_man d key))"
    by (simp add: local_enter_transfer_def)
next
  fix ci d key ex
  show "sp_wf (dg_spec_combine_transfer (ov_spec \<G> ep) ci (mk_dg_man d key) ex)"
    unfolding dg_spec_combine_transfer_def dgs_combine_env_ov_spec dgs_combine_assign_ov_spec
    by (simp add: sign_conf_spec_def local_state_dg_spec_st_for_lifted_def local_dg_spec_def
        local_combine_transfer_def)
qed

text \<open>Entry is absent from \<^locale>\<open>analysis_contract\<close>, so the override inherits the
  stock specification's contract outright.\<close>

lemma analysis_contract_ov_spec:
  assumes exact: "\<And>s. ep s = is_empty_state (fun_of_resolved_st_q_for \<G> s)"
  shows "analysis_contract (ov_spec \<G> ep) (sign_conf_gamma \<G>) \<G>"
proof -
  interpret stock: analysis_contract "sign_conf_spec \<G> ep" "sign_conf_gamma \<G>" \<G>
    by (rule sign_conf_sound_exec[OF exact])
  show ?thesis
  proof (unfold_locales, goal_cases)
    case 1 show ?case by (rule dg_spec_wf_ov_spec)
  next
    case (2 d d' g g') then show ?case by (rule stock.gammaDG_mono)
  next
    case (3 a \<tau> src gk)
    show ?case using stock.step_sound by (simp add: dg_spec_edge_program_def)
  next
    case (4 s dc \<tau> gk t de ci)
    show ?case using stock.combine_sound[where ci = ci and dc = dc and de = de
          and \<tau> = \<tau> and gk = gk, OF 4(1) 4(2)]
      by (simp add: dg_spec_combine_transfer_def)
  qed
qed

subsection \<open>The routed equation system, solved\<close>

text \<open>\<^const>\<open>sign_es_rule.equations\<close>'s construction at the overriding specification: same
  generator, same route, same buffered seed protocol, same plain-join solver.\<close>

definition ov_eqs ::
  "(pp \<times> sign list, (unit, sign list) routed_gk,
    (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "ov_eqs =
     routed_node_rhs_buffered intra_predecessor_addr_list call_site_list (\<lambda>_. Analysis_Global ())
       (exec_formals_route ov_gs)
       (\<lambda>ctx' src a. dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ()))
       (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
          (static_resolve ov_cfg) (\<lambda>d. d = Bot))
       (routed_entry_seed_programs Activation_Seed)
       ov_cfg Bot (Lifted cinit_sign_st) Bot"

definition ov_sol ::
  "(pp \<times> sign list) set \<times>
   (pp \<times> sign list + (unit, sign list) routed_gk
      \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "ov_sol = TD_side_always_join_Interp_solve ov_eqs (cfg_exit ov_cfg, [])"

definition ov_result :: "(sign list, sign abs_state) analysis_result" where
  "ov_result = Analysis_Result (fst ov_sol)
     (\<lambda>v ctx. readback_result_value ov_gs (canonicalize_lift ov_ep (locals (snd ov_sol (Inl (v, ctx))))))"

abbreviation ov_read :: "cfg_node \<Rightarrow> sign list \<Rightarrow> vname \<Rightarrow> sign lifted" where
  "ov_read v ctx x \<equiv> map_lift (\<lambda>st. st x) (lookup_context ov_result v ctx)"

abbreviation ov_seed :: "sign list \<Rightarrow> vname \<Rightarrow> sign lifted" where
  "ov_seed ctx x \<equiv> map_lift (\<lambda>s. fun_of_resolved_st_q_for ov_gs s x)
                     (locals (snd ov_sol (Inr (Activation_Seed p_entry ctx))))"

lemmas ov_unfold = ov_result_def ov_sol_def ov_eqs_def ov_cfg_def ov_pi_def ov_procs_def
  ov_ep_def ov_program_def

definition ov_alt_answer :: "nat \<Rightarrow> sign exec_dg_st lifted" where
  "ov_alt_answer i =
     (let caller = locals (snd ov_sol (Inl (Statement 3, [])));
          alts = ov_enter ov_gs ov_ep (call_info_of ov_ca (STR ''p'')) caller
      in locals (traverse_program
           (routed_call_alternative_program (ov_spec ov_gs ov_ep) (Analysis_Global ())
              Activation_Seed (exec_formals_route ov_gs) (\<lambda>d. d = Bot)
              [] ov_ca (Statement 3) (STR ''p'') (alts ! i))
           (snd ov_sol)))"

abbreviation ov_alt_read :: "nat \<Rightarrow> vname \<Rightarrow> sign lifted" where
  "ov_alt_read i x \<equiv>
     map_lift (\<lambda>s. fun_of_resolved_st_q_for ov_gs s x) (ov_alt_answer i)"

definition ov_caller_store :: store where
  "ov_caller_store = (\<lambda>_. 0)(STR ''x'' := 1)"

text \<open>The solver result is evaluated once. Every executable observation below is a
  logical projection of this snapshot, so adding a witness does not rerun the equation
  system.\<close>

lemma ov_solution_snapshot_raw:
  "(let sol = ov_sol;
        result = Analysis_Result (fst sol)
          (\<lambda>v ctx. readback_result_value ov_gs
            (canonicalize_lift ov_ep (locals (snd sol (Inl (v, ctx))))));
        read = (\<lambda>v ctx x. map_lift (\<lambda>st. st x) (lookup_context result v ctx));
        seed = (\<lambda>ctx x. map_lift (\<lambda>s. fun_of_resolved_st_q_for ov_gs s x)
          (locals (snd sol (Inr (Activation_Seed p_entry ctx)))));
        alt_answer = (\<lambda>i.
          let caller = locals (snd sol (Inl (Statement 3, [])));
              alts = ov_enter ov_gs ov_ep (call_info_of ov_ca (STR ''p'')) caller
          in locals (traverse_program
            (routed_call_alternative_program (ov_spec ov_gs ov_ep) (Analysis_Global ())
              Activation_Seed (exec_formals_route ov_gs) (\<lambda>d. d = Bot)
              [] ov_ca (Statement 3) (STR ''p'') (alts ! i))
            (snd sol)))
     in TD_side_always_join_Interp_solve_c ov_eqs (cfg_exit ov_cfg, []) \<noteq> None
      \<and> contexts_at result p_entry = {[SPos], [STop]}
      \<and> contexts_at result (Statement 3) = {[]}
      \<and> seed [SPos] (STR ''a'') = Lifted SPos
      \<and> seed [STop] (STR ''a'') = Lifted STop
      \<and> read p_entry [SPos] (STR ''a'') = Lifted SPos
      \<and> read p_entry [STop] (STR ''a'') = Lifted STop
      \<and> read p_result [SPos] ret_var = Lifted SPos
      \<and> read p_result [STop] ret_var = Lifted STop
      \<and> map_lift (\<lambda>s. fun_of_resolved_st_q_for ov_gs s (STR ''y''))
          (alt_answer 0) = Lifted SPos
      \<and> map_lift (\<lambda>s. fun_of_resolved_st_q_for ov_gs s (STR ''x''))
          (alt_answer 0) = Lifted SPos
      \<and> map_lift (\<lambda>s. fun_of_resolved_st_q_for ov_gs s (STR ''y''))
          (alt_answer 1) = Lifted STop
      \<and> map_lift (\<lambda>s. fun_of_resolved_st_q_for ov_gs s (STR ''x''))
          (alt_answer 1) = Lifted STop
      \<and> read (Statement 4) [] (STR ''x'') = Lifted STop
      \<and> read (Statement 4) [] (STR ''y'') = Lifted STop
      \<and> locals (snd sol (Inl (Statement 3, []))) =
          update_resolved_st_q_lift (Lifted cinit_sign_st)
            (location_of ov_gs (STR ''x'')) SPos
      \<and> exec_formals_route ov_gs (Statement 3) []
          (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
            (locals (snd sol (Inl (Statement 3, []))))) ov_ca = [SPos]
      \<and> forget_var ov_gs (STR ''x'') STop
          (locals (snd sol (Inl (Statement 3, [])))) =
          update_resolved_st_q_lift (Lifted cinit_sign_st)
            (location_of ov_gs (STR ''x'')) STop
      \<and> exec_formals_route ov_gs (Statement 3) []
          (map_lift (forget_formals ov_gs (call_info_of ov_ca (STR ''p'')))
            (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
              (locals (snd sol (Inl (Statement 3, [])))))) ov_ca = [STop]
      \<and> (\<forall>(u, ctx) \<in> fst sol. \<forall>(u', a, v) \<in> intra ov_cfg.
            u = u' \<longrightarrow> (v, ctx) \<in> fst sol)
      \<and> (\<forall>(cl, ctx) \<in> fst sol. \<forall>(cl', ca, ce, cont) \<in> calls ov_cfg.
            cl = cl' \<longrightarrow> (cont, ctx) \<in> fst sol)
      \<and> (\<forall>(u, ctx) \<in> fst sol. u = Statement 3 \<longrightarrow>
            (\<forall>(cont', entry) \<in> set (ov_enter ov_gs ov_ep
                (call_info_of ov_ca (STR ''p'')) (locals (snd sol (Inl (u, ctx))))).
              (p_entry, exec_formals_route ov_gs u ctx entry ov_ca) \<in> fst sol)))"
  unfolding ov_sol_def ov_eqs_def ov_cfg_def ov_pi_def ov_procs_def ov_ep_def ov_program_def
  by eval

lemma ov_solution_snapshot:
  "TD_side_always_join_Interp_solve_c ov_eqs (cfg_exit ov_cfg, []) \<noteq> None
   \<and> contexts_at ov_result p_entry = {[SPos], [STop]}
   \<and> contexts_at ov_result (Statement 3) = {[]}
   \<and> ov_seed [SPos] (STR ''a'') = Lifted SPos
   \<and> ov_seed [STop] (STR ''a'') = Lifted STop
   \<and> ov_read p_entry [SPos] (STR ''a'') = Lifted SPos
   \<and> ov_read p_entry [STop] (STR ''a'') = Lifted STop
   \<and> ov_read p_result [SPos] ret_var = Lifted SPos
   \<and> ov_read p_result [STop] ret_var = Lifted STop
   \<and> ov_alt_read 0 (STR ''y'') = Lifted SPos
   \<and> ov_alt_read 0 (STR ''x'') = Lifted SPos
   \<and> ov_alt_read 1 (STR ''y'') = Lifted STop
   \<and> ov_alt_read 1 (STR ''x'') = Lifted STop
   \<and> ov_read (Statement 4) [] (STR ''x'') = Lifted STop
   \<and> ov_read (Statement 4) [] (STR ''y'') = Lifted STop
   \<and> locals (snd ov_sol (Inl (Statement 3, []))) =
       update_resolved_st_q_lift (Lifted cinit_sign_st)
         (location_of ov_gs (STR ''x'')) SPos
   \<and> exec_formals_route ov_gs (Statement 3) []
       (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
         (locals (snd ov_sol (Inl (Statement 3, []))))) ov_ca = [SPos]
   \<and> forget_var ov_gs (STR ''x'') STop
       (locals (snd ov_sol (Inl (Statement 3, [])))) =
       update_resolved_st_q_lift (Lifted cinit_sign_st)
         (location_of ov_gs (STR ''x'')) STop
   \<and> exec_formals_route ov_gs (Statement 3) []
       (map_lift (forget_formals ov_gs (call_info_of ov_ca (STR ''p'')))
         (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
           (locals (snd ov_sol (Inl (Statement 3, [])))))) ov_ca = [STop]
   \<and> (\<forall>(u, ctx) \<in> fst ov_sol. \<forall>(u', a, v) \<in> intra ov_cfg.
          u = u' \<longrightarrow> (v, ctx) \<in> fst ov_sol)
   \<and> (\<forall>(cl, ctx) \<in> fst ov_sol. \<forall>(cl', ca, ce, cont) \<in> calls ov_cfg.
          cl = cl' \<longrightarrow> (cont, ctx) \<in> fst ov_sol)
   \<and> (\<forall>(u, ctx) \<in> fst ov_sol. u = Statement 3 \<longrightarrow>
          (\<forall>(cont', entry) \<in> set (ov_enter ov_gs ov_ep
              (call_info_of ov_ca (STR ''p''))
              (locals (snd ov_sol (Inl (u, ctx))))).
            (p_entry, exec_formals_route ov_gs u ctx entry ov_ca) \<in> fst ov_sol))"
  using ov_solution_snapshot_raw
  unfolding ov_result_def ov_alt_answer_def Let_def
  by blast

lemma ov_terminates_c:
  "TD_side_always_join_Interp_solve_c ov_eqs (cfg_exit ov_cfg, []) \<noteq> None"
  using ov_solution_snapshot by (elim conjE)

subsection \<open>1. One call, two contexts\<close>

lemma ov_two_contexts:
  "contexts_at ov_result p_entry = {[SPos], [STop]}"
  using ov_solution_snapshot by meson

lemma ov_two_contexts_card:
  "card (contexts_at ov_result p_entry) = 2"
  unfolding ov_two_contexts by simp

text \<open>\<open>main\<close> itself runs only under the root context.\<close>

lemma ov_caller_root_only:
  "contexts_at ov_result (Statement 3) = {[]}"
  using ov_solution_snapshot by blast+

subsection \<open>2. Each seed carries its own alternative's entry\<close>

lemma ov_seed_exact:
  "ov_seed [SPos] (STR ''a'') = Lifted SPos"
  using ov_solution_snapshot by blast

lemma ov_seed_forgotten:
  "ov_seed [STop] (STR ''a'') = Lifted STop"
  using ov_solution_snapshot by blast+

text \<open>The callee's entry unknown is exactly its seed: the seed read-back is its only
  predecessor.\<close>

lemma ov_entry_reads_seed:
  "ov_read p_entry [SPos] (STR ''a'') = Lifted SPos"
  "ov_read p_entry [STop] (STR ''a'') = Lifted STop"
  using ov_solution_snapshot by blast+

subsection \<open>3. Each activation returns what it was entered with, and stays paired\<close>

lemma ov_result_exact:
  "ov_read p_result [SPos] ret_var = Lifted SPos"
  using ov_solution_snapshot by blast+

lemma ov_result_forgotten:
  "ov_read p_result [STop] ret_var = Lifted STop"
  using ov_solution_snapshot by blast+

text \<open>
  Continuation/entry correlation, observed per alternative. The joined table cannot show
  it: Sign is non-relational, so the join of \<open>{(SPos, SPos), (STop, STop)}\<close> at \<open>(x, y)\<close> is
  the same \<open>(STop, STop)\<close> as the join of the swapped pairing. Traversing each alternative's
  own tree against the solved table does show it: alternative 1's combine writes \<open>y\<close> from
  the exact callee (\<^const>\<open>SPos\<close>) into its own untouched continuation (\<open>x = SPos\<close>),
  alternative 2's writes \<open>y\<close> from the forgotten callee (\<^const>\<open>STop\<close>) into its own
  forgotten continuation (\<open>x = STop\<close>).
\<close>

lemma ov_alt1_pairing:
  "ov_alt_read 0 (STR ''y'') = Lifted SPos"
  "ov_alt_read 0 (STR ''x'') = Lifted SPos"
  using ov_solution_snapshot by blast+

lemma ov_alt2_pairing:
  "ov_alt_read 1 (STR ''y'') = Lifted STop"
  "ov_alt_read 1 (STR ''x'') = Lifted STop"
  using ov_solution_snapshot by blast+

subsection \<open>4. The continuation holds the join of both alternatives\<close>

text \<open>Both \<open>x\<close> and \<open>y\<close> join to \<^const>\<open>STop\<close>: alternative 2 forgets \<open>x\<close> in its own
  continuation as well as \<open>a\<close> in its entry, so the imprecision this override costs shows up
  on both variables once the two alternatives join --- exactly what the relational bucket
  semantics below must account for instead of hiding.\<close>

lemma ov_continuation_join:
  "ov_read (Statement 4) [] (STR ''x'') = Lifted STop"
  "ov_read (Statement 4) [] (STR ''y'') = Lifted STop"
  using ov_solution_snapshot by blast+

subsection \<open>5. Negative: an empty entry list cannot cover a live caller\<close>

text \<open>The concrete caller store at the call site has \<open>x = 1\<close> and every global
  initialized to \<open>0\<close>.\<close>

lemma ov_empty_pairs_never_cover:
  "\<not> entry_pairs_cover (\<lambda>d'. sign_conf_gamma ov_gs d' g) ov_caller_store
       (call_enter ov_gs ov_ca ov_caller_store) []"
  by simp

text \<open>What the missing obligation would let through. With \<open>enter\<^sup>#\<close> answering \<open>[]\<close>, the
  solver seeds no callee, materializes no context at \<open>p\<close>, and leaves the continuation
  \<^const>\<open>Bot\<close> --- although the concrete run reaches it. A relation admitting no context for
  this call would produce the same empty buckets; conditional totality is what rules it out.\<close>

definition ov_empty_spec ::
  "(pp \<times> sign list, (unit, sign list) routed_gk, unit,
    sign exec_dg_st lifted, sign exec_dg_st lifted) dg_spec" where
  "ov_empty_spec = (sign_conf_spec ov_gs ov_ep)
     \<lparr> dgs_enter := (\<lambda>ci. local_enter_transfer (\<lambda>d. [])) \<rparr>"

declare ov_empty_spec_def [code_unfold]

definition ov_empty_eqs ::
  "(pp \<times> sign list, (unit, sign list) routed_gk,
    (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state) eqsT" where
  "ov_empty_eqs =
     routed_node_rhs_buffered intra_predecessor_addr_list call_site_list (\<lambda>_. Analysis_Global ())
       (exec_formals_route ov_gs)
       (\<lambda>ctx' src a. dg_spec_edge_program ov_empty_spec a src (\<lambda>_. Analysis_Global ()))
       (routed_call_program ov_empty_spec (Analysis_Global ()) Activation_Seed
          (static_resolve ov_cfg) (\<lambda>d. d = Bot))
       (routed_entry_seed_programs Activation_Seed)
       ov_cfg Bot (Lifted cinit_sign_st) Bot"

definition ov_empty_sol ::
  "(pp \<times> sign list) set \<times>
   (pp \<times> sign list + (unit, sign list) routed_gk
      \<Rightarrow> (sign exec_dg_st lifted, sign exec_dg_st lifted) dg_state)" where
  "ov_empty_sol = TD_side_always_join_Interp_solve ov_empty_eqs (cfg_exit ov_cfg, [])"

lemmas ov_empty_unfold = ov_empty_sol_def ov_empty_eqs_def ov_empty_spec_def ov_cfg_def
  ov_pi_def ov_procs_def ov_ep_def ov_program_def

lemma ov_empty_solution_snapshot_raw:
  "(let sol = ov_empty_sol
     in TD_side_always_join_Interp_solve_c ov_empty_eqs (cfg_exit ov_cfg, []) \<noteq> None
      \<and> (\<forall>(v, ctx) \<in> fst sol. v \<noteq> p_entry)
      \<and> locals (snd sol (Inl (Statement 4, []))) = Bot)"
  unfolding ov_empty_unfold
  by eval

lemma ov_empty_solution_snapshot:
  "TD_side_always_join_Interp_solve_c ov_empty_eqs (cfg_exit ov_cfg, []) \<noteq> None
   \<and> (\<forall>(v, ctx) \<in> fst ov_empty_sol. v \<noteq> p_entry)
   \<and> locals (snd ov_empty_sol (Inl (Statement 4, []))) = Bot"
  using ov_empty_solution_snapshot_raw
  unfolding Let_def
  by blast

lemma ov_empty_terminates_c:
  "TD_side_always_join_Interp_solve_c ov_empty_eqs (cfg_exit ov_cfg, []) \<noteq> None"
  using ov_empty_solution_snapshot by blast

lemma ov_empty_no_callee_context:
  "\<forall>(v, ctx) \<in> fst ov_empty_sol. v \<noteq> p_entry"
  using ov_empty_solution_snapshot by blast

lemma ov_empty_continuation_bot:
  "locals (snd ov_empty_sol (Inl (Statement 4, []))) = Bot"
  using ov_empty_solution_snapshot by blast

lemma ov_call_site_locals_probe:
  "locals (snd ov_sol (Inl (Statement 3, [])))
     = update_resolved_st_q_lift (Lifted cinit_sign_st) (location_of ov_gs (STR ''x'')) SPos"
  using ov_solution_snapshot by blast+

lemma ov_call_site_reader:
  "map_lift (fun_of_resolved_st_q_for ov_gs) (locals (snd ov_sol (Inl (Statement 3, []))))
     = Lifted ((fun_of_resolved_st_q_for ov_gs cinit_sign_st)(STR ''x'' := SPos))"
  unfolding ov_call_site_locals_probe update_resolved_st_q_lift_def
  by (simp add: is_bottom_sign_def)

lemma ov_caller_store_covered:
  "ov_caller_store \<in> sign_conf_gamma ov_gs (locals (snd ov_sol (Inl (Statement 3, [])))) g"
  unfolding sign_conf_gamma_def ov_call_site_reader gamma_lift_Lifted gamma_state_def
proof (rule CollectI, rule allI)
  fix y
  show "ov_caller_store y
          \<in> \<gamma> (((fun_of_resolved_st_q_for ov_gs cinit_sign_st)(STR ''x'' := SPos)) y)"
    by (cases "y = STR ''x''")
       (simp_all add: fun_of_initial_resolved_st_q gamma_sign_top ov_caller_store_def)
qed

lemma ov_alt1_route:
  "exec_formals_route ov_gs (Statement 3) []
     (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
        (locals (snd ov_sol (Inl (Statement 3, [])))))
     ov_ca = [SPos]"
  using ov_solution_snapshot by blast

lemma ov_entry1_not_empty_probe:
  "\<not> ov_ep (update_resolved_st_q
       (enter_frame_D_resolved_q STop
         (update_resolved_st_q cinit_sign_st (location_of ov_gs (STR ''x'')) SPos))
       (location_of ov_gs (STR ''a'')) SPos)"
  by eval

lemma ov_entry1_locals_exact:
  "transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
     (locals (snd ov_sol (Inl (Statement 3, []))))
   = Lifted (update_resolved_st_q
               (enter_frame_D_resolved_q STop
                 (update_resolved_st_q cinit_sign_st (location_of ov_gs (STR ''x'')) SPos))
               (location_of ov_gs (STR ''a'')) SPos)"
  unfolding ov_call_site_locals_probe update_resolved_st_q_lift_def
  by (simp add: bind_formals_resolved_q_singleton is_bottom_sign_def normalize_lift_def
                ov_entry1_not_empty_probe)

lemma ov_entry1_reader:
  "map_lift (fun_of_resolved_st_q_for ov_gs)
     (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
        (locals (snd ov_sol (Inl (Statement 3, [])))))
   = Lifted ((enter_frame ov_gs STop
                ((fun_of_resolved_st_q_for ov_gs cinit_sign_st)(STR ''x'' := SPos)))
             (STR ''a'' := SPos))"
  unfolding ov_entry1_locals_exact by simp

lemma ov_entry2_reader:
  "map_lift (fun_of_resolved_st_q_for ov_gs)
     (map_lift (forget_formals ov_gs (call_info_of ov_ca (STR ''p'')))
       (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
          (locals (snd ov_sol (Inl (Statement 3, []))))))
   = Lifted ((enter_frame ov_gs STop
                ((fun_of_resolved_st_q_for ov_gs cinit_sign_st)(STR ''x'' := SPos)))
             (STR ''a'' := STop))"
  unfolding forget_formals_def ov_entry1_locals_exact by simp

lemma ov_cont2_locals_probe:
  "forget_var ov_gs (STR ''x'') STop (locals (snd ov_sol (Inl (Statement 3, []))))
     = update_resolved_st_q_lift (Lifted cinit_sign_st) (location_of ov_gs (STR ''x'')) STop"
  using ov_solution_snapshot by blast

lemma ov_cont2_reader:
  "map_lift (fun_of_resolved_st_q_for ov_gs)
     (forget_var ov_gs (STR ''x'') STop (locals (snd ov_sol (Inl (Statement 3, [])))))
   = Lifted (((fun_of_resolved_st_q_for ov_gs cinit_sign_st)(STR ''x'' := STop)))"
  unfolding ov_cont2_locals_probe update_resolved_st_q_lift_def
  by (simp add: is_bottom_sign_def)

lemma ov_cont2_covered:
  "ov_caller_store
     \<in> sign_conf_gamma ov_gs (forget_var ov_gs (STR ''x'') STop (locals (snd ov_sol (Inl (Statement 3, [])))))
         g"
  unfolding sign_conf_gamma_def ov_cont2_reader gamma_lift_Lifted gamma_state_def
proof (rule CollectI, rule allI)
  fix y
  show "ov_caller_store y
          \<in> \<gamma> (((fun_of_resolved_st_q_for ov_gs cinit_sign_st)(STR ''x'' := STop)) y)"
    by (cases "y = STR ''x''")
       (simp_all add: fun_of_initial_resolved_st_q gamma_sign_top ov_caller_store_def)
qed

lemma ov_entry1_covered:
  "call_enter ov_gs ov_ca ov_caller_store
     \<in> sign_conf_gamma ov_gs
         (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
            (locals (snd ov_sol (Inl (Statement 3, [])))))
         g"
  unfolding sign_conf_gamma_def ov_entry1_reader gamma_lift_Lifted gamma_state_def
proof (rule CollectI, rule allI)
  fix y
  show "call_enter ov_gs ov_ca ov_caller_store y
          \<in> \<gamma> (((enter_frame ov_gs STop
                       ((fun_of_resolved_st_q_for ov_gs cinit_sign_st)(STR ''x'' := SPos)))
                    (STR ''a'' := SPos)) y)"
    by (cases "y = STR ''a''")
       (simp_all add: call_enter_CallEdge ov_caller_store_def gamma_sign_top
                      fun_of_initial_resolved_st_q)
qed

lemma ov_entry2_covered:
  "call_enter ov_gs ov_ca ov_caller_store
     \<in> sign_conf_gamma ov_gs
         (map_lift (forget_formals ov_gs (call_info_of ov_ca (STR ''p'')))
           (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
              (locals (snd ov_sol (Inl (Statement 3, []))))))
         g"
  unfolding sign_conf_gamma_def ov_entry2_reader gamma_lift_Lifted gamma_state_def
proof (rule CollectI, rule allI)
  fix y
  show "call_enter ov_gs ov_ca ov_caller_store y
          \<in> \<gamma> (((enter_frame ov_gs STop
                       ((fun_of_resolved_st_q_for ov_gs cinit_sign_st)(STR ''x'' := SPos)))
                    (STR ''a'' := STop)) y)"
    by (cases "y = STR ''a''")
       (simp_all add: call_enter_CallEdge ov_caller_store_def gamma_sign_top
                      fun_of_initial_resolved_st_q)
qed

lemma ov_alt2_route:
  "exec_formals_route ov_gs (Statement 3) []
     (map_lift (forget_formals ov_gs (call_info_of ov_ca (STR ''p'')))
       (transfer_lift ov_ep (sign_enter_st_for ov_gs (call_info_of ov_ca (STR ''p'')))
          (locals (snd ov_sol (Inl (Statement 3, []))))))
     ov_ca = [STop]"
  using ov_solution_snapshot by blast



subsection \<open>Soundness through the relational context layer\<close>

text \<open>
  \<^const>\<open>routed_entry_context_rel\<close> at \<^const>\<open>ov_enter\<close>: the relation this instance keys
  its collecting semantics by. None of the crux corollaries below is stateable with the
  retired functional selector, whose singleton premise this override deliberately breaks.
\<close>

abbreviation ov_R :: "sign list call_context_rel" where
  "ov_R \<equiv> routed_entry_context_rel (ov_enter ov_gs ov_ep) (sign_conf_gamma ov_gs) (snd ov_sol)
            (Analysis_Global ()) (exec_formals_route ov_gs)"

text \<open>An abbreviation is transparent to unification, but \<open>meson\<close> needs an explicit
  rewrite rule to fold a fully applied \<open>routed_entry_context_rel\<close> instance back into
  \<open>ov_R\<close>; this lemma is that rule.\<close>

lemma ov_R_eq:
  "ov_R = routed_entry_context_rel (ov_enter ov_gs ov_ep) (sign_conf_gamma ov_gs) (snd ov_sol)
            (Analysis_Global ()) (exec_formals_route ov_gs)"
  by (rule refl)

lemma ov_exact: "ov_ep s = is_empty_state (fun_of_resolved_st_q_for ov_gs s)"
  unfolding ov_ep_def by (rule resolved_st_q_is_bot_for_iff) simp

text \<open>Name the context variable \<open>ctx\<close>, never bare \<open>c\<close>: the vendored \<open>TD_side.state\<close> record
  exposes an unqualified field accessor \<open>c :: (_,_,_) TD_side.state_scheme \<Rightarrow> _ set\<close>, and a
  bound \<open>c\<close> in a raw \<open>\<forall>(_, c) \<in> _\<close> pattern here silently resolves to that constant
  instead of a fresh variable, producing a baffling type-clash error far from its cause.\<close>

lemma ov_fwd_closed_all:
  "\<forall>(u, ctx) \<in> fst ov_sol. \<forall>(u', a, v) \<in> intra ov_cfg. u = u' \<longrightarrow> (v, ctx) \<in> fst ov_sol"
  using ov_solution_snapshot by meson

lemma ov_fwd_ok:
  assumes "(u, ctx) \<in> fst ov_sol" and "(u, a, v) \<in> intra ov_cfg"
  shows "(v, ctx) \<in> fst ov_sol"
  using ov_fwd_closed_all assms by fastforce

lemma ov_comb_fwd_closed_all:
  "\<forall>(cl, c1) \<in> fst ov_sol. \<forall>(cl', ca, ce, cont) \<in> calls ov_cfg. cl = cl' \<longrightarrow> (cont, c1) \<in> fst ov_sol"
  using ov_solution_snapshot by meson

lemma ov_comb_fwd_ok:
  assumes "(cl, c1) \<in> fst ov_sol" and "(cl, ca, ce, cont) \<in> calls ov_cfg"
  shows "(cont, c1) \<in> fst ov_sol"
  using ov_comb_fwd_closed_all assms by fastforce

text \<open>The routed destination an admitted entry points at is already in the solved table.
  Bounded by \<^term>\<open>fst ov_sol\<close> and \<open>set (ov_enter ov_gs ov_ep ci d)\<close> (both finite), so
  \<open>eval\<close> decides it directly instead of symbolically rewriting the whole solved table.\<close>

lemma ov_enter_fwd_at_call:
  "\<forall>(u, ctx) \<in> fst ov_sol. u = Statement 3 \<longrightarrow>
     (\<forall>(cont', entry) \<in> set (ov_enter ov_gs ov_ep (call_info_of ov_ca (STR ''p''))
                               (locals (snd ov_sol (Inl (u, ctx))))).
        (p_entry, exec_formals_route ov_gs u ctx entry ov_ca) \<in> fst ov_sol)"
  using ov_solution_snapshot by blast+

lemma ov_pp_st:
  "part_post_solution ov_eqs (cfg_exit ov_cfg, []) (snd ov_sol) (fst ov_sol)"
  using TD_side_always_join_Interp.part_post_solution_of_solve_c[OF ov_terminates_c]
  unfolding ov_sol_def by simp

lemma ov_intra_side_free:
  "sides_of_program (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src g) \<tau> z = bot"
  unfolding dg_spec_edge_program_def dg_spec_step_ov_spec sign_conf_spec_def
  by (simp add: dg_spec_step_local_state_st_for_lifted)

lemma dg_spec_combine_transfer_ov_spec [simp]:
  "dg_spec_combine_transfer (ov_spec \<G> ep) ci m exit
     = dg_spec_combine_transfer (sign_conf_spec \<G> ep) ci m exit"
  by (simp add: dg_spec_combine_transfer_def)

lemma ov_cmb_side_free_at_gk0:
  "sides_of_program (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
      (static_resolve ov_cfg) (\<lambda>d. d = Bot) route ctx ca cc v) sigma (Inr (Analysis_Global ())) = bot"
proof (rule routed_call_program_side_free_at_gk0[OF dg_spec_wf_ov_spec])
  show "\<And>ci d pairs pub. enter_runs (enter\<^sup># (ov_spec ov_gs ov_ep) ci)
          (mk_dg_man d (\<lambda>_. Analysis_Global ())) sigma pairs pub \<Longrightarrow> pub (Inr (Analysis_Global ())) = bot"
    unfolding dgs_enter_ov_spec
    by (auto simp: bot_fun_def dest: enter_runs_local_pub_bot)
next
  show "\<And>ci d. \<exists>pairs pub. enter_runs (enter\<^sup># (ov_spec ov_gs ov_ep) ci)
          (mk_dg_man d (\<lambda>_. Analysis_Global ())) sigma pairs pub"
    unfolding dgs_enter_ov_spec by blast
next
  show "\<And>ci d de z. sides_of_rhs (sp_compile_with (\<lambda>x. DG x bot)
          (dg_spec_combine_transfer (ov_spec ov_gs ov_ep) ci
            (mk_dg_man d (\<lambda>_. Analysis_Global ())) de))
          sigma z = bot"
    by (simp add: sign_conf_spec_def dg_spec_combine_transfer_local_state_st_for_lifted
        sp_compile_with_def local_combine_transfer_def sp_return_def bot_dg_state_def)
next
  show "\<And>p ctx'. Activation_Seed (FunctionEntry p) ctx' \<noteq> Analysis_Global ()"
    by simp
qed

text \<open>The buffered post-solution reconciled with the unbuffered generator the routed
  locale is stated over. Only the entry differs from \<^const>\<open>sign_conf_spec\<close>, and none of the
  bridge's side-freeness obligations inspect what \<^const>\<open>dgs_enter\<close> answers with --- they
  hold for any list of alternatives, exactly as \<^theory>\<open>Voblint_Exec.Routed_Exec_Refinement\<close>
  discharges them once for every deterministic instance.\<close>

lemma ov_pp_routed:
  "part_post_solution
     (routed_node_rhs intra_predecessor_addr_list call_site_list (\<lambda>_. Analysis_Global ())
        (exec_formals_route ov_gs)
        (\<lambda>ctx' src a. dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ()))
        (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
           (static_resolve ov_cfg) (\<lambda>d. d = Bot))
        (routed_entry_seed_programs Activation_Seed)
        ov_cfg Bot (Lifted cinit_sign_st) Bot)
     (cfg_exit ov_cfg, []) (snd ov_sol) (fst ov_sol)"
proof (rule part_post_solution_routed_node_rhs_buffered
    [where it_c =
      "\<lambda>ctx' src a.
        dg_spec_edge_program (ov_spec ov_gs ov_ep) a src
          (\<lambda>_. Analysis_Global ())"
       and cmb_c = "routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
                      (static_resolve ov_cfg) (\<lambda>d. d = Bot)"])
  show "\<And>c' w. \<forall>p \<in> set (routed_contribution_programs
           intra_predecessor_addr_list call_site_list (exec_formals_route ov_gs)
           (\<lambda>ctx' src a. dg_spec_edge_program (ov_spec ov_gs ov_ep) a src
              (\<lambda>_. Analysis_Global ()))
           (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot))
           (routed_entry_seed_programs Activation_Seed) ov_cfg c' w). sp_wf p"
    by (rule routed_contribution_programs_wf)
       (auto intro: sp_wf_dg_spec_edge_program[OF dg_spec_wf_ov_spec]
         sp_wf_routed_call_program[OF dg_spec_wf_ov_spec])
next
  show "\<And>c' w. \<forall>p \<in> set (routed_contribution_programs
           intra_predecessor_addr_list call_site_list (exec_formals_route ov_gs)
           (\<lambda>ctx' src a. dg_spec_edge_program (ov_spec ov_gs ov_ep) a src
              (\<lambda>_. Analysis_Global ()))
           (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot))
           (routed_entry_seed_programs Activation_Seed) ov_cfg c' w). sp_wf p"
    by (rule routed_contribution_programs_wf)
       (auto intro: sp_wf_dg_spec_edge_program[OF dg_spec_wf_ov_spec]
         sp_wf_routed_call_program[OF dg_spec_wf_ov_spec])
next
  show "\<And>c' src a \<tau>. locals (traverse_program
           (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ())) \<tau>)
         = locals (traverse_program
           (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ())) \<tau>)"
    by (rule refl)
next
  show "\<And>c' src a \<tau>. locals (sides_of_program
           (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ())) \<tau>
           (Inr (Analysis_Global ()))) = bot"
    by (simp add: ov_intra_side_free bot_dg_state_def)
next
  show "\<And>c' src a \<tau>. globs (traverse_program
           (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ())) \<tau>)
         = globs (sides_of_program
           (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ())) \<tau>
           (Inr (Analysis_Global ())))"
    by (simp add: ov_intra_side_free dg_spec_edge_program_def sign_conf_spec_def
        dg_spec_step_local_state_st_for_lifted bot_dg_state_def)
next
  show "\<And>c' src a \<tau>. sides_of_program
           (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ())) \<tau>
           (Inr (Analysis_Global ())) = bot"
    by (rule ov_intra_side_free)
next
  show "\<And>c' src a \<tau> z. z \<noteq> Inr (Analysis_Global ()) \<Longrightarrow>
         sides_of_program
             (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ())) \<tau> z
           = sides_of_program
               (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src
                 (\<lambda>_. Analysis_Global ())) \<tau> z"
    by (rule refl)
next
  show "\<And>c' src a \<tau>. dep_program \<tau>
           (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ()))
         = dep_program \<tau>
             (dg_spec_edge_program (ov_spec ov_gs ov_ep) a src (\<lambda>_. Analysis_Global ()))"
    by (rule refl)
next
  show "\<And>c' ca cc ex \<tau>. locals (traverse_program
           (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex) \<tau>)
         = locals (traverse_program
           (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex) \<tau>)"
    by (rule refl)
next
  show "\<And>c' ca cc ex \<tau>. locals (sides_of_program
           (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex) \<tau>
           (Inr (Analysis_Global ()))) = bot"
    by (simp add: ov_cmb_side_free_at_gk0 bot_dg_state_def)
next
  show "\<And>c' ca cc ex \<tau>. globs (traverse_program
           (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex) \<tau>)
         = globs (sides_of_program
           (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex) \<tau>
           (Inr (Analysis_Global ())))"
    by (simp add: routed_call_program_global_free ov_cmb_side_free_at_gk0 bot_dg_state_def)
next
  show "\<And>c' ca cc ex \<tau>. sides_of_program
           (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex) \<tau>
           (Inr (Analysis_Global ())) = bot"
    by (rule ov_cmb_side_free_at_gk0)
next
  show "\<And>c' ca cc ex \<tau> z. z \<noteq> Inr (Analysis_Global ()) \<Longrightarrow>
         sides_of_program
             (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex) \<tau> z
           = sides_of_program
               (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ())
                 Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex) \<tau> z"
    by (rule refl)
next
  show "\<And>c' ca cc ex \<tau>. dep_program \<tau>
           (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex)
         = dep_program \<tau>
             (routed_call_program (ov_spec ov_gs ov_ep) (Analysis_Global ()) Activation_Seed
              (static_resolve ov_cfg) (\<lambda>d. d = Bot) (exec_formals_route ov_gs) c' ca cc ex)"
    by (rule refl)
next
  show "\<And>c' w \<tau> z x. x \<in> set (routed_entry_seed_programs Activation_Seed
           (exec_formals_route ov_gs) c' w) \<Longrightarrow> sides_of_program x \<tau> z = bot"
    by (rule routed_entry_seed_programs_free)
next
  show "\<And>c' w \<tau> x. x \<in> set (routed_entry_seed_programs Activation_Seed
           (exec_formals_route ov_gs) c' w) \<Longrightarrow> globs (traverse_program x \<tau>) = bot"
    by (rule routed_entry_seed_programs_local_only)
qed (rule ov_pp_st[unfolded ov_eqs_def])

interpretation ov_core: analysis_contract "ov_spec ov_gs ov_ep" "sign_conf_gamma ov_gs" ov_gs
  by (rule analysis_contract_ov_spec[OF ov_exact])

text \<open>The routed context locale, fully interpreted: every alternative's continuation is a
  sound description of the caller (\<open>EnterTotal\<close>), the routed table reflects whichever
  alternative a concrete relational admission points at (\<open>EnterCover\<close>), and a return
  leaves the continuation covered at the caller's own context (\<open>CombFwd\<close>).\<close>

interpretation ov_routed: routed_context_base_hetero
  "ov_spec ov_gs ov_ep" "sign_conf_gamma ov_gs" ov_gs ov_cfg "Analysis_Global ()"
  "exec_formals_route ov_gs" Bot "Lifted cinit_sign_st" Bot
  "snd ov_sol" "fst ov_sol" "(cfg_exit ov_cfg, [])"
  "solved_local_reader (fst ov_sol) (snd ov_sol)" Activation_Seed
  "static_resolve ov_cfg" "\<lambda>d. d = Bot"
  "\<lambda>m. \<lbrakk>map_lift (fun_of_resolved_st_q_for ov_gs) m\<rbrakk>\<^sub>\<bottom>" ov_R
proof (rule routed_context_base_hetero.intro
    [OF dg_ctx_activation_base.intro[OF analysis_contract_ov_spec[OF ov_exact]]],
  unfold_locales, goal_cases CmbWf ExtraWf FinE PP SgCov SgUncov Fwd FinC CallsUnique
    SeedKey IsBotBot IsBotSound ResolveSound EnterCover EnterTotal CombFwd)
  case CmbWf show ?case by (rule sp_wf_routed_call_program[OF dg_spec_wf_ov_spec])
next
  case ExtraWf then show ?case by (rule sp_wf_routed_entry_seed_programs)
next
  case FinE show ?case unfolding ov_cfg_def by (simp add: compile_prog_finite)
next
  case PP show ?case by (rule post_bounded_of_part_post_solution[OF ov_pp_routed])
next
  case (SgCov v ctx)
  thus ?case by (simp add: solved_local_reader_def sign_conf_gamma_def)
next
  case (SgUncov v ctx)
  thus ?case by (simp add: solved_local_reader_def)
next
  case (Fwd u a v ctx)
  show ?case by (rule ov_fwd_ok [OF Fwd(1) Fwd(3)])
next
  case FinC show ?case unfolding ov_cfg_def by (simp add: compile_prog_finite)
next
  case CallsUnique show ?case
    unfolding ov_cfg_def calls_source_unique_def using compile_prog_calls_source_unique
    by blast
next
  case (SeedKey p ctx) show ?case by simp
next
  case IsBotBot show ?case by simp
next
  case (IsBotSound d gv) then show ?case by (simp add: sign_conf_gamma_def)
next
  case (ResolveSound u ctx dst pars args p cont s)
  thus ?case unfolding ov_cfg_def by (simp add: compile_prog_finite)
next
  case (EnterCover u ctx dst pars args p cont s ctx')
  note ce = EnterCover(2) and Rc = EnterCover(4)
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?d = "locals (snd ov_sol (Inl (u, ctx)))"
  obtain cont' entry
    where mem: "(cont', entry) \<in> set (ov_enter ov_gs ov_ep ?ci ?d)"
      and ccov: "s \<in> sign_conf_gamma ov_gs cont' (globs (snd ov_sol (Inr (Analysis_Global ()))))"
      and ecov: "call_enter ov_gs (CallEdge dst pars args) s
                   \<in> sign_conf_gamma ov_gs entry (globs (snd ov_sol (Inr (Analysis_Global ()))))"
      and req: "ctx' = exec_formals_route ov_gs u ctx entry (CallEdge dst pars args)"
    using routed_entry_context_relE[OF Rc] by auto
  have Rr: "enter_runs (enter\<^sup># (ov_spec ov_gs ov_ep) ?ci) (mk_dg_man ?d (\<lambda>_. Analysis_Global ()))
              (snd ov_sol) (ov_enter ov_gs ov_ep ?ci ?d) bot"
    by (simp add: enter_runs_local_enter_transfer_mk_dg_man)
  have D: "enter_deps (enter\<^sup># (ov_spec ov_gs ov_ep) ?ci) (mk_dg_man ?d (\<lambda>_. Analysis_Global ()))
             (snd ov_sol) (ov_enter ov_gs ov_ep ?ci ?d) {}"
    by (simp add: enter_deps_local_enter_transfer_mk_dg_man)
  have upin: "u = Statement 3" and caeq: "CallEdge dst pars args = ov_ca"
      and ceeq: "FunctionEntry p = p_entry"
    using ov_calls_shape ce by auto
  have peq: "p = STR ''p''" using ceeq by simp
  have fwd: "(FunctionEntry p, ctx') \<in> fst ov_sol"
  proof -
    have mm: "(u, ctx) \<in> fst ov_sol" using EnterCover(1) .
    have "(p_entry, exec_formals_route ov_gs u ctx entry ov_ca) \<in> fst ov_sol"
      using ov_enter_fwd_at_call mm upin mem[unfolded caeq peq] by blast
    then show ?thesis unfolding req caeq ceeq by simp
  qed
  show ?case using Rr D mem ccov ecov req fwd by blast
next
  case (EnterTotal u ctx dst pars args p cont s)
  let ?ci = "call_info_of (CallEdge dst pars args) p"
  let ?d = "locals (snd ov_sol (Inl (u, ctx)))"
  show ?case
  proof (rule routed_entry_context_rel_total)
    show "entry_pairs_cover
      (\<lambda>d'. sign_conf_gamma ov_gs d'
        (globs (snd ov_sol (Inr (Analysis_Global ())))))
            s (call_enter ov_gs (CallEdge dst pars args) s) (ov_enter ov_gs ov_ep ?ci ?d)"
      unfolding ov_enter_def Let_def
      using sign_conf_entry_cover_exec[OF ov_exact EnterTotal(3), where ci = ?ci]
      unfolding entry_pairs_cover_def by auto
  qed
next
  case (CombFwd cl c1 dst pars args p cont)
  thus ?case by (rule ov_comb_fwd_ok)
qed

lemma ov_pos_context_admitted:
  "ov_R (Statement 3) []
     (call_info_of ov_ca (STR ''p''))
     ov_caller_store
     (call_enter ov_gs ov_ca ov_caller_store)
     [SPos]"
proof -
  let ?ci = "call_info_of ov_ca (STR ''p'')"
  let ?d = "locals (snd ov_sol (Inl (Statement 3, [])))"
  let ?entry = "transfer_lift ov_ep (sign_enter_st_for ov_gs ?ci) ?d"
  have mem: "(?d, ?entry) \<in> set (ov_enter ov_gs ov_ep ?ci ?d)"
    unfolding ov_enter_def Let_def by simp
  have caedge: "CallEdge (ci_dst ?ci) (ci_formals ?ci) (ci_args ?ci) = ov_ca"
    by simp
  show ?thesis
    using routed_entry_context_relI[
            where alts = "ov_enter ov_gs ov_ep" and \<gamma>\<^sub>D\<^sub>G = "sign_conf_gamma ov_gs"
              and sigma = "snd ov_sol"
              and route = "exec_formals_route ov_gs" and u = "Statement 3" and ctx = "[]",
            OF mem
              ov_caller_store_covered[where g = "globs (snd ov_sol (Inr (Analysis_Global ())))"]
              ov_entry1_covered[where g = "globs (snd ov_sol (Inr (Analysis_Global ())))"],
            unfolded caedge, unfolded ov_alt1_route]
    by (meson ov_R_eq)
qed

lemma ov_top_context_admitted:
  "ov_R (Statement 3) []
     (call_info_of ov_ca (STR ''p''))
     ov_caller_store
     (call_enter ov_gs ov_ca ov_caller_store)
     [STop]"
proof -
  let ?ci = "call_info_of ov_ca (STR ''p'')"
  let ?d = "locals (snd ov_sol (Inl (Statement 3, [])))"
  let ?cont2 = "forget_var ov_gs (STR ''x'') STop ?d"
  let ?entry1 = "transfer_lift ov_ep (sign_enter_st_for ov_gs ?ci) ?d"
  let ?entry2 = "map_lift (forget_formals ov_gs ?ci) ?entry1"
  have mem: "(?cont2, ?entry2) \<in> set (ov_enter ov_gs ov_ep ?ci ?d)"
    unfolding ov_enter_def Let_def by simp
  have caedge: "CallEdge (ci_dst ?ci) (ci_formals ?ci) (ci_args ?ci) = ov_ca"
    by simp
  show ?thesis
    using routed_entry_context_relI[
            where alts = "ov_enter ov_gs ov_ep" and \<gamma>\<^sub>D\<^sub>G = "sign_conf_gamma ov_gs"
              and sigma = "snd ov_sol"
              and route = "exec_formals_route ov_gs" and u = "Statement 3" and ctx = "[]",
            OF mem
              ov_cont2_covered[where g = "globs (snd ov_sol (Inr (Analysis_Global ())))"]
              ov_entry2_covered[where g = "globs (snd ov_sol (Inr (Analysis_Global ())))"],
            unfolded caedge, unfolded ov_alt2_route]
    by (meson ov_R_eq)
qed

lemma ov_two_contexts_admitted:
  "ov_R (Statement 3) [] (call_info_of ov_ca (STR ''p''))
     ov_caller_store (call_enter ov_gs ov_ca ov_caller_store) [SPos]
   \<and> ov_R (Statement 3) [] (call_info_of ov_ca (STR ''p''))
     ov_caller_store (call_enter ov_gs ov_ca ov_caller_store) [STop]
   \<and> [SPos] \<noteq> [STop]"
  using ov_pos_context_admitted ov_top_context_admitted by simp


subsection \<open>What this shows\<close>

text \<open>
  Proven, executably: the call/combine machinery keeps two overlapping alternatives
  distinguishable end to end --- each is read back through its own continuation
  (\<open>ov_alt1_pairing\<close>/\<open>ov_alt2_pairing\<close>) and reaches two distinct contexts at \<open>p_entry\<close>
  (\<open>ov_two_contexts\<close>), something the retired functional selector, whose singleton
  premise this override deliberately breaks, could not even state.

  Proven, relationally: the existing generic routed soundness bridge
  (\<^theory>\<open>Voblint_Exec.Routed_Exec_Refinement\<close>) already supports list-valued,
  non-deterministic entry without any change to it --- \<open>ov_pp_routed\<close> discharges the full
  buffered/unbuffered reconciliation for this override, since none of its side-freeness
  obligations inspect what the entry list contains, only that it is
  \<^const>\<open>local_enter_transfer\<close>-shaped, which \<open>ov_enter\<close> already is. This example supplies
  and discharges the corresponding non-deterministic entry obligations
  (\<open>routed_context_base_hetero\<close>'s \<open>EnterCover\<close>/\<open>EnterTotal\<close>/\<open>CombFwd\<close>) for the first time,
  and \<open>ov_two_contexts_admitted\<close> above names the one concrete call transition that genuinely
  admits the callee activation under both \<open>[SPos]\<close> and \<open>[STop]\<close> via \<open>ov_R\<close> --- not merely that
  two contexts exist somewhere in the abstract table, but that this call's own admitted-context
  relation holds for both. The caller itself stays at its own context, \<open>[]\<close>; it is the callee
  activation this one call reaches that is admitted under two contexts at once.

  Negative: an empty entry list admits no context at all for this call, so the seed
  never covers the live caller --- \<open>ov_empty_pairs_never_cover\<close> above is exactly the
  missing obligation \<^const>\<open>call_context_total_on\<close> rules out.
\<close>

end

