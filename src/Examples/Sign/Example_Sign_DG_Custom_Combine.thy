theory Example_Sign_DG_Custom_Combine
  imports
    "Voblint_Routing.Compiled_Routed_Equations"
    "Voblint_Framework.DG_Reader_Transport"
    "Voblint_Exec.Ownership_Split_Exec"
    "Voblint_Analysis_Sign.Sign_Exec"
    "Voblint_Analysis_Sign.Sign_Transfer"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation" "Voblint_Compile.Compile_Wellformed"
begin

section \<open>An analysis-supplied return combine on the D/G spine\<close>

text \<open>
  The call-return environment merge is a field of \<^typ>\<open>('x, 'k, 'v, 'dl, 'dg) dg_spec\<close>,
  not a formula built into the equation generator or the solver:
  \<^const>\<open>dgs_combine_env\<close> is what \<^const>\<open>dg_spec_combine_transfer\<close> consults
  before handing the merged environment to \<^const>\<open>dgs_combine_assign\<close>.  This
  theory witnesses that the field is genuinely free.  It takes the ordinary
  executable Sign specification, overrides \<^emph>\<open>only\<close> that one field, and runs
  the result through the same \<^const>\<open>compiled_routed_eqs_for\<close> generator and the same vendored solver a
  production analysis uses.  Every other field --- the caller continuation, the
  edge transfers, \<^const>\<open>dgs_enter\<close>, and \<^const>\<open>dgs_combine_assign\<close> --- is the
  stock one, so the observed difference isolates exactly that degree of
  freedom.
\<close>

subsection \<open>A callee-joining environment merge\<close>

text \<open>
  The stock environment merge passes the caller's locals through unchanged and
  discards the callee's entirely: only \<^const>\<open>ret_var\<close> survives, through the
  return assignment that \<^const>\<open>dgs_combine_assign\<close> performs afterwards, which
  is also where the caller's locals meet the current global slot.
  \<open>sign_combine_env_callee_join\<close>
  keeps them, joining the callee-exit locals into the caller's before the same
  reassembly.  Joining can only move the result up the lattice, so the merge
  stays sound; it is strictly less precise, and it is a different operation.  On
  a variable the caller left \<^const>\<open>SPos\<close> and the callee left \<^const>\<open>SNeg\<close>, the
  stock merge keeps \<^const>\<open>SPos\<close> while this one publishes \<^const>\<open>STop\<close>.
\<close>

definition sign_combine_env_callee_join ::
  "('x,'k,unit,'a::bounded_semilattice_sup_bot exec_dg_st,'a exec_dg_st) man_combine_transfer"
where
  "sign_combine_env_callee_join =
     local_combine_transfer (\<lambda>dc de. dc \<squnion> restrict_local_resolved_q de)"

subsection \<open>The Sign specification that uses it\<close>

definition sign_dg_spec_callee_join ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> sign exec_dg_st \<Rightarrow> sign exec_dg_st)
   \<Rightarrow> (call_info \<Rightarrow> sign exec_dg_st \<Rightarrow> sign exec_dg_st)
   \<Rightarrow> ('x, 'k, unit, sign exec_dg_st, sign exec_dg_st) dg_spec" where
  "sign_dg_spec_callee_join \<G> tf_st enter_st =
     (ownership_split_dg_spec_st_for \<G> tf_st enter_st)
       \<lparr> dgs_combine_env := (\<lambda>ci. sign_combine_env_callee_join) \<rparr>"

declare sign_dg_spec_callee_join_def [code_unfold]
text \<open>Only the environment merge differs; every other field is the stock one.\<close>

lemma dgs_enter_sign_dg_spec_callee_join [simp]:
  "enter\<^sup># (sign_dg_spec_callee_join \<G> tf_st enter_st)
     = enter\<^sup># (ownership_split_dg_spec_st_for \<G> tf_st enter_st)"
  by (simp add: sign_dg_spec_callee_join_def)

lemma dgs_combine_assign_sign_dg_spec_callee_join [simp]:
  "combine_assign\<^sup># (sign_dg_spec_callee_join \<G> tf_st enter_st)
     = combine_assign\<^sup># (ownership_split_dg_spec_st_for \<G> tf_st enter_st)"
  by (simp add: sign_dg_spec_callee_join_def)

lemma dg_spec_step_sign_dg_spec_callee_join [simp]:
  "dg_spec_step (sign_dg_spec_callee_join \<G> tf_st enter_st) a
     = dg_spec_step (ownership_split_dg_spec_st_for \<G> tf_st enter_st) a"
  by (cases a) (simp_all add: sign_dg_spec_callee_join_def)

lemma dgs_combine_env_sign_dg_spec_callee_join [simp]:
  "combine_env\<^sup># (sign_dg_spec_callee_join \<G> tf_st enter_st)
     = (\<lambda>ci. sign_combine_env_callee_join)"
  by (simp add: sign_dg_spec_callee_join_def)

subsection \<open>The merge really differs from the stock one\<close>

text \<open>
  The disagreement, pinned at the two concrete operands the section header
  describes: a caller state holding \<^const>\<open>SPos\<close> at \<open>r\<close> and a callee exit
  holding \<^const>\<open>SNeg\<close> there.  The stock merge's local component keeps
  \<^const>\<open>SPos\<close>; the callee-joining merge's publishes \<^const>\<open>STop\<close>.
\<close>

abbreviation cj_gs :: "vname \<Rightarrow> bool" where
  "cj_gs \<equiv> (\<lambda>_. False)"

definition cj_caller :: "sign exec_dg_st" where
  "cj_caller = update_resolved_st_q bot (Local_Location (STR ''r'')) SPos"

definition cj_callee :: "sign exec_dg_st" where
  "cj_callee = update_resolved_st_q bot (Local_Location (STR ''r'')) SNeg"

lemma stock_env_keeps_caller:
  "lookup_resolved_st_q cj_caller (Local_Location (STR ''r'')) = SPos"
  by (simp add: cj_caller_def)

lemma callee_join_env_publishes_top:
  "lookup_resolved_st_q (cj_caller \<squnion> restrict_local_resolved_q cj_callee)
     (Local_Location (STR ''r'')) = STop"
  by (simp add: cj_caller_def cj_callee_def sup_sign_def)

text \<open>So the two environment merges are different functions, and the override is
  not a re-spelling of the stock one.\<close>

lemma callee_join_merge_neq_stock:
  "(\<lambda>dc de. dc \<squnion> restrict_local_resolved_q de)
     \<noteq> (\<lambda>dc (de :: sign exec_dg_st). dc)"
proof
  assume "(\<lambda>dc de. dc \<squnion> restrict_local_resolved_q de)
            = (\<lambda>dc (de :: sign exec_dg_st). dc)"
  from fun_cong[OF fun_cong[OF this, of cj_caller], of cj_callee]
  have "cj_caller \<squnion> restrict_local_resolved_q cj_callee = cj_caller" .
  then show False
    using stock_env_keeps_caller callee_join_env_publishes_top by simp
qed

subsection \<open>The same merge at the abstract representation, and its soundness\<close>

text \<open>
  \<open>combine_env_callee_join_abs\<close> is the same operation on \<^typ>\<open>'a abs_state\<close>,
  the representation soundness is stated over.  The override is again a single
  field of the lifted specification, so \<^const>\<open>dg_spec_step\<close>,
  \<^const>\<open>dgs_enter\<close> and \<^const>\<open>dgs_combine_assign\<close> are
  the stock ones and their obligations transfer verbatim. Overriding at that
  position means the join runs on the two split local halves, before
  \<^const>\<open>ownership_split_lift\<close>'s wrapper merges the shared fact back in.

  Only \<open>combine_sound\<close> needs an argument, and it is the generic one: the merged
  environment this specification hands the wrapped combine is above the one the
  stock specification hands it, and the return combine and both projections are
  monotone in exactly that argument. So the answer and the published
  contribution both move up, and \<^const>\<open>gamma_ownership_split\<close>'s monotonicity
  carries the stock membership across. No second soundness chain appears: this
  instance reuses \<open>ownership_split_lift_contract\<close> for everything else.
\<close>

abbreviation sign_base_spec ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('x,'k,unit,sign abs_state,sign abs_state) dg_spec" where
  "sign_base_spec \<G> \<equiv> local_state_dg_spec_for \<G>
     skip_sign assign_sign special_sign branch_sign body_sign return_sign
     (enter_sign_ci_for \<G>) event_sign"

definition combine_env_callee_join_abs ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('x,'k,unit,'a::bounded_semilattice_sup_bot abs_state,'a abs_state) man_combine_transfer"
where
  "combine_env_callee_join_abs \<G> =
     local_combine_transfer (\<lambda>dc de. dc \<squnion> restrict_local_for \<G> de)"

definition sign_dg_spec_env_join ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('x,'k,unit,sign abs_state, sign abs_state) dg_spec" where
  "sign_dg_spec_env_join \<G> =
     (ownership_split_lift \<G> (sign_base_spec \<G>))
       \<lparr> dgs_combine_env := (\<lambda>ci. combine_env_callee_join_abs \<G>) \<rparr>"

declare sign_dg_spec_env_join_def [code_unfold]

lemma dg_spec_step_sign_dg_spec_env_join [simp]:
  "dg_spec_step (sign_dg_spec_env_join \<G>) a
     = dg_spec_step (ownership_split_lift \<G> (sign_base_spec \<G>)) a"
  by (cases a) (simp_all add: sign_dg_spec_env_join_def)

lemma dgs_enter_sign_dg_spec_env_join [simp]:
  "enter\<^sup># (sign_dg_spec_env_join \<G>)
     = enter\<^sup># (ownership_split_lift \<G> (sign_base_spec \<G>))"
  by (simp add: sign_dg_spec_env_join_def)

lemma dgs_query_sign_dg_spec_env_join [simp]:
  "dgs_query (sign_dg_spec_env_join \<G>)
     = dgs_query (ownership_split_lift \<G> (sign_base_spec \<G>))"
  by (simp add: sign_dg_spec_env_join_def)

lemma dg_spec_wf_ownership_split_lift_sign_base [intro]:
  "dg_spec_wf (ownership_split_lift \<G> (sign_base_spec \<G>))"
  by (rule dg_spec_wf_ownership_split_lift[OF dg_spec_wf_local_state_dg_spec_for])

lemma dg_spec_wf_sign_dg_spec_env_join [intro, simp]:
  "dg_spec_wf (sign_dg_spec_env_join \<G>)"
proof (unfold dg_spec_wf_def, intro conjI allI impI)
  show "sp_wf (dg_spec_step (sign_dg_spec_env_join \<G>) a ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>))"
    if "\<forall>q. sp_wf (A q)" for a d key A
    unfolding dg_spec_step_sign_dg_spec_env_join
    by (rule dg_spec_wf_step_ask[OF dg_spec_wf_ownership_split_lift_sign_base])
       (use that in blast)
next
  show "sp_wf (dgs_query (sign_dg_spec_env_join \<G>) ((mk_dg_man d key)\<lparr>man_ask := A\<rparr>) q)"
    for d key A q
    by simp
next
  fix ci d key
  show "sp_wf (enter\<^sup># (sign_dg_spec_env_join \<G>) ci (mk_dg_man d key))"
    by (simp only: dgs_enter_sign_dg_spec_env_join
        dg_spec_wf_enter[OF dg_spec_wf_ownership_split_lift_sign_base])
next
  fix ci d key ex
  show "sp_wf (dg_spec_combine_transfer (sign_dg_spec_env_join \<G>) ci (mk_dg_man d key) ex)"
    unfolding dg_spec_combine_transfer_def
    by (auto simp: sign_dg_spec_env_join_def combine_env_callee_join_abs_def
        local_combine_transfer_def
        intro!: sp_wf_bind
          sp_wf_dgs_combine_assign_ownership_split_lift[OF dg_spec_wf_local_state_dg_spec_for])
qed

text \<open>
  Both specifications run the same wrapped combine; they differ only in the
  local value it starts from. That is the whole content of the override, and it
  is what the two observations below inherit.
\<close>

lemma dg_spec_combine_transfer_env_join:
  "dg_spec_combine_transfer (sign_dg_spec_env_join \<G>) ci m de
     = ownership_split_combine_transfer \<G> (dg_spec_combine_transfer (sign_base_spec \<G>) ci)
         (m\<lparr>man_local := man_local m \<squnion> restrict_local_for \<G> de\<rparr>) de"
  unfolding dg_spec_combine_transfer_def sign_dg_spec_env_join_def
    combine_env_callee_join_abs_def ownership_split_lift_def
  by (simp add: local_transfer_def local_combine_transfer_def)

subsection \<open>The override only ever widens\<close>

text \<open>
  The merged environment this specification hands the return combine sits above
  the stock one, and every step from there is monotone: the combine reads a
  larger caller state, and both projections of the result preserve the order.
  So the answer and the published contribution both move up, and
  \<^const>\<open>gamma_ownership_split\<close>'s monotonicity carries the stock membership
  across. No second soundness chain appears --- everything but the combine is
  inherited from \<open>ownership_split_lift_contract\<close>.
\<close>

lemma combine_env_join_ge:
  "combine_env \<G> dc g \<le> combine_env \<G> (dc \<squnion> restrict_local_for \<G> de) g"
  by (rule combine_env_mono[OF sup_ge1 order_refl])

lemma combine_collect_abs_join_ge:
  "combine\<^sup># \<G> dst (combine_env \<G> dc g) (combine_env \<G> de g)
     \<le> combine\<^sup># \<G> dst (combine_env \<G> (dc \<squnion> restrict_local_for \<G> de) g)
         (combine_env \<G> de g)"
  by (rule combine_collect_abs_mono[OF combine_env_join_ge order_refl])

text \<open>The override's own tree observations. The generic reduction rules do not
  fire here: the transfer is wrapped in the lambda that rebuilds the manager
  with the joined local, so it is reduced once explicitly.\<close>

lemma traverse_combine_env_join:
  "locals (traverse_rhs (sp_compile_with (\<lambda>d. DG d bot)
       (dg_spec_combine_transfer (sign_dg_spec_env_join \<G>) ci
          (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau>)
     = restrict_local_for \<G>
         (combine\<^sup># \<G> (ci_dst ci)
            (combine_env \<G> (dc \<squnion> restrict_local_for \<G> de) (globs (\<tau> (Inr gk))))
            (combine_env \<G> de (globs (\<tau> (Inr gk)))))"
  unfolding dg_spec_combine_transfer_env_join
    ownership_split_combine_transfer_def local_state_dg_spec_for_def
    dg_spec_combine_transfer_local_dg_spec
  by (simp add: ownership_split_combine_transfer_gen_def local_combine_transfer_def
        mk_dg_man_def dg_read_global_def dg_sideg_def sp_bind_assoc)

lemma sides_combine_env_join:
  "globs (sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot)
       (dg_spec_combine_transfer (sign_dg_spec_env_join \<G>) ci
          (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau> (Inr gk))
     = restrict_global_for \<G>
         (combine\<^sup># \<G> (ci_dst ci)
            (combine_env \<G> (dc \<squnion> restrict_local_for \<G> de) (globs (\<tau> (Inr gk))))
            (combine_env \<G> de (globs (\<tau> (Inr gk)))))"
  unfolding dg_spec_combine_transfer_env_join
    ownership_split_combine_transfer_def local_state_dg_spec_for_def
    dg_spec_combine_transfer_local_dg_spec
  by (simp add: ownership_split_combine_transfer_gen_def local_combine_transfer_def
        mk_dg_man_def dg_read_global_def dg_sideg_def sp_bind_assoc)

text \<open>The stock observations, in the same shape, so the comparison below is
  between two equations rather than between a tree and an equation.\<close>

lemma traverse_combine_stock:
  "locals (traverse_rhs (sp_compile_with (\<lambda>d. DG d bot)
       (dg_spec_combine_transfer (ownership_split_lift \<G> (sign_base_spec \<G>)) ci
          (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau>)
     = restrict_local_for \<G>
         (combine\<^sup># \<G> (ci_dst ci)
            (combine_env \<G> dc (globs (\<tau> (Inr gk))))
            (combine_env \<G> de (globs (\<tau> (Inr gk)))))"
  unfolding dg_spec_combine_transfer_ownership_split_lift
    ownership_split_combine_transfer_def local_state_dg_spec_for_def
    dg_spec_combine_transfer_local_dg_spec
  by (simp add: ownership_split_combine_transfer_gen_def local_combine_transfer_def
        mk_dg_man_def dg_read_global_def dg_sideg_def sp_bind_assoc)

lemma sides_combine_stock:
  "globs (sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot)
       (dg_spec_combine_transfer (ownership_split_lift \<G> (sign_base_spec \<G>)) ci
          (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau> (Inr gk))
     = restrict_global_for \<G>
         (combine\<^sup># \<G> (ci_dst ci)
            (combine_env \<G> dc (globs (\<tau> (Inr gk))))
            (combine_env \<G> de (globs (\<tau> (Inr gk)))))"
  unfolding dg_spec_combine_transfer_ownership_split_lift
    ownership_split_combine_transfer_def local_state_dg_spec_for_def
    dg_spec_combine_transfer_local_dg_spec
  by (simp add: ownership_split_combine_transfer_gen_def local_combine_transfer_def
        mk_dg_man_def dg_read_global_def dg_sideg_def sp_bind_assoc)

lemma traverse_combine_env_join_ge:
  "locals (traverse_rhs (sp_compile_with (\<lambda>d. DG d bot)
       (dg_spec_combine_transfer (ownership_split_lift \<G> (sign_base_spec \<G>)) ci
          (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau>)
     \<le> locals (traverse_rhs (sp_compile_with (\<lambda>d. DG d bot)
          (dg_spec_combine_transfer (sign_dg_spec_env_join \<G>) ci
             (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau>)"
  unfolding traverse_combine_stock traverse_combine_env_join
  by (rule restrict_local_for_mono[OF combine_collect_abs_join_ge])

lemma sides_combine_env_join_ge:
  "globs (sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot)
       (dg_spec_combine_transfer (ownership_split_lift \<G> (sign_base_spec \<G>)) ci
          (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau> (Inr gk))
     \<le> globs (sides_of_rhs (sp_compile_with (\<lambda>d. DG d bot)
          (dg_spec_combine_transfer (sign_dg_spec_env_join \<G>) ci
             (mk_dg_man dc (\<lambda>_. gk)) de)) \<tau> (Inr gk))"
  unfolding sides_combine_stock sides_combine_env_join
  by (rule restrict_global_for_mono[OF combine_collect_abs_join_ge])

theorem analysis_contract_sign_dg_spec_env_join:
  "analysis_contract (sign_dg_spec_env_join \<G>) (gamma_ownership_split \<G>) \<G>"
proof -
  interpret sign_tf: sound_transfer_for \<G>
      skip_sign assign_sign special_sign branch_sign body_sign return_sign
      "enter_sign_ci_for \<G>" event_sign
    by (rule sign_tf.is_sound_transfer_for)
  interpret stock: analysis_contract
    "ownership_split_lift \<G> (sign_base_spec \<G>)" "gamma_ownership_split \<G>" \<G>
    by (rule sign_tf.ownership_split_lift_contract)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case 1 show ?case by (rule dg_spec_wf_sign_dg_spec_env_join)
  next
    case (2 d d' g g')
    then show ?case by (rule gamma_ownership_split_mono)
  next
    case (3 a \<tau> src gk)
    show ?case using stock.step_sound by (simp add: dg_spec_edge_program_def)
  next
    case (4 s dc \<tau> gk t de ci)
    from stock.combine_sound[where dc = dc and de = de and \<tau> = \<tau> and gk = gk and ci = ci,
        OF 4(1) 4(2)]
    show ?case
      by (rule subsetD[OF gamma_ownership_split_mono
            [OF traverse_combine_env_join_ge sides_combine_env_join_ge]])
  qed
qed

subsection \<open>The solved result really differs\<close>

text \<open>
  \<open>cj_program\<close>'s callee writes \<^const>\<open>SNeg\<close> to \<open>r\<close>, a name the caller already
  holds as \<^const>\<open>SPos\<close> across the call.  Both specifications compile the same
  program to the same CFG, generate equations with the same
  \<^const>\<open>compiled_routed_eqs_for\<close>, and are solved by the same vendored solver; only
  \<^const>\<open>dgs_combine_env\<close> differs between them.
\<close>

text \<open>\<open>cj_program\<close> is byte-identical to \<open>Example_Sign_DG_Custom_Body\<close>'s \<open>bf_program\<close>, and
  \<open>cj_stock_eqs\<close> below to that theory's \<open>bf_stock_eqs\<close>. One call, one formal, and one name
  that caller and callee both write is the smallest shape in which a single overridden
  \<open>dg_spec\<close> field is observable, and both overrides need exactly that shape; each theory
  keeps its own copy so neither witness inherits the other's imports.\<close>

definition cj_program :: imp_prog where
  "cj_program = program {
     fun mark(p) { r = 0 - 1; return p; }
     fun main() { r = 1; z = mark(7); }
   }"

abbreviation cj_prog_gs :: "vname \<Rightarrow> bool" where
  "cj_prog_gs \<equiv> declared_global cj_program"

definition cj_cfg :: cfg where
  "cj_cfg = compile_prog (prog_table cj_program) (prog_procs cj_program)"

abbreviation cj_lookup :: "sign exec_dg_st \<Rightarrow> vname \<Rightarrow> sign" where
  "cj_lookup s x \<equiv> lookup_resolved_st_q s (location_of cj_prog_gs x)"

definition cj_stock_eqs ::
  "pp \<times> unit
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
        (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "cj_stock_eqs = compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
     (ownership_split_dg_spec_st_for cj_prog_gs
        (sign_tf_st_for cj_prog_gs) (sign_enter_st_for cj_prog_gs))
     cj_cfg cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

definition cj_custom_eqs ::
  "pp \<times> unit
   \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk,
        (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "cj_custom_eqs = compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
     (sign_dg_spec_callee_join cj_prog_gs
        (sign_tf_st_for cj_prog_gs) (sign_enter_st_for cj_prog_gs))
     cj_cfg cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

lemma cj_stock_terminates:
  "TD_side_seed_join_warrowing_Interp_solve_c is_activation_seed cj_stock_eqs
     (cfg_exit cj_cfg, ()) \<noteq> None"
  by eval

lemma cj_custom_terminates:
  "TD_side_seed_join_warrowing_Interp_solve_c is_activation_seed cj_custom_eqs
     (cfg_exit cj_cfg, ()) \<noteq> None"
  by eval

definition cj_stock_sol ::
  "(pp \<times> unit) set
   \<times> (pp \<times> unit + (unit, unit) routed_gk
        \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "cj_stock_sol =
     TD_side_seed_join_warrowing_Interp_solve is_activation_seed cj_stock_eqs
       (cfg_exit cj_cfg, ())"

definition cj_custom_sol ::
  "(pp \<times> unit) set
   \<times> (pp \<times> unit + (unit, unit) routed_gk
        \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "cj_custom_sol =
     TD_side_seed_join_warrowing_Interp_solve is_activation_seed cj_custom_eqs
       (cfg_exit cj_cfg, ())"

text \<open>The single call site is \<open>Statement 4\<close>, resuming at \<open>Statement 5\<close>.\<close>

lemma cj_call_site:
  "cfg_calls_list cj_cfg =
     [(Statement 4, CallEdge (Some (STR ''z'')) [STR ''p''] [VIMP_Syntax.N 7],
       FunctionEntry (STR ''mark''), Statement 5)]"
  by eval

text \<open>
  Regression witness.  Before the call the two solved systems agree, so the edge
  transfers, \<^const>\<open>dgs_enter\<close> and the caller continuation are doing the same
  thing in both.  At the resume point they disagree at \<open>r\<close>: the stock
  environment merge discards the callee's locals and keeps the caller's
  \<^const>\<open>SPos\<close>, while the callee-joining one publishes \<^const>\<open>STop\<close>.  The
  destination \<open>z\<close> agrees, because \<^const>\<open>dgs_combine_assign\<close> --- which performs
  the return assignment --- is the stock field in both specifications.
\<close>

lemma cj_agree_before_the_call:
  "cj_lookup (locals (snd cj_stock_sol (Inl (Statement 4, ())))) (STR ''r'') = SPos"
  "cj_lookup (locals (snd cj_custom_sol (Inl (Statement 4, ())))) (STR ''r'')  = SPos"
  by eval+

lemma cj_stock_keeps_caller_after_the_call:
  "cj_lookup (locals (snd cj_stock_sol (Inl (Statement 5, ())))) (STR ''r'') = SPos"
  by eval

lemma cj_callee_join_widens_after_the_call:
  "cj_lookup (locals (snd cj_custom_sol (Inl (Statement 5, ())))) (STR ''r'') = STop"
  by eval

lemma cj_return_assignment_unaffected:
  "cj_lookup (locals (snd cj_stock_sol (Inl (Statement 5, ())))) (STR ''z'') = SPos"
  "cj_lookup (locals (snd cj_custom_sol (Inl (Statement 5, ())))) (STR ''z'') = SPos"
  by eval+

end
