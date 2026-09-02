theory Example_Sign_DG_Custom_Combine
  imports
    "Voblint_Exec.Exec_DG_Generator"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Framework.DG_LTR_Sound"
    "Voblint_Analysis.Sign_Transfer"
    "Voblint_Solver.TD_Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation" "Voblint_Compile.Compile_Wellformed"
begin


section \<open>An analysis-supplied return combine on the D/G spine\<close>

text \<open>
  The call-return environment merge is a field of \<^typ>\<open>('x, 'k, 'v, 'dl, 'dg) dg_spec\<close>,
  not a formula built into the equation generator or the solver:
  \<^const>\<open>dgs_combine_env\<close> is what \<^const>\<open>dgs_combine\<close> consults before handing the
  merged environment to \<^const>\<open>dgs_combine_assign\<close>.  This theory witnesses that
  the field is genuinely free.  It takes the ordinary executable Sign
  specification, overrides \<^emph>\<open>only\<close> that one field, and runs the result through
  the same \<^const>\<open>dg_gen_of\<close> generator and the same vendored solver a production
  analysis uses.  Every other field --- the caller continuation, the edge
  transfers, \<^const>\<open>dgs_enter\<close>, and \<^const>\<open>dgs_combine_assign\<close> --- is the stock
  one, so the observed difference isolates exactly that degree of freedom.
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
  "sign_dg_spec_callee_join gs tf_st enter_st =
     (unit_dg_spec_st_for gs tf_st enter_st)
       \<lparr> dgs_combine_env := (\<lambda>ci. sign_combine_env_callee_join) \<rparr>"

text \<open>Only the environment merge differs; every other field is the stock one.\<close>

lemma dgs_caller_cont_sign_dg_spec_callee_join [simp]:
  "dgs_caller_cont (sign_dg_spec_callee_join gs tf_st enter_st)
     = dgs_caller_cont (unit_dg_spec_st_for gs tf_st enter_st)"
  by (simp add: sign_dg_spec_callee_join_def)

lemma dgs_enter_sign_dg_spec_callee_join [simp]:
  "dgs_enter (sign_dg_spec_callee_join gs tf_st enter_st)
     = dgs_enter (unit_dg_spec_st_for gs tf_st enter_st)"
  by (simp add: sign_dg_spec_callee_join_def)

lemma dgs_combine_assign_sign_dg_spec_callee_join [simp]:
  "dgs_combine_assign (sign_dg_spec_callee_join gs tf_st enter_st)
     = dgs_combine_assign (unit_dg_spec_st_for gs tf_st enter_st)"
  by (simp add: sign_dg_spec_callee_join_def)

lemma dg_spec_step_sign_dg_spec_callee_join [simp]:
  "dg_spec_step (sign_dg_spec_callee_join gs tf_st enter_st) a
     = dg_spec_step (unit_dg_spec_st_for gs tf_st enter_st) a"
  by (cases a) (simp_all add: sign_dg_spec_callee_join_def)

lemma dgs_combine_env_sign_dg_spec_callee_join [simp]:
  "dgs_combine_env (sign_dg_spec_callee_join gs tf_st enter_st)
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
  record field of \<^const>\<open>unit_dg_spec_for\<close>, so \<^const>\<open>dg_spec_step\<close>,
  \<^const>\<open>dgs_caller_cont\<close>, \<^const>\<open>dgs_enter\<close> and \<^const>\<open>dgs_combine_assign\<close> are
  the stock ones and their obligations transfer verbatim.

  Only \<open>combine_sound\<close> needs an argument, and it is the generic one: the merged
  environment this specification hands \<^const>\<open>dgs_combine_assign\<close> is above the
  one the stock specification hands it, and the return assignment and both
  projections are monotone in exactly that argument. So the answer and the
  published contribution both move up, and \<^const>\<open>gamma_unit\<close>'s monotonicity
  carries the stock membership across. No second soundness chain appears: this
  instance reuses \<open>sound_dg_spec_unit_for\<close> for everything else.
\<close>

definition combine_env_callee_join_abs ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> ('x,'k,unit,'a::bounded_semilattice_sup_bot abs_state,'a abs_state) man_combine_transfer"
where
  "combine_env_callee_join_abs gs =
     local_combine_transfer (\<lambda>dc de. dc \<squnion> restrict_local_for gs de)"

definition sign_dg_spec_env_join ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('x,'k,unit,sign abs_state, sign abs_state) dg_spec" where
  "sign_dg_spec_env_join gs =
     (unit_dg_spec_for gs (sign_tf_for gs))
       \<lparr> dgs_combine_env := (\<lambda>ci. combine_env_callee_join_abs gs) \<rparr>"

lemma dg_spec_step_sign_dg_spec_env_join [simp]:
  "dg_spec_step (sign_dg_spec_env_join gs) a
     = dg_spec_step (unit_dg_spec_for gs (sign_tf_for gs)) a"
  by (cases a) (simp_all add: sign_dg_spec_env_join_def)

lemma dgs_caller_cont_sign_dg_spec_env_join [simp]:
  "dgs_caller_cont (sign_dg_spec_env_join gs)
     = dgs_caller_cont (unit_dg_spec_for gs (sign_tf_for gs))"
  by (simp add: sign_dg_spec_env_join_def)

lemma dgs_enter_sign_dg_spec_env_join [simp]:
  "dgs_enter (sign_dg_spec_env_join gs)
     = dgs_enter (unit_dg_spec_for gs (sign_tf_for gs))"
  by (simp add: sign_dg_spec_env_join_def)

text \<open>
  Both specifications run the same \<^const>\<open>dgs_combine_assign\<close>; they differ only
  in the local value it starts from. That is the whole content of the override,
  and it is what the two observations below inherit.
\<close>

lemma dg_spec_combine_transfer_env_join:
  "dg_spec_combine_transfer (sign_dg_spec_env_join gs) ci m de
     = unit_combine_transfer gs ci
         (man_with_local m (man_local m \<squnion> restrict_local_for gs de)) de"
  unfolding dg_spec_combine_transfer_def dgs_combine_def sign_dg_spec_env_join_def
    combine_env_callee_join_abs_def unit_dg_spec_for_def
  by (simp add: local_transfer_def local_combine_transfer_def man_with_local_def)

subsection \<open>The override only ever widens\<close>

text \<open>
  The merged environment this specification hands the return assignment sits
  above the stock one, and every step from there is monotone: the assignment
  writes the same return value into a larger state, and both projections of the
  result preserve the order. So the answer and the published contribution both
  move up, and \<^const>\<open>gamma_unit\<close>'s monotonicity carries the stock membership
  across. No second soundness chain appears --- everything but the combine is
  inherited from \<open>sound_dg_spec_unit_for\<close>.
\<close>

lemma combine_assign_mono:
  fixes sigma tau :: "'a::order abs_state"
  assumes "sigma \<le> tau"
  shows "combine_assign dst v sigma \<le> combine_assign dst v tau"
  using assms by (cases dst) (auto simp: le_fun_def)

lemma combine_env_join_ge:
  "combine_env gs dc g \<le> combine_env gs (dc \<squnion> restrict_local_for gs de) g"
  by (rule combine_env_mono[OF sup_ge1 order_refl])

text \<open>The override's own tree observations. The generic reduction rules do not
  fire here: the transfer is wrapped in the lambda that rebuilds the manager
  with the joined local, so it is reduced once explicitly.\<close>

lemma traverse_combine_env_join:
  "locals (traverse_rhs (dg_spec_combine_tree
       (sign_dg_spec_env_join gs) ci src_cc src_ex (\<lambda>_. gk)) \<tau>)
     = restrict_local_for gs
         (combine_assign (ci_dst ci) (locals (\<tau> src_ex) ret_var)
            (combine_env gs (locals (\<tau> src_cc) \<squnion> restrict_local_for gs (locals (\<tau> src_ex)))
               (globs (\<tau> (Inr gk)))))"
  unfolding dg_spec_combine_tree_def dg_spec_combine_transfer_env_join
    unit_combine_transfer_def
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def
        unit_combine_transfer_gen_def unit_transfer_gen_def mk_dg_man_def
        man_with_local_def dg_read_at_def dg_read_global_def dg_sideg_def
        sp_bind_assoc Let_def)

lemma sides_combine_env_join:
  "globs (sides_of_rhs (dg_spec_combine_tree
       (sign_dg_spec_env_join gs) ci src_cc src_ex (\<lambda>_. gk)) \<tau> (Inr gk))
     = restrict_global_for gs
         (combine_assign (ci_dst ci) (locals (\<tau> src_ex) ret_var)
            (combine_env gs (locals (\<tau> src_cc) \<squnion> restrict_local_for gs (locals (\<tau> src_ex)))
               (globs (\<tau> (Inr gk)))))"
  unfolding dg_spec_combine_tree_def dg_spec_combine_transfer_env_join
    unit_combine_transfer_def
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def
        unit_combine_transfer_gen_def unit_transfer_gen_def mk_dg_man_def
        man_with_local_def dg_read_at_def dg_read_global_def dg_sideg_def
        sp_bind_assoc Let_def)

text \<open>The stock observations, in the same shape, so the comparison below is
  between two equations rather than between a tree and an equation.\<close>

lemma traverse_combine_stock:
  "locals (traverse_rhs (dg_spec_combine_tree
       (unit_dg_spec_for gs tf) ci src_cc src_ex (\<lambda>_. gk)) \<tau>)
     = restrict_local_for gs
         (combine_assign (ci_dst ci) (locals (\<tau> src_ex) ret_var)
            (combine_env gs (locals (\<tau> src_cc)) (globs (\<tau> (Inr gk)))))"
  unfolding dg_spec_combine_tree_def dg_spec_combine_transfer_unit_dg_spec_for
    unit_combine_transfer_def by simp

lemma sides_combine_stock:
  "globs (sides_of_rhs (dg_spec_combine_tree
       (unit_dg_spec_for gs tf) ci src_cc src_ex (\<lambda>_. gk)) \<tau> (Inr gk))
     = restrict_global_for gs
         (combine_assign (ci_dst ci) (locals (\<tau> src_ex) ret_var)
            (combine_env gs (locals (\<tau> src_cc)) (globs (\<tau> (Inr gk)))))"
  unfolding dg_spec_combine_tree_def dg_spec_combine_transfer_unit_dg_spec_for
    unit_combine_transfer_def by simp

lemma traverse_combine_env_join_ge:
  "locals (traverse_rhs (dg_spec_combine_tree
       (unit_dg_spec_for gs (sign_tf_for gs)) ci src_cc src_ex (\<lambda>_. gk)) \<tau>)
     \<le> locals (traverse_rhs (dg_spec_combine_tree
          (sign_dg_spec_env_join gs) ci src_cc src_ex (\<lambda>_. gk)) \<tau>)"
  unfolding traverse_combine_stock traverse_combine_env_join
  by (rule restrict_local_for_mono[OF combine_assign_mono[OF combine_env_join_ge]])

lemma sides_combine_env_join_ge:
  "globs (sides_of_rhs (dg_spec_combine_tree
       (unit_dg_spec_for gs (sign_tf_for gs)) ci src_cc src_ex (\<lambda>_. gk)) \<tau> (Inr gk))
     \<le> globs (sides_of_rhs (dg_spec_combine_tree
          (sign_dg_spec_env_join gs) ci src_cc src_ex (\<lambda>_. gk)) \<tau> (Inr gk))"
  unfolding sides_combine_stock sides_combine_env_join
  by (rule restrict_global_for_mono[OF combine_assign_mono[OF combine_env_join_ge]])

theorem sound_dg_spec_sign_dg_spec_env_join:
  assumes reserved: "reserved_ret_var gs"
  shows "sound_dg_spec (sign_dg_spec_env_join gs) (gamma_unit gs) gs"
proof -
  interpret stock: sound_dg_spec
    "unit_dg_spec_for gs (sign_tf_for gs)" "gamma_unit gs" gs
    by (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for reserved])
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 d d' g g')
    then show ?case by (rule gamma_unit_mono)
  next
    case (2 a \<tau> src gk)
    show ?case using stock.step_sound by (simp add: dg_spec_edge_tree_def)
  next
    case (3 s \<tau> src gk ci)
    then show ?case using stock.enter_sound by simp
  next
    case (4 s \<tau> src_cc gk t src_ex ci)
    from stock.combine_sound[OF 4] show ?case
      by (rule subsetD[OF gamma_unit_mono
            [OF traverse_combine_env_join_ge sides_combine_env_join_ge]])
  qed
qed

subsection \<open>The solved result really differs\<close>

text \<open>
  \<open>cj_program\<close>'s callee writes \<^const>\<open>SNeg\<close> to \<open>r\<close>, a name the caller already
  holds as \<^const>\<open>SPos\<close> across the call.  Both specifications compile the same
  program to the same CFG, generate equations with the same
  \<^const>\<open>dg_gen_of\<close>, and are solved by the same vendored solver; only
  \<^const>\<open>dgs_combine_env\<close> differs between them.
\<close>

definition cj_program :: imp_prog where
  "cj_program = program {
     void mark(p) { r := 0 - 1; return p }
     void main() { r := 1; z := mark(7) }
   }"

abbreviation cj_prog_gs :: "vname \<Rightarrow> bool" where
  "cj_prog_gs \<equiv> declared_global cj_program"

definition cj_cfg :: cfg where
  "cj_cfg = compile_prog (prog_table cj_program) (prog_procs cj_program)"

abbreviation cj_lookup :: "sign exec_dg_st \<Rightarrow> vname \<Rightarrow> sign" where
  "cj_lookup s x \<equiv> lookup_resolved_st_q s (location_of cj_prog_gs x)"

definition cj_stock_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "cj_stock_eqs = dg_gen_of
     (unit_dg_spec_st_for cj_prog_gs (sign_tf_st_for cj_prog_gs) (sign_enter_st_for cj_prog_gs))
     cj_cfg bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

definition cj_custom_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, unit, (sign exec_dg_st, sign exec_dg_st) dg_state) strategy_tree" where
  "cj_custom_eqs = dg_gen_of
     (sign_dg_spec_callee_join cj_prog_gs (sign_tf_st_for cj_prog_gs) (sign_enter_st_for cj_prog_gs))
     cj_cfg bot cinit_sign_st (restrict_global_resolved_q cinit_sign_st)"

lemma cj_stock_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c cj_stock_eqs (cfg_exit cj_cfg, ()) \<noteq> None"
  by eval

lemma cj_custom_terminates:
  "TD_side_warrowing_apinis_Interp_solve_c cj_custom_eqs (cfg_exit cj_cfg, ()) \<noteq> None"
  by eval

definition cj_stock_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "cj_stock_sol = TD_side_warrowing_apinis_Interp_solve cj_stock_eqs (cfg_exit cj_cfg, ())"

definition cj_custom_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + unit \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_state)" where
  "cj_custom_sol = TD_side_warrowing_apinis_Interp_solve cj_custom_eqs (cfg_exit cj_cfg, ())"

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
