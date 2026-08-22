theory Example_Sign_DG_Custom_Combine
  imports
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Sign_DG"
    "Voblint_Core.Solver_Menu"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation"
begin


section \<open>An analysis-supplied return combine on the D/G spine\<close>

text \<open>
  The call-return environment merge is a field of \<^typ>\<open>('dl, 'dg) dg_spec\<close>, not a
  formula built into the equation generator or the solver:
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
  \<^const>\<open>unit_combine_step_st_env\<close> rebuilds the returning environment from the
  caller's locals and the current global slot, discarding the callee's locals
  entirely: only \<^const>\<open>ret_var\<close> survives, through the return assignment that
  \<^const>\<open>dgs_combine_assign\<close> performs afterwards.  \<open>sign_combine_env_callee_join\<close>
  keeps them, joining the callee-exit locals into the caller's before the same
  reassembly.  Joining can only move the result up the lattice, so the merge
  stays sound; it is strictly less precise, and it is a different operation.  On
  a variable the caller left \<^const>\<open>SPos\<close> and the callee left \<^const>\<open>SNeg\<close>, the
  stock merge keeps \<^const>\<open>SPos\<close> while this one publishes \<^const>\<open>STop\<close>.
\<close>

definition sign_combine_env_callee_join ::
  "'a::bounded_semilattice_sup_bot exec_dg_st \<Rightarrow> 'a exec_dg_st \<Rightarrow> 'a exec_dg_st
   \<Rightarrow> 'a exec_dg_st \<times> 'a exec_dg_st" where
  "sign_combine_env_callee_join dc de g =
     unit_combine_step_st_env (dc \<squnion> restrict_local_resolved_q de) de g"


subsection \<open>The Sign specification that uses it\<close>

definition sign_dg_spec_callee_join ::
  "(vname \<Rightarrow> bool)
   \<Rightarrow> (edge_action \<Rightarrow> sign exec_dg_st \<Rightarrow> sign exec_dg_st)
   \<Rightarrow> (vname list \<Rightarrow> exp list \<Rightarrow> sign exec_dg_st \<Rightarrow> sign exec_dg_st)
   \<Rightarrow> (sign exec_dg_st, sign exec_dg_st) dg_spec" where
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
  "lookup_resolved_st_q
     (snd (unit_combine_step_st_env cj_caller cj_callee bot))
     (Local_Location (STR ''r'')) = SPos"
  by (simp add: cj_caller_def cj_callee_def unit_combine_step_st_env_def)

lemma callee_join_env_publishes_top:
  "lookup_resolved_st_q
     (snd (sign_combine_env_callee_join cj_caller cj_callee bot))
     (Local_Location (STR ''r'')) = STop"
  by (simp add: cj_caller_def cj_callee_def sign_combine_env_callee_join_def
      unit_combine_step_st_env_def sup_sign_def)

lemma sign_combine_env_callee_join_neq_stock:
  "(sign_combine_env_callee_join :: sign exec_dg_st \<Rightarrow> _) \<noteq> unit_combine_step_st_env"
proof
  assume "(sign_combine_env_callee_join :: sign exec_dg_st \<Rightarrow> _) = unit_combine_step_st_env"
  from fun_cong[OF fun_cong[OF fun_cong[OF this, of cj_caller], of cj_callee], of bot]
  have "sign_combine_env_callee_join cj_caller cj_callee bot
          = unit_combine_step_st_env cj_caller cj_callee bot" .
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
  one the stock specification hands it, and
  @{thm unit_combine_step_assign_for_mono} says the return assignment is monotone
  in exactly that argument.  Both components of the combine therefore move up,
  and \<^const>\<open>gamma_unit\<close>'s monotonicity carries the stock membership across.  No
  second soundness chain appears: this instance reuses
  @{thm sound_dg_spec_unit_for} for everything else.
\<close>

definition combine_env_callee_join_abs ::
  "(vname \<Rightarrow> bool) \<Rightarrow> call_info \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state
   \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state \<times> 'a abs_state" where
  "combine_env_callee_join_abs gs ci dc de g =
     unit_combine_step_env_for gs ci (dc \<squnion> restrict_local_for gs de) de g"

definition sign_dg_spec_env_join ::
  "(vname \<Rightarrow> bool) \<Rightarrow> (sign abs_state, sign abs_state) dg_spec" where
  "sign_dg_spec_env_join gs =
     (unit_dg_spec_for gs (sign_tf_for gs))
       \<lparr> dgs_combine_env := combine_env_callee_join_abs gs \<rparr>"

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

text \<open>Both specifications reach the same \<^const>\<open>dgs_combine_assign\<close>, differing
  only in the environment it receives.\<close>

lemma dgs_combine_unit_dg_spec_for_shape:
  "dgs_combine (unit_dg_spec_for gs tf) ci dc de g
     = unit_combine_step_assign_for gs ci de g (unit_combine_step_env_for gs ci dc de g)"
  by (simp add: dgs_combine_def unit_dg_spec_for_def)

lemma dgs_combine_sign_dg_spec_env_join_shape:
  "dgs_combine (sign_dg_spec_env_join gs) ci dc de g
     = unit_combine_step_assign_for gs ci de g (combine_env_callee_join_abs gs ci dc de g)"
  by (simp add: dgs_combine_def sign_dg_spec_env_join_def unit_dg_spec_for_def)

lemma combine_env_callee_join_abs_join:
  "fst (combine_env_callee_join_abs gs ci dc de g)
     \<squnion> snd (combine_env_callee_join_abs gs ci dc de g)
   = combine_env_abs gs (dc \<squnion> restrict_local_for gs de) g"
  unfolding combine_env_callee_join_abs_def
  by (rule unit_combine_step_env_for_join)

lemma combine_env_callee_join_abs_ge:
  "fst (unit_combine_step_env_for gs ci dc de g)
     \<squnion> snd (unit_combine_step_env_for gs ci dc de g)
   \<le> fst (combine_env_callee_join_abs gs ci dc de g)
     \<squnion> snd (combine_env_callee_join_abs gs ci dc de g)"
  unfolding unit_combine_step_env_for_join combine_env_callee_join_abs_join
  by (rule combine_env_abs_mono1[OF sup_ge1])

lemma dgs_combine_sign_dg_spec_env_join_ge:
  "fst (dgs_combine (unit_dg_spec_for gs (sign_tf_for gs)) ci dc de g)
     \<le> fst (dgs_combine (sign_dg_spec_env_join gs) ci dc de g)"
  "snd (dgs_combine (unit_dg_spec_for gs (sign_tf_for gs)) ci dc de g)
     \<le> snd (dgs_combine (sign_dg_spec_env_join gs) ci dc de g)"
  unfolding dgs_combine_unit_dg_spec_for_shape dgs_combine_sign_dg_spec_env_join_shape
  by (rule unit_combine_step_assign_for_mono[OF order_refl combine_env_callee_join_abs_ge])+

lemma gamma_unit_combine_sound_env_join:
  assumes reserved: "reserved_ret_var gs"
    and s: "s \<in> gamma_unit gs dcont g" and t: "t \<in> gamma_unit gs de g"
  shows "combine_collect gs (ci_dst ci) s t \<in>
           (case dgs_combine (sign_dg_spec_env_join gs) ci dcont de g of
              (g', d') \<Rightarrow> gamma_unit gs d' g')"
proof -
  interpret stock: sound_dg_spec
    "unit_dg_spec_for gs (sign_tf_for gs)" "gamma_unit gs" gs
    by (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for reserved])
  have stock_in: "combine_collect gs (ci_dst ci) s t
      \<in> gamma_unit gs (snd (dgs_combine (unit_dg_spec_for gs (sign_tf_for gs)) ci dcont de g))
                      (fst (dgs_combine (unit_dg_spec_for gs (sign_tf_for gs)) ci dcont de g))"
    using stock.combine_sound[OF s t] by (simp add: case_prod_beta)
  have widen: "gamma_unit gs (snd (dgs_combine (unit_dg_spec_for gs (sign_tf_for gs)) ci dcont de g))
                             (fst (dgs_combine (unit_dg_spec_for gs (sign_tf_for gs)) ci dcont de g))
      \<subseteq> gamma_unit gs (snd (dgs_combine (sign_dg_spec_env_join gs) ci dcont de g))
                       (fst (dgs_combine (sign_dg_spec_env_join gs) ci dcont de g))"
    by (rule gamma_unit_mono[OF dgs_combine_sign_dg_spec_env_join_ge(2)
          dgs_combine_sign_dg_spec_env_join_ge(1)])
  from stock_in widen show ?thesis by (auto simp: case_prod_beta)
qed

theorem sound_dg_spec_sign_dg_spec_env_join:
  assumes reserved: "reserved_ret_var gs"
  shows "sound_dg_spec (sign_dg_spec_env_join gs) (gamma_unit gs) gs"
proof -
  interpret stock: sound_dg_spec
    "unit_dg_spec_for gs (sign_tf_for gs)" "gamma_unit gs" gs
    by (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for reserved])
  show ?thesis
    apply unfold_locales
    subgoal for d d' g g'
      by (rule gamma_unit_mono)
    subgoal for a d g
      using stock.step_sound by simp
    subgoal premises prems
      using stock.caller_cont_sound[OF prems] by simp
    subgoal premises prems
      by (rule gamma_unit_combine_sound_env_join[OF reserved prems])
    subgoal premises prems
      using stock.enter_sound[OF prems] by simp
    done
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
  "cj_cfg = compile_prog (prog_table cj_program) (prog_procs cj_program)
              prog_main_name (prog_main cj_program)"

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
