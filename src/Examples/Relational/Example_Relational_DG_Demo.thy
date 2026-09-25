theory Example_Relational_DG_Demo
  imports
    "Voblint_Routing.Compiled_Routed_Equations"
    "Voblint_Framework.DG_Reader_Transport"
    "Voblint_Exec.Ownership_Split_Exec"
    "Voblint_Analysis_Relational.Rel_Order_Domain"
    "Voblint_Analysis_Interval.Interval_Transfer"
    "Voblint_Analysis_Interval.Interval_Exec"
    "Voblint_Solver.TD_Solver_Bridge"
    "Voblint_Compile.Compile_Wellformed"
    "Voblint_CFG.CFG_Prune"
    "Voblint_VIMP.VIMP_Notation"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
section \<open>End-to-end demo: a relational analysis on the same executable pipeline as Interval\<close>

text \<open>
  @{theory Voblint_Analysis_Relational.Rel_Order_Domain} interprets
  \<^locale>\<open>analysis_contract\<close> over \<open>relc\<close>, a non-\<open>abs_state\<close> relational carrier,
  with zero DG-framework changes -- the mathematical half of the claim.
  This file is the executable half: the same CFG, the same generic
  \<open>compiled_routed_eqs_for\<close> generator, and the same vendored solver that runs Interval
  also run \<open>relc\<close>, end to end, with a genuinely different observable result.

  \<^bold>\<open>Program.\<close> \<open>if (x < y) { z = 1; } else { z = 0; }\<close>, with \<open>x\<close>/\<open>y\<close> left
  entirely unconstrained at entry (no prior assignment).  This is deliberately
  the case where Interval learns nothing from the guard: \<open>x < y\<close> narrows
  \<open>x\<close>'s interval only using \<open>y\<close>'s \<^emph>\<open>current\<close> upper bound, and vice versa;
  with both at \<open>[-inf,+inf]\<close>, the guard supplies no new bound for either
  variable.  \<open>relc\<close> instead records the pair \<open>(x,y)\<close> directly, because
  \<open>assume_step\<close> reads the guard's syntactic shape, not either variable's
  current abstract value.
\<close>

subsection \<open>The VIMP source program -- a full program block, not an inline stub\<close>

definition demo_program :: imp_prog where
  "demo_program = program { 
   fun main() { 
     if (x < y) 
        { z = 1; } 
     else 
        { z = 0; }
     } 
}"

subsection \<open>CFG construction\<close>

text \<open>No \<open>global\<close> declarations, so the classifier this program's own source gives
  is trivially false everywhere.\<close>
abbreviation demo_gs :: "vname \<Rightarrow> bool" where
  "demo_gs \<equiv> declared_global demo_program"

lemma demo_program_declared_global_vars [simp]:
  "declared_global_vars demo_program = []"
  by (simp add: demo_program_def)

text \<open>Local shorthand for the executable state's lookup projection, fixed at this
  file's own \<open>demo_gs\<close> classifier.\<close>
abbreviation demo_lookup :: "('a::bot) exec_dg_st \<Rightarrow> vname \<Rightarrow> 'a" where
  "demo_lookup s x \<equiv> lookup_resolved_st_q s (location_of demo_gs x)"

definition demo_pi :: proc_table where
  "demo_pi = prog_table demo_program"

definition demo_cfg :: cfg where
  "demo_cfg = compile_prog demo_pi (prog_procs demo_program)"

interpretation demo: compiled_cfg demo_pi "prog_procs demo_program" demo_cfg
  by (unfold_locales; unfold demo_cfg_def; simp add: compile_prog_finite)

text \<open>\<open>Statement 1\<close> is the true branch of the guard, right after the
  \<open>assume\<close> and before \<open>z := 1\<close> -- exactly where \<open>x < y\<close> is freshly known
  and nothing else has happened yet.  This is the read point both analyses
  are compared at.\<close>

subsection \<open>Interval, on the same CFG, same generator, same solver menu\<close>

definition demo_ivl_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (ivl exec_dg_st, ivl exec_dg_st) dg_state) strategy_tree" where
  "demo_ivl_eqs =
     compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
       (ownership_split_dg_spec_st_for demo_gs (ivl_tf_st_for demo_gs) (ivl_enter_st_for demo_gs))
       demo_cfg (initial_resolved_st_q ivl_top ivl_top)
       (restrict_global_resolved_q (initial_resolved_st_q ivl_top ivl_top))"

definition demo_ivl_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (ivl exec_dg_st, ivl exec_dg_st) dg_state)" where
  "demo_ivl_sol = TD_side_always_join_Interp_solve demo_ivl_eqs (cfg_exit demo_cfg, ())"

lemma demo_ivl_terminates:
  "TD_side_always_join_Interp_solve_c demo_ivl_eqs (cfg_exit demo_cfg, ()) \<noteq> None"
  by eval

subsection \<open>The relational analysis, on the very same CFG, generator, and solver\<close>

text \<open>\<open>rel_order_spec\<close> is already both the sound \<^emph>\<open>and\<close> the executable
  specification -- \<open>relc\<close> needed no \<open>Exec_St_Transfer\<close>-style refinement layer,
  so \<open>compiled_routed_eqs_for\<close> is applied to it directly, with no bridging step and no
  parallel generator.\<close>

definition demo_rel_eqs ::
  "pp \<times> unit \<Rightarrow> (pp \<times> unit, (unit, unit) routed_gk, (relc, relc) dg_state) strategy_tree" where
  "demo_rel_eqs = compiled_routed_eqs_for (Analysis_Global ()) Activation_Seed route_unit
     rel_order_spec demo_cfg top_relc top_relc"

definition demo_rel_sol ::
  "(pp \<times> unit) set \<times> (pp \<times> unit + (unit, unit) routed_gk \<Rightarrow> (relc, relc) dg_state)" where
  "demo_rel_sol = TD_side_always_join_Interp_solve demo_rel_eqs (cfg_exit demo_cfg, ())"

lemma demo_rel_terminates:
  "TD_side_always_join_Interp_solve_c demo_rel_eqs (cfg_exit demo_cfg, ()) \<noteq> None"
  by eval

subsection \<open>The comparison\<close>

text \<open>Interval's bound for \<open>x\<close> (and, symmetrically, \<open>y\<close>) at the true branch
  is unchanged from entry: the guard supplied no new information because
  neither operand had a finite bound for the other to narrow against.\<close>

lemma demo_ivl_x_at_branch:
  "demo_lookup (locals (snd demo_ivl_sol (Inl (Statement 1, ())))) (STR ''x'') = Ivl MinInf PlusInf"
  unfolding demo_ivl_sol_def demo_ivl_eqs_def by eval

lemma demo_ivl_y_at_branch:
  "demo_lookup (locals (snd demo_ivl_sol (Inl (Statement 1, ())))) (STR ''y'') = Ivl MinInf PlusInf"
  unfolding demo_ivl_sol_def demo_ivl_eqs_def by eval

text \<open>\<open>relc\<close>, at the very same point, has recorded the pair directly.
  The false branch is precise too: \<open>assume_not_step\<close> reads \<open>\<not>(x < y)\<close> as
  \<open>y \<le> x\<close>, the mirror image of the true branch's transfer -- Interval's
  guard transfer stays uninformative on both branches for the same reason
  it was on the true one.  Each witness also excludes \<open>Bot\<close> explicitly, so
  empty concretization cannot make the relation assertion hold vacuously.\<close>

lemma demo_rel_learns_xy:
  "locals (snd demo_rel_sol (Inl (Statement 1, ()))) \<noteq> Bot \<and>
   relc_has (STR ''x'') (STR ''y'')
     (locals (snd demo_rel_sol (Inl (Statement 1, ()))))"
  unfolding demo_rel_sol_def demo_rel_eqs_def by eval

lemma demo_rel_learns_yx:
  "locals (snd demo_rel_sol (Inl (Statement 2, ()))) \<noteq> Bot \<and>
   relc_has (STR ''y'') (STR ''x'')
     (locals (snd demo_rel_sol (Inl (Statement 2, ()))))"
  unfolding demo_rel_sol_def demo_rel_eqs_def by eval

text \<open>Side by side, the three lemmas above are the comparison: at \<open>Statement 1\<close>
  Interval's two bounds stay \<open>[-inf,+inf]\<close> while \<open>relc\<close> answers \<open>True\<close> for the
  pair \<open>(x,y)\<close>.\<close>

lemma direct_relational_order_guards:
  "assume_step (Greater (V x) (V y)) (RelC {}) = RelC {(y, x)}"
  "assume_step (LessEq (V x) (V y)) (RelC {}) = RelC {(x, y)}"
  "assume_not_step (GreaterEq (V x) (V y)) (RelC {}) = RelC {(x, y)}"
  "assume_not_step (NotEq (V x) (V y)) (RelC {}) = RelC {(x, y), (y, x)}"
  by (simp_all add: assume_step_def assume_not_step_def)

end


