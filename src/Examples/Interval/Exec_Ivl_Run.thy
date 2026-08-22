theory Exec_Ivl_Run
  imports "Voblint_CLI.Interval_Codegen"
            Voblint_Core.Solver_Menu "Voblint_CFG.CFG_Prune"
            "Voblint_VIMP.VIMP_Notation"
            Example_Interval_Loop_Coverage
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
section \<open>Executable interval loop: backward filters + TD solver (eval only)\<close>

text \<open>
  The executable counterpart of
  \<^theory>\<open>Voblint_Examples.Example_Interval_Loop_Coverage\<close>, whose
  \<^const>\<open>loop_prog\<close> (@{text "x := 0; while (x < 20) { x := x + 1 }"}) and
  compiled \<open>loop_cfg\<close> this theory imports rather than restates: there it is
  carried to trace-native soundness, here through three fixpoint engines.

  The routed transfer \<open>ictx_spec\<close> applies the same forward-gated branch
  transfer as @{const branch_ivl} on @{const EA_Assume} edges.  Node~2
  therefore reads @{text "[0,19]"} because @{text "x < 20"} refines
  @{text "x"} at the loop head --- not because of widening.

  This theory runs several fixpoint engines on the one canonical routed
  equation system \<^const>\<open>ictx_eqs_prog\<close>: bounded Kleene iteration on
  @{const eq}, @{const TD_side_warrowing_apinis_Interp_solve} (pointwise
  interval widening for solver termination), and -- through
  \<^const>\<open>run_menu\<close> -- every update rule on the solver menu at once.  All of
  them agree here, which is the point: the precision comes from the backward
  guard filter, not from the solver.
\<close>

text \<open>\<^const>\<open>loop_prog\<close> and its compiled \<open>loop_cfg\<close> come from
  \<^theory>\<open>Voblint_Examples.Example_Interval_Loop_Coverage\<close>, which also carries the
  edge-set literal (\<open>loop_cfg_full\<close>) and the trace-native soundness this theory's
  computed bounds are the executable counterpart of. No \<open>global\<close> declarations,
  so the classifier this program's own source gives is trivially false
  everywhere.\<close>

abbreviation loop_gs :: "vname \<Rightarrow> bool" where
  "loop_gs \<equiv> declared_global loop_prog"

lemma loop_prog_declared_global_vars [simp]:
  "declared_global_vars loop_prog = []"
  by (simp add: loop_prog_def)

declare loop_cfg_entry [simp]

lemma loop_cfg_exit [simp]: "cfg_exit loop_cfg = FunctionResult (STR ''main'')"
  by (simp add: loop_cfg_full cfg_exit_def)

definition loop_ivl_eqs ::
    "(pp \<times> unit, gk, (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state) eqsT" where
  "loop_ivl_eqs = ictx_eqs_prog loop_gs prog_main_name loop_prog"

text \<open>One projection, reused by every engine below: take a solved D/G slot's local
  component and read \<open>x\<close> out of it.\<close>

definition loop_read_x ::
    "(ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state \<Rightarrow> ivl" where
  "loop_read_x d =
     case_lifted bot (\<lambda>q. lookup_resolved_st_q q (location_of loop_gs (STR ''x''))) (locals d)"

definition loop_sig0 ::
    "pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state" where
  "loop_sig0 = (\<lambda>_. bot)"

definition loop_kleene_step ::
    "(pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       \<Rightarrow> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "loop_kleene_step sig =
     (\<lambda>k. case k of
        Inl v \<Rightarrow> eq loop_ivl_eqs v sig
      | Inr g \<Rightarrow> sig (Inr g))"

fun loop_iter_sig ::
    "nat \<Rightarrow> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)
       \<Rightarrow> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "loop_iter_sig 0 sig = sig"
| "loop_iter_sig (Suc n) sig = loop_iter_sig n (loop_kleene_step sig)"

definition loop_ivl_at :: "pp \<Rightarrow> ivl" where
  "loop_ivl_at pp = loop_read_x (loop_iter_sig 100 loop_sig0 (Inl (pp, ())))"

text \<open>Loop head (node 1): @{text "[0,20]"}.  Body entry (node 2): @{text "[0,19]"} from
  @{const EA_Assume} backward refinement on @{text "x < 20"}.\<close>
lemma loop_head_ivl:
  "loop_ivl_at (Statement 1) = Ivl (Fin 0) (Fin 20)"
  by (simp add: loop_ivl_at_def) eval

lemma loop_body_ivl:
  "loop_ivl_at (Statement 2) = Ivl (Fin 0) (Fin 19)"
  by (simp add: loop_ivl_at_def) eval

definition loop_ivl_td_sol ::
    "(pp \<times> unit) set
       \<times> (pp \<times> unit + gk \<Rightarrow> (ivl exec_dg_st lifted, ivl exec_dg_st lifted) dg_state)" where
  "loop_ivl_td_sol = ictx_sol_prog_warrow loop_gs prog_main_name loop_prog"

definition loop_ivl_td_at :: "pp \<Rightarrow> ivl" where
  "loop_ivl_td_at pp = loop_read_x (snd loop_ivl_td_sol (Inl (pp, ())))"

text \<open>Widening TD (Apinis warrowing): same intervals as bounded Kleene --- backward
  filters carry the precision; widening is solver infrastructure only on this program.\<close>
lemma loop_head_ivl_td:
  "loop_ivl_td_at (Statement 1) = Ivl (Fin 0) (Fin 20)"
  by (simp add: loop_ivl_td_at_def) eval

lemma loop_body_ivl_td:
  "loop_ivl_td_at (Statement 2) = Ivl (Fin 0) (Fin 19)"
  by (simp add: loop_ivl_td_at_def) eval

subsection \<open>The loop under every update rule at once\<close>

text \<open>\<^const>\<open>run_menu\<close> reads the loop-head value of \<open>x\<close> under each update rule in one line,
  and here all three \<^emph>\<open>agree\<close> at the precise \<open>[0, 20]\<close>.  \<open>x\<close> is a bounded local: interval
  narrowing (fill an infinite bound from the guard-refined value) plus the backward guard
  filter on \<open>x < 20\<close> recovers the bound whether the global rule widens (\<open>warrow\<close>) or not
  (\<open>join\<close>, \<open>per_origin\<close>).  Contrast a flow-insensitive \<^emph>\<open>global\<close> counter, where the same
  machinery cannot bound the write-back and the slot stays \<open>[0, +inf]\<close>.\<close>
lemma loop_head_across_update_rules:
  "run_menu loop_read_x loop_ivl_eqs (cfg_exit loop_cfg, ()) (Inl (Statement 1, ()))
     = [(STR ''join'',              Ivl (Fin 0) (Fin 20)),
        (STR ''per_origin'',        Ivl (Fin 0) (Fin 20)),
        (STR ''warrow'',            Ivl (Fin 0) (Fin 20)),
        (STR ''warrow_per_origin'', Ivl (Fin 0) (Fin 20))]"
  by eval

subsection \<open>Whole-program entry points, and a second program\<close>

text \<open>
  \<open>analyse_interval_join_result_for\<close> and \<open>analyse_interval_td_result_for\<close>
  (\<open>Interval_Checks\<close>) are the whole-program convenience layer over the very
  \<^const>\<open>ictx_eqs_prog\<close> system \<open>loop_ivl_eqs\<close> above is, under the join and the
  Apinis-warrowing update rule respectively. A different program from
  \<open>loop_prog\<close>, run through them: the entry points are not specialized to one
  hard-coded example.\<close>

definition analyse_interval_demo2_prog :: imp_prog where
  "analyse_interval_demo2_prog = program { void main() { a := 3; b := a + 1 } }"

lemma analyse_interval_demo2_terminates:
  "ictx_terminates_prog (declared_global analyse_interval_demo2_prog) prog_main_name
     analyse_interval_demo2_prog"
  by (rule ictx_terminates_prog_via_solve_c) eval

definition analyse_interval_demo2_env :: "vname \<Rightarrow> ivl" where
  "analyse_interval_demo2_env =
     (case lookup_context
             (analyse_interval_join_result analyse_interval_demo2_prog)
             (cfg_exit (prog_cfg prog_main_name analyse_interval_demo2_prog)) () of
        Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"

lemma analyse_interval_demo2_result:
  "analyse_interval_demo2_env (STR ''b'') = Ivl (Fin 4) (Fin 4)"
  by (simp add: analyse_interval_demo2_env_def) eval

text \<open>
  \<open>analyse_interval_td_result_for\<close> mirrors \<open>analyse_interval_join_result_for\<close>
  but solves via the warrowing rule \<open>loop_ivl_td_sol\<close> uses above. On this
  program the two agree exactly.
\<close>

definition analyse_interval_td_demo2_env :: "vname \<Rightarrow> ivl" where
  "analyse_interval_td_demo2_env =
     (case lookup_context
             (analyse_interval_td_result analyse_interval_demo2_prog)
             (cfg_exit (prog_cfg prog_main_name analyse_interval_demo2_prog)) () of
        Unreachable \<Rightarrow> bot | Reachable st \<Rightarrow> st)"

lemma analyse_interval_td_demo2_result:
  "analyse_interval_td_demo2_env (STR ''b'') = Ivl (Fin 4) (Fin 4)"
  by (simp add: analyse_interval_td_demo2_env_def) eval

subsection \<open>Executable code generation\<close>

text \<open>
  No per-domain \<open>export_code\<close> here.  External callers reach the Interval
  analysis through the unified dispatcher \<open>analyse\<close> (\<open>Analyse_Dispatch\<close>,
  which routes \<open>Interval_Analysis\<close> to \<open>analyse_interval_td_report\<close>); a
  second, domain-specific export module would just be a parallel, redundant
  API surface for the same computation.
\<close>

end
