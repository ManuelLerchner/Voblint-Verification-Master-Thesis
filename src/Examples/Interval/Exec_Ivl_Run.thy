theory Exec_Ivl_Run
  imports Voblint_Analysis.Ivl_Exec Voblint_Analysis.Interval_Exec_Sound
            Voblint_Core.Solver_Menu "Voblint_CFG.CFG_Prune"
            "Voblint_VIMP.VIMP_Notation"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
section \<open>Executable interval loop: backward filters + TD solver (eval only)\<close>

text \<open>
  Same program as @{text "Example_Interval_Loop_Coverage"} in session
  \<^session>\<open>Voblint_Formalization\<close>:
  @{text "x := 0; while (x < 20) { x := x + 1 }"}.

  The executable transfer \<open>ivl_tf_st_for\<close> applies the same forward-gated
  branch transfer as @{const branch_ivl} (via \<open>branch_ivl_st_for\<close> /
  @{const branch_ivl_st}) on @{const EA_Assume} edges.  Node~2 therefore
  reads @{text "[0,19]"} because @{text "x < 20"} refines @{text "x"} at the
  loop head --- not because of widening.

  This theory evaluates two fixpoint engines on @{const side_cfg_T_eff_st}:
  bounded Kleene iteration on @{const eq}, and @{const TD_side_warrowing_apinis_Interp_solve}
  (pointwise interval widening on @{typ "ivl resolved_st_q"} for solver termination).
  The example uses the trace-native post-fixpoint soundness theorem.
\<close>

definition loop_prog :: imp_prog where
  "loop_prog = program {
     void main() { x := 0; while (x < 20) { x := x + 1 } }
   }"

text \<open>No \<open>global\<close> declarations, so the classifier this program's own source
  gives is trivially false everywhere.\<close>
abbreviation loop_gs :: "vname \<Rightarrow> bool" where
  "loop_gs \<equiv> declared_global loop_prog"

lemma loop_prog_declared_global_vars [simp]:
  "declared_global_vars loop_prog = []"
  by (simp add: loop_prog_def)

definition loop_cfg :: cfg where
  "loop_cfg =
     \<lparr> intra =
         {(FunctionEntry (STR ''main''), EA_Nop, Statement 0),
          (Statement 0, EA_Assign (STR ''x'') (N 0), Statement 1),
          (Statement 1, EA_Assume (Less (V (STR ''x'')) (N 20)), Statement 2),
          (Statement 1, EA_AssumeNot (Less (V (STR ''x'')) (N 20)), Statement 3),
          (Statement 2, EA_Assign (STR ''x'') (Plus (V (STR ''x'')) (N 1)), Statement 1),
          (Statement 3, EA_Ret None (STR ''main''), FunctionResult (STR ''main''))},
       calls = {},
       cfg_entry = FunctionEntry (STR ''main''),
       checks = {} \<rparr>"

lemma loop_cfg_compiles:
  "loop_cfg = compile_prog (prog_table loop_prog) (prog_procs loop_prog) prog_main_name (prog_main loop_prog)"
  by eval

lemma loop_cfg_entry [simp]: "cfg_entry loop_cfg = FunctionEntry (STR ''main'')"
  by (simp add: loop_cfg_def)

lemma loop_cfg_exit [simp]: "cfg_exit loop_cfg = FunctionResult (STR ''main'')"
  by (simp add: loop_cfg_def cfg_exit_def)

definition loop_is_bot_pred :: "ivl resolved_st_q \<Rightarrow> bool" where
  "loop_is_bot_pred = resolved_st_q_is_bot_for (declared_global_vars loop_prog)"

definition loop_ivl_eqs :: "(pp, unit, ivl resolved_st_q lifted) eqsT" where
  "loop_ivl_eqs = side_cfg_T_eff_st loop_cfg (ivl_etf_st_for loop_is_bot_pred loop_gs) bot cinit_ivl_st ()"

definition loop_sig0 :: "pp + unit \<Rightarrow> ivl resolved_st_q lifted" where
  "loop_sig0 k =
     (case k of Inl _ \<Rightarrow> Bot | Inr () \<Rightarrow> Lifted (restrict_global_resolved_q cinit_ivl_st))"

definition loop_kleene_step :: "(pp + unit \<Rightarrow> ivl resolved_st_q lifted) \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q lifted)" where
  "loop_kleene_step sig =
     (\<lambda>k. case k of
        Inl v \<Rightarrow> eq loop_ivl_eqs v sig
      | Inr () \<Rightarrow> sig (Inr ()))"

fun loop_iter_sig :: "nat \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q lifted) \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q lifted)" where
  "loop_iter_sig 0 sig = sig"
| "loop_iter_sig (Suc n) sig = loop_iter_sig n (loop_kleene_step sig)"

definition loop_ivl_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl resolved_st_q lifted)" where
  "loop_ivl_sol =
     ({FunctionEntry (STR ''main''), FunctionResult (STR ''main'')}
        \<union> Statement ` {0, 1, 2, 3},
      loop_iter_sig 100 loop_sig0)"

definition loop_ivl_at :: "pp \<Rightarrow> ivl" where
  "loop_ivl_at pp = case_lifted bot (\<lambda>q. lookup_resolved_st_q q (location_of loop_gs (STR ''x'')))
     (snd loop_ivl_sol (Inl pp))"

text \<open>Loop head (node 1): @{text "[0,20]"}.  Body entry (node 2): @{text "[0,19]"} from
  @{const EA_Assume} backward refinement on @{text "x < 20"}.\<close>
value "string_of_ivl (loop_ivl_at (Statement 1))"
value "string_of_ivl (loop_ivl_at (Statement 2))"
value "string_of_ivl (loop_ivl_at (Statement 3))"

lemma loop_head_ivl:
  "loop_ivl_at (Statement 1) = Ivl (Fin 0) (Fin 20)"
  by eval

lemma loop_body_ivl:
  "loop_ivl_at (Statement 2) = Ivl (Fin 0) (Fin 19)"
  by eval

definition loop_ivl_td_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl resolved_st_q lifted)" where
  "loop_ivl_td_sol = TD_side_warrowing_apinis_Interp_solve loop_ivl_eqs (cfg_exit loop_cfg)"

definition loop_ivl_td_at :: "pp \<Rightarrow> ivl" where
  "loop_ivl_td_at pp = case_lifted bot (\<lambda>q. lookup_resolved_st_q q (location_of loop_gs (STR ''x'')))
     (snd loop_ivl_td_sol (Inl pp))"

text \<open>Widening TD (Apinis warrowing): same intervals as bounded Kleene --- backward
  filters carry the precision; widening is solver infrastructure only on this program.\<close>
value "string_of_ivl (loop_ivl_td_at (Statement 1))"
value "string_of_ivl (loop_ivl_td_at (Statement 2))"

lemma loop_head_ivl_td:
  "loop_ivl_td_at (Statement 1) = Ivl (Fin 0) (Fin 20)"
  by eval

lemma loop_body_ivl_td:
  "loop_ivl_td_at (Statement 2) = Ivl (Fin 0) (Fin 19)"
  by eval

subsection \<open>The loop under every update rule at once\<close>

text \<open>\<^const>\<open>run_menu\<close> reads the loop-head value of \<open>x\<close> under each update rule in one line,
  and here all three \<^emph>\<open>agree\<close> at the precise \<open>[0, 20]\<close>.  \<open>x\<close> is a bounded local: interval
  narrowing (fill an infinite bound from the guard-refined value) plus the backward guard
  filter on \<open>x < 20\<close> recovers the bound whether the global rule widens (\<open>warrow\<close>) or not
  (\<open>join\<close>, \<open>per_origin\<close>).  Contrast a flow-insensitive \<^emph>\<open>global\<close> counter, where the same
  machinery cannot bound the write-back and the slot stays \<open>[0, +inf]\<close>.\<close>
value "run_menu loop_gs loop_ivl_eqs (cfg_exit loop_cfg) (Inl (Statement 1)) (STR ''x'')"

lemma loop_head_across_update_rules:
  "run_menu loop_gs loop_ivl_eqs (cfg_exit loop_cfg) (Inl (Statement 1)) (STR ''x'')
     = [(STR ''join'',       Ivl (Fin 0) (Fin 20)),
        (STR ''per_origin'', Ivl (Fin 0) (Fin 20)),
        (STR ''warrow'',     Ivl (Fin 0) (Fin 20))]"
  unfolding loop_ivl_eqs_def run_menu_def solver_menu_def by eval

subsection \<open>Whole-program entry points, and a second program\<close>

text \<open>
  \<open>analyse_interval\<close>/\<open>analyse_interval_for\<close> and \<open>analyse_interval_td\<close>/
  \<open>analyse_interval_td_for\<close> now live in \<open>Interval_Exec_Sound\<close>'s whole-program
  convenience layer, alongside \<open>ivl_exec_prog\<close> --- \<open>loop_ivl_eqs\<close> here is
  built from the same @{const side_cfg_T_eff_st} pipeline those entry points
  use, not the native D/G spine (\<open>dg_gen_of\<close>) the Sign flagship
  (\<open>Exec_Sign_DG_Run\<close>) uses, so this file only needs to import them, not
  re-derive them.

  A different program from \<open>loop_prog\<close>, run through the very same
  \<open>analyse_interval\<close>: the entry point is not specialized to one hard-coded
  example.\<close>

definition analyse_interval_demo2_prog :: imp_prog where
  "analyse_interval_demo2_prog = program { void main() { a := 3; b := a + 1 } }"

lemma analyse_interval_demo2_terminates:
  "ivl_terminates_prog (declared_global analyse_interval_demo2_prog) prog_main_name
     analyse_interval_demo2_prog"
  by (rule ivl_terminates_prog_via_solve_c) eval

lemma analyse_interval_demo2_result:
  "case_lifted bot (\<lambda>\<sigma>. \<sigma>) (analyse_interval analyse_interval_demo2_prog) (STR ''b'')
     = Ivl (Fin 4) (Fin 4)"
  unfolding analyse_interval_def analyse_interval_for_def ivl_exec_prog_def
    ivl_exec_prog_at_def prog_cfg_def
  by eval

text \<open>
  \<open>analyse_interval_td\<close>/\<open>analyse_interval_td_for\<close> (\<open>Interval_Exec_Sound\<close>) mirror
  \<open>analyse_interval\<close>/\<open>analyse_interval_for\<close> but solve via the warrowing rule
  \<open>loop_ivl_td_sol\<close> uses above --- see that theory's comment for why \<open>M3\<close>
  (soundness) is deliberately left open for the warrowing variant.
\<close>

lemma analyse_interval_td_demo2_result:
  "case_lifted bot (\<lambda>\<sigma>. \<sigma>) (analyse_interval_td analyse_interval_demo2_prog) (STR ''b'')
     = Ivl (Fin 4) (Fin 4)"
  unfolding analyse_interval_td_def analyse_interval_td_for_def prog_cfg_def
  by eval

subsection \<open>Executable code generation\<close>

text \<open>
  No per-domain \<open>export_code\<close> here: both TD entry points, \<open>loop_ivl_sol\<close> (bounded Kleene) and
  \<open>loop_ivl_td_sol\<close> (Apinis warrowing), already export cleanly through Isabelle's code generator
  (confirmed once, historically, as the M1 codegen-closure milestone). \<open>analyse_interval\<close> and
  \<open>analyse_interval_td\<close> are reached by external callers through the unified dispatcher
  \<open>analyse\<close> (\<open>Analyse_Dispatch\<close>, downstream, which dispatches \<open>Interval_Analysis\<close> to
  \<open>analyse_interval_td_report\<close>) instead --- a second, domain-specific export module here would
  just be a parallel, redundant API surface for the same computation.
\<close>

end




