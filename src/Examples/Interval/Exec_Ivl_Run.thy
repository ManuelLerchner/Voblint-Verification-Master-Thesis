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

  The executable transfer \<open>ivl_tf_st_for\<close> applies the same backward guard
  filters as @{const assume_ivl} (via \<open>assume_ivl_st_for\<close> / @{const bfilter_ivl_st})
  on @{const EA_Assume} edges.  Node~2 therefore reads @{text "[0,19]"} because
  @{text "x < 20"} refines @{text "x"} at the loop head --- not because of widening.

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
         {(FunctionEntry ''main'', EA_Nop, Statement 0),
          (Statement 0, EA_Assign ''x'' (N 0), Statement 1),
          (Statement 1, EA_Assume (Less (V ''x'') (N 20)), Statement 2),
          (Statement 1, EA_AssumeNot (Less (V ''x'') (N 20)), Statement 3),
          (Statement 2, EA_Assign ''x'' (Plus (V ''x'') (N 1)), Statement 1),
          (Statement 3, EA_Ret None ''main'', FunctionResult ''main'')},
       calls = {},
       cfg_entry = FunctionEntry ''main'',
       checks = {} \<rparr>"

lemma loop_cfg_compiles:
  "loop_cfg = compile_prog (prog_table loop_prog) (prog_procs loop_prog) prog_main_name (prog_main loop_prog)"
  by eval

lemma loop_cfg_entry [simp]: "cfg_entry loop_cfg = FunctionEntry ''main''"
  by (simp add: loop_cfg_def)

lemma loop_cfg_exit [simp]: "cfg_exit loop_cfg = FunctionResult ''main''"
  by (simp add: loop_cfg_def cfg_exit_def)

definition loop_ivl_eqs :: "(pp, unit, ivl resolved_st_q) eqsT" where
  "loop_ivl_eqs = side_cfg_T_eff_st loop_cfg (ivl_etf_st_for loop_gs) bot cinit_ivl_st ()"

definition loop_sig0 :: "pp + unit \<Rightarrow> ivl resolved_st_q" where
  "loop_sig0 k =
     (case k of Inl _ \<Rightarrow> bot | Inr () \<Rightarrow> restrict_global_resolved_q cinit_ivl_st)"

definition loop_kleene_step :: "(pp + unit \<Rightarrow> ivl resolved_st_q) \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q)" where
  "loop_kleene_step sig =
     (\<lambda>k. case k of
        Inl v \<Rightarrow> eq loop_ivl_eqs v sig
      | Inr () \<Rightarrow> sig (Inr ()))"

fun loop_iter_sig :: "nat \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q) \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q)" where
  "loop_iter_sig 0 sig = sig"
| "loop_iter_sig (Suc n) sig = loop_iter_sig n (loop_kleene_step sig)"

definition loop_ivl_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl resolved_st_q)" where
  "loop_ivl_sol =
     ({FunctionEntry ''main'', FunctionResult ''main''}
        \<union> Statement ` {0, 1, 2, 3},
      loop_iter_sig 100 loop_sig0)"

definition loop_ivl_at :: "pp \<Rightarrow> ivl" where
  "loop_ivl_at pp = lookup_resolved_st_q (snd loop_ivl_sol (Inl pp)) (location_of loop_gs ''x'')"

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

definition loop_ivl_td_sol :: "pp set \<times> (pp + unit \<Rightarrow> ivl resolved_st_q)" where
  "loop_ivl_td_sol = TD_side_warrowing_apinis_Interp_solve loop_ivl_eqs (cfg_exit loop_cfg)"

definition loop_ivl_td_at :: "pp \<Rightarrow> ivl" where
  "loop_ivl_td_at pp = lookup_resolved_st_q (snd loop_ivl_td_sol (Inl pp)) (location_of loop_gs ''x'')"

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
value "run_menu loop_gs loop_ivl_eqs (cfg_exit loop_cfg) (Inl (Statement 1)) ''x''"

lemma loop_head_across_update_rules:
  "run_menu loop_gs loop_ivl_eqs (cfg_exit loop_cfg) (Inl (Statement 1)) ''x''
     = [(STR ''join'',       Ivl (Fin 0) (Fin 20)),
        (STR ''per_origin'', Ivl (Fin 0) (Fin 20)),
        (STR ''warrow'',     Ivl (Fin 0) (Fin 20))]"
  unfolding loop_ivl_eqs_def run_menu_def solver_menu_def by eval

subsection \<open>Whole-program entry point: an arbitrary VIMP program (join rule)\<close>

text \<open>
  \<open>loop_ivl_eqs\<close> is built from @{const side_cfg_T_eff_st}, the same
  equation-generation pipeline @{const ivl_exec_eqs} in \<open>Interval_Exec_Sound\<close>
  uses --- not the native D/G spine (\<open>dg_gen_of\<close>) the Sign flagship
  (\<open>Exec_Sign_DG_Run\<close>) uses.  That file's own whole-program layer,
  @{const ivl_exec_prog} / @{const ivl_terminates_prog} /
  \<open>ivl_exec_prog_sound_collecting\<close>, is already fully generic in the
  classifier and the program, so \<open>analyse_interval_for\<close>/\<open>analyse_interval\<close>
  below are thin renames, not a new proof: reusing the existing chain exactly
  as instructed, rather than re-deriving a parallel one.

  This gives a collecting-level guarantee (\<open>ltr_collect\<close>), the level this
  pipeline already had proved for it, not the source-run/\<open>csim\<close> level
  \<open>analyse_sign_sound\<close> gets from the D/G-native chain in the Sign flagship
  --- \<open>Exec_Ivl_Run\<close> never established a source-run-level theorem for this
  pipeline, so \<open>analyse_interval_sound\<close> does not manufacture one.
\<close>

definition analyse_interval_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> ivl abs_state" where
  "analyse_interval_for gs p = ivl_exec_prog gs prog_main_name p"

definition analyse_interval :: "imp_prog \<Rightarrow> ivl abs_state" where
  "analyse_interval p = analyse_interval_for (declared_global p) p"

corollary analyse_interval_sound:
  assumes "ivl_terminates_prog (declared_global p) prog_main_name p"
  shows "ltr_collect (declared_global p) (prog_cfg prog_main_name p) (cinit_stores (declared_global p))
           (cfg_exit (prog_cfg prog_main_name p))
         \<le> \<lbrakk>analyse_interval p\<rbrakk>"
  unfolding analyse_interval_def analyse_interval_for_def
  by (rule ivl_exec_prog_sound_collecting[OF assms])

text \<open>A different program from \<open>loop_prog\<close>, run through the very same
  \<open>analyse_interval\<close>: the entry point is not specialized to one hard-coded
  example.\<close>

definition analyse_interval_demo2_prog :: imp_prog where
  "analyse_interval_demo2_prog = program { void main() { a := 3; b := a + 1 } }"

lemma analyse_interval_demo2_terminates:
  "ivl_terminates_prog (declared_global analyse_interval_demo2_prog) prog_main_name
     analyse_interval_demo2_prog"
  by (rule ivl_terminates_prog_via_solve_c) eval

lemma analyse_interval_demo2_result:
  "analyse_interval analyse_interval_demo2_prog ''b'' = Ivl (Fin 4) (Fin 4)"
  unfolding analyse_interval_def analyse_interval_for_def ivl_exec_prog_def
    ivl_exec_prog_at_def prog_cfg_def
  by eval

subsection \<open>A warrowing-rule entry point (definition only, no soundness proof yet)\<close>

text \<open>
  \<open>analyse_interval_td\<close> mirrors \<open>analyse_interval\<close> but solves via
  @{const TD_side_warrowing_apinis_Interp_solve} (the same rule
  \<open>loop_ivl_td_sol\<close> uses above) instead of the always-join rule, following
  \<open>ivl_exec_raw\<close>/\<open>ivl_exec_at\<close>/\<open>ivl_exec_prog\<close>'s own shape.  \<open>M3\<close> is
  deliberately left open here: \<open>ivl_exec_prog_sound_collecting\<close>'s proof leans
  on solver-specific side-restriction machinery
  (\<open>TD_side_always_join_solve_Inr_rg\<close>) with no established warrowing-rule
  analogue anywhere in the codebase.  Proving one is real new proof work
  (does warrowing even preserve the same restriction invariant?), not a
  rename, so it is flagged for the maintainer rather than attempted here.
\<close>

definition analyse_interval_td_raw ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> (pp + unit \<Rightarrow> ivl resolved_st_q)" where
  "analyse_interval_td_raw gs Pi ps mnm main =
     snd (TD_side_warrowing_apinis_Interp_solve
            (ivl_exec_eqs gs Pi ps mnm main) (cfg_exit (compile_prog Pi ps mnm main)))"

definition analyse_interval_td_at ::
    "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com \<Rightarrow> pp \<Rightarrow> ivl abs_state" where
  "analyse_interval_td_at gs Pi ps mnm main v =
     side_env (fun_of_resolved_st_q_for gs \<circ> analyse_interval_td_raw gs Pi ps mnm main) v"

definition analyse_interval_td_for :: "(vname \<Rightarrow> bool) \<Rightarrow> imp_prog \<Rightarrow> ivl abs_state" where
  "analyse_interval_td_for gs p =
     analyse_interval_td_at gs (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (cfg_exit (prog_cfg prog_main_name p))"

definition analyse_interval_td :: "imp_prog \<Rightarrow> ivl abs_state" where
  "analyse_interval_td p = analyse_interval_td_for (declared_global p) p"

lemma analyse_interval_td_demo2_result:
  "analyse_interval_td analyse_interval_demo2_prog ''b'' = Ivl (Fin 4) (Fin 4)"
  unfolding analyse_interval_td_def analyse_interval_td_for_def analyse_interval_td_at_def
    analyse_interval_td_raw_def prog_cfg_def
  by eval

subsection \<open>Executable code generation\<close>

text \<open>
  Both TD entry points, \<open>loop_ivl_sol\<close> (bounded Kleene) and \<open>loop_ivl_td_sol\<close>
  (Apinis warrowing), export through Isabelle's code generator, not merely
  through \<open>eval\<close>/\<open>value\<close>, alongside the classifier-generic \<open>analyse_interval\<close>
  and \<open>analyse_interval_td\<close>.
\<close>

export_code loop_ivl_sol loop_ivl_td_sol
  analyse_interval_for analyse_interval analyse_interval_td_for analyse_interval_td
  in Haskell module_name Interval_Demo file_prefix "Interval_Demo"

export_code loop_ivl_sol loop_ivl_td_sol
  analyse_interval_for analyse_interval analyse_interval_td_for analyse_interval_td
  in OCaml module_name Interval_Demo file_prefix "Interval_Demo_OCaml"

end




