theory Exec_Ivl_Run
  imports Voblint_Analysis.Ivl_Exec Voblint_Core.Solver_Menu "Voblint_CFG.CFG_Prune"
            "Voblint_VIMP.VIMP_Notation"
begin

(* Disambiguate our N constructor from the phase datatype constructor. *)
hide_const phase.N
section \<open>Executable interval loop: backward filters + TD solver (eval only)\<close>

text \<open>
  Same program as @{text "Example_Interval_Loop_Coverage"} in session
  \<^session>\<open>Voblint_Formalization\<close>:
  @{text "x := 0; while (x < 20) { x := x + 1 }"}.

  The executable transfer @{const ivl_tf_st} applies the same backward guard
  filters as @{const assume_ivl} (via @{const assume_ivl_st} / @{const bfilter_ivl_st})
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
       cfg_entry = FunctionEntry ''main'' \<rparr>"

lemma loop_cfg_compiles:
  "loop_cfg = compile_prog (prog_table loop_prog) (prog_procs loop_prog) prog_main_name (prog_main loop_prog)"
  by eval

lemma loop_cfg_entry [simp]: "cfg_entry loop_cfg = FunctionEntry ''main''"
  by (simp add: loop_cfg_def)

lemma loop_cfg_exit [simp]: "cfg_exit loop_cfg = FunctionResult ''main''"
  by (simp add: loop_cfg_def cfg_exit_def)

definition loop_ivl_eqs :: "(pp, unit, ivl resolved_st_q) eqsT" where
  "loop_ivl_eqs = side_cfg_T_eff_st loop_cfg ivl_etf_st bot cinit_ivl_st ()"

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
  "loop_ivl_at pp = lookup_resolved_st_q (snd loop_ivl_sol (Inl pp)) (location_of is_global ''x'')"

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
  "loop_ivl_td_at pp = lookup_resolved_st_q (snd loop_ivl_td_sol (Inl pp)) (location_of is_global ''x'')"

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
value "run_menu is_global loop_ivl_eqs (cfg_exit loop_cfg) (Inl (Statement 1)) ''x''"

lemma loop_head_across_update_rules:
  "run_menu is_global loop_ivl_eqs (cfg_exit loop_cfg) (Inl (Statement 1)) ''x''
     = [(STR ''join'',       Ivl (Fin 0) (Fin 20)),
        (STR ''per_origin'', Ivl (Fin 0) (Fin 20)),
        (STR ''warrow'',     Ivl (Fin 0) (Fin 20))]"
  unfolding loop_ivl_eqs_def run_menu_def solver_menu_def by eval

end




