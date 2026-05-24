theory Goblint_Formalization
  imports
    (* ── Language ──────────────────────────────────────────── *)
    IMP2_Syntax
    IMP2_SmallStep
    (* ── Control-Flow Graph (cfg_collect, runs_to) ── *)
    CFG_Def
    CFG_Path
    IMP2_to_CFG
    CFG_Runs_To_Bridge
    CFG_GraphViz
    (* ── Abstract Domains ──────────────────────────────────── *)
    Abstract_Domain
    Sign_Domain
    Interval_Domain
    (* ── Equation System ───────────────────────────────────── *)
    Constraint_System
    Constraint_System_Sound
    (* ── Solver ─────────────────────────────────────────────── *)
    TD_Interface
    TD_Soundness
    (* ── Full Pipeline ──────────────────────────────────────── *)
    Pipeline
begin

(*
  Goblint Formalization -- Top Level.

  Master's thesis at TUM: prove the complete Goblint static analysis pipeline.
  Supervisors: Alexandra Gra{\ss}, Michael Schwarz.

  Pipeline (cfg_collect spec):
    AST  --(compile/to_cfg)-->  CFG  --(rhs/make_rhs_tree)-->  Equations  --(TD)-->  Result
    [IMP2_*, CFG_*, Constraint_System, TD_CFG_Core, TD_Interface, Pipeline]

  Canonical soundness: pipeline_invariant_sound, pipeline_sound_path.
  Exit sugar: runs_to (runs_to_def); goblint_sign_sound for sign domain.

  Sign pipeline: proved (goblint_sign_sound; carries P1-P3 TD assumptions).
  Interval: ivl_pipeline_sound (stretch packaging).

  Abstract domains:
    Sign      -- Tier 1 (finite lattice, no widening)  [Domains/Sign_Domain]
    Interval  -- Tier 2 (widening required)            [Domains/Interval_Domain]
    Octagon   -- Tier 3 stretch goal                   [TODO]
*)

(* ── Smoke Test: IMP2 Syntax and Semantics ─────────────────────
   Verify that the basic machinery type-checks. *)

definition example_swap :: com where
  "example_swap =
     (''tmp'' ::= V ''x'' ;;
      ''x''   ::= V ''y'' ;;
      ''y''   ::= V ''tmp'')"

lemma example_swap_runs_to:
  "\<exists>t. runs_to example_swap s t"
proof -
  let ?s1 = "s(''tmp'' := s ''x'')"
  let ?s2 = "?s1(''x'' := ?s1 ''y'')"
  let ?s3 = "?s2(''y'' := ?s2 ''tmp'')"
  have e1: "(''tmp'' ::= V ''x'', s) \<rightarrow>* (SKIP, ?s1)"
    by (auto intro: star.step)
  have e2: "(''x'' ::= V ''y'', ?s1) \<rightarrow>* (SKIP, ?s2)"
    by (auto intro: star.step)
  have e3: "(''y'' ::= V ''tmp'', ?s2) \<rightarrow>* (SKIP, ?s3)"
    by (auto intro: star.step)
  have e12: "(''tmp'' ::= V ''x'' ;; ''x'' ::= V ''y'', s) \<rightarrow>* (SKIP, ?s2)"
    using seq_comp[OF e1 e2] .
  have e123: "(example_swap, s) \<rightarrow>* (SKIP, ?s3)"
    unfolding example_swap_def
    using seq_comp[OF e12 e3] .
  hence "runs_to example_swap s ?s3" by (rule small_step_runs_to)
  thus ?thesis by blast
qed

lemma example_swap_correct:
  "runs_to example_swap s t \<Longrightarrow> t ''x'' = s ''y'' \<and> t ''y'' = s ''x''"
proof -
  assume "runs_to example_swap s t"
  hence star: "(example_swap, s) \<rightarrow>* (SKIP, t)" by (rule runs_to_small_step)
  then have star':
    "(''tmp'' ::= V ''x'' ;; ''x'' ::= V ''y'' ;; ''y'' ::= V ''tmp'', s) \<rightarrow>* (SKIP, t)"
    unfolding example_swap_def .
  from seq_star_finish[OF star'] obtain s2 where
        s12_step: "(''tmp'' ::= V ''x'' ;; ''x'' ::= V ''y'', s) \<rightarrow>* (SKIP, s2)"
    and rest2:  "(''y'' ::= V ''tmp'', s2) \<rightarrow>* (SKIP, t)"
    by blast
  from seq_star_finish[OF s12_step] obtain s1 where
        s1_step: "(''tmp'' ::= V ''x'', s) \<rightarrow>* (SKIP, s1)"
    and s2_step: "(''x'' ::= V ''y'', s1) \<rightarrow>* (SKIP, s2)"
    by blast
  from s1_step have s1_eq: "s1 = s(''tmp'' := s ''x'')"
    using star_Assign_eq by fastforce
  from s2_step have s2_eq: "s2 = s1(''x'' := s1 ''y'')"
    using star_Assign_eq by fastforce
  from rest2 have t_eq: "t = s2(''y'' := s2 ''tmp'')"
    using star_Assign_eq by fastforce
  show "t ''x'' = s ''y'' \<and> t ''y'' = s ''x''"
    using t_eq s2_eq s1_eq by simp
qed

(* ── Top-Level Soundness Theorem (Sign Domain) ─────────────────
   Entry point for the thesis main result. *)

theorem goblint_sign_sound:
  assumes runs: "runs_to c s t"
  assumes join_cfi:
    "comp_fun_idem ((\<squnion>) ::
       sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state)"
  assumes td_solve_dom:
    "TD_plain.solve_dom
       (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot
          (ac_init (sign_analysis_config s)))
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach
       (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot
          (ac_init (sign_analysis_config s)))
       (TD_plain_Interp_solve
          (make_rhs_tree (to_cfg c) sign_tf (\<squnion>) bot
            (ac_init (sign_analysis_config s)))
          (cfg_entry (to_cfg c)))
       (cfg_entry (to_cfg c))"
  shows
    "t \<in> sign_domain.gamma_state
            (run_analysis (sign_analysis_config s) c
               (cfg_exit (to_cfg c)))"
  by (rule sign_pipeline_sound
        [OF runs sign_init_in_gamma join_cfi td_solve_dom td_cfg_in_reach])

end
