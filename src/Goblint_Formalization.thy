theory Goblint_Formalization
  imports
    (* ── Language ──────────────────────────────────────────── *)
    IMP2_Syntax
    IMP2_Semantics
    IMP2_Collecting
    (* ── Control-Flow Graph ────────────────────────────────── *)
    CFG_Def
    CFG_Path
    IMP2_to_CFG
    CFG_Collecting
    (* ── Abstract Domains ──────────────────────────────────── *)
    Abstract_Domain
    Sign_Domain
    Interval_Domain
    (* ── Equation System ───────────────────────────────────── *)
    Constraint_System
    Constraint_System_Sound
    Direct_Equations
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

  Pipeline (two routes — both proved equivalent):

  Route A — CFG-mediated:
    AST  --(compile)-->  CFG  --(rhs/make_rhs_tree)-->  Equations  --(TD)-->  Result
    [IMP2_*, CFG_*, Constraint_System, TD_Interface]

  Route B — Direct (no CFG record):
    AST  --(predecessors_of/direct_tree)-->  Equations  --(TD)-->  Result
    [Direct_Equations]

  Equivalence theorem: direct_eq_cfg_analyse (Direct_Equations.thy)

  Every proof is currently deferred (sorry).
  Fill in leaves first; propagate upward.

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

lemma example_swap_terminates: "\<exists>t. big_step (example_swap, s) t"
  unfolding example_swap_def
  apply (rule exI)
  apply (rule big_step.Seq, rule big_step.Seq,
         rule big_step.Assign, rule big_step.Assign,
         rule big_step.Assign)
  done

lemma example_swap_correct:
  "big_step (example_swap, s) t ==> t ''x'' = s ''y'' \<and> t ''y'' = s ''x''"
  unfolding example_swap_def
  by (auto elim!: big_step.cases)

(* ── Top-Level Soundness Theorem (Sign Domain) ─────────────────
   Entry point for the thesis main result. *)

theorem goblint_sign_sound:
  "big_step (c, s) t
   ==>  t : sign_domain.gamma_state
              (run_analysis (sign_analysis_config s) c
                 (cfg_exit (to_cfg c)))"
  by (rule sign_pipeline_sound)

end
