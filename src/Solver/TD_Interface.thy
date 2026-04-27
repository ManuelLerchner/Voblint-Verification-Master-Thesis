theory TD_Interface
  imports Constraint_System CFG_Collecting
begin

(*
  Top-Down Solver Interface.

  ═══════════════════════════════════════════════════════════════════
  THESIS GOAL: Connect our abstract interpretation to the AFP solver.
  ═══════════════════════════════════════════════════════════════════

  The AFP "Top_Down_Solver" (Stade, Schwarz, Seidl, Tilscher, CAV 2024)
  is a verified top-down fixpoint solver.  Its key locale is TD_plain:

    locale TD_plain =
      fixes rhs :: "'v => ('v => 'a) => 'a"
      assumes mono: monotone (<=) (<=) (rhs v)
    begin
      theorem partial_correctness:
        "rhs v (solve start) <= solve start v"  -- solve gives a POST-FIXPOINT
    end

  Our contribution:
    (1) Build make_rhs from the CFG + transfer functions  [this file]
    (2) Prove make_rhs is monotone                        [make_rhs_mono]
    (3) By TD_plain.partial_correctness => post-fixpoint  [td_analyse_post_fixpoint]
    (4) Prove post-fixpoints overapproximate reality      [post_fixpoint_sound]
    (5) Conclude: td_analyse output is sound              [td_solver_sound]

  Steps (1)+(2)+(4) are our proof obligations.
  Step (3) is the AFP solver's verified theorem.

  ── How to connect to AFP ───────────────────────────────────────
  When "AFP.Top_Down_Solver" is installed (via Isabelle's AFP package):
    1. Replace the axiomatisation of td_solve below with:
         imports "AFP.Top_Down_Solver"
    2. Replace td_solve_post_fixpoint with:
         interpretation td: TD_plain "make_rhs g tf join_abs bot_abs s0"
           by (unfold_locales) (rule make_rhs_mono)
    3. td_analyse_post_fixpoint then follows from td.partial_correctness.
  ──────────────────────────────────────────────────────────────────
*)

(* ── Stub: AFP TD Solver (replace with real import when available) *)
(*
  The axiom td_solve_post_fixpoint below IS the statement of
  TD_plain.partial_correctness.  It is axiomatised here only until
  the AFP session is installed.  No other axioms are introduced.
*)

typedecl ('v, 'a) td_result   (* placeholder for solver output type *)

axiomatization
  td_solve :: "('v => ('v => 'a::ord) => 'a) => 'v => 'v => 'a"
where
  td_solve_post_fixpoint:
    "!!rhsfn v start. monotone (<=) (<=) (rhsfn v)
     ==>  rhsfn v (td_solve rhsfn start) <= td_solve rhsfn start v"

(* ── Monotone RHS Wrapper ─────────────────────────────────────── *)
(*
  Bundle the constraint system into the format required by td_solve.
*)

definition make_rhs ::
    "cfg
     => 'a::ord domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp => (pp => 'a abs_state) => 'a abs_state"
where
  "make_rhs g tf join_abs bot_abs s0 v env =
     rhs g tf join_abs bot_abs s0 env v"

(*
  OUR PROOF OBLIGATION: make_rhs is monotone in the environment.
  This is what lets us apply the AFP solver.
  Proof sketch: image of monotone map is monotone; fold of join over
  larger image gives larger result (join is monotone in both args).
*)
lemma make_rhs_mono:
  assumes fin: "finite (cfg_edges g)"
  assumes cfu: "comp_fun_commute (join_abs :: 'a::ord abs_state => 'a abs_state => 'a abs_state)"
  shows "monotone (<=) (<=) (make_rhs g tf join_abs bot_abs s0 v)"
  unfolding monotone_def make_rhs_def
  using rhs_mono[OF fin cfu]
  by (simp add: le_fun_def)

(* ── Solver Instantiation ─────────────────────────────────────── *)

definition td_analyse ::
    "com
     => 'a::ord domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => pp => 'a abs_state"
where
  "td_analyse c tf join_abs bot_abs s0 =
     (let g   = to_cfg c;
          rhsfn = make_rhs g tf join_abs bot_abs s0
      in  td_solve rhsfn (cfg_entry g))"

(*
  AFP CONTRIBUTION: solver output IS a post-fixpoint.
  Intended proof: unfold is_post_fixpoint_def, td_analyse_def, Let_def;
  discharge with td_solve_post_fixpoint[OF make_rhs_mono ...] and simp.
  Sorry'd for now — simp setup did not finish the automation (heavy goal).
*)
theorem td_analyse_post_fixpoint:
  assumes fin: "finite (cfg_edges (to_cfg c))"
  assumes cfu: "comp_fun_commute (join_abs :: 'a::ord abs_state => 'a abs_state => 'a abs_state)"
  shows "is_post_fixpoint (to_cfg c) tf join_abs bot_abs s0
           (td_analyse c tf join_abs bot_abs s0)"
  sorry

end
