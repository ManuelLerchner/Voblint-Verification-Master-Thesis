theory Constraint_System
  imports CFG_Def Abstract_Domain
begin

(*
  Equation System over a CFG.

  Given:
    - A CFG  g
    - An abstract domain  D  (instance of abstract_domain)
    - Per-domain transfer functions for each edge action

  We construct an equation system (constraint system) where each
  program point v has an equation:
    sigma(v) = join_over { tf(a)(sigma(u)) | (u,a,v) in g }

  plus the special base case at the entry:
    sigma(entry) includes the initial abstract state.

  The equation system is represented as an RHS function:
    rhs :: pp => (pp => D abs_state) => D abs_state

  This is the format expected by the Top_Down_Solver locale.

  All transfer functions are parameterised over the domain via a locale
  so the same equation-system construction works for Sign, Interval, etc.
*)

(* ── Abstract Transfer Function Record ───────────────────────── *)
(*
  A domain_transfer bundles the per-action abstract transformers.
  Parameterised by the abstract value type 'a.
*)

record 'a domain_transfer =
  tf_assign    :: "vname => aexp => ('a abs_state) => ('a abs_state)"
  tf_assume    :: "bexp  => ('a abs_state) => ('a abs_state)"
  tf_assume_not :: "bexp => ('a abs_state) => ('a abs_state)"

(* ── Apply Transfer Function to One Edge ─────────────────────── *)

fun apply_tf :: "'a domain_transfer
                 => edge_action
                 => ('a abs_state)
                 => ('a abs_state)" where
    "apply_tf tf EA_Nop              sigma = sigma"
  | "apply_tf tf (EA_Assign x a)     sigma = tf_assign tf x a sigma"
  | "apply_tf tf (EA_Assume b)       sigma = tf_assume tf b sigma"
  | "apply_tf tf (EA_AssumeNot b)    sigma = tf_assume_not tf b sigma"

(* ── Abstract Join over a Set ─────────────────────────────────── *)
(*
  Fold join_abs over a finite set of abstract states.
  Requires comp_fun_commute join_abs for the result to be order-independent.
  Finiteness of the predecessor set follows from finite (cfg_edges g).
*)

definition abs_join_set ::
    "('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state set
     => 'a abs_state"
where
  "abs_join_set join_abs bot_abs S = Finite_Set.fold join_abs bot_abs S"

definition rhs ::
    "cfg
     => 'a domain_transfer
     => ('a abs_state => 'a abs_state => 'a abs_state)
     => 'a abs_state
     => 'a abs_state
     => (pp => 'a abs_state)
     => pp
     => 'a abs_state"
where
  "rhs g tf join_abs bot_abs s0 env v =
     (let preds = {(u, a) | u a. (u, a, v) : cfg_edges g};
          vals  = image (%( u, a). apply_tf tf a (env u)) preds;
          base  = if v = cfg_entry g then insert s0 vals else vals
      in  abs_join_set join_abs bot_abs base)"

(* ── Monotonicity of rhs ──────────────────────────────────────── *)
(*
  The RHS is monotone in the environment: if env1 <= env2 pointwise
  (in the abstract order), then rhs env1 <= rhs env2.
  This is required by TD_plain for the solver to be applicable.
*)

(*
  Key proof obligation for using the AFP TD solver:
  The RHS is monotone in the environment.
  Proof sketch: apply_tf is monotone (transfer functions are monotone),
  image under monotone map grows, fold of join_abs over a larger set is larger.
  Requires: (1) finite (cfg_edges g), (2) comp_fun_commute join_abs,
            (3) join_abs is monotone in each argument.
*)
lemma rhs_mono:
  assumes fin: "finite (cfg_edges g)"
  assumes cfu: "comp_fun_commute (join_abs :: 'a::ord abs_state => 'a abs_state => 'a abs_state)"
  assumes env_le: "ALL v. env1 v <= env2 v"
  shows "rhs g tf join_abs bot_abs s0 env1 v <= rhs g tf join_abs bot_abs s0 env2 v"
  sorry

(* ── Soundness of rhs ─────────────────────────────────────────── *)
(*
  Key soundness statement for the constraint system:
  If env is a post-fixpoint (env v <= rhs ... env v for all v),
  then env overapproximates the CFG collecting semantics.
  Proved in Constraint_System_Sound.thy.
*)

end
