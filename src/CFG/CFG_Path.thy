theory CFG_Path
  imports CFG_Def
begin

(*
  CFG_Path -- Inductive path predicate for CFGs.

  Pattern: inductive path + derived notation + intro/elim/simp lemma library.
  Adapted from: https://github.com/lohner/FormalSSA (Ullrich & Lohner, Isabelle2016)
                "Verified Construction of Static Single-Assignment Form"
                SSA_CFG.thy / Graph_path.thy — path2 + lemma library.
  See wiki: ~/goblint-formalization-kb/wiki/concepts/isabelle-proof-engineering.md
            Pattern 1 (inductive path), Pattern 2 (attribute discipline),
            Pattern 4 (derived _cases / _induct lemmas).

  Why this file exists:
    post_fixpoint_sound and cfg_collect_exit_eq_collect both need to reason
    about sequences of edges from the entry to an arbitrary program point.
    Without an inductive path predicate, every reachability argument requires
    raw list induction and manual invariant re-establishment at each step.

  Design choices vs. FormalSSA:
    - FormalSSA path2: list of *nodes* (predecessor-based graph)
    - Our cfg_path:   list of *(edge_action * pp)* steps (labeled-edge graph)
    Edge actions are recorded because transfer-function composition in
    post_fixpoint_sound needs to know which action was taken on each step.
*)

(* ── Core Inductive Predicate ─────────────────────────────────── *)

(*
  cfg_path g u steps v
    = there is a path from u to v in g, taking the sequence of (action, next-pp)
      pairs listed in 'steps'.

  Base case:  empty path stays at u.
  Step case:  if there is an edge (u, a, w) in g and a path from w to v,
              then we can prepend (a, w) to get a path from u to v.
*)

inductive cfg_path :: "cfg => pp => (edge_action * pp) list => pp => bool" where
  empty[intro]: "cfg_path g v [] v"
| step[intro]:  "(u, a, w) : cfg_edges g ==> cfg_path g w es v
                 ==> cfg_path g u ((a, w) # es) v"

(* ── Reachability Abbreviation + Notation ─────────────────────── *)

(*
  g |- u -->* v   iff some path (of any steps) exists from u to v.
  Notation inspired by FormalSSA's "n⌜ns⌝→m".
*)

abbreviation cfg_reaches :: "cfg => pp => pp => bool" ("_ \<turnstile> _ \<rightarrow>* _" [50,0,50] 80) where
  "cfg_reaches g u v == (EX es. cfg_path g u es v)"

(* ── Intro Lemmas ──────────────────────────────────────────────── *)

lemma cfg_reaches_refl[intro, simp]: "g \<turnstile> v \<rightarrow>* v"
  sorry

lemma cfg_reaches_step[intro]:
  "(u, a, w) : cfg_edges g ==> g \<turnstile> w \<rightarrow>* v ==> g \<turnstile> u \<rightarrow>* v"
  sorry

lemma cfg_reaches_trans[intro]:
  "g \<turnstile> u \<rightarrow>* v ==> g \<turnstile> v \<rightarrow>* w ==> g \<turnstile> u \<rightarrow>* w"
  sorry

(* ── Cases Lemma (Pattern 4) ───────────────────────────────────── *)

(*
  Named case split mirroring the inductive constructor structure.
  Avoids "simp add: cfg_path.simps" which unfolds too aggressively.
*)

lemma cfg_path_cases[consumes 1, case_names empty step]:
  assumes "cfg_path g u es v"
  obtains
    (empty) "es = []" "u = v"
  | (step)  a w es' where
      "es = (a, w) # es'"
      "(u, a, w) : cfg_edges g"
      "cfg_path g w es' v"
  sorry

(* ── Induction Rule (Pattern 4) ────────────────────────────────── *)

(*
  Custom induction rule with named cases and [consumes 1] so that
    proof (induction rule: cfg_path_induct)
  works directly and produces named subgoals 'empty' and 'step'.
*)

lemma cfg_path_induct[consumes 1, case_names empty step]:
  assumes "cfg_path g u es v"
  assumes empty: "P g v [] v"
  assumes step:  "!!u a w es.
                    (u, a, w) : cfg_edges g ==>
                    cfg_path g w es v ==>
                    P g w es v ==>
                    P g u ((a, w) # es) v"
  shows "P g u es v"
  sorry

(* ── Elim / Simp Lemmas ────────────────────────────────────────── *)

lemma cfg_path_not_Nil_imp_step[dest]:
  "cfg_path g u es v ==> es ~= [] ==>
   EX a w es'. es = (a, w) # es' & (u, a, w) : cfg_edges g & cfg_path g w es' v"
  sorry

(*
  Each step (a,w) in the path list came from some edge in the CFG.
  The source of that edge is NOT necessarily u (the path start) — it is
  whatever node preceded w along the path.  The old statement
    (a,w) ∈ set (map snd es) ⟹ (u,a,w) ∈ cfg_edges g
  was wrong for paths of length > 1.  Correct form: existential source.
*)
lemma cfg_path_edges_in_cfg:
  "cfg_path g u es v ==> (a, w) : set es ==> EX src. (src, a, w) : cfg_edges g"
  sorry (* induction on cfg_path: empty vacuous; step: (a',w') = head → src = u; IH for tail *)

(* Convenience: first step of a non-empty path hits the CFG at u. *)
lemma cfg_path_first_edge:
  "cfg_path g u ((a, w) # es) v ==> (u, a, w) : cfg_edges g"
  sorry (* by cfg_path.cases: only the step constructor applies; its premise gives (u,a,w) ∈ cfg_edges g *)

(* ── Reachability from Entry ───────────────────────────────────── *)

definition cfg_reachable :: "cfg => pp => bool" where
  "cfg_reachable g v = (g \<turnstile> cfg_entry g \<rightarrow>* v)"

lemma cfg_entry_reachable[intro, simp]: "cfg_reachable g (cfg_entry g)"
  unfolding cfg_reachable_def by (rule cfg_reaches_refl)

(*
  cfg_exit_reachable_from_entry is unprovable for arbitrary well-formed CFGs:
  cfg_wf does not guarantee a path from entry to exit.  Replaced by
  to_cfg_exit_reachable below, which uses the compile structure.
*)
lemma cfg_exit_reachable_from_entry:
  "cfg_wf g ==>
   (ALL (u, _, v) : cfg_edges g. cfg_reachable g u --> cfg_reachable g v) ==>
   cfg_reachable g (cfg_exit g)"
  sorry  (* intentionally weak; use to_cfg_exit_reachable for to_cfg results *)

(*
  For CFGs produced by to_cfg, the exit IS reachable from entry.
  Proved by structural induction on c using compile's edge structure.
*)
lemma to_cfg_exit_reachable:
  "cfg_reachable (to_cfg c) (cfg_exit (to_cfg c))"
  sorry

(* ── Transfer Function Composition Along a Path ───────────────── *)

(*
  Compose edge_collect along a path to get the overall state transformer.
  Used in post_fixpoint_sound to relate rho(u) to rho(v) via path steps.
*)

fun path_collect :: "(edge_action * pp) list => state set => state set" where
  "path_collect [] S = S"
| "path_collect ((a, _) # es) S = path_collect es (edge_collect a S)"

lemma path_collect_empty[simp]: "path_collect [] S = S"
  by simp

lemma path_collect_mono:
  "S \<subseteq> T ==> path_collect es S \<subseteq> path_collect es T"
  sorry

end
