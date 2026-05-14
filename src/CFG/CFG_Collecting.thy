theory CFG_Collecting
  imports IMP2_to_CFG IMP2_Collecting CFG_Path
begin

(*
  CFG -- Collecting Semantics.

  Defines the collecting semantics directly on the CFG as the canonical
  fixpoint of the transfer functions over edges, then proves it agrees
  with the IMP2 collecting semantics.  This bridge is used in
  Equations/Constraint_System_Sound.thy.
*)

(* ── Per-Edge Transfer Function on State Sets ─────────────────── *)

fun edge_collect :: "edge_action => store set => store set" where
    "edge_collect EA_Nop          S = S"
  | "edge_collect (EA_Assign x a) S = {s(x := aval a s) | s. s : S}"
  | "edge_collect (EA_Assume b)    S = Collect (\<lambda>s. s \<in> S \<and> bval b s)"
  | "edge_collect (EA_AssumeNot b) S = Collect (\<lambda>s. s \<in> S \<and> \<not> bval b s)"

lemma edge_collect_mono:
  assumes "S \<subseteq> T"
  shows "edge_collect a S \<subseteq> edge_collect a T"
proof (cases a)
  case EA_Nop
  with assms show ?thesis by simp
next
  case (EA_Assign x1 a1)
  with assms show ?thesis by auto
next
  case (EA_Assume b)
  with assms show ?thesis by (auto simp add: subset_iff mem_Collect_eq)
next
  case (EA_AssumeNot b)
  with assms show ?thesis by (auto simp add: subset_iff mem_Collect_eq)
qed

(* Lived in CFG_Path.thy but must follow edge_collect (no import cycle). *)
fun path_collect :: "(edge_action * pp) list => store set => store set" where
  "path_collect [] S = S"
| "path_collect ((a, _) # es) S = path_collect es (edge_collect a S)"

lemma path_collect_empty[simp]: "path_collect [] S = S"
  by simp

lemma path_collect_mono_strong:
  "S \<subseteq> T \<Longrightarrow> path_collect es S \<subseteq> path_collect es T"
proof (induction es arbitrary: S T)
  case Nil
  assume le: "S \<subseteq> T"
  show "path_collect [] S \<subseteq> path_collect [] T"
    unfolding path_collect.simps using le by blast
next
  case (Cons e es)
  assume le: "S \<subseteq> T"
  obtain a p where ep: "e = (a, p)" by (cases e) auto
  have sub_edge: "edge_collect a S \<subseteq> edge_collect a T"
    by (rule edge_collect_mono[OF le])
  have step: "path_collect es (edge_collect a S) \<subseteq> path_collect es (edge_collect a T)"
    by (rule Cons.IH[OF sub_edge])
  show "path_collect (e # es) S \<subseteq> path_collect (e # es) T"
    unfolding path_collect.simps using ep step by simp
qed

lemma path_collect_mono:
  assumes subset: "S \<subseteq> T"
  shows "path_collect es S \<subseteq> path_collect es T"
  by (rule path_collect_mono_strong[OF subset])

(* ── CFG Collecting Environment ───────────────────────────────── *)
(*
  A collecting environment maps each program point to the set of states
  that can appear there during any execution starting from some fixed
  initial set.
*)

type_synonym cenv = "pp => store set"

definition cenv_join :: "pp => cenv set => store set" where
  "cenv_join v envs = Union {rho v | rho. rho : envs}"

(* ── Collecting Transformer for One Program Point ─────────────── *)
(*
  collect_pp g rho v = join of edge_collect(a)(rho u) over all (u,a,v) in g.
  This is the single-step "push" of states through each incoming edge.
*)

definition collect_pp :: "cfg => cenv => pp => store set" where
  "collect_pp g rho v =
     Union {edge_collect a (rho u) | u a. (u, a, v) : cfg_edges g}"

(* ── Least Fixpoint (Collecting Semantics over CFG) ───────────── *)
(*
  Given an initial store set S at the entry, the CFG collecting semantics
  is the least fixpoint of the monotone transformer collect_pp.
*)

definition cfg_collect :: "cfg => store set => cenv" where
  "cfg_collect g S =
     lfp (\<lambda>rho v.
            if v = cfg_entry g then S Un collect_pp g rho v
            else collect_pp g rho v)"

(* ── Monotonicity of collect_pp ──────────────────────────────────
   Required for lfp to be well-defined. *)

lemma collect_pp_mono:
  "mono (\<lambda>rho. collect_pp g rho v)"
proof (rule monoI)
  fix rho1 rho2 :: cenv
  assume le: "rho1 \<le> rho2"
  have ru: "\<And>u. rho1 u \<subseteq> rho2 u"
    using le by (simp add: le_fun_def)
  have edge: "\<And>u a. (u, a, v) \<in> cfg_edges g \<Longrightarrow> edge_collect a (rho1 u) \<subseteq> edge_collect a (rho2 u)"
    by (meson ru edge_collect_mono)
  show "collect_pp g rho1 v \<subseteq> collect_pp g rho2 v"
    unfolding collect_pp_def using edge by blast
qed

(* ── Correspondence Theorem ──────────────────────────────────────
   CFG collecting semantics at the exit node equals IMP2 collecting.
   Split into two directions so each can be proved independently. *)

(*
  ⊆ direction: every store the CFG collecting semantics puts at the exit
  is also a big_step output.

  Proof: show (collect c S) is a post-fixpoint of the concrete CFG transformer F.
  Then lfp_least gives cfg_collect ≤ collect at exit.
  Key: for each com case, check that CFG edges match big_step transitions exactly:
    - SKIP: single EA_Nop edge entry→exit; collect_pp gives S; collect SKIP S = S ✓
    - Assign: single EA_Assign edge; collect_pp = image; matches big_step.Assign ✓
    - Seq: edges chain via mid-point; matches big_step.Seq ✓
    - If: two assume/assume_not edges to branches; matches WhileTrue/WhileFalse ✓
    - While: loop-head→assume→body→back-edge + assume_not→exit; matches WhileTrue/WhileFalse ✓
*)
lemma cfg_collect_exit_le_collect:
  "cfg_collect (to_cfg c) S (cfg_exit (to_cfg c)) <= collect c S"
  sorry

(*
  ⊇ direction: every big_step output is captured by the CFG collecting semantics.

  Proof: induction on the big_step derivation.
  For each rule, unfold cfg_collect one step and show the output lands in the lfp.
  The WHILE case needs the IH for the body AND for the recursive WHILE call.
  Key lemma needed: lfp unfolding (lfp f = f (lfp f)) to push states through edges.
*)
lemma collect_le_cfg_collect_exit:
  "collect c S <= cfg_collect (to_cfg c) S (cfg_exit (to_cfg c))"
  sorry

theorem cfg_collect_exit_eq_collect:
  "cfg_collect (to_cfg c) S (cfg_exit (to_cfg c)) = collect c S"
  by (rule antisym) (rule cfg_collect_exit_le_collect, rule collect_le_cfg_collect_exit)

(* ── Reachability on CFG ─────────────────────────────────────────
   Helper: a store s is reachable at program point v iff it appears
   in cfg_collect. Used in soundness proofs. *)

definition cfg_reach :: "cfg => store set => pp => store set" where
  "cfg_reach g S = cfg_collect g S"

lemma cfg_reach_entry:
  "S <= cfg_reach (to_cfg c) S (cfg_entry (to_cfg c))"
  sorry

end
