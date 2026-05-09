theory Constraint_System_Sound
  imports Constraint_System CFG_Collecting
begin

(*
  Constraint System -- Soundness Theorem.

  Main result: any post-fixpoint of the equation system overapproximates
  the CFG collecting semantics.

  Proof strategy:
    1. Define what it means for env to be a post-fixpoint.
    2. Prove: post-fixpoint ==> env(v) >= cfg_collect(v) for all v.
       By induction on the CFG collecting semantics (or by lfp properties).
    3. Conclude: every concrete state reachable at v is in gamma(env(v)).

  This is the "big bridge" in the pipeline connecting the abstract
  constraint system back to concrete program behaviour.
*)

(* ── Post-Fixpoint Condition ──────────────────────────────────── *)
(* Defined in Constraint_System as is_post_fixpoint / is_post_fixpoint_def. *)

(* ── Overapproximation of Collecting Semantics ───────────────── *)
(*
  Informal sketch of the proof:
  By lfp.induct on cfg_collect: the collecting semantics is the least
  fixpoint of collect_pp.  We show that env also satisfies the fixpoint
  equation (because it is a post-fixpoint and transfer functions are sound).
  Then by minimality of lfp, env >= cfg_collect.
*)

context abstract_domain
begin

(* Step lemma for collect_pp abstract soundness; proof deferred. *)
lemma collect_pp_abstract_sound:
  assumes post_fp: "is_post_fixpoint g tf join_state bot_state s0 env"
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  shows
    "collect_pp g (\<lambda>v. gamma_state (env v)) v <= gamma_state (env v)"
  sorry

lemma post_fixpoint_sound:
  assumes post_fp: "is_post_fixpoint g tf join_state bot_state s0 env"
  assumes S_sound: "S <= gamma_state s0"
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  shows
    "\<forall>v. cfg_reach g S v <= gamma_state (env v)"
  sorry

end

context abstract_domain
begin

(* ── Corollary: Exit-Point Soundness ─────────────────────────── *)
(*
  At the exit point, the abstract value covers all reachable output states.
*)

corollary exit_sound:
  assumes post_fp: "is_post_fixpoint (to_cfg c) tf join_state bot_state s0 env"
  assumes S_sound: "S <= gamma_state s0"   (* was missing; needed by post_fixpoint_sound *)
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  assumes s_in_S: "s : S"
  assumes terminates: "big_step (c, s) t"
  shows   "t : gamma_state (env (cfg_exit (to_cfg c)))"
  sorry
  (* Proof: post_fixpoint_sound + S_sound gives \<forall>v. cfg_reach g S v ⊆ gamma_state(env v).
     collect_While + collect_le_cfg_collect_exit give t \<in> cfg_reach g S exit.
     Conclude t \<in> gamma_state(env exit). *)

end

end
