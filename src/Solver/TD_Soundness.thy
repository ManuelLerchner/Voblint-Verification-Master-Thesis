theory TD_Soundness
  imports TD_Interface Constraint_System_Sound Sign_Domain Interval_Domain
begin

(*
  TD Solver Soundness.

  Combines:
    (1)  TD solver produces a post-fixpoint         (TD_Interface.td_analyse_post_fixpoint)
    (2)  Post-fixpoints overapproximate reachability (Constraint_System_Sound.post_fixpoint_sound)

  to obtain the central soundness result:

    If s0 is in gamma(env_entry), and c terminates with output t,
    then t is in gamma(env_exit).

  where env = td_analyse c tf ...
*)

(* ── Combined Soundness ───────────────────────────────────────── *)

context abstract_domain
begin

theorem td_solver_sound:
  assumes tf_sound_assign:
    "\<forall>x a sigma. \<forall>s \<in> gamma_state sigma.
       s(x := aval a s) \<in> gamma_state (tf_assign tf x a sigma)"
  assumes tf_sound_assume:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume tf b sigma)"
  assumes tf_sound_assume_not:
    "\<forall>b sigma. \<forall>s \<in> gamma_state sigma. \<not> bval b s
       \<longrightarrow> s \<in> gamma_state (tf_assume_not tf b sigma)"
  assumes s0_sound:
    "s : gamma_state s0"
  assumes terminates:
    "big_step (c, s) t"
  (* Solver bridge (see TD_Interface.td_analyse_post_fixpoint): CFG finiteness,
     idempotent fold-join, TD termination domain, and whole-CFG reachability. *)
  assumes fin_cfg: "finite (cfg_edges (to_cfg c))"
  assumes join_state_cfi:
    "comp_fun_idem (join_state :: 'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state)"
  assumes td_solve_dom:
    "TD_plain.solve_dom (make_rhs_tree (to_cfg c) tf join_state bot_state s0)
       (cfg_entry (to_cfg c))"
  assumes td_cfg_in_reach:
    "\<And>v::pp. v \<in> reach (make_rhs_tree (to_cfg c) tf join_state bot_state s0)
                    (TD_plain_Interp_solve (make_rhs_tree (to_cfg c) tf join_state bot_state s0)
                      (cfg_entry (to_cfg c)))
                    (cfg_entry (to_cfg c))"
  shows
    "t : gamma_state ((td_analyse c tf join_state bot_state s0)
                       (cfg_exit (to_cfg c)))"
proof -
  have post_fp: "is_post_fixpoint (to_cfg c) tf join_state bot_state s0
                   (td_analyse c tf join_state bot_state s0)"
    by (rule td_analyse_post_fixpoint[OF fin_cfg join_state_cfi join_state_comm
          td_solve_dom td_cfg_in_reach])
  show ?thesis
    by (rule exit_sound[OF post_fp order.refl tf_sound_assign tf_sound_assume
          tf_sound_assume_not s0_sound terminates])
qed

end

(* ── Sign Domain Instantiation ────────────────────────────────── *)
(*
  Concrete instantiation of the soundness theorem for the Sign domain.
*)

theorem sign_analysis_sound:
  assumes s_sound:    "s : sign_domain.gamma_state s0"
  assumes terminates: "big_step (c, s) t"
  shows   "t : sign_domain.gamma_state
                 ((td_analyse c sign_tf
                   sign_domain.join_state sign_domain.bot_state s0)
                   (cfg_exit (to_cfg c)))"
  sorry

(* ── Interval Domain Instantiation ───────────────────────────── *)

theorem interval_analysis_sound:
  assumes s_sound:    "s : ivl_domain.gamma_state s0"
  assumes terminates: "big_step (c, s) t"
  shows   "t : ivl_domain.gamma_state
                 ((td_analyse c ivl_tf
                   ivl_domain.join_state ivl_domain.bot_state s0)
                   (cfg_exit (to_cfg c)))"
  sorry

end
