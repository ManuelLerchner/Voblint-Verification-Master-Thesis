theory Pipeline
  imports TD_Soundness Sign_Domain Interval_Domain
begin

(*
  Full Analysis Pipeline.

  This theory assembles the complete end-to-end pipeline:

    IMP2 source  --[to_cfg]\<longrightarrow>  CFG
                 --[rhs]-----\<longrightarrow>  Constraint System
                 --[td_solve]\<longrightarrow>  Fixed-Point Environment
                 --[gamma]---\<longrightarrow>  State-Set Overapproximation

  The pipeline is parameterised over an abstract domain.
  Concrete instantiations for Sign and Interval are provided below.

  Top-level soundness theorem:
    For any domain D with verified transfer functions, if program c is run
    from initial state s (with s in gamma(sigma_0) for some initial abstraction
    sigma_0), and c terminates in t, then t in gamma(sigma_exit).
*)

(* ── Transfer-Function Soundness Bundle ──────────────────────── *)
(*
  Packages the three soundness conditions for domain transfer functions
  into a single predicate, parameterised over a concretisation gamma.
*)

definition domain_transfer_sound ::
    "('a::{ord,bot} => int set)
     => 'a domain_transfer
     => bool"
where
  "domain_transfer_sound gamma tf =
     ((\<forall>x a sigma. \<forall>s \<in> abstract_domain.gamma_state gamma sigma.
         s(x := aval a s) \<in> abstract_domain.gamma_state gamma (tf_assign tf x a sigma))
      \<and> (\<forall>b sigma. \<forall>s \<in> abstract_domain.gamma_state gamma sigma. bval b s
           \<longrightarrow> s \<in> abstract_domain.gamma_state gamma (tf_assume tf b sigma))
      \<and> (\<forall>b sigma. \<forall>s \<in> abstract_domain.gamma_state gamma sigma. \<not> bval b s
           \<longrightarrow> s \<in> abstract_domain.gamma_state gamma (tf_assume_not tf b sigma)))"

(* ── Generic Pipeline Record ──────────────────────────────────── *)
(*
  Bundle everything needed to run an analysis:
    - the abstract domain operations
    - the transfer functions
    - the initial abstract state
*)

record 'a analysis_config =
  ac_join     :: "'a abs_state => 'a abs_state => 'a abs_state"
  ac_bot      :: "'a abs_state"
  ac_gamma    :: "'a => int set"
  ac_tf       :: "'a domain_transfer"
  ac_init     :: "'a abs_state"

(* ── Run the Pipeline ─────────────────────────────────────────── *)

definition run_analysis ::
    "('a::{ord,bot}) analysis_config => com => pp => 'a abs_state"
where
  "run_analysis cfg c =
     td_analyse c
       (ac_tf cfg)
       (ac_join cfg)
       (ac_bot cfg)
       (ac_init cfg)"

(* ── Pipeline Soundness (Generic) ────────────────────────────── *)
(*
  The main theorem of the thesis:
    If the transfer functions in cfg are sound with respect to gamma,
    and the initial concrete state s is in gamma(ac_init cfg),
    and program c terminates in t,
    then t is in gamma(run_analysis cfg c (exit of c)).
*)

theorem pipeline_sound:
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s : abstract_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  assumes terminates: "big_step (c, s) t"
  shows   "t : abstract_domain.gamma_state (ac_gamma cfg)
                  (run_analysis cfg c (cfg_exit (to_cfg c)))"
  sorry

(* ── Sign Analysis Pipeline ───────────────────────────────────── *)
(*
  Concrete analysis using the Sign domain.
*)

definition sign_analysis_config :: "state => sign analysis_config" where
  "sign_analysis_config s =
     (| ac_join  = sign_domain.join_state,
        ac_bot   = sign_domain.bot_state,
        ac_gamma = gamma_sign,
        ac_tf    = (| tf_assign    = assign_sign,
                      tf_assume    = assume_sign,
                      tf_assume_not = assume_not_sign |),
        ac_init  = (\<lambda>x. sign_of_int (s x)) |)"

text \<open>
  Scaffold: reduce sign pipeline soundness to the generic pipeline theorem at
  @{const sign_analysis_config}; discharge Sign TF lemmas (Phase I) and
  @{const sign_of_int} / @{const gamma_sign} for the initial state.
\<close>

lemma sign_analysis_init_in_gamma_stub:
  "s : sign_domain.gamma_state (ac_init (sign_analysis_config s))"
  sorry (* per-variable: s x \<in> gamma_sign (sign_of_int (s x)) *)

lemma sign_analysis_tf_sound_stub:
  "domain_transfer_sound gamma_sign (ac_tf (sign_analysis_config s))"
  sorry (* Phase I: assign_sign, assume_sign, assume_not_sign *)

lemma sign_pipeline_sound_scaffold:
  assumes runs: "big_step (c, s) t"
    and tf_ok: "domain_transfer_sound gamma_sign (ac_tf (sign_analysis_config s))"
    and init_ok: "s : sign_domain.gamma_state (ac_init (sign_analysis_config s))"
  shows "t : sign_domain.gamma_state
             (run_analysis (sign_analysis_config s) c (cfg_exit (to_cfg c)))"
proof -
  show ?thesis
    sorry (* pipeline_sound [OF tf_ok init_ok runs], gamma_state coercion Sign vs abstract_domain *)
qed

(* Corollary of scaffold + stubs once lemmas exist. *)
corollary sign_pipeline_sound:
  assumes terminates: "big_step (c, s) t"
  shows   "t : sign_domain.gamma_state
                  (run_analysis (sign_analysis_config s) c
                     (cfg_exit (to_cfg c)))"
  using sign_pipeline_sound_scaffold[OF terminates sign_analysis_tf_sound_stub sign_analysis_init_in_gamma_stub]
  sorry

(* ── Interval Analysis Pipeline ──────────────────────────────── *)
(*
  Concrete analysis using the Interval domain.
*)

definition ivl_analysis_config :: "state => ivl analysis_config" where
  "ivl_analysis_config s =
     (| ac_join  = ivl_domain.join_state,
        ac_bot   = ivl_domain.bot_state,
        ac_gamma = gamma_ivl,
        ac_tf    = (| tf_assign    = assign_ivl,
                      tf_assume    = assume_ivl,
                      tf_assume_not = assume_not_ivl |),
        ac_init  = (\<lambda>x. Ivl (Fin (s x)) (Fin (s x))) |)"

(*
  Same structure as sign_pipeline_sound.
  Requires ivl TF soundness + init soundness (analogues of the sign stubs).
  Those must be proved before this corollary can be closed.
*)
corollary ivl_pipeline_sound:
  assumes terminates: "big_step (c, s) t"
  shows   "t : ivl_domain.gamma_state
                  (run_analysis (ivl_analysis_config s) c
                     (cfg_exit (to_cfg c)))"
  sorry (* pipeline_sound[OF ivl_tf_sound_stub ivl_init_sound_stub terminates] once those exist *)

(* ── Option 2: Point-Map Invariant (Recommended Presentation) ── *)
(*
  Stronger than pipeline_sound: the abstract state at EVERY program point
  is a sound invariant, not just at the exit.

  This falls out for free from post_fixpoint_sound + td_analyse_post_fixpoint:
    td_analyse_post_fixpoint  →  is_post_fixpoint ... (run_analysis cfg c)
    post_fixpoint_sound       →  \<forall>v. cfg_reach g {s} v ⊆ gamma_state (env v)
  Exit soundness (pipeline_sound) is the v = cfg_exit special case.

  This is what supervisors requested in meeting 2:
    "point-map soundness predicate: \<forall> p. collect_sem_at c p ⊆ γ(mlup σ p)"
*)

(*
  Point-map invariant: the solver result is sound at EVERY program point.
  Does NOT require termination — holds for all starting states s in gamma(init).
  The terminates assumption was removed; it is unused (the \<forall>v conclusion
  does not depend on any specific execution reaching exit).
*)
theorem pipeline_invariant_sound:
  assumes tf_sound:   "domain_transfer_sound (ac_gamma cfg) (ac_tf cfg)"
  assumes s_in_gamma: "s : abstract_domain.gamma_state (ac_gamma cfg) (ac_init cfg)"
  shows   "\<forall>v. cfg_reach (to_cfg c) {s} v <=
                    abstract_domain.gamma_state (ac_gamma cfg)
                      (run_analysis cfg c v)"
  sorry
  (* Proof:
       (1) td_analyse_post_fixpoint gives is_post_fixpoint (run_analysis cfg c)
       (2) {s} ⊆ gamma_state(ac_init cfg) from s_in_gamma
       (3) post_fixpoint_sound gives \<forall>v. cfg_reach ... {s} v ⊆ gamma_state(env v)
     pipeline_sound is the v = cfg_exit special case; terminates not needed. *)

(*
  Sign-domain specialisation.  Hypotheses must match pipeline_invariant_sound:
  TF soundness + s \<in> gamma(init).  The (c,s)⇒t assumption was superfluous.
*)
theorem sign_pipeline_invariant_sound:
  assumes tf_ok:   "domain_transfer_sound gamma_sign (ac_tf (sign_analysis_config s))"
  assumes init_ok: "s : sign_domain.gamma_state (ac_init (sign_analysis_config s))"
  shows   "\<forall>v. cfg_reach (to_cfg c) {s} v <=
                    sign_domain.gamma_state
                      (run_analysis (sign_analysis_config s) c v)"
  sorry (* BY pipeline_invariant_sound[OF tf_ok init_ok'] once init_ok matches abstract_domain.gamma_state *)

end
