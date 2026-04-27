theory Pipeline
  imports TD_Soundness Sign_Domain Interval_Domain
begin

(*
  Full Analysis Pipeline.

  This theory assembles the complete end-to-end pipeline:

    IMP2 source  --[to_cfg]-->  CFG
                 --[rhs]------>  Constraint System
                 --[td_solve]->  Fixed-Point Environment
                 --[gamma]---->  State-Set Overapproximation

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
    "('a::ord => int set)
     => 'a domain_transfer
     => bool"
where
  "domain_transfer_sound gamma tf =
     ((ALL x a sigma. ALL s : abstract_domain.gamma_state gamma sigma.
         s(x := aval a s) : abstract_domain.gamma_state gamma (tf_assign tf x a sigma))
      & (ALL b sigma. ALL s : abstract_domain.gamma_state gamma sigma. bval b s
           --> s : abstract_domain.gamma_state gamma (tf_assume tf b sigma))
      & (ALL b sigma. ALL s : abstract_domain.gamma_state gamma sigma. ~ bval b s
           --> s : abstract_domain.gamma_state gamma (tf_assume_not tf b sigma)))"

(* ── Generic Pipeline Record ──────────────────────────────────── *)
(*
  Bundle everything needed to run an analysis:
    - the abstract domain operations
    - the transfer functions
    - the initial abstract state
*)

record ('a::ord) analysis_config =
  ac_join     :: "'a abs_state => 'a abs_state => 'a abs_state"
  ac_bot      :: "'a abs_state"
  ac_gamma    :: "'a => int set"
  ac_tf       :: "'a domain_transfer"
  ac_init     :: "'a abs_state"

(* ── Run the Pipeline ─────────────────────────────────────────── *)

definition run_analysis ::
    "('a::ord) analysis_config => com => pp => 'a abs_state"
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
        ac_init  = (%x. sign_of_int (s x)) |)"

theorem sign_pipeline_sound:
  assumes "big_step (c, s) t"
  shows   "t : sign_domain.gamma_state
                  (run_analysis (sign_analysis_config s) c
                     (cfg_exit (to_cfg c)))"
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
        ac_init  = (%x. Ivl (Fin (s x)) (Fin (s x))) |)"

theorem ivl_pipeline_sound:
  assumes "big_step (c, s) t"
  shows   "t : ivl_domain.gamma_state
                  (run_analysis (ivl_analysis_config s) c
                     (cfg_exit (to_cfg c)))"
  sorry

end
