theory Analysis_Config
  imports Main
begin

section \<open>Semantic analysis configuration\<close>

text \<open>
  One canonical, executable representation of the choices that change
  \<^emph>\<open>what gets solved\<close>: abstract domain, solver update-rule discipline, and
  context sensitivity. Presentation choices (DOT vs. a textual snapshot,
  collapsed vs. expanded context rendering) are deliberately absent -- they
  select how an already-computed result is drawn, never what the solver
  computes, and stay owned by the CLI layer instead (\<open>Analysis_GraphViz.thy\<close>).

  This theory names \<open>Sign\<close>/\<open>Interval\<close>/\<open>Int\<close> explicitly by construction, so it
  sits in \<open>Voblint_Analysis\<close> rather than \<open>Voblint_Core\<close>: \<open>Core\<close> carries no
  domain-specific content, and a domain-naming enum is domain-specific
  content even though it carries no analysis logic of its own.

  Constructor names below reuse exactly what \<open>Analyse_Dispatch\<close>'s own
  \<open>analysis_domain\<close>/\<open>context_mode\<close>/\<open>solver_choice\<close> already use
  (\<open>Sign_Analysis\<close>, \<open>Ctx_EntryState\<close>, \<open>Solver_Warrow\<close>, ...): only the
  \<open>analysis_domain \<Rightarrow> analysis_domain\<close> type rename is a real improvement
  (it names what the type \<^emph>\<open>is\<close>, not the shape of its first constructor);
  renaming already-public constructor names across every consumer -- the
  CLI, every \<open>Analyse_Dispatch\<close> branch, every codegen export -- would be
  pure churn this migration does not need.
\<close>

subsection \<open>Selection axes\<close>

text \<open>
  Every value below is a real, currently reachable public selection --
  reachable from the CLI, from \<open>Analyse_Dispatch\<close>'s existing dispatchers, or
  both. Refinement mode (\<open>Refine_Never\<close>/\<open>Refine_Once\<close>/\<open>Refine_Fixpoint\<close>,
  \<open>Int_Refinement.thy\<close>) stays out of this datatype: \<open>Int_Analysis\<close> is
  fixed at \<open>Refine_Fixpoint\<close> in production, and adding the axis here would
  design a configuration space around behavior that does not yet reach the
  CLI or \<open>Analyse_Dispatch\<close> at all.

  Call-string context length, by contrast, is now genuinely public: unlike
  the fixed \<open>k=1\<close>/\<open>k=2\<close> example theories this datatype once deferred to,
  \<open>Interval_Call_String_Ctx_Sound.thy\<close> is one
  runtime-\<open>k\<close>-parametric pipeline, proved to reproduce those two examples'
  exact solved states and their precision separation. \<open>Ctx_CallString k\<close>
  routes to it directly, the same way \<open>Ctx_EntryState\<close> routes to
  \<open>Interval_Exec_Ctx_Sound.thy\<close>.
\<close>

datatype analysis_domain = Sign_Analysis | Interval_Analysis | Int_Analysis

datatype solver_choice = Solver_Join | Solver_PerOrigin | Solver_Warrow

datatype context_mode = Ctx_None | Ctx_EntryState | Ctx_CallString nat

text \<open>
  \<open>cfg_solver\<close> is an \<^typ>\<open>solver_choice option\<close>, not a bare \<open>solver_choice\<close>,
  because \<open>None\<close> and an explicit selection are observably different today:
  \<open>--context entry-state\<close> alone resolves to the warrowing solver, but
  \<open>--context entry-state --solver warrow\<close> is rejected even though the
  resolved solver is the same value, because the CLI treats an explicit
  \<open>--solver\<close> selection as incompatible with any \<open>--context\<close> other than
  \<open>none\<close>, unconditionally. Collapsing \<open>None\<close> and \<open>Some\<close>-of-the-default into
  one bare field would erase that distinction and could not reproduce this
  behavior.
\<close>

record analysis_config =
  cfg_domain :: analysis_domain
  cfg_solver :: "solver_choice option"
  cfg_context :: context_mode

text \<open>
  A plain, exportable constructor: OCaml code (the CLI) never sees the raw
  record literal syntax underneath \<^type>\<open>analysis_config\<close>, only this
  function -- the same pattern \<open>mk_program\<close> already gives \<open>imp_prog\<close>,
  a record no other export ever exposes directly either.
\<close>

definition mk_analysis_config ::
    "analysis_domain \<Rightarrow> solver_choice option \<Rightarrow> context_mode \<Rightarrow> analysis_config" where
  "mk_analysis_config d s c = \<lparr> cfg_domain = d, cfg_solver = s, cfg_context = c \<rparr>"

subsection \<open>Resolved plan\<close>

text \<open>
  What \<open>resolve_analysis_config\<close> below resolves a legal
  \<^type>\<open>analysis_config\<close> to: exactly enough to pick the one existing,
  already-typed report/result function a caller should run next
  (\<open>Analyse_Dispatch\<close>'s own \<open>analyse\<close>/\<open>analyse_ctx\<close>/\<open>analyse_with_solver\<close>
  branches, unchanged). \<open>Plan_Interval_EntryState\<close> and
  \<open>Plan_Interval_CallString\<close> both carry a \<^typ>\<open>solver_choice\<close>: the routed
  equation system underneath either context (\<open>Interval_Exec_Ctx_Sound.thy\<close>'s
  \<open>entry_state_eqs\<close>, \<open>Interval_Call_String_Ctx_Sound.thy\<close>'s
  \<open>cs_call_string_eqs\<close>) names no solve function of its own -- only the
  shared D/G spec and the routing policy -- so it is solved under all three
  disciplines exactly as the flat \<open>Ctx_None\<close> equation system already is
  (\<open>Interval_Exec_Sound.thy\<close>'s \<open>analyse_interval_dg_join_for\<close>/
  \<open>_per_origin_for\<close>/default). Warrow stays each context's implicit default
  (\<open>cfg_solver = None\<close>), matching the behavior already shipped before this
  generalization.
\<close>

datatype analysis_plan =
    Plan_Sign solver_choice
  | Plan_Sign_EntryState solver_choice
  | Plan_Sign_CallString solver_choice nat
  | Plan_Interval solver_choice
  | Plan_Interval_EntryState solver_choice
  | Plan_Interval_CallString solver_choice nat
  | Plan_Int solver_choice
  | Plan_Int_EntryState solver_choice
  | Plan_Int_CallString solver_choice nat

subsection \<open>Canonical resolver\<close>

text \<open>
  The one legality-and-defaults table this configuration has. Every other
  question about an \<^type>\<open>analysis_config\<close> -- is it valid at all, what plan
  does it resolve to -- is answered by consulting this function, never by a
  second, independently maintained case split: \<open>valid_analysis_config\<close>
  below is stated directly in terms of it, and any config-driven dispatch
  wrapper built on top must go through \<open>resolve_analysis_config\<close>
  rather than re-deciding legality itself.

  Read by domain:

  \<^item> \<open>Sign\<close>: \<open>Solver_Warrow\<close> is unsupported at every context (\<open>sign\<close> has no
    \<open>widen\<close> instance, so nothing downstream of this resolver could execute
    it even if accepted here). \<open>Ctx_EntryState\<close> and \<open>Ctx_CallString k\<close>
    (\<open>k \<ge> 1\<close>) are both supported at the one solver Sign's own routed
    soundness proves at each, \<open>Solver_Join\<close>; \<open>Solver_PerOrigin\<close> is
    genuinely unproven at either context (unlike at \<open>Ctx_None\<close>, where it
    already is) and stays unsupported until that proof exists, matching
    this resolver's stated discipline of following proved capability
    rather than solver symmetry.
  \<^item> \<open>Interval\<close>: every solver is supported at \<open>Ctx_None\<close>, at \<open>Ctx_EntryState\<close>,
    and at \<open>Ctx_CallString k\<close> (\<open>k \<ge> 1\<close>) alike, defaulting to \<open>Solver_Warrow\<close>
    at each: the routed equation system underneath either context is exactly
    as solver-independent as the flat one.
  \<^item> \<open>Int\<close>: every solver is supported at \<open>Ctx_None\<close>, defaulting to
    \<open>Solver_Warrow\<close> (\<open>Int_Analysis\<close>'s own production default). \<open>Ctx_EntryState\<close>
    and \<open>Ctx_CallString k\<close> (\<open>k \<ge> 1\<close>) are both supported at the one solver Int's
    own routed soundness proves at each, \<open>Solver_Join\<close>, mirroring Sign's own
    posture at both contexts.
\<close>

fun resolve_analysis_config :: "analysis_config \<Rightarrow> analysis_plan option" where
  "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = None, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Sign Solver_Join)"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Sign Solver_Join)"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Sign Solver_PerOrigin)"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_None \<rparr>
     = None"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = None, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Sign_EntryState Solver_Join)"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Sign_EntryState Solver_Join)"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = None, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Sign_CallString Solver_Join k))"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Sign_CallString Solver_Join k))"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = None, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Interval Solver_Warrow)"
| "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some s, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Interval s)"
| "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = None, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState Solver_Warrow)"
| "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some s, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState s)"
| "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = None, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Interval_CallString Solver_Warrow k))"
| "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some s, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Interval_CallString s k))"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = None, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Int Solver_Warrow)"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some s, cfg_context = Ctx_None \<rparr>
     = Some (Plan_Int s)"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = None, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Int_EntryState Solver_Join)"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Int_EntryState Solver_Join)"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
     = None"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = None, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Int_CallString Solver_Join k))"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString k \<rparr>
     = (if k = 0 then None else Some (Plan_Int_CallString Solver_Join k))"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString k \<rparr>
     = None"
| "resolve_analysis_config \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString k \<rparr>
     = None"

definition valid_analysis_config :: "analysis_config \<Rightarrow> bool" where
  "valid_analysis_config cfg = (resolve_analysis_config cfg \<noteq> None)"

subsection \<open>The resolver matrix, pinned\<close>

text \<open>
  Every currently-public combination and its resolution, as a regression
  against the CLI's actual observable behavior rather than a restatement of
  the equations above. \<open>Interval\<close> at \<open>Ctx_EntryState\<close> pins each of the
  three explicit-solver rejections individually, not just one
  representative: the CLI's solver/context exclusion is unconditional on
  the solver value, and only pinning \<open>Solver_Join\<close> (say) would leave
  \<open>Solver_Warrow\<close> -- the one value that happens to equal EntryState's own
  internal default -- unpinned, exactly the case most likely to
  accidentally become valid in a future edit.
\<close>

definition default_config :: "analysis_domain \<Rightarrow> context_mode \<Rightarrow> analysis_config" where
  "default_config d c = mk_analysis_config d None c"

lemma resolver_sign_default:
  "resolve_analysis_config (default_config Sign_Analysis Ctx_None) = Some (Plan_Sign Solver_Join)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_default:
  "resolve_analysis_config (default_config Interval_Analysis Ctx_None) = Some (Plan_Interval Solver_Warrow)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_default:
  "resolve_analysis_config (default_config Int_Analysis Ctx_None) = Some (Plan_Int Solver_Warrow)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_warrow_invalid:
  "resolve_analysis_config \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_None \<rparr> = None"
  by simp

lemma resolver_interval_entrystate_default_valid:
  "resolve_analysis_config (default_config Interval_Analysis Ctx_EntryState)
     = Some (Plan_Interval_EntryState Solver_Warrow)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_entrystate_join_valid:
  "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState Solver_Join)"
  by simp

lemma resolver_interval_entrystate_per_origin_valid:
  "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState Solver_PerOrigin)"
  by simp

lemma resolver_interval_entrystate_warrow_valid:
  "resolve_analysis_config \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
     = Some (Plan_Interval_EntryState Solver_Warrow)"
  by simp

text \<open>
  Sign at \<open>Ctx_EntryState\<close>, pinned the same way \<open>Ctx_CallString\<close>'s own regressions are:
  valid at the implicit-default and explicit \<open>Solver_Join\<close> selections, invalid at the
  two solvers Sign's entry-state soundness does not prove.
\<close>

lemma resolver_sign_entrystate_default_valid:
  "resolve_analysis_config (default_config Sign_Analysis Ctx_EntryState)
     = Some (Plan_Sign_EntryState Solver_Join)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_entrystate_explicit_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
   = Some (Plan_Sign_EntryState Solver_Join)"
  by simp

lemma resolver_sign_entrystate_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr>
   = None"
  by simp

lemma resolver_sign_entrystate_warrow_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
   = None"
  by simp

text \<open>
  Int at \<open>Ctx_EntryState\<close>, pinned the same way Sign's own resolver regressions are:
  valid at the implicit-default and explicit \<open>Solver_Join\<close> selections, invalid at the
  two solvers Int's own entry-state soundness does not prove.
\<close>

lemma resolver_int_entrystate_default_valid:
  "resolve_analysis_config (default_config Int_Analysis Ctx_EntryState)
     = Some (Plan_Int_EntryState Solver_Join)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_entrystate_explicit_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_EntryState \<rparr>
   = Some (Plan_Int_EntryState Solver_Join)"
  by simp

lemma resolver_int_entrystate_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_EntryState \<rparr>
   = None"
  by simp

lemma resolver_int_entrystate_warrow_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_EntryState \<rparr>
   = None"
  by simp

text \<open>
  Call-string, pinned the same way: \<open>k=1\<close>/\<open>k=2\<close> at the implicit default
  solver resolve to Warrow; \<open>k=0\<close> is rejected regardless of solver, even
  though \<open>cs_route 0\<close> (\<open>Call_String_Context.thy\<close>) is itself a well-defined,
  well-typed route (it collapses every activation's context to \<open>[]\<close>,
  distinct from \<open>Ctx_None\<close>'s own, entirely separate flat equation system --
  \<open>k=0\<close> is not \<open>Ctx_None\<close> in disguise). Exposing it anyway would only
  invite exactly the confusion this decision avoids: a user who wants no
  context sensitivity already has \<open>Ctx_None\<close>; a \<open>call-string\<close> selection
  whose only well-typed positive-information use is separating at least two
  call sites needs \<open>k \<ge> 1\<close> to do that at all, so \<open>k=0\<close> has no positive
  reason to exist as a public value. Every explicit-solver pairing at \<open>k \<ge> 1\<close>
  is valid, exactly as \<open>Ctx_EntryState\<close>'s now is; Sign/Int at any \<open>k\<close> stay
  rejected, matching \<open>Ctx_EntryState\<close>'s.
\<close>

lemma resolver_interval_callstring_k1_valid:
  "resolve_analysis_config (default_config Interval_Analysis (Ctx_CallString 1))
     = Some (Plan_Interval_CallString Solver_Warrow 1)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_callstring_k2_valid:
  "resolve_analysis_config (default_config Interval_Analysis (Ctx_CallString 2))
     = Some (Plan_Interval_CallString Solver_Warrow 2)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_callstring_zero_invalid:
  "resolve_analysis_config (default_config Interval_Analysis (Ctx_CallString 0)) = None"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_interval_callstring_zero_explicit_solver_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 0 \<rparr>
   = None"
  by simp

lemma resolver_interval_callstring_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Interval_CallString Solver_Join 2)"
  by simp

lemma resolver_interval_callstring_per_origin_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Interval_CallString Solver_PerOrigin 2)"
  by simp

lemma resolver_interval_callstring_warrow_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Interval_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Interval_CallString Solver_Warrow 2)"
  by simp

text \<open>
  Sign at \<open>Ctx_CallString\<close>: valid at \<open>k \<ge> 1\<close> under the one solver Sign's own
  routed call-string soundness actually proves (\<open>Solver_Join\<close>, matching the
  implicit default), \<open>k = 0\<close> rejected exactly as Interval's is, and
  \<open>Solver_PerOrigin\<close>/\<open>Solver_Warrow\<close> rejected -- unlike Interval, where every
  solver is proved at every context -- because Sign's call-string soundness
  currently proves only the always-join discipline.
\<close>

lemma resolver_sign_callstring_k1_valid:
  "resolve_analysis_config (default_config Sign_Analysis (Ctx_CallString 1))
     = Some (Plan_Sign_CallString Solver_Join 1)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_callstring_k2_valid:
  "resolve_analysis_config (default_config Sign_Analysis (Ctx_CallString 2))
     = Some (Plan_Sign_CallString Solver_Join 2)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_callstring_zero_invalid:
  "resolve_analysis_config (default_config Sign_Analysis (Ctx_CallString 0)) = None"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_sign_callstring_explicit_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Sign_CallString Solver_Join 2)"
  by simp

lemma resolver_sign_callstring_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr>
   = None"
  by simp

lemma resolver_sign_callstring_warrow_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Sign_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr>
   = None"
  by simp

text \<open>
  Int at \<open>Ctx_CallString\<close>, pinned the same way Sign's own resolver regressions are:
  valid at \<open>k \<ge> 1\<close> under the implicit-default and explicit \<open>Solver_Join\<close> selections,
  invalid at \<open>k = 0\<close> and at the two solvers Int's own call-string soundness does not
  prove.
\<close>

lemma resolver_int_callstring_k1_valid:
  "resolve_analysis_config (default_config Int_Analysis (Ctx_CallString 1))
     = Some (Plan_Int_CallString Solver_Join 1)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_callstring_k2_valid:
  "resolve_analysis_config (default_config Int_Analysis (Ctx_CallString 2))
     = Some (Plan_Int_CallString Solver_Join 2)"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_callstring_zero_invalid:
  "resolve_analysis_config (default_config Int_Analysis (Ctx_CallString 0)) = None"
  by (simp add: default_config_def mk_analysis_config_def)

lemma resolver_int_callstring_explicit_join_valid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Join, cfg_context = Ctx_CallString 2 \<rparr>
   = Some (Plan_Int_CallString Solver_Join 2)"
  by simp

lemma resolver_int_callstring_per_origin_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_PerOrigin, cfg_context = Ctx_CallString 2 \<rparr>
   = None"
  by simp

lemma resolver_int_callstring_warrow_invalid:
  "resolve_analysis_config
     \<lparr> cfg_domain = Int_Analysis, cfg_solver = Some Solver_Warrow, cfg_context = Ctx_CallString 2 \<rparr>
   = None"
  by simp



lemma valid_analysis_config_eq_resolver:
  "valid_analysis_config cfg \<longleftrightarrow> resolve_analysis_config cfg \<noteq> None"
  by (simp add: valid_analysis_config_def)

end

