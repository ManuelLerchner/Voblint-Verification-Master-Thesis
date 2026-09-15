theory Analysis_Config
  imports Main
begin

section \<open>Semantic analysis configuration\<close>

text \<open>
  One canonical, executable representation of the choices that change
  \<^emph>\<open>what gets solved\<close>: abstract domain, solver update-rule discipline, and
  context sensitivity. Presentation choices (DOT vs. a textual snapshot) are
  deliberately absent -- they select how an already-computed result is drawn,
  never what the solver computes, and stay with the handwritten renderers.

  This theory names every domain explicitly by construction, so it sits in
  \<open>Voblint_CLI\<close> rather than under \<open>Analyses/Shared/\<close>: the shared layer carries no
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
  \<open>Int_Refinement\<close>) stays out of this datatype: \<open>Int_Analysis\<close> is
  fixed at \<open>Refine_Fixpoint\<close> in production, and adding the axis here would
  design a configuration space around behavior that does not yet reach the
  CLI or \<open>Analyse_Dispatch\<close> at all.

  Call-string context length, by contrast, is now genuinely public: unlike
  the fixed \<open>k=1\<close>/\<open>k=2\<close> example theories this datatype once deferred to,
  \<open>Interval_Analyses\<close> is one
  runtime-\<open>k\<close>-parametric pipeline, proved to reproduce those two examples'
  exact solved states and their precision separation. \<open>Ctx_CallString k\<close>
  routes to it directly, the same way \<open>Ctx_EntryState\<close> routes to
  \<open>Interval_Analyses\<close>.
\<close>

datatype analysis_domain =
    Sign_Analysis | Interval_Analysis | Int_Analysis | Parity_Analysis
  | Congruence_Analysis

datatype solver_choice =
    Solver_Join | Solver_PerOrigin | Solver_Warrow | Solver_WarrowPerOrigin

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
  (\<open>Analyse_Dispatch\<close>'s own \<open>analyse\<close>/\<open>analyse_with_solver\<close> branches,
  unchanged). \<open>Plan_Interval_EntryState\<close> and
  \<open>Plan_Interval_CallString\<close> both carry a \<^typ>\<open>solver_choice\<close>: the routed
  equation system underneath either context (\<open>Interval_Analyses\<close>'s
  \<open>entry_state_eqs_prog\<close>, \<open>Interval_Analyses\<close>'s
  \<open>cs_call_string_eqs_prog\<close>) names no solve function of its own -- only the
  shared D/G spec and the routing policy -- so it is solved under all three
  disciplines exactly as the flat \<open>Ctx_None\<close> equation system already is
  (\<open>Interval_Assembly\<close>'s join, per-origin and warrowing registrations). Warrow stays
  each context's implicit default
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
  | Plan_Parity solver_choice
  | Plan_Parity_EntryState solver_choice
  | Plan_Parity_CallString solver_choice nat
  | Plan_Congruence solver_choice
  | Plan_Congruence_EntryState solver_choice
  | Plan_Congruence_CallString solver_choice nat

subsection \<open>Canonical resolver\<close>

text \<open>
  The one legality-and-defaults table this configuration has. Every other
  question about an \<^type>\<open>analysis_config\<close> -- is it valid at all, what plan
  does it resolve to -- is answered by consulting this function, never by a
  second, independently maintained case split: \<open>valid_analysis_config\<close>
  is stated directly in terms of it, and any config-driven dispatch
  wrapper built on top must go through \<open>resolve_analysis_config\<close>
  rather than re-deciding legality itself. Both are generated from the
  registry rather than written here; this describes what they decide.

  Read by domain:

  \<^item> \<open>Sign\<close>: \<open>Solver_Warrow\<close> is unsupported at every context. As with Parity
    below, the rule is mechanically available --- \<open>sign\<close> is a finite lattice
    whose \<open>warrowing\<close> instance sets \<open>widen = sup\<close> --- but no solved table or
    soundness corollary stands behind it, and this resolver follows proved
    capability rather than the instance. \<open>Ctx_EntryState\<close> and \<open>Ctx_CallString k\<close>
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
    and \<open>Ctx_CallString k\<close> (\<open>k \<ge> 1\<close>) are supported at the two solvers Int's
    own routed soundness certifies at each, \<open>Solver_Warrow\<close> (the default, as at
    \<open>Ctx_None\<close>: always-join has no termination guarantee on the interval
    component once a collapsed context feeds a callee its own decremented
    formals) and \<open>Solver_Join\<close>.
  \<^item> \<open>Parity\<close>: \<open>Solver_Join\<close> (the default) at every context, and
    \<open>Solver_PerOrigin\<close> additionally at \<open>Ctx_None\<close> --- the solved tables
    Parity's own routed instances build. \<open>Solver_Warrow\<close> is mechanically
    available (\<open>parity\<close> is a finite lattice with \<open>widen = sup\<close>) but has no
    solved table or soundness corollary, so it stays unsupported rather than
    being exposed on the strength of the instance alone. \<open>Ctx_CallString 0\<close>
    is rejected: a zero-length call string is the unit context spelled twice.
  \<^item> \<open>Congruence\<close>: \<open>Solver_Join\<close> (the default) at every context, and
    \<open>Solver_PerOrigin\<close> additionally at \<open>Ctx_None\<close>, on the same reading as
    Parity --- the solved tables its own routed instances build, not the
    instances the lattice would admit. \<open>Ctx_CallString 0\<close> is rejected as
    everywhere else.
\<close>

text \<open>
  The configuration a caller supplies when it makes no choice: the domain and
  context it asked for, and no solver, so the resolver applies that pairing's
  own default.
\<close>

definition default_config :: "analysis_domain \<Rightarrow> context_mode \<Rightarrow> analysis_config" where
  "default_config d c = mk_analysis_config d None c"

end
