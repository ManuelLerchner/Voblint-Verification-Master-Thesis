# Next work

GitHub Project 8 contains scheduling and dependencies. The stable technical
directions are:

## Context abstractions

Define finite executable context domains with a proved abstraction relation to
concrete activations. Evaluate recursive and widening-heavy examples separately
from repeated-call examples.

Tracked in detail in #108 (references #66, #77); summary below, keep the
two in sync if either changes.

**Naming note (2026-08-11, issue #110):** the dated milestones below narrate
each identifier as it was named at the time. Issue #110's terminology pass
renamed the semantic context function per instance from `*_enterc` to
`*_context` and gave the generic locale parameter `route` inline notation
`context#`: `ivl_enterc` -> `ivl_context`, `entry_state_enterc` ->
`entry_state_context`, `formals_enterc` -> `formals_context_sem`. `route`,
`route_ivl`, `route_enterc_agree`, and `enterc` itself (the generic locale
parameter these are all named relative to) are unchanged. Grep the current
name if a mention below doesn't turn up a hit.

Post-#66, `routed_context` (`Routed_Context.thy`) is real Core-level
infrastructure, not example-level: it discharges the CALL/COMB obligations
once, generically in a `route`/`enterc` pair and context type `'c`. Four
interpretations already exist, including `Example_Interval_DG_Ctx_Flagship
.thy`'s `route_ivl`/`ivl_enterc` -- a genuinely value-derived context
(`'c = ivl`, not call-site history), with `contexts_distinct` proved `by
eval` for two calls with different argument values landing in separate,
un-joined contexts. So the CALL/COMB soundness machinery this feature needs
already exists and is reusable. What's still missing:

**Finiteness dependency resolved (2026-08-10).** `'c` carries no
`::finite` sort constraint anywhere in `routed_context`/`dg_ctx_activation`/
the TD solver -- `solve_dom` is a per-run computational-domain predicate,
not a type-class constraint, and `Interval_Exec_Sound.thy`'s
`ivl_exec_terminates_via_solve_c` already discharges it empirically for the
flat analysis, with soundness proved unconditionally from there. So #77
("Context-bounding lifters") is not a termination blocker for G1: unbounded
entry-state contexts can ship on the same "if the solver returns, the
result is sound" contract the flat analysis already relies on.

**Exactness boundary found while grounding G1 (2026-08-10).**
`route_enterc_agree` (`Routed_Context.thy:101-107`) is a literal equality
required across every concretization of the caller's entered abstract
state. Since `enterc` decodes a concrete value to an exact point, the
equality only holds when the caller's abstract value at each
context-forming formal is itself exact -- true of the flagship's
literal-constant calls, not guaranteed generally. #77 resurfaces here for a
different reason than termination: making the equality hold for non-exact
callers needs `'c` to carry an order with the solver monotone in it --
structurally #77's "Context Widening", reached from the routing-soundness
side rather than the termination side. #108's G1-G5 plan (in the issue):

1. **G1 -- generic exact-entry context construction (infrastructure, not
   yet a general CLI feature). Done, batch-green (2026-08-10).**
   `route_ivl`/`ivl_enterc` were hardcoded to one formal name (`"p"`), built
   for that one flagship program. Replaced with `formals_context`/
   `formals_route`/`formals_route_gen`/`formals_at_call_site`/
   `formals_enterc` (`Routed_Context.thy`, domain-generic, no `Ivl`
   reference), reusing `CallEdge`'s own `pars` field -- no separate
   `formals(Pi(q))` lookup needed -- and discharged via a `routed_context`
   interpretation across `Example_Interval_DG_Ctx_Flagship.thy`,
   `_Ctx_Sound.thy`, `_Ctx_Collect.thy`, and `Example_Interval_Source_Ctx.thy`
   (the last caught only by the batch build, not interactive I/Q, since it
   was never opened during development). No procedure identity folded into
   `'c`: `vars`/`seed_key` already pair `'c` with `pp`, which disambiguates
   by callee. Proved at exact call sites (matching the flagship); the
   exactness precondition above is not lifted -- that's G2.
2. **G2 -- abstract context coverage semantics. Done, batch-green
   (2026-08-10).** G2a's `ctx_rep`-over-exact-`key` design (below, kept for
   the historical record) turned out not to compose through COMB: a
   trace's admitted context and the callee's admitted context were
   rediscovered independently, so nothing tied them together at the
   return. The fix was architectural, not a patch -- replace the
   deterministic `enterc :: cfg_node => 'c => store => 'c` with a
   relational `admiss :: cfg_node => 'c => store => 'c => bool`, and key
   traces through it via a new inductive `ctx_key` (mirroring `key`'s own
   recursion, `CFG_Local_Trace.thy`) instead of the old deterministic
   `key`. This is the paper's own soundness argument (Erhard, Schinabeck,
   Schwarz, Seidl, "Context Gas and friends," IJSTTT 2025, Section 10's
   description function `beta`, rules D1-D3, Theorem 1/Theorem 2), not an
   ad hoc analogy: the callee's admitted context is now *derived from* the
   caller's own admiss-witnessed context (`ctx_key_entry_invariant_iff`),
   never rediscovered, which is exactly what makes COMB provable.

   `ltr_gamma` (`LTR_Abstract.thy`) is restated over `admiss`/`seedc` with
   a new `ADMISS_TOTAL` assumption and `admiss`-relaxed CALL/COMB;
   `activation_collect` (`CFG_Local_Trace.thy`) is redefined directly via
   `ctx_key`, dropping G2a's `ctx_rep`/`MONO` machinery entirely (`ctx_key`
   itself now does what `MONO` patched around). `admiss_exact enterc`
   (`admiss_exact_def`: `c' = enterc u c s`) is the functional special case
   recovering the old deterministic behavior exactly, proved via
   `ctx_key_exact_iff`: `ctx_key (admiss_exact enterc) seedc t c <->
   key enterc seedc t = c`. Every existing exact-context client --
   `Call_String_Collecting_Refinement.thy`, all four CallString examples
   (Interval K1/K2/flat, Sign K1/K2), both G1 Ctx examples
   (`Example_Interval_DG_Ctx_Collect.thy`, `Example_Interval_Source_Ctx
   .thy`) -- reduces to its previous behavior through that lemma, with no
   change to `Routed_Context.thy`'s locale itself: `route_enterc_agree`
   stays a plain equation, since an `admiss` instance that ignores its
   `store` argument (using only the caller's already-solved abstract
   state) is *already* `admiss_exact`-shaped.

   The acceptance case is proved: `Example_Interval_DG_EntryState_{Base,
   Ctx,Sound,Collect}.thy` compile `void p(a) { return a }` / `void main()
   { x := random(); y := p(x) }`, route the call through the caller's
   solved (necessarily `Top`) interval for `x`, and the executable solver
   confirms `ctx_call = [ivl_top]` (`ctx_call_val`, `by eval`) -- one
   context, not a family indexed by which concrete value `random()`
   produced. `entry_state_coverage` (`Example_Interval_DG_EntryState_Collect
   .thy`) is the crux corollary: for every concrete store reaching the
   call site, the callee entry lands at the same fixed `ctx_call`, with no
   `s`-dependence anywhere in the conclusion.

   G2a's design, for reference: `activation_collect` took a coverage
   relation `ctx_rep :: 'c => 'c => bool` (membership `ctx_rep (key enterc
   seedc t) c`), and `activation_collect_sound` a `MONO` obligation
   (`ctx_rep c1 c2 ==> sg-slot c1 <= sg-slot c2`) -- both now superseded by
   `admiss`/`ctx_key` and removed from the codebase.
3. **G3 -- executable context-sensitive Interval endpoint. Done, batch-green
   (2026-08-11).** `entry_state_sol`/`entry_state_terminates`
   (`Interval_Exec_Ctx_Sound.thy`, `src/Formalization/Pipeline/`)
   generalize the acceptance example's fixed program to an arbitrary
   `imp_prog`, keyed on `pp x ivl list` exactly as sketched below, same
   `solve_dom`/`solve_c` convention as `analyse_interval_td_raw`. The
   soundness chain reuses G2's generic `admiss_exact`/`ctx_key` theorems
   directly: `entry_state_enterc` recovers the routed value from the
   caller's own solved state via a new compiler invariant,
   `compile_prog_calls_source_unique` (`VIMP_Proc_to_CFG.thy`) -- no CFG
   node produced by `compile_prog` has two distinct outgoing call edges --
   which lets `call_action_at_call_site`/`call_action_at_call_site_eq`
   (`Routed_Context.thy`) resolve the one call at a node unconditionally,
   for any program, not just the acceptance example's one call site.
   Keystone: `entry_state_activation_collect_sound`.
4. **G4 -- context-aware checks/reporting. Done, batch-green (2026-08-11).**
   Not a bespoke combinator: `check_result` is a real `semilattice_sup`
   instance (`Abstract_Checks.thy`) -- `Check_Unknown` top, `Proved`/
   `Refuted` incomparable -- so aggregation across every context a node's
   solver output covers is `Finite_Set.fold1`/`Sup_fin` over that lattice,
   proved associative/commutative/idempotent by the typeclass laws, not a
   hand-rolled "all Proved -> PROVED, all Refuted -> REFUTED" reduction.
   `classify_checks_ctx`/`classify_checks_verdicts` (`Abstract_Checks.thy`)
   read a solved `analysis_result` rather than a solver state, and enumerate
   covered contexts via `contexts_at` over the solver's own already-finite
   key set, never a raw comprehension (`ivl list` has no `enum` instance --
   its only order is the non-total abstract-domain lattice). Deadness is a
   fourth verdict, `contextual_verdict`'s `Dead`, not a `check_result`
   value: a context whose stored state concretizes to nothing is excluded
   from the join, and a check whose every covered context is dead reports
   `Dead` and is suppressed at the CLI, instead of classifying vacuously
   against `bot` and reporting a fabricated `Check_Proved`.
5. **G5 -- CLI exposure + precision witness. Done, batch-green
   (2026-08-11).** `--analysis interval --context entry-state` (default
   `--context none`, byte-identical to prior behavior --
   `analyse_ctx_none_eq_analyse` pins the equivalence); `--analysis sign
   --context entry-state` is a checked, explicit unsupported-combination
   error (exit 1), not a silent fallback. Regressions:
   `tests/regression/03-procedures/precision/04-two_call_sites_entry_state
   .vimp` is the precision witness (two calls at distinct exact argument
   values, `--context none` -> UNKNOWN per the known-imprecision sibling,
   `--context entry-state` -> PROVED);
   `tests/regression/03-procedures/soundness/01-entry_state_random_arg.vimp`
   is the random()-argument acceptance case (one wide context, terminates,
   UNKNOWN is the sound verdict, not a false PROVED). `context_mode`/
   `analyse_ctx` export through the same Haskell/OCaml `export_code`
   pipeline as `analyse` (`Analyse_Dispatch.thy`,
   `Example_State_Report_GraphViz.thy`), including the CI-only OCaml
   compile check (`Voblint_OCaml_Check.thy`). `--dot`/`--dot-full`/
   `--graph-snapshot` also support `--context entry-state`
   (`entry_state_report_dot_auto`/`entry_state_full_state_dot_auto` and
   their `_graph_snapshot_auto` siblings, `Example_State_Report_GraphViz
   .thy`): a rendered node can only carry one state, so a node reachable
   under several contexts renders the `Sup_fin` join of each context's
   reading through `ivl`'s own `semilattice_sup` -- the same aggregation
   principle as G4's check verdicts, this time over the domain lattice
   instead of `check_result`. This is a documented projection, not a
   per-context breakdown: genuinely duplicated clusters (one `square`
   cluster per context, mirroring the call-string K1/K2 examples' own
   hand-written context lists) would need an executable enumeration of
   the solver's own covered-context set, which isn't available for `ivl
   list` today -- `sorted_list_of_set` needs a `linorder` `ivl` doesn't
   and shouldn't have, `Finite_Set.fold (#) []` needs `ivl list ::
   finite`, which it structurally isn't (confirmed by a direct spike, not
   just reasoned about). Tracked as its own follow-up (#112), not worked
   around with an artificial order on `ivl`; the check/report layer is
   unaffected (it already preserves per-context precision internally).
   Regression: `tests/regression/13-full-state-dot
   /02-entry_state_context_join.vimp` shows the join directly (`n=[3,4]`
   inside the shared callee, joining `[3,3]`/`[4,4]` from the two call
   sites, while the caller's own checks stay context-separated and
   PROVED); `tests/regression/11-graph-snapshot
   /03-two_call_sites_entry_state.vimp` is the DOT-free sibling.

Arbitrary `gs`/`--flow-insensitive` stays explicitly out of scope -- see
#66's M4 / `docs/SEIDL_CONTEXT_LIFECYCLE_MIGRATION.md`; `declared_global p`
stays invariant across whatever this lands as.

6. **G6 -- #77 scoping audit and call-string finiteness. Done, batch-green
   (2026-08-21).** #77 ("Context-bounding lifters: Context Gas / Loopfree
   Callstring / Context Widening") asks to make context-space bounding "a
   first-class, terminating mechanism instead of relying on the ambient
   finiteness assumption," but the issue itself flags that it isn't yet
   actionable ("missing grounding," "recommend scoping this the way #66 is
   scoped... before starting"). This entry is that scoping pass, done
   directly against current source rather than the issue's own now-stale
   premise (`'c::finite` is not a sort constraint anywhere in
   `routed_context`/`dg_ctx_activation`/the TD solver interface -- see G1's
   finiteness-dependency note above, still true).

   The routed-domain migration (`docs/PROOF_PHASES.md`) put both context
   instances behind one architecture, so auditing them together settles
   which one #77 is actually about:

   - **Call-string contexts are already fully bounded, and now provably
     so.** `cs_route k` truncates every context to length `<= k`
     (`cs_route_length`, pre-existing); a compiled program's CFG has
     finitely many nodes (`cfg_nodes_finite`, new, `CFG_Def.thy`); combined
     with the standard library's own `finite_lists_length_le`, the entire
     call-string-keyed context space any `k`-bounded call-string routing
     over a compiled program could ever produce is finite --
     `compiled_call_strings_finite`/`compiled_call_string_vars_finite`/
     `compiled_call_string_gk_finite` (new, `Call_String_Context_Finite
     .thy`, Core). This is a genuine strengthening over the `solve_dom`
     contract every routed instance otherwise relies on (a per-run,
     empirical termination check): finiteness holds for the whole context
     space before any solve is attempted, for every domain that
     instantiates `call_string_routed_context` alike, not just the one a
     particular run happens to explore. Empirical companion:
     `tests/regression/17-call-string/known-imprecision
     /01-deep_recursion_bounded_context.vimp` runs a self-recursive
     procedure 50 levels deep under `--context-depth 1` and completes
     immediately -- one context per recursion level never materializes,
     confirming the finiteness bound is not merely a paper fact.
   - **Entry-state contexts are the genuinely open half, and #77's "gas /
     widening" language is about them, not call-strings.** An entry-state
     context is a domain value (`ivl list`, `sign list`, ...), not a
     bounded-length list over a finite alphabet; for an infinite-height
     domain such as `ivl` the context space is genuinely unbounded, and
     today's contract is the same empirical `solve_dom` guarantee the flat
     (`Ctx_None`) analysis already ships with (G1's finiteness-dependency
     note above). That is a deliberate, already-accepted design choice, not
     a bug -- but it is exactly what #77 would need to change to be
     "first-class" there.

   **What's still missing before entry-state bounding is actionable:** a
   concrete policy decision with real, user-visible precision consequences
   that nothing in the codebase or #77 specifies -- e.g., a gas budget that
   widens overflow entries into one shared per-callee context, versus a
   loop-detecting variant, versus something else, and in either case what
   the routed seed-key type and the `admiss`/`ctx_key` instance
   (`docs/NEXT_STEPS.md` G2, `LTR_Abstract.thy`) look like for a
   non-deterministic bounding relation. G2's `admiss` generalization
   already covers this abstractly (any sound relation works, not just
   `admiss_exact`), so no new Core soundness machinery is anticipated to be
   needed -- only the concrete policy choice and its own instance. Do not
   start implementation here without first picking one policy and writing
   it up the way M1-M4/G1-G5 above are written up; reading Erhard,
   Schinabeck, Schwarz, Seidl, "Context gas and friends: taming
   context-sensitivity on the fly" first (the issue's own cited source) is
   worthwhile before choosing.

## D/G communication

Improve analysis-defined shared-state reads and publications where a concrete
precision example requires it. Preserve the generic separation between local
`D` facts and shared `G` facts.

## Placement-aware D/G generation (settled, no further action planned)

`sound_dg_spec` is a proved `sublocale` of `sound_dg_hooks`
(`DG_Soundness.thy`, `DG_LTR_Sound.thy`): one implementation, two abstraction
levels. `sound_dg_spec` is the concise adapter every ordinary analysis
interprets (one locale interpretation, no per-CFG-node proof burden);
`sound_dg_hooks` is the framework-construction API for analyses whose D/G
structure needs arbitrary hook trees, such as owner-sensitive placement.
Sign, Interval, Parity, Mixed, CallString, and Ctx all stay on
`sound_dg_spec`/`dg_ctx_activation`/`routed_context`; two examples,
`Example_Interval_Placement.thy` and `Example_Sign_Placement.thy`, exercise
`sound_dg_hooks` directly as framework validation, not as templates.

This closes a prior migration attempt: two flagships
(`Exec_Sign_DG_Run.thy`, `Example_Parity_DG_Flagship.thy`) were migrated onto
`sound_dg_hooks` directly on the mistaken premise that `sound_dg_spec` was a
duplicate implementation. Both grew 5-6x for no closed soundness/drift risk
(`docs/reviews/M4_SPINE_BOUNDARY_AUDIT.md`) and were reverted. No further
example migration to `sound_dg_hooks` is planned; do not propose one without
new evidence that a specific analysis's D/G structure genuinely needs the
hook-tree level `sound_dg_spec` cannot express.

## Domain composition

No generic reduced-product constructor is planned. `sound_dg_spec`'s carriers
are already opaque, and `Rel_Order_Domain.thy` demonstrates a non-`abs_state`
instance against the unmodified framework; see
`docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md` (Option 4) for the settled
architecture. New heterogeneous or relational analyses are added directly
against `sound_dg_spec`, not through a shared product/reduction layer.

## Cross-analysis query composition

Not yet modeled: Goblint's MCP-style `EvalInt` query channel, where every
activated analysis can answer an expression query and a requester meets the
answers, recursively into subexpressions and callee-side `combine`. Voblint's
composite `int_dom` only reduces internally among its own scalar components.
Design investigation tracked in #70; alignment inventory and staging (Phase 3)
in #141.

## Numeric precision

Improve interval guards, loop invariants, and widening policies through concrete
examples. Keep precision engineering independent of the concrete semantic
reference model.

## Equality backward narrowing (done)

`inv_eq`, analogous to `inv_less`, is a `backward_domain` operator alongside
`inv_less`/`inv_plus`/`inv_minus`/`inv_times` (`Abstract_Domain.thy`).
`bfilter`'s `Eq` case narrows through it on both branches, not only the true
branch. Sign has a real, monotone instance (`inv_eq_sign`,
`Sign_Backward.thy`); Interval keeps a sound identity fallback with the
precision gap documented in-theory (`Interval_Backward.thy`). This is
separate from the boolean `eq_true`/`eq_false` query interface used for check
classification (`Abstract_Numeric_Queries.thy`).

## Source extensions

Arrays and richer types require syntax, operational semantics, compiler,
transfer, and soundness extensions. Add them as explicit vertical slices.

## Release gate

Keep live comments timeless, maintain a zero `sorry` inventory, and run the
complete batch build before merging proof changes.
