# Next work

GitHub Project 8 contains scheduling and dependencies. The stable technical
directions are:

## Context abstractions

Entry-state and call-string contexts are done for every analysis `run_voblint`
activates, from the collecting semantics to the CLI:

- **Semantics.** A context policy admits the contexts of one concrete call,
  `gactivation_context_rel` threads them over traces, and `activation_collect` is indexed
  by them (`Activation_Trace_Context`). A functional policy embeds through
  `context_policy_of_fun`.
- **Routing.** `grouted_context` (`Routed_Context`) discharges the call
  and combine obligations once for any context type `'c`; the `gdg_analysis`
  registrations `mcp_cs` and `mcp_es` (`MCP.thy`) instantiate it with call
  strings and entry states. `'c` carries no `finite` sort constraint:
  termination is the per-run `solve_dom` premise, as for the flat analysis.
- **Endpoints.** `gdg_analysis.entry_state_activation_collect_sound` and
  `fun_route_activation_collect_sound` (`DG_Analysis.thy`) bound each bucket;
  `report_state_sound` and `report_check_sound` (`Run_Report.thy`) reach the
  report, and `run_voblint_source_sound` a source run.
- **Checks and rendering.** `classify_checks_verdicts` joins verdicts over the
  contexts the solved table covers (`table_contexts`), with `Dead` kept apart from
  the three check results; the graph draws one node per `(pp, ctx)` pair.
- **Regressions.** `tests/regression/03-procedures/precision/04-two_call_sites_entry_state.vimp`
  (precision), `tests/regression/03-procedures/soundness/01-entry_state_random_arg.vimp`
  (one wide context), `tests/regression/13-full-state-dot/02-entry_state_contexts.vimp`
  (one cluster per entry-state context).

A user-chosen set of flow-insensitive variables stays out of scope;
`is_global` (`VIMP_Semantics.thy`) is the classifier everywhere, and
`--program-globals flow-insensitive` applies to every declared global at once.

### Open: context bounding

- **Call strings have a bounded candidate space, which is less than bounded.**
  `cs_route k` truncates every context to length `<= k` (`cs_route_length`), a
  compiled program has finitely many nodes (`cfg_nodes_finite`), and with
  `finite_lists_length_le` the contexts a `k`-bounded routing over a compiled
  program could produce form a finite set --
  `compiled_call_strings_finite`/`compiled_call_string_vars_finite`/
  `compiled_call_string_gk_finite` (`Context_Space_Finite.thy`, `Voblint_Routing`).
  Containment of the node and context halves is a hypothesis of each of them,
  and truncation alone does not give the second. Nor do they bear on
  `solve_dom`: a finite key space does not make a solve terminate. Closing the
  gap means proving key closure under routing. Empirical companion:
  `tests/regression/17-call-string/known-imprecision/01-deep_recursion_bounded_context.vimp`
  (50 levels of recursion under `--context-depth 1`).
- **Entry-state contexts are unbounded.** An entry-state context is a domain
  value; for an infinite-height domain such as Interval the context space is
  unbounded, and the contract is the same `solve_dom`
  premise the flat analysis ships with. Bounding it needs a policy decision
  first -- a gas budget that widens overflow entries into one shared per-callee
  context, a loop-detecting variant, or something else -- and then that policy's
  `context_policy` instance. Erhard, Schinabeck, Schwarz, Seidl, "Context gas
  and friends: taming context-sensitivity on the fly" is the reference.

## D/G communication

Improve analysis-defined shared-state reads and publications where a concrete
precision example requires it. Preserve the generic separation between local
`D` facts and shared `G` facts.

## Placement-aware D/G generation (removed)

The hook-tree layer (`sound_dg_hooks`) and the placement examples built on it
were removed; `docs/GOBLINT_ALIGNMENT_REGISTER.md` records why. No further
action is planned.

## Domain composition

No generic reduced-product constructor is planned. `ganalysis_contract`'s carriers
are opaque, and `Order_Analysis.thy` runs a relational domain over variable
identities against the unmodified framework; see
`docs/RELATIONAL_DOMAIN_ARCHITECTURE_DECISION.md` (Option 4) for the settled
architecture. The one reduced product, `int_tuple` (`Int_Tuple_Kind.thy`), pairs
Interval and Congruence as Goblint's `IntDomTuple` does.

## Cross-analysis query composition (done)

Activated analyses run as one through `mcp_registry` (`MCP_Registry.thy`) and
answer each other's `EvalInt` queries; `docs/COOPERATING_ANALYSES_DESIGN.md`
records the design.

## Soundness in the domain interface (done)

A non-relational domain is an instance of the type class `kind_int_domain`
(`Nonrelational_Domain.thy`), whose assumptions state soundness and the bounds of
widening and narrowing; none asks for monotonicity. Sign,
Interval, Parity, Congruence and `int_tuple` at each refinement mode
instantiate it.

## Numeric precision

Improve interval guards, loop invariants, and widening policies through concrete
examples. Keep precision engineering independent of the concrete semantic
reference model.

## Backward narrowing of guards (done)

A guard narrows both operands of a comparison through the domain's `refine_ik`
(`kind_int_domain`, `Nonrelational_Domain.thy`), after `inv_bin_int` in Goblint's
`baseInvariant.ml`. The value-level operators `inv_eq`, `inv_less`, `inv_plus`,
`inv_minus` and `inv_times` (`Backward_Domain.thy`) remain in the domain
libraries; Sign's `inv_eq_sign` is in `Sign_Backward.thy`. Check classification
uses the separate `eq_true`/`eq_false` query interface (`Numeric_Queries.thy`).

## Per-domain configuration duplication (done)

No domain writes its configuration out by hand. Each analysis is one constructor
of `analysis` (`Analysis_Config.thy`); the registrations `mcp_cs`, `mcp_es`,
`mcp_split` and `mcp_split_es` (`MCP.thy`, `MCP_Split.thy`) supply the equation
system, solve, reader, result table and soundness endpoints for all of them.

## Deferred from the Framework and Analysis restructure

Each of these was found with evidence during the restructure and deliberately
not acted on, either because it needs a semantic decision or because it belongs
to a larger migration.

**Dictionary ownership.** Variables are identities (`var_id`, `Var_Id.thy`), and
`is_global` reads the identity's constructor. The executable carrier still keeps
one default dictionary per partition, so it admits an entry for a variable in the
dictionary that does not own it. `st_rep_is_bot` (`Nonrelational_Exec.thy`)
consults `is_global` only to skip those entries: the quotient's equality observes
both dictionaries while the represented function reads each variable in only the
one that owns it.

**Names that still need a read before they are changed.** `State_Restriction`
holds only ownership projections, so `Ownership_Restriction` would be more
truthful. `DG_Ctx_Activation` abbreviates a
word its own directory already supplies.

**Refining the dictionary entries.** A `gdefault_dict`'s association list is a
candidate for an AFP `rbt` map. Benchmark the generated OCaml rather than
Isabelle evaluation.

## Source extensions

Arrays and richer types require syntax, operational semantics, compiler,
transfer, and soundness extensions. Add them as explicit vertical slices.

## Release gate

Keep live comments timeless, maintain a zero `sorry` inventory, and run the
complete batch build before merging proof changes.
