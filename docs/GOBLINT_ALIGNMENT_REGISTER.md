# Goblint Alignment Register

Status: **living audit.** This is the canonical long-term record of where the
formalization differs from upstream Goblint, why the difference exists, and what
would close it. It is an architecture register, not a thesis backlog. Active
work remains in the linked migration plans and GitHub Project 8.

## Target and evidence

**Target.** Model the semantic and solver-facing parts of Goblint's analysis
framework closely enough that each deliberate simplification is explicit,
justified, and replaceable. Exact source-level reproduction of CIL, every
analysis, and every manager service is not implied by this target.

**Upstream baseline.** Goblint `analyzer` `master`, checked 2026-07-16 at
`8d32b6b3d8cc08c5455817895b3af6eb5b00c21a`. The directly checked source is
[`constraints.ml`](https://github.com/goblint/analyzer/blob/8d32b6b3d8cc08c5455817895b3af6eb5b00c21a/src/framework/constraints.ml):
`FromSpec` defines local unknowns as `(node, S.C.t)` and its normal-call path
uses `enter`, derives a callee context, seeds the callee entry, and combines
callee exits through `combine_env` and `combine_assign`.

Evidence labels:

| Label | Meaning |
| --- | --- |
| **source-checked** | Checked against the upstream baseline above. |
| **local-checked** | Checked against the named Isabelle source or migration document. |
| **inference** | Architectural conclusion from the checked facts; re-check before implementation. |

## Alignment snapshot

| Area | Current state | Difference from Goblint | Why it exists | Closure path | Status |
| --- | --- | --- | --- | --- | --- |
| Source language | Scalar, procedural IMP2; an AFP IMP2 bridge embeds scalars into constant arrays. | Goblint analyzes C/CIL programs, including memory, types, and library semantics. | A small executable language permits end-to-end collecting and compiler proofs; the AFP bridge anchors its concrete semantics. | Arrays, then a C/CIL front-end model only after a concrete proof target is selected. | Deliberate scope boundary. |
| CFG and collecting semantics | Verified interprocedural CFG, trace collecting semantics, explicit enter edges and combine triples. | Goblint consumes its C CFG and has framework-specific node/edge forms. | The CFG is the proof-level semantic interface; reproducing CIL CFG construction would dominate the current proof. | Specify a translation relation from a selected Goblint CFG fragment before claiming CFG fidelity. | Inference; no active migration. |
| Unknown space and contexts | One generalized D/G executable generator; monovariant = the `unit` instantiation. The routed interval instance computes exact per-context results (batch-green eval); the collecting-soundness certificate is the remaining proof. | Goblint's `FromSpec` local variable is `(node, S.C.t)` and selects context at calls. | The semantic layer was built before the executable route; the generic route seeds the callee entry dynamically. | Finish the soundness pipeline in `ROUTE_A7_EXECUTABLE_DG_MIGRATION.md` (bridge -> route lemma -> `activation_collect_sound` -> coverage -> interval theorem -> source lift). | Active; generator + routing done, certificate remaining. |
| Context input boundary | Context is selected from the post-enter callee state (`enterc c s'` on the entered store), matching `context man f callee_state`; argument-sensitive context is expressible. | Goblint's `Spec.context` receives a local `D.t`; global information is available through the manager/global channel, not by framework-level joining. | The prior caller-store / joined `side_env_cmp` read could not express argument context; routing on the entered callee state fixes it. | Certify the routed solution via `activation_collect_sound` + `point_digest` (ENTER_MONO); the manager/query channel remains a simplification. | Callee-state routing done (batch-green); soundness certificate remaining. |
| Call entry and return | IMP2 carries actuals and an optional destination through CFG metadata, but entry/reset and the abstract caller-local/callee-global merge are fixed. | Goblint's `enter` can return several caller/callee states; `combine_env` and `combine_assign` are analysis operations. | Fixed operations match the IMP2 concrete semantics and keep the first TD bridge small. | First-class analysis-driven call contract, then generator-driving `combine_env`/`combine_assign` with multi-result entry. | Basic source call/return implemented; analysis-defined contract missing. |
| Local/global payloads | One `'a abs_state = vname => 'a` serves local slots and named global slots. | Goblint distinguishes `D.t` local and `G.t` global lattices. | The vendored TD bridge and current Sign/Interval instances use one payload type. | Split state/tree/transfer payloads and re-state gamma over the two components. | High-cost stretch. |
| Relational state | Pointwise abstract states. | Goblint analyses may use opaque relational local states; product maps cannot represent cross-variable constraints faithfully. | Pointwise Sign and Interval make executable transfer and gamma proofs direct. | Abstract-state interface with sound projection/merge operations; prerequisite for an Octagon result. | Deferred. |
| Named globals and side effects | `QueryG`/`Side`, finite keys, and D/G routing are modeled. | Goblint has analysis-defined global variables and global payloads, with richer namespaces and update behavior. | The finite-key, common-payload form fits `TD_side` and current examples. | Combine this with payload separation and per-global update rules. | Partial alignment. |
| Update rules | Default TD-side update behavior only. | Goblint permits analysis-specific update/widening policies, including origin-sensitive behavior. | Solver interface was kept close to vendored TD. | Parameterize update policy and prove its solver obligations; begin with one origin-sensitive witness. | Open. |
| Multi-analysis manager | One analysis stack; no manager, `ask`, `emit`, thread, or event protocol. | Goblint composes analyses and exposes inter-analysis queries through the manager. | Whole-framework composition is outside the single-analysis soundness thesis. | Product local domains, sum global namespaces, query-answer contracts, then a minimal two-analysis example. | Explicitly out of current scope. |
| Termination and context bounding | Soundness assumes `solve_dom`; contexts are statically finite in current executable instances. | Goblint uses widening and context lifters to control discovered contexts. | `TD_side` is vendored for partial correctness; proving its termination is separate work. | M3a finite-height Sign termination; M1 plus M3b call-string lifter; general widening requires upstream solver work. | Open, partly upstream-gated. |

## Call flow and context selection (source-checked, 2026-07-16)

Goblint models a normal call as **split -> analyze -> combine** over contextual
unknowns, not a concrete push/run/pop. From
[`analyses.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/analyses.ml)
and
[`constraints.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/constraints.ml):

1. `enter man lv f args : (D.t * D.t) list` -> pairs `(caller continuation, callee
   entry state)`; the callee entry has the actuals bound to formals. `enter` is
   analysis-defined and may return several pairs.
2. Context is selected from the **post-enter callee state**:
   `List.map (fun (c, callee) -> (c, S.context man f callee, callee)) paths`.
   So `context man f callee_state` reads the callee-entry state, not the caller.
3. The callee entry is published: `sidel (FunctionEntry f, fc) callee_state`; local
   unknowns are indexed `node x context`.
4. `return man (Some e) f` produces the callee return state; the synthetic return
   slot is an analysis representation detail (the generic framework only requires
   `return`, it does not mandate a universal `#ret`).
5. The exit is read for the selected context: `getl (Function f, fc)`.
6. Combination is two phases: `combine_env caller callee_return` (globals / effects,
   no result assignment), then `combine_assign lv callee_return` (only the
   destination write).

### What the formalization implements (this repo)

| Goblint | Formalization | Status |
| --- | --- | --- |
| `enter` -> callee entry with bound formals | `EA_Enter formals actuals` / `edge_step` (`bind_formals` over `enter_state`) | done |
| `context man f callee_state` (post-enter callee state) | `enterc c s'` on the entered store `s'` (`trace_witness_act.enter`) | done, **batch-green** |
| local unknown `(node, context)` | `Inl (pp, ctx)` | done |
| `sidel (FunctionEntry f, fc) callee_state` | seed slot `Inr (Seed callee_entry ctx)`, published by the routed enter `Side` | done, batch-green (interval example) |
| `getl (Function f, fc)` | routed callee-exit read `Inl (ex, route ...)` in the combine | done, batch-green |
| `combine_env` then `combine_assign` | `combine_collect dst s t = combine_assign dst (t ret_var) (combine_states s t)` (`combine_states <s | t>` = env: caller locals + callee globals; `combine_assign dst` = destination write) | done |

The load-bearing correction this session: **context is now selected from the
callee-entry abstract state after parameter binding** (`enterc c s'`), matching
`context man f callee_state`. The prior model routed on the caller store, which
cannot express argument-sensitive context. See
`ROUTE_A7_EXECUTABLE_DG_MIGRATION.md` (architectural finding + minimal fix).

### Claim discipline

Accurate: *a simplified, machine-checked semantic model of Goblint's
interprocedural context-sensitive architecture.* Not: *the exact implementation.*
Known simplifications (future faithfulness, not blockers): `enter` is a single
language-level formal-binding transfer, not an analysis-controlled `(D.t * D.t)
list` (no multi-path split / nondeterminism); the context selector sees the caller
context and entered store, not a full manager/query interface; `D.t` is a store,
not a product of relational / heap / thread / path-sensitive domains; `combine_env`
/ `combine_assign` are composed in one `combine_collect`, not exposed as two
analysis-overridable hooks.

## Boundary examples

These are capability boundaries, not claims that every Goblint configuration
proves every assertion. “Goblint-side” means an analysis instance with the
required domain or cooperating analyses can express and run the scenario. The
formalization-side column states the exact missing layer.

| Scenario | Goblint-side example | Formalization-side boundary | Required closure |
| --- | --- | --- | --- |
| C memory and aliases | `int a[2]; int *p = c ? &a[0] : &a[1]; *p = 0;` A C analysis can model the pointer, array cells, and weak update. | IMP2 has scalar stores only. There are no arrays, addresses, dereference, allocation, or alias semantics to state a matching collecting theorem. | `ARRAY_SYNTAX_EXTENSION.md` for arrays; the source-language boundary in `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` for memory/CIL. |
| Relational numeric invariant | `int x = input(); int y = x; x++; assert(x == y + 1);` A relational numeric domain can retain the relation between `x` and `y`. | The current state is pointwise. Sign/Interval can track each variable but cannot express `x - y = 1`; `input()`/havoc is also only planned. | `RELATIONAL_DOMAIN_PLAN.md` plus `NONDET_HAVOC_MIGRATION.md`. |
| Analysis-specific call behavior | `r = f(p);` where the analysis must preserve a relation between caller state, pointer argument, and returned value. Goblint supplies the call syntax to `enter`, `combine_env`, and `combine_assign`. | IMP2 can formalize ordinary actuals and return destinations, but the generic abstract merge is fixed; an analysis cannot provide its own call-sensitive callback contract. | Gap 3 in `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`. |
| Inter-analysis query | A taint transfer asks a value/pointer analysis whether a sink or dereference is feasible before reporting it. | `QueryG` reads this analysis's named global slots only. There is no manager, query type, answer lattice, or product of active analyses. | Gap 7a in `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`; Seidl Slice 8. |
| Origin-sensitive global update | Several loop or call-site origins side-effect the same global; a per-origin update policy can widen one contribution without immediately losing the others. | `Origin_Lift` gives executable per-origin cells, but the side-effect/dependency half of its `part_post_solution` soundness transport is unfinished. | P11 in `OPEN_PROBLEMS.md`, then Seidl Slice 7 solver integration. |
| Recursive context bounding | `int f(int n) { return n ? f(n - 1) : 0; }` analyzed with Context Gas or Loopfree Callstring. | Recursive IMP2 behavior is expressible, but the executable proof uses a statically finite context type and assumes solver termination. It cannot certify a dynamically bounded context lifter. | `M1_CALLSTRING_CONTEXT_MIGRATION.md` and M3b; M3a separately removes the Sign termination hypothesis. |

### Already expressible here

The contrast is not “C versus nothing.” Current IMP2 already formalizes and
certifies scalar assignments, conditionals, loops, procedures with actuals and
optional return destinations, named global side effects, and fixed structural
call/return restoration. It also has semantic context-indexed collecting
soundness. The examples above begin where those capabilities require a richer
source language, a non-pointwise state, an analysis-provided framework hook, or
a termination argument.

## Current migration map

Only migrations with an open or in-progress status are listed. A migration may
advance the target without closing an entire register row.

| Migration | Register rows | Audit reading |
| --- | --- | --- |
| `ROUTE_A7_EXECUTABLE_DG_MIGRATION.md` | Unknown space and contexts | Highest-priority executable fidelity step: it gives the D/G semantic context model a single solver generator. |
| `M1_CALLSTRING_CONTEXT_MIGRATION.md` | Unknown space and contexts | Adds a computed textbook context; it is breadth, not a repair of the semantic model. |
| `M3_CONTEXT_BOUNDING_TERMINATION_MIGRATION.md` | Termination and context bounding | M3a strengthens the theorem; M3b models a real lifter; M3c is upstream-gated. |
| `M2_DGC_RREAD_BOUNDARY_MIGRATION.md` | Context input boundary | The transport toolkit is landed; the remaining value-keyed `ENTER_MONO` closure is refuted for the current retain route. |
| `CONTEXT_SENSITIVE_GLOBALS_MIGRATION.md` | Contexts, named globals | Umbrella status document; defer to Route A7/M2 for executable boundary details. |
| `DIGEST_GENERATOR_COLLECTING_DISCHARGE_MIGRATION.md` | Context input boundary | The superset-reader class is closed; tight point-dependent readers still need a direct argument. |
| `SEIDL_2026_GOBLINT_ALIGNMENT_MIGRATION.md` | Payloads, combine, updates, manager | Best framework-level comparison, but its implementation claims must stay subordinate to this register's evidence labels. |
| `TRACE_BASED_FORK_MIGRATION.md` | Contexts | Track A only; complements M1. |
| `GHOST_INSTRUMENTATION_MIGRATION.md` | Validation only | Useful executable observability, not a Goblint framework-alignment closure. |
| `NONDET_HAVOC_MIGRATION.md` | Source language | Improves semantic breadth; it does not reduce the C/CIL gap. |

## Rules for future alignment work

- State the upstream interface fragment and commit before calling a design
  Goblint-faithful.
- State whether a result is semantic-only, executable-generator, or end-to-end.
- Add a register row or update an existing row whenever a simplification becomes
  load-bearing in a theorem statement.
- Record the rationale as a constraint, not history: proof cost, vendored solver
  interface, source-language scope, or a required concrete semantics.
- Do not call `(node, context)` alignment complete while the executable generator
  cannot derive and seed the selected callee context. (As of 2026-07-16 the
  generator *does* derive and seed the callee context from the post-enter callee
  state, batch-green; what remains for "complete" is the collecting-soundness
  certificate for the routed solution, not the routing mechanism.)

## Superseded inventories

`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` remains useful for the original detailed
design sketches. Its Gap 7 statement that contexts are absent is stale: semantic
context collection and context-indexed unknowns now exist. Read its Gap 7 through
the status in this register and `GOBLINT_ALIGNMENT_TRACKS.md`.
