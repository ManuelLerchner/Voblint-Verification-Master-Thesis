# Post-deletion cleanup queue (P3-P12)

Picked up automatically once Slice C/D (obsolete TD/etf spine deletion) is
complete and the full gates are green. Remeasure before acting: the audit
counts below predate the deletion.

## 0. Re-audit the post-deletion tree first

Recount theories and `.thy` LOC; recompute the imports/session DAG, dead
definitions and normalized duplicate families; recheck `Exec_DG_Bridge`, the
domain x context matrix and the `code_identifier` map. Record a post-deletion
baseline, then continue without pausing.

## P3 - Finish the `Exec_DG_Bridge` migration

`Exec_DG_Bridge.thy` (~4.9k lines) carries two parallel transport families:
per-tree traversal commutation, bundled transport relation,
classifier-parametric fold transport, generator tree-list transport,
equation-system transport, post-solution transport, monovariant
specialization. Identify the carrier-generic canonical family, delete the
superseded one outright (no abstraction that keeps both), redirect consumers.
Then split by responsibility if the dependency structure justifies it, roughly
`Core/Exec/Exec_DG_Refines`, `_Trees`, `_Generator`, `_Monovariant`.

Gate: no duplicate family; all consumers on the carrier-generic one; no
theorem lost to renaming; I/Q clean; build and regressions green; own commit.

## P4 - Collapse the domain x context clone matrix

Audit measured 76-98% structural identity across Sign/Interval/Int/Parity
context-soundness files, including ~14 copies of the ~85-line `*_pp_abs`
proof. `Routed_Unit_Domain.pp_abs` already looks like the generic version and
is underused.

Reconstruct the surviving matrix, separate genuinely domain-specific content
from cloned plumbing, and build one canonical generic locale parameterized
only over what varies: dg_spec/executable spec, initial local/global state,
route/context policy, classifier/report projection, global predicate where
needed. Reuse the existing generic locales rather than adding a layer beside
them. Genericize `pp_abs`, the node-soundness bridge, result-table
construction, post-solution/result lookup, and report construction where
structurally identical.

Migrate one simple pair first (Sign vs Parity at `Ctx_None`), pin behaviour,
then the rest. Each `(domain, context)` file should end up as spec
instantiation + context-policy instantiation + a few domain-specific
commute/classifier facts + public aliases.

Gate: re-run normalized similarity; the 0.9+ clone families must be gone, not
renamed. Public `analyse*` behaviour preserved. Own commit.

## P5 - Rehome generic D/G framework into Core

Anything under `Analysis/Instances/*` or `Formalization/` that is parameterized
over carriers/specs and not tied to a concrete domain belongs in `Core`.
Candidates: surviving `Exec_DG_*`, `DG_Base_Exec`,
`Monovariant_Analysis_Result`, `Routed_Unit_Domain`, the generic
context/result pipeline. Real moves into `Core/Exec/` and `Core/Pipeline/`,
not wrapper theories.

Invariant to verify mechanically: Core imports no domain-specific Analysis
theory. Own commit.

## P6 - Normalize the source/session layout

Only after P4/P5. `Formalization` is not an endpoint session: most of it is
domain x context executable instantiation used by CLI/codegen. Normalize
toward `Core/{Domain,Equations,Exec,Solver,Pipeline}`, per-domain directories
with a `Ctx/` subdirectory, `Soundness/`, `CLI/{Entry,Report}`, `Export/`,
`Examples/`. Pick one naming convention for the context-matrix role, which
currently appears as `*_Exec_Ctx_Sound`, `*_Ctx_None_Routed_Sound`,
`*_Entry_State_Ctx_Sound`, `*_Call_String_Ctx_Sound`. Rename `CLI/Codegen/*`,
which holds analysis entry/soundness bridges rather than the `export_code`
layer. Update ROOT, ROOTS, imports, docs and the module map atomically.

## P7 - Complete #143 with a relational custom-combine witness

Do this before broad API cleanup so the canonical architecture gets a
relational stress test. Leave the deliberately-imprecise `relc` instance
alone. Build a new relational `dg_spec` over a carrier whose relation set
holds facts `(x, y)` meaning `x <= y`.

`caller_cont ci dc ...` drops only relations mentioning variables the callee
may modify; derive a conservative may-write summary from the VIMP
procedure/CFG via `ci_callee`, or take an explicit conservative per-procedure
summary parameter documented as the analogue of Goblint's query-side
information. `combine_env` must use both operands: surviving caller relations
met with caller-visible callee-exit relations, restricted to variables whose
meaning survives in the caller. `combine_assign` stays the second phase.

Regression: a program where `x <= y` survives from the caller (callee touches
neither) while `g <= h` comes from the callee exit; prove both hold after
return, and compare against a havoc/structural implementation that recovers
only one. It must run through the canonical D/G generator and solver, not by
evaluating the combine directly. Prove `sound_dg_spec` for the instance. Close
#143 when it passes. Own commit.

## P8 - Generate the `code_identifier` module map

The hand-maintained OCaml remap has already caused a real module-dependency
cycle. Derive the mapping from the actual export closure: deterministic,
stably ordered, generated artifact checked in, CI/lint failing when stale, and
a new exported dependency never silently emitting an unexpected module. Remap
the export closure only, not every theory in the repository. Verify the
generated `Voblint_CLI.ml` module structure and the absence of cycles.

## P9 - Dead-code sweep

Re-run after the refactors. Investigate rather than blindly delete:
`Rel_Order_Domain`, the `Int_Backward` never/once/fixpoint families, unused
`analyse_*_ctx_result` variants, `Interval_Point_Digest`,
`Call_String_Collecting_Refinement`, `Call_String_Context_Finite`, unused
GraphViz helpers. Classify each as dead implementation (delete), useful but
unreferenced theorem (retain/document/integrate), regression or history only
(move to Examples/docs), or public API compatibility (deliberate call).
Re-run reachability after each tranche; commit coherent groups.

## P10 - Simplify the API name cross-product

Only now look at `_for`, `_lifted`, `_placed`, `_buffered`, `_st`, `_ctx`,
`_per_origin`, `_warrow`. For each axis decide whether it is a runtime/config
parameter, a type-level representation distinction, a proof specialization
worth keeping, or obsolete migration scaffolding. Prefer `analysis_config`,
`solver_mode`, `context_policy` and generic locale parameters where they
genuinely replace orthogonal named families; keep separate constants where
that makes theorem statements clearer. Do not optimize for constant count, and
do not change stable public CLI behaviour unnecessarily.

## P11 - Examples and witness organization

After the semantic refactors: runnable/regression material primarily under
`Examples`; domain example structure mirroring domain source structure where
useful; normalize `Ivl_Exec` to `Interval_*` if low risk; stray `*Regression*`
files into regression subfolders. Leave small `by eval` sanity facts in core
theories where they serve as local executable lemmas. Avoid churn for its own
sake.

## P12 - Docs and hygiene

Archive completed `*_MIGRATION.md`, `*_HANDOFF.md` and superseded audits under
`docs/history/`, keeping live architecture and decision docs in place. Fix
CLAUDE.md's dependency chain. Remove stale staged-migration comments. Remove
`*.thy~` and editor autosaves, empty directories and `__pycache__`; extend
`.gitignore` for untracked OCaml build outputs; do not commit generated HTML
or fonts.

## Verification and commit discipline

I/Q diagnostics with a forced recheck for incremental work, plus the
structural host sweep that catches a malformed or missing final `end`. Session
build per major commit; full gates per architectural phase (`build`,
`codegen-check`, `git diff --exit-code -- codegen/generated/`,
`codegen-regression`, `cli-test`, `cli-smoke`, `lint`, `regression-lint`).
Record the Apple-Silicon Isabelle/opam OCaml mismatch exactly rather than
attributing unrelated failures to it. Stage explicit paths only; never
`git add -A`. One coherent commit per phase.

## Stop conditions

Continue through proof failures, import fallout, mechanical cascades, rename
churn, stale diagnostics and codegen regeneration. Stop only if a cleanup
would remove a capability with no canonical replacement and a real design
choice is required; if remeasurement shows the audit premise is materially
false and continuing would mean choosing a new architecture; or if concurrent
worktree modifications create a data-loss risk.

## Final questions

1. Does Voblint have exactly one interprocedural analysis spine?
2. Is there exactly one generic domain x context soundness pipeline?
3. Does the generated CLI traverse that canonical architecture?
4. Can a genuinely relational analysis provide a sound custom caller
   continuation and combine without modifying generic infrastructure?

All four must be demonstrably yes.
