# Post-deletion cleanup queue (P3-P12)

Picked up once Slice C/D (obsolete TD/etf spine deletion) is complete and the
full gates are green. Section 0 below is the measured post-deletion baseline;
every count in P3-P12 is stated against it.

## 0. Where this stands

Measured after the TD/etf deletion and the consolidation that followed.

| metric | pre-deletion | after deletion | now |
| --- | --- | --- | --- |
| `src` theories | 227 | 212 | 212 |
| `src` `.thy` lines | ~96k | 85.8k | 83.8k |
| `analyse_*` constants | 134 | 128 | 128 |
| suffix families with >=4 variants | 19 | 9 | 9 |
| `docs/` markdown files (live) | 142 | 142 | 70 |
| staged-migration phrases in `.thy` | many | 9 | 0 |

Session graph, and why `Formalization` is not a leaf, are in the project
contract; `ROOTS` lists eight directories and omits `src/CodegenCheck`
deliberately.

### Done

- **P3** Exec_DG_Bridge's duplicate transport family. The carrier-generic
  engine now proves the raw readback's post-solution transport too, as it
  already did the lifted one; the eleven private `_for` support lemmas and the
  unadopted exec-side lifted spec island are gone. 4885 -> 4234 lines.
- **P4** the domain x context clone matrix. `routed_unit_domain_exec` became
  `routed_domain_exec` by taking the routing functions and their agreement as
  parameters, which is the only thing the eleven copies differed in. All
  eleven post-solution transports -- Sign, Parity, Interval x3, Int x3 at the
  unit context, Sign/Int/Interval at entry-state, Sign/Int at call-string --
  are now that one derivation instantiated. About 1200 lines.
- **P12, in part** `docs/history/` separates 70 completed migration notes,
  handoffs, audits and plans from the 70 live documents; the theory comments
  no longer describe themselves as staged ahead of a migration; the session
  graph in the project contract is correct; editor debris is gone.

### Blocked on one build

`P5` and `P6` move theories between sessions, and `P8` changes what
`export_code` emits. None can be verified interactively: I/Q checks a theory
against the session heaps it already has, so a cross-session move or an export
change is only real once the batch build and `codegen-check` agree. Run those
two gates before starting either.

## P3 - Split `Exec_DG_Bridge`

What is left of P3 is the split, not the deletion. At 4234 lines the file still
holds four responsibilities: the refinement relation and basic transport, the
per-tree and fold commutation, the equation-system and post-solution transport,
and the monovariant specialisation. Split it along those lines when it moves to
Core (P5), not before -- doing both at once keeps the import churn to one pass.

## P5 - Rehome generic D/G framework into Core

Done. The four domain-generic theories that lived in
`Analysis/Instances/Product/` by accident now sit in `Core/Solver/Context/DG/`,
next to the abstract framework they mirror:

```text
Exec_DG_Bridge               carrier-generic executable/abstract transport
DG_Base_Exec                 executable mirror of Core's DG_Base
Routed_Domain_Exec           the routing layer, renamed with the locale
Monovariant_Analysis_Result  one executable AnalysisResult constructor
```

What remains of the directory is the `Int_*` product domain (Sign x Interval),
which is the only thing the name `Mixed` describes, plus `Rel_Order_Domain`, a
relational instance that belongs with the domains. Both are P6's problem.

Invariant now enforced by the build: Core imports no Analysis theory, because
Core is built before Analysis exists.

## P6 - Normalize the source/session layout

Only after P4/P5. `Formalization` is not an endpoint session: most of it is
domain x context executable instantiation used by CLI/codegen. Normalize
toward `Core/{Domain,Equations,Exec,Solver,Pipeline}`, per-domain directories
with a `Ctx/` subdirectory, `Soundness/`, `CLI/{Entry,Report}`, `Export/`,
`Examples/`. Pick one naming convention for the context-matrix role, which
currently appears as `*_Exec_Ctx_Sound`, `*_Ctx_None_Routed_Sound`,
`*_Entry_State_Ctx_Sound`, `*_Call_String_Ctx_Sound`. Rename `CLI/Entry/*`,
which holds analysis entry/soundness bridges rather than the `export_code`
layer. Update ROOT, ROOTS, imports, docs and the module map atomically.

## P7 - A relational custom-combine stress test

Not a prerequisite for #143, which this branch closes. This is the relational
follow-on tracked by #25: put the canonical architecture under a domain whose
combine genuinely needs both operands.

`Examples/Mixed/Example_Relational_DG_Demo.thy` (202 lines) already exercises
`Rel_Order_Domain` through the routed spine, so the starting point exists.
Build a relational `dg_spec` over a carrier whose relation set holds facts
`(x, y)` meaning `x <= y`.

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
evaluating the combine directly. Prove `sound_dg_spec` for the instance. Own
commit.

## P8 - Generate the `code_identifier` module map

`CLI/Analyse_Dispatch.thy` carries 119 hand-written `code_module` entries and
nineteen theories still escape them, emitting their own OCaml module:

```text
Analysis_Config  Analysis_GraphViz  Call_String_Context  State_Report_GraphViz
Congruence_Print  Interval_Print  Parity_Print  Sign_Print  Int_Print
Parity_Exec  Parity_Checks  Parity_Numeric_Queries  Parity_Ctx_None_Sound
Sign_Ctx_Call_String_Sound  Sign_Ctx_Entry_State_Sound
Int_Ctx_Call_String_Sound   Int_Ctx_Entry_State_Sound
Interval_Ctx_Call_String_Sound
```

The split is unprincipled: `Sign_Ctx_None_Sound` is remapped,
`Sign_Ctx_Call_String_Sound` is not. Each unmapped theory is a latent module
dependency cycle waiting on the next edit.

Derive the mapping from the actual export closure: deterministic, stably
ordered, generated artifact checked in, CI/lint failing when stale, and a new
exported dependency never silently emitting an unexpected module. Remap the
export closure only, not every theory in the repository. Verify the generated
`Voblint_CLI.ml` module structure and the absence of cycles.

## P9 - Dead-code sweep

Re-run after the refactors; the current measurement is 296 constants defined,
never referenced outside their own theory, and absent from the generated
OCaml (excluding `Examples`, where file-local witness constants are expected).
Concentrations:

```text
26  Mixed/Exec_DG_Bridge.thy       expected to fall out of P3
22  Mixed/Rel_Order_Domain.thy     NOT dead - Example_Relational_DG_Demo uses it
21  Mixed/Int_Backward.thy         the never/once/fixpoint dispatch family
18  Tooling/Analysis_GraphViz.thy  unused report/cluster renderers
13  VIMP/VIMP_Notation.thy         mostly syntax scaffolding
```

Two theories in `Core/Solver/Context/DG/` build via `Core/ROOT` but nothing
imports them and nothing they prove is cited:
`Call_String_Collecting_Refinement.thy` (86) and `Call_String_Context_Finite.thy`
(76). The finiteness results look like a termination argument that was proved
and then bypassed; decide deliberately rather than deleting.

Classify each candidate as dead implementation (delete), useful but
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

`docs/` holds 142 markdown files and 49.6k lines. Of those, 69 files and 27.0k
lines are `*_MIGRATION.md` / `*_HANDOFF.md` / `*_AUDIT.md` / `*_PLAN.md`:
completed work-in-progress notes. Only `docs/architecture/history/` is
structured. Archive them under `docs/history/`, keeping live architecture and
decision docs in place. Fix CLAUDE.md's dependency chain, which still shows
`Formalization` as an endpoint (see section 0).

Current hygiene counts:

```text
105  untracked .thy~ jEdit backups under src/
  1  src/Analysis/ROOT~
  1  emacs autosave under src/Examples/Tooling/
  1  empty directory under src/
  0  sorry / oops
 84  metis + 4 smt call sites          batch-hang risk per CLAUDE.md
  6  staging/migration phrases in .thy comments
```

Remove the backups, autosaves and empty directories; extend `.gitignore` for
the untracked OCaml build outputs under `cli/` and `tests/property/`; do not
commit generated HTML or fonts. The six staging phrases are the `issue #123`
subsections in `Exec_DG_Bridge` and go with P3.

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
   Yes, as of Slice D: zero references to the TD/etf vocabulary remain in
   `src`, `vendor`, `codegen`, `cli` or `tests`, and the D/G import closure
   intersects the deleted set nowhere.
2. Is there exactly one generic domain x context soundness pipeline?
   Not yet. Twenty-one `pp_abs` theorems and one generic version that two
   files cite. P4.
3. Does the generated CLI traverse that canonical architecture?
   Yes. Deleting the second spine left `Voblint_CLI.ml` byte-identical.
4. Can a genuinely relational analysis provide a sound custom caller
   continuation and combine without modifying generic infrastructure?
   Demonstrated for a non-relational custom combine
   (`Example_Sign_DG_Custom_Combine`). The relational case is P7 / #25.
