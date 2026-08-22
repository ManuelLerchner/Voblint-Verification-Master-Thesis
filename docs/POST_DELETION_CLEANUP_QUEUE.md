# Post-deletion cleanup queue (P3-P12)

Picked up once Slice C/D (obsolete TD/etf spine deletion) is complete and the
full gates are green. Section 0 below is the measured post-deletion baseline;
every count in P3-P12 is stated against it.

## 0. Post-deletion baseline (measured)

Measured on the branch after Slice D, against the pre-deletion audit.

| metric | before | after |
| --- | --- | --- |
| `src` theories | 227 | 212 |
| `src` `.thy` lines | ~96k | 85.8k |
| `Core` | 55 thy / 27.6k | 44 thy / 19.6k |
| `Analysis` | 71 thy / 32.0k | 66 thy / 29.2k |
| `analyse_*` constants | 134 | 128 |
| suffix families with >=4 variants | 19 fams / 89 consts | 9 fams / 38 consts |
| `code_identifier` entries | 122 | 119 |
| theories escaping the map | 20 | 19 |

Sessions and their ROOT graph:

```text
VIMP -> CFG -> Core -> Analysis -+-> Formalization -+
                                 |                  v
                                 +----------------> CLI -> Codegen
                                                     +---> Examples
```

`Voblint_Formalization` is not an endpoint: `CLI/Analyse_Dispatch.thy` imports
it, so the soundness session sits inside the export chain. `ROOTS` lists eight
directories; `src/CodegenCheck` is not among them and builds only when CI
names it.

What the deletion did and did not change:

- `side_cfg_T_eff*` as a suffix family is gone; so are `make_side_rhs_tree_eff*`,
  and `unit_step` / `unit_dg_spec` / `unit_combine_step` fell below four
  variants. The remaining nine families are the domain x mode axes of
  `analyse_*_ctx_result`, `analyse_*_report`, `analyse_*_result`, and
  `formals_route`.
- The `Exec_DG_Bridge` duplicate families, the `pp_abs` clone matrix, the
  generic framework under `Instances/Mixed`, the `CLI/Codegen` misnomer, the
  hand-curated `code_identifier` map and the docs sprawl are untouched by it.
- `Rel_Order_Domain` is no longer dead: `Examples/Mixed/Example_Relational_DG_Demo.thy`
  (202 lines) consumes it. It is a relational witness, not removable code.

## P3 - Finish the `Exec_DG_Bridge` migration

`src/Analysis/Instances/Mixed/Exec_DG_Bridge.thy`, 4885 lines, carries two
transport families. The carrier-generic one lives under the single
`Carrier-generic whole-CFG commute` section (lines 3719-4339, 33 declarations);
the superseded specialized one is split across lines 2687-3718 (37) and
4340-4885 (20). Six subsection titles appear in both:

```text
Per-tree traversal commutation                     2687   3770
Bundled per-tree transport relation                4340   3838
Classifier-parametric fold transport               3333   4005
Per-node tree-list transport for the generator     4420   4051
Equation-system transport for the generic generator 4457  4077
The post-solution transport theorem                4559   4164
```

The migration stalled at adoption, not at construction. The generic
`part_post_solution_seed_dg_st_to_abs` (4166) has zero external users, while
its specialized `_for` counterparts carry every downstream call site:
`part_post_solution_seed_dg_st_to_abs_lifted_for` in six `Formalization/Pipeline`
theories and two call-string examples, `part_post_solution_dg_st_to_abs_for` and
`part_post_solution_dg_st_to_abs_lifted_for` in `Run_Analysis_Sound` and the
interval flagship. Eleven external declarations in total keep the old family
alive; the generic family exports six.

Repoint those call sites at the generic theorems, delete the superseded family
outright (no abstraction that keeps both), then split by responsibility if the
dependency structure justifies it, roughly `Core/Exec/Exec_DG_Refines`,
`_Trees`, `_Generator`, `_Monovariant`. Five subsections (610, 710, 796, 1040,
1147) still carry `issue #123` staging language that the comment rules forbid;
they go with the migration.

Gate: no duplicate family; all consumers on the carrier-generic one; no
theorem lost to renaming; I/Q clean; build and regressions green; own commit.

## P4 - Collapse the domain x context clone matrix

Twenty-one `pp_abs` theorems exist. One is generic
(`Routed_Unit_Domain.pp_abs`, 108); fourteen are production clones and six are
in `Examples`. Only two files outside `Routed_Unit_Domain` cite it at all
(`Run_Analysis_Sound`, `Parity_Exec_Ctx_Sound`), which is why the adopters are
the small cells and the non-adopters are the large ones:

| cell | lines |
| --- | --- |
| `Analysis/.../Sign_Exec_Ctx_Sound` | 557 |
| `Analysis/.../Parity_Exec_Ctx_Sound` | 571 |
| `Analysis/.../Interval_Ctx_None_Routed_Sound` | 1544 |
| `Analysis/.../Int_Exec_Ctx_Sound` | 1682 |
| `Formalization/Pipeline/Interval_Exec_Ctx_Sound` | 1274 |
| `Formalization/Pipeline/Int_Entry_State_Ctx_Sound` | 628 |
| `Formalization/Pipeline/Sign_Entry_State_Ctx_Sound` | 614 |
| `Formalization/Pipeline/Int_Call_String_Ctx_Sound` | 369 |
| `Formalization/Pipeline/Sign_Call_String_Ctx_Sound` | 361 |
| `Formalization/Pipeline/Interval_Call_String_Ctx_Sound` | 263 |
| `CLI/Codegen/{Sign,Interval,Int,Parity}_Codegen` | 491 / 783 / 289 / 246 |

9672 lines across fourteen files, split between two sessions on no principle,
with four names for the same cell role (`_Exec_Ctx_Sound`,
`_Ctx_None_Routed_Sound`, `_Entry_State_Ctx_Sound`, `_Call_String_Ctx_Sound`).
`Interval` and `Int` each carry the solver-mode axis inline as three separate
theorems (`ictx_pp_abs`, `_per_origin`, `_warrow`), which is the same axis
`Routed_Unit_Domain` already parameterizes.

Hoist the generic `ctx_sound` locale into `Core`, adopt
`Routed_Unit_Domain.pp_abs`, and re-instantiate every cell. Nothing may lose a
theorem statement; each cell keeps its named public corollary.

## P5 - Rehome generic D/G framework into Core

`Analysis/Instances/Mixed/` holds 5464 lines that are domain-generic and only
live there by accident:

```text
4885  Exec_DG_Bridge.thy               carrier-generic executable/abstract transport
 293  DG_Base_Exec.thy                 executable mirror of Core's DG_Base
 197  Routed_Unit_Domain.thy           unit-context routed execution, per domain
  89  Monovariant_Analysis_Result.thy  one executable AnalysisResult constructor
```

The rest of the directory is the `Int_*` product domain (Sign x Interval), which
is the only thing the name `Mixed` describes, plus `Rel_Order_Domain` (489
lines), a relational instance that belongs with the domains, not here.

Move the four generic files into `Core/Exec/` and the generic context/result
pipeline into `Core/Pipeline/`. Real moves, not wrapper theories.
`Core/.../DG/DG_Base.thy` and `Mixed/DG_Base_Exec.thy` are two halves of one
concept and should end up adjacent.

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
Parity_Exec  Parity_Checks  Parity_Numeric_Queries  Parity_Exec_Ctx_Sound
Sign_Call_String_Ctx_Sound  Sign_Entry_State_Ctx_Sound
Int_Call_String_Ctx_Sound   Int_Entry_State_Ctx_Sound
Interval_Call_String_Ctx_Sound
```

The split is unprincipled: `Sign_Exec_Ctx_Sound` is remapped,
`Sign_Call_String_Ctx_Sound` is not. Each unmapped theory is a latent module
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
