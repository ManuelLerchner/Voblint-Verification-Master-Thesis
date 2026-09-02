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
contract; `ROOTS` lists eight directories, one per session.

### Done

- **P3** Exec_DG_Bridge's duplicate transport family, then the file itself.
  The carrier-generic engine now proves the raw readback's post-solution
  transport as it already did the lifted one, and the eleven private `_for`
  support lemmas and the unadopted exec-side lifted spec island are gone.
  What was left split along its four layers: `Exec_DG_Refines` (769),
  `Exec_DG_Trees` (1553), `Exec_DG_Generator` (1588), `Exec_DG_Bridge` (370).
- **P4** the domain x context clone matrix. `routed_unit_domain_exec` became
  `routed_domain_exec` by taking the routing functions and their agreement as
  parameters, which is the only thing the eleven copies differed in. All
  eleven post-solution transports are now that one derivation instantiated.
- **P5** the four domain-generic theories moved from
  `Analysis/Instances/Mixed` into `Core/Solver/Context/DG`, where the session
  boundary enforces what their comments only asserted.
- **P6** `CLI/Codegen` -> `CLI/Entry` (it contains no `export_code`),
  `Instances/Mixed` -> `Product` with `Rel_Order_Domain` to
  `Instances/Relational`, the ten context cells into
  `Instances/<Domain>/Ctx/<Domain>_Ctx_<Policy>_Sound`, and
  `Voblint_Formalization` -> `Voblint_Soundness` holding only its two
  endpoints.
- **P8** sixteen escaped modules folded into `Core`, leaving the four `cli/`
  names; `scripts/check_codegen_modules.py` fails on any new escapee, in the
  pre-commit hook and `pixi run codegen-modules`.
- **P12, in part** `docs/history/` separates the completed migration record
  from the live documentation; no theory comment describes itself as staged
  ahead of a migration; the session graph in the project contract is correct.

### Remaining

`P9`, `P10` and `P11` are judgement work rather than mechanism, and all three
touch `Analysis` and `Examples`. Check for concurrent work there before
starting.

## P3 - Split `Exec_DG_Bridge`

Done, after the move to Core so the import churn was one pass. The cuts are
where the file already changed subject, so no proof moved relative to another,
and `Exec_DG_Bridge` keeps its name because it is still the bridge theorem --
importing it pulls the whole stack, so no consumer changed.

## P5 - Rehome generic D/G framework into Core

Done. The four domain-generic theories that lived in
`Analysis/Instances/Product/` by accident now sit in `Core/Solver/Context/DG/`,
next to the abstract framework they mirror:

```text
Exec_DG_Bridge               carrier-generic executable/abstract transport
DG_Local_State_Exec                 executable mirror of Core's DG_Local_State_Spec
Routed_Domain_Exec           the routing layer, renamed with the locale
Result_Normalization  one executable AnalysisResult constructor
```

What remains of the directory is the `Int_*` product domain (Sign x Interval),
which is the only thing the name `Mixed` describes, plus `Rel_Order_Domain`, a
relational instance that belongs with the domains. Both are P6's problem.

Invariant now enforced by the build: Core imports no Analysis theory, because
Core is built before Analysis exists.

## P6 - Normalize the source/session layout

Done; what follows records what the names now mean.

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

## P8 - Guard the `code_identifier` module map

Done. Generating the list from the export closure turned out to be the wrong
shape: 43 of its entries map HOL and AFP library modules that no repository
source mentions, so the closure cannot be derived from the tree. Checking the
emitted output can, and catches the same failure one edit earlier.

The map now names 135 theories and four modules survive: `Core`, plus the
three the handwritten OCaml calls into -- `Analysis_Config`,
`Analyse_Dispatch`, `State_Report_GraphViz`. Folding cannot introduce a cycle
(a cycle needs two modules), so those three are a deliberate API surface
rather than the residue of which edit happened to fail first.

`scripts/check_codegen_modules.py` reads the checked-in export and fails on
any module outside that set, naming the theory to add. It needs no Isabelle,
so it runs in the pre-commit hook beside the ASCII and grammar-drift guards,
and as `pixi run codegen-modules`.

## P9 - Dead-code sweep

Done, and the answer is: there is nothing to delete. Three successive audits
reported 177, then 288, then 942 dead constants. Every one of those figures was
an artefact of a criterion that does not model how Isabelle names are used.

- "unreferenced outside its own file" is not deadness. A type class
  instantiation body defines `gamma`, `is_bot`, `is_top` and `(<)` for a type;
  the definition's *name* is never used again because callers use the class
  operation. All seven strictly-unreferenced definitions in the tree --
  `gamma_abs_congruence`, `less_congruence`, `gamma_abs_int_dom_ext` and four
  `is_top_*'` -- are exactly that, and deleting any of them breaks its
  instance.
- Counting lemmas at all inflates the figure past usefulness. A `[simp]` fact
  is consumed by automation without ever being named, so textual reachability
  says nothing about whether a proof depends on it. That is where 942 comes
  from.
- `Rel_Order_Domain` was called "entirely dead, 489 lines" by the first audit.
  `Example_Relational_DG_Demo` consumes it.

Two theories in `Core/Solver/Context/DG/` still build without being imported,
and both stay. `Call_String_Collecting_Refinement` proves that a coarser
call-string bound never sees more activations than a finer one.
`Call_String_Context_Finite` proves the whole call-string context space finite
before any solve is attempted -- a genuine strengthening over the per-run
`solve_dom` contract, and the answer to the bounding question in #77. Neither
is dead; they are results nothing has needed to cite yet, which the queue's own
classification says to retain.

If a future sweep is wanted, the only defensible criterion is: a `definition`
outside a class instantiation, never mentioned again anywhere, absent from the
generated OCaml. That set is currently empty.

## P10 - Simplify the API name cross-product

Deferred, deliberately. Nine families and 38 constants remain, down from
nineteen and 89: the rest went with the TD/etf spine. What survives is the
genuine domain x solver-mode axis -- `analyse_*_ctx_result` and its
`_per_origin`/`_warrow` siblings -- and that axis is exactly what the
update-rule parameterization is reshaping. Collapsing it first would be work
done twice, in the wrong order.

Revisit once the routed spine is parameterized over the update rule. For each
remaining axis decide whether it is a runtime/config parameter, a type-level
representation distinction, a proof specialization worth keeping, or leftover
scaffolding. Do not optimize for constant count, and do not change stable
public CLI behaviour unnecessarily.

## P11 - Examples and witness organization

Done. `Examples/` now mirrors `Analysis/Instances/`: `Mixed` became `Product`
and the relational demo moved to a `Relational` folder of its own, matching the
domain-side split. `Exec_Ivl_Run` became `Exec_Interval_Run`, so no runnable
demo abbreviates a domain the others spell out.

The "eight stray `*Regression*` files outside `Examples/Regression/`" from the
earlier audit was a misreading: the session README states the convention
explicitly -- folders group by abstract domain, not by capability, and
`Regression/` is for the domain-agnostic witnesses. Those eight are filed
correctly. The two that were genuinely misfiled ran the other way,
domain-specific regressions sitting in the domain-agnostic folder, and are now
with their domains. The README says so, so the next reader does not re-derive
it.

## P12 - Docs and hygiene

Done. `docs/history/` holds the 70 completed migration notes, handoffs, audits
and plans; 70 live documents remain, and the index points at the archive
rather than saying such material is merely "kept in version control". Theory
comments no longer describe themselves as staged ahead of a migration, and the
88 file-path citations across 37 theories are now theory names, as the comment
rules ask. Editor debris and the empty directory are gone.

### The metis/smt audit

The contract keeps `metis` and `smt` only where reconstruction is fast in
batch, and names them the leading cause of build hangs. Measured on a full
verbose build: 84 `metis` and 4 `smt` call sites across 24 theories, and
**not one of them is slow**. The build emits a slow-command warning for
exactly one command in the whole tree, and it is not a `metis`:

```text
command "by" running for 32.048s (line 856 of VIMP_Proc_to_CFG)
```

That is the terminal `qed (auto simp: frag_stmts_def split: option.splits)`
closing the residual cases of the `frag_stmts` induction -- cause 2 on the
slow-build list, unbounded automation over inductive cases, not tactic
reconstruction. It is 32 seconds inside a six-minute build, bounded and
reproducible, in a compiler-correctness proof that nothing else in the tree
would benefit from destabilising. Recorded rather than changed; if it ever
grows, the fix is to name the residual cases rather than widen the `auto`.

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
