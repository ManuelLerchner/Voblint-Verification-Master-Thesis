# Digest-Spine Removal Plan

**Status:** proposed cleanup, audit-backed. No removal work has started.

This plan supersedes:

* `docs/CONTEXT_POLICY_MIGRATION.md`
* the witness-merging portion of `docs/COLLECTING_SEMANTICS_UNIFICATION_PLAN.md`

The successful generic `collect_by` refactor remains valid and is retained.

## Objective

Factor the Goblint-faithful generator, read-soundness, activation, and executable proof machinery out of the relational digest experiment, then remove the experiment from the main development.

The migration must preserve the current primary guarantees:

```isabelle
cfg_collect g S v ⊆ γ (meaning σ v)
```

and, for activation-sensitive results:

```isabelle
cfg_collect_ctx_act enterc seedc g S v c
  ⊆ γ (meaning_ctx σ v c)
```

The migration is not required to preserve digest-only results whose purpose is relational context matching, value-history digests, modular `proc_entry` traces, or “digest beats flat” comparisons.

---

## Architectural decision

The canonical concrete execution witness for the retained interprocedural context-sensitive development is:

```text
valid_ltr
```

Contexts are obtained functionally:

```isabelle
key enterc seedc :: ltr ⇒ context
```

The retained collecting architecture is:

```text
valid_ltr
    │
    │ collect_by ... (key enterc seedc)
    ▼
cfg_collect_ctx_act
    │
    ▼
activation collecting soundness
    │
    ▼
functional keyed generator
    │
    ▼
TD-side solver
    │
    ├── context-sensitive endpoint:
    │     cfg_collect_ctx_act ... v c ⊆ γ (meaning_ctx σ v c)
    │
    └── joined/plain endpoint:
          cfg_collect ... v ⊆ γ (meaning σ v)
```

The post-removal architecture must not expose a residual relational context parameter merely instantiated with equality.

In particular, the retained API should use concepts such as:

```text
context key
context equality
keyed read
keyed routing
```

rather than:

```text
cmp = (=)
relational context compatibility
digest compatibility
```

Equality should be built into the retained functional-key interface, not supplied as a degenerate relational parameter.

---

## Verdict

The following relational collecting infrastructure is an overgeneralized side experiment and is removable:

* `trace_witness`
* `cfg_collect_trace`
* `cfg_collect_ctx`
* `Ctx_Collect_Backbone`
* relational `cmp`
* modular `proc_entry` collecting
* value-history digest semantics
* relational digest read/filtering results
* digest-versus-flat precision examples

It is not on the logical soundness path of the current executable flagships.

The only remaining dependency is infrastructural:

* parts of the keyed generator and read-soundness tower are currently stated over `cfg_collect_ctx`;
* the activation and executable developments consume only their functional/equality behavior;
* those reusable parts must be restated over `cfg_collect_ctx_act` or plain `cfg_collect` before the digest spine can be deleted.

---

## Evidence

### Executable flagships

The primary executable theorems target plain collecting semantics:

```isabelle
Example_Interval_DG_Flagship.flagship_collect_sound:
  cfg_collect ... ⊆ ivl_dg_gamma σ
```

```isabelle
Exec_Sign_DG_Run.dgEx_collect_sound:
  cfg_collect ... ⊆ sign_dg_gamma σ
```

Their semantic soundness path goes through `DG_Soundness` and
`DG_Context_Soundness`, using direct reasoning over `cfg_collect`.

This does **not** yet establish an import-free path: `Exec_Sign_DG_Run` currently
imports `Sign_Exec_Sound`, which imports `CFG_Collect_Trace`. The dependency ledger
must distinguish this theorem-placement dependency from a semantic dependence on
trace collecting.

Their final semantic endpoint does not require:

* `cfg_collect_ctx`
* `Ctx_Collect_Backbone`
* `trace_witness.proc_entry`
* relational `cmp`

### Activation flagship

The activation-sensitive flagship targets:

```isabelle
cfg_collect_ctx_act
```

and proceeds through:

* `valid_ltr`
* `Activation_Backbone`
* `Activation_Local_Sound`
* activation generator-realization lemmas

The theorem statement and local proof do not use relational `cfg_collect_ctx`.
Its current imports still include `Interval_Point_Digest`; the pre-removal ledger
must classify each imported fact before treating the activation path as independent.

### Goblint correspondence hypothesis

This table is a target-alignment claim, not evidence by itself. Before removal,
validate every “no counterpart” and “retain” row against a pinned Goblint revision
and record the source path, revision, and relevant API or implementation location in
the dependency ledger. Do not make a removal decision from this table alone.

The retained architecture corresponds to Goblint as follows:

| Formalization concept                      | Goblint counterpart                                                  | Decision                            |
| ------------------------------------------ | -------------------------------------------------------------------- | ----------------------------------- |
| `valid_ltr`                                | local-trace concrete semantics                                       | retain                              |
| `key enterc seedc`                         | functional computation of a context from the entering abstract state | retain                              |
| keyed solver unknowns                      | map keys containing exact context values                             | retain                              |
| enter routing                              | functional callee-context computation                                | retain                              |
| caller context on return                   | combine into the caller’s context                                    | retain                              |
| `trace_witness`                            | no direct implementation counterpart                                 | remove                              |
| `proc_entry` modular seed                  | no corresponding concrete trace constructor                          | remove                              |
| relational `cmp`                           | contexts are exact keys, not relationally matched                    | remove                              |
| value-history digest as concrete semantics | no corresponding concrete collecting model                           | remove                              |
| `gcmp` filtering                           | no relational global-context lookup counterpart                      | remove                              |
| `cmb` / combine realization                | call-return abstract transfer                                        | retain under non-digest terminology |

---

## Scope classification

### Category A — retained core

These theories belong to the Goblint-faithful architecture:

* `DG_Framework`
* `DG_Soundness`
* `DG_Context_Soundness`
* `Exec_DG_Bridge`
* `Exec_Bridge`
* `valid_ltr` definitions and lemmas
* `Activation_Backbone`
* `Activation_Local_Sound`
* `DG_Ctx_Activation`
* `Source_Activation_Sound`
* `cfg_collect_ctx_act`
* `collect_by`
* executable sign and interval DG pipelines
* current flagship examples
* functional keyed generator machinery after extraction
* the functional replacement for `dg_postfix_c_collect_sound`

Required action:

```text
retain, simplify imports, and rename residual digest-oriented APIs
```

### Category B — trace-based compatibility users

These use `cfg_collect_trace` only as a route to a final reachable store:

* `Example_Proc_Call`
* `Example_Side_Branch_Calls`
* `Example_Mixed_Flow_Sign`
* `Example_Interval_Loop_Coverage`
* `Example_IMP2_Coverage`
* `Sign_Exec_Sound`
* `Mixed_Flow_Sound`
* the non-digest headline portion of `Trace_Analysis_Sound`

Required action:

Prefer the weakest faithful theorem statement.

Use plain collecting semantics when context is irrelevant:

```isabelle
s ∈ cfg_collect g S v
```

Use activation witnesses only when witness structure is relevant:

```isabelle
t ∈ valid_ltr g S
sink_node t = v
```

with result store:

```isabelle
sink_store t
```

Do not introduce `valid_ltr` merely to replace trace syntax when the theorem’s actual semantic content is already `cfg_collect`.

### Category C — digest-only experiment

Expected deletion candidates:

* `Ctx_Collect_Backbone`
* relational endpoint of `Local_DG`
* `DG_Route_Soundness`
* `Value_Digest_Reader`
* `Example_Trace_Digest_Combine`
* `Example_Trace_Digest_Precision`
* `Example_Trace_Digest_ReachingCompat`
* `Exec_Sign_Cmp_Keyed_DG_Run`
* digest-only portions of `Trace_Analysis_Sound`
* relational definitions and theorems in `Digest_Global_Read`
* relational digest examples and supporting wrappers

Required action:

```text
delete after all Category-A and Category-B imports have been severed
```

### Category D — mixed or reusable infrastructure

Known candidates:

* `TD_Side_Eff_Cmp_Gen`
* `TD_Side_Eff_Cmp_Pull`
* `TD_Side_Eff_Cmp_Sound`
* `Clean_RRead_Sound`
* `Seed_EnterMono_Lift`
* `Digest_Global_Read`
* shared non-digest portions of `CFG_Collect_Trace`

These files must be split by semantic responsibility.

For every theorem or definition in this category, classify it individually as:

```text
D1: generic generator infrastructure
D2: functional activation/keyed-read infrastructure
D3: relational digest infrastructure
D4: dead compatibility wrapper
```

Actions:

* D1: move to a neutrally named retained theory.
* D2: restate directly over `cfg_collect_ctx_act` or `cfg_collect`.
* D3: delete.
* D4: delete after call sites migrate.

Do not specialize an intrinsically digest-specific theorem merely by setting `cmp = (=)`. Replace it with a direct theorem over the retained semantics.

---

## Preservation obligations

Before deleting any digest theory, establish a preservation ledger containing the exact retained theorem names and their post-migration replacements.

At minimum preserve:

### Plain collecting soundness

```isabelle
cfg_collect ... v ⊆ γ (meaning σ v)
```

for:

* generic DG soundness;
* executable sign instance;
* executable interval flagship;
* source-to-CFG lift where currently available.

### Per-key DG plain endpoint

Preserve a direct functional replacement for the current theorem:

```isabelle
dg_postfix_c_collect_sound:
  cfg_collect g S0 v ⊆ dg_gamma_c sigma ctx v
```

Its retained form may use a functional context key and a non-digest name, but it
must continue to state that a selected keyed D/G view covers plain collecting
semantics. This theorem is distinct from relational digest collecting soundness and
must not disappear merely because it currently resides in a digest-named context
theory.

### Activation collecting soundness

```isabelle
cfg_collect_ctx_act ... v c
  ⊆ γ (meaning_ctx σ v c)
```

for:

* the generic activation backbone;
* activation generator realization;
* the activation flagship.

### Solver correctness

Preserve the chain:

```text
computed solver result
    ⇒ partial/post solution
    ⇒ abstract semantic post-solution
    ⇒ collecting soundness
```

### Call/return behavior

Preserve proofs for:

* functional callee context creation;
* caller context restoration;
* parameter transfer;
* destination-aware return transfer;
* global/local routing required by the current parameter/return migration.

The cleanup must not regress the in-progress destination-aware combine architecture.

---

## Pre-removal gate

Before any file deletion, verify the complete transitive proof path of the activation flagship.

The check must establish that every used theorem from:

* `Seed_EnterMono_Lift`
* `Clean_RRead_Sound`
* `TD_Side_Eff_Cmp_Sound`
* `TD_Side_Eff_Cmp_Gen`
* `Interval_Point_Digest`
* `Digest_Global_Read`

is one of:

1. independent of `cfg_collect_ctx`;
2. used only through equality behavior that can be stated directly over `cfg_collect_ctx_act`;
3. used only for generator algebra and independent of concrete digest semantics.

For each consumed theorem, record:

```text
current theorem
current defining theory
current premises
current semantic endpoint
activation call site
replacement theorem
destination theory
```

The gate passes only when no retained proof requires:

* relational `cmp`;
* one concrete context being compatible with multiple abstract slots;
* `trace_witness.proc_entry`;
* `cfg_collect_ctx`;
* digest history;
* relational global-read filtering.

If any such requirement is genuinely needed by a retained flagship theorem, stop and report before changing the architecture.

---

## Staged migration

Each stage must:

1. modify one coherent architectural layer;
2. end with empty I/Q error diagnostics for every changed theory;
3. introduce no new `sorry`, `oops`, axioms, disabled theories, or hidden session exclusions;
4. be committed separately;
5. include a brief commit note listing theorem replacements and deleted dependencies.

Run I/Q diagnostics and affected-session checks as the inner loop. Run the full
project build at the defined migration gates after Stages 2, 4, and 5, and again at
the final Stage 7 validation. Do not use a full build to locate an individual proof
failure that I/Q can identify.

### Stage 0 — preserve the experiment externally

Before destructive work:

* create a named Git tag or archival branch at the last commit containing the complete digest experiment;
* record that reference in the migration document;
* do not keep dead digest code in the main session merely for archival purposes.

Suggested reference:

```text
archive/relational-digest-experiment
```

**Done.** Annotated tag `archive/relational-digest-experiment` created at commit
`4779e90f` (`feat(cfg): add generic collect_by collector; express activation
collecting as its instance`) — the last commit holding the complete relational
digest spine.

No semantic changes.

### Stage 1 — complete the dependency and theorem ledger

Produce:

* direct and transitive importer lists;
* Category D theorem-level classification;
* retained theorem preservation ledger;
* exact activation-flagship proof dependency path;
* exact source/parameter-return dependency path.

Exit criterion:

```text
every retained use of a Category-C/D theory has a planned replacement
```

No theory deletion.

### Stage 2 — rebase Category B

Replace trace-based final-store statements.

Preferred order:

1. migrate examples;
2. migrate generic sign/mixed-flow soundness;
3. split digest and non-digest portions of `Trace_Analysis_Sound`;
4. remove obsolete trace-to-`cfg_collect` bridge lemmas when unused.

Choose direct `cfg_collect` statements unless witness structure is required.

Exit criteria:

* no Category-B theory imports `CFG_Collect_Trace` for `cfg_collect_trace`;
* no Category-B theorem mentions `trace_witness`;
* original store-level conclusions remain available;
* changed theories have empty I/Q error diagnostics.

Migration gate: run the full project build before Stage 3 begins.

### Stage 3 — introduce retained functional keyed-read theories

Create neutrally named theories for retained machinery. Exact names should follow repository conventions, but conceptually separate:

```text
Functional_Context_Read
Activation_Read_Sound
TD_Side_Keyed_Gen
TD_Side_Keyed_Sound
Seed_Enter_Lift
```

Required transformations:

* remove `cmp` parameters from retained theorem signatures;
* replace relational compatibility premises with exact key equality;
* state concrete semantic premises over:

  * `cfg_collect_ctx_act`, when context-sensitive;
  * `cfg_collect`, when joined or context-insensitive;
* retain only the generator operations genuinely used by the current pipeline;
* rename `dg`, `digest`, `cmp`, `gcmp`, and similar identifiers where they no longer describe the retained concept.

Do not preserve a relational theorem plus an equality corollary as the main interface. The direct functional theorem must become canonical.

Exit criteria:

* activation and executable paths import the new functional theories;
* those paths no longer import `Ctx_Collect_Backbone`;
* those paths no longer mention `cfg_collect_ctx` or relational `cmp`;
* changed theories have empty I/Q error diagnostics.

### Stage 4 — sever the generator from digest semantics

Refactor retained generator and realization infrastructure so it depends only on:

* exact context keys;
* exact keyed reads;
* functional enter routing;
* call/return combine;
* required global unknown layout;
* `cfg_collect` or `cfg_collect_ctx_act` soundness.

Check especially:

* `rt`
* `cmb`
* `gkey`
* former `gcmp`
* `enterc`
* `seedc`
* destination-aware return routing

Required outcome:

```text
generator implementation has no import or theorem dependency on trace_witness,
cfg_collect_ctx, proc_entry, relational cmp, or value-history digest semantics
```

If an old name such as `Cmp_Gen` remains but no comparison relation exists, rename the theory and exported constants.

Exit criteria:

* generic solver and executable examples build using only functional keyed infrastructure;
* theorem statements no longer expose degenerate `cmp = (=)` premises;
* changed theories have empty I/Q error diagnostics.

Migration gate: run the full project build before Stage 5 begins.

### Stage 5 — remove Category C

Delete:

* relational digest collecting backbone;
* relational `Local_DG` endpoint;
* digest route-soundness theories;
* value-history reader;
* digest precision examples;
* relational executable example;
* all remaining digest-only wrappers.

For `CFG_Collect_Trace`:

1. inventory remaining definitions;
2. move genuinely shared definitions to a neutral home;
3. delete:

   * `trace_witness`;
   * `cfg_collect_trace`;
   * `cfg_collect_ctx`;
   * `proc_entry` constructor rules;
   * digest-specific adequacy and projection lemmas;
4. delete the theory entirely if nothing meaningful remains.

Potential shared definitions such as `trace`, `alpha_last`, or `cfg_witness` should be retained only if still used after Category-B migration. Do not extract unused abstractions merely because they could be reusable.

Exit criteria:

```text
grep finds no live references to:
trace_witness
cfg_collect_trace
cfg_collect_ctx
Ctx_Collect_Backbone
proc_entry constructor
relational cmp context premises
Value_Digest_Reader
vd_obs
gcmp
```

Exclude unrelated variables coincidentally named `proc_entry`; check constructor-qualified or theory-relevant occurrences.

Full build must be green.

Migration gate: run the full project build before Stage 6 begins.

### Stage 6 — session and documentation cleanup

Update:

* `ROOT`
* nested `ROOT` files
* `Voblint.thy`
* aggregate theories
* dependency diagrams
* README architecture sections
* developer handoff documents
* migration documents
* GraphViz renderers if they expose removed context concepts

Replace superseded plans with a concise outcome record explaining:

* why the relational digest spine was retired;
* why preserving the relational digest model was no longer a project goal;
* why the final architecture uses `valid_ltr`;
* which reusable machinery was extracted;
* which capabilities were intentionally removed;
* where the archived experiment can be found.

Do not leave documents describing relational `cmp` as current architecture.

Exit criteria:

* documentation and theory graph describe the same architecture;
* no stale imports or dangling theory names;
* full build is green.

### Stage 7 — final architectural validation

Run the full project build with the repository’s standard command.

Additionally verify:

* executable sign solver evaluation still succeeds;
* executable interval flagship still computes its solution;
* activation flagship theorem still proves;
* source-lift theorem still proves;
* parameter/return examples still prove;
* no theorem silently changed from `cfg_collect` to a narrower semantics;
* no theorem relies on an archived or excluded session;
* no new `sorry`;
* no new `oops`;
* no untracked generated proof artifacts.

Produce a final report containing:

```text
commits
deleted theories
moved definitions
renamed theories/constants
old theorem → new theorem mapping
retained flagship theorem statements
removed capabilities
full build command and exit result
```

---

## Removal readiness checklist

The relational digest spine may be deleted only after all boxes are satisfied:

* [ ] Category-B users no longer consume trace semantics.
* [ ] Activation flagship has no relational theorem dependency.
* [ ] Executable DG path has no relational theorem dependency.
* [ ] Keyed-read soundness is stated directly over retained semantics.
* [ ] Generator realization does not expose `cmp`.
* [ ] Destination-aware call/return work is preserved.
* [ ] Shared definitions have either been moved or proven unused.
* [ ] Main theorem endpoints have named replacements.
* [ ] Full build is green before deletion.
* [ ] Archival tag or branch exists.

---

## Abort conditions

Stop and report if any stage establishes that:

* the executable DG pipeline semantically requires relational context compatibility;
* the activation flagship requires one concrete execution to inhabit multiple abstract contexts;
* a retained source-soundness theorem depends on `trace_witness.proc_entry`;
* removing the spine weakens the main `cfg_collect ⊆ γ(σ)` theorem;
* the functional replacement requires stronger assumptions than the current flagship provides;
* destination-aware call/return soundness depends on relational digest machinery;
* removal would require disabling a current flagship or moving it outside the main session;
* Goblint’s current implementation contains an equivalent relational concrete digest semantics.

An import dependency alone is not an abort condition. First determine whether it is semantic or merely caused by theorem placement.

---

## Intentionally removed capabilities

The cleanup intentionally removes:

* relational context compatibility through `cmp`;
* one concrete digest being represented by multiple abstract context slots;
* modular `proc_entry` trace seeding;
* value-history digest collecting semantics;
* relational global-read filtering;
* digest-specific executable instances;
* “digest more precise than flat” results, including:

  * `digest_strictly_more_precise`;
  * `digest_beats_flat`;
  * `reaching_compat_beats_flat`;
  * `combine_digest_filters_tr3`.

These are not preservation obligations for the Goblint-faithful architecture.

---

## Expected final result

The development should contain one primary interprocedural semantic spine:

```text
valid_ltr
```

one generic collector combinator:

```text
collect_by
```

one functional activation collector:

```text
cfg_collect_ctx_act
```

and retained soundness layers for:

```text
functional context routing
keyed unknowns and reads
call/return combine
TD-side solver correctness
plain cfg_collect soundness
activation-sensitive soundness
source-level soundness
```

No retained core theorem should mention relational digest compatibility merely as an implementation artifact.
