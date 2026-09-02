# Export-surface audit: formalization vs generated OCaml

Audit date: 2026-08-24. Baseline: working tree at `10a98af3`
(`refactor/address-based-pred-sel`), `codegen/generated/ml/Voblint_CLI.ml`
(12,638 lines) as checked in.

Question asked: which formalization constructs never reach the exported code,
which of those are legacy rather than proof-carrying, where the definitions and
proofs are more complicated than the result needs, and where the model still
diverges from Goblint.

## Method

1. Extracted every `definition`/`fun`/`primrec`/`abbreviation`/`datatype`/
   `record`/`type_synonym` name from the 215 tracked `.thy` files (1,869 raw names).
2. Extracted every top-level binding from the generated OCaml (1,439 names),
   matching Isabelle's name mangling (leading-case fold, `a`..`h` clash suffix).
3. Cross-referenced each name against every `.thy` file, separating *code*
   occurrences from occurrences inside `text \<open>...\<close>` blocks and `(* *)`
   comments. Prose-only mentions are not uses.
4. Spot-verified every claim below against the source; nothing here rests on the
   name-matching heuristic alone.

**Caveat that shapes the whole report.** "Absent from the export" is a weak
signal on its own. Isabelle emits the transitive closure of the export roots
under the *registered code equations*, so a specification-side constant that a
`[code]` lemma rewrites away vanishes from the OCaml while remaining load-bearing
in the proof. `ownership_split_dg_spec_for`, `dg_gen_of`, `fun_of_dg_st`, `gamma_ownership_split` and
most of `Exec_DG_Generator` are in that category: absent from the OCaml, not
legacy. The findings below are the cases where absence *plus* a use-graph check
shows the construct is genuinely unreferenced or superseded.

## 1. Confirmed dead: unreferenced definitions

Verified by exact-token search over code only — comments and `text \<open>...\<close>`
blocks stripped with a nesting-aware scanner, because prose mentions dominate
the naive grep counts for exactly the constants that are retired. Each entry
below occurs the two times a `definition` costs itself (signature plus defining
equation), or once for a type synonym, and nowhere else in the tree.

| Construct | Site | Count |
| --- | --- | --- |
| `analyse_sign_ctx_result`, `analyse_sign_ctx_result_per_origin`, `analyse_parity_ctx_result`, `analyse_parity_ctx_result_per_origin`, `analyse_interval_ctx_result{,_per_origin,_warrow,_wpo}` | the `*_Ctx_None_Sound` theories | 8 |
| `prog_enter_state`, `prog_combine_env`, `prog_pstep`, `prog_restrict_local`, `prog_restrict_global` | `VIMP_Notation.thy` | 5 |
| `prog_cfg_edges`, `prog_cfg_calls`, `no_annotations`, `enter_action_label`, `compiled_domain_graph_config` | `Analysis_GraphViz.thy` | 5 |
| `analyse_sign_eqs_for`, `analyse_interval_dg_env`, `analyse_int_dg_env` | the `*_Exec_Sound` theories (see §2.1) | 3 |
| `placed_dg_gen_of` | `Exec_DG_Trees.thy` (see §2.2) | 1 |
| `analyse_report` | `DG_Analysis_Adapter.thy` | 1 |
| `publish_global_cont`, `publish_seed_cont` | `DG_Transfer_Combinators.thy` | 2 |
| `side_solver` (type synonym) | `Solver_Menu.thy` | 1 |
| `scoped_location_of` | `Exec_Placement.thy` (callers build the pair directly) | 1 |

The `analyse_*_ctx_result*` row is the notable one: the whole unparameterized
convenience layer over `analyse_*_ctx_result_*_for` was written and never wired
up. The CLI reaches the solver through the `_for` forms exclusively.

Example-session-only — alive, but only as `value`/`eval` fodder:
`analyse_sign_env`, `analyse_int_dg_join_for`, `analyse_int_dg_join_env_for`,
`analyse_int_dg_per_origin_for`, `analyse_int_dg_per_origin_env_for`.

**Two false-positive classes to skip if you re-run this analysis.** A
`definition` inside an `instantiation ... begin` block names the *equation*, not
a constant — `gamma_abs_sign`, `is_top_sign'`, `is_bot_sign`, `inf_sign`,
`less_congruence`, `bot_relc`, `bot_point_state` and their siblings all look
unreferenced while being live `[simp]` rules for an overloaded constant.
(That retraction was over-broad by one: `widen_state`, `Abstract_Domain.thy:914`,
sits *after* `class abstract_domain` at `:902`, in no `instantiation` block, and
has exactly two occurrences in the tree — its own declaration and body. It is
genuinely dead. Verified.) Likewise a `record` type name (`export_edge`, `procedure_scope`)
occurs only at its declaration while its selectors carry all the traffic; both
of those records are load-bearing (`xe_src`/`xe_dst`/`xe_kind`/`xe_label` are
export roots, `scope_locals`/`scope_return_slot` are used across nine files).

The one real observation left in that class is cosmetic: `is_top_sign'`,
`is_top_ivl'`, `is_top_parity'` and `is_top_congruence'` are primed only to dodge
a name clash with the underlying `is_top_sign`/`is_top_ivl`/... predicates, and
none is ever cited by name. Renaming them (e.g. `is_top_sign_abs`) would remove
four primed identifiers that read like leftovers but are not.

## 2. Superseded strata

### 2.1 The Base analysis family under the routed family

The live executable path is

```text
analyse <domain> -> analyse_<d>_report -> analyse_<d>_result_for
  -> analyse_<d>_ctx_result_for        (in <Domain>_Ctx_None_Sound)
  -> routed D/G generator -> TD_side_* solver
```

`Sign_Exec_Sound.thy`, `Interval_Exec_Sound.thy` and `Int_Exec_Sound.thy` carry
a second, older family — `analyse_sign`, `analyse_sign_eqs`,
`analyse_interval_dg*`, `analyse_int_dg*`. **None of its constants appears in
the generated OCaml, and — once `text \<open>...\<close>` blocks are excluded — none is
referenced from live code either.** The many hits a naive grep produces are all
prose: `Analyse_Dispatch.thy:230`/`:304`, `Interval_Entry.thy`,
`Monovariant_Analysis_Result.thy` and the `*_Ctx_*_Sound` theories mention these
names only to say they are *not* the path taken.

After a nesting-aware strip of comments and `text` blocks, the complete
remaining code-level use of the family is:

| Constant | Only remaining use |
| --- | --- |
| `analyse_sign_eqs` | one `by eval` demo lemma, `Sign_Entry.thy:352` |
| `analyse_sign`, `analyse_sign_eqs` | two identification lemmas in `Example_Sign_Codegen_Exec_Consistency.thy` |
| `analyse_interval_dg_for` | `Example_Analysis_Result_Regression.thy` (3×) |
| `analyse_int_dg_eqs_for`, `analyse_int_dg_env_for`, `analyse_int_dg_join_env_for`, `analyse_int_dg_per_origin_env_for` | `Example_Int_Refinement_Mode_Regression.thy` |

Everything else in the three files — `analyse_sign_env`, `analyse_sign_for`,
`analyse_sign_eqs_for`, `analyse_sign_env_for`, `analyse_interval_dg`,
`analyse_interval_dg_eqs`, `analyse_interval_dg_env`,
`analyse_interval_dg_eqs_for`, `analyse_interval_dg_env_for`,
`analyse_interval_dg_join_for`, `analyse_interval_dg_per_origin_for`,
`analyse_int_dg`, `analyse_int_dg_eqs`, `analyse_int_dg_env`,
`analyse_int_dg_for`, `analyse_int_dg_join_for`,
`analyse_int_dg_per_origin_for` — has **no use anywhere in the tree**.

So this is not a specification-side residue that soundness leans on; it is a
retired entry-point layer plus the examples that used to demonstrate it.
Concretely:

- `Sign_Exec_Sound.thy` (100 lines) is six definitions and one `[code]` lemma,
  all of it unreferenced outside the two demo lemmas above. Deleting the theory,
  `Sign_Entry.thy`'s `analyse_sign_demo2_result`, and
  `Example_Sign_Codegen_Exec_Consistency.thy` removes the Sign Base stratum
  entirely.
- `Int_Exec_Sound.thy` is misnamed rather than dead: besides the retired
  `analyse_int_dg*` entries it is the *only* home of `int_tf_for`,
  `int_tf_st_for` and `int_dom_enter_st_for`, which all three `Int_Ctx_*`
  theories genuinely use. Those belong in `Int_Transfer`/`Int_Exec`, next to
  their Sign and Parity counterparts.
- `Interval_Exec_Sound.thy` reduces to whatever
  `Example_Analysis_Result_Regression.thy` needs; that regression should be
  restated over `analyse_interval_ctx_result_for`, which is the function the CLI
  actually runs.
- `Sign_Entry.thy:364` documents `analyse_sign` as "already export cleanly
  (confirmed once, historically, as the M1 ...)". That is exactly the
  development-stage framing `AGENTS.md` forbids in theory comments, and it
  documents a constant that is no longer exported.

### 2.2 The non-strict `placed_dg_*` family

`Exec_DG_Trees.thy` (1,553 lines) defines each executable tree three ways:
`placed_dg_X_tree_with` (the projection-parameterized generic),
`placed_dg_X_tree` (instantiated at the defensive `project_resolved_on`), and
`placed_dg_X_tree_strict` (instantiated at `project_resolved_on_strict`), for
`X ∈ {edge, combine, enter}`, plus the matching `_of` and `_gen_of` shapes.

Every consumer outside the file uses **only** the `_strict` instantiation
(`placed_dg_gen_of_strict` × 22, `placed_dg_edge_of_strict`, ...). Not one
non-strict name is referenced outside `Exec_DG_Trees.thy`.

Blocks that mention a non-strict name and never mention a strict one account for
**668 of the file's 1,554 lines** — including
`placed_dg_edge_tree_side_support_bounded` (87 lines),
`placed_dg_combine_tree_transfer_support_bounded` (67),
`dg_refines_on_placed_entry` (73), `dg_refines_on_placed_combine` (49),
`dg_refines_on_placed_edge` (41) and four more support-bound lemmas. Before
deleting, check whether any `_strict` proof cites one of those lemma *names*;
the header text suggests not, since the strict variant's support bound holds
"unconditionally, with no fact about the raw transfer's own support needed" —
i.e. it is proved directly, not by specializing the defensive bound.

This is the single largest concentrated cleanup in the tree.

### 2.3 The Isabelle DOT emitter

`Analysis_GraphViz.thy` (1,318 lines, **121 definitions, 2 lemmas**) and
`State_Report_GraphViz.thy` (1,239 lines, 58 definitions, 6 lemmas) contain
three parallel renderers:

| Family | Reaches OCaml? | Consumer |
| --- | --- | --- |
| `export_*` / `analysis_graph_to_export` / `raw_cfg_export` | yes | `cli/dot_render.ml`, `cli/html_report.ml` |
| `*_canonical_text` | yes | regression fixtures |
| `analysis_graph_to_dot`, `contextual_analysis_dot`, `raw_cfg_dot{,_lit,_with_report,_with_report_lit}`, `state_report_dot`, `analysis_cluster_dot`, `analysis_edge_dot`, plus `dq`/`nl`/`gv_nl`/`join_gv_nl`/`graphviz_label_text`/`graphviz_html_text`/`source_html_label`/`check_report_html_label`/`check_report_dot_cluster`/`insert_dot_cluster_before_close` | **no** | eight `Example_*` theories only |

So the shipped CLI renders DOT in handwritten OCaml from the structured export,
while the proof session carries a second, complete DOT-and-HTML string emitter
that no shipped artifact ever runs. Its only consumers are `value`-printing
example theories. Two honest options: keep it and say plainly in the theory text
that it exists to render documentation figures from inside the session, or move
those figures to the CLI and delete the emitter.

What should not stand is the current bookkeeping. `AGENTS.md`'s module map still
advertises `State_Report_GraphViz` as "the twelve `*_dot_auto` /
`*_graph_snapshot_auto`", the export block names `*_graph_snapshot_auto` and
`*_export_auto`, and `state_report_dot_auto` / `full_state_dot_auto` /
`entry_state_full_state_dot_auto_code` **do not exist anywhere in the tree** —
their only nine surviving occurrences are prose mentions inside
`State_Report_GraphViz.thy`'s own `text` blocks, describing the theory as if
those entry points were still there.

`Analysis_GraphViz` also contributes 121 of the tree's definitions against 2
lemmas. Note what that does *not* mean: the bulk of those 1,318 lines is graph
*structure* extraction — clusters, node identity, positions, kinds, ownership —
which the structured export needs and which is the part worth deriving from the
verified CFG. Blocks that touch only DOT/HTML string building come to **313
lines**, with a further ~66 shared with the `*_canonical_text` family and needing
a split. Retiring the emitter is a ~310-line deletion, not a ~1,300-line one.

### 2.4 Unconsumed export roots

`export_code` names roots that nothing outside the generated module calls:
`char_of_integer`, `Restore`, `Unwind`, and the four `abstract_value`
constructors `SignValue`/`IntervalValue`/`IntDomValue`/`ParityValue` (the CLI
goes through `string_of_abstract_value`). The export block's own text claims the
roots are "what handwritten OCaml under `cli/`, `codegen/regression/ocaml/` and
`tests/property/` actually calls", and for these six that is not true.

**Correction, found by executing this.** An earlier draft listed
`int_of_integer` here too. It is load-bearing: naming it as a root is what keeps
`type int` *concrete* in the emitted signature, and `cli/vimp_parser.mly`,
`tests/property/ast_driver.ml` and `codegen/regression/ocaml/main.ml` all
construct `Int_of_integer` directly. Removing it turned the type abstract and
broke `cli-build` with `Unbound constructor Voblint_CLI.Core.Int_of_integer`.
The original search looked for the lowercase function name and missed the
capitalized constructor — a root can be load-bearing through the *type* it
exposes, not only through direct calls. Check both spellings.

### 2.5 `Rel_Order_Domain.thy`

489 lines whose own header says "The purpose of this file is not a useful
analysis". It demonstrates that a non-`abs_state` carrier discharges
`sound_dg_spec` unchanged. That is a real result about the framework's
genericity and worth keeping — but it is a *demonstration*, and it sits in
`src/Analysis/Instances/`, where every sibling is a shipped domain. It belongs
next to its `Example_Relational_DG_Demo.thy`, not in the instance directory.

## 3. Simplification and generalization

### 3.1 Per-domain instantiation is copy-adapted, not instantiated

Normalizing domain names away and diffing:

| Pair | Line-level similarity |
| --- | --- |
| `Sign_Ctx_None_Sound` vs `Parity_Ctx_None_Sound` | **0.83** (255 identical lines of ~460) |
| `Int_Ctx_Entry_State_Sound` vs `Sign_Ctx_Entry_State_Sound` | 0.68 |
| `Sign_Entry` vs `Parity_Entry` | 0.63 |
| `Sign_Checks` vs `Parity_Checks` | 0.56 |
| `Sign_Exec` vs `Parity_Exec` | 0.55 |

Adding a domain currently costs 9 files / ~1,900 lines (Parity, the newest and
cheapest) for a four-element lattice. The Sign/Parity `Ctx_None` pair is the
clearest target: at 0.83 similarity the two files differ essentially in the
carrier type and the domain's `is_bot` predicate, both of which the framework
already abstracts. A `routed_unit_instance` locale taking
(`domain_transfer`, executable mirror, `is_bot_pred`, `numeric_ops`) and
producing `<d>ctx_sol`/`<d>ctx_terminates`/`analyse_<d>_ctx_result_for` plus the
node-soundness bridge would collapse both, and Interval/Int would instantiate it
with their extra solver rules on top.

The naming is also inconsistent in a way that hides the parallelism:
`Sign_DG`/`Interval_DG` vs `Parity_Base_DG`/`Int_Base_DG` for the same role, and
`Ivl_Exec` vs `Sign_Exec`/`Parity_Exec`/`Int_Exec`.

### 3.2 The `_lifted` mirror

`ownership_split_dg_spec_for` / `ownership_split_dg_spec_for_lifted`, `ownership_split_step_for` / `_lifted`,
`unit_combine_step_env_for` / `_lifted`, `unit_combine_step_assign_for` /
`_lifted`, `gamma_ownership_split` / `gamma_ownership_split_lifted`, `formals_route` / `_lifted` /
`_gen` / `_lifted_gen`, `branch` / `branch_lifted` — each pair is structurally
identical modulo the carrier (`'a abs_state` vs `'a abs_state lifted`) plus an
`is_bot_pred`, and each pair is bridged by an explicit `*_agrees` lemma.

Measured cost: blocks touching `lifted` are 252/2,473 lines of `DG_Framework`,
134/1,124 of `Routed_Context`, 203/2,318 of `DG_Soundness` — about 10% each.
That is smaller than the shape suggests, so this is a medium-priority cleanup,
not a large one. The right move is not a delete but a parameterization: the two
differ only in whether the carrier has a *decidable, canonical* bottom, and a
single definition taking a "collapse-to-bottom" operation would instantiate to
both, with the `*_agrees` lemmas becoming one generic lemma.

### 3.3 `_gen` alongside its own base

`formals_route_lifted_gen` (38 uses) vs `formals_route_lifted` (7),
`entry_state_route_gen` vs `entry_state_route`, `entry_exec_route_gen` vs
`entry_exec_route`, `dg_tree_st_commute_for` vs `dg_tree_st_commute`,
`sctx_entry_route_gen` / `ictx_entry_route_gen` vs their bases. In each case the
generalized form carries the traffic and the base survives as a thin
specialization — the "new API plus old-API shim" shape `AGENTS.md` calls a
smell. Fold each base into the `_gen` form by instantiation and drop the name.

### 3.4 Misplaced size

`src/Examples/Interval/Example_Interval_Placement.thy` is 2,903 lines — the
largest file in the repository, larger than `DG_Framework` or `DG_Soundness`.
An example that outweighs the framework it exercises is doing something other
than exemplifying.

## 4. Goblint alignment

`docs/GOBLINT_ALIGNMENT_REGISTER.md` is genuinely current (updated 2026-08-24,
`10a98af3`) and its snapshot table holds up against the tree. Checked and
confirmed: `dg_spec` mirrors `Analyses.Spec`'s call protocol field for field
(`dgs_skip`/`assign`/`special`/`branch`/`body`/`return`/`enter`/`event`, plus
`dgs_caller_cont` for `enter`'s caller half and the split
`dgs_combine_env`/`dgs_combine_assign`); local unknowns are `Inl (pp, ctx)`
against Goblint's `(node, S.C.t)`; the exported OCaml really does run the
vendored solver (`tD_side_always_join_Interp_solve`,
`tD_side_per_origin_Interp_solve`, `tD_side_warrowing_apinis_Interp_solve`,
`tD_side_warrowing_per_origin_Interp_solve` are all present).

Three items the register does not currently state correctly:

1. **`combine_env` / `combine_assign` are two hooks now.** The register's
   implementation table says "implemented, composed rather than exposed as two
   hooks". `dg_spec` has had `dgs_combine_env` and `dgs_combine_assign` as
   separate fields since `f7d7a3fd`, with `dgs_combine` a derived composition.
   The row describes the concrete collecting side (`combine_collect`) and is
   right about that, but as written it understates the abstract side.

2. **The domain roster is out of date.** `AGENTS.md` still says "Sign,
   Interval, then Octagon as a stretch goal" and the register/`PROOF_OVERVIEW`
   still describe "the mixed Sign/Interval instance". `int_dom` is a
   **four-component** record — `int_sign`, `int_ivl`, `int_parity`,
   `int_congruence` — and `analysis_domain` is `Sign | Interval | Int | Parity`.
   Congruence exists as a domain component with 2,793 lines behind it and
   appears in no contract document.

3. **`__voblint_check` has no Goblint counterpart row.** VIMP compiles checks to
   a dedicated `EA_Check` edge action and `Check_Event` analysis event with its
   own `abstract_check_domain` classification pipeline. Goblint models
   `assert` through `special`, not through a distinct edge kind or event. This
   is a real, deliberate modeling divergence — it is what makes the verdict
   layer clean — and the register's snapshot table has no row for it.

Beyond that, `Analyses.Spec` fields with no counterpart here, none of which the
register lists as an explicit deviation: `query`/`ask`, `sync`, `vdecl`, `asm`,
`morphstate`, `threadenter`/`threadspawn`, `paths_as_set`. Most fall under the
already-recorded "no multi-analysis manager" and "no concurrency" boundaries,
but `paths_as_set` is the same mechanism as the deferred multi-result `enter`
and belongs in that row. Also, in Goblint `context` is a field *of* `Spec`;
here it is a separate `context_domain` axis outside `dg_spec`. That is arguably
a better factoring, but it is a structural difference and unrecorded.

## 5. Documentation rot

### 5.1 Theory prose names constants that do not exist

Scanning every `\<open>name\<close>` / `\<^verbatim>\<open>name\<close>` occurrence inside `text`
blocks and comparing against all identifiers that occur in code anywhere in
`src/` or `vendor/` yields **44 dangling identifiers**. A handful are false
positives — `id_binary_pred`/`id_unary_log`/`id_binary_log` are deliberate
references to *Goblint's* names, and `bfilter_X_st`/`branch_X_st_for` use `X` as
a domain metavariable. The rest are renamed or deleted constants still named in
prose. The worst cases:

| Stale name | Where it is cited | Reality |
| --- | --- | --- |
| `fun_of_dg_st` | `Exec_DG_Bridge`, `Exec_DG_Refines`, `Exec_DG_Trees`, `Exec_Sign_DG_Run`, `Run_Analysis_Sound`, **`Voblint.thy`** | the constant is `fun_of_dg_st_gen` |
| `part_post_solution_dg_st_to_abs`, `dg_post_solution_collect_sound_ltr` | **`Voblint.thy`** (×3), `Run_Analysis_Sound` | gone |
| `state_report_dot_auto`, `full_state_dot_auto`, `entry_state_full_state_dot_auto_code` | `State_Report_GraphViz` (9 mentions) | gone; see §2.3 |
| `sound_dg_spec_ltr` | `DG_LTR_Sound` | renamed `sound_dg_spec_ltr_for` |
| `analyse_interval_td`, `analyse_interval_td_at`, `analyse_interval_td_terminates` | `Interval_Checks`, `Interval_Ctx_Entry_State_Sound` | only `analyse_interval_td_result`/`_report` exist |
| `assume_sign_st`, `assume_not_sign_st`, `branch_parity_st_for` | `Sign_Backward`, `Parity_Exec` | gone |
| `p_reg_join`, `p_reg_per_origin`, `analyse_sign_sound` | `Interval_Entry` | gone |
| `collect_checks_prog`, `etf_combine_collect`, `gamma_eq_env`, `route_2_commute`, `csim_call_preservation`, `fun_of_st`, `fun_of_exec_dg_st` | various | gone |

**Root cause, and the fix.** Every one of these is written as
`\<open>name\<close>` or `\<^verbatim>\<open>name\<close>`, which the document checker does
*not* resolve against the theory context. The same reference written as
`\<^const>\<open>name\<close>` or `@{const name}` fails the build the moment the
constant is renamed. Converting these — at minimum in `Voblint.thy`,
`Run_Analysis_Sound.thy` and the `Exec_DG_*` theories — turns this whole class of
rot into a batch-build error instead of an audit finding.

`Voblint.thy` is the acute case: it is the capstone whose stated job is to
narrate the verified chain, and its "Executable frontend" section names four
non-existent constants and presents `Sign_Exec_Sound` as "the native D/G runtime
API for Sign" — the retired family of §2.1, which the CLI has not called for
some time.

### 5.2 Markdown

**Correction to an earlier draft of this audit.** I first reported "44 dangling
`*.md` references" as references to deleted files, and specifically claimed the
three tracks `GOBLINT_ALIGNMENT_TRACKS.md` indexes point at nothing. That is
wrong. Resolving all 114 distinct `.md` targets cited across `docs/`,
`AGENTS.md`, `README.md`, `src/`, `tests/` and `scripts/`:

| Outcome | Count |
| --- | --- |
| resolves in `docs/` | 49 |
| resolves in **`docs/history/`**, cited as `docs/X.md` | 51 |
| genuinely absent | 12 |

So the bulk is **path-stale after an earlier move**, one mechanical
`docs/ -> docs/history/` rewrite from fixed — not rot. Verified present in
`docs/history/`: `M1_CALLSTRING_CONTEXT_MIGRATION.md`,
`M3_CONTEXT_BOUNDING_TERMINATION_MIGRATION.md`,
`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md`, `TRACE_BASED_FORK_MIGRATION.md`,
`DG_GAMMA_UNIT_VS_GAMMA_JOIN_AUDIT.md`, `RELATIONAL_DOMAIN_PLAN.md`,
`NONDET_HAVOC_MIGRATION.md`. Of the three alignment tracks, only **M2**
(`M2_DGC_RREAD_BOUNDARY_MIGRATION.md`) is genuinely gone.

The other 11 genuinely absent: `AFP_IMP2_REBASE_MIGRATION`,
`ARCHITECTURE_MIGRATION_PLAN`, `CONTEXT_GENERATOR_MIGRATION_ARCHIVED`,
`ENTER_DIVERGENCE_TRACE`, `GENERATOR_INVENTORY_BEFORE_MIGRATION`,
`GENERIC_NONRELATIONAL_PIPELINE_ARCHITECTURE_DECISION`,
`GHOST_DOMAIN_SEEDING_MIGRATION`,
`MIGRATION_TO_GOBLINT_ALIGNED_ARCHITECTURE`, `PROCEDURES_EXTENSION_PLAN`,
`STRUCTURAL_AUDIT`, `TD_SIDE_FOLD_UNIFICATION_MIGRATION`.

Two of the moves need a content edit rather than a `git mv`, because a live file
cites a doc heading for history:
`tests/regression/11-graph-snapshot/known-imprecision/03-recursion.vimp:9` ->
`CALLSTRING_CONTEXT_DESIGN.md`, and `NEXT_STEPS.md` ->
`ROUTE_A7_GOBLINT_CONTEXT_DESIGN_STUDY.md`.

Remaining markdown findings:

- **`CHECK_ARCHITECTURE.md` describes a deleted path.** Its pipeline diagram
  routes through "`Sign_Exec_Sound` / `Interval_Exec_Sound`" and a
  `<domain>_exec_prog_at` constant. `exec_prog_at` does not exist anywhere in
  the tree; the live route is `*_Ctx_None_Sound` / `analyse_*_ctx_result_for`.
- **`AGENTS.md` module map is stale** on `State_Report_GraphViz` (§2.3) and on
  the domain roster (§4).
- **`docs/INDEX.md` does not mention `GOBLINT_ALIGNMENT_REGISTER.md`** — the
  index omits the living register.
- **`LOCALES.md` and `PIPELINE_AST_TO_SOLUTION.md` are wrong as references**,
  not merely stale: `LOCALES.md` claims to cover "every locale in the project"
  while 7 of 9 cited theories are gone, all six section paths use the deleted
  `Generic/` tree, and it omits the entire current DG locale family;
  `PIPELINE_AST_TO_SOLUTION.md` requires a companion `demo/voblint_pipeline/`
  that does not exist. `ARRAY_SYNTAX_EXTENSION.md` plans work whose premise
  (`to_imp2_aexp`, `IMP2_VCG_Example.thy`) was deleted. These three are
  delete candidates, not history candidates.
- **72 markdown files in `docs/`** (plus 70 already in `docs/history/`, plus 3
  nested). A file-by-file classification puts roughly 28 as LIVING, 42 as
  SUPERSEDED (move to `docs/history/`), 3 as STALE-DELETE, and 1 as an ungated
  build artifact — see §8.2.

## 6. What the migration actually buys

Line counts are measured, not estimated, except where marked. Baseline: 85,574
lines across 215 theories.

### Tier A — pure deletion, verified severable, no proof risk

| Item | Lines |
| --- | --- |
| §1 dead definitions (excluding the 27 lines that fall inside files deleted whole below) | 89 |
| Non-strict `placed_dg_*` family — verified: no proof cites it, no file outside `Exec_DG_Trees.thy` mentions it, and the one strict-side citation of `placed_dg_edge_tree` is a `text` block | 668 |
| `Sign_Exec_Sound.thy` (whole file) | 101 |
| `Example_Sign_Codegen_Exec_Consistency.thy` (whole file) | 22 |
| `Sign_Entry.thy` — the `analyse_sign_demo2` lemma and the Base-family prose | 31 |
| `Interval_Exec_Sound.thy` (whole file; `Example_Analysis_Result_Regression` restates over `analyse_interval_ctx_result_for`) | 126 |
| `Int_Exec_Sound.thy` minus the 33 lines of `int_tf_for`/`int_tf_st_for`/`int_dom_enter_st_for` that move to `Int_Transfer`/`Int_Exec` | 156 |
| **Tier A total** | **1,193** |

### Tier B — deletion behind one decision

| Item | Lines | Gate |
| --- | --- | --- |
| Fold `placed_dg_*_with` into `_strict` once the non-strict instantiation is gone | 100–190 | a fold, not a pure delete; 193 lines currently mention `_with` |
| Retire the Isabelle DOT/HTML emitter (§2.3) | 313 clean, ~66 needing a split from `*_canonical_text` | requires deciding where documentation figures come from |
| **Tier B range** | **410–570** | |

### Tier C — generalization; net shrink plus a structural win

| Item | Net lines | Basis |
| --- | --- | --- |
| Shared locale for `Sign_Ctx_None_Sound` + `Parity_Ctx_None_Sound` | −280 to −330 (estimate) | 462 + 455 lines today, 381 identical after normalising the domain name away; subtract locale and interpretation overhead |
| Fold each `_gen`/base pair into the `_gen` form (§3.3) | −50 to −80 (estimate) | mostly renames at call sites, not deletions |

### Zero-line items that carry most of the correctness value

Converting the 44 `\<open>name\<close>` prose references to `\<^const>\<open>name\<close>`;
correcting the three alignment-register rows; fixing `AGENTS.md`'s module map
and domain roster; fixing `CHECK_ARCHITECTURE.md`'s pipeline; moving
`Rel_Order_Domain.thy` next to its demo; dropping the seven unconsumed export
roots.

### Total

**Superseded by the six-agent sweep (sections 8–13). Revised budget:**

| Area | Dead (delete) | Unification (net) |
| --- | ---: | ---: |
| Original sweep (§1–§3, §7) | 1,193 | 740–980 |
| `src/Framework/Solver` (§9) | ~860 | ~250 |
| `src/CFG` (§10) | ~550 | ~595 |
| `src/Analysis` (§12) | ~700 | ~4,440 |
| `src/Framework/Domain` + `Equations` (§13) | ~2,700 | ~370 |
| `src/VIMP` + `src/CLI` (§11) | ~200 | ~1,230 |
| **Total** | **≈6,200** | **≈7,600** |

**≈13,800 lines, or 16% of the 85,574-line tree.** Two caveats on that number:
the dead column is verified name by name and is the reliable half; the
unification column mixes measured diffs (U1's 289/314 identical lines, U5's
byte-identical 189-line blocks, `Compile_Locality`'s ten diffed pairs) with
projections that assume a locale refactor goes through cleanly, and those will
come in worse than estimated. Read the dead column as a commitment and the
unification column as an upper bound.

### What does *not* change

**The generated OCaml is byte-identical — with one deliberate exception.**
That is the premise of the whole audit: everything in the dead column is already
absent from `codegen/generated/ml/Voblint_CLI.ml`, so `pixi run codegen-check`
must come back clean. That check is also the verification — a non-empty export
diff means something classified as dead was not.

The exception is §12.2's U1: collapsing the four identical `gk` datatypes into
one `'c gk` in Core removes `gka`/`gkb`/`gkc` and their `equal_gk*` functions
from the generated module. That is the only planned change to the shipped
artifact, and it should be made as its own commit so `codegen-check` stays a
clean signal everywhere else.

Nothing here adds a theorem, changes a precision result, or touches soundness.
Build time barely moves either: the deleted proofs are support-bound lemmas and
definitions, not the `Control_Simulation` / `DG_Soundness` / `Exec_DG_Generator`
bulk that dominates the batch.

### What does change

1. **One analysis path instead of two.** Today `Voblint.thy` — the capstone
   whose job is to narrate the verified chain — presents `Sign_Exec_Sound` as
   "the native D/G runtime API for Sign". A reader following that reaches code
   the CLI has not called for some time. After Tier A there is exactly one route
   from `analyse` to the solver.
2. **Adding a domain gets measurably cheaper.** Parity, the newest domain, costs
   1,926 lines across 9 files; ~455 of those are `Ctx_None` boilerplate that
   Tier C turns into an instantiation. A sixth domain would inherit that.
3. **Rename rot becomes a build error.** The 44 dangling prose references exist
   because `\<open>name\<close>` is not resolved against the context. After the
   conversion, the next rename fails the batch build.
4. **The `_strict` / non-strict fork disappears** — 24 named blocks fewer to keep
   in sync, in the file where the executable trees and their support bounds live.

The honest summary: this is a legibility and maintenance migration, not a
performance or capability one. Its value is that the tree stops describing two
architectures when it has one.

## 7. The Examples session

18,043 lines, 64 theories. Composition: 50% `lemma`, 21% `text`, 12%
`definition`, 4% `theorem`. Audited separately because "example" is not what a
large part of it is.

### 7.1 Session hygiene: clean

All 64 theories are actually built — 63 listed in `src/Examples/ROOT`, one
reached by import. No ROOT entry names a missing file, no theory on disk is
unreachable. Nothing to fix here; recorded so it is not re-audited.

### 7.2 Cross-domain examples are genuinely different — no copy-adapt farm

This is the opposite of `src/Analysis`, and worth stating plainly. Normalising
the domain name away and measuring line-level similarity:

| Family | Similarity |
| --- | --- |
| `Example_*_Checks_Store_Only` (Sign / Parity / Interval) | 0.27 – 0.29 |
| `Example_*_DG_Flagship` (Interval / Parity / Interval-IP) | 0.09 – 0.21 |
| `Example_*_DG_CallString_K1` / `_K2` (Sign / Interval) | 0.34 / 0.36 |
| `Example_Side_*` (Execute / Proc_Global / Branch_Calls) | 0.09 – 0.21 |
| `Exec_*_DG_Run` (Sign / Int / Interval) | 0.12 – 0.17 |
| `Example_*_Placement` (Sign / Interval) | 0.08 |

Compare `Sign_Ctx_None_Sound` vs `Parity_Ctx_None_Sound` at 0.83 (§3.1). The
examples differentiate; the instances copy. No unification opportunity here.

### 7.3 Duplicated example programs: two, both trivial

Of 49 distinct `program { ... }` blocks in the tree, exactly two are defined
twice:

- `x := 0; while (x < 20) { x := x + 1 }` — `flagship_prog`
  (`Example_Interval_DG_Flagship`) and `loop_prog`
  (`Example_Interval_Loop_Coverage`).
- the `global g; void bump(n) { g := g + n; return g }` program —
  `nestg_program` (`Example_Interval_DG_CallString_K1`) and `gcall_prog`
  (`Example_Interval_DG_Ctx_Globals_Regression`).

Cheap to share, low value either way.

### 7.4 `Example_Interval_Placement.thy` is not an example

2,904 lines — the largest file in the repository, larger than `DG_Framework`
(2,472) or `DG_Soundness` (2,318). 2,451 of those lines are `lemma`, against 48
`by eval` and 49 structured `proof` blocks. Its sibling
`Example_Sign_Placement.thy` (957) shares the section skeleton at 0.08
line-similarity — the same argument, developed twice, independently.

Section breakdown of the Interval file:

| Lines | Section |
| --- | --- |
| 161 | Interval placement slice with independent global policies |
| 270 | Hook-parametric abstract D/G soundness |
| **734** | Executable-to-abstract post-solution transport |
| 146 | Per-node-shape instantiation |
| **541** | Per-node instantiation |
| 142 | Entry seed and abstract post-solution |
| 75 | Node coverage and dependency closure |
| **629** | Per-node local/side bounds and the abstract post-solution |
| 74 | Trace-native collecting soundness |

Three things are going on, and only the last is an example.

**(a) A locally-generalized lemma triple that belongs in the framework.**
Inside the 734-line transport section sits a 12-lemma grid: for each of
`edge` / `enter` / `combine`, the four steps `placement_hook_gen_single_X`,
`..._X_reduced`, `placement_dg_eqs_single_X`, `placement_dg_refines_X`
(`Example_Interval_Placement.thy:651`–`1281`, ~370 lines). `placement_dg_refines_edge`
(`:1008`) is *already general in `v`* — it fixes CFG-shape hypotheses
(`intra_predecessor_list ... = [(u, a)]`, no combine, no enter) and quantifies
over the node. Nothing in its statement is interval-specific beyond the
`ivl_tf_st_for` / `ivl_tf_for` pair it mentions. It is the example re-deriving,
for itself, the instantiation of the framework's own
`dg_refines_on_placed_edge_strict` / `_enter` / `_combine`. Parameterized over
the transfer pair and hoisted into `Exec_DG_Refines`, it would serve both
placement examples and come free for a third domain. **Verified: the lemma
statement is general in `v`; not verified: that the hoist goes through
mechanically.**

**(b) Per-node grind.** `placement_dg_refines_statement0/1/2/3/5`,
`_function_result_main`, `_function_result_add`, `_function_entry_add` — one
lemma per CFG node of one hand-built program. The "Per-node instantiation" and
"Per-node local/side bounds" sections come to **1,170 lines** in the Interval
file and 329 in the Sign one. A generic "refines at every node of a finite
solved set" lemma is what these want; note that the routed path already states
its node-soundness bridge that way (`Sign_Entry.analyse_sign_result_node_sound_for`
takes four coverage hypotheses and quantifies over the node).

**(c) Both files bypass the routed spine.** Neither imports `Routed_Context` or
`DG_Analysis_Adapter`; both build directly on `DG_LTR_Sound` + `Exec_DG_Bridge`.
They are a second, older derivation route to a collecting-soundness theorem,
kept alive alongside the one the CLI uses.

**They are not deletable.** `GOBLINT_ALIGNMENT_REGISTER.md`'s D/G-reconstruction
row cites `Example_Sign_Placement.thy` and `Example_Interval_Placement.thy` as
the concrete counterexamples distinguishing `gamma_ownership_split gs` from `gamma_join` —
they are load-bearing evidence for a documented architectural claim. The
finding is that 3,861 lines is a disproportionate way to carry that evidence,
and that ~1,500 of it is framework work misfiled as an example.

### 7.5 `Voblint.thy`

493 lines, 411 of them `text` (83%) — a prose index over the whole
development. It names four constants that do not exist (§5.1) and its
"Executable frontend" section presents the retired Base family (§2.1) as the
runtime API. Since it is pure narration, it drifts silently; converting its
`\<^verbatim>\<open>...\<close>` references to `\<^const>\<open>...\<close>` would
make the batch build hold it to the truth.

## 8. The unverified periphery (`cli/`, `tests/`, `scripts/`, `docs/`, CI)

Everything below is outside the proved chain, so none of it can make a theorem
false. It can, however, make the *shipped tool* wrong, and two of these are
already visible defects rather than hygiene.

### 8.1 Dead scripts and artifacts

| Path | Evidence |
| --- | --- |
| `scripts/migrate_pcompletes.py` | zero inbound references; `:13-21` targets six files, five of which no longer exist (`src/VIMP/IMP2_Bridge.thy`, `src/VIMP/IMP2_VCG_Example.thy`, three under the deleted `src/Formalization/`). It cannot run. |
| `scripts/rename_greek_vars.py` | zero inbound references; a one-shot rename that landed 2026-06-15 |
| `scripts/extract_vimp_grammar.py` | `:1-2` self-declares "Feasibility prototype" — extract the grammar IR *from* `VIMP_Notation.thy`. That question is settled: `grammar/vimp.yaml` is canonical. Only inbound reference is a comment in `gen_vimp_isabelle.py:50` |
| `docs/generated/DEFINITIONS_OVERVIEW.md` | **tracked, 1.2 MB**, although `scripts/extract_definitions.py:8-9` says its output is "intended as a gitignored, regenerable index — not a source of truth". Indexes 194 of the 215 theories. Nothing regenerates or gates it. Gitignore it plus add a pixi task, or delete it |
| `scripts/extract_definitions.py --lint` | a working documentation-coverage lint wired to no pixi task, no lefthook job, no CI step |

Also: `tools/` contains only a `__pycache__` for a deleted script; a literal
empty `./~/` directory sits at the repo root; `.claude/CLAUDE.md` and
`.claude/claude.md` are two tracked symlinks to the same blob (only one
materializes on a case-insensitive filesystem); and three non-`.thy` files cite
things that do not exist — `scripts/setup.sh:11` names a `pixi run
update-autocorrode` task that `pixi.toml:86-88` explicitly says does not exist,
`.gitignore:52` names a deleted `scripts/emit_html_report.py`, `cli/.gitignore:1-2`
says "`make` regenerates all of these" and there is no `Makefile`.

### 8.2 `docs/` classification

72 top-level files, classified individually against the tree (does the constant
it is built around still exist? are its cited theories present? does it
self-declare a status?): **~28 LIVING, ~42 SUPERSEDED (move to `docs/history/`,
which already holds 70), 3 STALE-DELETE, 1 ungated artifact.** The three
delete candidates are `LOCALES.md`, `PIPELINE_AST_TO_SOLUTION.md` and
`ARRAY_SYNTAX_EXTENSION.md` — see §5.2 for why those are wrong-as-references
rather than merely historical.

One naming hazard worth fixing while moving: `PROCEDURE_AWARE_CFG_ARCHITECTURE.md`
is *living* — `docs/INDEX.md` treats it as the architecture entry point — so the
`*_MIGRATION.md` suffix currently means two different things. Rename it.

### 8.3 Regression corpus (94 fixtures; `tests/run.py --lint` passes, so all of this is past the static gate)

**Duplicates**

- `06-reachability/precision/03-infeasible_guard_nowarn.vimp` and
  `05-unreachable_dead_branch_literal.vimp` have byte-identical bodies modulo a
  trailing comment. `05:4-6` claims 03 "exercises with a real condition instead
  of the literal sentinel" — but 03's dead check *is* `__voblint_check(false)`.
  Fix 03 to use a real condition, or delete it.
- Two `11-graph-snapshot` fixtures duplicate an existing `03-procedures`
  program and flags, differing only by an `EXPECT-GRAPH` block that could live
  in the original.
- Two `15-solver-choice` fixtures exercise `--solver warrow` on Interval —
  which `Analyse_Dispatch.thy:186` *proves* returns the same value as no flag.
  They duplicate `00-sanity/precision/01` and `12-widening/precision/01`.

**Miscategorised**

- `17-call-string/precision/01-depth1_merges_shared_callee.vimp:124-125` — every
  check is UNKNOWN while the concrete results are fixed (`f(3)->g(3)->6`,
  `f(10)->20`), and the header already names the mechanism. This is a textbook
  `known-imprecision/` case sitting in `precision/`. `tests/run.py`'s
  `lint_case` only inspects `known-imprecision`/`soundness` path components, so
  an all-UNKNOWN `precision/` case passes silently — the exact failure mode the
  module docstring warns about.
- `05-checks/precision/01-multiple_checks.vimp:8-9` mixes a genuinely
  underdetermined `__voblint_nondet_int()` check (a `soundness/` claim) into a
  `precision/` fixture.
- The classic `known-imprecision` ↔ `soundness` confusion is **absent** — all
  nine `known-imprecision/` fixtures have verified fixed concrete results.

**Headers that name no mechanism** (the convention requires one): the two
recursion cases, `11-graph-snapshot/known-imprecision/03-recursion.vimp:7-11`
and `17-call-string/known-imprecision/01-deep_recursion_bounded_context.vimp:15-19`.
The second delegates its mechanism to the first, which delegates to two docs, so
no component is ever named — and the delegation is factually wrong (`fact(50)`
vs `fact(3)`).

**Stale or suspect prose**

- `03-procedures/precision/09-two_call_sites_share_resume_node.vimp:8-18`
  describes a *fixed* defect in the present tense ("destabilizes again,
  forever"). The fix landed in `84d2c354` without touching the file, which now
  asserts a passing `// PROVED`. This is precisely what the regression
  discipline in `AGENTS.md` forbids.
- Two fixtures cite sibling fixtures that do not exist
  (`03-procedures/precision/05:8-12`, `15-solver-choice/precision/04:2`), and
  the first tells the reader a result "remains UNKNOWN" that its own successor
  now proves.
- Two fixtures claim "these are the only two fixtures carrying an EXPECT-GRAPH
  block"; there are 26.

### 8.4 CI does not run three of the gates `AGENTS.md` relies on

`pixi.toml:143` comments the `ci` task as "Everything CI runs, under one name."
Neither set contains the other, and nothing invokes `pixi run ci`:

| Gate | `pixi run ci` | `.github/workflows/ci.yml` |
| --- | --- | --- |
| `lint` (lefthook) | yes | **no** |
| `grammar-check` | yes | **no** |
| `codegen-modules` | via `lint` | **no** |
| `html` | no | yes |
| `isabelle-lint` | no | yes |

Verified: `rg 'grammar-check\|codegen-modules\|lefthook' .github/` returns
nothing. Consequences:

1. **`AGENTS.md`'s grammar-pipeline claim is wrong.** It says the lefthook hook
   means the drift check "runs locally, not only in CI". There is no CI
   coverage at all. A hand-edited `.mly` — which the same section forbids — or a
   `grammar/vimp.yaml` change committed with `LEFTHOOK=0` reaches `main` green.
2. `check_codegen_modules.py` has no CI gate; its only enforcement is the local
   pre-commit hook, and `.lefthook.yaml:21-24` fires it only when the generated
   `.ml` or `Analyse_Dispatch.thy` is staged — so committing a *new* theory
   alone triggers nothing.
3. `codegen-check` and `grammar-check` both use `git diff --exit-code`, which
   does not report **untracked** files. `regenerate-codegen.sh:13` does `rm -rf
   codegen/generated`, so a newly emitted file lands untracked and the check
   passes silently. Use `git status --porcelain <dir>` instead.

Found fine and worth recording: the three build-time copies of
`Voblint_CLI.ml` all regenerate from `codegen/generated/` and are all
gitignored — no stale-copy trust anywhere; the `.source-hash` staleness stamp
recomputes correctly from HEAD; `check_codegen_modules.py` runs green against
the current export (6 modules — `AGENTS.md` says four and omits the two HOL
runtime modules `Bit_Shifts` and `Str_Literal`); `tests/run.py --lint` reports
94 fixtures, no issues.

### 8.5 Trust-boundary defects in `cli/`

Two of these are live bugs, not hygiene.

**(a) ~~The same CFG node gets two different names.~~ RETRACTED — not a bug.**
An earlier draft reported `string_of_cfg_node` rendering `FunctionResult p` as
`result_p` while `graphviz_point_label` renders it `exit_p`, and called that a
divergence. Running the CLI settles it:

```
main_result_main_ctx0 [... label="exit_main\nr=[6,6]"];
```

The two serve different roles. `string_of_cfg_node` builds the DOT **node id**
(`owner ^ "_" ^ string_of_cfg_node p ^ "_ctx" ^ ctx`), which wants a structural
name derived from the constructor; `graphviz_point_label` builds the **display
label**, which wants the symmetric `entry_`/`exit_` pair. They agree on
`FunctionEntry` incidentally and differ on `FunctionResult` deliberately. The
check report never carries a `FunctionEntry`/`FunctionResult` node, since checks
compile to `EA_Check` between `Statement` nodes, so the two spellings never
label the same thing in the same role.

The verification error was checking that two strings differ without checking
that they are used for the same purpose. What survives is much narrower:
`cli/main.ml:153-156` does hand-reimplement the node-id mapping in OCaml,
because `string_of_cfg_node` is not exported — but only its `Statement` branch
is ever exercised.

**(b) `--dot-full` is a no-op under two configurations — verified, and the
reason matters.** Under `--context call-string` or `--context-graph expanded`,
`--dot-full` produces byte-identical output to plain `--dot`. But it is not a
missing feature: those views already annotate *every* node with its per-context
state, so there is nothing left for "full" to add. The four-way `if/else` chain
written out four times is what made the coincidence invisible — the first two
branches are identical in all four copies. Collapsing it to two helpers with a
`~full` flag states the fact once, and `--help` now says it.

**(c) `cli/html_report.ml` re-parses rendered strings, against its own header.**
`:18` states "nothing re-derives the CFG or parses a rendered rendering back".
Thirty lines later: `:52-59` splits `"<var>=<value>"` out of already-rendered
`xn_lines`; `:66-93` re-parses the product domain's flattened string
(`"sign=..., ivl=..., parity=..., congruence=..."`) with a `", " + ident + "="`
heuristic, when the verified layer already exposes it structured as
`abstract_value`; `:112-119` parses the statement index back out of a `"pp<N>"`
label — a third copy of the convention from (a).

**(d) `cli/html_report.ml:298-306` is an undeclared third consumer of the VIMP
grammar.** `AGENTS.md` says `grammar/vimp.yaml` is the sole source of truth and
names exactly two generators. The HTML source view carries a hand-written VIMP
tokenizer (`kw_statement`, `kw_declaration`, `kw_special`, `is_op`). It is
*currently* in sync with `grammar/vimp.yaml:98-125` — all 10 keywords, all 15
punctuation characters — but nothing keeps it so, and `grammar-check` does not
look at this file. One divergence already exists: `is_ident_rest` accepts `'`,
which the `ident` lexeme does not.

**(e) `cli/main.ml:549-551`'s "one legality gate" claim overstates.** It says
every combination is decided by `valid_analysis_config`, "not by a second,
hand-maintained OCaml compatibility table". But `:572-658` are seven
hand-written rejection rules, and every graph and HTML path (`:673-713`,
`:774-815`) bypasses the dispatcher entirely — those route on `!context_kind` /
`!context_graph` directly into `State_Report_GraphViz.*_auto`, which take a bare
`analysis_domain`, not a config. The verified dispatcher covers only the three
`analyse_config*` text paths at `:816-827`. Suspected consequence, not
confirmed: `main.ml:689`'s `failwith "unsupported --analysis/--solver
combination"` is justified as unreachable because `valid_analysis_config`
already rejected it — but `valid_analysis_config` never saw `--html`.

Found fine: `cli/vimp_frontend.ml` correctly consumes `Core.prog_stmt_post_order`
rather than re-deriving the ordering, and fails closed on a length mismatch;
`cli/main.ml`'s reachability handling is driven by verified flags rather than
reconstructed in OCaml, and the file documents that this was deliberately moved
into the verified layer. That is the model the rest of `cli/` should follow.

## 9. `src/Framework/Solver` (15,168 lines)

### 9.1 Confirmed dead — verified with prose stripped

| Item | Site | Lines | Evidence |
| --- | --- | --- | --- |
| `TD_side_always_join_solve_Inr_rg` + its 4-way `pinduct` `TD_side_always_join_rg_ind` | `Solver_Side_RG.thy:143-318` | **176** | one code occurrence: the lemma line. Its mirror half (`..._warrowing_apinis_...`, `:477-702`) *is* live via `Interval_Warrowing.thy`. `solve_dom_of_solve_c` -- the theory's only cross-domain-cited fact at the time of this audit -- has since moved to `Voblint_Solver.Solver_Menu`, which now owns the generic `solve_c`/`part_post_solution` bridge; nothing left in this file is cited outside its own `..._warrowing_apinis_...` mirror half |
| `td_cfg_side_solver_dg` locale | `DG_Framework.thy:2360-2463` | **104** | never interpreted, never `sublocale`d, named nowhere. Its header claims it gives a mechanical `TD_side_mono` interpretation "for any `side_cfg_T_eff_keyed_seed_dg` instance"; no instance takes it |
| `unit_routed_context_hetero` locale | `Routed_Context_Unit.thy:168-243` | 76 | never interpreted. Header claims domains reach the adapter theorems "by interpreting this locale instead of re-deriving them per domain" — no domain does |
| ten `fst_/snd_dgs_*_for` shape lemmas | `Exec_DG_Refines.thy:655-731` | 77 | untagged, uncited. Header states the intended caller explicitly; there is none |
| six mono/static-deps lemmas for the pre-`_at` tree formers | `DG_Framework.thy:388-463` (line range shifted by the `_at`-specialization reorder; content and dead-code status unchanged) | 76 | superseded by `apply_dg_spec_at`; no analysis cites any of the six |
| `analyse_report_ctx` + `analyse_report` + two soundness theorems | `DG_Analysis_Adapter.thy:244-311` | 68 | `analyse_result` in the same locale is live; only the report projection is dead |
| `pair_of_dg`/`dg_of_pair`/`merge_dg`/`split_dg` + six `[simp]` rules | `DG_Framework.thy:194-242` | 49 | the four constants occur only inside this window, so the six rewrite rules are permanently inert |
| `monovariant_analysis_result_for` + 2 lemmas | `Monovariant_Analysis_Result.thy:170-210` | 41+34 | superseded *within its own file* by `ctx_solved_for`, which is what the adapters go through. Its 34-line header names three adapters as consumers; none references it |
| `buffer_eqs` + 5 lemmas | `Side_Buffering.thy:131-136, 266-288` | 29 | the pipeline calls tree-level `buffer_sides` directly (`DG_Framework.thy:1681`); the buffered *system* wrapper is never applied |
| `dgs_enter_pair` + 2 `[simp]` projections | `DG_Framework.thy:590-614` | 25 | see §9.3 G5 |
| smaller: `cs_project_gk`, `seed_predecessor_addr_list`, `cs_route_project_ctx`, `proj_local_ge_refl`, `val_at` + 2, five `cs_route_*`/`cs_context_*` lemmas, `threefold_monoD_*` | various | ~90 | each uncited; several carry "any **future** …" or "should one ever be wanted" framing |

**The one that is not merely dead — `publish_seed` encodes the opposite convention from the code.**
`DG_Transfer_Combinators.thy:78-79` defines `publish_seed key x = depend_on key (DG bot x) (answer (DG bot bot))` — payload in the **`globs`** half. The actual seed publication (`Routed_Context.thy:87-88`) writes `depend_on (seed_key (FunctionEntry p) ctx') (DG entry bot) ...` — payload in the **`locals`** half, which is how `routed_extra_g` (`:136`) reads it back with `answer_local (locals seed_state)`. The surrounding 20-line doc block asserts the wrong convention twice and claims "a routed context-sensitive analysis uses one of each per call" — it uses `publish_global` and zero `publish_seed`. Also verified: `publish_global` and `publish_seed` are **textually identical** definitions, as are their `_cont` forms. Four names, two bodies, one wrong comment. Deleting the seed pair removes a trap for the next person who reaches for it.

### 9.2 Unification

- **`activation_collect_sound` vs `_gen`, `valid_ltr_ctx_sound` vs `_gen`** (`Activation_Backbone.thy:24-90`, `Activation_Local_Sound.thy:37-118`): identical proofs modulo `gamma_state` vs `gammaM`. The `_gen` header already says the specialization is "accidental". Both base names are used externally, so keep them — as `lemmas X = X_gen [where gammaM = gamma_state]`. **Saves ~84 of 211 lines.**
- **Base tree formers vs `_at` formers** (`DG_Framework.thy`): four constant pairs, two full duplicated lemma sets (9 + 7 lemmas), and **four proved-but-uncited bridge lemmas** (`dg_edge_tree_as_at` `:428`, `apply_dg_spec_as_at` `:1555`, …). The collapse is already proved and nobody uses it. ~94 lines of parallel definition; the six inert mono lemmas above are the free half.
- **Twelve identical `metis` calls** — `by (metis map_prod_simp snd_conv surj_pair)` ×6 and the `fst_conv` variant ×6 across `Exec_DG_Generator.thy` and `Exec_DG_Trees.thy`. Two named `[simp]` lemmas (`fst (map_prod f g p) = f (fst p)`, `by (cases p) simp`) turn all twelve into `by simp`. This is the densest `metis` cluster in the project, in a file with 19 of the scope's 26 `metis` calls.
- **`cs_route` and `cs_context` are the same function** (`Call_String_Context.thy:31, 39`) — both `take k (u # ctx)`, both ignoring their last argument. Six lemmas exist in mirrored pairs, five of them uncited.
- **`proj_local_ge` / `proj_global_ge`** (`Call_String_Solver_Projection.thy:78-131`): identical `foldr`-domination inductions. One `foldr_guarded_sup_ge` lemma makes both one-liners. 54 -> ~14.
- **Severable but load-bearing, not dead**: the `_placed` family (`ownership_split_dg_spec_placed` and the `gamma_join` soundness section, ~210 lines) is absent from the OCaml and reached only from `Sign_DG.thy` and two Examples — but `sound_dg_spec_unit_placed` is a real theorem that `Sign_DG.thy:36` interprets. Treat as a demonstration family with a known cost.

### 9.3 Goblint findings beyond the register

Drift (register statements no longer true), independently reproducing §4's D1 and adding four:
`analysis-defined call contract missing` is superseded by the same three `dg_spec` fields;
`the collecting-soundness certificate is the remaining proof` is contradicted by
`sctx_entry_activation_collect_sound` and the `Int` counterpart, both proved;
**`point_digest` / `ENTER_MONO`, cited as the closure path, occur nowhere in `src/`** — removed
in the digest-removal commits; and `Update rules ... Default TD-side behavior only. Open`
contradicts `Solver_Menu.thy:63-70`'s four rules and the register's own line 146.

Gaps not recorded:

- **G1 — there is no `sync` hook.** `dg_spec` has no `sync` field and `sync` occurs nowhere in `src/` (verified). Goblint's `Spec.sync` runs after every transfer and at loop heads, and is exactly where `basePriv.ml`'s privatizations publish. This matters *because* the register's publication-timing row is built around publication timing, cites `VojdaniPriv`, and proposes "add a publish-on-unlock transition example" — **there is no hook at which such a transition could fire.** Publication here can only happen inside an edge transfer's returned `'dg`. The row records the semantic mismatch and misses the structural one.
- **G2 — all program globals occupy exactly one solver unknown.** Every instance's global-key type is `Global | Seed pp ctx` (verified across `Call_String_Context`, `Parity_Ctx_None_Sound`, and the Interval/Int counterparts), and `dg_edge_tree` reads and publishes that one key once per edge. Goblint's global unknowns are `G of V.t`, one per declared global, with `sideg`/`getg` interleavable many times per transfer. The register records the *payload* collapse and says "finite keys ... Partial alignment"; it does not record the key-count collapse, whose consequences are whole-store dependency granularity, whole-store widening, and a read-once/publish-once per-edge schedule that `strategy_tree` could otherwise express.
- **G3 — the context selector never sees the resolved callee.** `Routed_Context.thy:70-92` computes `ctx' = route cc ctx entry ca` — `p` is in scope and used on the next line for `seed_key`, but is not passed to `route`. Goblint's `Spec.context man f d` is per-callee. Invisible today because every instance pins `static_resolve`, but it is the second prerequisite (alongside multi-result `enter`) for a state-reading resolver.
- **G4 — the supplied `combine_env#` may only move upward.** `Constraint_System.thy:837-839` states soundness against the fixed concrete split `λx. if gs x then t x else s x`. The field's own motivation names Goblint's `varEq`, "whose `combine_env` meets the callee exit with a taint-filtered caller state" — a *meet*, which this obligation does not admit. The hook is free; its soundness contract is not.
- **G5 — the `enter`-returns-a-pair protocol is documented only by dead constants.** `dgs_enter_pair` and its flat twin `tf_enter_pair` (`Constraint_System.thy:674`) both state the pair shape and are both dead; the generator calls the halves separately.

## 10. `src/CFG` (9,295 lines)

### 10.1 The finding to act on first: the CLI's well-formedness gate is not connected to its own soundness premises

**Verified.** `cli/main.ml:536` gates every run on
`Core.wf_program_compile_input_exec prog`. That unfolds through
`wf_program_compile_input` (`Compile_Invariants.thy:36-39`) to
`wf_compile_input (storage_global p prog_main_name) ...`.

Every soundness theorem in the project instead assumes
`wf_compile_input (declared_global p) ...` — verified across all four
`src/CLI/Entry/*_Entry.thy`, `Analyse_Dispatch.thy` (six sites), and
`src/Soundness/` (sixteen sites).

Searching all of `src/` for a bridge: `wf_program_compile_input_exec` appears only
in its own definition, its `_sound` lemma, prose, the `export_code` root list, and
two `by eval` witnesses in one Example. **There is no corollary linking the
executable gate to the premise the theorems require.**

The gap is one `simp` step wide — `storage_global_iff [simp]` (`VIMP_Notation.thy:90`)
already proves `storage_global p owner x <-> declared_global p x`. But the corollary
does not exist, and both halves build green independently, so nothing surfaces it.
This is the "instantiation gap" pattern from the project's own autoformalization
audit, sitting in the load-bearing position.

### 10.2 Other confirmed dead

`intra_successors` (`CFG_Def.thy:238`), `cone` (`CFG_Prune.thy:74` — and
`Voblint.thy:230` claims it "feed[s] the cone guard"; nothing feeds anything),
`collect_result` (`LTR_Collect.thy:176`), `com_stmt_order` + 4 lemmas
(`VIMP_Proc_to_CFG.thy:188-233`, ~55 lines).

**`wf_cfg` is proved for every compiled program and assumed by nothing.**
`compile_prog_wf` (`VIMP_Proc_to_CFG.thy:1226`) is uncited; `wf_cfg`'s four
consumers in `CFG_Def.thy` are all uncited and each restates one `wf_cfg_def`
conjunct verbatim. No soundness theorem takes `wf_cfg g` as a premise.

**`frames_match` is not used by the simulation relation it was written for.**
`csim` (`Control_Simulation.thy:1280-1298`) recurses structurally instead; the
predicate's entire six-lemma inversion suite is uncited (~37 lines). Outside
`src/CFG` it is consumed only by two regression witnesses.

`control_at_call_edge` (`Control_Simulation.thy:132-190`, 59 lines) — the file's
own prose says `control_at_seq_after_call_edge` "generalises" it; its five
siblings are all used, only the call one was subsumed and left behind.

`CFG_Prune.thy` is 572 lines with an external surface of five names; a ~400-line
chain ending in `compile_prog_entry_cfg_reaches_exit` has no consumer, and
`docs/CFG_COMPILER_CONTINUATION_REDESIGN.md:1708` claims it "is consumed".

### 10.3 Unification in the two big proof files

**`Control_Simulation.thy` — ~530 of 2,507 lines are mechanically duplicated, ~330 recoverable.**

- The `control_at_*_edge` family (`:25-362`, 338 lines) is one skeleton six times. What the three inductive cases actually need is *pure monotonicity of the witness in the edge sets* — nothing case-specific. A `control_at_descend` lemma taking a monotone predicate parameter reduces 338 -> ~130.
- `seq_after_eq_*_iff` (`:937-984`): eighteen statements, all with the identical proof `by (induction afters arbitrary: c; auto)+`, all saying one thing. 55 -> ~10.
- `is_returning` / `head_call` / `head_return` (`:1375-1466`) are the same spine recursion with three leaf tests, each carrying the same three satellites (two of which are byte-identical inductions). Factoring `head_of` collapses this with the previous item: 98 + 55 -> ~40.
- The four `csim_*_completion` theorems share a **byte-identical ~10-line `Nested` tail**; the theory's own prose at `:2085` admits the mirroring. A `csim_Nested_lift` lemma removes ~55 lines.

**`Compile_Locality.thy` — ten `intra`/`calls` lemma pairs, ~565 lines, roughly half duplicate.**
Diffed the two largest: `compile_procs_intra_owner` vs `..._calls_owner` (169 lines
for one argument, 8 mechanical diff hunks) and `frag_edge_intra` vs `frag_edge_calls`
(149 lines, 7 hunks). Every lemma in all ten pairs touches an edge only through its
source node and its *landing* node — `v` for an intra triple, `af` for a calls
quadruple. One projection collapses all ten pairs to ten lemmas: **~565 -> ~300.**

And the abstraction already exists — as the dead one. That projection is exactly the
INTRA ∪ COMB_CALLER half of `cfg_succ_rel` (`CFG_Prune.thy:28-34`), which §10.2 shows
nothing consumes. Widening `cfg_succ_rel` to take raw `E`/`K` turns a dead definition
into the load-bearing one.

### 10.4 CFG-vocabulary gaps the register does not record

The register's entire CFG coverage is one cell naming nothing. Beyond the known
`EA_Check` item: `VDecl` has no analogue and locals arrive by whole-namespace
zeroing at the caller, so every callee local is *definitely* `0` at entry and C's
uninitialized-read imprecision is inexpressible; Goblint's `Entry` edge is an
untyped `EA_Nop`; **`EA_Nop` collapses six distinct phenomena** (`SKIP`, two
special-call cases, `Restore`, `Unwind`, function entry) and is not invertible;
`ASM` has no analogue and there is no opaque-effect edge at all — `edge_step` is
total and exactly known for all seven actions; **`EA_Special` moves library calls
onto `intra` structurally at compile time**, where Goblint keeps them as `Proc`
edges and splits `special` per-analysis at transfer time (this is the closest
structural sibling of the `EA_Check` finding and deserves the same row);
`cfg_node` keys entries by `pname`, not a `fundec`, so `Statement n` carries no
owner, no source location, and `CallEdge` must duplicate `ce_formals` with nothing
in `wf_cfg` tying them to the callee's declaration; the 4-place `calls` relation is
a graph-level encoding of Goblint's *analysis-level* enter/combine split, so ENTRY
and COMB_RESULT have no Goblint CFG counterpart; `calls` is unindexed and
`valid_ltr.ret` recovers the continuation by *matching* at return time, an
unstated well-formedness condition; `EA_Ret` hard-wires `#ret` into the
*concrete semantics of the edge*, so no analysis in this framework can pass a
return value another way; and `Restore`/`Unwind` — two runtime-only `com`
constructors with no CIL counterpart — appear zero times in the register.

### 10.5 Theory prose describing a different architecture

Beyond the stale names already listed in §5.1, three passages describe machinery the
code does not have. All sit in plain `\<open>...\<close>` cartouches, which the document
checker does not resolve:

- **`VIMP_Proc_to_CFG.thy:26-28`** describes a source command `Scope` represented by
  "transparent `EA_Nop` **brackets**". `datatype com` has no `Scope`, `git log -S` finds
  it never existed, and every `EA_Nop` emission in `compile` is a single edge — there are
  no brackets. The same file says it correctly 75 lines later.
- **`CFG_Prune.thy:13-20`** explains the three call-derived successor arms in terms of
  `etf_enter` and `etf_combine_collect`, constants from a deleted record that survive only
  in an untracked `.thy~` backup. The transfer bundle is now `dg_spec`, where the single
  combine is three fields. Structural note: `CFG_Prune` is in `Voblint_CFG`, *upstream* of
  `Voblint_Framework` — the prose cites downstream constants across a session boundary, which is
  how it drifted unnoticed.
- **`LTR_Abstract.thy:220-224`** names three deleted lemmas and describes a migration
  ("once `activation_collect` itself is redefined against `ctx_key`") that already landed —
  and misplaces the definition, which is in the same session at `LTR_Def.thy:990`.

## 11. `src/VIMP`, `src/CLI`, `src/Soundness`, `src/Codegen`

### 11.1 Dead

`state_report_dot` (`State_Report_GraphViz.thy:157`) — confirms §2.3 from the other
direction. `is_bottom_abstract_value` (`:47`) — its sibling `is_top_abstract_value` is
live and in the OCaml, so the asymmetry is real;
`docs/VERIFICATION_CHAIN_AND_TRUST_BOUNDARY.md:314` records the CLI-side caller being
removed and nothing replaced the HOL-side one.

A four-constant cluster in VIMP falls together: `special_mentions_global`
(`VIMP_Special.thy:73`) is dead, and once it goes so are `exp_mentions_global`,
`aval_eq_on_locals`, and `mentions_global_defs` (`VIMP_Expr.thy:59-76`) — the last of
which is an **always-on `[simp]` rule for a dead constant**, since `VIMP_Expr` is
imported by the entire tree. Its prose describes a mechanism ("effectful edge trees use
this to omit the unit-global `QueryG`") that nothing implements.

**`analyse_ctx` is dead *and* disagrees with the canonical resolver.**
`Analysis_Config.thy:145-157` states the contract: "The one legality-and-defaults table
this configuration has ... never by a second, independently maintained case split."
`Analyse_Dispatch.thy:87-101` is a second case split, and at `:95`
`analyse_ctx Sign_Analysis (Ctx_CallString k) p = Some (...)` has **no `k` guard**, while
`resolve_analysis_config` rejects `k = 0`. Not CLI-observable only because `analyse_ctx`
is dead — which is the argument for deleting it rather than keeping it as a compatibility
table. `analyse_with_solver` (`:163-180`) is a third table and *is* live; it should be
restated as a consumer of `resolve_analysis_config`.

### 11.2 The Entry files: ~1,478 of 1,811 lines are one bundle written six times

The bundle is `X_result_node_sound_for` -> `X_report_sound_{proved,refuted}_for` ->
two corollaries. It occurs six times (Sign, Parity, Int, Interval ×3). Measured on
prose-stripped lines:

| Pair | Lines | Ratio | Differing |
| --- | --- | --- | --- |
| `analyse_sign_report_sound_proved` vs `analyse_parity_...` | 21 / 21 | **1.00** | **0** |
| `analyse_sign_report_sound_refuted` vs `analyse_interval_...` | 21 / 21 | **1.00** | **0** |
| `..._proved_for` (Sign vs Parity) | 38 / 32 | 0.91 | 6 |
| `..._result_node_sound_for` (Sign vs Parity) | 149 / 101 | 0.77 | 58 |

Ten of the twelve corollaries are character-identical modulo the domain token. And the
generic lemma the bundle needs **already exists**: `Sign_Checks.thy:191` is literally
`lemmas sctx_result_node_sound = sctx_adapter.analyse_result_node_sound`, and
`Int_Ctx_None_Sound.thy:574` re-exports the same `dg_analysis_adapter` fact. One locale
fixing the spine (`sol_prog`, `terminates_prog`, `sigma_abs`, `cinit_st`, `result_for`,
`report_for`, `classify`) proves the bundle once; each domain contributes an
`interpretation` supplying six facts it already has. Int's `mode` needs no special case —
`ictx_sol_prog_warrow mode` is already the partially-applied spine. **~1,478 -> ~400.**

Two free wins that need no locale: 59 of the 71 lines separating Sign from Parity are
Sign restating eight already-named facts as explicit `show`s where the other three
domains write `[OF ...]` — converting deletes **~48 lines from `Sign_Entry.thy` with no
semantic change**. And `Sign_Entry.thy:333-489` is **157 lines (32% of the file) of demo
programs and `by eval` lemmas that do not belong in this session**: `src/CLI/ROOT:3-7`
describes `Voblint_CLI` as "independent of the demonstration and regression theories",
and `src/Soundness/README.md` gives the reason ("Theorems only ... so this session builds
without the slow codegen and `value` runs"). The other three Entry files have no such
block, and the prose itself says these mirror `tests/regression/03-procedures/` fixtures
that already exist.

### 11.3 `State_Report_GraphViz.thy`

Six `_graph_snapshot_auto` / `_export_auto` pairs differ in **exactly one token**
(`raw_cfg_canonical_text_lit` vs `raw_cfg_export`) — one `..._with` per family plus 12
one-line instantiations leaves the exported surface unchanged and removes six chances for
a snapshot and its export to drift apart. Separately, `entry_state_ctx_*` (~163 lines) and
`cs_ctx_*` (~150 lines) are the same six-constant pipeline written twice — and the real
difference is not the context policy: **`cs_ctx_graph_config` is domain-generic while
`entry_state_ctx_graph_config` hardwires Interval** (`ivl_top`, inline lambdas). Factoring
them saves ~120 lines *and* removes the only reason the entry-state renderer is
Interval-only.

### 11.4 `Voblint_CLI`'s dependency on `Voblint_Soundness` is vestigial

**Verified**: `Run_Analysis_Sound.thy` declares 19 names; **none of them occurs anywhere
in `src/CLI`** with prose stripped. All four Entry theories import
`Voblint_Soundness.Run_Analysis_Sound` and `src/CLI/ROOT` carries the session dependency
solely to resolve those imports. This falsifies `AGENTS.md`'s contract statement that
`Voblint_Soundness` "contains ... the per-domain, per-context instantiations the CLI
dispatches to, so it is not a leaf: `Voblint_CLI` imports it" — those instantiations live
under `src/Analysis/Instances/<Domain>/Ctx/`, as `src/Soundness/README.md` itself says,
and the CLI reaches them through `Voblint_Analysis`.

Found fine, and worth recording because it is the claim most worth doubting:
`Run_Analysis_Sound`'s top-level theorems *are* instantiated on concrete programs
(`Example_Interval_DG_Flagship.thy:226`, `Exec_Sign_DG_Run.thy:153`,
`Example_Parity_DG_Flagship.thy:220`), so there is no instantiation gap there, and
`run_source_sound`'s conclusion matches `PROOF_OVERVIEW.md`'s "Source-facing result"
clause for clause.

### 11.5 More register drift

`input()`/havoc is recorded as "only planned"; it is implemented end to end and
`Nondet_Int` is an export root. The **configuration surface has no row at all** —
Voblint's `analysis_config` is a closed 3-field record naming exactly one domain,
resolved by a hand-enumerated 40-branch function into a closed 10-constructor
`analysis_plan`, where Goblint's `--set ana.activated` takes an open list of composable
analyses registered by string name. Adding a domain here means editing the plan datatype,
the resolver, and seven dispatch functions plus the `code_identifier` list; there it is a
registration. And **`wf_source_program` is an analysis precondition with no Goblint
counterpart** — it rejects a `main` with an explicit `return`, which is a representational
rejection, not a semantic one. Goblint has no admissibility predicate; it analyzes what
CIL produces.

`Analyse_Dispatch.thy`'s own prose is wrong in three places about the module structure:
"two named OCaml modules", a module `Analyse` that does not exist, and "around sixty"
`code_module` entries where there are 137. The export emits **six** modules;
`AGENTS.md` says four, omitting the two serializer preludes. The `code_identifier` block
itself is correct — `check_codegen_modules.py` passes.

## 12. `src/Analysis` (25,703 lines) — the largest unification target in the project

### 12.1 Dead

**Whole files with zero external consumers, verified name by name:**
`Sign_DG.thy` (137), `Int_DG.thy` (206), `Int_Base_DG.thy` (154),
`Parity_Base_DG.thy` (74), `Interval_DG.thy` (86, one Example consumer).

The `<D>_Base_DG` pair (228 lines) is dead in an instructive way: each places an
`interpretation ... : sound_dg_spec` **inside a `context fixes gs ... end` block**,
so the facts never escape the context — and neither file's own theorems cite them
(they prove themselves from `local_state_dg_spec_st_for_lifted_dg_spec_step_commute`
directly). The interpretations are inert *and* the twelve `*_local_state_dg_spec_*_commute`
theorems beside them have zero citations. Both files exist only as import edges.

The `<D>_DG` family (429 lines) is different: `sign_dg_api` / `ivl_dg_api` /
`int_{never,once,fixpoint}_dg_api` are never interpreted and
`<D>_dg_post_solution_collect_sound` is never cited, but these are *real terminal
soundness theorems*. The shipped pipeline runs through `local_state_dg_spec_*` +
`dg_ctx_activation_base` and never reaches them. That is the project's own
"instantiation gap" pattern in reverse — the abstract statement exists and no
concrete path arrives at it. The `int_*_dg_api_trivial_gs` lemmas prove
non-vacuity, which suggests the authors already knew.

Dead constants: five more in `Analysis_GraphViz.thy` beyond the ones in §1
(`prog_cfg_edges`, `prog_cfg_calls`, `no_annotations`,
`compiled_domain_graph_config`, `enter_action_label`); `congruence_fact_of_parity`
+ its `[simp]` gamma lemma (`Int_Domain.thy:222-228`), superseded by
`restrict_congruence_by_parity` which is what `congruence_fact_of_int_dom`
actually calls. Plus proved-and-never-consumed lemma families:
`fun_of_st_top_<D>_st` ×4, `<D>_tf_st_for_reduces` ×5 (only Interval's is used —
the `action_reduces` obligation is consumed exclusively by Interval's route
through `Run_Analysis_Sound`, and four domains prove it out of symmetry),
`update_{sign,ivl,parity,congruence}_{exact,le}` ×8. **~700 lines.**

### 12.2 The measured unification budget

| Item | Now | After | Saved |
| --- | ---: | ---: | ---: |
| U1 `<D>_Ctx_None_Sound` ×4 -> one Core locale | 2,812 | ~880 | **~1,930** |
| U2 `Ctx_Entry_State` ×3 + `Ctx_Call_String` ×3 | 3,055 | ~1,940 | ~1,120 |
| U5 Product `refine_mode` triplication | ~950 | ~350 | ~600 |
| U3 `<D>_Transfer` bundling tails ×4 | 324 | ~55 | ~270 |
| U6 `Int_Backward` wrapper layer (5 ops × 5 lemmas) | 222 | ~45 | ~180 |
| U7 `is_bot_pred` false abstraction | — | — | ~180 |
| U4 `<D>_Exec` (Sign, Parity) | 223 | ~60 | ~163 |
| §12.1 dead | ~700 | 0 | ~700 |
| **Total** | | | **≈5,140 — 20% of the directory** |

**U1 is the one to do first, and the evidence is unusually strong.** After
normalising the domain name, **289 of 314 code lines match between
`Sign_Ctx_None_Sound` and `Parity_Ctx_None_Sound`** (ratio 0.896), and every one
of the 25 non-matching lines is an import reordering, a line-wrap, one extra
`[simp]` lemma, or a lemma *name*. **Zero obligations differ. Zero proof steps
differ.** Both declare the same `datatype gk`, both interpret `routed_domain_exec`
with the same five-goal proof, both interpret `dg_ctx_activation_base` with the
same five cases, both interpret `unit_routed_context` with the same
`goal_cases FinC SeedKey CallFwd CombFwd EnterAgree` — including an identical
8-line `EnterAgree` proof.

The locale needs to fix four things (executable transfer mirror, executable enter,
abstract transfer record, initial store) and assume exactly the four facts each
domain already proves (`<D>_tf_st_for_commute`, `<D>_enter_st_for_commute`,
`<D>_is_sound_transfer_for`, `fun_of_st_cinit_<D>_st_for`). Nothing else.

**And the pattern is already in the codebase, on the other axis.**
`Interval_Ctx_None_Sound.thy:152`'s `ictx_solved` locale factors the *solver* axis
correctly: four update rules contribute four `global_interpretation`s over one
locale whose single assumption is `part_post_solution` of the shared system.
Diffing its PerOrigin block against its warrowing block shows only the
interpretation prefix and the prose. The machinery and the taste are there; they
were never turned on the domain axis.

**Codegen dividend, verified in the artifact.** The generated OCaml carries seven
`gk` types, four of them **literally identical**:

```
type gk  = Global  | Seed  of cfg_node * unit
type gka = Globala | Seeda of cfg_node * unit
type gkb = Globalb | Seedb of cfg_node * unit
type gkc = Globalc | Seedc of cfg_node * unit
type gkd = Globald | Seedd of cfg_node * unit int_dom_ext list
type gke = Globale | Seede of cfg_node * sign list
type gkf = Globalf | Seedf of cfg_node * ivl list
```

One `'c gk` in Core collapses the first four and parameterizes the rest — the one
place where this migration *does* change the generated OCaml.

**U5 is the sharpest single duplication in the tree, and it is byte-verified.**
`Refine_Never` / `Refine_Once` / `Refine_Fixpoint` are three *copies* rather than
one parameter, even though every underlying operation already takes `mode` as an
argument. `diff` of `Int_Backward.thy:1022-1210` against `:1211-1399` after
substituting the mode token returns **zero lines** — 189 lines byte-identical.
`Int_Exec.thy` is 332 of 381 lines in three copies. Every proof in those blocks
already cites lemmas stated uniformly in `mode`; the only thing forcing the copy
is that `global_interpretation` needs ground arguments for its `defines`. One
`int_dom_backward_refined_mode` lemma plus three thin interpretations replaces it.

**U7 is textbook false abstraction.** Every `<X>_eqs`/`_sol`/`_terminates` in all
eight Ctx files takes `is_bot_pred` as a parameter, and every context reasoning
about it carries `assumes exact: "is_bot_pred s = is_bot_state (fun_of_... gs s)"`
— an assumption that determines the parameter extensionally from `gs`. Across
`src/Analysis`, `src/Examples`, `src/CLI` and `src/Soundness` the **only** value
ever passed is `resolved_st_q_is_bot_for (declared_global_vars p)`, at 27 sites.
Caveat worth checking before removing it: the parameter may be hoisting
`declared_global_vars p` out of the executable inner loop, in which case the fix
is a `[code]` equation with a `let`, not the parameter.

**Cost of a new four-element domain**, after U1/U3/U4: **~890 lines, down from
Parity's 1,922** (~54%). The remainder is irreducible — the lattice, gamma, the
arithmetic soundness/monotonicity table, the min/max special ops.

### 12.3 A precision defect, verified

`int_dom_min_raw` and `int_dom_max_raw` (`Int_Transfer.thy:92, 100`) update three
components and leave `int_congruence` at `top` from the record base — unlike
`plus_int_dom_raw` / `minus_int_dom_raw` / `times_int_dom_raw`
(`Int_Arithmetic.thy:19, 28, 37`), which all set four. Sound, but
`int_congruence := sup (int_congruence a) (int_congruence b)` is equally sound
(`min i j ∈ {i,j} ⊆ gamma ca ∪ gamma cb ⊆ gamma (ca ⊔ cb)`, and
`join_congruence_ub1/ub2` are already proved) and strictly more precise. The
analogy is direct: `parity_min` is *already* exactly the join in the mixed case.
Per the project's regression discipline this needs a `by eval` witness in
`Example_Int_Domain.thy` pinning the improved value, not just the code change.

### 12.4 Value-domain alignment is entirely unregistered

`GOBLINT_ALIGNMENT_REGISTER.md` contains **zero** occurrences of `IntDomain`,
`congruence`, `parity`, `refine_with`, `ikind`, `overflow`, `def_exc` or `Enums`.
Its only domain-facing row is "Relational state". The whole value-domain axis —
which is what `src/Analysis` *is* — has no entry.

What belongs there (Goblint-side facts recalled, not source-checked — re-check
against `intDomain.ml` at the register's pinned baseline before writing them in):

- **Good alignment worth naming before it drifts.** `refine_mode` is a direct
  transliteration of `ana.int.refinement`; `refine_fix_option` uses `while_option`
  on structural stability matching Goblint's `refine` loop; the `_raw` /
  mode-wrapped split correctly separates "unreduced componentwise product" from
  "reduction is a policy at the operation boundary". That is Goblint's own
  structure.
- **The component sets do not match in either direction.** Goblint has `DefExc`,
  `Interval`, `Enums`, `Congruence`, `IntervalSet`; Voblint has `sign`, `ivl`,
  `parity`, `congruence`. Two of Voblint's four model nothing upstream; three of
  Goblint's five are unmodelled.
- **Components are structurally mandatory, not optional.** Goblint's tuple is
  five `option` slots switched by `ana.int.<name>`; `int_dom` is a record where
  every field is always present. `--disable ana.int.interval` has no expressible
  analogue.
- **Two reduction edges are missing**: interval -> congruence (Goblint's
  `Congruence.refine_with_interval`; a short interval pins a congruence) and
  congruence -> sign (cheap: `mk_congruence c 0` determines the sign exactly).
- **`int_parity` may be redundant against `int_congruence`** — and the tree
  already proves both directions of the embedding
  (`gamma_congruence (congruence_fact_of_parity p) = gamma_parity p`,
  `refine_parity_with_congruence`, `restrict_congruence_by_parity` with exactness).
  Parity is congruence with modulus pinned to 2, and Goblint has no parity domain.
  Open question, not verified: does any forward operation make the parity
  component strictly more precise than the congruence one? If not, `int_parity`
  earns nothing inside the product and its removal takes ~250 lines of plumbing
  with it. Worth a `nitpick`-scale check. (This is not an argument against
  `Parity_Analysis` as a standalone domain, which is a fine instance.)
- **No `ikind`, no wraparound.** Every Goblint `IntDomain` operation is
  `ikind`-parameterised and calls `norm ik`. No soundness theorem in
  `src/Analysis` covers a wrapping integer. A scope decision, but an unrecorded one.

### 12.5 Found fine — do not re-audit

`Int_Warrowing.thy` and `Congruence_Warrowing.thy` read as 100% uncited but are
`instantiation ... :: warrowing` blocks, consumed through the class system.
`Analysis_Config.thy`'s 43 uncited `resolver_*` lemmas are deliberate regression
pins with the rationale written out; correct as they stand. The `_raw` /
mode-wrapped split is the right factoring — it is the *wrapper proof layer* that
is boilerplate, not the split.

**Congruence's 2,793 lines are earned, and it is the counter-example that proves
the boilerplate thesis.** `Congruence_Arithmetic` + `Congruence_Backward` are
Bezout/CRT/`preimage_times_const` number theory — genuine, hard, non-mechanical,
and actually reached. Congruence has no `_Transfer`, `_Exec`, `_DG`, `_Checks` or
`_Ctx_*` layer at all, because it is only a product component — and it is the
leanest domain per line of real mathematics in the directory.

## 13. `src/Framework/Domain` and `src/Framework/Equations`

> **2026-08-31 correction.** The selector unification proposed in §13.2 has
> landed. `combine_env` is generic in key and codomain; frame entry, abstract
> restrictions, and executable projections derive from it. `Split_State` and
> the unused `merge_dg`/`split_dg` conversion cluster were deleted. The audit
> below records the pre-refactor evidence that motivated that change.

Two of my open questions resolve **against** the suspicion: **`Exec_Placement.thy`
and `Split_State.thy` are both genuinely proof-load-bearing** despite
contributing nothing to the export. `Exec_Placement`'s `scope_locations`,
`project_resolved_on{,_strict}` and ~15 lemmas are consumed by `Exec_DG_Trees`,
`Exec_DG_Generator`, `Exec_DG_Refines` and three Examples; `Split_State`'s
`project_component`, `merge_state`, `split_state` and the classic split
predicates are consumed by `DG_Framework`, `DG_Soundness` and `Sign_DG`. Their
OCaml absence is worth nothing as evidence — `project_component` and
`restrict_local_for` are also absent and are core to the DG soundness proof.

### 13.1 Dead — ~2,700 lines across 188 items

- **The `assemble_local_global` / `res_edge` / `res_combine` subsystem** (~173
  lines across `Abstract_Domain.thy:838-901`, `State_Restriction.thy:203-274`,
  `Exec_Refinement.thy:126-162`) — the monovariant `pp + unit` equation shape the
  routed DG generator replaced. A closed loop: nothing outside those three blocks
  touches it, and its one `[simp]` anchor is a rewrite rule about a constant no
  live term contains.
- **The two `resolved_st` refinement locales** (~150 lines, `Exec_St.thy:1380-1456`
  and `:2165-2231`) — never interpreted, none of their 12 lemma names appears
  elsewhere, and the `_q` half is a mechanical copy of the raw half.
- **The `*_st_lift` backward-filter layer** — ~480 of `Exec_Backward.thy`'s 726
  lines. What is live is `afilter_st`/`bfilter_st`/`branch_st` and their commute
  lemmas, consumed by four domains; the `_lift` layer is a parallel formulation
  nothing calls (the pipeline lifts via `transfer_lift`). Deleting it strands
  `live_resolved_st_q`, the three `*_reductive` lemmas (~140 lines) and
  `is_bot_state_bind_formals_abs_enter_frame_D`. **Judgment flag:**
  `afilter_st_lift_correct` / `bfilter_st_lift_correct` are named *correctness*
  results — removing them removes stated theorems, not just scaffolding.
- **`wf_split` and the `merge_state` algebra** — ~117 of `Split_State.thy`'s 189
  lines, while the file itself stays.
- **Two declared, never-used type classes**: `class bounded_widening` and
  `class bounded_narrowing` (`Exec_St.thy:6-7`) have exactly one occurrence each
  in the whole tree — the declaration. Their sibling `bounded_warrowing` is used
  in 13 files. Verified.
- **`widen_state`** (`Abstract_Domain.thy:914`) — see the correction in §1.
- **`SPIKE_sup_fin_eval`** (`Abstract_Checks.thy:47`):
  `lemma SPIKE_sup_fin_eval: "Sup_fin {Check_Proved, Check_Proved} = Check_Proved" by eval`
  — a scratch probe, name and all, left in a production theory.
- Plus ~30 smaller items: `state_sup` + 4 lemmas, `inv_eq_identity`, `le_pairI`,
  the `normalize_point_*` family (~103 lines), `CFG_Enumeration.thy`'s entire
  `finite_*` layer and the set-valued `return_calls` triple (~138 lines), and
  seven `State_Restriction`/`Exec_Refinement` leaves.

**Suspected, not settled:** `Exec_Refinement.thy` (173 lines) has zero external
references to any of its 14 items, but eight are `[simp]` and may fire implicitly
inside `Exec_DG_Refines`/`Ivl_Exec` proofs. The theory is imported by six others
purely as a path to `Exec_St` + `State_Restriction`. Settle it by stripping the
`[simp]` tags and rebuilding.

### 13.2 Unification

- **Three isomorphic copies of `'a lifted`.** `'a lifted = Bot | Lifted 'a`
  (`Abstract_Domain.thy:399-511`), `'a point_state = Unreachable | Reachable 'a`
  (`Analysis_Result.thy:38-100`), `contextual_verdict = Dead | Decided check_result`
  (`Abstract_Checks.thy:441-500`). The instantiation bodies are line-for-line
  identical modulo constructor names — `point_state` even copies `lifted`'s
  `(plugins del: quickcheck_narrowing)` workaround. Downstream, `gamma_point` ≈
  `gamma_lift`, `normalize_point` ≈ `normalize_lift`, and
  `normalize_point_canonicalize_lift_eq_old` (since deleted along with the rest
  of the confirmed-dead `normalize_point_*` family below) literally proved the
  two towers agree. Type synonyms plus constructor abbreviations let both
  inherit all eight instances instead of re-proving four each: **123 lines of
  instantiation plus ~116 of the `normalize_point_*` family.** A real refactor
  (pattern matching in `fun` definitions has to be rewritten), not a rename.
- **Four definitions of "mask a state by a placement predicate"** —
  `project_component`, `restrict_local_for`, `restrict_global_for`, `split_state`
  — where the first is the general one the DG layer actually calls and the other
  three are its instances. The connecting equation exists as
  `split_state_eq_restrict` and is **dead**; no lemma at all connects
  `project_component` to `restrict_*_for`. **And a fifth, duplicated outright:**
  `merge_state gs lg = (λx. if gs x then snd lg x else fst lg x)` and
  `combine_env_abs gs sc se = (λx. if gs x then se x else sc x)` are identical up
  to currying, both live and heavily used (18 files for `combine_env_abs`), with
  **no bridging lemma between them**. That is two masking algebras that can drift
  apart inside separate soundness proofs.
- **A 5 × 5 copy-adapted `inv_*` block** (`Abstract_Domain.thy:1473-1566`): five
  operators × five lemmas whose proofs are character-identical modulo the operator
  name. Twenty of the twenty-five are dead; only the `mono_conj` five are used.
  Four generic lemmas over a free `iv :: 'r ⇒ 'a ⇒ 'a ⇒ 'a × 'a` replace all 25.
  94 lines -> ~20.
- **A duplicated locale, verified.** `semantic_intersection`
  (`Abstract_Domain.thy:931`) and `derived_eq_false_from_intersection`
  (`Abstract_Numeric_Queries.thy:119`) fix the same parameter and state the same
  assumption under different names — and `:143` then re-earns it with
  `sublocale backward_domain ⊆ derived_eq_false_from_intersection intersect
  by unfold_locales (rule intersect_sound)`. Move `eq_false` into
  `semantic_intersection` and delete the second locale (~23 lines).
- `abstract_expression_domain` (`Abstract_Checks.thy:58-104`) is a pass-through
  locale referenced exactly twice — its own declaration and the `for`-clause of
  the locale below it. Nothing interprets it.
- `CFG_Enumeration.thy` repeats a 5-part boilerplate eight times (428 lines);
  deleting the dead `finite_*`/`*_iff` half alone removes ~138 and makes the
  file's real interface — seven `*_list` constants and their `set_*_list` lemmas —
  legible.

### 13.3 Goblint

Independently reproduces the `combine_env`/`combine_assign` drift (§4) and the
IMP2-vs-VIMP naming drift, and adds:

- **The `D`/`G` payload split has landed at the type level, and the register still
  files it as an unstarted "high-cost stretch."** `('l,'g) split_state`,
  `datatype ('l,'g) dg_state`, `record ('dl,'dg) dg_spec` with every field typed
  `... ⇒ 'dl ⇒ 'dg ⇒ 'dg × 'dl`, and `local_state_dg_spec_for_lifted` leaving `'g` free.
  What is *actually* still true is narrower and worth stating precisely: **no live
  instance varies the parameter** — every one pins `('a, 'a)` — and
  `merge_state`/`split_state`/`merge_dg`/`split_dg` are monotyped at `('a,'a)`, so
  the round-trip lemmas cannot even be stated at `'dl ≠ 'dg`. That is the same
  false-abstraction shape the register already records correctly for
  `static_resolve`, and it should be recorded the same way.
- **`startstate` / `exitstate` / `morphstate` have no counterpart anywhere** —
  zero hits across all `.thy`, and no register row. `main`'s entry state is a
  framework constant rather than analysis-supplied (Goblint's `base.ml` uses
  `startstate` to install global initializers); there is no `exitstate`; and
  `morphstate` — re-basing a `D.t` onto another function's frame, used at thread
  entry and for unknown calls — has no analogue, so nothing in the model can
  express "the same abstract state, viewed from another frame."
- **The intra-analysis query channel is structurally absent too.** The register
  records the missing *inter*-analysis manager. It does not record that the four
  numeric queries live as locale parameters of `abstract_numeric_queries`,
  consumed only by the check layer — they are not fields of `domain_transfer` or
  `dg_spec`, so **a transfer function cannot ask a query at all**, and the query
  surface is a fixed four-element enumeration where Goblint has an extensible
  `'a Queries.t` GADT with a per-query result lattice.
- **The `combine_env`/`combine_assign` split is nominal — the work sits in the
  wrong halves.** Goblint: `combine_env` handles globals and effects with no
  result assignment; `combine_assign` writes only the destination. Here
  `DG_Local_State_Spec.thy:47-51` sets `dgs_combine_env = (λci dc de g. (g, dc))` — the
  identity on the caller continuation — while `dgs_combine_assign` does *both* the
  global merge and the destination write. The record has Goblint's field names but
  not Goblint's factorization.

## Suggested order

0. **Close the `wf_program_compile_input_exec` gap (§10.1).** One corollary. The
   CLI gates every run on a predicate that has no proved connection to the
   premise every soundness theorem in the project assumes; `storage_global_iff`
   already supplies the step. This is the only finding in the audit that touches
   what the tool actually guarantees, and it is invisible because both halves
   build green.
1. **Delete the verified-dead list**, area by area, each as its own commit with
   `pixi run codegen-check` green after every one. ~6,200 lines, no proof risk.
   Start with the four large severable blocks: the non-strict `placed_dg_*`
   family (§2.2, 668), `Exec_Backward`'s `_st_lift` layer (§13.1, ~480 — but note
   the judgment flag on the two `*_correct` theorems), the
   `assemble_local_global` subsystem (§13.1, ~173), and
   `Solver_Side_RG`'s always-join half (§9.1, 176).
2. **Retire the Base analysis stratum** (§2.1) and rehome `int_tf_for` and its
   siblings out of `Int_Exec_Sound.thy`.
3. **Fix the three items that are wrong rather than merely stale**: the
   `result_main` / `exit_main` node-label divergence (§8.5a), `--dot-full`
   silently ignored under two configurations (§8.5b), and `publish_seed`
   encoding the opposite `globs`/`locals` convention from the code (§9.1).
4. **Add CI gates for `grammar-check` and `codegen-modules`** (§8.4), and switch
   `codegen-check`/`grammar-check` from `git diff --exit-code` to
   `git status --porcelain` so a newly emitted file cannot pass silently.
5. **U1: one Core locale for `<D>_Ctx_None_Sound`** (§12.2). The largest single
   win in the tree, and the pattern already exists one axis over in
   `ictx_solved`.
6. **U5: collapse the `refine_mode` triplication** (§12.2) — byte-verified, and
   every underlying operation already takes `mode`.
7. **Convert prose references to `\<^const>\<open>...\<close>`** (§5.1) so the
   next rename fails the build. Then fix `CHECK_ARCHITECTURE.md`, `AGENTS.md`'s
   module map and domain roster, and `docs/INDEX.md`'s omission of the register.
8. **`git mv` the 42 superseded docs to `docs/history/`** and rewrite the 51
   path-stale citations (§5.2, §8.2) — two of them need a content edit, not a
   move.
9. **Update the alignment register** with everything in §4, §9.3, §10.4, §11.5,
   §12.4 and §13.3. The register is the project's best document; it is also
   describing a system two migrations behind in several rows, and it has no row
   at all for the value-domain axis or the configuration surface.
10. **The rest of the unification budget** — `Control_Simulation`'s
    `control_at_descend` and `csim_Nested_lift` (§10.3), `Compile_Locality`'s
    `frag_local_succ` (which turns a dead definition into the load-bearing one),
    the three `'a lifted` towers (§13.2), the Entry-file locale (§11.2).

Two things to decide rather than schedule: whether the Isabelle DOT emitter stays
(§2.3), and whether `int_parity` earns its place inside `int_dom` given that both
directions of its embedding into `int_congruence` are already proved (§12.4).
