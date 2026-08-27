<!-- markdownlint-disable-file MD025 -->

# AGENTS.md

Work as a formal proof engineer in Isabelle/HOL. Match the surrounding theory's
structure, naming, comment density, and proof style. Prefer small, explicit
proof steps whose batch behavior is predictable.

## Load context when needed

Keep this file as the project contract. Load detailed guidance only for the
task at hand:

- Before reading, editing, or proving anything in a `.thy` file, read
  `docs/ISABELLE_AGENT_NOTES.md`.
- For the proof architecture and intended claims, read
  `docs/PROOF_OVERVIEW.md` and `docs/PROOF_PHASES.md`.
- For current terminology and defining layers, read `docs/GLOSSARY.md`.
- Before claiming any difference from Goblint is new, unresolved, or worth
  closing, read `docs/GOBLINT_ALIGNMENT_REGISTER.md`. It is the canonical
  record of where this formalization differs from upstream, why, and what
  would close it. An audit run against the source alone will rediscover
  decisions already recorded there and mistake them for findings.
- For scope and priorities, read `docs/ROADMAP.md`, `docs/NEXT_STEPS.md`, and
  `docs/NON_GOALS.md`.
- For an area-specific task, read the nearest `README.md`.
- Use `.thy` files as the source of truth for definitions, theorem statements,
  and proof status. Do not copy drifting lemma inventories into this file.

## Project contract

Voblint verifies this pipeline:

```text
VIMP source -> CFG -> equation system -> TD solver
            -> sound abstract result -> source-level result
```

The formalization should remain faithful to Goblint's architecture and, where a
claim depends on analyzer behavior, to the actual Goblint source.

`valid_ltr` defines the activation-local interprocedural trace semantics.
Soundness targets every program point: `ltr_collect` is the
context-insensitive projection, while `activation_collect` retains activation
keys for context-sensitive results. `ltr_collect_semantic_postfix` connects a
semantic post-fixpoint to `ltr_collect`; `source_completes_ltr_collect_exit`
connects terminating source runs to compiled exit reachability. These are
semantic anchors, not a proof-status inventory.

Locked decisions:

| Topic | Decision |
| --- | --- |
| Logic | Isabelle/HOL over HOL-IMP |
| Source language | VIMP |
| Solver | Vendored verified `TD` solver |
| Solver interface | `part_post_solution` (vendored, generic over unknown/value types) |
| Analysis path | Procedure-aware CFG and generic D/G pipeline |
| Domains | Sign, Interval, Parity, and the Int product (Sign x Interval x Parity x Congruence); Octagon a stretch goal |
| Joins | `Finite_Set.fold` with finite edges, commutativity, and associativity |
| State order | Pointwise `'a::ord` |

The procedure-aware CFG and generic D/G route are the sole analysis path. Every
instance uses the side-effecting verified solver. `analysis_domain` names four
selectable analyses -- `Sign_Analysis`, `Interval_Analysis`, `Int_Analysis`,
`Parity_Analysis`. Congruence is not selectable on its own: it is the fourth
component of `int_dom`, alongside sign, interval and parity.

The session dependency graph is:

```text
VIMP -> CFG -> Core -> Analysis -+-> Formalization -+
                                 |                  v
                                 +----------------> CLI -> Codegen
                                                     +---> Examples
```

`Voblint_Core` is the abstract framework: domains, constraint systems, and the
TD solver bridge, with no domain-specific content. `Voblint_Analysis` threads
each concrete domain instance (Sign, Interval, ...) through it.

Cross-session theory imports use qualified names.
`Voblint_Soundness` contains the reusable soundness endpoints and the
per-domain, per-context instantiations the CLI dispatches to, so it is not a
leaf: `Voblint_CLI` imports it, and the export in `Voblint_Codegen` reaches
through it. `Voblint_Examples` contains executable runs, regressions, GraphViz
output, and the `Voblint` capstone.

`ROOTS` lists eight session directories, one per session in the graph above.

The generated OCaml is compile-checked by actually compiling it: both
`codegen-regression` and `cli-build` run `ocamlfind ocamlopt` over
`codegen/generated/ml/Voblint_CLI.ml`, so a serializer defect fails those
tasks locally and in CI.

The procedural language includes calls, explicit returns, and runtime-only
restore/unwind commands. CFGs separate local `intra` edges from the `calls`
relation and use `FunctionEntry` and `FunctionResult` nodes. Concrete transfer
primitives live in `src/CFG/CFG_Transfer.thy`; activation-local semantics live
under `src/CFG/Collecting/`.

## VIMP grammar pipeline

`grammar/vimp.yaml` is the sole source of truth for VIMP syntax. Two
generators realize it for two unrelated parser targets:

```text
grammar/vimp.yaml
       |
       +-- scripts/gen_vimp_menhir.py   -> cli/vimp_parser.mly, cli/vimp_lexer.mll
       +-- scripts/gen_vimp_isabelle.py -> src/VIMP/VIMP_Grammar_Generated.thy
```

Two generators exist because the two consumers have unrelated parser
infrastructures -- Menhir/ocamllex for the CLI frontend, Isabelle mixfix
syntax and `parse_translation` for `VIMP_Grammar_Generated.thy` (imported by
`VIMP_Notation.thy`) -- and neither can express the other's grammar format.
Each generator handles its own target-specific realization of the one
canonical grammar: e.g. Isabelle numeral decoding, zero-argument call
productions, and workarounds for `Num.num` having no `0`/`1` literal on the
Isabelle side; `%left`/`%right` precedence declarations on the Menhir side.
These realizations do not make `grammar/vimp.yaml` non-canonical, and none of
them may introduce grammar shape (new productions, new precedence) that the
other generator does not also realize.

This whole pipeline sits **outside the proved pipeline** and is **untrusted
code**: no soundness theorem covers lexing or parsing. The proved chain
(Project contract, above) starts at an already-constructed VIMP AST
(`imp_prog`); how that AST was produced -- CLI frontend, `ast_driver`, by
hand -- is irrelevant to any soundness theorem. Confidence in the generated
parsers instead comes from process, not proof: one canonical grammar,
deterministic generation with a drift check, the `.vimp` regression corpus,
AST round-trip and print-stability checks, and Hypothesis-based parser
fuzzing under `tests/property/`. A `lefthook` pre-commit hook (`.lefthook.yaml`,
installed by `./scripts/setup.sh` or `pixi run lefthook-install`) regenerates
both grammar artifacts and blocks the commit if that leaves the working tree
dirty, so the drift check runs locally, not only in CI.

When changing VIMP syntax:

1. Edit `grammar/vimp.yaml` only.
2. Never hand-edit `cli/vimp_parser.mly`, `cli/vimp_lexer.mll`, or
   `src/VIMP/VIMP_Grammar_Generated.thy` -- all three are generated.
3. Regenerate: `pixi run gen-grammar-menhir` (Menhir/ocamllex) and
   `pixi run gen-grammar-isabelle` (Isabelle); load the regenerated
   `VIMP_Grammar_Generated.thy` through I/Q per the theory-file boundary
   rules below, not a host editor. (The pre-commit hook does this
   automatically; this step is for regenerating before that point.)
4. Update or add fixtures in the `.vimp` regression corpus and, if the
   change affects generation strategies, `tests/property/strategies.py`.
5. Run the property-test suite (`pixi run property`).
6. Run `pixi run grammar-check` (regenerates both frontends and fails on
   any diff) and `AFP=/path/to/afp/thys pixi run codegen-check`.
7. Run the Isabelle batch build (`AFP=/path/to/afp/thys pixi run build`) if
   generated syntax changed.

`prog_main`'s separate HOL representation (`imp_prog`'s dedicated
`prog_main :: com` field, instead of folding `main` into `proc_rep` as an
ordinary entry) is a settled representation choice documented inline in
`grammar/vimp.yaml`'s comments, not part of this grammar migration.

## Theory-file boundary

Never use host filesystem read or edit tools on tracked `.thy` files. Isabelle/
jEdit owns their document state; host access can create stale-buffer and
phantom-proof failures.

- Authenticate once per I/Q connection before any other I/Q tool: call
  `authenticate` with token `isabelle-local` (matches `IQ_AUTH_TOKEN` in
  `scripts/start-iq.sh`). Every I/Q call fails with "Not authenticated" until
  this runs.
- Use I/Q `open_file`, `read_file`, and `write_file`.
- If jEdit is unavailable, use I/R `repl_edit`.
- A brand-new, untracked theory may be created once through the host, then must
  immediately be opened in I/Q.
- After an I/Q write: save, run
  `scripts/normalize_isabelle_ascii.py`, reopen the file, and check diagnostics.
- Write Isabelle symbols in ASCII source form. Unicode is allowed in comments,
  but not in theory syntax.

If an actual I/Q or I/R call fails, report it and request
`rtk ./scripts/start-both.sh` or `rtk ./scripts/start-ir.sh`. Do not substitute
a batch build for contextual proof development.

## New theories and the code-export module map

`export_code` in `src/Codegen/Export/Voblint_Codegen.thy` names no
`module_name`, so the OCaml serializer would distribute output one module per
contributing theory. `src/CLI/Analyse_Dispatch.thy` remaps almost every
contributing theory onto `Core` through one `code_identifier` block, because
the unsplit theories have real mutual code-level dependencies. Six modules are
emitted -- four because the handwritten OCaml in `cli/` names them, and two
that are HOL's own serializer preludes:

```text
Core                   everything else, folded into one module
Analysis_Config        mk_analysis_config, valid_analysis_config
Analyse_Dispatch       analyse_config, analyse_config_ctx,
                       analyse_config_with_state, abstract_value
State_Report_GraphViz  the fifteen *_graph_snapshot_auto / *_export_auto /
                       *_payload_auto renderer entry points
Bit_Shifts             HOL runtime support, not a project theory
Str_Literal            HOL runtime support, not a project theory
```

`scripts/check_codegen_modules.py` holds the same six names; keep the two in
step.

Adding a theory whose constants are reachable from an export root therefore
requires adding it to that `code_identifier` list. Forget it and the new
theory keeps its own generated module, which the already-merged `Core` may
both depend on and be depended on by, and `export_code` fails with:

```text
Dependency "<some_core_constant>" -> "<your_constant>" would result in module
dependency cycle
```

The error names two constants and no theory, so it reads like a layering bug
in the new theory. It usually is not: check the `code_identifier` list first.
The fix is one line there, not a `module_name` on the export -- that would
collapse the four surviving modules together too and change the API `cli/`
links against.

`scripts/check_codegen_modules.py` (`pixi run codegen-modules`, and a
pre-commit job) turns a missing entry into an immediate failure naming the
theory, instead of a cycle error two edits later. It reads the checked-in
export, so it needs no Isabelle. When it reports an unexpected module, add the
mapping and re-run `pixi run codegen`.

Sessions and `pixi run build` do not catch a stale export: only
`Voblint_Codegen` runs it, and it is the last session built. A change that
lands a new theory without regenerating `codegen/generated/` leaves the
breakage for whoever next runs a full build.

## Regression discipline

Whenever a change fixes a bug, changes semantics, or introduces a feature,
add or update a regression test that locks in the new behavior -- an
executable witness whose assertion pins the corrected/intended result, not
the one it replaces.

**A regression belongs in the `.vimp` corpus whenever the CLI can observe it.**
Only what the CLI cannot observe stays in Isabelle. Every `by eval`
lemma is a theory the batch build must re-evaluate, and re-evaluating a
solver run is the single largest cost in `Voblint_Examples`; the same
assertion as a `tests/regression/` fixture costs milliseconds and is a
one-line edit when a value legitimately changes.

The test is concrete: run the program through `cli/voblint` and ask whether
the fact appears in what it prints. A check verdict, a per-node variable
value, a context split, a node reported dead or absent, a rendered cluster or
edge, a solver terminating under a given `--solver` -- all of these are
fixture material, including through `// PARAM:` flags and `EXPECT-GRAPH`
blocks. What has no CLI surface stays in Isabelle: domain arithmetic and
backward filters applied to literal abstract values, elaboration and transfer
primitives, compiled `EA_*`/`texp` shapes, structural invariants over a graph
value rather than over rendered output, queries at a program point that is not
a CFG node, and any behaviour reached only by a parameter the CLI does not
expose.

Soundness theorems always stay. A fixture asserts what the analyzer answered;
it cannot assert that the answer is sound. Anything connecting a computed
result to `ltr_collect` is proof content, not a pinning, however it is proved.

A `by eval` fact that a later theorem consumes -- a `*_terminates_c` feeding
`part_post_solution_of_solve_c`, a `wf_cfg` or `cfg_exit_covers` feeding
`vars_cover` -- is a premise, not a pinning, and stays where its consumer can
cite it.

A test asserting a value that is itself the bug is worse than no test: it
converts the bug into a locked-in regression and the batch build stays green
straight through a broken fix. When a fix changes what a lemma or fixture
should assert, update the assertion and its surrounding comment in the same
change -- do not leave a fixture's comment describing behavior as a "known
limitation" once the limitation is fixed.

Within a `tests/regression/<NN-group>/` directory, a case sits in one of
three subdirectories, chosen by what the *concrete* program actually does,
not by what the analyzer currently reports:

- `precision/` -- the concrete result is fixed and decidable from the
  source alone. PROVED/REFUTED are the contract; UNKNOWN there generally
  means a regression.
- `soundness/` -- the concrete result is genuinely not fixed (e.g. an
  unconstrained `random()` feeds the checked condition): both a satisfying
  and a violating execution exist. UNKNOWN is the only sound answer here,
  not a limitation to explain -- asserting PROVED or REFUTED would itself
  be unsound.
- `known-imprecision/` -- the concrete result is fixed, but the abstraction
  can't establish it. The case's header comment must name the concrete
  mechanism -- which component loses the information and why -- not just
  assert that a limitation exists.

Picking `known-imprecision/` for a case that actually belongs in
`soundness/` is a real miscategorization, not a style choice: it invites a
"mechanism" comment for a case that has none (the concrete semantics is
just underdetermined), and it makes precision improvements look like they
"fixed" a case that was never wrong. See `tests/run.py`'s module docstring
for the full convention.

## Proof development

Before each proof, decide whether it is short and simple.

- Short proofs: use `by ...` or apply-style Isar, one or two tactics at a time.
- Longer proofs: sketch structured Isar top-down, isolate hard obligations, and
  fill placeholders individually.
- If a valid obligation is difficult, repair the proof or strengthen its
  invariant. Before changing the architecture, establish that the intended
  theorem is false and try to produce a small `nitpick [timeout=5]`
  counterexample.

Comments explain the current theory and why a choice matters. Do not preserve
project history in source comments: avoid references to removed theories,
retired paths, former names, or migration alternatives. Use Isabelle document
structure (`section`, `subsection`, and `text`) for exposition.

- Comparisons to a still-existing sibling definition or lemma are valid.
- Temporal language that describes the mathematics is valid (e.g. a compiler
  phase, an activation's returning phase). Remove only project-history framing.
- No links to files in comments: no raw or relative paths, no `\<^file>`
  antiquotations, no `docs/*.md` citations. Reference another theory by name
  via `@{theory Qualified.Name}` if needed; state everything else inline.
- No development-stage or migration-plan language: no "Stage 0/1/2", "TODO",
  "still needs", "so far only", or similar staged/future-work framing. A
  comment describes the theory as it stands, not the plan to get there.

## Batch-friendly proof habits

These rules keep interactive development fast and make the final batch build a
reliable one-shot gate.

### Workflow

- **I/Q inner loop, batch outer gate.** Debug one failing command through
  `get_diagnostics` and `explore`. Run the batch build once the complete task or
  migration is file-clean, when the user requests it, or at the commit gate.
  Do not build between stages or tactic changes.
- **I/Q is not completion.** Interactive checking can finish a step while
  subgoals remain or accept an invalid intro rule. Empty file diagnostics mean
  ready for batch, not proved.
- **Batch is completion.** Show the green verbose build log before calling proof
  work done.

### Automation that batch tolerates

- Prefer small, named case-split or decomposition lemmas with
  `by (rule ...)` or `cases rule: ...` over `auto elim!:` on inductive
  predicates.
- Prefer bounded tactics such as `simp only:` and `auto simp:` with an explicit
  lemma set over unbounded automation on large imported rule sets. This governs
  proof-site tactic calls, not whether a lemma itself carries an attribute.
- Default to attributing a new lemma `[simp]`, `[dest]`, `[intro]`, or `[elim]`
  when its shape naturally fits that role: a rewrite whose RHS is no more
  complex than its LHS is `[simp]`; a one-step destruct or introduction off a
  definition's unfolding is `[dest]` or `[intro]`. Tagging lets later call
  sites cite the lemma by name or let `blast`/`auto` find it, instead of
  re-unfolding the definition at each site. Leave a lemma bare only when
  tagging it would be ambiguous or ill-suited: multiple competing rewrite
  directions, a rule that risks looping with existing simp rules, or a fact
  whose applicability is genuinely context-dependent.
- Prefer structured Isar with explicit `show` subgoals over long `[OF ...]`
  chains when facts must align exactly.
- When a subgoal resists one line of automation, hoist a helper lemma. Do not
  widen `auto` or `simp` to force it.
- Before tagging a lemma `[simp]`, check whether its LHS pattern overlaps with
  an existing lemma's LHS that serves a different normal form (a general
  distributive/homomorphism law competing with a specific combine lemma over
  the same redex is the classic case). Two rules that both match the same
  term but stop at different points are non-confluent even when each is
  individually true. When a batch build surfaces a real regression from such
  a conflict, fix it at the algebra level: add the missing bridging lemma(s)
  so every rewrite path reaches the same normal form, rather than reverting
  the new tag. Once confluent, the general laws can carry `[simp]` again, and
  any lemma that only restated a special case of that confluent set is dead
  weight — delete it and its citations rather than keep it as an inert
  corollary.

### Locale and constant shapes

- Theorems inside locales use locale-qualified constants. Callers outside often
  need the same fully applied global shape as the target lemma.
- Before `theorem_callee[OF ...]`, compare interpretation-local premises with
  fully applied global premises. A shape mismatch fails even when the
  mathematics agrees.
- Surface concrete corollaries through global definitions, small expansion
  lemmas, or an `interpretation` block instead of repeating fragile unfolds.

### Sledgehammer in batch

- Try Sledgehammer first on every non-trivial subgoal with a timeout of at most
  15 seconds.
- Prefer paste-backs using `blast`, `auto`, or `meson`.
- Keep `metis` and `smt` only after the batch build confirms they reconstruct
  quickly; they are a leading source of build hangs.

## ASCII-only `.thy` sources

Never write Unicode Isabelle symbols in theory syntax. I/Q accepts and may
serialize them, while the batch parser rejects them with an inner lexical
error.

| Use | Avoid |
| --- | --- |
| `\<Longrightarrow>` | `⟹` |
| `\<Rightarrow>` | `⇒` |
| `\<And>` | `⋀` |
| `\<in>` | `∈` |
| `\<not>` | `¬` |
| `\<noteq>` | `≠` |
| `\<forall>` / `\<exists>` | `∀` / `∃` |
| `\<le>` / `\<ge>` | `≤` / `≥` |
| `\<subseteq>` | `⊆` |
| `\<union>` / `\<inter>` | `∪` / `∩` |
| `\<lbrakk>` / `\<rbrakk>` | `⟦` / `⟧` |
| `\<dots>` | `…` |
| `\<open>` / `\<close>` | `‹` / `›` |

Unicode in comments is allowed. The `lefthook` pre-commit hook's
`isabelle-ascii` job runs `scripts/check_isabelle_ascii.py` over staged `.thy`
files and rejects non-ASCII theory syntax.

I/Q may serialize ASCII input such as `\<lambda>` and `\<open>` as Unicode.
After every `write_file`:

1. `save_file`.
2. Normalize the saved source:

   ```bash
   rtk python3 scripts/normalize_isabelle_ascii.py path/to/Theory.thy
   ```

3. Reopen the file so jEdit reads the normalized text.
4. Check diagnostics again.

Skipping the reopen can leave I/Q checking text that differs from the batch
input.

## Autoformalization audit (Kappelmann et al., 2026)

Run this audit before declaring a theorem done. These errors can survive a
successful batch build.

1. **Locale ordering.** Never assume `P c` before `c` is defined; Isabelle can
   instantiate the assumption to derive a contradiction. Define `c`, prove
   `P c`, then interpret or introduce the locale with that fact.
2. **Instantiation gap.** Abstract locale theorems do not establish the
   concrete result without an `interpretation`, suitable `[where ...]`
   instantiation, or named concrete corollary.
3. **False abstraction.** Prove invariance under abstract orders,
   enumerations, and strategies, or remove those parameters.
4. **Definition-statement drift.** Compare the theorem with
   `docs/PROOF_OVERVIEW.md`. Check for internal annotations presented as output,
   an operational `coverageTest` substituted for a declarative property, or a
   dropped well-typedness condition.
5. **Reusable statement shape.** Prefer `fixes`, `assumes`, and `shows` over
   `\<forall>x. P x \<longrightarrow> Q x` so callers can use `[where ...]` and
   `[OF ...]`.
6. **Sledgehammer use.** Try Sledgehammer on every non-trivial subgoal. Prefer
   `blast`, `auto`, and `meson`; retain `metis` only when reconstruction is fast
   in batch.
7. **Generalization through existing theory.** Replace ad hoc duplicates with
   relevant AFP or Isabelle results, including fixpoint, well-foundedness,
   independence-system, matroid, `Order.Lattice_Prelims`, and `HOL-Algebra`
   results.
8. **Two-stage review.** First review locale ordering, instantiation,
   abstraction, statement alignment, and statement shape. Then perform a
   hostile peer review that tries to exploit those assumptions.

Human review remains important for locale ordering, false abstraction, and
definition-statement drift. Proof status lives in `docs/PROOF_PHASES.md`; keep
lemma inventories out of this file.

## Status reporting

The build commands and slow-build diagnosis live in
`docs/ISABELLE_AGENT_NOTES.md`.

Status terms have exact meanings:

- **done**: the requested theorem exists, is proved, and passes the batch build.
- **landed**: the change passes its required checks but is not committed.
- **committed**: `git commit` has recorded the change.
- **in progress**: an obligation remains open or final verification has not run.

A green build does not complete a missing theorem or replace a semantic claim
with an executable example.

Use this compact progress format when it fits:

```text
Done:      <what is now true>
Reason:    <mechanism>
Blockers:  <remaining obligations>
Next:      <next proof or step>
```

## Accuracy

Verify claims against the repository or the cited primary source before stating
them. This includes:

- analyzer behavior or Goblint alignment;
- paper content or quotations;
- whether a definition or lemma exists;
- claims that correctness is inherited or follows from another layer;
- proof completion.

Flag unresolved uncertainty and name the file or source that must settle it.

## Host commands

Prefix every shell command with `rtk`; it filters supported tools and otherwise
passes commands through. Use `rtk proxy <command>` only when raw output is
required. Prefer `rg` for search and `fd` for file discovery.
