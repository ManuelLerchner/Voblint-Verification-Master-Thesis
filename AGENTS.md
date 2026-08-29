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
- Before auditing or cleaning up a session, read
  `docs/SESSION_CLEANUP_PLAYBOOK.md`: the procedure, the patterns that paid
  off, and the traps that each cost a rebuild.
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
VIMP -> CFG -> Compile -> Core -> Analysis -+-> Formalization -+
                                            |                  v
                                            +----------------> CLI -> Codegen
                                                                +---> Examples
```

`Voblint_CFG` is the graph model and its activation-local collecting
semantics: what a soundness claim is stated *about*. It never mentions the
compiler, so the D/G soundness endpoints hold for an arbitrary CFG rather than
only for compiled ones, and the session boundary is what keeps that true.
`Voblint_Compile` is the VIMP-to-CFG compiler and its correctness (structural
invariants, forward simulation, and the bridge from a source run to a valid
local trace).

`Voblint_Core` is the abstract framework: domains, constraint systems, and the
TD solver bridge, with no domain-specific content. `Voblint_Analysis` threads
each concrete domain instance (Sign, Interval, ...) through it.

Cross-session theory imports use qualified names.
`Voblint_Soundness` contains the reusable soundness endpoints and the
per-domain, per-context instantiations the CLI dispatches to, so it is not a
leaf: `Voblint_CLI` imports it, and the export in `Voblint_Codegen` reaches
through it. `Voblint_Examples` contains executable runs, regressions, GraphViz
output, and the `Voblint` capstone.

`ROOTS` lists nine session directories, one per session in the graph above.

The generated OCaml is compile-checked by actually compiling it: both
`codegen-regression` and `cli-build` run `ocamlfind ocamlopt` over
`codegen/generated/ml/Voblint_CLI.ml`, so a serializer defect fails those
tasks locally and in CI.

The procedural language includes calls, explicit returns, and runtime-only
restore/unwind commands. CFGs separate local `intra` edges from the `calls`
relation and use `FunctionEntry` and `FunctionResult` nodes. Concrete transfer
primitives live in `src/CFG/CFG_Transfer.thy`; activation-local semantics live
under `src/CFG/Collecting/`. The compiler that produces such a graph from a
VIMP program lives in `src/Compile/`; only `Procedure_Ownership` and
`Source_To_Trace` there mention both the compiler and the collecting
semantics.

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

The entry procedure is an ordinary `proc_rep` entry, not a separate field:
`imp_prog` carries only `proc_rep` and `declared_global_vars`, `mk_program`
conses `(prog_main_name, formals = [], body = m)` onto `proc_rep`, and
`prog_main` is the lookup `main_body (prog_table p)`. This is a settled
representation choice, not part of this grammar migration.

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
the one it replaces. Use whichever regression layer the change actually
touches: a `by eval` lemma in `Example_Analysis_Dispatch.thy` (or the nearest
sibling `Example_*.thy`) for solver/domain behavior, a `tests/regression/`
`.vimp` fixture for CLI-observable behavior, or both when a fix is
code-generated from Isabelle into `codegen/generated/` and therefore visible
at the CLI too.

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

## Style

Baseline: the Isabelle Community Conventions
(<https://isabelle.systems/conventions/>) and Gerwin Klein's style notes
(<https://proofcraft.org/blog/isabelle-style.html>, `-part2`). The rules
below restate the parts that matter here and record where this project
deviates. When a rule here conflicts with the baseline, this file wins.

### Layout

- Lines <= 100 symbols. Three things are exempt because they cannot be broken:
  generated theories (`VIMP_Grammar_Generated`), whose layout the generator
  owns; URLs in comments; and `mixfix` annotation strings. Two-space indent. One blank line between top-level
  declarations. `proof`, `next`, `qed` flush left within their block.
- Theories <= 1500 lines. Split along a concern boundary (a domain, a proof
  layer, a generator), never by line count alone. One concern per theory;
  a theory that exists only to fix import order is merged into its consumer.
- Function equations one per line; `|` consistently at line start.
- A definition or `fun` header and its name share a line; the body is
  indented under it.

### Statements

- `fixes`/`assumes`/`shows` over object-logic `\<forall>x. P x \<longrightarrow> Q x`, so
  callers can instantiate with `[where ...]` and `[OF ...]`. A theorem with
  `assumes` puts a line break after its name.
- `obtains` for existential conclusions and case distinctions.
- Do not mix object and meta logic in one statement.
- Decide a normal form per concept and state every lemma in it (e.g. always
  `le_fun_def`-unfolded pointwise order, or never).
- Drop quantifiers, parentheses, and type annotations the reader and Isabelle
  infer.

### Naming

- Constants, lemmas, locales: `lower_snake_case`. Datatype constructors and
  theories: `Capitalized_Snake_Case`. Sessions: `Voblint_<Session>`.
- A lemma name reads its conclusion left to right in the library vocabulary:
  `_eq_`, `_le_`, `_iff_`, `_mono`, `_sound`, `_left`/`_right`, `_self`.
  Hypotheses follow `_if_` (`le_if_lt`). Introduction, elimination and
  destruction rules end in `I`, `E`, `D`.
- Locale interpretations and `lemmas` re-exports name the concrete instance
  (`ivl_exec_sound`, not `sound_1`).
- Variables follow the library: `xs` for lists, `S`/`A` for sets, `P`/`Q` for
  predicates, `f`/`g` for functions. Avoid `c`, `inv`, and other names that
  resolve to imported constants.

### Attributes

Baseline: <https://isabelle.systems/conventions/theorem_attributes.html>.
Its governing rule is *do not declare something `simp`/`intro`/etc. unless you
are sure it is a good idea*: a declared rule must take an obvious step that
does not surprise the reader, and classical rules matter less than `simp`
rules because conceptually non-trivial reasoning reads better applied
explicitly. Everything below refines that; the two deviations are marked.

- Only named lemmas carry attributes.
- A lemma is `[simp]` when its LHS is already in simp normal form and the
  RHS is clearly simpler. Prefer unconditional equations; a conditional one is
  worth tagging only when its precondition is cheap relative to how often the
  rule fires. A one-step destruct or introduction off a definition is `[dest]`
  or `[intro]`. Tag by default when the shape fits; leave bare when two rewrite
  directions compete, the rule can loop, or the step is conceptually
  non-trivial and should stay visible in proofs.
- When a new constant is introduced, prove its simple `simp` rules with it.
  When a family of rules recurs across theories, give it a named collection or
  `lemmas` bundle (`call_info_of_simps`, `mk_program_simps`,
  `wf_compile_input_simps`) rather than repeating the list per call site.
- Before tagging `[simp]`, check for an existing simp rule with an
  overlapping LHS that stops at a different normal form. Fix a
  non-confluent pair at the algebra level with a bridging lemma; once
  confluent, delete any lemma that only restated a special case.
- **A rule named as a rule carries its attribute** (deviation: the baseline
  would leave this to judgement). The naming convention below
  ends introduction, elimination and destruction rules in `I`, `E`, `D`; a
  lemma with one of those names and no `[intro]` / `[elim]` / `[dest]` is
  either mis-named or withheld from the automation it was written for. Tag it,
  or rename it to say what it really is. The one standing exception is a
  multi-conclusion `D` bundle cited by index (`wf_compile_inputD(8)`): tagging
  it `[dest]` would spawn every conclusion from every occurrence of its
  premise, so those stay bare and stay explicitly cited.
- **Every `inductive` predicate carries its inversion rules** (deviation: the
  baseline states no such requirement). Give it one
  `inductive_cases` per constructor shape the proofs case on, named
  `<pred>_<Shape>E`, and tag it: `[elim!]` when inverting that shape is
  deterministic, plain `[elim]` when a case recurses into a subterm (`Seq`,
  `If`, `While`, `Call`) so the classical reasoner does not chase the nesting
  eagerly. A predicate without them forces every consumer to hand-roll
  `cases rule: <pred>.cases`, and turns proofs that should be one `auto` into
  a case-per-constructor `proof` block --- `control_at_initial` was 25 lines
  of exactly that before `control_at` had its rules.
- **Declare `<pred>.intros [intro]` when the clauses are cheap to search** ---
  their premises are memberships, equations, or smaller instances of the same
  predicate (`pstep`, `intra_step`, `cstep`, `control_at`, `stack_repr`).
  Leave them undeclared when picking the clause is the substance of the proof
  rather than bookkeeping: `csim` and `valid_ltr` keep their introduction rules
  explicit, because which constructor applies is what their theorems are
  about.
- Keep attribute changes local with `context`/`bundle`; avoid
  `[simplified]`, `[rule_format]`, and global `declare ... [simp del]`.
- Never check in `sorry`, `back`, or an unattributed `sledgehammer` call.

### Proofs

- Decide the shape first. One-step goals: `by ...`. Otherwise structured
  Isar, sketched top-down with named subgoals, hard obligations hoisted
  into helper lemmas. Do not switch from `apply` to `proof` mid-proof.
- Target `by (induction ...) (auto simp: ...)` for structural inductions.
  When cases need hand-picked rule sets, promote the recurring rules to
  global `[simp]`/`[intro]`/`[dest]` lemmas instead of repeating them per
  case. A case that still resists one line becomes a helper lemma; do not
  widen `auto` or `simp` to force it.
- Unrestricted `auto` only terminally. Prefer `simp only:` and `auto simp:`
  with an explicit rule set over unbounded automation on large imported
  sets.
- Prefer named case-split or decomposition lemmas with `by (rule ...)` or
  `cases rule:` over `auto elim!:` on inductive predicates.
- Prefer structured Isar with explicit `show` subgoals over long
  `[OF ...]` chains when facts must align exactly.
- Sledgehammer on every non-trivial subgoal, timeout <= 15 s. Paste back
  `blast`, `auto`, `meson`. Keep `metis` and `smt` only after the batch
  build confirms fast reconstruction.
- `unfolding` over `simp add: foo_def` to unfold a definition.
- Comment any step that takes longer than about a minute.
- If a valid obligation is difficult, repair the proof or strengthen its
  invariant. Before changing the architecture, establish that the intended
  theorem is false with a small `nitpick [timeout=5]` counterexample.

### Locales

- Theorems inside locales use locale-qualified constants; callers outside
  need the fully applied global shape. Before `callee[OF ...]`, compare
  interpretation-local premises with fully applied global premises.
- Surface concrete corollaries through global definitions, small expansion
  lemmas, or an `interpretation` block, not repeated unfolds.
- A parameter threaded through many definitions and lemmas of one layer is
  a locale parameter, not an explicit argument, unless the layer is
  interpreted at many distinct values.

### Comments

- **Every theory opens with an orientation block.** Three to ten lines, after
  the `section` heading, answering: what question does this file settle, what
  is its main result, and what local vocabulary must the reader already have.
  This is the one `text` block exempt from the no-restating rule below, and
  the only one a newcomer is guaranteed to read.
  - Write it operationally, in plain words, the way `VIMP_Proc` does: "a call
    evaluates its actuals in the caller store, binds them in a fresh
    activation, and pushes a frame". Never open with a signature --- a reader
    who does not yet know the argument order learns nothing from
    `f a b c d relates ...`.
  - Define a term the first time the session uses it, in the same sentence.
    Words like *residual*, *fragment*, *located*, *activation* are local
    jargon, not English; a header that explains one of them with the others
    is circular.
  - The `section` heading states the question, not the machinery: "Where a
    partly executed command sits in the graph" over "Located control inside a
    compiled procedure fragment".
- Beyond that block, comment only what the definition or statement does not
  already say: a non-obvious design decision, a Goblint-alignment rationale, a
  proof step that surprises. A `text` block that restates the lemma it
  precedes is deleted.
- Explain why, not what. Timeless: describe the theory as it stands, not
  project history, removed theories, former names, migration plans, or
  staged/future work ("TODO", "still needs", "Stage 1").
- No file links: no paths, no `\<^file>`, no `docs/*.md` citations. Name
  another theory with `@{theory Qualified.Name}`; state everything else
  inline. Comparisons to a still-existing sibling definition are fine.
- Exposition uses `section`/`subsection`/`text`, one short `text` per
  section at most; `(* *)` only inside proofs.
- A session's `README.md` carries what no single theory can: the vocabulary
  table, one worked example carried end to end, and the shape of the
  dependency graph. A reader who cannot start from the README will not be
  rescued by the theory headers.

### Workflow

- **I/Q inner loop, batch outer gate.** Debug one failing command through
  `get_diagnostics` and `explore`. Run the batch build once the complete
  task is file-clean, when the user requests it, or at the commit gate.
- **I/Q is not completion.** Empty diagnostics mean ready for batch, not
  proved. **Batch is completion.** Show the green build log before calling
  proof work done.

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
