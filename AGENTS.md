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
- Before moving, splitting, or deleting anything in `src/Abstract_Interpreter/Framework`, read
  `docs/CORE_REFACTOR_PLAN.md` and work its step table in order; record
  what the build contradicts in its "Decisions and corrections" section.
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
instance uses the side-effecting verified solver. `analysis_domain` names five
selectable analyses -- `Sign_Analysis`, `Interval_Analysis`, `Int_Analysis`,
`Parity_Analysis`, `Congruence_Analysis`. Congruence is both selectable on its
own and the fourth component of `int_dom`, alongside sign, interval and parity.

The session dependency graph is:

```text
VIMP -+-> CFG ----+-> Compile ---------+
      |           |                    v
      |           +-> Framework ---> Exec -> Routing -> Result -> Nonrelational -> Analysis/* -+
      +-> Domain -------^                                                                      |
TD   ---> Solver -------^                                                                      v
                                                                                  CLI -> Codegen
                                                                                   +--> Examples/*
```

(`CFG` depends on `VIMP` only; `Framework` on `CFG`, `Domain` and `Solver`;
`Compile` on `CFG`; `Exec` on `Framework` and `Compile`. `Routing`, `Result`
and `Nonrelational` are the three `Analyses/Shared/` sessions described next.)

`Analysis/*` and `Examples/*` are each a family of sessions, not one session.
What every domain reuses lives under `src/Analyses/Shared/` as three chained
sessions, `Voblint_Routing -> Voblint_Result -> Voblint_Nonrelational`, with
`Voblint_Routing` parented on `Voblint_Exec`: routing
policies over a compiled program, the publication surface and source-level
endpoints, and the reuse locales
a non-relational domain interprets. `Voblint_Result` builds on `Voblint_Routing`'s
equations and contexts; `Voblint_Nonrelational` imports neither, and is chained
after them only so a domain inherits all three from one heap instead of
re-elaborating two.

`Voblint_Nonrelational` is the parent of `Voblint_Analysis_Sign`, `_Interval`,
`_Parity`, `_Congruence` and `_Int` (which also lists the four component domains
it reduces). `Voblint_Analysis_Relational` is the exception: it is parented on
`Voblint_Exec`, *below* the chain, so the pointwise reuse locales are
unavailable to it rather than merely unimported -- which is what makes
`Rel_Order_Domain`'s negative claim structural. Every theory under
`Shared/Nonrelational/` fixes a store as one value per variable; nothing that
does may move below this layer. `Voblint_Examples_<Domain>` is parented on that
domain's analysis session, so a domain's witnesses never pull a sibling domain
into their closure.

`Voblint_CFG` is the graph model and its activation-local collecting
semantics: what a soundness claim is stated *about*. It never mentions the
compiler, so the D/G soundness endpoints hold for an arbitrary CFG rather than
only for compiled ones, and the session boundary is what keeps that true.
`Voblint_Compile` is the VIMP-to-CFG compiler and its correctness (structural
invariants, forward simulation, and the bridge from a source run to a valid
local trace).

`Voblint_Domain` is what an abstract value and an abstract state are: the
sound-domain classes with their concretization, the dead-code lift, pointwise
states, and the bridge between those constructions. `Voblint_Solver` is the
strategy-tree equation language of the vendored side-effecting solver and its
monotonicity and post-solution
vocabulary; it never sees a CFG. `Voblint_Framework` is the D/G analysis framework:
local/global state selection, the transfer contract, the equation generator, and
collecting soundness for an arbitrary CFG, with no domain-specific content and
no compiler.
`Voblint_Exec` is the executable carrier and the transport of a solved
system from the solver's association-list states to the function-valued
states the framework is stated over. The `Voblint_Analysis_*` sessions thread
each concrete domain instance (Sign, Interval, ...) through them; the reuse
locales, the publication surface and the compile-dependent routed contexts live
under `src/Analyses/Shared/`. The dispatch config and the graph export are not
there -- no domain imports either, so both live in `Voblint_CLI` beside their
only consumers.
`docs/CORE_REFACTOR_PLAN.md` records why the split runs along these lines
and what remains to move.

Cross-session theory imports use qualified names.
The reusable soundness endpoints contain nothing domain-specific, so they sit
*below* the analysis family rather than after it, in `Voblint_Result`:
`Source_Activation_Sound` holds the domain-free source bridges
(`source_activation_sound`, `source_sound_from_ltr_collecting_cap`,
`source_completes_ltr_collect_exit`), and `Unit_DG_Analysis`'s
`unit_dg_analysis` states the context-insensitive endpoints (`source_sound`,
`completed_run_sound`, `result_node_sound`) once, so every domain inherits them
from an ancestor heap. Every context-insensitive result is an instance of that
locale. Each domain's own
instantiation of those endpoints -- the runtime API over an arbitrary
`imp_prog` paired with its production soundness theorems -- is `<Domain>_Entry`
in that domain's analysis session, because it depends on that domain and on
the shared chain and on nothing else. `Voblint_CLI` is then only the
dispatcher and the render surface: the soundness statements it does own are the
corollaries over `analyse` itself, which cannot live above the theory that
defines `analyse`.

The `Voblint_Examples_*` sessions contain executable runs, regressions and
GraphViz output, one session per folder under `src/Examples`. `Voblint_Examples`
itself is the residue plus the `Voblint` capstone: the witnesses that reach the
`AnalysisConfig` dispatcher or the GraphViz render surface import `Voblint_CLI`
and therefore see every domain, so they live together in `Voblint_Examples_CLI`
(`src/Examples/CLI`) instead of being spread back through the domain folders,
where they would recouple each domain's session to all of them. The store-only
check trio sits there too, so the three domains' witnesses read side by side.
That session is the capstone's *parent*, not a listed session: theories imported
from an ancestor come from its heap, while theories from a merely listed session
are re-elaborated in the importer.

`ROOTS` lists one directory per session. Isabelle rejects two sessions sharing
a directory, so a new session means a new directory, and every directory under
`src` that holds a `ROOT` owns exactly the theories beneath it that no nested
session claims.

A `theories` entry is a theory *name*, never a path: a slash there is a
malformed import and fails the whole session at load, so jEdit does not start
and the mistake presents as a dead editor rather than as an error in the file
that caused it. A subdirectory goes on the search path through `directories`
instead --- `directories "generated"` plus a bare `Sign_Assembly`.
`pixi run root-entries` checks that, that every `directories` entry exists, and
that every `.thy` on a session's search path is reached from something the
session builds; it needs no Isabelle.

The generated OCaml is compile-checked by actually compiling it: both
`codegen-regression` and `cli-build` run `ocamlfind ocamlopt` over
`codegen/generated/ml/Voblint_CLI.ml`, so a serializer defect fails those
tasks locally and in CI.

The procedural language includes calls, explicit returns, and runtime-only
restore/unwind commands. CFGs separate local `intra` edges from the `calls`
relation and use `FunctionEntry` and `FunctionResult` nodes. Concrete transfer
primitives live in `src/Program_Model/CFG/CFG_Transfer.thy`; activation-local semantics live
under `src/Program_Model/CFG/Collecting/`. The compiler that produces such a graph from a
VIMP program lives in `src/Program_Model/Compile/`; only `Procedure_Ownership` and
`Source_To_Trace` there mention both the compiler and the collecting
semantics.

## VIMP grammar pipeline

`grammar/vimp.yaml` is the sole source of truth for VIMP syntax. Two
generators realize it for two unrelated parser targets:

```text
grammar/vimp.yaml
       |
       +-- scripts/gen_vimp_menhir.py   -> cli/vimp_parser.mly, cli/vimp_lexer.mll
       +-- scripts/gen_vimp_isabelle.py -> src/Program_Model/VIMP/VIMP_Grammar_Generated.thy
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
   `src/Program_Model/VIMP/VIMP_Grammar_Generated.thy` -- all three are generated.
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

**A diagnostics read describes the buffer, not the file.** Reopening a file is
not evidence that jEdit reloaded it, so after any host write to a tracked
theory, compare the buffer against disk -- one `read_file` at a line the write
changed -- before believing any diagnostics. Both polarities of this have
already happened here in one session: a bulk host substitution that jEdit had
not picked up was certified clean and reached the user as two red theories, and
a regenerated file was read as still failing at byte offsets whose content no
longer existed. The result looks entirely normal in both directions, which is
what makes the check worth its one call.

**A theory that loads as `Draft.<name>` is not verified in its session.** A
draft node resolves imports without consulting the session, so its diagnostics
say nothing about whether the ROOT actually finds the file, and saving from one
rewrites same-session imports into session-qualified form. A theory whose ROOT
entry changed after jEdit loaded the session structure stays a draft until
jEdit restarts. Report content and wiring separately until the node name says
`<Session>.<Theory>`.

If an actual I/Q or I/R call fails, report it and request
`rtk ./scripts/start-both.sh` or `rtk ./scripts/start-ir.sh`. Do not substitute
a batch build for contextual proof development.

## New theories and the code-export module map

`export_code` in `src/Executable_Surface/Codegen/Export/Voblint_Codegen.thy` declares
`module_name Generated`, which puts the whole reachable program into one OCaml
module. Three modules are emitted -- that one, plus two that are HOL's own
serializer preludes, injected as literal target code rather than generated
from constants here:

```text
Generated    the entire reachable program: entry points, domains, solver,
             CFG, VIMP AST
Bit_Shifts   HOL runtime support, not a project theory
Str_Literal  HOL runtime support, not a project theory
```

`scripts/check_codegen_modules.py` holds the same three names; keep the two in
step.

The generated internals are monolithic and the export says so. Do not try to
recover per-theory modules by dropping `module_name`: OCaml's single-file
output emits modules in dependency order and cannot express a cycle, while the
executable state, the solver and the CFG instantiation depend on each other at
code level, so the serializer fails with

```text
Dependency "<some_constant>" -> "<your_constant>" would result in module
dependency cycle
```

naming two constants and no theory. Even a split Isabelle accepts can fail
later under `ocamlfind ocamlopt`, on a type-class dictionary field that
module-signature inference does not expose across the new boundary. Modularity,
if wanted, belongs in a handwritten OCaml facade over `Generated` -- a layer
this project does not have.

Because everything lands in one module, adding a theory whose constants are
reachable from an export root needs no export-side bookkeeping at all. What it
still needs is a regeneration: `scripts/check_codegen_modules.py`
(`pixi run codegen-modules`, and a pre-commit job) reads the checked-in export,
so it needs no Isabelle, and it reports theories that changed since the export
was last regenerated.

One thing does have to be named explicitly. The serializer keeps a datatype's
constructors out of the emitted signature unless it considers them public, and
an abstract type cannot be pattern-matched on. So a datatype whose *shape* the
handwritten OCaml depends on -- `lifted`'s `Bot`/`Lifted`, which `cli/main.ml`
matches to tell a dead point from a live verdict -- is an export root even
though nothing calls it.

The same applies to plain constants: `prog_table`/`prog_main`/`prog_procs` are
roots because the property AST driver names them, not because anything calls
them on the analysis path. This used to be slack -- under the old per-theory
split a symbol also went public whenever a sibling generated module called it,
and handwritten OCaml rode along on that. One module means one force: the root
list. `pixi run codegen-api` (`scripts/check_generated_api.py`, and a
pre-commit job) checks the consumers against the checked-in signature and names
the missing root; compiling them is the exact check and still runs in
`cli-build`, `codegen-regression` and `property-build`.

Sessions and `pixi run build` do not catch a stale export: only
`Voblint_Codegen` runs it, and it is the last session built. A change that
lands a new theory without regenerating `codegen/generated/` leaves the
breakage for whoever next runs a full build.

A named `dg_spec` is a construction-time description, never an exported
runtime value -- the Isabelle analogue of Goblint's `Spec` module. Its unknown
and global-key types occur only inside its transfer programs, never in an
argument that builds it, so it has no most general ML type and the serializer
rejects it with `includes a free type variable`. The rule is therefore
uniform, and applies to concrete domain specifications (`sign_conf_spec`,
`rel_order_spec`) exactly as it does to the generic builders in `DG_Spec`:

> **A named `dg_spec` that can reach code generation declares its own `_def`
> `[code_unfold]`, next to the definition.**

Whether a given spec would survive anyway -- because some enclosing definition
happens to unfold first -- is not worth reasoning about per domain. A
redundant declaration costs nothing; a missing one fails in generated ML, far
from the theory that caused it.

A second, differently-shaped hole in the same wall. A locale constant whose own
type does not mention the domain type variable carries a sort hypothesis the
code generator cannot see, so `declare <locale>.<const>_def [code]` is rejected
with a *warning* -- "Not a proper equation" -- and the equation is simply
absent. Nothing fails until the first `by eval` that reaches it, which then
reports "no code equations" naming a constant nobody wrote by hand.

> **A pipeline constant whose type omits the domain type variable has its body
> inlined into the code equations of the constants that use it, rather than a
> `[code]` declaration of its own.**

`routed_dg_pipeline.root_query :: 'c => imp_prog => pp * 'c` is the instance:
`solution` and `terminates` carry `solution_code`/`terminates_code`, which
spell the root query out. A registration that renames the pipeline's constants
through `defines` never meets this, because each renamed constant gets its own
equation from the interpretation; a call site that applies the pipeline
directly -- which is what a runtime parameter such as a call-string bound
forces, since no `global_interpretation` can fix it -- meets it immediately.

## Prose that claims a dependency must pin the theory

A bare `\<open>name\<close>` cartouche is unchecked. `scripts/check_thy_prose_refs.py`
only asks whether the name exists *somewhere* in the tree, which is all it can
ask: prose here cites other domains' counterparts constantly and on purpose
("mirroring Sign's own `analyse_sign_report_for`"), so a lint that demanded
every reference resolve in the citing theory's own import closure would flag
around a hundred correct sentences.

That leaves one failure it cannot catch: prose stating that a proof is *built
from* a fact the citing theory cannot see. `Interval_Entry` claimed its
node-soundness bridges were built from `ictx_activation_collect_sound_warrow`
for as long as `ictx_` was ambiguous -- a theorem only Int has, while the
bridges actually use `interval_conf_result_node_sound_warrow`. The lint passed
throughout, because the name existed in Int.

So distinguish the two kinds of citation:

- A **comparison** -- "mirroring", "as X does", "the counterpart of" -- may name
  anything, in a bare cartouche.
- A **dependency claim** -- "built from", "follows from", "discharged by" --
  names the owning theory with `\<^theory>\<open>Session.Theory\<close>`, which
  Isabelle checks and which therefore fails if the theory is not in scope. Use
  `\<^const>` for a constant, since that is checked outright.

The distinction is what a reader needs anyway: a comparison is orientation, a
dependency claim is something they may go on to rely on.

The pin narrows the failure but does not close it. `\<^theory>\<open>S.T\<close>`
is checked to be *in scope*, never to be the theory that owns the name beside
it, so a dependency claim can pin a sibling theory of the real one and pass
forever. `Int_Entry` pinned `Int_Analyses` for a constant defined in
`Int_Solver_Analyses`, alongside a source fact that did not exist and a premise
count that was one short. When a dependency claim names a constant, prefer
`\<^const>` for the constant itself --- that is checked outright --- and read
the pin as documentation of where to look rather than as a guarantee.

## Do not infer removability from local non-use

Before removing a parameter, name, key component, or locale assumption, check
three things:

1. whether it occurs in the fully expanded statement or constructed value;
2. whether it is consumed through locale inheritance, interpretation,
   abbreviation, or another transitive dependency;
3. whether callers use it to distinguish instantiated objects, even when the
   current body does not inspect it.

A component can be load-bearing as identity, routing information, or inherited
configuration while the declaration in front of you never applies it. A lemma
about `f gs x` needs `gs` whether or not the lemma inspects it, and a locale
that forwards a parameter to a parent needs it whether or not its own body
mentions it again. Local body inspection and raw occurrence counts are
discovery signals, not evidence.

The same failure mode produced three separate defects here: `enter_local`
(a deleted constant left an assumption quantifying over an arbitrary
function), `gk` (a deleted datatype let a signature silently rebind to another
theory's type of the same name), and `gs` (an audit read "not applied in the
body" as "removable" for a locale parameter its parent consumes nine times).

## Where the global-variable predicate may appear

`gs :: vname => bool` is VIMP's declaration of which names are global. It has
three legitimate roles: naming the concrete call/return semantics an abstract
answer must over-approximate (`call_enter`, `combine_collect`, `valid_ltr`),
implementing the ownership-split specification, and keying the executable
carrier's locations. It is not a framework parameter, and the invariant is:

> `gs` exists only above or at the transfer boundary. Below it, operations may
> consume an already-classified location but must never classify a name.

The checkable form of that is narrower and has no exceptions:
`Framework/Constraints` must not depend on ownership-split semantics.
`CFG_Enumeration`, `DG_Constraint_Trees` and `DG_Keyed_Generator` mention `gs` zero
times, as do `DG_Spec` and `DG_Manager`.

The boundary statement above has exactly one known exception, and it is
deliberate. `resolved_st_is_bot` classifies below the boundary because the
quotient's equality observes every tagged location while the concretization
reads back only the one `gs` selects for each name; a bottom test that must
agree with the readback has to filter the others, which `canonical_location`
names. A carrier holding `Local_Location` and `Global_Location` is not itself
evidence of leakage -- a join, order or widening that needed `gs` to
reconstruct the classification would be, and none does. The exception is
expected to disappear when variables carry resolved declaration identities
rather than textual names.

## Deleting an API

Isabelle does not reject every surviving use of a removed name. In a term it
does; but inside `assumes`, `fixes`, and theorem statements an unknown
lowercase identifier is a legal free variable, so a locale whose assumption
cites a deleted constant keeps building -- while that assumption silently
stops constraining anything and now holds for an arbitrary function of that
name. Deleting `DG_Transfer_Combinators.thy` did exactly this to three
`call_fwd_ok` assumptions via `enter_local`, and every session stayed green
for several rebuilds afterwards. This is the `false abstraction` error of the
autoformalization audit below, and no batch build can see it.

So a deletion is not finished when the build is green:

1. Search for consumers of every removed name *before* deleting, including
   inside `assumes` and theorem statements.
2. Append the removed names to `scripts/retired_identifiers.txt`.
   `pixi run retired-identifiers` then fails on any that come back. Remove a
   name from that list -- explicitly, in the same commit -- if a later design
   deliberately reuses it.
3. Run `pixi run locale-parameters`. It reports any identifier left free in a
   locale assumption anywhere in `src/`, which is the general form of the same
   defect and catches names that were never constants here at all.
4. Run the full batch build over the leaf sessions, not just the session you
   edited. A session that fails cancels the rest of its own theories, so one
   red session hides every later one: a build that stops early has told you
   nothing about what follows it.

## Regression discipline

Whenever a change fixes a bug, changes semantics, or introduces a feature,
add or update a regression test that locks in the new behavior -- an
executable witness whose assertion pins the corrected/intended result, not
the one it replaces. Use whichever regression layer the change actually
touches: a `by eval` lemma in `Example_Analysis_Dispatch_Regression.thy` (or the nearest
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
