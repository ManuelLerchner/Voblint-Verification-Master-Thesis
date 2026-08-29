# Session cleanup playbook

How the per-session audit-and-clean pass works, what it found in the sessions
already done (VIMP, then CFG), and the traps that cost a rebuild each. Read
this before auditing the next session (Core, then Analysis, ...).

## Procedure

1. **Survey, read-only.** One agent per session. Deliverables: a session map
   (per theory: role, definitions, main vs helper lemmas, attributes), dead
   or misplaced material, proof-automation candidates (longest proofs first),
   threading that a locale would remove, file scope, comment density. Use
   `rg -w <name> src cli --glob '!*.thy~'` for usage counts.
2. **Act on the ranked verdict**, VIMP-internal edits first, downstream
   ripple second. Every theory edit goes through I/Q; host tools only for
   closed, non-theory files and for generating exact hunks.
3. **Gate.** `AFP=$HOME/afp/thys pixi run build`, then `pixi run codegen`,
   `pixi run cli-test`, `pixi run property`. Commit only after all four.

Scripts that helped (recreate under the scratchpad as needed):

- a proof-length ranker: each `lemma`/`theorem` up to the next top-level
  command, sorted by line count, flagging `induct` and `simp` counts;
- a style-metrics pass: comment share, lines over 100 *symbols*
  (count `\<...>` as one), `metis`/`smt`/`sorry`, files over 1500 lines;
- a hunk generator: compute the target text on the host, diff it against
  the buffer, emit minimally-unique `old`/`new` blocks, apply each as an
  I/Q `str_replace`.

## Patterns that paid off

- **Wrapper definitions over library or record constructors are dead
  weight.** `proc_decl_of xs c` was `\<lparr>formals = xs, body = c\<rparr>`;
  every site unfolded `proc_decl_of_def`. Deleting it removed 21 unfold
  citations and the two selector lemmas that existed only to service it.
  The OCaml side constructs `Proc_decl_ext (xs, c, ())` directly.
- **Polymorphic abbreviation instead of a concrete definition plus an
  abstract copy.** `bind_formals` (concrete) and `bind_formals_abs`
  (abstract) were the same `fold` over `zip`. One abbreviation at type
  `'v` serves both; `fold`/`zip` library simps apply, and no `_def` needs
  unfolding.
- **Abbreviation instead of a definition when nothing needs the constant
  opaque.** `pcompletes gs \<Pi> c s t` as an abbreviation for
  `psteps gs \<Pi> (c, s, []) (SKIP, t, [])` kept the name and its lemma
  family and deleted every `unfolding pcompletes_def`.
- **One multi-conclusion destruction lemma instead of N projections.**
  `wf_source_programD` (eight `and`-conclusions, `by blast+`) replaced
  seven lemmas; the CFG mirror became
  `lemmas wf_compile_inputD = wf_source_programD[OF ...]`, cited as
  `wf_compile_inputD(k)`.
- **Applied-form simp rules for opaque definitions.** `enter_state_apply`
  removed `enter_state_def` from 17 downstream sites. Check for the same
  gap whenever a definition is a lambda.
- **One always-on rewrite can force a whole idiom.**
  `pcompletes_iff_small_termination [simp]` rewrote every `pcompletes`
  goal into an existential, which is why downstream proofs kept writing
  `unfolding pcompletes_def`. Delete rules that fight the intro lemmas.
- **Collapse parameters that are provably ignored.**
  `storage_global p owner` never depended on `owner`; three theories each
  re-proved `storage_global p _ = declared_global p`. `declared_global p`
  everywhere.
- **Split by concern, and import the narrow theory.** `VIMP_Program`
  (record + lookups) split from `VIMP_Notation` (parser ML), so
  `Compile_Invariants` and `Exec_Placement` no longer import the
  `parse_translation` to reach `imp_prog`.
- **Restate `fun` equations with `case` when a sibling already does.**
  `com_vnames (Return e)` with `case e of` let `finite_com_vnames` collapse
  from 40 lines to `by (induction c) (auto split: option.splits)`.
- **Hoist the step lemma the long proofs keep re-deriving.**
  `pstep_Call`/`pstep_Call_parameterless` turned five 20-50 line call
  proofs into one-to-three lines each.

## Traps

- **Grep cannot see simp-set uses.** A `[simp]` lemma with zero textual
  citations may be load-bearing (`special_result_ex` broke `CFG_Def`;
  `combine_collapse`/`combine_nest_*` were restored pre-emptively). Delete
  attributed lemmas only if they restate the definition; otherwise keep
  them and let the build decide.
- **Transitive imports.** Seven Example theories used `program { ... }`
  through `Compile_Invariants`'s import of `VIMP_Notation`. A theory that
  uses a quotation must import `VIMP_Notation` itself.
- **`OF` on a premise `\<Pi> p = Some ...` reports "multiple unifiers"**
  (`?\<Pi> ?p` is not a pattern). Use `using p by (rule X)` so the
  conclusion fixes `\<Pi>` and `p` first, or `X[where \<Pi> = \<Pi> and
  p = p, OF p]`.
- **`fold` unfolds to `\<circ>`.** `fold.simps` gives
  `fold f (x # xs) = fold f xs \<circ> f x`; add `comp_apply` (and
  `prod.case` for tupled functions) when unfolding by hand.
- **I/Q `str_replace` with an empty `new_str` is a silent no-op**
  (`bytes_written: 0`). Delete a block by replacing it together with the
  following line.
- **I/Q buffer sync.** `save_file` without a path flushes every open
  buffer, including ones whose disk copy changed underneath (it recreated
  a deleted theory twice and reverted an import). Save by path. Files
  opened with `view = false` reject `write_file`; open them in view.
- **A wedged I/Q buffer will overwrite host edits later.** When `save_file`
  or `open_file` hangs and is killed, the buffer still holds its old text; a
  later flush writes that over whatever the host wrote in the meantime. It
  silently reverted a 28-site rename in one theory. If I/Q stops responding,
  do not fall back to host edits on a file it still has open --- restart I/Q
  first, or verify with `git diff` before building.
- **Edits landing mid-build** abort the build with "Incoherent digest";
  finish the edit batch, then build.
- **Style measured in symbols, not bytes.** `\<Rightarrow>` is one column
  in jEdit; measure line length after collapsing `\<...>`.

## Traps from the parameter-deletion pass

- **Deleting a parameter is an arity change, so check arity, not spelling.**
  After removing `main_name`/`main`, a repo-wide "no bare `main_name`
  remains" grep returned zero while four call-string `interpretation`s still
  supplied the pair, spelled `"STR ''main''" nest_main`. The oracle is
  Isabelle's *More arguments than parameters in instantiation of locale*,
  not a token search. Enumerate the constant's call sites by head name and
  compare each site's argument count against the definition.
- **An unused `fixes` is legal, so the build will not find dead parameters.**
  Both routed-context locales kept `main_name :: pname and main :: com` in
  their `fixes` long after nothing read them, and every session stayed
  green. This is audit item 3 (false abstraction); only reading the locale
  header finds it.
- **Anchor a deletion script on the head constant, never on the argument.**
  A pass keyed on the *name* `main_name` stripped the second argument from
  twenty `scope_locations p owner` calls, which take a genuine owner. The
  line-count and line-length assertions passed straight through the damage.
  Assert on the head's expected arity, and diff every changed line.
- **`str.split(lit)` then `lit.join(parts[1:])` loses one separator.** It
  rewrote `by (rule compile_prog_calls_empty)` to `by ()` in seven files.
  Prefer `str.replace` for literal substitution; if a split is unavoidable,
  assert the rejoined text still contains the literal N times.
- **A `<cfg>_compile [simp]` folding rule defeats `unfolding <cfg>_def`.**
  Several examples declare `compile_prog ... = <x>_cfg` as `[simp]`; a proof
  that opens the definition and then calls `simp` has it folded straight
  back, leaving the goal untouched. Use `simp only:` with the definition and
  the rules you want.
- **A green build does not mean the migration is finished.** The build
  abandons a session at its first failing theory, so each fix exposes only
  the next layer. Error counts fell 40 -> 40 -> 15 -> 2 over five passes on
  the same session; budget for the tail rather than reading the first clean
  prefix as done.

## VIMP status after the pass

1894 -> 1019 lines across eight hand-written theories (`VIMP_Settings`
deleted, `VIMP_Program` added), plus the 220-line `VIMP_Grammar_Generated`
the generator owns. No `metis`/`smt`/`sorry`. Explicit `gs`/`\<Pi>`
threading kept: the CFG/Core locales already take `gs` as a parameter and
a VIMP-level locale would need ~20 interpretations to save two words in
~30 statements.

Both items left for the CFG pass are done: `wf_compile_input_simps` grew the
leaf definitions, and the nine non-Example `VIMP_Notation` importers now
import `VIMP_Program`.

## Patterns from the CFG pass

- **Two greps can settle a session boundary.** `rg -c compile Collecting/*`
  returned 0 and `rg -c 'valid_ltr|ltr_collect' Compiler/*` returned 0, which
  proved the CFG session was a diamond (graph model at the bottom, collecting
  semantics and compiler as independent branches, two bridge theories at the
  top) rather than a stack. That is what made the `Voblint_CFG` /
  `Voblint_Compile` split obvious and safe -- no reading of 6500 lines. Do this
  before proposing any move: the natural-sounding split ("lift the collecting
  layer into its own session between CFG and Core") was impossible, because a
  theory *inside* CFG already depended on it.
- **A session boundary is the only thing that enforces a layering claim.** The
  soundness endpoints are stated for an arbitrary CFG, not only compiled ones.
  Nothing but the `Voblint_CFG` boundary stops a later edit from importing
  `compile` into `LTR_Def` and quietly narrowing every one of them.
- **One named simp bundle instead of N selector lemmas.** `call_info_of_simps`
  (four `ci_*` projections) and `mk_program_simps` (four `prog_*_make`
  projections) each collapse to one `[simp]` lemma with N conclusions, proved
  `by (simp_all add: X_def)` or `by (force simp: ...)+`. The `D`-lemma pattern
  for `assumes`/`shows` facts; this is its equational twin.
- **`Code.abort` instead of a plausible default on an unreachable branch.**
  `call_formals` returned `[]` for an undeclared procedure and `cfg_exit`
  returned the entry node for a non-procedure entry -- both unreachable behind
  the CLI's `wf_program_compile_input_exec` gate, but a silent default turns an
  invariant violation into valid-looking data. `Code.abort (STR ''...'')
  (\<lambda>_. old_default)` keeps the HOL function total, leaves every proof
  unchanged, and generates `failwith` in the OCaml. Reserve it for
  *invariant violations*; a user-facing error belongs in the CLI's gate, which
  already returns a bool and exits 4.
- **The `_origin` lemma for a list-recursive compilation pass.** "Every edge of
  `compile_procs` comes from one declared member's `compile_proc` fragment,
  compiled inside the pass's counter range" (`compile_procs_intra_origin` and
  its `calls` twin) replaced five ~25-line list inductions with two-line
  corollaries and removed all eight `metis prod_cases3` sites in one move.

## Traps from the CFG pass

- **`unfolding <named set>` is not `simp: <named set>`.** `unfolding` rewrites
  once, up front. If a `fun` in the goal generates fresh occurrences of those
  constants *during* the proof, they are no longer unfoldable. `wf_source_com`
  is a `fun` whose default simp equations introduce `special_table` after the
  `unfolding` step has run, so the leaf definitions have to be in the `simp:`
  set. Cost: one full Examples rebuild.
- **An OOM kill looks nothing like a proof failure.** A batch build running
  alongside a live PIDE/jEdit session was killed (`Killed: 9`, exit 137) with
  zero `***` lines in the log. Read the log tail, not the exit code, before
  concluding a proof broke -- and do not run the batch gate and an interactive
  session at once.
- **There is a second OCaml harness.** `cli-build`/`cli-test` compile `cli/`,
  but `codegen-regression` compiles `codegen/regression/ocaml/main.ml`.
  Deleting an Isabelle constant that only that harness used stayed green
  through the Isabelle build, `cli-test` and `property`, and failed only in
  `codegen-regression` -- one commit later.
- **`fastforce` on an existential goal with arithmetic side conditions can
  fail to terminate.** Build the witness explicitly (`have "P a \<and> ..."`
  then `by blast`) rather than reaching for `smt`, which the style rules ban.

## Patterns from the Compile review pass

- **Two predicates that always travel together are one predicate.** Every
  `csim` constructor carried `compiled_at` (this fragment is in the graph at
  this offset) next to `proc_activation` (this fragment is procedure `p`'s
  body), and every construction site proved both. Folding the second into the
  first removed a premise from three constructor rules, deleted a definition
  and its destruction lemma, and shortened every `[OF ...]` chain through
  `csim.induct`. Check for the pattern by grepping the weaker predicate: if it
  has no site where it appears alone, it is not a separate concept.
- **A second structural induction over the same case tree is a missing
  bridge lemma.** `compile_control_at_SKIP_exit_path` proved "a located `SKIP`
  reaches its continuation" as an `intra_path`; `control_at_skip_to_exit`
  re-proved it, case for case, as a `star cstep`. The real content is
  `intra_path g x y ==> star (cstep gs g) (fst x, snd x, stk) (fst y, snd y, stk)`
  --- graph-generic, eight lines, and it belongs in `CFG_Exec` next to `cstep`.
  The second induction then collapses to one `using ... by simp`. Cost: 40
  lines and one duplicated case analysis.
- **Derive the specialized inversion lemma from the general one.**
  `pstep_seq_after_seq_restore` (stepping `Seq inner Restore` down a
  `seq_after` spine) repeated the whole `rev_induct` of
  `pstep_seq_after_headD`. It is that lemma at `w = Seq inner Restore` plus one
  `Seq` inversion --- six lines instead of thirty.
- **A configuration-shaped predicate that reads one component.**
  `source_wf :: com * store * frame list => bool` case-split its argument and
  looked only at the command. `return_safe :: com => bool` says the same thing,
  states the exported `csim_step` premise honestly, and stops callers from
  building a dummy store and frame list to ask the question.
- **Unused `assumes` survive because nothing type-checks them away.**
  `csim_call_base` took `length actuals = length (formals decl)` and
  `distinct (formals decl)`; neither appeared in the proof body, and both were
  threaded in by every caller. A third, `special_table q = None`, was derivable
  from two other premises. Read the proof body against the assumption list
  before adding one more.
- **Theory boundaries drift at the last lemma, not the first.**
  `Simulation_Relation` had grown a preservation theorem
  (`csim_returning_completion`) and its frame-stack plumbing; the symptom was a
  header in `Simulation_Preservation` promising three completion theorems when
  `csim_step` dispatches four ways. When a header miscounts what the file
  holds, check whether the file is still holding it.
- **Global `[intro]` / `[elim]` on a predicate that unpacks existential
  compiler evidence** makes proof search unpredictable for no gain: the
  explicit proofs already wrote `by (rule compiled_atI ...)`. Tag structural,
  terminating rewrites; leave evidence-unpacking rules bare.

## Patterns from the naming and structure pass

- **A free variable named like a constant.** `source_global` was used 469 times
  across four sessions and defined nowhere -- every theorem mentioning it was
  universally quantified over an arbitrary globals predicate, which is sound and
  more general than it reads. VIMP and CFG already called the same parameter
  `gs`. Before renaming, split each file into top-level command blocks and check
  none contains both names: two did, and merging them there removed generality
  no caller used. A grep for a definition is the cheap test --- if a name that
  looks like a constant has none, it is a variable.
- **Test a `[simp del]` exception by deleting it.** `declare pstep.Seq2
  [simp del]`, three lines under the blanket `pstep.intros [simp, intro]`, had no
  comment saying why. The build is green without it, so the exception was stale.
  An undocumented attribute exception is worth one build to check.
- **Split a long theory where the dependency graph already cuts.** `VIMP_Proc_to_CFG`
  was 1272 lines over five concerns. Listing what each half declares and grepping
  who consumes it showed one clean cut: everything from call-source uniqueness
  onward is *what is true of the compiled graph*, consumed by 38 files but almost
  all of them transitively through `Compile_Invariants`. Only five direct
  importers needed repointing. `Compile_Wellformed` is that half (690 lines) and
  the compiler theory drops to 544.
- **Statement order was in the wrong theory.** `com_stmt_post_order` and its
  three characterization lemmas sat in the compiler theory but are consumed only
  by `Compile_Invariants`'s `prog_stmt_post_order`, the CLI's source-position
  map. Moving them puts the whole statement-order story in one place. Watch the
  order when moving into an existing section: a `text` block referring to
  \<^const> a definition must come after it, not before.

## Style-guide compliance, measured

The baselines are the Isabelle Community Conventions
(<https://isabelle.systems/conventions/>) and Gerwin Klein's two style posts
(<https://proofcraft.org/blog/isabelle-style.html>, `-part2`). Both reduce to
rules a script can check; run these before declaring a session clean.

VIMP, CFG and Compile pass all of them: no `sorry`, no `axiomatization`, no
unnamed global attributes, no `[simplified]` / `[rule_format]`, no implicit
`apply rule`, no `apply (auto; ...)`, no apply scripts at all, no
`sledgehammer`, no `metis`, no `smt`, and no theory over the 1500-line cap.
Every `inductive` predicate carries tagged inversion rules, and every lemma
named `...I` / `...E` / `...D` carries its attribute apart from the two
multi-conclusion `D` bundles cited by index.

The sessions after them do not, and this is the measured scope of their
passes:

| | Core | Analysis | CLI | Examples |
| --- | --- | --- | --- | --- |
| theories / lines | 52 / 25407 | 62 / 25490 | 6 / 4129 | 64 / 18198 |
| `metis` | 45 | 14 | - | 5 |
| `smt` | - | 4 | - | - |
| `apply` lines | 61 | 41 | - | 9 |
| `[rule_format]` | 4 | 1 | - | - |
| `apply (auto; ...)` | - | 4 | - | - |
| implicit `by rule` | 2 | - | - | - |
| theories over 1500 lines | 5 | 3 | - | 1 |
| lines over 100 symbols | 381 | 458 | 470 | 486 |
| theories with no orientation block | 3 | 6 | 2 | 6 |

The largest theories are `Example_Interval_Placement` (2901),
`DG_Framework` (2472), `DG_Soundness` (2317), `Exec_St` (2231) and
`Abstract_Domain` (2110). Splitting those is the structural half of the Core
pass; retiring `metis` and the apply scripts is the proof half.

## CFG and Compile status after the pass

The 6573-line `Voblint_CFG` became two sessions: `Voblint_CFG` at 1559 lines
across 8 theories (graph model, `CFG_Exec`, `Collecting/`) and the new
`Voblint_Compile` at 5086 across 9 (compiler, forward simulation, the two
bridge theories). Every theory took its name from what it states rather than
from the pass that produced it, and the two over-long ones were split along a
concern boundary:

```text
Control_Residual            -> Simulation/Residual_Location
Control_Emit                -> Simulation/Residual_Edges
Control_Simulation          -> Simulation/Simulation_Relation   (2507 -> three theories)
Control_Simulation_Forward  -> Simulation/Simulation_Preservation
Compile_Locality            -> Procedure_Ownership              (1490 -> 660)
Located_LTR                 -> Source_To_Trace
Located_Exec                -> Voblint_CFG.CFG_Exec
VIMP_Proc_to_CFG            -> VIMP_Proc_to_CFG (544) + Compile_Wellformed (690)
```

`Compile_Certificate` (75 lines) folded into `Simulation_Preservation` and
`Compile_Reaches` (159) into `Compile_Invariants`; `CFG_Prune` kept only its
graph-generic half. Constants were renamed for the same reason as the theories:
`procs_compiled` -> `procs_embedded`, `source_wf` -> `return_safe`,
`source_global` -> `gs`, and `proc_activation` folded into `compiled_at`.

Largest theory in either session is now 852 lines. No `metis`, no `smt`, no
`sorry`, no apply scripts, and each session ends with a non-vacuity witness
(`pcompletes_witness`, `ltr_collect_witness`, `procs_embedded_witness` /
`csim_witness` / `source_run_has_ltr_witness`).
