# Isabelle development and verification

Load this guide before working with a `.thy` file or judging proof completion.
`AGENTS.md` defines the project contract; this file contains the operational
workflow and project-specific traps.

## Choose the Isabelle interface

| Interface | Endpoint | Use |
| --- | --- | --- |
| I/Q | jEdit document server, port 8765 | Normal development: file state, diagnostics, context, exploration, edits |
| I/R | MCP port 9148; REPL TCP port 9147 | Headless fallback when jEdit is unavailable |

Start both with `rtk ./scripts/start-both.sh`. Use
`rtk ./scripts/start-iq.sh` for jEdit and I/Q only, or
`rtk ./scripts/start-ir.sh` for the headless REPL.
`scripts/setup.sh` installs their pinned AutoCorrode sources under the ignored
`vendor/autocorrode/` directory and registers I/Q in Isabelle's user component
configuration. `AUTOCORRODE_HOME` may point I/R at another checkout.
AutoCorrode is developer tooling, outside the proof dependencies.

Authenticate I/Q or connect I/R with token `isabelle-local` before other server
calls. Treat a failed real call as the availability check; do not make a
separate probe.

## Theory-file ownership

Tracked `.thy` files belong to Isabelle's document model.

- Read and open them through I/Q.
- Edit them through I/Q `write_file`, preferably a small `str_replace`.
- If I/Q is unavailable, edit through I/R `repl_edit`.
- Never use host read, edit, or write tools on them. jEdit may retain a stale
  buffer after a host edit, so later diagnostics can check text different from
  the file on disk.
- The first creation of a new, untracked theory is the sole host-write
  exception. Open it in I/Q immediately afterward.

If a host edit happens accidentally, apply the same replacement through I/Q to
resynchronize the document model.

## I/Q inner loop

For every theory edit:

1. `open_file` and inspect file diagnostics.
2. Use `get_context_info`, `get_command_info`, or `get_proof_blocks` to read the
   contextual state around the target command.
3. Trial the smallest plausible proof step with `explore`. Ask for the current
   subgoal again after one or two tactics.
4. Apply a small `write_file` replacement.
5. `save_file`.
6. Normalize the saved source:

   ```bash
   rtk python3 scripts/normalize_isabelle_ascii.py path/to/Theory.thy
   ```

7. Reopen the theory so jEdit sees the normalized disk text.
8. Check file-scoped error diagnostics. Repeat on one failing command at a time.

After every write, confirm persistence through the reopened file or fresh
diagnostics. Save timeouts and buffer lag have produced phantom fixes.

Do not run `isabelle build` to discover an error that I/Q already identifies.
Use the final build procedure below after interactive development.

## Six ways this environment misreports state

Each of these looks like an ordinary correct result. All six have produced a
wrong claim here, and the defence is the same for all of them: **a statement
about state names what was read and when**, never what was true earlier in the
session.

**Empty diagnostics over zero commands.** `get_diagnostics` on a node the
session has not parsed yet returns `count: 0`, `errors: 0`,
`fully_processed: true` -- clean in every field a caller normally reads.
`get_processing_status` on the same node showed 548 unprocessed. Check
`total_commands` before believing `errors: 0`; zero commands is not a clean
file, it is an unread one.

**A line range computed from disk while the buffer is dirty.** An outline taken
with `grep` is disk coordinates; unsaved I/Q edits shift the buffer under them.
Deleting by those numbers removed 68 lines from the middle of a live proof.
Save first, then outline, then edit -- and never mix a host read with an
unsaved buffer.

**A buffer that has not picked up a host write.** The older half of the same
hazard: diagnostics describe the buffer, so a bulk host substitution jEdit has
not reloaded reads as clean. Compare buffer against disk at one changed line
before believing anything.

**A regeneration in progress.** `pixi run codegen` removes `codegen/generated/`
before writing it, so anything reading concurrently sees a *missing* file
rather than a stale one. `git status` reported it deleted, and a checker
reported it not found; both were reading mid-write.

**A session that vanishes between calls.** I/Q can be killed by the host for
memory pressure. Results obtained before it died stay valid for the revision on
disk, but nothing is verified after it until a restart finishes.

**A filtered check.** Most `pixi run` tasks here report failure as *output* and
still exit 0. `sessions-check` printed its error and `tail -1` ate it, which would
have carried a change past the guard written for that exact hazard. **A check
that reports failure as output rather than as exit status must never be
filtered.** The same rule applies to counting instead of listing: print what
matched, not how many.

## Any `.thy` change that bypasses I/Q needs a restart

A theory whose ROOT entry changed loads as `Draft.<name>` until jEdit restarts.
The file-set analogue is less obvious and bites harder: when a theory is
**deleted and regenerated at a different path under the same name**, no ROOT
entry changes, but the running session holds a buffer for the old file and
resolves two nodes of that name at once:

```text
exception THEORY raised: Duplicate theory name {..., Int_Analyses}
```

Every later error is fallout from the session having no coherent theory
context, so the count is meaningless. Restart, then read.

**The quiet case is a regeneration in place, and it is the dangerous one.** The
duplicate above at least announces itself. When a generator overwrites a theory
at the *same* path under the *same* name -- no ROOT change, no duplicate, no
exception -- nothing looks different: the node name is right, the file is where
it belongs, and the session goes on serving the bytes it loaded. Diagnostics
taken after `pixi run assembly-generate` describe the previous render, and because a
regeneration moves lines they cite offsets whose content has changed
underneath. This was caught once by comparing the buffer against disk at a line
the run had changed, and would otherwise have produced a confident report about
text that no longer existed.

The reason it hides is that a generator run does not feel like editing -- nobody
typed anything and no editor was involved. But `target.write_text(rendered)` is
a host write like any other and the session cannot tell the difference. So the
rule is not about editing: **any change to a `.thy` that does not go through
I/Q needs a restart before its diagnostics mean anything** -- deleted, moved, or
overwritten in place.

Restarting is also the only way to check adoption at all. A `Draft.` node
resolves imports without consulting the session, so its diagnostics say nothing
about whether the ROOT finds the file. After adopting a generated theory,
confirm the node reports `<Session>.<Theory>` -- and check its *consumers*, not
only the theory itself. A generated theory that dropped an import its
hand-written predecessor had is clean on its own and breaks everything
downstream of it.

## I/R fallback

- Initialize a REPL from a fully qualified import, such as
  `Voblint_CFG.LTR_Def`.
- Send one Isar command per `step`.
- After a theory edit, reload it with its fully qualified theory name.
- `explore` is non-persistent; a REPL step changes the current state.
- `explore query='proof'` requires `Isar_Explore` in the current session.
  Sledgehammer and theorem search do not require that import.

If neither interface is available, report the failed call and ask for
`rtk ./scripts/start-both.sh` or `rtk ./scripts/start-ir.sh`.

## Proof workflow

### Choose the proof shape

Ask whether the proof is short and simple before writing it.

- Use `by ...` or apply-style Isar for short proofs.
- In apply style, run one or two tactics, inspect the subgoal, then continue.
- For larger proofs, sketch structured Isar top-down with `sorry` placeholders.
  Fill one placeholder at a time.
- Hoist a difficult placeholder into a named helper lemma or isolate it in a
  `proof -` block.

Avoid replacing an entire working proof script to repair one command.

### Search live proof status

Theories, rather than documentation, are authoritative:

```bash
rtk rg -n '^\s*sorry' src/
rtk rg -n '^(lemma|theorem) ' src/
```

## Batch outer gate

Run a batch build when:

- every changed theory has no I/Q errors and the complete task is ready;
- the user explicitly requests a build or CI check;
- imports, a session `ROOT`, or a new theory require a heap refresh;
- preparing a commit.

Use the repository interfaces so session arguments do not drift:

```bash
rtk pixi run isabelle-build
```

`isabelle build -f` forces the named session's **ancestors** too, not just the
session named. On this tree that means Pure and HOL, which rebuilds every heap
below the project and turns a targeted check into a full-tree rebuild. To get a
log rather than a cache hit for one session, delete that session's heap or use
`-o` verbosity; do not reach for `-f`.

On a fresh clone without parent heaps:

```bash
rtk pixi run isabelle-bootstrap
```

`pixi run isabelle-build` streams a verbose, parallel build of `Voblint_Examples`,
whose closure is every session except `Voblint_Codegen`; `pixi run codegen`
builds that one. Changes confined to `src/Examples/**` are covered by the same
`rtk pixi run isabelle-build` run.

### Slow-build diagnosis

With warm heaps, more than about 40 seconds of silence after a theory starts
usually indicates proof search blow-up. Frequent causes:

1. `metis` or `smt` reconstruction;
2. `auto` with destructive elimination on inductive rules;
3. bidirectional `simp` or `auto` rewriting;
4. a recursive `[simp]` declaration;
5. a new `[intro]` or congruence rule that triggers repeatedly.

Stop the build rather than extending its timeout. The final `Running <Theory>`
line identifies the likely file. If necessary, rerun the underlying build with
another `-v` for command timings, then inspect that command in I/Q. Bound the
automation, remove the problematic attribute, or split the proof.

Do not call a theorem done until its requested statement exists, its proof is
closed, and the batch log is green.

## Isabelle and HOL-IMP traps

### Context and locales

- Free variables can resolve to imported constants. Bind variables explicitly
  or use names such as `ctx`, `cmd`, and `cost` rather than `c`.
- A fact exported from `context fixes ... assumes A and B and C begin ... end`
  carries every enclosing `assumes` as an extra premise, even when its own
  proof or body used only some of them -- this applies to plain `definition`s
  inside the block too, not only `lemma`/`theorem`. Citing such a fact from
  outside with a partial premise list, e.g. `foo[OF A]`, does not error at the
  `OF` application: it silently produces a still-conditional fact, so a later
  `unfolding foo[OF A]` or `simp add: foo[OF A]` just fails to fire, and the
  resulting diagnostic points at the rewrite site, not the missing premise.
  When an `OF`-based rewrite unexpectedly does nothing, do not guess from the
  enclosing `assumes` clause -- print the fact's actual exported statement
  (`thm foo`, or an I/Q `get_command_info` probe on a scratch `thm foo` line)
  to see every premise it carries, then supply all of them via `OF`.
- A `lemmas foo = interp.bar` re-export of an *interpreted* locale fact is not
  exempt from the trap above: if establishing `interp` itself needed the
  context's `assumes` (a typical `interpretation ... proof (unfold_locales,
  ...)` block citing them), `foo` carries those same premises, because the
  interpretation genuinely depends on them, not merely by textual proximity.
  Whether a given re-export needs zero, some, or every enclosing premise is
  not predictable from the block structure alone; check per-instance with a
  scratch `thm foo` rather than assuming a `lemmas` re-export is always
  premise-free just because it is not a hand-written `lemma`.
- A closely related, differently-shaped failure: citing `X[OF a1 ... an]`
  with *fewer* facts than `X` has premises does not error at the `OF`
  application either -- it produces a still-conditional fact, and `by (rule
  X[OF a1 ... an])` then reports "Failed to apply initial proof method" with
  the *unsupplied premises* listed as the remaining subgoals in the
  diagnostic. This is a louder, more legible failure than the silent-no-op
  case above (which manifests through a rewrite that just does nothing), but
  both stem from the same root cause: undercounting a fact's true premise
  list. Read the diagnostic's leftover-subgoal list to see exactly which
  premises are still missing, rather than re-deriving the count from the
  locale/context signature by hand.
- When a bridging `have` states an equation whose RHS mixes a local
  abbreviation (e.g. a `define is_bot_pred where "is_bot_pred = ..."`) used
  in two syntactically identical but semantically different roles -- once as
  an *index* argument threaded through unrelated locale parameters, once as
  the *predicate* argument to a function like `canonicalize_lift` -- keep the
  abbreviation folded (`is_bot_pred`, not its spelled-out RHS) in the `have`
  statement itself, matching whatever sibling fact it must compose with. A
  later `[unfolded is_bot_pred_def]`/`[folded is_bot_pred_def]` rewrites
  *every* occurrence of that one Free variable uniformly; Isabelle cannot
  tell "the index occurrence" from "the predicate occurrence" apart once both
  are the same syntactic term, so partially unfolding one but not the other
  is not expressible after the fact -- decide the folded/unfolded shape when
  writing the `have`'s statement, not by post-hoc `unfolded`/`folded`
  attributes on the derived fact.

### I/Q buffer sync

- `open_file` on a file I/Q already tracks does **not** force a reload from
  disk -- it can return `"opened": true` while jEdit's in-memory buffer still
  holds stale (pre-edit) content. This matters most after any edit that
  bypassed I/Q (an accidental host `Edit`/`Write` on a tracked `.thy`, or a
  `git checkout`/`stash` that changed disk underneath an open buffer):
  `get_diagnostics` run right after such an `open_file` can report a clean
  zero-error result that is checking the *old* text, not the one just
  written to disk, producing false confidence.
- Recover by re-applying the same edit through I/Q `write_file` (never
  `save_file` first, which would flush the stale buffer back over the clean
  disk content) so jEdit's buffer and disk agree again. Before trusting a
  suspiciously-clean `get_diagnostics` result after any out-of-band disk
  change, confirm the buffer actually contains the expected text with
  `read_file` on the specific changed lines -- a passing diagnostic is not
  evidence the buffer was ever resynced.
- The opposite direction is the more expensive one, because nothing reports
  it: an I/Q `write_file` changes the **buffer**, not the file. A whole
  session's work can be green in I/Q and absent from disk, so a batch build --
  yours or another agent's -- reads the old text and fails on errors you
  cannot reproduce. `get_diagnostics` will keep saying zero the whole time,
  correctly, about the buffer.
- `save_file` with a path returns `{"saved_files": []}` when that buffer is not
  dirty. Do not read that as "already written": it is also what you get when
  the save did not happen. Call `save_file` with **no** path, which saves every
  dirty buffer and names them, and then verify against the file:

  ```bash
  rtk proxy wc -l <every file you touched>
  ```

  A line count that disagrees with what I/Q shows is the cheapest available
  proof that the buffer and the file have diverged; a diagnostic result is not
  evidence about the file at all. Do this before quoting any result to another
  agent, before a build, and before a commit.

### Isar syntax

- `(* ... *)` inside a quoted HOL term is syntax, not a comment.
- Numeral literals cannot be `fun` patterns.
- `inv` clashes with `Hilbert_Choice.inv`.
- Write `ALL j. n <= j --> ...`, not `ALL j >= n. ...`.
- Do not use Isar keywords such as `back`, `prefer`, `defer`, `then`, `with`,
  `also`, or `finally` as fact labels.
- If `obtain` followed by `show` reports obtained parameters in the result, use
  `have` for the intermediate fact and reserve `show` for the final case goal.
- A set-comprehension binder can clash with a surrounding fixed variable. Rename
  the fixed variable or use an explicit `Collect`.

### Induction and HOL-IMP

- `big_step.induct` binds case arguments in the textual order of each rule, not
  conclusion order. Read the rule before naming `IfTrue`, `IfFalse`, or
  `WhileTrue` case arguments.
- HOL-IMP sessions extend `"HOL-IMP"` and import qualified theories such as
  `"HOL-IMP.Com"` and `"HOL-IMP.Big_Step"`.
- For existential executions, introduce the witness before applying `Assign` or
  `Seq`.

### Codegen module cycles

- Splitting `export_code` targets by session/theory boundary can produce an
  OCaml module dependency cycle (the `Exec_St_*` executable state is generically
  instantiated at the solver's own `widening`/`narrowing` type classes, and
  the CFG-specific solver instantiation needs `cfg_node` back -- a real,
  mutual code-level dependency, not an arbitrary grouping choice) or, even
  when `export_code` itself is clean, a rejection from `ocamlfind ocamlopt`
  over an unbound type-class dictionary record field once `code_identifier`
  introduces module boundaries the unsplit default did not have.
- The project's fix is not to split: `export_code` in `Voblint_Codegen.thy`
  declares `module_name Generated`, and no `code_identifier`/`code_module`
  remapping remains in `src/`. `AGENTS.md`'s "New theories and the code-export
  module map" is the contract.
- Diagnose with the actual `export_code`/`codegen-check` output, not by
  guessing from theory imports: a clean `export_code` does not guarantee a
  clean `ocamlfind` link.

### CFG shapes

- Local edges are triples `(source, action, target)`. Calls are quadruples
  `(call-site, action, callee-entry, continuation)`. Decompose the tuples before
  simplification.
- Pointwise state or environment order often needs `le_fun_def` before a
  monotonicity lemma can apply.

The nearest CFG README contains current semantic and compiler-specific
invariants.
