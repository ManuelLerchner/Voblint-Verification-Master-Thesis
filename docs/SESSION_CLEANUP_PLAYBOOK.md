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
- **Edits landing mid-build** abort the build with "Incoherent digest";
  finish the edit batch, then build.
- **Style measured in symbols, not bytes.** `\<Rightarrow>` is one column
  in jEdit; measure line length after collapsing `\<...>`.

## VIMP status after the pass

1894 -> ~990 lines across eight theories (`VIMP_Settings` deleted,
`VIMP_Program` added). No `metis`/`smt`/`sorry`. Explicit `gs`/`\<Pi>`
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
  `compile` into `CFG_Local_Trace` and quietly narrowing every one of them.
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

## CFG status after the pass

`Voblint_CFG` 6573 -> 1288 lines (graph model plus `Collecting/`);
`Voblint_Compile` is the new 5285-line session holding the compiler, the
forward simulation, and the two bridge theories. `Control_Simulation` (2507
lines, over the 1500 cap) became `Control_Emit` / `Control_Simulation` /
`Control_Simulation_Forward`; `Compile_Locality` 1490 -> 660;
`Compile_Certificate` 134 -> 71; `CFG_Prune` split into its graph-generic half
(stays in `Voblint_CFG`) and `Compile_Reaches`. No `metis`, no `smt`, no
`sorry` in either session.
