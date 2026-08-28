# Session cleanup playbook

How the per-session audit-and-clean pass works, what it found in the first
session (VIMP), and the traps that cost a rebuild each. Read this before
auditing the next session (CFG, then Core, Analysis, ...).

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

Left for the CFG pass: growing `wf_compile_input_simps` with the leaf
definitions (`reserved_ret_var_def`, `source_exp_def`, `valid_formal_def`,
`value_providing_def`, `special_table_def`, `ret_var_def`,
`prog_main_name_def`) so the sixteen Example theories that repeat the same
`auto simp:` list become `unfolding wf_compile_input_simps by simp`; and
switching the nine non-Example importers of `VIMP_Notation` that use no
quotation (`*_Ctx_None_Sound`, `Int_Exec_Sound`, `Analyse_Dispatch`, ...)
to `VIMP_Program`.
