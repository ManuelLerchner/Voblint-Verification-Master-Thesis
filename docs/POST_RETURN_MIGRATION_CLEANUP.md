# Post-return-migration cleanup backlog

Written after the parameter-passing / return-value migration (`EA_Enter xs es`,
4-tuple `combines`, `combine_collect dst s t = combine_assign dst (t ret_var)
(combine_states s t)`) landed and both `Voblint_Analysis` and
`Voblint_Formalization` compiled green. The migration touched ~15 files and, in
doing so, exposed structural duplication that predates it but was multiplied by
it. Nothing below is a correctness gap — every item is a length / complexity /
maintainability reduction. Ranked by payoff.

A future agent should treat each item as an independent refactor: verify the
claim against the cited `file:line`, make the change behind a green
`isabelle build`, and delete the corresponding entry here.

---

## 1. Two combine operators that are provably equal — unify on `combine_collect`

**The redundancy.** The codebase carries two combine notions:

* binary combine — `combine_states s t` written `<s|t>`, and its abstract
  companion `combine_abs σc σe` written `⟨σc|σe⟩`
  (`src/Analysis/Generic/Equations/Constraint_System.thy:275`).
* return-threaded combine — `combine_collect dst s t` and
  `combine_collect_abs dst σc σe`
  (`src/CFG/Collecting/CFG_Collect.thy:150`,
  `src/Analysis/Generic/Equations/Constraint_System.thy:402`).

But they collapse:

```
combine_collect None s t
  = combine_assign None (t ret_var) (combine_states s t)   -- CFG_Collect.thy:150
  = combine_states s t                                     -- combine_assign None _ s = s, IMP2_Proc.thy:71
```

So `<s|t>` is **definitionally the `dst = None` instance** of `combine_collect`,
and `⟨σc|σe⟩` is the `dst = None` instance of `combine_collect_abs` (check the
`combine_collect_abs` unfolding — `combine_assign_abs None` should be identity on
the return slot).

**Why it hurts.** Keeping both is a bug magnet. During the migration the same
proof broke in ~6 places purely because a `show`/assumption still used the binary
form while the surrounding obligation had moved to `combine_collect dst`:
`DG_Route_Soundness`, `Local_DG`, `Clean_RRead_Sound`, `Seeded_Activation_Sound`,
`Activation_Witness_From`. The `seeded_activation_comb` call site also hit a
higher-order "multiple unifiers" failure that only exists because the two
operators must be manually kept in sync.

**Cleanup.**
1. Prove `combine_states s t = combine_collect None s t` and
   `combine_abs σc σe = combine_collect_abs None σc σe` (should be `by (simp add:
   combine_collect_def combine_collect_abs_def)` or one `unfolding`).
2. Migrate the one remaining binary-combine consumer, `twfr` in
   `src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/Activation_Witness_From.thy`
   (its combine rule still produces `combine_states`; see the `combine` case
   around line 207 and `combine_states_def` at line 210), to `combine_collect
   None`.
3. Retire `combine_states_sound` / `combine_abs_bound_sound`'s binary form and the
   `<_|_>` / `⟨_|_⟩` notations, or keep them as `abbreviation`s for the `None`
   instance so old proofs still parse.

**Highest-value item** — removes the dual-combine confusion at the root and
unblocks items 4 and 6.

---

## 2. The eight-obligation collecting-soundness contract is restated ~6×

The premise bundle

```
ENTRY / PROC_ENTRY / EDGE(_BOUND) / COMB / DG_INTRA / DG_RETURN / DG_CALLEE / ENTER_MONO
```

appears verbatim — modulo how the "meaning" is read (`M` vs `sg (Inl ·)` vs
`dg_gamma_c` vs `gamma_unit`) — in:

* `trace_ctx_sound_meaning` / `collect_ctx_sound_meaning`
  (`src/Analysis/Generic/Solver/Context/Ctx_Collect_Backbone.thy`) — the intended
  single backbone.
* `sound_dg_spec.dg_collect_ctx_sound`
  (`src/Analysis/Generic/Solver/Context/Goblint/DG/DG_Route_Soundness.thy:21`).
* `clean_ctx_collect_rread` and `clean_ctx_collect_rread_head`
  (`src/Analysis/Generic/Solver/Context/Goblint/Read/Clean_RRead_Sound.thy`).
* `clean_ctx_collect_rread_via_dg`
  (`src/Analysis/Generic/Solver/Context/Goblint/DG/Local_DG.thy:104`).
* `activation_trace_sound` / `activation_collect_sound`
  (`src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/Seeded_Activation_Sound.thy:41`).

The backbone exists precisely to unify these, and the DG endpoint is already a
corollary of it (`collect_ctx_sound_meaning`). Two spines do **not** ride it:

* `clean_ctx_collect_rread` detours through `Local_DG.via_dg` instead of the
  backbone directly (works, but an extra hop).
* **`activation_trace_sound` re-runs its own `trace_witness_act.induct`** — a full
  parallel trace induction. This was the single most expensive file to migrate
  (SEED_G/COMB/DG_CALLEE all re-derived by hand).

**Cleanup.** Make `activation_trace_sound` an instance of
`trace_ctx_sound_meaning` (its `enterc/combc/seedc` context algebra is exactly the
backbone's `rt`/`entdg`/`dg`/`cmp` parameters specialised). If that lands, the
activation trace induction disappears. Then re-express `clean_ctx_collect_rread`
as a direct backbone instance rather than via the DG adapter, if the extra hop is
not carrying its weight.

---

## 3. `trace_witness` vs `trace_witness_act` are near-clones

`trace_witness` (`src/CFG/Collecting/CFG_Collect_Trace.thy`) and
`trace_witness_act` (`src/CFG/Collecting/CFG_Collect_Activation.thy`) have the same
five rules (`entry / proc_entry / intra / enter / combine`), the same
`call_enter_store` linkage in the combine rule, and copy-pasted `_nonempty`
lemmas. They differ only in context threading: `trace_witness` fixes nothing;
`trace_witness_act` threads `enterc / combc / seedc`.

**Cleanup.** Define one predicate parameterized by a context algebra and recover
`trace_witness` as the degenerate instance (`enterc = λc _. c`,
`combc = λc1 c2. c1`, `seedc` arbitrary). Removes a whole duplicated inductive
library plus its `.induct` / `.intros` / `_nonempty` scaffolding. Related to item
2 — do them together.

---

## 4. The abstract-bound → concrete-soundness reduction is inlined 4×

The pattern "replace the raw semantic COMB with an order bound
`combine_collect_abs dst … ≤ …` and discharge via `combine_collect_sound` +
`gamma_state_mono`" is re-proven at:

* `combine_abs_bound_sound`
  (`src/Analysis/Generic/Solver/Context/Goblint/Read/Clean_RRead_Sound.thy`) — the
  canonical lemma.
* `seeded_activation_comb`
  (`src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/Seeded_Activation_Sound.thy`)
  — and then **inlined again** at that lemma's two call sites as
  `using bnd combine_collect_sound[OF sc se] gamma_state_mono by blast`
  (a higher-order `OF` ambiguity forced the inline; see item 1 — with a single
  combine the ambiguity goes away).
* the `clean_*_bound` theorems in `Clean_RRead_Sound.thy`.
* the DG `unit`/`indep` combine cases in `DG_Soundness.thy`.

**Cleanup.** Route every site through the one `combine_abs_bound_sound`. After
item 1 the `OF` ambiguity that caused the inlines disappears.

---

## 5. Scattered `bind_formals` / `local_formals` invariance facts

The migration needed the same lemma — "writing local formals does not disturb a
global-reading function" — in three places, each rediscovered:

* `bind_formals_abs_global`
  (`src/Analysis/Generic/Equations/Constraint_System.thy:951`) — abstract state.
* `bind_formals_local_invariant`
  (`src/Analysis/Generic/Solver/Context/Goblint/Read/Support/TD_Side_Eff_Cmp_Sound.thy`)
  — arbitrary global-only digest `f`.
* `bind_formals_notin` + `bind_formals_in_cover_seed`
  (`src/Analysis/Generic/Solver/Context/Goblint/Routing/Support/Activation/Seeded_Activation_Sound.thy`).

**Cleanup.** Collect a small `bind_formals` API next to the definition
(`src/IMP2/IMP2_Proc.thy:63`): `bind_formals_notin` (position outside `xs`
untouched), `bind_formals_global` (globals untouched under `local_formals`), and
the two invariance corollaries built on top. Every consumer then imports one
place instead of re-proving.

---

## 6. `Sign_Named_Global_Eff`: two identical `sound_effectful_transfer` witnesses

`flag_etf` and `named_etf`
(`src/Analysis/Instances/NamedGlobalSign/Sign_Named_Global_Eff.thy`) each carry a
full six-obligation `sound_effectful_transfer` proof
(`nop / assign / assume / assume_not / enter / combine`). The two proofs are
structurally identical, differing only in the `*_etf_full_*` simp lemma names
(`flag_etf_full_enter` vs `named_etf_full_enter`, etc., all `unfolding *_etf_def
by (simp add: route_tree_etf_full)`).

**Cleanup.** Factor the shared skeleton into one lemma parameterized by the route
family (or a small locale over `route_tree_etf_full` / `route_combine_etf_full`),
instantiated twice. Roughly halves the file's proof text.

---

## 7. `Exec_DG_Bridge`: the `(cc, ex, dst)` combine-tree map repeated ~5×

`map (λ(cc, ex, dst). dg_cmb_of S () dst cc ex) (combine_predecessor_list g v)`
(and the `S_st` / `S_abs` variants) appears in `eq_dg_gen_of_commute`,
`sides_dg_gen_of_commute`, and `dep_dg_gen_of_eq`
(`src/Analysis/Instances/Mixed/Exec_DG_Bridge.thy`), and the same shape lives in
`dg_trees_def` (`src/Analysis/Generic/Solver/Context/Goblint/DG/DG_Soundness.thy`).

**Cleanup.** Introduce one `dg_combine_trees g v` (or reuse `dg_trees`' second
summand) so the tuple-destructuring lambda is written once. Localises future arity
changes to a single definition instead of five call sites.

---

## 8. Positional `subgoal premises prems for …` in locale-instance proofs

`sound_dg_spec_indep` and `sound_dg_spec_unit`
(`src/Analysis/Generic/Solver/Context/Goblint/DG/DG_Soundness.thy`) discharge the
`combine_sound` obligation with `subgoal premises prems for s dc g t de dst`,
where the `for` binders match the goal's meta-quantifiers **by position**. The
`dst` arity change broke this silently (the binders shifted, `s`/`dc` rebound to
the wrong types). This is audit item 2 ("instantiation gap") in miniature.

**Cleanup.** Surface a concrete corollary of the `sound_dg_spec.combine_sound`
axiom at the locale boundary (a named lemma with explicit `fixes`/`assumes`) and
apply it by name, instead of relying on positional `for` binders that re-break on
every signature change.

---

## Suggested order

1. **Item 1** (unify the two combines) — keystone; unblocks 4 and removes the
   most recurring migration friction.
2. **Items 4, 5, 7** — mechanical, low-risk, each a self-contained lemma/def move.
3. **Item 6** — contained to one file.
4. **Items 2, 3** — biggest line-count wins but touch inductions; do together and
   last, after 1 has simplified the combine story they thread.
5. **Item 8** — small, do alongside any future `sound_dg_spec` change.

Each item is independently shippable behind a green
`isabelle build ... Voblint_Analysis` (and `Voblint_Formalization` for anything
that changes a public contract). Delete items from this file as they land.
