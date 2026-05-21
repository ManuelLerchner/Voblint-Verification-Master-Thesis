# AFP Graph Library Migration Plan

**Status:** Phases 0-4 landed 2026-05-22 (Option B locale-interp), then **promoted to Option A carrier change** the same day. Build green; sorry count unchanged (16).

**Option A landed (carrier change, 2026-05-22):** the original plan deferred carrier change in favour of locale interpretation (Option B). On review, the Option B `cfg_as_dgraph` projection had **zero call sites** outside its own simp lemmas — pure overhead with no payoff. Promoted to Option A:

```isabelle
record cfg = "(pp, edge_action) graph" +
  cfg_entry :: pp
  cfg_exit  :: pp
```

`cfg` is now genuinely a `graph` by record extension. `cfg_edges c` becomes `edges c` everywhere (mass rename through 12 files, ~98 sites). Smart constructor `mk_cfg en ex E` auto-populates `nodes` so `valid_graph (graph.truncate (mk_cfg en ex E))` holds by construction. The bridge lemma `cfg_collect_exit_eq_collect` survived intact. One proof in `TD_Interface.thy` had to be tightened from `using ... by blast` to `by (rule ...[OF ...])` because `blast` could not unify through the inherited selector.

**Phase 3 scope correction (2026-05-22):** the original plan claimed Phase 3 would discharge `td_cfg_in_reach` via `cfg_reach.reaches_trans`. On audit, `td_cfg_in_reach` refers to the **TD solver's internal strategy-tree `reach` set**, not CFG-edge reachability. The two notions are unrelated; discharging the premise needs solver-layer reasoning (TD iteration covers all CFG points), not a graph-interp bridge. Phase 3 therefore landed in reduced form: `CFG_Reach.thy` exposes the `Graph_Defs` interp + `cfg_reach_iff_cfg_path` and is available for any future caller, but the `td_cfg_in_reach` assumption in `Pipeline.thy` remains. Reopen as a separate solver-layer ticket if desired.

**Library naming correction (2026-05-22):** Wimmer's `TA_Graphs.Graph_Defs` is informal shorthand from the `archive-of-graph-formalizations` survey. The actual AFP location is session `Timed_Automata`, theory `Graphs`, locale `Graph_Defs`. ROOT references `Timed_Automata` (not the non-existent `TA_Graphs` session).

**Decision:** 2026-05-22 (meeting 3 §C/§D + KB `wiki/research/graph-library-evaluation.md`).
**Goal:** stop hand-rolling path algebra in `src/CFG/CFG_Path.thy`. Reuse mature AFP graph libraries via locale interpretation instead of carrier change.
**Non-goal:** changing the CFG carrier type, redoing the bridge lemma `cfg_collect_exit_eq_collect`, or touching the solver / domain layers.

See also:
- `~/goblint-formalization-kb/wiki/research/graph-library-evaluation.md` — full library-by-library comparison + rationale
- `~/goblint-formalization-kb/wiki/concepts/cfg-representation.md` — what our `cfg` record is and why
- `~/goblint-formalization-kb/wiki/meetings/2026-05-18-meeting3.md` §C/§D — supervisor framing for AFP-reuse
- `docs/SMALL_STEP_MIGRATION.md` — separate migration (deferred); independent of this one
- AFP `Dijkstra_Shortest_Path.Graph` — primary library
- Wimmer `TA_Graphs.Graph_Defs` — reachability adjunct

---

## Two-library hybrid

| Role | Library | Why |
|---|---|---|
| Primary labelled carrier | `Dijkstra_Shortest_Path.Graph` | `record graph = nodes :: 'v set, edges :: ('v × 'w × 'v) set` — **shape-identical** to our `cfg_edges`. Built-in label slot. `valid_graph` locale gives path-split lemmas. |
| Reachability adjunct | `TA_Graphs.Graph_Defs` | Pure relational locale (`steps`, `reaches`, `reaches_trans`). Used for the `td_cfg_in_reach` premise discharge. |
| Rejected | `Graph_Theory.digraph` (Noschinski) | Abstract arcs + tail/head → label side-fn indirection forces bridge rewrite. No payoff. Future-target only if SCC / cycle-elimination ever needed. |
| Rejected | `DDFS`, `Cava_Automata.Digraph_Basic` | No labels → no transfer-function composition possible. |

Adoption strategy: **locale interpretation, not carrier change.** Keeps `record cfg`, `cfg_edges`, `cfg_entry`, `cfg_exit` as-is. No rename storm. Bridge lemma untouched.

---

## Migration scope (proof-repo audit, 2026-05-22)

`src/CFG/CFG_Path.thy` hand-rolls path machinery: `cfg_path`, `cfg_path_append`, `cfg_path_split`, `path_collect`, `path_collect_offset_path`. Roughly 200 LOC. Most of it can be replaced by interp lemmas from `Dijkstra_Shortest_Path.Graph` (`is_path`, `is_path_split`, `path_split_vertex`, `path_split_set`).

`src/CFG/CFG_Def.thy` defines `record cfg` with extras `cfg_entry`, `cfg_exit`. Needs one `definition` (`cfg_as_dgraph`) + one `interpretation` block.

`src/Pipeline/Pipeline.thy` carries `td_cfg_in_reach` as an opaque premise. With `TA_Graphs.Graph_Defs` interp on the label-erased relation, this becomes provable from the CFG well-formedness lemmas.

No other files touched. Domains, solver, IMP2 syntax, IMP2 semantics, equations — all untouched.

---

## Phase plan

### Phase 0 — preflight (1 hr)

- [ ] Confirm `Dijkstra_Shortest_Path` is in the AFP we depend on (`ROOT` / session file).
- [ ] Confirm `TA_Graphs.thy` is reachable; if not in AFP, vendor it under `src/Vendored/TA_Graphs.thy` (Apache-2.0).
- [ ] Snapshot baseline build + sorry count: `isabelle build -d . Goblint_Formalization | tee /tmp/baseline.log`.

### Phase 1 — Dijkstra interp on `cfg` (1–2 days)

**Touches:** `src/CFG/CFG_Def.thy`.

1. Derive nodes set:

```isabelle
definition cfg_nodes :: "cfg ⇒ pp set" where
  "cfg_nodes c ≡ {cfg_entry c, cfg_exit c}
               ∪ fst ` cfg_edges c
               ∪ (snd ∘ snd) ` cfg_edges c"
```

2. Build the projection into Lammich's record:

```isabelle
definition cfg_as_dgraph :: "cfg ⇒ (pp, edge_action) Dijkstra_Shortest_Path.graph" where
  "cfg_as_dgraph c ≡ ⦇ nodes = cfg_nodes c, edges = cfg_edges c ⦈"
```

3. Discharge the `valid_graph` axioms (trivial — `cfg_nodes` is defined to satisfy them):

```isabelle
interpretation cfg_dgraph: valid_graph "cfg_as_dgraph c"
  by unfold_locales (auto simp: cfg_as_dgraph_def cfg_nodes_def)
```

4. Add wellformedness lemma `cfg_edges_in_nodes` and `cfg_entry_in_nodes`, `cfg_exit_in_nodes` for downstream use.

**Acceptance:** `isabelle build` green; no change to existing lemma statements; new interp lemmas available via `cfg_dgraph.is_path_split`, etc.

### Phase 2 — port `CFG_Path.thy` to Dijkstra lemmas (3–5 days)

**Touches:** `src/CFG/CFG_Path.thy`, plus any caller that uses `cfg_path_split` / `cfg_path_append` directly.

Strategy: keep our `cfg_path` predicate but prove **equivalence** to Lammich's `is_path` on the projected graph. Then derive our existing lemma library via the equivalence + Lammich's lemmas.

```isabelle
lemma cfg_path_iff_is_path:
  "cfg_path c u es v ⟷ cfg_dgraph.is_path c u (map_action_path es) v"
  by (induction rule: cfg_path.induct) (auto simp: ...)
```

Replace these proofs with `using cfg_path_iff_is_path cfg_dgraph.is_path_split by blast`:

- `cfg_path_append` — derive from `cfg_dgraph.is_path_split'`
- `cfg_path_split` — derive from `cfg_dgraph.is_path_split`
- Internal path-splitting in the bridge `cfg_collect_exit_eq_collect` — leave untouched (proof closed; only refactor if mechanical)

Keep `path_collect` and `path_collect_offset_path` — they are about **action folding**, not path validity, so Lammich's API doesn't cover them. These stay hand-rolled (this is the irreducible Goblint-specific bit).

**Acceptance:** `src/CFG/CFG_Path.thy` line count drops ≥ 25%; build green; bridge proof in `CFG_Collecting.thy` unchanged.

### Phase 3 — `TA_Graphs` interp for reachability (1–2 days)

**Touches:** new `src/CFG/CFG_Reach.thy`; `src/Pipeline/Pipeline.thy` (premise discharge).

1. Project label-erased step relation:

```isabelle
definition cfg_step :: "cfg ⇒ pp ⇒ pp ⇒ bool" where
  "cfg_step c p q ≡ ∃a. (p, a, q) ∈ cfg_edges c"
```

2. Interpret `Graph_Defs`:

```isabelle
interpretation cfg_reach: Graph_Defs "cfg_step c" .
```

3. Tie `cfg_reach.reaches` back to `cfg_path`:

```isabelle
lemma cfg_reach_iff_cfg_path:
  "cfg_reach.reaches c u v ⟷ (∃es. cfg_path c u es v)"
  by (induction rule: cfg_reach.reaches.induct) ...
```

4. In `Pipeline.thy`, replace the opaque `td_cfg_in_reach` assumption with a proved lemma using `cfg_reach.reaches_trans` and the well-formedness of compiled CFGs.

**Acceptance:** `pipeline_sound` no longer carries `td_cfg_in_reach` as a free assumption; `PROOF_PHASES.md` sorry/assumption inventory updates accordingly.

### Phase 4 — cleanup + docs (½ day)

- Remove dead hand-rolled lemmas in `CFG_Path.thy` that are now strictly weaker than Lammich's interp lemmas (no callers).
- Update `docs/HOL_IMP_COMPARISON.md` cross-link: note we now interp into Dijkstra rather than mirror Nipkow's `Vertex_Walk`.
- Update `docs/PROOF_OVERVIEW.md` § "CFG representation" to point at Dijkstra interp + TA_Graphs adjunct.
- Bump KB log: `wiki/log.md` entry "afp-graph migration complete".

---

## What stays hand-rolled (and why)

| Component | Why not replaced |
|---|---|
| `path_collect :: edge_action list ⇒ store set ⇒ store set` | Goblint-specific transfer-function composition. No AFP equivalent. |
| `path_collect_offset_path` | About `offset_edges` on compound CFGs — bespoke to our compile function. |
| `cfg_path` predicate | Kept as our canonical API; equivalence lemma to `is_path` carries us. Removing it would force every downstream caller to re-prove on Dijkstra side. |
| `cfg_entry`, `cfg_exit` distinguished points | Not part of Lammich's record; we extend by record extension at the `cfg_as_dgraph` projection. |

---

## What about `Graph_Theory.digraph` later?

Open the door only if **any** of these become critical-path:

- SCC reasoning on the CFG (e.g. loop-detection-driven analyses).
- Cycle elimination on paths (e.g. `apath_awalk_to_apath`-style decompositions).
- Walks-vs-paths distinction stronger than `distinct` suffices for.

None of these are needed for sign / parity / interval / relational stretch goals. Defer indefinitely.

---

## Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| `Dijkstra_Shortest_Path` not in current AFP session deps | Low | Add to ROOT / vendor under `src/Vendored/`. |
| `cfg_path_iff_is_path` requires non-trivial well-formedness side conditions | Medium | Pin to `cfg_nodes` defn; finite + entry/exit ∈ nodes already proved in `CFG_Def`. |
| Phase 3 reachability lemma needs CFG-shape inversion lemmas not yet proved | Medium | Bridge proof already does enough case-analysis on `cfg_edges`; reuse. |
| Phase 2 lemma-port breaks downstream proofs using *exact* statement form | Low | Keep our `cfg_path_*` names as aliases; only the proof shrinks. |

---

## Order of execution

Strictly sequential — each phase depends on the previous interp:

1. Phase 0 preflight
2. Phase 1 Dijkstra interp on `cfg`
3. Phase 2 port `CFG_Path.thy` lemmas
4. Phase 3 `TA_Graphs` reachability interp + `Pipeline.thy` premise discharge
5. Phase 4 cleanup

**Estimate:** ~1 week focused effort. Independent of the small-step migration (`docs/SMALL_STEP_MIGRATION.md`) — can land either first.

---

## Out of scope

- Carrier-change refactor (Option A from KB note): `record cfg = Dijkstra.graph + ...`. Considered, deferred. Interp-only (Option B) preferred to minimise churn.
- Adopting `Graph_Theory.digraph` — see above.
- Touching `src/IMP2/IMP2_Syntax.thy` to extend Nipkow `HOL-IMP.AExp`/`BExp` via nested constructors. Tracked separately in `docs/IMP_SYNTAX_NIPKOW_EXTENSION.md` (Approach 2 cheap-now, Approach 1 nested-wrap deferred to next syntax-touching migration).
- Any small-step changes — handled in `docs/SMALL_STEP_MIGRATION.md`.
