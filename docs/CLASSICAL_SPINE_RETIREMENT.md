# Migration — retire the classical (intra) spine into the unified/IP spine

Status: **executed (extraction + intra-top-layer deletion); `_IP` rename NOT done
(infeasible as a rename — see below).** This was the deletion/rename phase the
[[UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md]] deliberately deferred. U1–U4 already
unified the *math*; this doc planned the *retirement* of the intra spine.

## OUTCOME (what was actually done)

- **Extraction.** The intra-procedural (classical) spine was copied into a
  self-contained sibling repo `~/git/goblint-formalization-classical` (own `ROOT`,
  TD fully vendored as plain files, builds sorry-free).
- **Deletion from main** (branch `refactor/drop-classical-spine`). Removed the 16+1
  intra-*only* leaf theories: `TD_Soundness`, `Sign_Soundness`,
  `Interval_Soundness`, `Interval_Domain`, `Pipeline`, `Trace_Soundness`,
  `TD_Widen_Interface`, `TD_WN_Interface`, `Goblint_Formalization`,
  `CFG_Exit_Reachable`, and the 7 intra examples. Main went 58 -> 41 theories and
  still builds green (IP / Side / unified untouched).
- **Key structural finding — there is no separable "classical core" to delete.**
  The IP/Side/unified spine is *built on* the intra foundation, not a duplicate of
  it: `cfg_collect` (intra collecting) is used by `Analysis_Sound`
  (`intra.collect_post_fixpoint_sound` / `intra_collect_eq`, the unified soundness
  engine) and by the entire **Side (M3)** axis (`Sign_Side_Soundness`,
  `TD_Side_CFG/Soundness`, `Example_Side_Global`). `Constraint_System_Sound`,
  `CFG_Runs_To_Bridge`, the collecting layer, and `TD_Interface`'s intra locale are
  all transitively imported by IP. So only the intra **analysis top layer** is
  classical-only; the substrate stays.
- **`_IP` rename is therefore NOT a rename.** Dropping `_IP` would rename
  `cfg_collect_ip -> cfg_collect`, colliding with the load-bearing intra
  `cfg_collect`. Making IP canonical requires first re-homing `Analysis_Sound` and
  the Side axis off the intra collecting semantics — a deep refactor (Option B's
  research slice), not a mechanical rename. Left undone deliberately.
- **`TD_Interface` intra-locale trim** (`td_cfg_plain_solver` / `td_analyse`, now
  used only inside `TD_Interface`): pending — needs an I/Q `.thy` edit + build.

The original A/B analysis below predates the execution and is kept for context.

Read first: `docs/UNIFIED_ANALYSIS_MIGRATION_HANDOFF.md` (U1–U4, done, green).

## 0. What is already done (do not redo)

The hard part — collapsing two `lfp(F)` skeletons and two post-fixpoint
soundness proofs into one — is **finished**:

- `src/CFG/Collecting/CFG_Collect_Unified.thy` — `collecting` locale, parameterised
  by `combine_at :: cfg => cenv => pp => store set`. Proves `F`/`collect` lfp
  skeleton **once**. Two interpretations:
  - `intra` (`combine_at = (\<lambda>_ _ _. {})`) with `intra_collect_eq: intra.collect g S = cfg_collect g S`
  - `ip` (`combine_at = collect_combine_pp`) with `ip_collect_eq: ip.collect g S = cfg_collect_ip g S`
- `src/Equations/Analysis_Sound.thy` — `collect_post_fixpoint_sound` (lfp→gamma
  engine in the locale) + `unified_post_fixpoint_sound[_ip]`.

So `cfg_collect` and `cfg_collect_ip` are **already proven equal** to the two
interpretations of one engine. What remains is bureaucracy + two genuinely new
proof obligations (the embedding and the Side/Interval re-home).

## 1. Why the classical spine is not free to delete

`rg`-confirmed consumers of the intra `cfg_collect` / `to_cfg` (non-`_IP`):

| Consumer stack | Built on | Status if intra deleted |
| --- | --- | --- |
| Intra examples (`Example_Sign_*`, `Example_NonTerminating_*`) | intra | re-home or reframe as pcom |
| **Interval** (`Interval_Soundness`, `Example_Interval_*`) | **intra** | **orphaned** — no IP interval variant |
| **Side-effecting / M3** (`TD_Side_*`, `Sign_Side_*`, `Example_Side_Global`) | **intra** | **orphaned** — no IP side variant |
| Intra soundness (`TD_Soundness`, `Constraint_System_Sound`, `Pipeline`, `Trace_Soundness`) | intra | recovered via locale (U2) |
| Small-step bridge (`CFG_Runs_To_Bridge`, `CFG_Exit_Reachable`, `CFG_Compound_Paths`, `CFG_Path_Bridge`) | `com` + `compile`/`to_cfg` | needs `com ↪ pcom` embedding |

Two real blockers, not bureaucracy:

1. **`com` is a different transition system, not a sublanguage.** `pstep`
   configs are `(c, s, frs)` (frame stack on every config); `com` small-step is
   `(c, s)`. `com` is the frame-free fragment of `pcom` (constructors PSKIP /
   PAssign / PSeq / PIf / PWhile; missing PScope / PCall / PRestore). The intra
   adequacy bridge (`CFG_Runs_To_Bridge`, store-level `runs_to`) is stated on
   `(c,s)`. To make it an instance of the IP bridge (`pruns_to_ip`,
   `CFG_Collect_IP_Adeq`) you must prove a **simulation**:
   `embed :: com => pcom`, then `com` run with empty frame stack projects to the
   `pcom` run of `embed c`, store-equal. The CFG side is near-definitional —
   `compile c n` and `compile_pcom pi lay (embed c) n` produce the **same**
   `(n',en,ex,E)` with `C = {}` (the bodies are line-for-line identical for the
   five shared constructors) — but the small-step simulation is new work.

2. **Side and Interval verticals are intra-rooted.** There is no IP side-effecting
   solver and no IP interval soundness. Deleting intra without re-homing these
   deletes M3 and the interval headline. The unified `collecting` locale does not
   cover the `TD_side` backend (different `'l + 'g` unknown shape — see handoff §7,
   "two backends stay").

## 2. Two target end-states

### Option A — collapse duplicates, keep `com` as surface fragment (recommended)

Make the *definitions* `cfg_collect` / `cfg_collect_ip` thin wrappers over the
locale (or delete the standalone `lfp` bodies and replace each use with the
interpretation constant). Keep `com`, `compile`, `to_cfg`, and the intra
small-step bridge as the **surface intra-procedural language** — the thesis
HOL-IMP narrative leans on `(c,s)`. Both `intra` and `ip` interpretations coexist;
**the `_IP` suffix stays** (it names the combine-carrying interpretation, which is
a real distinction at the consumer level).

- Deletes: the duplicated `cfg_collect_F` / `cfg_collect` lfp skeleton bodies (now
  in the locale), duplicated post-fixpoint soundness bodies (now `Analysis_Sound`).
- Keeps: `com`, `compile`/`to_cfg`, intra bridge, Side, Interval — all untouched.
- New proof: **none** beyond re-export aliases.
- Churn: small, one PR.
- Outcome: no more duplicated *engine*, but `cfg_collect` vs `cfg_collect_ip`
  still both named. Does **not** literally "drop `_IP`".

### Option B — pcom-only spine, drop `_IP`, embed `com`

Make the (renamed, suffix-dropped) IP spine the **only** spine. `com` either
deleted or kept solely as a fragment feeding the embedding.

- New proofs: (1) `embed :: com => pcom` + `compile`/`compile_pcom` agreement +
  `pstep` simulation; (2) re-home Side and Interval onto the unified/IP spine
  (Side needs an IP-flavoured `combine_at` or an argument that `combines = {}`
  makes the side backend coincide).
- Rename: drop `_IP` across ~12 theories + constants; update ROOT.
- Churn: large, multi-PR. Touches ~30 theories.
- Outcome: the literal goal — one spine, no `_IP`, classical recovered as the
  `combines = {}` / frame-free instance.

### Recommendation

**A now, B as a follow-up only if the thesis wants a single spine.** The unified
locale already removed the duplicated mathematics; A banks that as deletions with
zero new proof risk. B's cost is dominated by re-homing the **Side** vertical
(M3), which the unified locale explicitly does not cover — that is a research
slice, not a rename. Do not couple it to the deletion.

## 3. Slices (Option A)

| Slice | Action | Exit |
| --- | --- | --- |
| R1 | Replace `cfg_collect` def body with `intra.collect` (via `intra_collect_eq` as the new `[simp]`/`[code]` unfold), keep the name. Same for `cfg_collect_ip = ip.collect`. | batch green; no standalone `lfp(cfg_collect_F)` left |
| R2 | Delete duplicated intra post-fixpoint soundness bodies in `Constraint_System_Sound` / `TD_Soundness`; re-export names as corollaries of `Analysis_Sound`. | old theorem names resolve, batch green |
| R3 | Fold `CFG_Edges_Collect` / `CFG_Collecting_Core` standalone `cfg_collect_F` into `CFG_Collect_Unified` (or leave as the `intra` re-export module). | one collecting engine theory |
| R4 | Doc + ROADMAP update; mark intra spine "interpretation of unified". | this doc → Done |

Each slice exits sorry-free with **no example regression** (handoff §8 gate).

## 4. Slices (Option B — only on explicit go)

| Slice | Action |
| --- | --- |
| B1 | `embed :: com => pcom`; `compile_pcom pi lay (embed c) n = (\<dots>, {})` by `pcom.induct` / `com.induct` (near-definitional). |
| B2 | `pstep` simulation: `(c,s) →* (SKIP,t)` iff `pstep* pi (embed c, s, []) (PSKIP, t, [])`; store-projection lemma. Re-root `CFG_Runs_To_Bridge` results as instances. |
| B3 | Re-home **Interval** onto unified spine (interval `combine_at` is `{}`; mostly rename). |
| B4 | Re-home **Side** (M3): decide whether `TD_side` soundness routes through the unified collecting at `combines = {}`, or stays a separate backend with the suffix dropped only on the collecting side. **Research slice — scope separately.** |
| B5 | Drop `_IP` suffix across constants + theory names; update ROOT, examples, docs. |
| B6 | Delete now-dead intra-only theories (`CFG_Edges_Collect` if fully subsumed; intra `to_cfg` if `com` dropped). |

## 5. Build gate

```bash
isabelle build -v -d ~/afp/thys -d vendor/td-verification -D . Goblint_Formalization
```

Sorry-free, no example regression, per slice. I/Q inner loop, batch as the gate
(AGENTS.md). Never claim a slice done on I/Q alone.

## 6. Open decision (blocks start)

**A or B?** A is the safe completion of the unified migration. B is the literal
"delete classical + drop `_IP`" but its cost is re-homing Side/Interval, not the
deletion itself. Pick before R1/B1.
