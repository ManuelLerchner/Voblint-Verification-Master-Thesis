# IMP Syntax → Nipkow Extension Plan

> **Status (2026-05):** **Approach 1c implemented** in `src/IMP2/IMP2_Syntax.thy`
> (hybrid `BaseN`/`BaseB` wrap over HOL-IMP leaf forms + native compound/ext
> constructors). Semantics in `IMP2_SmallStep.thy`. The sections below record
> the original decision process; Approach 2 (`to_hol_imp_aexp` projection) was
> not pursued.

**Decision pointer:** Meeting 3 §B (KB `wiki/meetings/2026-05-18-meeting3.md`) — supervisor (Alexandra) suggested extending Nipkow's HOL-IMP via nested constructor wrap + `abbreviation` sugar rather than redeclaring `aexp` / `bexp` from scratch.
**Goal:** stop redeclaring `aexp` / `bexp` in `src/IMP2/IMP2_Syntax.thy`. Reuse `HOL-IMP.AExp` / `HOL-IMP.BExp` directly; extend with our additional constructors (`Minus`, `Times`, `Or`, `Eq`).
**Non-goal:** changing `com` (already structurally identical to `HOL-IMP.Com`), changing semantics, replacing big-step (separate doc), or adopting AFP `IMP2` (different beast — see Rejected).

See also:
- `~/goblint-formalization-kb/wiki/meetings/2026-05-18-meeting3.md` §B — Alexandra's nested-constructor route + abbreviation caveat
- `~/goblint-formalization-kb/wiki/concepts/imp-language.md` — Datatype extension caveat
- `~/goblint-formalization-kb/wiki/concepts/imp2.md` — why we don't adopt AFP `IMP2` wholesale (naming collision, no soundness payoff)
- `~/goblint-formalization-kb/wiki/research/graph-library-evaluation.md` — parallel AFP-reuse case (graph libraries)
- Nipkow `HOL-IMP.AExp` — `datatype aexp = N int | V vname | Plus aexp aexp`; `aval`
- Nipkow `HOL-IMP.BExp` — `datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp`; `bval`

---

## Current state (implemented: Approach 1c)

`src/IMP2/IMP2_Syntax.thy` uses a **hybrid wrap** (see file header comment):

- Leaf forms `N`, `V`, `Bc` abbreviate `BaseN` / `BaseB` wraps over HOL-IMP
  `AExp` / `BExp`.
- Shared compound constructors (`Plus`, `Not`, `And`, `Less`) and extensions
  (`Minus`, `Times`, `Or`, `Eq`) are **native** IMP2 constructors (Nipkow's
  compound forms are typed over Nipkow datatypes, so they cannot express
  "Plus over our extended aexp" inside the wrap alone).
- `com` remains native and structurally identical to `HOL-IMP.Com`.
- `aval` / `bval` live in `IMP2_SmallStep.thy`; wrapped leaf cases delegate to
  `AExp.aval` / `BExp.bval`.

Trade-off documented in the theory: abbreviations `N`, `V`, `Bc` do not unfold
in pattern matches — leaf cases must spell `BaseN (AExp.N _)` etc.

---

## Original plan (pre-implementation snapshot)

The following described the **from-scratch** syntax before Approach 1c landed:

`src/IMP2/IMP2_Syntax.thy` redeclared **from scratch**:

```isabelle
datatype aexp =
    N     int
  | V     vname
  | Plus  aexp aexp        -- shared with HOL-IMP
  | Minus aexp aexp        -- our extension
  | Times aexp aexp        -- our extension

datatype bexp =
    Bc    bool
  | Not   bexp
  | And   bexp bexp
  | Or    bexp bexp        -- our extension
  | Less  aexp aexp
  | Eq    aexp aexp        -- our extension

datatype com = SKIP | Assign vname aexp | Seq com com
             | If bexp com com | While bexp com
```

with `aval` / `bval` in `IMP2_SmallStep.thy` (formerly planned as `IMP2_Semantics.thy`).

Comment that was removed from the file stated: *"We define IMP2 from scratch (not importing HOL-IMP.Com)…"*
That justification was weak after Meeting 3 §B. AFP-reuse stance: import + interpret/extend over redeclaration — **now partially realized via Approach 1c.**

---

## Approaches considered

### Approach 1 — Nested constructor wrap (Alexandra's suggestion)

```isabelle
theory IMP2_Syntax
  imports "HOL-IMP.AExp" "HOL-IMP.BExp" "HOL-IMP.Com"
begin

datatype aexp_ext =
    Base "HOL_IMP.aexp"
  | Minus aexp_ext aexp_ext
  | Times aexp_ext aexp_ext

abbreviation N_ext :: "int \<Rightarrow> aexp_ext"   where "N_ext n   \<equiv> Base (HOL_IMP.N n)"
abbreviation V_ext :: "vname \<Rightarrow> aexp_ext" where "V_ext x   \<equiv> Base (HOL_IMP.V x)"
abbreviation Plus_ext where "Plus_ext a b \<equiv> Base (HOL_IMP.Plus a b)"
```

**Pros:**
- Genuine reuse — Nipkow's `aexp` theorems apply directly inside the `Base` wrapper.
- Future-compatible with AFP `IMP2` arrays / `PScope` (same extension pattern).
- Aligns with Alexandra's recommendation.

**Cons (realistic — Meeting 3 §B):**
- **Abbreviations do not unfold in pattern matching.** Case analysis on `aexp_ext` still sees `Base (HOL_IMP.N n)` not `N_ext n`. Every `fun aval_ext` clause and every collecting/transfer lemma sees the `Base ...` shape and must case-split on the wrapped Nipkow constructor — duplication.
- `fun aval_ext` recurses *into* `Nipkow.aval` for `Base _` and recurses on `aexp_ext` for `Minus`/`Times`. Two recursions instead of one.
- `Plus` only lives inside `Base` → loses uniform "addition" treatment when collecting; sign / parity / interval transfer functions need a layer of unwrapping.
- Every existing proof in `IMP2_Collecting`, `IMP2_to_CFG`, `Constraint_System*`, `Domains/*` rewrites for the new shape.

### Approach 2 — Document local declaration + cite Nipkow

Keep current `IMP2_Syntax.thy` as-is, add provenance comments + a `theorem` block establishing the structural isomorphism with `HOL-IMP.aexp`:

```isabelle
text \<open>Our @{type aexp} mirrors @{type HOL_IMP.aexp} with two added constructors
  (Minus, Times). Constructor names and arities for shared constructors (N, V, Plus)
  are deliberately identical to ease cross-reading with Nipkow's HOL-IMP development.\<close>

primrec to_hol_imp_aexp :: "aexp \<Rightarrow> HOL_IMP.aexp option" where
  "to_hol_imp_aexp (N n)        = Some (HOL_IMP.N n)" |
  "to_hol_imp_aexp (V x)        = Some (HOL_IMP.V x)" |
  "to_hol_imp_aexp (Plus a b)   = ..." |
  "to_hol_imp_aexp (Minus _ _)  = None" |
  "to_hol_imp_aexp (Times _ _)  = None"

lemma aval_agrees_on_hol_imp:
  "to_hol_imp_aexp a = Some a' \<Longrightarrow> aval a s = HOL_IMP.aval a' s"
  by (induction a arbitrary: a') (auto split: option.splits)
```

**Pros:**
- Zero rewrite of downstream proofs.
- Makes the Nipkow correspondence formal (a checked theorem, not a comment).
- Cheap to land.

**Cons:**
- Doesn't actually *reuse* Nipkow's lemmas — only proves we could.
- Genuine AFP-reuse stance is not satisfied at the syntax level (it still is at the graph / solver level).

### Approach 3 — Adopt AFP `IMP2` (Lammich/Wimmer)

Rejected by Meeting 3 §B. AFP `IMP2` carries arrays, `PScope`, `Assign-Locals`, `combine-states` machinery — none needed; bridge re-statement would be expensive; no soundness payoff for sign / parity / interval. Naming collision (`src/IMP2/` ≠ AFP `IMP2`) also tracked separately.

---

## Recommendation — Approach 2 now, Approach 1 deferred

**Rationale.** Meeting 3 §B verdict was *"Stay on the current extended-HOL-IMP for now; eventual move toward a Nipkow-IMP extension (open: own further extension vs. partial AFP-IMP2 adoption — Alexandra's nested-constructor route is the realistic path)."* Approach 1's abbreviation-doesn't-unfold cost is real and falls on already-closed proofs (bridge, sign chain). Approach 2 codifies the correspondence + locks the AFP-reuse stance at the documentation layer without paying the rewrite cost.

**Trigger to revisit Approach 1.** Land Approach 1 only when we are touching `IMP2_Syntax` / `IMP2_SmallStep` anyway:

- When adding the interval domain (`Domains/Interval_Domain` already exists but is partial) — new transfer functions touch shared call sites.
- When adopting AFP `IMP2` arrays (if Octagon / relational stretch goal materialises).

Doing it standalone now = pure cost.

---

## Phase plan (Approach 2)

### Phase 0 — preflight (½ hr)

- [ ] Confirm `HOL-IMP` is in our session deps (`ROOT`); if not, add.
- [ ] Snapshot baseline build: `isabelle build -d . Goblint_Formalization`.

### Phase 1 — provenance comments + `to_hol_imp_aexp` projection (½ day)

**Touches:** `src/IMP2/IMP2_Syntax.thy`, `src/IMP2/IMP2_SmallStep.thy`.

1. Add `imports "HOL-IMP.AExp" "HOL-IMP.BExp"` to `IMP2_Syntax.thy` (alongside existing imports).
2. Add structural-correspondence `text` block citing Nipkow.
3. Define `to_hol_imp_aexp :: aexp \<Rightarrow> HOL_IMP.aexp option` and `to_hol_imp_bexp` as `primrec`s returning `Some` on shared constructors, `None` on `Minus`/`Times`/`Or`/`Eq`.
4. Prove `aval_agrees_on_hol_imp` and `bval_agrees_on_hol_imp`.
5. Replace the comment block at line 13 ("We define IMP2 from scratch...") with the new stance: "Constructors and arities mirror HOL-IMP.AExp / HOL-IMP.BExp for the shared subset; correspondence checked by `aval_agrees_on_hol_imp` / `bval_agrees_on_hol_imp`."

**Acceptance:** `isabelle build` green; new lemmas check; no existing proof changes.

### Phase 2 — naming-collision fix-up (½ day)

**Touches:** `src/IMP2/` → rename or document.

Meeting 3 §B flagged: *"`src/IMP2/IMP2_*.thy` and `src/CFG/IMP2_*.thy` are not AFP IMP2. They are a homegrown HOL-IMP extension."* This is a separate concern but fits naturally with this migration. Options:

- **A (rename)** — move `src/IMP2/` to `src/IMP_Extended/` or `src/Source_Lang/`. Updates `ROOT`, every `imports` clause, and `IMP2_to_CFG.thy` references. ~30 minutes of mechanical sed + build.
- **B (document)** — leave names; add a `README.md` under `src/IMP2/` clarifying the collision.

**Lean B** for now; revisit A if AFP `IMP2` is ever pulled in.

**Acceptance:** `src/IMP2/README.md` written; meeting note collision callout resolved.

### Phase 3 — KB log + cross-link (10 min)

- Append `wiki/log.md` entry: `[YYYY-MM-DD] compile | imp-syntax-nipkow-correspondence` documenting the Phase 1 + 2 work.
- Update `wiki/concepts/imp-language.md` §Datatype extension caveat with pointer to the new `to_hol_imp_aexp` lemma.

---

## Phase plan (Approach 1, deferred — sketch only)

Recorded for the day this becomes worth doing.

1. Replace `datatype aexp = ...` with `datatype aexp = Base "HOL_IMP.aexp" | Minus aexp aexp | Times aexp aexp`. Same for `bexp`.
2. Add `abbreviation` sugar for `N`, `V`, `Plus`, `Bc`, `Not`, `And`, `Less` mapping to `Base (HOL_IMP....)`.
3. Rewrite `aval` / `bval` to recurse into `HOL_IMP.aval` / `HOL_IMP.bval` for the `Base _` case, into our wrapper for added constructors.
4. **Forced rewrites** (Meeting 3 §B): every pattern-match clause in `IMP2_Collecting`, `IMP2_to_CFG`, `Constraint_System_Sound`, `Domains/Sign_Domain`, `Domains/Interval_Domain` that case-splits on `aexp` or `bexp` now sees `Base ...` shape — duplication unavoidable.
5. Provide `simp` rules `aval (Base a) s = HOL_IMP.aval a s` etc. and a `case_aexp_unfolded` rule for ergonomic case-analysis (compensates for abbreviation non-unfolding).
6. Re-derive bridge, sign chain, interval chain.

**Estimate:** ~1–2 weeks focused effort (depends heavily on whether small-step migration has also landed; combined migration is cheaper than serial).

---

## Files touched (Approach 2)

| File | Change | Net LOC |
|---|---|---|
| `src/IMP2/IMP2_Syntax.thy` | + `HOL-IMP.AExp` / `BExp` imports; comment block rewrite | +~15 |
| `src/IMP2/IMP2_SmallStep.thy` | + `to_hol_imp_aexp`/`bexp` + agreement lemmas | +~30 |
| `src/IMP2/README.md` | New — naming-collision callout | +~20 |
| `~/goblint-formalization-kb/wiki/log.md` | Append entry | +1 |
| `~/goblint-formalization-kb/wiki/concepts/imp-language.md` | Cross-link to agreement lemma | +1 line |

---

## What stays unchanged

- `com` datatype — already isomorphic to `HOL-IMP.Com`; Meeting 3 §B confirmed only `aexp`/`bexp` extend.
- Big-step `(c, s) \<Rightarrow> t` semantics — owned by small-step migration.
- Constructor names `N`, `V`, `Plus`, `Bc`, `Not`, `And`, `Less` — deliberately identical to Nipkow already; just not formally connected.
- `instance aexp :: countable`, `instance bexp :: countable` — keep (countability only; no `linorder` on AST).
- `edge_action :: linorder` in `CFG_Def` — implementation order for `cfg_edges_list` / `predecessor_list` (TD bridge), not language semantics.

---

## Risk register

| Risk | Likelihood | Mitigation |
|---|---|---|
| `HOL-IMP` not in session deps | Low | Add to `ROOT` `Goblint_Formalization` session. |
| Name clash with `HOL_IMP.N` / `HOL_IMP.V` / etc. via import | Medium | Use qualified names `HOL_IMP.N`; check `IMP2_Syntax.thy` constructors are not accidentally shadowed. |
| `aval_agrees_on_hol_imp` ends up vacuous (no caller cares) | Medium | Documented as provenance check; not load-bearing. The point is the formal correspondence record. |
| Approach 2 perceived as "not real AFP-reuse" | Medium | Document trigger conditions for Approach 1 (above) so the deferral is principled, not lazy. |

---

## Out of scope

- Approach 1 (nested constructor wrap) — phase plan sketched, deferred to next syntax-touching migration.
- Adopting AFP `IMP2` — rejected by Meeting 3 §B; tracked in `wiki/concepts/imp2.md`.
- `com` extension (e.g. arrays, procedures) — no current driver.
- Renaming `src/IMP2/` — handled via README callout for now.
