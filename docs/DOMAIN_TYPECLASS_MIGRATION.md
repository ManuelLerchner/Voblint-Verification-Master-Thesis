# Migration: `sound_domain` / `abstract_domain` — Locales to Type Classes

## Motivation

* One canonical `gamma` per domain type (no per-interpretation prefix).
* Global `⟦_⟧` notation.
* Fewer `interpretation` blocks; simpler downstream theorem statements.
* Easier instantiation of new domains.

Backward-analysis infrastructure is **not** converted (see Scope below).

---

## Scope

### In scope — convert

| File | What changes |
|---|---|
| `src/Analysis/Domains/Abstract_Domain.thy` | `locale sound_domain` → `class sound_domain`; `locale abstract_domain` → `class abstract_domain`; `gamma_state` / `widen_state` become global definitions; `context sound_domain` blocks become standalone class lemmas |
| `src/Analysis/Domains/Sign_Domain.thy` | `interpretation sign_domain: abstract_domain` → `instantiation sign :: abstract_domain`; drop local notation |
| `src/Analysis/Domains/Interval_Domain.thy` | `interpretation ivl_domain: abstract_domain` → `instantiation ivl :: abstract_domain`; drop local notation |
| `src/Analysis/Equations/Constraint_System.thy` | `locale sound_transfer = sound_domain + ...` → `locale sound_transfer` with `'a::sound_domain` constraint; same for `sound_effectful_transfer`; `context sound_domain` block → standalone lemma |
| `src/Analysis/Solver/TD_Side_CFG.thy` | `st.gamma_state` → `gamma_state`; `sound_transfer γ tf` interpretation signature update |
| `src/Analysis/Solver/TD_Side_Eff_Sound.thy` | `gamma_state` references unchanged in text but now resolve globally |
| `src/Analysis/Solver/TD_Side_Eff_Soundness.thy` | `sound_domain.gamma_state γ (...)` → `gamma_state (...)` |
| `src/Analysis/Solver/TD_Side_Eff_Pipeline.thy` | `sound_domain.gamma_state γ (...)` → `gamma_state (...)` |

### Partially in scope — restructure, keep locale form

| File | What changes |
|---|---|
| `src/Analysis/Domains/Abstract_Domain.thy` `backward_domain` | Drop `= sound_domain γ for γ ...`; add `'a::sound_domain` type constraint; rename `γ` → `gamma` throughout; the `for γ` parameter disappears entirely |

### Out of scope — untouched

* All transfer-function locale bodies (proof scripts inside `sound_transfer`, `sound_effectful_transfer`, `backward_domain`).
* Solver theories beyond the `sound_domain.gamma_state γ` call sites listed above.

---

## Invariant: `abs_state` is NOT a `sound_domain` instance

`abs_state = vname => 'a` is a function space over `'a::sound_domain`.
Its concretisation is `gamma_state :: 'a abs_state => store set`, which is a
separately-named global function, **not** the class operation `gamma`.

There must be no `instance "fun" :: (type, sound_domain) sound_domain`.
Attempting one would require defining `gamma :: (vname => 'a) => int set`,
which is exactly `gamma_state` — conflating the two breaks the design.

The existing `instance "fun" :: (type, bounded_semilattice_sup_bot) bounded_semilattice_sup_bot`
stays and is sufficient for the lattice structure.

---

## Target design

### `class sound_domain`

```isabelle
class sound_domain = bounded_semilattice_sup_bot +
  fixes gamma :: "'a => int set"
  assumes gamma_bot: "gamma bot = {}"
  assumes gamma_mono: "a ≤ b ==> gamma a ⊆ gamma b"
```

### `class abstract_domain`

```isabelle
class abstract_domain = sound_domain +
  fixes widen :: "'a => 'a => 'a"
  assumes widen_ub1: "gamma a ⊆ gamma (widen a b)"
  assumes widen_ub2: "gamma b ⊆ gamma (widen a b)"
```

### Global `gamma_state`

```isabelle
definition gamma_state ::
  "('a::sound_domain) abs_state => store set"
where
  "gamma_state sigma = {s. ALL x. s x : gamma (sigma x)}"

notation gamma_state ("\<lbrakk>_\<rbrakk>")
```

One declaration in `Abstract_Domain.thy`; all domain-local notation lines deleted.

### Global `widen_state`

```isabelle
definition widen_state ::
  "('a::abstract_domain) abs_state => 'a abs_state => 'a abs_state"
where
  "widen_state sigma1 sigma2 = (%x. widen (sigma1 x) (sigma2 x))"
```

### Class-polymorphic lemmas

Moved out of `context sound_domain`:

```isabelle
lemma gamma_sup_ub1:   "gamma a ⊆ gamma (a ⊔ b)"     for a b :: "'a::sound_domain"
lemma gamma_sup_ub2:   "gamma b ⊆ gamma (a ⊔ b)"
lemma gamma_sup_sound: "gamma a ∪ gamma b ⊆ gamma (a ⊔ b)"
lemma gamma_state_mono:      "sigma1 ≤ sigma2 ==> [|sigma1|] ⊆ [|sigma2|]"
lemma gamma_state_bot:       "[|bot|] = {}"
lemma gamma_state_sup_ub1:   "[|sigma1|] ⊆ [|sigma1 ⊔ sigma2|]"
lemma gamma_state_sup_ub2:   "[|sigma2|] ⊆ [|sigma1 ⊔ sigma2|]"
lemma gamma_abs_sup_set_ub:  "finite S ==> x : S ==> gamma x ⊆ gamma (Finite_Set.fold (⊔) bot S)"
```

### `locale sound_transfer` — restructured, not deleted

```isabelle
locale sound_transfer =
  fixes tf :: "'a::sound_domain domain_transfer"
  assumes tf_sound_assign: ...
  assumes tf_sound_assume: ...
  assumes tf_sound_assume_not: ...
  assumes tf_sound_enter: ...
```

The `= sound_domain +` inheritance is removed. The type constraint `'a::sound_domain`
on `tf` brings in `gamma` and `gamma_state` from the class. All `⟦_⟧` uses inside
the locale's assumptions and lemmas resolve via the global notation.

`sound_effectful_transfer` receives the same treatment: drop `= sound_domain +`,
add `'a::sound_domain` to the type of `etf`.

### `locale backward_domain` — restructured, not deleted

```isabelle
locale backward_domain =
  fixes
    meet     :: "'a::sound_domain => 'a => 'a"
    and aval_abs  :: "aexp => 'a abs_state => 'a"
    and inv_less  :: "bool => 'a => 'a => 'a * 'a"
    and inv_plus  :: "'a => 'a => 'a => 'a * 'a"
    and inv_minus :: "'a => 'a => 'a => 'a * 'a"
    and inv_times :: "'a => 'a => 'a => 'a * 'a"
  assumes
    meet_sound: "n : gamma a ==> n : gamma b ==> n : gamma (meet a b)"
    ...
```

The `= sound_domain γ for γ` inheritance and the explicit `γ` parameter are
removed. Every occurrence of `γ` in assumptions and proof bodies becomes `gamma`.
`gamma_state_def` in proof unfoldings becomes the global definition.

---

## Migration order

### Step 1 — introduce classes alongside locales (non-breaking)

Add `class sound_domain` and `class abstract_domain` at the top of
`Abstract_Domain.thy`, before the existing locale definitions.
Do not delete anything.
Add a global `gamma_state` definition using the class `gamma`.
Keep the locale `gamma_state` definition; it is still needed by the
locale-based proofs until Step 6.

Build check: `get_diagnostics` on `Abstract_Domain.thy` should be clean.

### Step 2 — global `gamma_state` notation

Remove the `notation gamma_state ("\<lbrakk>_\<rbrakk>")` line from inside
`context sound_domain`.
Add it at the top level pointing to the new global `gamma_state`.
Remove the local notation lines from `Sign_Domain.thy` and
`Interval_Domain.thy`.

Fix any breakage in those files (references to `sign_domain.gamma_state`
and `ivl_domain.gamma_state` should become bare `gamma_state`).

Delete the now-redundant bridging lemmas:
* `sign_gamma_state_conv` (Sign_Domain.thy)
* `ivl_gamma_state_conv` (Interval_Domain.thy)

### Step 3 — class-polymorphic helper lemmas

Move `gamma_sup_ub1`, `gamma_sup_ub2`, `gamma_sup_sound`,
`gamma_state_mono`, `gamma_state_bot`, `gamma_state_sup_ub1`,
`gamma_state_sup_ub2`, `gamma_abs_sup_set_ub` out of
`context sound_domain` blocks and into standalone lemmas with
`'a::sound_domain` type constraints.

Keep the locale versions temporarily via `context sound_domain begin lemma ... = ... end`
wrappers that delegate to the class lemmas, if downstream proofs still use
the locale-qualified names. Remove those wrappers in Step 6.

Move `widen_state` out of `context abstract_domain` to a global definition.

### Step 4 — restructure `sound_transfer` and `sound_effectful_transfer`

In `Constraint_System.thy`:

1. Change `locale sound_transfer = sound_domain + fixes tf :: "'a domain_transfer"`
   to `locale sound_transfer = fixes tf :: "'a::sound_domain domain_transfer"`.
2. Same for `sound_effectful_transfer`.
3. Replace the `context sound_domain begin ... end` block (around
   `combine_states_sound`) with a standalone lemma.

In `TD_Side_CFG.thy`:
* Update `interpret st: sound_transfer γ tf` — drop the `γ` argument.
* Replace `st.gamma_state` with `gamma_state` throughout.

Build check: `get_diagnostics` on `Constraint_System.thy` and
`TD_Side_CFG.thy`.

### Step 5 — restructure `backward_domain`

In `Abstract_Domain.thy`:
* Drop `= sound_domain γ for γ :: ...` from `locale backward_domain`.
* Add `'a::sound_domain` constraint to `meet` (first `fixes` parameter);
  the constraint propagates to the full locale.
* Replace all `γ` with `gamma` in assumptions, `afilter`, `bfilter`, and
  their proof bodies.
* `gamma_state_def` unfoldings already refer to the same definition as before;
  no proof strategy changes expected.

Build check: `get_diagnostics` on `Abstract_Domain.thy`.

### Step 6 — convert Sign domain

In `Sign_Domain.thy`:
* Replace `interpretation sign_domain: abstract_domain gamma_sign widen_sign`
  with `instantiation sign :: abstract_domain begin ... end`.
* Instance proof discharges `gamma_bot`, `gamma_mono`, `widen_ub1`, `widen_ub2`
  (these match the existing interpretation obligations exactly).

Build check: `get_diagnostics` on `Sign_Domain.thy` and all downstream theories.

### Step 7 — convert Interval domain

Same pattern as Sign.

`interpretation ivl_domain: abstract_domain gamma_ivl widen_ivl`
becomes `instantiation ivl :: abstract_domain`.

### Step 8 — update Solver files

In `TD_Side_Eff_Soundness.thy` and `TD_Side_Eff_Pipeline.thy`:
* Replace `sound_domain.gamma_state γ (...)` with `gamma_state (...)`.
  The explicit `γ` argument is gone; the class resolves it from the type.

These are mechanical substitutions; no proof logic changes.

### Step 9 — remove locale `sound_domain`

Prerequisites before deleting:
* Steps 1–8 complete and `get_diagnostics` clean on every touched file.
* No `context sound_domain` blocks remain anywhere in `src/`.
* No `= sound_domain` locale inheritance remains in `Constraint_System.thy`.
* No `sound_domain.gamma_state γ` call sites remain in Solver files.

Then delete the `locale sound_domain` block from `Abstract_Domain.thy`.

### Step 10 — remove locale `abstract_domain`

Prerequisites: Sign and Interval instantiations build cleanly; no
`= abstract_domain` locale inheritance anywhere; `widen_state` is global.

Delete the `locale abstract_domain` block from `Abstract_Domain.thy`.

### Step 11 — full build gate

```bash
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

Show green output before declaring done.

---

## Risk register

| Risk | Mitigation |
|---|---|
| `sound_transfer` / `sound_effectful_transfer` break when `sound_domain` locale is deleted | Step 4 must precede Step 9; confirm no `= sound_domain` remaining before deletion |
| `sound_domain.gamma_state γ` call sites in Solver survive to Step 9 | Grep `sound_domain.gamma_state` before Step 9; zero hits required |
| `backward_domain` proof bodies use `γ` after rename | Step 5 `get_diagnostics` is the gate; do not proceed to Step 6 with errors there |
| `abs_state` accidentally gets a `sound_domain` instance somewhere | Grep for `instance.*fun.*sound_domain` before final build; must be absent |
| Notation conflict from domain-local `notation gamma_state` lines | Step 2 removes both; do not leave them after Step 2 completes |
| Bridging lemmas `sign_gamma_state_conv` / `ivl_gamma_state_conv` left as dead code | Delete in Step 2 when the qualified names they bridge disappear |

---

## Success criteria

After Step 11:

* `⟦σ⟧`, `gamma`, `widen` resolve globally without qualification.
* No `sign_domain.gamma_state`, `ivl_domain.gamma_state`, or
  `sound_domain.gamma_state` references anywhere in `src/`.
* No `interpretation ... abstract_domain` or `interpretation ... sound_domain`
  blocks; replaced entirely by `instantiation ... :: abstract_domain`.
* Solver theorems require only `'a::sound_domain` or `'a::abstract_domain`
  type constraints; no locale interpretation prefixes.
* `isabelle build` green on `Voblint_Formalization`.
