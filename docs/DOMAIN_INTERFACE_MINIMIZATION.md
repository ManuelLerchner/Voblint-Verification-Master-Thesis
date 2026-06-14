# Migration — minimize the domain-author interface

Status: **IN PROGRESS.** Authored 2026-06-14. Migration doc + plan landed;
`.thy` edits pending (blocked on I/Q server start).

## Goal

Make the locale interface a new-domain author must satisfy *meaningful and
minimal*: one locale to interpret, no dead obligations. Today a domain author
reverse-engineers the contract from `Sign_Domain.thy` and proves **six** things
across **three** locales, one of which (`widen`) is consumed by nothing on the
soundness path.

End state: interpret **one** locale (`sound_transfer`) — `gamma` + 2 axioms,
4 transfer functions + 4 soundness lemmas + 1 monotonicity lemma — and the
full end-to-end soundness theorem (`side_analyse_ip_collect_sound_exit_pruned`)
follows. `widen` / `abstract_domain` move off the required path.

## The problem (audit findings)

The end-to-end soundness theorem `side_analyse_ip_collect_sound_exit_pruned`
lives in `context sound_transfer`, where

```
sound_transfer = sound_domain + tf + 4 gamma-soundness axioms
sound_domain   = fixes gamma + gamma_bot + gamma_mono
```

A domain author must additionally supply, today:

| # | Obligation | Where | On soundness path? |
|---|------------|-------|--------------------|
| 1 | `bounded_semilattice_sup_bot` instances | `Sign_Domain.thy:200-235` | yes (the carrier) |
| 2 | `gamma` + `gamma_bot`/`gamma_mono` (`sound_domain`) | `:241-246` | yes |
| 3 | `widen` + `widen_ub1`/`widen_ub2` (`abstract_domain`) | `:239-254` | **no** |
| 4 | `domain_transfer` record (4 fns) | `:394-398` | yes |
| 5 | 4 transfer-soundness lemmas (`sound_transfer`) | `:426-440` | yes |
| 6 | `tf_mono` (`apply_tf` monotone) | `:505` | yes, but free-floating |

Two concrete defects:

1. **`widen` is a dead abstraction (#3).** `rg widen` outside its own def file
   and Sign returns zero hits on the soundness path. The equation system
   `side_cfg_T_ip` joins with `(sup)`, *not* `widen` — widening is not even
   plumbed into the solver. Termination is *assumed* via the
   `side_cfg_ip_solve_dom ...` hypothesis, not derived from widening. So a
   finite-domain author pays for `widen` + 2 axioms with no payoff. This is the
   Kappelmann "false abstraction" smell: a parameter that is neither proven
   invariant nor consumed.

2. **`tf_mono` is split off from `sound_transfer` (#6).** It is a raw `\<And>`
   premise on the `td_cfg_side_ip_solver` solver locale, re-stated as an
   explicit hypothesis on `side_analyse_ip_collect_sound_exit_pruned`, and
   discovered separately from the four γ-soundness obligations. There is no
   single locale whose interpretation discharges everything the pipeline
   consumes.

`combine_abs` (call/return merge: globals from callee-exit, locals from caller)
is correctly **not** a domain parameter — it is language semantics, proven sound
once generically in `sound_domain`. Keep it fixed.

## Decisions on record

- **Remove `widen` from the *required* path, do not delete the abstraction.**
  `abstract_domain` (+ `widen` + axioms) stays defined in `Abstract_Domain.thy`
  for the interval/widening termination track (`INTERVAL_REINTRODUCTION_PLAN.md`,
  `EXIT_ROOTED_SOLVE_MIGRATION.md`, ROADMAP). It is simply no longer on the
  soundness path and no longer interpreted by the reference domain.
- **Fold `tf_mono` into `sound_transfer`.** One locale = the full contract.
- **Re-point the `sign_domain` interpretation `abstract_domain -> sound_domain`.**
  `gamma_state` is defined in `sound_domain`, so `sign_domain.gamma_state` and
  every downstream use keep resolving unchanged.
- **Drop `widen_sign` from Sign.** Sign is the reference template; the template
  must be minimal. The `abstract_domain` locale stays type-checked once the
  interval domain lands and interprets it.
  - *Considered and rejected:* keeping a separate
    `interpretation sign_widen: abstract_domain gamma_sign widen_sign` in Sign so
    the widening locale stays exercised before intervals land. Rejected — it
    re-introduces the dead obligation into the reference template and muddies the
    "one locale" story. The interval domain will exercise `abstract_domain`; a
    type-checked-but-uninterpreted locale is acceptable until then.

## Plan (additive, build-gated)

### Step 1 — `sound_transfer` gains `tf_mono` (`Constraint_System.thy`)

Add to the `sound_transfer` locale:

```
assumes tf_mono:
  "\<And>a s1 s2. s1 \<le> s2 \<Longrightarrow> apply_tf tf a s1 \<le> apply_tf tf a s2"
```

(`apply_tf` is already in scope, defined at `Constraint_System.thy:43`.)

### Step 2 — drop the redundant premise (`TD_Side_IP_Soundness.thy`)

`side_analyse_ip_collect_sound_exit_pruned` is in `context sound_transfer`.
Remove its explicit

```
assumes tf_mono: "\<And>a s1 s2. ..."
```

and rely on the locale fact (the `interpret ip: td_cfg_side_ip_solver g tf bot s0
using tf_mono ...` line resolves `tf_mono` from the enclosing locale unchanged).

`td_cfg_side_ip_solver` (the pure-solver locale, no γ) keeps its own `tf_mono`
assumption — it has no `sound_domain` context. `side_analyse_ip_eq_env_at`
(`TD_Side_IP_Interface.thy:136`, standalone) keeps its `tf_mono` too.

### Step 3 — Sign: minimize the template (`Sign_Domain.thy`)

1. Move the monotonicity block (`sign_plus_mono1` ... `sign_tf_mono`,
   `:442-509`) to **above** the `sign_sound_tf` interpretation (before `:426`).
   Dependencies (`assume_not_sign_mono :310`, `enter_sign_mono :360`,
   `assign_sign :317`, `sign_tf :394`) all precede that point.
2. Change `interpretation sign_domain: abstract_domain gamma_sign widen_sign`
   to `interpretation sign_domain: sound_domain gamma_sign`; drop the two
   `widen_*` `show` goals.
3. Add a fifth `show` to the `sign_sound_tf: sound_transfer` interpretation:
   `by (rule sign_tf_mono)` (per-action; the locale obligation is over
   `apply_tf`, which `sign_tf_mono` already states).
4. Delete `widen_sign` (`:104-107`) — now unused.

### Step 4 — fix the one call site (`Sign_Side_IP_Soundness.thy:30`)

```
[OF sign_sound_tf.sound_transfer_axioms sign_tf_mono side_solve_dom gs]
```
becomes
```
[OF sign_sound_tf.sound_transfer_axioms side_solve_dom gs]
```
(`tf_mono` is now bundled inside `sound_transfer_axioms`.)

### Step 5 — docs

- `src/Analysis/Domains/README.md`: state the **contract** (the one locale +
  its obligations), not just a file list. Note `abstract_domain` is the
  optional widening/termination extension, not required for soundness.
- This file: flip status to DONE with a completion record + green build log.

## Risk / blast radius

- `sign_domain.gamma_state` is used across `Example_IMP2_Coverage`,
  `Example_Trace_Digest_Precision`, `Example_Side_Proc_Global`,
  `Sign_Side_IP_Soundness`, and within `Sign_Domain`. All resolve through
  `sound_domain.gamma_state` after the re-point — **no rename needed**.
- `sound_transfer` has exactly **one** interpretation (`sign_sound_tf`); adding
  an assumption breaks only that one, fixed in Step 3.
- Theorems in `context sound_transfer` that do not interpret the solver
  (`side_collect_sound_ip_at`, the `Trace_IP_Analysis_Sound` digest overlay)
  are unaffected — they never referenced `tf_mono`.

## Verification

Gate: full `isabelle build` green (not I/Q alone), per repo policy:

```bash
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

## New-domain author contract (target end state)

To add a domain `'a` and obtain end-to-end soundness:

1. Carrier instances: `order`, `order_bot`, `sup`, `semilattice_sup`,
   `bounded_semilattice_sup_bot` — **before** any interpretation.
2. `gamma :: 'a => int set`; prove `gamma bot = {}` and `a <= b ==> gamma a
   \<subseteq> gamma b`.
3. Four transfer functions in a `domain_transfer` record.
4. Interpret `sound_transfer gamma tf`: discharge the 4 γ-soundness goals
   (assign/assume/assume-not/enter) + 1 monotonicity goal (`apply_tf` monotone).

Then `side_analyse_ip` runs the verified solver and
`side_analyse_ip_collect_sound_exit_pruned` gives soundness against the IP
collecting semantics at the exit. No `widen`, no separate mono plumbing.

Widening (for infinite-height domains that need termination, e.g. intervals)
is the *optional* `abstract_domain` extension — see
`INTERVAL_REINTRODUCTION_PLAN.md`.
