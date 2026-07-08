# M3 — Context-bounding lifters / termination

Status: **PLANNED. Partly cheap, partly open research.** Splits into three
sub-tracks of very different maturity. Lands on a worktree branch off `main`;
`main` stays green.

Design basis: `GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` Gap 6 (termination) and the
context-sensitivity axis; `docs/NON_GOALS.md` P1 (the `solve_dom` vendor
hypothesis). Goblint reference: the three lifters (Context Widening, Loopfree
Callstring, Context Gas), [Context Gas and friends, STTT
2025](https://link.springer.com/content/pdf/10.1007/s10009-025-00803-3.pdf),
implemented in `src/lifters` of
[goblint/analyzer](https://github.com/goblint/analyzer).

---

## 1. Goal and motivation

Replace "the context set is finite by fiat and the solver terminates by
assumption" with *proved* termination — first for a finite-height domain
(closing P1 honestly for Sign), then by modelling at least one Goblint
context-bounding lifter that keeps the encountered-context set finite *on the
fly* rather than by a static type bound.

Motivation: the analysis currently rests on two unproved finiteness facts —
`'c::finite` (contexts) and `solve_dom` (termination). Goblint's precision on
recursive/procedural programs comes precisely from *not* fixing the context set
statically: it discovers contexts and bounds them dynamically (Context Gas
decrements per nested call; Loopfree Callstring drops repeated frames). Modelling
a lifter is what makes our context-sensitivity terminate on recursion the way
Goblint's does, and closing P1 for Sign removes the largest honest gap in the
soundness story.

## 2. Relation to Goblint (source references)

- Goblint's TD solver applies widening at stabilization points; termination on a
  finite-height lattice follows from ascending-chain stabilization
  (`GOBLINT_SPEC_FULL_ALIGNMENT_PLAN.md` Gap 6).
- Context bounding is *not* in the solver but in **lifters** wrapping the `Spec`:
  Context Widening, Loopfree Callstring, Context Gas — `src/lifters`, [STTT
  2025](https://link.springer.com/content/pdf/10.1007/s10009-025-00803-3.pdf).
- Context Gas: called functions are analyzed with decremented gas, and
  context-insensitively once gas hits zero; proven to encounter only finitely many
  contexts during fixpoint iteration — the termination lever for recursion.
- Loopfree Callstring: bounds by collapsing repeated stack frames — the simplest
  lifter to model (a syntactic idempotent map on call strings).

## 3. Current status in the Isabelle formalization

**Reusable:**

| Artifact | File | Role for M3 |
| --- | --- | --- |
| `solve_dom` hypothesis (P1) at every analyzer soundness site | `Sign_Side_Soundness.thy`, `Mixed_Flow_Sound.thy`, `Sign_Named_Global_Eff.thy`, examples | the assumption M3a discharges for Sign |
| Sign domain (finite height `{SBot,SNeg,SZero,SPos,SNonNeg,STop}`) + `abstract_domain`/`sound_domain` classes | `Sign_Domain.thy`, `Abstract_Domain.thy` | the finite-height object for M3a |
| `widen` operator on `abstract_domain`; interval widening (bot-law + real narrowing) | `Interval_Domain.thy` | the widening whose termination M3 would need for intervals |
| vendored `TD_side` + its `TD_side_upd_rule` / warrowing locale | `vendor/td-verification` | the solver whose termination is assumed |
| `'c::finite` context instances (`sign_gctx`, bounded call strings via M1) | `Example_Finite_Sign_Context_Analysis.thy`, M1 | the static bound M3b replaces with a dynamic one |

**Not present:** any termination proof for `TD_side`; any dynamic (non-`finite`)
context-bounding construction; any lifter model.

## 4. Missing pieces

- **M3a:** a proof `∀v. solve_dom v` for the Sign constraint system by
  lattice-height / ascending-chain induction — no widening needed (finite height).
- **M3b:** a Loopfree Callstring (or Context Gas) lifter: a context wrapper +
  a proof that only finitely many contexts are encountered, replacing the
  `'c::finite` fiat with a dynamic bound. Depends on M1 for a call-string context.
- **M3c:** general `TD_side` termination with widening on infinite-height domains
  (intervals) — a termination proof for the vendored solver itself. Open research;
  the vendor leaves termination to the user.

## 5. Dependencies

- **M3a is independent** of M1, M2, and the rest of M3 — do it anytime; only needs
  the Sign domain + the constraint system.
- **M3b depends on M1** (needs a call-string context to bound) and is independent
  of M2.
- **M3c depends on nothing here but is gated by upstream** (vendored solver
  termination) — likely requires changes in `td-verification`, so it is future
  work, not a repo-local slice.

## 6. Risks and proof obligations

| ID | Obligation / risk | Severity | Note |
| --- | --- | --- | --- |
| T1 | Sign ascending chains stabilize ⇒ `solve_dom` | Low | finite height (6); standard well-founded argument. The safe, cheap win. |
| T2 | The height-induction connects to the vendored solver's `solve_dom` shape | Med | the solver's termination predicate must be *derivable*, not merely "the lattice is finite" — check the exact `TD_side` obligation shape before promising T1 closes P1 |
| T3 | Loopfree Callstring lifter: finitely-many-contexts proof | Med | idempotent frame-collapse; finiteness of the image set |
| T4 | Context Gas: monotone context wrapper + finite gas ⇒ finite contexts | Med-High | decrementing gas is a well-founded measure; interaction with `mono_sides` when gas hits zero (context collapse) needs care |
| T5 | General widening termination (M3c) | **Open** | vendored solver does not prove it; out of local scope |
| T6 | Don't bump build timeouts to mask a slow termination witness | Low | per repo build-timeout policy |

## 7. Concrete stages (independently buildable commits)

Three sub-tracks; ship M3a alone if that is all that is wanted.

### M3a — Sign termination (standalone, cheap)

| Stage | Commit | Content |
| --- | --- | --- |
| a1 | `feat(term): Sign lattice finite-height + well-founded ascending chains` | height measure on `sign`; strict-ascent well-foundedness lemma |
| a2 | `feat(term): solve_dom for the Sign constraint system` | discharge `∀v. solve_dom v` from a2's chain argument in the exact vendored predicate shape (T2); replace the P1 hypothesis in `Sign_Side_Soundness` with the proved fact |
| a3 | `docs(term): P1 closed for Sign; still assumed for infinite-height domains` | update `NON_GOALS.md` / `NEXT_STEPS.md` P1 stance for the Sign case |

### M3b — Loopfree Callstring lifter (needs M1)

| Stage | Commit | Content |
| --- | --- | --- |
| b1 | `feat(lifter): loopfree call-string context wrapper` | idempotent frame-collapse map on the M1 call-string context; abstraction lemma vs raw call string |
| b2 | `feat(lifter): finitely-many-contexts under loopfree collapse` | prove the encountered-context image is finite without a static `k` bound |
| b3 | `feat(lifter): sound analyzer under the loopfree lifter` | the lifted context still satisfies `digest_env_sound`; precision not worse than raw k-CFA on a recursive witness |

### M3c — General widening termination (future)

| Stage | Commit | Content |
| --- | --- | --- |
| c1 | `docs(term): scope note — TD_side widening termination is upstream` | record that M3c requires a `td-verification` change; keep as future work, not a local slice |

## 8. Deliverables and exit criteria

- **M3a:** `∀v. solve_dom v` proved for Sign; the P1 hypothesis removed from at
  least `Sign_Side_Soundness`. Green, no `sorry`. Honest closure of the largest
  assumption for one domain.
- **M3b:** a loopfree-callstring lifter with a proved finite-context bound and a
  sound analyzer instance; a recursive witness that terminates without a static
  `k`. Green, no `sorry`.
- **M3c:** a scope note only — no code; the obligation is upstream.

## 9. Expected impact

- **Executability:** M3a/M3b preserve it (finite constructions code-generate).
  M3b additionally lets a *recursive* program terminate under a dynamically
  bounded context, closer to Goblint's runtime behaviour.
- **Soundness:** M3a strengthens the theorem — soundness becomes unconditional for
  Sign (no `solve_dom` hypothesis). M3b keeps soundness additive. No regression.
- **Precision:** neutral for M3a. M3b trades a static `k` cut for a dynamic
  loop-free cut — on recursion it can be *more* precise than a fixed small `k`
  while still terminating (Goblint's motivation for the lifters).

## 10. Classification

- **M3a:** high-value, low-cost — closes an honest gap; between optional and
  thesis-strengthening (an unconditional Sign theorem is a cleaner headline).
- **M3b:** Goblint-faithfulness (models a real lifter); optional; depends on M1.
- **M3c:** future work, upstream-gated, out of local scope.
