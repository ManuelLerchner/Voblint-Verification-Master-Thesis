# Decision: keep structural expressions; anchor soundness to AFP IMP2 via a one-way bridge

Status: **AMENDED** 2026-06-12. Supersedes the earlier "do not build on IMP2"
call. The executability rationale below is unchanged and still load-bearing;
what changed is the *goal*. We do not adopt IMP2's type, but we now project
**into** it as a semantic anchor. Migration plan: `docs/AFP_IMP2_REBASE_MIGRATION.md`.

## Question

Can we cut self-maintained code by reusing AFP IMP2's `aexp`/`bexp` (and
`aval`/`bval`) instead of our hand-rolled structural ones?

## Decision

**Two parts.**

1. **Do not adopt** IMP2's reflected-operator `aexp`/`bexp`. Keep the structural
   `aexp`/`bexp` + per-domain `aval`/`bval`. The analyzer stays executable and
   runs only on the structural type (rationale below — unchanged).
2. **Do build a one-way bridge** `to_imp2 :: aexp => IMP2.aexp` (+ `bexp`, +
   state embedding) and re-anchor soundness to IMP2's semantics. The bridge
   flows structural -> IMP2 only; we never dispatch on IMP2's reflected `f`, so
   executability is untouched. This is *not* dedup (the expression layer is ~30
   lines either way) — it buys a recognized semantics and array-readiness. See
   the amended alternatives table and `docs/AFP_IMP2_REBASE_MIGRATION.md`.

## Rationale - apply vs dispatch

AFP IMP2 reflects operators as opaque HOL functions:

```
datatype aexp = ... | Binop (int => int => int) aexp aexp | Unop (int => int) aexp
```

- **Concrete evaluation applies the operator** - executable:
  `aval (Binop f a b) s = f (aval a s) (aval b s)`. Calling `f` on concrete
  ints computes fine; you never inspect `f`.
- **Abstract evaluation must dispatch on the operator** - not executable. To get
  the abstract counterpart (`sign_plus`, `sign_times`, ...) you must decide
  *which* operator `f` is. That is equality on `int => int => int`, which is
  **undecidable and has no code-generator instance** in Isabelle.

Our analyzer is executable by design (concrete demos compute, GraphViz output,
real abstract results). Executable operator dispatch requires a **matchable
finite tag**, i.e. structural constructors (`Plus`/`Minus`/`Times`) - exactly
the current design.

### Restricting `f` to a chosen set does not help execution

Allowing only `f in {(+),(*),(-)}` via a well-formedness invariant works for
**soundness proofs** (case-split under the assumption). It does **not** make the
analyzer executable: dispatching on `f` at runtime still needs decidable
function equality, and even checking `f in {...}` is `f = (+) \/ ...` - again
non-executable. To execute you must store a finite **tag** instead of a
function, and tagged operators *are* the current structural design (one level of
indirection added, nothing gained).

### The non-executable escape hatch

The best abstract transformer `binop_abs f x# y# = alpha { f x y | x in gamma x#,
y in gamma y# }` is sound for any `f`, so one could define abstract evaluation
over reflected operators - but it is non-executable (`alpha` of the infinite
image of an opaque `f`). It also forces a Galois `alpha`; our soundness is
`gamma`-only with per-operator lemmas (`sign_plus_sound`). Rejected.

## Why AFP IMP2 gets away with reflection

IMP2 is a program-verification framework (VCG / Hoare logic), not an abstract
interpreter. It only ever **applies** operators and reasons via verification
conditions; it never maps an operator to an abstract counterpart. Reflection is
free - even convenient - on the apply side. The executability seen in IMP2 is
concrete execution, which does not transfer to abstract interpretation.

**Sharpening (do not overclaim).** Reflection is not incompatible with abstract
interpretation *as a proof*. With a well-formedness assumption on `f` (monotone,
or `f in {(+),(-),(*)}`) the best transformer `binop_abs f = alpha . image f` is
sound by case-split; we too could "get away with it" for the soundness theorem.
The blocker is **executability alone**, and assumptions do not lift it: the
runtime check `f = (+)` is still function equality with no code instance. So the
decision hinges on one requirement - an executable analyzer - not on any
theorem-level obstruction. Drop that requirement and reflected reuse is viable;
keep it and structural tags are forced.

## Consequences

- The structural `aexp`/`bexp` (~30 lines, `IMP2_Syntax`) and each domain's
  `aval`/`bval` (4-6 lines, e.g. `aval_sign`) stay hand-maintained. Irreducible.
- We already reuse the *correct* upstream: Nipkow's structural `HOL-IMP.AExp` /
  `BExp` at the leaves (`BaseN "AExp.aexp"`), extended with `Minus`/`Times`.
- Adding operators (div, mod, ...) is **additive** to the structural `aexp`: one
  constructor + one sound abstract transfer per operator. Not a fork of IMP2.

## Alternatives considered (all rejected)

| Option | Verdict |
| --- | --- |
| Reflected operators + best transformer (`alpha . image`) | non-executable |
| Reflected operators + restrict `f` to a finite set | dispatch still non-executable |
| **Embed our structural syntax *into* IMP2 (one-way bridge)** | **ADOPTED** - no dedup, but anchors soundness to a recognized semantics + array-ready (see migration doc) |
| Reuse IMP2 commands/procedures only, keep our expressions | forks IMP2 over its `aexp`; our `pcom` is ~300 lines anyway |

## Related

- `docs/AFP_IMP2_REBASE_MIGRATION.md` - the migration plan implementing part 2
  (the one-way bridge + soundness re-anchoring).
- `docs/IP_ONLY_CONSOLIDATION.md` - where the real duplication (~3500 lines,
  intra spine vs IP spine) actually lives. The expression layer is not it.
