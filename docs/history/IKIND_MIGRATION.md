# Ikind migration — machine-integer types, wraparound, and casts

Status: **PLANNED, not started** (2026-08-24). Full per-variable integer
kinds (width + signedness), wraparound concrete semantics, explicit casts,
and ikind-parameterised abstract transfer. This is the "Integer width and
wraparound" register row's closure path, executed in full rather than the
cheaper single-global-ikind variant (that variant was evaluated and
rejected in favour of this one; its useful staging survives as B1/B4/B6
below). Lands stage-by-stage on worktree branches; `main` stays green
throughout.

Register anchor: `GOBLINT_ALIGNMENT_REGISTER.md`, row *Integer width and
wraparound*.

---

## 1. Goal and motivation

Give VIMP a machine-integer type system so that:

- every variable has a declared kind `ik` (e.g. `uint32`), and the
  concrete semantics computes in that kind — `aval` wraps, exactly where
  Goblint's `norm ik` sits;
- interval (and every other domain's) transfer can use `range ik` as a
  hard bound: `x := nondet()` on a `uint32` yields `[0, 4294967295]`, not
  `[-inf, +inf]`, and widening has a floor/ceiling to land on;
- width-dependent domains become definable at all — bitfield masks need a
  bit count; Goblint's `BitfieldDomain` and `DefExc` are undefinable over
  mathematical `int` (`src/Analysis/Instances/Defexc/` is an empty
  placeholder today for exactly this reason);
- overflow becomes an analyzable event instead of a fiction: a new
  regression family can pin wraparound and cast behaviour.

This is a change to the semantic reference model, not a domain addon.
Soundness of an `ik`-bounded refinement is only stateable if concrete
values actually stay in `range ik`, so the concrete semantics moves first
and everything downstream re-proves against it.

## 2. Relation to Goblint

Source-checked 2026-08-24 against `goblint/analyzer` `master`
(`src/cdomain/value/cdomains/intDomain0.ml`,
`src/cdomain/value/cdomains/int/bitfieldDomain.ml`):

- Every `IntDomain` operation is ikind-parameterised: `add ik x y`, most
  returning `t * overflow_info` (`{overflow: bool; underflow: bool}`).
- `Size.range ik` computes the representable `[min, max]` from
  `Size.bit ik = bytesSizeOfInt ik * 8`; `norm ik` clamps/wraps results
  back into that range.
- Unsigned kinds always wrap. Signed behaviour is configured by
  `sem.int.signed_overflow`: the default treats a possible signed
  overflow as "go to top and warn"; `assume_wraparound` wraps;
  `assume_none` assumes overflow cannot happen.
- `cast_to` converts between kinds by modular arithmetic (`Z.erem` plus
  range adjustment); CIL has already made every conversion an explicit
  `CastE` node by the time Goblint sees the program.
- `IntDomTupleImpl` threads one `ikind` through all component domains;
  `IntDomLifter` pairs an abstract value with its ikind where the value
  must carry its own kind.
- `BitfieldDomain` represents a value as a pair `(z, o)` of may-be-zero /
  may-be-one masks; join/meet are bitwise or/and, order is bitwise
  implication, arithmetic goes through tristate numbers, and its
  reduction edges (`of_interval`, `refine_with_interval`,
  `refine_with_congruence`) are exactly the `Int_Refinement` fan-out
  shape this repo already has.

What this migration reproduces: the ikind parameter, `range`/`norm`,
wraparound semantics, explicit casts, ikind-parameterised transfer with
the overflow-to-top default, and (as the payoff stage) the bitfield
domain with its interval reduction edges.

What it deliberately does not reproduce is listed per decision in §3 and
recorded in the register row.

## 3. Locked design decisions

### D1 — Kind set: fixed-width stdint kinds, not C's platform kinds

```text
datatype ikind = I8 | U8 | I16 | U16 | I32 | U32 | I64 | U64
```

with `ik_bits :: ikind => nat`, `ik_signed :: ikind => bool`,
`ik_min / ik_max / ik_range`, and `ik_norm`. Surface keywords are
`int8 .. int64`, `uint8 .. uint64`, plus `int` = `int32` and `uint` =
`uint32` aliases. Goblint's ikind is C's (`IChar .. IULongLong`) with
platform sizes from CIL; VIMP has no platform, so stdint-style fixed
widths realize the same mechanism without CIL's machine model. A closed
datatype is finite, executable, and code-generates cleanly.

### D2 — Carrier stays HOL `int`; `norm ik` is Euclidean remainder

No `HOL-Library.Word`. The store remains `vname => int` with a typedness
invariant (`s x : range (Gamma x)`); `norm ik` is defined by `mod 2^bits`
plus signed re-centering (two's complement). Rationale: `gamma :: 'a =>
int set` stays the class operation it is today (the
`DOMAIN_TYPECLASS_MIGRATION.md` outcome is untouched), no conversions
between word lengths ever appear in gamma statements, and `Size.cast`'s
`Z.erem` is exactly this definition upstream.

### D3 — Concrete signed overflow is two's-complement wraparound

VIMP's semantics stays total: every arithmetic result is normed, signed
included. C makes signed overflow undefined; VIMP has no UB machinery
and defining wrap keeps `pstep` total and executable. The abstract layer
is then free to be less precise than wrap (D7) — going to top is sound
over wrap; `assume_none` (which is *unsound* over wrap) is not modelled.
The `sem.int.signed_overflow` configuration surface is a precision knob
upstream; here only its sound points exist.

### D4 — Explicit casts only; no promotions or usual arithmetic conversions

The type checker requires both operands of a binary operation to have the
same ikind and the RHS of an assignment to have the LHS variable's ikind;
mixing kinds requires a source-level cast `(uint32) e`, a new
`Cast ikind exp` constructor. Comparisons and logical operators yield
`int32`-typed 0/1 (C's `int`). This is CIL-faithful, not a shortcut:
Goblint never sees an implicit conversion — CIL has already inserted
every cast — so a checker that rejects mixed-kind operations models the
post-CIL program, and `cast_to` remains the only conversion mechanism.
C's integer promotions are CIL's job and are out of scope here.

### D5 — Literals stay `N int`, range-checked by the checker

No ikind field on `N`. A literal is well-typed at whatever kind its
context expects, provided its value lies in `range ik`; the checker
enforces the range. This avoids re-threading a kind annotation through
every existing theory, example, and pin for a field that static typing
determines anyway. (CIL constants carry a kind; here the typing judgment
supplies it.)

Where no expected kind exists — a comparison's operands, a logical
operator's operands — the operand kind is *synthesized*: a variable
forces its declared kind (`esyn`), and a literal-only operand tree
defaults to `int32`, exactly C's rule that a bare integer constant has
type `int`. Synthesis is load-bearing for semantics, not a convenience:
the value of `200 + 100 < 250` depends on the kind the sum wraps at
(`44 < 250` at `uint8`, C's `300 < 250` at `int32`), so an
underdetermined operand kind would make evaluation ill-defined.
`VIMP_Typing.thy` pins the pair.

### D6 — Ikinds are threaded statically, not stored in abstract values

`typeof Gamma e :: ikind option` is a total function on the typed AST,
and every variable's kind comes from the typing environment carried by
`imp_prog`/`proc_rep`. Transfer functions receive the ikind from the
syntax at each site; abstract values do not carry their kind. This
avoids `IntDomLifter` entirely. Upstream needs the lifter because a
`D.t` value can flow between differently-kinded expressions; here the
checker's equal-kind discipline (D4) makes the kind a function of the
program point.

Consequence: `cast_abs` needs only the *target* kind. Values are
mathematical integers already in their source kind's range, so a cast's
concrete action is `norm ik'` alone — the from-kind that `cast_to
~from_ik` needs upstream is representation bookkeeping this encoding does
not have.

### D7 — Abstract default: overflow-to-top; precise wraparound is incremental

Every forward transfer's first sound version is: if the mathematical
result provably lies in `range ik`, behave as today; otherwise return
top. One uniform lemma pattern (`in-range ==> norm ik n = n`; otherwise
the result is in `gamma top`) discharges the bulk of the ~256 arithmetic
soundness obligations mechanically. This matches Goblint's default
signed-overflow behaviour and unsigned `norm`-to-top-on-imprecision.
Precise wrapped transfer (e.g. interval `norm` producing the wrapped
hull) is a per-operation precision upgrade layered on afterwards, domain
by domain, with the soundness statement unchanged.

### D8 — Untyped declarations default to `int32`

`global g;`, untyped formals, and undeclared locals keep parsing and mean
`int32`. This keeps the entire `.vimp` corpus (157 fixtures), the quoted
programs in `src/Examples` (~28k LOC), and every existing pin
syntactically valid; their semantics is preserved wherever no 32-bit
overflow occurs (the corpus uses small literals throughout — checked
2026-08-24, the only large literal is in a comment). The deviation from
C (implicit `int`) is recorded in the register row.

### D9 — Locals are declared in a function prologue, not by statements

New per-function `local <ty> x, y;` lines before the body, lowered into
the typing environment — no new `com` constructor, no new CFG edge kind,
no `pstep` rule. This is CIL-faithful (`fundec.slocals` declares every
local up front) and keeps declarations static information. Undeclared
assigned variables fall under D8.

## 4. Stages

Each stage gates independently (batch build green, plus the named
checks) before the next begins.

### B1 — `VIMP_Ikind.thy`

New theory in `src/VIMP/` (imported below `VIMP_Expr`): the `ikind`
datatype, `ik_bits`, `ik_signed`, `ik_min`, `ik_max`, `ik_range`,
`ik_norm`, and the algebra the later stages consume:

- `ik_norm_in_range`, `ik_norm_id`, `ik_norm_idem`;
- congruences `ik_norm ik (ik_norm ik a + ik_norm ik b) = ik_norm ik (a
  + b)` (and for `-`, `*`, unary minus) — the lemmas that let transfer
  proofs move `ik_norm` around;
- executable `by eval` pins for the bounds and wrap boundaries, stated
  in power form rather than decimal literals (`ik_max U32 = 2 ^ 32 - 1`,
  `ik_norm U8 (2 ^ 8) = 0`, etc.).

Gate: batch build; no consumer yet.

### B2 — Grammar and AST

`grammar/vimp.yaml` only, then regenerate both frontends:

- type keywords (D1) and a `ty` nonterminal;
- `globals_decl` gains an optional type: `global uint32 g, h;`;
- typed formals: `void f(uint32 n, int8 m)`; untyped stays legal (D8);
- prologue `local` declarations (D9);
- cast production `(ty) e` at unary precedence, lowering to `Cast`;
- `exp` gains `Cast ikind exp` (this is a datatype change in
  `VIMP_Syntax.thy` alongside the generated grammar).

Also: `VIMP_Source_Print.thy`, `tests/property/strategies.py` (generate
typed programs and casts), round-trip and print-stability checks, new
`09-parser` fixtures. Gate: `pixi run grammar-check`, `pixi run
property`, batch build of `Voblint_VIMP`.

### B3 — Typing layer

Typing environment on `proc_rep`/`imp_prog` (formals + locals + globals
+ the return slot), `typeof`, and an executable checker
`wf_typed_program` folded into the `wf_source_program` gate that every
soundness theorem and the CLI already pass through. Checker rules: D4
equal-kind discipline, D5 literal ranges, D8 defaults. Gate: batch
build; checker `by eval` pins; CLI rejects an ill-typed fixture.

### B4 — Concrete semantics

- The typed evaluator is `taval` (`VIMP_Typing.thy`), evaluating at an
  expected kind with normed leaves; `taval_syn` evaluates at the
  synthesized kind (branch conditions, special-call arguments). `Cast
  ik' e` becomes a `taval` case when the constructor lands (B2). The
  untyped `aval` survives alongside it only while `src/CFG/` and the
  abstract layers still cite it; B5/B6 delete it.
- `pstep` gains the typing environment as a third relation parameter
  (`pstep Γ gs Π`): `Assign` and `ret_var` evaluate at the target
  variable's kind, actuals at their formal's kind (`map2`), `Special`
  and `combine_assign` norm their writes. `prog_tyenv` is the
  program-level seam (the `I32` default until declarations land).
  Store-typedness preservation is proved end-to-end
  (`pstep_preserves_styped`, `psteps_preserves_styped`,
  `pcompletes_preserves_styped`).
- The CFG mirror (`edge_step`, `special_step`, `combine_collect`,
  `call_enter`) changes in lockstep, and `Control_Simulation.thy` plus
  the collecting layers re-prove. The simulation carries stores rather
  than computing on them, so this is expected to be broad but mechanical.

Gate: batch build of `Voblint_VIMP` + `Voblint_CFG`.

### B5 — Core interface reshape

The pivot, and the only structural surgery:

- `Abstract_Arithmetic.thy`'s `expression_domain_sound` drops its
  `{plus, minus, times}` sort constraints; abstract arithmetic becomes
  locale-fixed ikind-parameterised operations
  (`a_plus :: ikind => 'a => 'a => 'a`, ...), with `ev` consuming the
  typed AST. The `sound_domain` class itself — `gamma`, `widen`,
  `gamma_state` — is untouched.
- `backward_domain`'s `inv_plus/inv_minus/inv_times` (and `afilter`,
  `feasible`, `bfilter` above them) gain the ikind at each node from
  `typeof`; the `inv_*_sound` obligations are restated over
  `norm ik (n1 + n2)` with operands in range.
- New locale-fixed `a_cast :: ikind => 'a => 'a` with
  `v : gamma a ==> norm ik' v : gamma (a_cast ik' a)`.
- `numeric_ops` / `special_ops` records and `domain_transfer` pick up
  the environment; `abstract_numeric_queries` and `Abstract_Checks` are
  restated (comparison queries are over already-normed values, so their
  statements barely move).

Gate: batch build of `Voblint_Core` with a single toy instance.

### B6 — Domains

Per domain — Sign, Interval, Parity, Congruence, then `int_dom` and
`Int_Refinement` — apply D7: forward ops and `inv_*` gain the ikind with
the overflow-to-top pattern, plus `a_cast`. Domain-specific notes:

- **Interval** keeps the `eint` carrier and its `order_top`; boundedness
  enters through transfer: `Nondet_Int` at kind `ik` returns
  `[ik_min, ik_max]`, and `widen_ivl` re-targets moved bounds at
  `ik_min/ik_max` instead of `MinInf/PlusInf` where the site's kind is
  known. Side effect worth pursuing separately: per-kind intervals have
  finite height, which bears on the `solve_dom` hypothesis (M3
  territory, not this migration's obligation).
- **Congruence** is the one domain needing new mathematics, not
  re-proof: a residue class mod `m` survives `norm ik` only when `m`
  divides `2^bits`; otherwise the transfer goes top on possible
  overflow. Upstream Congruence has the same guard structure in `norm`.
- **Sign / Parity** are nearly free: parity is preserved by `mod 2^bits`
  (`bits >= 1`); sign transfers use the overflow-to-top default (a
  wrapped `SPos + SPos` can be negative when signed).

Gate: batch build of `Voblint_Analysis`; per-domain `by eval` pins for
one wraparound and one cast case each.

### B7 — Exec mirror, dispatch, codegen, CLI

`Exec_Backward.thy`, per-domain `*_Exec.thy`, `Analysis_Config` /
`Analyse_Dispatch`, the `code_identifier` list (new theories:
`VIMP_Ikind` at minimum — the module-cycle rule in `AGENTS.md` applies),
`pixi run codegen`, `cli/` lowering of type syntax (Zarith stays; kinds
are static). Gate: `codegen-regression`, `cli-build`,
`codegen-modules`.

### B8 — Pins and fixtures

- Sweep the `by eval` pins (~600) — churn concentrates where `Nondet` /
  widening previously produced `MinInf/PlusInf` and now produce kind
  bounds.
- Existing 157 fixtures stay valid under D8; expected verdicts move only
  where bounds add precision.
- New regression group `23-machine-ints/` (or next free number):
  unsigned wrap (`precision/`), signed wrap, cast truncation and
  sign-reinterpretation, an overflow-driven check that becomes UNKNOWN
  under overflow-to-top (`known-imprecision/`, mechanism: D7 transfer
  discards the wrapped hull), nondet-bounded-by-kind refinement.

Gate: `tests/run.py` green; full batch build.

### B9 — Payoff: bitfield domain, precise wrapping transfers

- **Bitfield**: `(z, o)` may-be-zero/may-be-one masks over the site
  kind's width, as a fifth `int_dom` component (register row "Value
  domains": the record edit, `Int_Refinement` edges `of_interval` /
  `refine_with_interval` / `refine_with_congruence`, dispatch, and
  `code_identifier` all move together). This also supplies the
  interval-to-congruence-shaped reduction pattern that register row
  names as missing.
- **Precise wrap**: upgrade interval (then congruence) transfer from
  overflow-to-top to the wrapped hull where profitable, one operation at
  a time, each with its own pin.
- `DefExc` becomes definable; whether to port it is a separate decision,
  not part of this migration.

Gate: batch build; new fixtures; register row updated to its final
state.

## 5. What stays untouched

- `src/Core/Solver/**` and `vendor/td-verification` (~44k LOC):
  polymorphic in the domain carrier; nothing there mentions `int`.
- The `sound_domain` / `abstract_domain` class hierarchy, `gamma :: 'a
  => int set`, `gamma_state`, widening classes: gamma's codomain stays
  `int set` because the carrier stays `int` (D2).
- The D/G framework, context routing, check verdict lattice, GraphViz
  layer: they consume `'a abs_state` opaquely.

## 6. Risks and open questions

| Risk | Handling |
| --- | --- |
| `Control_Simulation.thy` (2.5k LOC) re-proof blows up | B4 gates alone; the simulation moves stores, does not compute on them; if a case resists, the fix is at the lemma level (store-typedness invariant strengthening), not a redesign |
| Congruence x wrap needs real new theory | Scoped in B6: top-on-overflow is the sound floor; divisor-of-`2^bits` precision is the only precise case attempted |
| Pin churn misread as regressions | B8 does the sweep in one change per example session, with the D8 argument (small literals) written into the commit |
| Grammar change destabilizes both frontends | B2 is grammar-only and gates on `grammar-check` + property fuzzing before any semantics moves |
| `bfilter`'s 435 call sites | The call sites take the environment through `numeric_ops`/locale parameters, not per-site edits; B5 confirms the shape on one toy instance before B6 fans out |
| Checker rejects programs Goblint would accept (mixed kinds) | Recorded as the D4 deviation: the model is the post-CIL program; revisit only if a promotion-bearing frontend is ever modelled |

## 7. Register and roadmap bookkeeping

- `GOBLINT_ALIGNMENT_REGISTER.md` row *Integer width and wraparound*:
  status moves from "recorded scope boundary" to active migration
  pointing here; the row's final state after B9 should record D1, D3,
  D4, D6, D8 as the surviving deviations.
- Row *Value domains*: B9 updates the component list and the reduction-
  edge inventory.
- `ROADMAP.md` "Numeric precision" no longer claims the semantic
  reference model is fixed; a "Machine integers" extension direction
  points here.
- `docs/GLOSSARY.md`: `ikind`, `norm`, typed store invariant, once B1
  lands.
