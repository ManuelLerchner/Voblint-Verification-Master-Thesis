# Ikind migration — machine-integer types, wraparound, and casts

Tracking issue: #167.

Status: **IN PROGRESS** (2026-08-25). B1 (`VIMP_Ikind.thy`, on
`take_bit`/`signed_take_bit`) and B4's VIMP half (typed `pstep`, kind
preservation, procedure return kinds, and — landed this session — C-style
integer promotion and truncate-once-at-the-boundary assignment/call/return
conversion, see the revised D4 below) are landed and batch-green
(`Voblint_VIMP`); B2 (grammar: optional type annotations, default
`int32`) is landed for globals/formals -- see its subsection below for
the corpus-conversion decision this session made. B4's CFG half is
**done and batch-green**: every CFG-session theory (`CFG_Def.thy`,
`Located_Exec.thy`, `CFG_Local_Trace.thy`, `LTR_Collect.thy`,
`LTR_Abstract.thy`, `VIMP_Proc_to_CFG.thy`, `CFG_Transfer.thy`,
`Control_Residual.thy`, `Compile_Invariants.thy`,
`Control_Simulation.thy`, `CFG_Prune.thy`, `Compile_Certificate.thy`,
`Compile_Locality.thy`, `Located_LTR.thy`) is threaded with `Γ`, `EA_Ret`'s
baked return kind, and the same promotion/truncate-once fixes; a clean,
isolated `isabelle build ... Voblint_CFG` passes at 100% for all
thirteen theories (2026-08-25). This surfaced a genuine downstream break
in `Voblint_Core`, closed the same session: `Voblint_Core`'s own generic
D/G-framework `Γ`-threading (44+ theories, `isabelle build ...
Voblint_Core` at 100%) is likewise **done and batch-green** -- see B5's
subsection below for what it covered, the genuine `combine_collect`
soundness gap it surfaced (closed with an explicit, honest `ret_ok`
premise pending B5's `a_cast`), and what's still open
(`Voblint_Analysis`/`CLI`/`Examples`, B6/B7 territory). Full per-variable integer
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

### D2 — Carrier stays HOL `int`; `norm ik` is `take_bit`/`signed_take_bit`

No `HOL-Library.Word`. The store remains `vname => int` with a typedness
invariant (`s x : range (Gamma x)`). Rationale: `gamma :: 'a => int set`
stays the class operation it is today (the `DOMAIN_TYPECLASS_MIGRATION.md`
outcome is untouched), no conversions between word lengths ever appear in
gamma statements, and `Size.cast`'s `Z.erem` is exactly this truncation
upstream. `'a word` is not the carrier because its width lives in the HOL
*type* (`'a::len`) — one type per width — whereas VIMP's `store` is one
`vname => int` shared by every variable regardless of kind, with `ikind`
consulted as a runtime value from the typing environment (D6); giving the
carrier a type-level width would force either monomorphising every
program to one kind or an existential wrapper across widths, reopening
the `IntDomLifter`-style value/kind pairing D6 rejects.

`norm ik` is still built on the primitive `'a word` itself is built on:
`ik_norm ik n = signed_take_bit (bits-1) n` (signed) /
`take_bit bits n` (unsigned), from `HOL.Bit_Operations` (part of `Main`,
no import needed) — `'a word` is defined as `int` quotiented by
`take_bit`-equivalence, so this is the same truncation primitive a
bit-vector carrier would use, without the type-level width. This
replaced an earlier hand-rolled `mod 2^bits` definition with matching
Euclidean-remainder proofs; the library's existing arithmetic-interaction
lemmas (`take_bit_add`, `signed_take_bit_add`, ...) directly discharge
`ik_norm_add`/`_diff`/`_mult`/`_uminus`, and the same `ring_bit_operations`
class carries bitwise AND/OR/XOR/shifts on `int` — the B9 bitfield domain
needs exactly these and gets them without separate bit-vector proof work.

### D3 — Concrete signed overflow is two's-complement wraparound

VIMP's semantics stays total: every arithmetic result is normed, signed
included. C makes signed overflow undefined; VIMP has no UB machinery
and defining wrap keeps `pstep` total and executable. The abstract layer
is then free to be less precise than wrap (D7) — going to top is sound
over wrap; `assume_none` (which is *unsound* over wrap) is not modelled.
The `sem.int.signed_overflow` configuration surface is a precision knob
upstream; here only its sound points exist.

### D4 — Explicit casts for genuine kind mismatches; integer promotion IS modeled

**Revised 2026-08-25** (superseding the original "promotions are CIL's job,
out of scope" text below): a Goblint-source audit this session
(`cabs2cil.ml`'s `arithmeticConversion`/`integralPromotion`, `doBinOp`'s
`makeCastT` on both operands, `Base.evalbinop_base`) found that CIL does
*not* leave narrow-kind operands as-is — every kind narrower than `int` is
promoted to `int` (ISO 6.3.1.8) *before* any binary/comparison/logical
operator runs, and both operands are cast to the common post-promotion
type before Goblint's analyzer ever sees the `BinOp`/`Return`/`Set` node.
Treating promotion as out of scope silently diverged from Goblint: a
`uint8` operand in a comparison or arithmetic expression wrapped at 8 bits
instead of behaving as `int32`, and a narrow-typed assignment/call-arg/
return conversion truncated at *every* intermediate operator instead of
once at the boundary.

Both are now modeled, minimally:

- `ik_promote :: ikind => ikind` (`VIMP_Ikind.thy`) promotes any kind
  narrower than `I32` to `I32`; `I32` and wider are unaffected (`I32`
  represents every value of a narrower kind, so the "promote to unsigned
  int" branch of the C rule never triggers for this fixed kind set).
- `esyn`'s variable case applies `ik_promote` at the one leaf
  (`V x`); `kjoin`/`opk` are otherwise unchanged, so every synthesized
  kind — `Plus`/`Minus`/`Times`, `Less`/`Eq`, `Not`/`And`/`Or`,
  `special_result`'s `Min`/`Max` — is promoted for free, with no separate
  promotion step at each use site.
- `Assign`, `Call`'s actual-argument binding, and `ReturnSome` (`pstep`,
  mirrored in `edge_step`'s `EA_Assign`/`EA_Ret`) evaluate the RHS/actual/
  return expression at its own synthesized (now-promoted) kind via
  `taval_syn`, then apply `ik_norm` to the externally-required kind
  *once*, matching CIL's cast-once-at-the-conversion-boundary discipline
  instead of forcing the destination's kind down through every
  intermediate operator.

The original D4 text below (same-kind operand checking, explicit casts for
genuine mismatches) is otherwise still accurate and unrevised: `wt_exp`
still requires an operator's two operands to check at the *same* kind
(now understood as: either their shared declared kind, or their shared
promoted kind — `wt_exp`'s `V x` case accepts both), and a genuine
cross-kind mismatch still needs an explicit cast once the `Cast`
constructor lands. What changes is only that "same kind" no longer means
"same *declared* kind" when both operands are narrower than `int` — it
means same kind *after* promotion, exactly as CIL computes it.

Original text (2026-08-24, promotion out of scope):

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

`grammar/vimp.yaml` only, then regenerate both frontends. **Landed**
(2026-08-25) for globals and formals, staged as follows:

- Type keywords are the eight explicit-width stdint spellings only
  (`int8`/`uint8`/.../`int64`/`uint64`). **No bare `int`/`uint` alias
  keywords**, contrary to this doc's original D1 sketch: an Isabelle
  mixfix literal becomes an inner-syntax token in every importing
  theory, so an `int` keyword would shadow HOL's own `int` type token
  repo-wide -- confirmed by a load failure when tried. The unannotated
  default (see below) already supplies the `int32` meaning, so the
  alias was dropped rather than worked around.
- A `ty` nonterminal, lowering to the `ikind` constructors.
- `globals_decl` gains a second production, `global <ty> ids ;`
  (`globals_decl_typed`), alongside the untyped one -- an annotation is
  syntactically optional per `global` line, not per name; a program may
  carry any number of `global` lines so differently-kinded globals are
  declarable. Optionality is two grammar productions, not an epsilon:
  Isabelle mixfix has no empty derivation, the same constraint that
  already forced `call0`/`callret0`.
- Formals: a new `formal` nonterminal (`formal_untyped` / `formal_typed`,
  same optional-annotation shape), and `formals` becomes a list of
  `formal` instead of `IDENT`.
- **Staging decision (this session, per direction): every annotation
  is optional and defaults to `int32`; the untyped corpus is converted
  to explicit annotations later, in its own change, not as part of B2.**
  This lands the parser/AST/`imp_prog` surface without forcing a
  simultaneous rewrite of 157 regression fixtures and ~28k lines of
  `src/Examples` quotations. Untyped declarations lower to `(name,
  None)` and contribute no entry to the new `imp_prog.declared_kinds`
  field; `prog_tyenv` (`VIMP_Notation.thy`) looks the name up in
  `declared_kinds` and falls back to `I32`.
- `imp_prog` gains `declared_kinds :: (vname * ikind) list`; `mk_program`
  (existing callers, zero kinds) is now a thin wrapper around the new
  `mk_program_typed` (procs, main, globals, kinds).
- `VIMP_Notation.thy`'s hand-written `program { ... }`/`global` syntax and
  `parse_translation` were rewritten to match: `global` is now its own
  nonterminal pair (`imp2_gdecl`/`imp2_gdecls`, one-or-more lines) instead
  of a single optional `ids` argument, and `prog_tr` collects annotated
  kinds from both declared globals and every procedure's formals into
  the program's `declared_kinds` list.
- Not yet done: `local` prologue declarations (D9), the `Cast` expression
  constructor and its unary-precedence syntax, `VIMP_Source_Print.thy`,
  `tests/property/strategies.py`, and the grammar-check/property/corpus
  gates below -- deferred to a follow-up B2 continuation alongside the
  corpus conversion.

Remaining gate before B2 is called closed: `pixi run grammar-check`,
`pixi run property`, batch build of `Voblint_VIMP`, and the corpus
conversion (untyped -> explicit annotations) with its own fixture sweep.

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
- `pstep` gains the typing environment as a relation parameter
  (`pstep Γ gs Π`): `Assign` and `ret_var` evaluate at the target
  variable's kind, actuals at their formal's kind (`map2`), `Special`
  and `combine_assign` norm their writes. `prog_tyenv` is the
  program-level seam (the `I32` default until declarations land).
  Store-typedness preservation is proved end-to-end
  (`pstep_preserves_styped`, `psteps_preserves_styped`,
  `pcompletes_preserves_styped`).
- **Landed** (2026-08-25): procedure return kinds. `proc_decl` gains
  `ret_kind :: ikind option` (`None` for `void`; `proc_decl_of` stays
  the void constructor so no existing call site changes,
  `proc_decl_of_typed` is new). `Return`'s expression norms at the
  *callee's* declared kind, not a single global lookup — the earlier
  draft normed every `Return` in every procedure against one fixed
  `Γ ret_var`, silently truncating any procedure declaring a return
  kind other than that one. Fixed by making the active return kind a
  fourth `pstep` configuration component (`com × store × frame list ×
  ikind`), set by `Call` from the callee's declared kind and
  saved/restored across the call boundary via `Frame`'s new third
  field — a return-address-register discipline, not a frame-stack
  lookup: an earlier attempt derived the active kind from the frame
  stack's head instead, which made `pstep_frame_extend` genuinely
  false (a `Return` step's target value depended on frames beyond the
  ones it itself touches, once a nested `Call`'s `Seq2`-wrapped result
  could re-expose a shallow one-level check). `in_flight_unwind` is
  defined recursively through `Seq` for the same reason. The
  store-typedness invariant needed one addition, `sstyped` (full
  `styped`, weakened to `rstyped` — every variable but `ret_var` — only
  while the command is mid-`Unwind`): `Return`'s own write targets the
  active kind, not any single fixed one, so no per-name invariant
  covers it, but the gap is provably transient — `combine_env` reads
  `ret_var` from the *saved* caller frame at `Restore`/`UnwindAct`,
  never the finishing callee store, so typedness is restored the
  instant the frame pops. The external guarantee
  (`pcompletes_preserves_styped`) still concludes full `styped`,
  unchanged. Batch-verified: `Voblint_VIMP` green
  (`SESSION=Voblint_VIMP pixi run build`).
- The CFG mirror (`edge_step`, `special_step`, `combine_collect`,
  `call_enter`) does **not** yet change in lockstep — confirmed broken
  by the batch build, not merely inferred: `Voblint_CFG` fails at
  `CFG_Def.thy`'s `special_step`, whose `special_result` call now needs
  a `Γ`, and `combine_collect` calls the now-4-arg `combine_assign`.
  There is no safe placeholder fix: `ik_norm` always wraps into *some*
  finite range, so handing either function an arbitrary `Γ` introduces
  truncation the surrounding untyped `aval`-based CFG semantics does
  not have anywhere else, and would only coincide with `pstep`'s own
  (now-typed) norm by accident of today's all-default-`I32` corpus, not
  by construction. Closing this requires threading the *same* `Γ`
  `pstep` uses through `edge_step`/`special_step`/`call_enter`/
  `combine_collect`/`cstep`, then re-proving `Control_Simulation.thy`'s
  source/compiled bisimulation (2.5k lines) against it. Scoped as its
  own gated stage below (B4-CFG), not attempted with B4's VIMP half.

Gate (B4-VIMP): batch build of `Voblint_VIMP`. **Done.**

Gate (B4-CFG): batch build of `Voblint_CFG` after threading `Γ` through
`edge_step`/`special_step`/`call_enter`/`combine_collect`/`cstep` and
re-proving `Control_Simulation.thy`. **Done** (2026-08-25): verified with
an isolated clean build (`isabelle build -d <AFP> -d <TD> -d <repo>
Voblint_CFG`, i.e. `-d` not the project's default `-D`, since `-D`
auto-selects every repo-local session and had been masking the
`SESSION=` scoping in `scripts/mk/build.sh` -- the session-only build
target was previously untested in isolation for that reason). All
thirteen `Voblint_CFG` theories report 100%; zero errors. The
`Control_Simulation.thy` re-proof (~2.6k lines after threading) is the
one line item the risk table below flagged as the size risk; it closed
without a redesign -- the one real defect found mid-proof was a
transcription typo in `csim_call_base`'s `shows` clause (`proc_ret_kind
Π p` where the callee's `proc_ret_kind Π q` was needed), not a
tactic-strength or invariant problem.

`scripts/mk/build.sh`'s `SESSION=` variable does not scope
`pixi run build` to one session -- `-D "$REPO_ROOT"` auto-selects every
repo-local session regardless of the trailing target, so
`SESSION=Voblint_CFG pixi run build` still builds the full graph and
still fails downstream in `Voblint_Core` until the Core-leg below lands.
Use a direct `isabelle build -d ... Voblint_CFG` invocation (lowercase
`-d`, register-only) to gate one session in isolation.

`Voblint_Core`'s own `Γ`-threading ripple -- the break B4-CFG's completed
build surfaced -- is **done and batch-green** (2026-08-25), confirmed by
an isolated `isabelle build -d <AFP> -d <TD> -d <repo> Voblint_Core`: all
44+ theories report 100%, zero errors. This threaded `Γ` through every
Core-session call site of `edge_step`/`edge_collect`/`special_result`/
`call_enter`/`call_enter_store`/`combine_collect`/`activation_collect`/
`valid_ltr`/`ltr_collect`/`sound_transfer_for`/`sound_dg_spec`/
`sound_dg_hooks` and their locale `fixes` lists (`Constraint_System.thy`,
`Constraint_System_Sound.thy`, `DG_Framework.thy`, `DG_Soundness.thy`,
`DG_Base.thy`, `DG_Base_Exec.thy`, `DG_Ctx_Activation.thy`,
`DG_Analysis_Adapter.thy`, `DG_LTR_Sound.thy`, `Routed_Context.thy`,
`Routed_Context_Unit.thy`, `Call_String_Routed_Context.thy`,
`Entry_State_Routed_Context.thy`, `Exec_DG_Refines.thy`,
`Activation_Local_Sound.thy`, `Activation_Backbone.thy`,
`Call_String_Collecting_Refinement.thy`), gave `ikind` a `linorder`
instance (`VIMP_Ikind.thy`, needed by `CFG_Enumeration.thy`'s `derive`),
and baked `EA_Ret`'s/`dgs_return`'s resolved return kind into every
executable-mirror dispatcher that pattern-matches `edge_action` directly
(`apply_tf`, `dg_spec_step`, `unit_dg_spec_st_for`, `base_dg_spec_st_for_lifted`).

This is *not* full B5 (below): it is Core's generic, domain-agnostic
solver-facing layer -- the D/G framework, routed-context machinery, and
the constraint-system interface -- becoming type-check-and-prove clean
against the now-`Γ`-parameterised concrete semantics, without touching
`Abstract_Arithmetic.thy`'s numeric operations or adding `a_cast`. One
genuine semantic gap surfaced and needed a real (not mechanical) fix:
`combine_collect`'s concrete definition now truncates the return value to
the *destination's* declared kind (`ik_norm (Γ x)`, from B4-VIMP), but
`combine_collect_abs` still publishes the callee's return slot verbatim --
precisely truncating it soundly would need a domain-level cast operation
(matching Goblint's `IntDomain0.cast_to`, source-checked in `base.ml`/
`valueDomain.ml` 2026-08-25: casts happen generically in
`VD.update_offset`'s scalar case for *every* write, ordinary assignment
and call-return alike, dispatching to the int domain's own `cast_to`),
which is exactly B5/B6's `a_cast` and does not exist on any domain yet.
Rather than build that now or silently drop precision, every lemma on
this path (`combine_collect_sound` and its eight callers through
`DG_Base.thy`/`DG_Soundness.thy`) gained an explicit `ret_ok: "⋀x v.
ik_norm (Γ x) v = v"` premise -- an honest, unproven-here obligation
("`Γ`'s norm is a no-op on every value actually in play") that today's
all-`I32`-default corpus (D8) trivially satisfies, and that B5's `a_cast`
will eventually let a domain instance discharge precisely instead of
assuming away.

### B5 — Core interface reshape

The pivot, and the only remaining structural surgery -- narrowed by the
`Voblint_Core` Γ-threading above, which already did the *locale-signature*
half of this stage; what remains is the *numeric* half:

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
  `v : gamma a ==> norm ik' v : gamma (a_cast ik' a)`, discharging the
  `ret_ok` obligations `Voblint_Core`'s `combine_collect_sound` chain
  left open above -- the concrete site the migration doc already
  identified needing exactly this operation.
- `numeric_ops` / `special_ops` records and `domain_transfer` pick up
  the environment; `abstract_numeric_queries` and `Abstract_Checks` are
  restated (comparison queries are over already-normed values, so their
  statements barely move).

Gate: batch build of `Voblint_Core` with a single toy instance.

`Voblint_Analysis`/`Voblint_CLI`/`Voblint_Examples` are not yet
attempted: a batch build past `Voblint_Core` (`isabelle build ...
Voblint_Examples`) fails immediately in `Rel_Order_Domain.thy`,
`Analysis_GraphViz.thy`, and `Special_Ops.thy` with the identical
missing-`Γ`/`EA_Ret`-arity pattern `Voblint_Core` just closed, now
repeated once per concrete domain (Sign/Interval/Parity/Congruence) --
squarely B6/B7 work, not B5's numeric reshape.

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

**B6 cast pivot, landed this session (2026-08-25):** the originally
planned generic `a_cast_of` combinator was replaced by a Goblint-faithful
per-domain `cast` operator, added as an explicit parameter to
`expression_domain_sound` (`Abstract_Arithmetic.thy`) alongside `cast_sound`/
`cast_mono` assumptions. Per-domain designs, checked against
`goblint/analyzer` source (`IntDomain0.ml`'s `Interval.norm ~cast:true`,
`Congruence.cast_to`) 2026-08-25:

- **Interval** (`ivl_cast`, `Interval_Backward.thy`): unbounded side stays
  top; in-range unchanged; too-wide-to-wrap goes top; otherwise wraps both
  bounds via modular reduction, going top if the wrapped bounds end up
  disconnected. Matches Goblint's `norm ~cast:true` case-for-case.
- **Congruence** (`cong_cast`, `Congruence_Arithmetic.thy`): an exact-point
  class (`Some(c,0)`) always wraps via `ik_norm` (a single value can still
  overflow); a genuine class (`Some(c,m)`, `m<>0`) widens unconditionally to
  `top`. This is *not* what Goblint's own `cast_to` does at matching kind
  (it passes a genuine class through unchanged) — that behavior was checked
  and found not directly transferable to this formalization's `cast` locale
  obligation: `ik_norm` is not injective, so a fixed `v : gamma a` at the
  pre-cast kind does not determine `ik_norm ik v`'s residue class from `a`
  alone once `m` does not divide `ik_mod ik`. Verified unsound by explicit
  counterexample (`v=132`, `mk_congruence 0 3`, `I8`: `ik_norm(132) = -124`,
  `3` does not divide `(-124-0)`) before implementing the widen-to-top
  alternative, which is provably sound and monotonic.
- **Sign / Parity** (`sign_cast`, `parity_cast`): thin wrappers around the
  original `a_cast_of` combinator. Both domains are magnitude-free (no
  Goblint analog casts a bare sign or parity value), so the generic
  combinator's overflow-to-top behavior is already the right, and only
  sensible, design here — this is not a shortcut, it is the correct
  instance.
- **Int product domain** (`int_dom_cast`, `Int_Arithmetic.thy`):
  componentwise composition of the four casts above, sound and monotone by
  construction since `gamma_int_dom` is a plain intersection (no
  cross-component correlation needed). Reaching this required building a
  typed evaluator, `taval_int_dom :: tyenv => refine_mode => ikind => exp
  => (vname => int_dom) => int_dom`, from scratch — `Int_Arithmetic.thy`
  had no ikind-aware evaluator at all before this session (`aval_int_dom`
  was, and remains, untyped); `int_dom`'s composite `lt`/`eqb`/`tobool`
  queries do not fit `expression_domain_sound`'s single-operator-per-domain
  shape (documented in-file, pre-existing), so `taval_int_dom_sound`/
  `_mono` are proved by direct structural induction over `exp`, mirroring
  `aval_int_dom_sound`/`_mono`'s existing shape rather than a locale
  interpretation.

**Int_Backward.thy's inv_plus/inv_minus/inv_times, final design this
session:** `backward_domain`'s `inv_plus_sound` obligation is stated
against the *wrapped* result (`ik_norm ik (n1+n2) : gamma r`), and
`inv_plus` originally carried no `ik` parameter at all — it had to be
sound for every `ik` uniformly. `int_dom`'s composite backward narrowing
routed `Congruence_Backward.inv_plus_congruence`'s real inverse (`x =
(x+y) - y`) through this locale; that identity reasons from the
*unwrapped* sum and is not sound against the wrapped `r` as-is (same
counterexample shape as the cast case above). `Sign_Backward.thy`/
`Interval_Backward.thy` have no analogous real inverse to begin with and
stay on `inv_conservative` (the shared no-op, always-sound fallback)
unconditionally — that part is unaffected by anything below.

A first pass widened `backward_domain`/`backward_domain_refined`'s
`inv_plus`/`inv_minus`/`inv_times` fields to `ikind => 'a => 'a => 'a =>
'a * 'a` (threaded from the premise's own `ik`) but then routed *every*
component, including Congruence, through `inv_conservative` — a genuine
precision regression versus the pre-existing (never proved batch-clean)
design, since it discarded Congruence's real inverse entirely rather than
reconciling it with the wrap. That transitional design was rejected:
Congruence's own class-exactness fact makes the reconciliation possible
without discarding it. `cong_unwrap` (`Congruence_Arithmetic.thy`)
combines `ik_norm ik v : gamma r` with `ik_mod_dvd_ik_norm_diff` (`v` and
`ik_norm ik v` agree modulo any divisor of `ik_mod ik`) to derive `v :
gamma_congruence` at modulus `gcd m (ik_mod ik)` unconditionally — sound
and monotone in one formula, with no case split on whether `m` divides
`ik_mod ik`. `cong_cast` (the forward direction) got the same
`gcd`-based refinement for its genuine-class case, replacing the earlier,
strictly less precise "`m` divides `ik_mod ik` -> unchanged, else -> top"
design. `Congruence_Backward.thy`'s `inv_plus_congruence_ik`/
`inv_minus_congruence_ik`/`inv_times_congruence_ik` compose `cong_unwrap`
with the unchanged `inv_plus_congruence`/`inv_minus_congruence`/
`inv_times_congruence` family — the same composition works uniformly for
all three since each shares the "`r` is the exact operation result"
premise shape. `Int_Backward.thy`'s `inv_plus_int_dom_raw`/
`inv_minus_int_dom_raw`/`inv_times_int_dom_raw` route Sign/Interval/
Parity through `inv_conservative ik` (unchanged, still no-ops) and
Congruence through these `_ik` wrappers (real narrowing), restoring
genuine cross-component Congruence narrowing in all three
(`Refine_Never`/`Refine_Once`/`Refine_Fixpoint`) `backward_domain[_refined]`
interpretations.

`Example_Int_Backward.thy`'s `bfilter_int_dom_once_plus_eq_exact`,
`bfilter_int_dom_fixpoint_plus_eq_exact`, and
`bfilter_int_dom_never_plus_eq_congruence_only` are still **not yet
updated** — not because Congruence narrowing is unsound or missing any
more, but because every `bfilter_int_dom_*`/`afilter_ivl`/`bfilter_ivl`
example call site now also needs a leading `G :: tyenv` argument from the
`Voblint_Core` Γ-threading — see the B6/B7 gate note below — which this
file predates. Once that gate lands, these lemmas need re-deriving via
`by eval` against the restored narrowing, not merely re-stating with the
extra argument.

**B6/B7 gate status (2026-08-25): not yet met.** The per-domain
arithmetic/backward-filter layers above (`Sign_Arithmetic.thy`,
`Sign_Backward.thy`, `Interval_Backward.thy`, `Congruence_Arithmetic.thy`,
`Parity_Domain.thy`, `Int_Arithmetic.thy`, `Int_Backward.thy`) are each
individually I/Q-clean, but a full `Voblint_Analysis` batch build still
fails, in a *different, deeper* layer than the cast/backward work above:
`Sign_Transfer.thy`, `Interval_Transfer.thy`, `Parity_Transfer.thy`, and
`Int_Transfer.thy` — the `domain_transfer`-record-instantiating forward
transfer functions (`assign_X`, `special_X`/`branch_X`, `enter_X_for`,
`return_X`) actually dispatched by the analysis, not merely their
executable mirrors — still call the *old* untyped `aval_X`, which no
longer exists now that `aval_sign`/`aval_ivl`/`aval_parity`/
`taval_int_dom` are `tyenv => ikind => exp => ... => 'a`. `Sign_Exec.thy`,
`Ivl_Exec.thy`, `Parity_Exec.thy`, and `Int_Exec.thy` (the executable
mirrors layered on top, `Numeric_Ops.thy`'s `n_aval`/`n_bfilter` fields)
have the same untyped-call breakage independently. Congruence is
unaffected: its own arithmetic stayed deliberately untyped this session
(no Goblint cast analog needing it), so it never had a `Congruence_Transfer.thy`/
`Congruence_Exec.thy` pair to break.

The fix is understood precisely (checked against `CFG_Def.thy`'s
`edge_step`, which already threads `Γ :: tyenv` through the concrete
side): `EA_Assign x a` norms at the *target*'s declared kind
(`ik_norm (Γ x) (taval_syn Γ a s)`) after evaluating `a` at its own
synthesized kind (`taval_syn`, i.e. `taval Γ (opk (esyn Γ a)) a s`);
`EA_Assume`/`EA_AssumeNot` evaluate the condition at its own synthesized
kind with no further wrap; `EA_Ret`/call-argument binding norm at the
callee's/formal's declared kind after synthesized-kind evaluation. The
abstract-domain analogue is the same double-cast shape already used by
`int_dom_cast`/`taval_int_dom`: e.g. `assign_sign G x a sigma =
sigma(x := sign_cast (G x) (aval_sign G (opk (esyn G a)) a sigma))`.

What makes this a separate, larger stage rather than a same-session
follow-on fix: `sign_tf_for`/`ivl_tf_for`/`parity_tf_for`/`int_tf_for`
(the functions that construct a `domain_transfer` value, curried over
`gs :: vname => bool`) are called from 100+ sites across 20+ files —
`*/Ctx/*_Sound.thy` soundness developments and numerous
`Examples/*_Placement.thy`/`*_DG_Flagship.thy`/`*_DG_CallString*.thy`
regression files, several with `by eval`-checked concrete expected
abstract values that will shift once `ik_norm` wrapping is actually
threaded through. This is squarely B7 territory (the executable-mirror/
dispatch layer) plus a fresh pass over B6's own domain examples, not
attempted in this session: it needs its own gated pass — thread `G` through
`domain_transfer`'s `tf_assign`/`tf_special`/`tf_branch`/`tf_return`/
`tf_enter` fields and `apply_tf` (or, less invasively, curry `G` into each
`X_tf_for` constructor the way `gs` already is, keeping `domain_transfer`'s
field types and `apply_tf`'s signature untouched — the smaller-blast-radius
option, not yet chosen), fix `Sign_Transfer.thy`/`Interval_Transfer.thy`/
`Parity_Transfer.thy`/`Int_Transfer.thy` and their four `*_Exec.thy`
mirrors, then work through the Ctx/Sound/Examples call sites and their
regression values.

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
| Checker rejects programs Goblint would accept (mixed kinds) | Recorded as the D4 deviation: the model is the post-CIL program; revisit only if a promotion-bearing frontend is ever modelled -- **superseded 2026-08-25**, see the D4 revision above: promotion is now modeled, so this row is closed |
| Overflow-possible diagnostics ("warn" half of `sem.int.signed_overflow`'s default, D7 only covers the "go to top" half) | Tracked separately, issue #169 -- depends on B5/B6 landing (the flag is a byproduct of the case split those stages introduce); touches every domain's transfer signature plus a new report channel, so deliberately not folded into this migration's stages |

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
