# Machine integers

VIMP programs compute over mathematical integers unless they declare machine
kinds. A program that declares kinds is elaborated to a typed intermediate
representation and lowered back to VIMP with explicit conversions, and the
verified analyzer runs on the lowered program.

## Pipeline

```text
VIMP source with kind declarations
  | parse (cli/frontend, generated from manifests/vimp-grammar.yaml)
  v
imp_prog, kind_decls
  | typed_prog = per procedure: elab_com, then lower_com     (Voblint_Typed)
  |   elab_com : ('a, vname, exp) gcom -> ('a, var_id, texp) gcom
  |   lower_com: ('a, var_id, texp) gcom -> ('a, vname, exp) gcom
  v
imp_prog whose expressions carry Cast nodes
  | run_voblint (unchanged: compile, solve, report)
  v
report, with run_voblint_source_sound
```

A program that declares no kind skips `typed_prog` and keeps its
mathematical-integer meaning. The regression suite checks both
(`tests/regression/26-machine-kinds`).

## Source syntax

```c
global u8 g;
fun u16 f(u8 n) { u8 x; x = n + 1; return x; }
fun main() { i64 r; r = f(300); g = r; }
```

Kinds go on `global` lines, formals, return kinds (`fun u16 f`) and locals,
which are declared before a body's first statement, as CIL's `fundec.slocals`
lists them. A procedure without a return kind returns no value. A program that
writes any kind must write one on every global and formal and declare every
local; `cli/frontend/vimp_typing.ml` checks this and builds the `kind_decls`.
Globals start at zero, as C's static storage does. A declared local starts at an
arbitrary value of its kind: the parser begins the body with
`x = __voblint_nondet_int();` for each declared local, so the typed semantics
converts that value to the local's kind. `(k) e` converts explicitly in any
program. The Isabelle `program { ... }` notation reads untyped programs only; a
typed program in a theory is written `typed_prog p ds`.

## What is defined and proved

| Theory | Content | Main facts |
| --- | --- | --- |
| `Voblint_VIMP.Machine_Kind` | `ikind`, ranges, `ik_norm` (wraparound via `take_bit`/`signed_take_bit`), integer promotion, `usual_kind` | `ik_norm_in_range`, `ik_norm_id`, `even_ik_norm_iff`, `ik_norm_interval_shift` |
| `Voblint_VIMP.VIMP_Syntax`, `VIMP_Expr` | `Cast ikind exp` in `exp`; `aval (Cast ik e) s = ik_norm ik (aval e s)` | |
| `Voblint_Typed.Var_Id` | `var_id = GlobalId \| ScopedId \| ReturnId`, `resolve_var`, `kenv`, typed stores | `resolve_var_eq_iff` |
| `Voblint_Typed.Typed_Exp` | source typed semantics `taval`, typed expressions `texp`, `teval`, `wt_texp`, `elaborate`, `texp_erase` | `wt_texp_elaborate`, `teval_in_range`, `teval_elaborate`, `texp_erase_elaborate` |
| `Voblint_Typed.Typed_Com` | `'a tcom`, `elab_com`, `wt_tcom`, `tcom_erase` | `wt_tcom_elab_com`, `tcom_erase_elab_com`, `skeleton_elab_com` |
| `Voblint_Typed.Typed_Lower` | `lower`, `lower_com`, `kind_decls`, `typed_prog` | `lower_elaborate`, `lower_com_meaning`, `prog_table_typed_prog`, `skeleton_lower_com` |
| `Voblint_Typed.Typed_Semantics` | typed small-step semantics `tstep` on typed stores, `typed_table`, `typed_main`, store relation `srel` | `teval_lower`, `tstep_sim`, `tsteps_sim`, `tab_rel_typed_table`, `tinit_sim` |
| `Voblint_CLI.Typed_Certified` | | `run_voblint_typed_sound` |

`lower_elaborate`: `aval (lower (elaborate ρ κ ik e)) s = taval (κ ∘ ρ) ik e s`
for every store `s`. A lowered read is `Cast k (V x)`, so the lowered meaning
needs no typed-store premise. `teval_elaborate` relates the typed evaluator
`teval` to `taval` on typed stores.

`lower_com_meaning`: every expression of a lowered command evaluates, on every
store, to `taval` of a source expression of the original command at some kind.

`tstep` is the typed source semantics. It runs elaborated commands on typed
stores (`var_id => int`) with the frame discipline of `pstep`. Every write
stores a value of the target identity's kind: elaboration converts assigned
values, actual arguments and returned values, and the semantics converts call
and library results to the destination's kind. Each procedure has its own return
slot `ReturnId q`, so a typed frame records its callee.

`tstep_sim` proves that every typed step is matched by one `pstep` of the
lowered command. The invariant `sim` relates the configurations:

- the lowered command is `lower_com` of the typed one;
- `tok` records which activation each part of a running command belongs to;
- in the running activation of `q`, `srel` makes every identity that `q`
  resolves hold its lowered value converted to the identity's kind, and makes
  both return slots hold the same value;
- `frel` gives each saved frame the same relation for its caller.

`tsteps_sim` lifts this to runs. `tab_rel_typed_table` and `tinit_sim` discharge
the table and initial-store premises for `typed_table p ds`, whenever the
lowering is a well-formed source program.

`run_voblint_typed_sound` is the end-to-end theorem for typed programs. Let
`run_voblint config (typed_prog p ds)` return `Analysed res`, and let a typed run
reach `(c, t, tfs)` from `typed_main p ds` and a typed initial store. Then some
untyped run of the lowering reaches `(lower_com c, s, fs)`, with `s` related to
`t` by `srel`. The usual conclusion of `run_voblint_source_sound` then holds of
`s`: the configuration is observed at some node, and at every such node the
collecting semantics, the report and every definite verdict admit `s`. Through
`srel`, a well-typed expression of the running activation has the same value on
`t` and on `s` (`teval_lower_scoped`).

The theorem needs no CFG, trace semantics or analyzer for the typed language.
The simulation transfers typed runs to the lowered program, and the existing
chain covers that program.

## Analyses

Every non-relational domain implements a sound and monotone cast as part of
`sound_arith_ops` (`cst`, `cast_sound`, `cast_mono`):

| Domain | Cast |
| --- | --- |
| Interval | identity inside the kind's range; an interval narrower than the range whose wrapped bounds stay ordered is shifted exactly; otherwise the whole range |
| Parity | identity (wraparound subtracts an even multiple) |
| Sign | keeps `SBot` and `SZero`; `SNonNeg` at an unsigned kind; otherwise top |
| Congruence | a singleton maps to the converted constant; any other class becomes top |
| Int | componentwise, then refined |

Because a lowered read converts to the variable's kind, an unconstrained
variable is read inside its kind's range: kind-aware initial values come from
the reads, without changing the initial abstract state. Backward refinement
does not narrow through a cast, which is sound. The relational Order analysis
matches only plain variables, so it treats a cast as an expression it does not
interpret; since every read of a typed program is a cast, it learns no
relations in typed programs.

## Semantic choices

- **Signed overflow wraps.** C leaves it undefined. The typed semantics gives
  it the `-fwrapv` meaning, so a verdict on a typed program is about wrapping
  arithmetic, not about a C program whose signed arithmetic overflows.
- **Division and remainder** use VIMP's total `c_div`/`c_mod`: truncation
  toward zero for a nonzero divisor, the VIMP conventions for a zero divisor;
  `INT_MIN / -1` wraps.
- **Literals** take `i32` or `i64` from their magnitude, as C types the
  unsigned token.
- **Resolution follows current VIMP.** A declared global is one identity in
  every procedure; any other name is local to its procedure. Lowering names an
  identity by its source name, which identifies it within one activation
  because VIMP has no shadowing and locals live per activation.
- **A call destination is converted when it is read.** The returned value is
  stored as it is, and every later read converts it to the destination's kind.

## Differences from PR #172

- Identities are `var_id` in the typed IR and lower to their source names; no
  `#`-encoded strings.
- Operators are factored into `TArith ik aop` and `TCmp cop`.
- Typed programs have their own small-step semantics `tstep`. They reach the
  analyzer by lowering, and `tstep_sim` connects the two. There is no second CFG,
  trace semantics or analyzer: `pstep`, the CFG, traces, the solver and the
  headline theorem are unchanged and reused.
- Kind-aware initial values come from reads at the variable's kind instead of
  kind-dependent seeds.
