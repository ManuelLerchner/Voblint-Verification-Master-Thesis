# Static variable identity migration

## Why

`tyenv = vname => ikind` (`src/VIMP/VIMP_Typing.thy:24`) is one flat, program-wide
map, built by `prog_tyenv p = tv_env (declared_kinds p)` over a single
`typed_var list` assembled in `cli/vimp_parser.mly:218-222` as global entries
followed by every procedure's formals. `tv_env` is `map_of`, which returns the
first match.

Two procedures with same-named formals of different kinds therefore resolve to
whichever declaration the parser emitted first:

```c
void f(uint8 n) { n := n + 200; return n }
void g(int64 n) { n := n + 200; return n }
void main() { a := f(100); b := g(100);
  __voblint_check(a == 44); __voblint_check(b == 300) }
```

```text
a==44    PROVED   a=[44,44]
b==300   REFUTED  b=[44,44]        <-- b is 300
```

Swapping the two procedure declarations swaps the verdicts. One of them is a
REFUTED on a true property.

No soundness theorem is violated: `declared_kinds` genuinely holds that
duplicate, so the analysis is correct for the `imp_prog` it was handed. The
defect is that the untrusted frontend silently builds an AST that does not mean
what the source says -- the failure mode the trust boundary leaves unprotected
by proof. The parser once rejected global/formal collisions; `grammar/vimp.yaml`
records that check being dropped and never replaced.

## Target

CIL gives every global, formal and local a `varinfo` with a unique `vid` and a
declared `vtype`, and Goblint's base analysis keys its state by `varinfo` rather
than by text. The same shape here:

```text
raw names
   -> verified name resolution
unique var_id + var_info
   -> typed elaboration with explicit conversions
typed CFG and state indexed by var_id
   -> kind-indexed concrete and abstract operations
```

No `vname => ikind` in the typed core, and no total fallback inside
`kind_of_var`.

## Open design question

Whether local and formal identities carry a positional index or the source name:

- `ScopedId pname nat` -- identity independent of the name, supports block
  shadowing when VIMP gains blocks.
- `ScopedId pname vname` -- fixes the defect equally (the `pname` disambiguates),
  makes display free at every report and GraphViz site, keeps ids stable when a
  procedure gains a variable, and reduces uniqueness-within-a-scope to
  uniqueness of the `vname` component.

VIMP's grammar has declaration forms for globals and formals only, and no
block-scope syntax to shadow in. The recommendation is `vname`-keyed now, with
positional ids arriving alongside whatever change introduces blocks. The
limitation to record either way: a source-name-keyed identity changes when a
variable is renamed, so it is not declaration-based the way CIL's `vid` is.

`pname` is a stable scope identity in the typed core already:
`proc_table = pname => proc_decl option` (`VIMP_Proc.thy:76`) makes procedure
names unique by construction. The gap is in the frontend, where the CLI parser
does not reject duplicate procedure definitions -- one more check for A5.

## Settled decisions

**Return slot is procedure-scoped.** `ReturnId pname`, not one nullary
constructor: procedures return different kinds, and recursive activations reuse
the same static id in separate frames. `reserved_ret_var` disappears because the
resolver never constructs `ReturnId` from user syntax.

**Resolution and elaboration are separate passes.** `raw_prog -> resolved_prog
-> tprog`, with `resolve p = Inr rp ==> wf_resolved_prog rp` and
`elaborate rp = Inr tp ==> wf_tprog tp`. Otherwise there is an intermediate
"typed" program whose conversion semantics are still incomplete.

**Implicit locals get synthetic declarations.** Every non-global, non-formal
name occurring in a procedure -- including read-only occurrences -- becomes a
synthetic `I32` local declaration. The corpus contains read-only implicit
locals, so a resolver that rejects every undeclared name would reject existing
fixtures. The `I32` default is applied while constructing the synthetic
declaration, never inside `kind_of_var`.

**Rejection rule is duplicate binding in one lexical scope**, whether or not the
kinds agree. The same parameter name in different procedures is valid C and
stays valid here.

**`TCast` carries only its destination kind.** The source kind is
`kind_of_texp` of the operand; duplicating it would create a well-formedness
obligation to keep the two in sync.

**Definite initialization is not typing.** "Assigned on every path before read"
is a dataflow property, not name resolution. Resolution fails on an
unresolvable name; initialization is a separate question. A read-only synthetic
local is therefore uninitialized, and its initial abstract value is the
declaration's kind range, never zero.

**Kind lookup is partial, and resolved once.** `decl_table = var_id => var_info
option`, so `kind_of_var :: decl_table => var_id => ikind option`. Nothing
downstream performs a fallible lookup: elaboration discharges the option and
writes the kind into the node, exactly as `TVar ik v` already carries it, so
transfer functions read the kind off the expression rather than off a table.
The state-seeding code is the one other consumer, and it is under an explicit
declaration-membership premise.

**Naming: `ScopedId`, not `LocalId`.** The constructor covers formals, explicit
locals and synthetic locals alike.

## Kind-aware domain operations

Goblint passes an `ikind` to `top_of`, arithmetic, joins, widening and
narrowing. Doing the same through an operations record would stop the state
domain being a `bounded_warrowing` instance, which is what the vendored solver
demands (`Solver_Side_RG` takes `'d::bounded_warrowing`; `Exec_St.thy:1127`
supplies it for `resolved_st_q`).

Kind-tagged cells give every operation its kind without touching the solver
interface. The tag must be a horizontal sum, because the class laws quantify
over all values including mismatched tags:

```isabelle
datatype 'a kd = KBot | KD ikind 'a | KTop
```

```text
KBot <= x                    x <= KTop
KD k a <= KD k b  iff  a <= b
KD k _ , KD l _   incomparable for k ~= l

sup KBot x               = x
sup KTop _               = KTop
sup (KD k a) (KD k b)    = KD k (sup a b)
sup (KD k _) (KD l _)    = KTop            for k ~= l

widen (KD k a) (KD k b)  = KD k (widen_k k a b)
widen mismatched         = KTop
```

`top_of k = KD k (domain_top_of k)`, not `KTop`. Mismatched tags stay
unreachable for well-formed states, but the instance must handle them lawfully.

Two obligations this creates in existing code:

- Two elements have empty concretization (`KBot` and `KD k bot`) and two have a
  maximal one (`KTop` with `gamma = UNIV`, `KD k top_k` with
  `gamma = ik_range k`). `Abstract_Domain`'s short-circuits test `is_bot`, which
  is already a predicate rather than equality with `bot`, so the shape survives
   -- but every `is_bot` instance must recognize both.
- `gamma_top`, an `expression_domain_sound` assumption, is about `KTop`, not
  about `KD k top_k`.

## Absent cells and the typed-state invariant

A total abstract state needs a reading for identifiers it does not explicitly
store, and `KTop` is the wrong one: its concretization is `UNIV`, not the
identifier's `ik_range`, so it violates the invariant A8 establishes on its
first lookup.

The plumbing to fix this already exists.
`fun_of_resolved_st_q_for :: (vname => bool) => 'a resolved_st_q => vname => 'a`
(`Exec_St.thy:1461`) already threads a program-derived classifier through every
state lookup. Replacing that `vname => bool` with the declaration table is a
like-for-like substitution at all 458 of its sites, and it makes the absent-cell
reading kind-aware for free:

```text
absent v  |->  KD k top      where  kind_of_var Delta v = Some k
```

No reachable cell is then `KTop` or an untagged `KBot`; `KTop` exists only so
the class laws hold on values the analysis never builds.

The obligations this leaves, and they are the highest proof risk in the whole
migration:

```isabelle
wf_abs_state Delta sigma  <-->
  (\<forall>v k. kind_of_var Delta v = Some k \<longrightarrow>
     (\<exists>a. sigma v = KD k a) \<or> is_bot (sigma v))
```

with preservation under `sup`, `widen`, `narrow` and every transfer.

`inf` is not among them. The backward filters take `intersect` as a locale
parameter (`Abstract_Domain.thy:961`) precisely because it is not the lattice
meet -- `meet_ivl_normalized_breaks_greatest` is the counterexample -- and
`bounded_warrowing = bounded_semilattice_sup_bot + warrowing` requires no meet.

## Frontend closure criterion

The defect is not closed by the CLI calling `resolve`. It is closed when every
production analysis entry point accepts only successfully resolved and
elaborated programs. Concretely: no export root accepts `declared_kinds` or the
old `tyenv`, no parser helper constructs a `tprog` directly, resolution errors
carry procedure, name and source location, and the ambiguous constructors are
confined to tests or deleted.

## Slices

Each slice ends on a green build. Anything called `tprog` has complete
executable conversion semantics -- A6 replaces the conversion policy atomically
rather than completing a half-elaborated program.

| # | Slice | Closes |
| --- | --- | --- |
| A1 | `var_id`, `var_info`, `decl_table`, partial `kind_of_var`, declaration well-formedness. Pure addition. | -- |
| A2 | `resolve :: raw_prog => error + resolved_prog`: lexical scope tables, deterministic synthetic-local collection, shadowing policy, soundness theorem. | -- |
| A3 | `elaborate :: resolved_prog => error + tprog`, complete under the current VIMP conversion policy, with `wf_tprog`. | -- |
| A4 | Re-index `store` and `abs_state` to `var_id`; classifier parameter becomes the declaration table. `gs`, `location_of`, `Global_Location` / `Local_Location`, `reserved_ret_var` all collapse. `lookup_var` confined to test and reporting boundaries. | -- |
| A5 | Switch and close every production frontend path; order-independence regressions. | order-dependence defect |
| A6 | Replace the conversion policy with the C-like fixed-width rules: operand promotions, argument binding, return, comparison operands. | C conformance |
| A7 | `kd` horizontal sum; order, bot, top, sup, widen, narrow, `is_bot`, concretization monotonicity. Transfers stay conservative. | -- |
| A8 | `wf_abs_state` preservation and kind-relative concretization. | Cause B premise |
| A9 | Precise kind-aware arithmetic, casts, widening and narrowing. Revert the kind-agnostic "recognize every machine-kind extreme" narrowing atomically here. | Cause B |

`gamma (KD k a) = gamma a Int ik_range k` makes kind-relative concretization
definitional, so A8 reduces to the concrete-side obligation: that `teval`,
assignment, argument binding and return preserve the typed-store invariant.

Resolver test matrix for A2 and A5: duplicate globals; duplicate formals; formal
colliding with an explicit or synthetic local; the same name in two procedures
(accepted, distinct kinds); a global shadowed by a formal (C permits it, the
formal wins -- the rule must be stated, not inherited); duplicate procedure
definitions.

`src/Examples` holds roughly 1400 `STR ''...''` variable literals. They keep
their textual source and gain one `resolve` call rather than being rewritten
against raw identities.
