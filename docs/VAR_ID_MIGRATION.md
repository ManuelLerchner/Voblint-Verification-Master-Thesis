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

`resolved_st_q` cannot express this by adjusting a default. It compresses a
state into one default for locals, one for globals, and sparse overrides, and
locals do not share a kind: no single interval is both `top_of U8 = [0,255]`
and `top_of I64`. Two ways out, and only one of them is a slice rather than a
redesign:

- **Explicit entry per resolved declaration.** Build the seed after resolution
  from `resolved_kinds`, one override per encoded identity. The compression
  stays, the defaults stop carrying meaning for anything declared, and
  `fun_of_resolved_st_q_for`'s signature is untouched. Recommended.
- **Kind-dependent default in the lookup.** Replace the
  `vname => bool` classifier at all 458 sites of
  `fun_of_resolved_st_q_for :: (vname => bool) => 'a resolved_st_q => vname => 'a`
  (`Exec_St.thy:1461`) with the declaration table, so an absent cell reads
  `KD k top` where `kind_of_var Delta v = Some k`. Much larger, and it buys
  nothing the first option does not once every declaration has an entry.

Either way no reachable cell is `KTop` or an untagged `KBot`; `KTop` exists
only so the class laws hold on values the analysis never builds.

Tagging the seed is not the whole invariant. Goblint establishes a cell's kind
at *every* construction site, not only at `init_value`: an expression result
takes the CIL result type, an assignment the destination type, a formal
binding the formal's kind, a return the procedure's return kind, a special
call its declared result kind. Seed-first is a workable incremental order, but
the invariant only closes once every write preserves the tag.

`ret_var` is the exception that has to be designed for rather than discovered.
Its kind is dynamic: during an unwind it holds a value at the *callee's*
declared return kind, which is exactly why concrete preservation already
weakens from `styped` to `rstyped` there (`pstep_preserves_sstyped`). The
tagged invariant must permit the same --

```text
ordinary identity  |->  its declaration's kind
ret_var mid-unwind |->  the current callee's return kind
```

-- and must show that return slots tagged at two different callee kinds never
meet at a solver join. Without that, `KTop` becomes reachable for a valid
program and the whole carrier stops paying for itself.

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

## Status

Landed and green under `isabelle build Voblint_VIMP`:

- `VIMP_Var_Id.thy` -- `var_id` (`GlobalId` / `ScopedId` / `ReturnId`), `var_info`,
  `decl_table`, partial `kind_of_var`, `origin_fits`, `wf_decls`, `ret_kind_of`.
- `imp_prog` carries `declared_scoped :: (pname * typed_var) list`;
  `mk_program_typed` takes it as a fifth argument.
- Procedure-local declarations parse on both frontends. `grammar/vimp.yaml`
  gained `local_decl` and a `locals_star` slot in `function_decl`; the Menhir
  generator realizes them with zero grammar conflicts, and the hand-written
  `program { ... }` notation realizes them as eight keyword-initial productions
  (see below). The CLI parses and analyses a declaration-carrying program end
  to end.
- `VIMP_Decls.thy` -- `prog_decls :: imp_prog => decl_table` over globals,
  formals and locals, with `wf_decls (prog_decls p)` proved.

The payoff is witnessed, not asserted:

```isabelle
kind_of_var (prog_decls two_kinds_prog) (ScopedId (STR ''f'') (STR ''acc'')) = Some U8
kind_of_var (prog_decls two_kinds_prog) (ScopedId (STR ''g'') (STR ''acc'')) = Some I64
prog_tyenv two_kinds_prog (STR ''acc'') = I32
```

Two procedures bind `acc` at different kinds and each identity answers with its
own declaration, while the flat name-keyed environment cannot tell them apart.

Declarations are recorded but not yet consumed: the analysis still reads kinds
out of `prog_tyenv`, so adding a declaration changes no verdict. That is what
makes the corpus migration safe to land before enforcement.

### A2 landed: `VIMP_Resolve.thy`

`resolve :: imp_prog => resolve_error list + imp_prog` is the renaming pass.
It resolves each occurrence to a `var_id` -- formal or local of the enclosing
procedure, else a declared global, else a synthetic local of that
procedure -- and rewrites the program to use `var_id_name` of that identity.
`declared_scoped` now carries annotated formals alongside locals, so a
formal's kind is decided by its own declaration rather than by the position
its name took in the flat list.

`resolve_errors` decides exactly what the correctness theorem needs:
distinct procedures, distinct globals, distinct formals and scoped
declarations per procedure, no procedure-bound name shadowing a global,
separator-free names, pairwise distinct identities, and a declared entry
procedure. On success:

```isabelle
prog_tyenv (resolve_prog p) (var_id_name (ScopedId q x)) = scoped_kind p q x
prog_tyenv (resolve_prog p) x                            = prog_tyenv p x     -- x global
```

so the resolved program's flat environment answers each identity with its own
declaration. The witness is the reviewer's own example: `uint8 f(uint8 n)` and
`int64 g(int64 n)` resolve to `U8` and `I64`, where `prog_tyenv` of the source
answers `U8` for both.

`display_vname_in` (`VIMP_Var_Id.thy`) is the inverse at the reporting
boundary: it shows a global unchanged, shows a scoped identity as the name the
source wrote, and qualifies it `proc::name` only where the rendered list holds
that name for two scopes at once. On a name no resolver produced -- every name
in an unresolved program -- it is proved to be the identity, so reports over
unresolved programs read exactly as before.

### A5 landed: every analysis entry point resolves

`analyse_config`, `analyse_config_ctx`, `analyse_config_with_state` and all
fifteen `*_auto` renderers bind `p = resolve_prog p0` before anything else, so
no export root compiles an unresolved program. The frontend's
`check_kinds_agree` -- which rejected two procedures binding one name at two
kinds, because the flat environment had no representation for it -- is gone:
`tests/regression/24-scoped-names/` is the same programs, now analysed.

```text
uint8 f(uint8 n) { return n + 200 }
int64 g(int64 n) { return n + 200 }
void main() { int32 a, b; a := f(100); b := g(100);
  __voblint_check(a == 44); __voblint_check(b == 300) }
```

```text
a==44    PROVED   a=[44,44]
b==300   PROVED   b=[300,300]
```

Swapping the two definitions changes neither verdict, which
`02-declaration_order_does_not_matter.vimp` pins.

Reporting shows the source name, not the identity. `display_scoped` drops the
scope at every leaf a printer renders -- expressions, commands, CFG edge
labels, per-procedure state lines -- since a printed expression belongs to one
procedure and cannot collide with itself. `display_vname_in` handles the one
listing that spans the whole program, a full-state node label, by qualifying
`proc::name` only where two scopes bind the same name. Both are proved to be
the identity on a name no resolver produced. The corpus is byte-identical:
same 15 failures as before, plus one snapshot whose variable lines reordered
because `main#a` sorts after a global `g` where `a` sorted before it.

### Isabelle needs one production per kind keyword

The canonical grammar has a single `local_decl: ty ids SEMI`. Menhir realizes
it directly -- one token of lookahead on the kind keyword settles where a
declaration sequence ends. Isabelle's parser does not: a production whose
template begins with a nonterminal leaves it unable to separate the declaration
prologue from the statement list, and every such program failed to parse.
`_gdecl` escapes this only because `global` marks each of its lines. The
notation therefore declares `_ldecl_int8` ... `_ldecl_uint64`, eight
keyword-initial productions with identical surface syntax, each mapping back
onto the generated `_ty_<k>` so the kind names stay listed once. This is a
target-specific realization of one canonical production, not a second grammar.

### Known gap: the source printer drops kind annotations

`pretty_string_of_program` emits `global g1, g2;` from its globals argument, so
globals do survive a round trip -- but it prints them untyped, and the parser
maps an untyped global to no kind at all, so nothing reaches `declared_kinds`.
Locals are not printed either. The printed form is therefore kind-erased: it
re-parses into a program whose every variable has the default kind.

The property suite covers declaration-carrying programs for parse acceptance
only, not for print round-trip, for exactly this reason.

### Representing an identity as a name

Parameterizing the AST over its variable type -- `'v exp`, `'v com`, `'v texp`
-- would touch roughly 676 type positions and every store, abstract state and
solver unknown. It is not necessary. A `var_id` carries exactly a scope and a
name, so it injects into the existing `vname` key space:

```text
GlobalId x    ->  x
ScopedId p x  ->  p # x
ReturnId p    ->  p # # ret
```

`#` is what makes this safe: the lexer's identifier class is
`[a-zA-Z_][a-zA-Z_0-9]*`, so no source program can write a name containing one.
`ret_var = STR ''#ret''` already relies on that, so this is the codebase's own
idiom rather than a new convention.

The injection is proved invertible -- `name_var_id (var_id_name v) = v` for
separator-free identities, hence `var_id_name_inj`. Identity remains the
specification; `vname` remains the representation. Stores, abstract states,
`pstep` and every existing signature are untouched.

This matters because the cheaper alternative does not work. Compilation is
per-procedure (`compile_proc Gamma Pi p decl n`), so a per-procedure `tyenv`
would scope the compiled side correctly -- but `pstep Gamma gs Pi` fixes one
environment for the whole relation and its configuration carries no procedure
identity, so the source semantics cannot resolve a name per procedure. `csim`
would then relate two semantics that disagree. Resolution has to reach the
commands themselves, which the name injection achieves without changing their
type.

## Declarations are now explicit corpus-wide

Every declaration in `tests/regression/` carries a kind:

| Class | Added | Was |
| --- | --- | --- |
| Locals | 404 | implicit, `I32` by default |
| Formals | 131 | 131 bare, 1 annotated |
| Globals | 30 | 30 bare, 36 annotated |
| Return types | 113 | every procedure spelled `void` |

Each annotation names the kind the declaration already resolved to, so the
migration is semantically inert: the corpus stayed at 167 passed / 18 failed
with a byte-identical failing set, lint clean over 185 fixtures, property
suite green. The transform is idempotent -- running it twice changes nothing,
which is the check the first locals pass failed, leaving five fixtures with
doubled prologues that a later parser check caught.

Ordering matters here and is worth stating: annotate first, enforce second.
Enforcing first rejects 146 fixtures at once with nothing to bisect against.

### Frontend asymmetry, and what closes it

Enforcement lands on the Menhir frontend first, because that is where the
migrated corpus lives. The Isabelle `program { ... }` notation keeps accepting
the untyped forms for now: `prog_tr` rejecting them would break every
`void f(n)` in `src/Examples`, and those 34 program-constructing theories are
migrated separately.

This is a deliberate, temporary divergence between the two frontends. It closes
when the Example theories are annotated, at which point the same checks move
into `prog_tr` and the untyped `formal_untyped` and `globals_decl` productions
can leave `grammar/vimp.yaml` entirely -- at which point the grammar, rather
than a check, is the contract.

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
| A6b | Typed concrete initialization and a declaration-derived abstract seed, cell type still plain `ivl`. See below. | initialization half of the `styped` gap |
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

### A6b in detail: the seed slice

Changing the abstract seed alone does not close the initialization gap. The
concrete collecting semantics still starts from out-of-range stores, because
`cinit_stores gs = {s. ALL x. gs x --> s x = 0}` constrains globals only. Both
halves move together:

```isabelle
typed_cinit_stores Gamma gs = {s. styped Gamma s AND (ALL x. gs x --> s x = 0)}

typed_cinit_stores Gamma gs SUBSETEQ gamma_state (cinit_ivl_st_for Gamma gs p)
```

and then `ltr_collect` and the source-facing soundness chain migrate to the
typed initial set, at which point `styped Gamma s0` stops being a hypothesis
the caller discharges.

Order:

1. Define the typed concrete initial-store set.
2. Make the Interval seed depend on the resolved program and `prog_tyenv`.
3. Populate every declared identity explicitly, per the first option above.
4. Prove the exact lookup equations for the new seed.
5. Prove typed-initial-store coverage.
6. Migrate every Interval entry point and collecting-soundness theorem.
7. Add mixed-kind local and global regressions.
8. Keep the cell type plain `ivl`. The carrier is A7.

The choice this bakes in, and it is VIMP's rather than C's: an uninitialized
local holds an arbitrary representable value of its declared kind. C leaves it
indeterminate and reading it may be undefined. Goblint's `init_value` makes the
same abstraction; recording it as a VIMP semantics decision keeps the
`Wrap`-policy framing honest.
