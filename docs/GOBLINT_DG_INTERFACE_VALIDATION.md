# DG interface validation against Goblint's intended abstraction

> **Status:** DELIVERED. Grounded in Goblint master source (`analyses.ml`,
> `base.ml`, `constraints.ml`). **Recommendation: leave the DG interface
> unchanged.** The local-only context routing in `sound_dg_spec_core` faithfully models
> Goblint; no minimal interface change is required.

## Primary-source evidence

### E1 — the `Spec` interface separates D, G, C (analyses.ml)

```ocaml
module D : Lattice.S      (* local, context-sensitive domain *)
module G : Lattice.S      (* global, flow-insensitive domain *)
module C : Printable.S    (* context domain *)
module V : SpecSysVar     (* global constraint-variable keys *)

val context: (D.t, G.t, C.t, V.t) man -> fundec -> D.t -> C.t
```

### E2 — the manager record: the only global channel (analyses.ml)

```ocaml
type ('d,'g,'c,'v) man =
  { ask      : 'a. 'a Queries.t -> 'a Queries.result
  ; ...
  ; context  : unit -> 'c
  ; local    : 'd
  ; global   : 'v -> 'g          (* read a published global *)
  ; sideg    : 'v -> 'g -> unit   (* side-effect a global *)
  ; spawn    : ... }
```

`global`/`sideg` are the sole global read/write channel, and `sideg` is a field of
the *universal* `man` passed to every transfer function.

### E3 — the base analysis computes context from local state, dropping globals (base.ml)

```ocaml
let context man (fd: fundec) (st: store): store =
    let f keep drop_fn (st: store) = if keep then st else { st with cpa = drop_fn st.cpa} in
    st |>
    f (not !earlyglobs) (CPA.filter (fun k v -> (not k.vglob) || is_excluded_from_earlyglobs k))
    %> f (... "ana.base.context.non-ptr" ...) drop_non_ptrs
    %> f (... "ana.base.context.int" ...) drop_ints
    %> f (... "ana.base.context.interval" ...) drop_interval
    ...
```

The body threads only the local `st`. It reads **no** `man.global` and issues **no**
`man.ask`. Its first filter *drops syntactic globals from the context*.

### E4 — context is invoked with the entering/caller local state (constraints.ml)

```ocaml
let paths = S.enter man lv f args in
let paths = List.map (fun (c,v) -> (c, S.context man f v, v)) paths in
```

and at spawn:

```ocaml
let c = S.context man fd d in
sidel (FunctionEntry fd, c) d;
```

The `D.t` argument to `context` is the entering local state `v` (from `enter`) or the
caller local state `d` (at spawn) — never a global read.

## Answers

**1. What may the context function inspect?** Syntactically, the full `man` (so
`man.global`, `man.ask`) plus the local `D.t` (E1). *Intended* input: the local
state — the base analysis inspects only its local `st` argument and reads no globals
(E3). The `man` handle exists for uniformity (queries/emit), not to fold globals into
the context.

**2. Local only, or local + published globals?** **Local only, by intent.** Context
is invoked on the entering/caller local state (E4) and the reference implementation
projects that local state and *excludes* globals (E3). Globals live in a separate
flow-insensitive channel read on demand (E2), not in the context.

**3. Is the local/global split interface or implementation detail?** **Interface.**
`D` and `G` are distinct `Spec` components with distinct lattices; `man.global`/
`man.sideg` are the only crossing (E1, E2). The split is definitional, not incidental.

**4. Effectful analyses — ordinary instances or a separate class?** **Ordinary.**
`sideg` is a field of the universal `man` (E2); any transfer function of any analysis
may side-effect globals. There is no separate effectful-analysis type. This is the
thesis of Goblint's side-effecting constraint systems.

**5. Does `sound_dg_spec_core` faithfully model this?** **Yes.**

- D/G separation with a joint `gammaDG d g` matches E1/E2.
- Side-effects are built into the interface, not bolted on: `dg_edge_tree` emits
  `Side () (DG bot (fst (step l g)))` (a global contribution) alongside
  `Answer (DG (snd (step l g)) bot)` (the local update). Every DG edge is
  side-effecting by construction — the E4/E2 `sideg` discipline. Effectful analyses
  are therefore ordinary DG instances, matching answer 4.
- Context routing `rt cl ctx (dg_D_c sigma ctx cl)` reads `dg_D_c = locals (sigma (Inl …))`
  — the **local slot only**, with the global slot `dg_G_c` excluded. This matches E3
  exactly: context from local state, globals dropped.

**6. Minimal interface change if not faithful?** **None required.** The interface is
faithful for the intended (base) model. Extending `rt` to `pp -> 'c -> 'D -> 'G -> 'c`
(context reading globals) would model a capability the reference analysis deliberately
avoids (E3), enlarging surface for no faithfulness gain.

## Reconciliation with the current architecture

| Component | Goblint counterpart | Verdict |
| --- | --- | --- |
| `Ctx_Collect_Backbone` (generic `rd`, `rt`) | the context-sliced collecting semantics | Faithful, agnostic; accommodates local-only *and* wider readings. Unchanged. |
| `sound_dg_spec_core` (D, G, `gammaDG`, `dgs_combine`, `rt` over `dg_D_c`) | `Spec` (D, G, C, `context man f v`, `sideg`) | **Faithful.** Local-only routing = E3; built-in `Side ()` = E2/E4. Unchanged. |
| `Local_DG` (G = unit, `gammaDG d () = [[d]]`) | a globals-free `Spec` instance | Faithful specialization. Unchanged. |

### Correction to the prior `side_env_ctx` determination

`SIDE_ENV_CTX_DG_DETERMINATION.md` framed DG's local-only routing (`rt` over
`dg_D_c`) as an *obstruction* to expressing the effectful `side_env_ctx` spine as a
DG corollary. The Goblint evidence now settles the point the other way: **local-only
routing is the faithful model** (E3/E4), and the effectful `side_env_ctx` path has
been deleted. The shared helpers that used to sit under that path now live in
`TD_Side_Eff_Ctx_Shared`; the current architecture is DG / keyed / digest / clean
over that shared context-collection backbone.

## Recommendation

**Leave the DG interface unchanged.** `sound_dg_spec_core` faithfully models Goblint's
`Spec`: separate D/G lattices, context computed from local state with globals
excluded, and side-effects as an ordinary (built-in) capability. No minimal interface
change is warranted by the evidence.

## Sources

- [`analyses.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/analyses.ml) — `Spec` module type, `man` record.
- [`base.ml`](https://github.com/goblint/analyzer/blob/master/src/analyses/base.ml) — `context` implementation.
- [`constraints.ml`](https://github.com/goblint/analyzer/blob/master/src/framework/constraints.ml) — `context`/`enter` call sites.
- [Side-Effecting Constraint Systems (Apinis, Seidl, Vojdani)](https://goblint.in.tum.de/assets/papers/side.pdf) — side-effecting as the unifying mechanism.
