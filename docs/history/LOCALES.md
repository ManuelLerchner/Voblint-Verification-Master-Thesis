# Locale reference

Every locale in the project, grouped by its extension hierarchy (a `└─` child
`extends` its parent — it inherits all the parent's `fixes`/`assumes`). For each:
what it abstracts, why it exists, and its parameters (`fixes`), hypotheses
(`assumes`), and in-locale `definition`s.

Locales sit on top of the domain **type classes** (not locales, listed once for
context): `sound_domain = bounded_semilattice_sup_bot + gamma + mono` (an abstract
domain with a concretisation `gamma`), `abstract_domain = sound_domain + widening`,
`show_val` (printable), and the `bounded_{widening,narrowing,warrowing}` executable
classes. These are `class`es because they are per-*type* structure; locales below
abstract over *values* (transfer functions, digests, generators).

---

## 1. Backward (guard) domain — `Generic/Domain/Abstract_Domain.thy`

**`backward_domain`** — abstracts a domain's *backward* operators (meet + inverse
arithmetic) so guard refinement (`afilter`/`bfilter`) is proved once, generically.
Why: every domain needs sound `assume`; without this locale each would re-prove the
same expression-tree recursion.

- `fixes` `meet`, `aval_abs` (abstract expression eval), `inv_less`, `inv_plus`,
  `inv_minus`, `inv_times` (each backward-propagates a result constraint to operands).
- `assumes` `meet_sound`, `aval_abs_sound`, `inv_{less,plus,minus,times}_sound` —
  each says the operator over-approximates its concrete counterpart (soundness w.r.t. `gamma`).
- `defines` `afilter` (refine an arith expr by a target abstract value),
  `bfilter` (refine a store by a boolean guard's truth value).

&nbsp;&nbsp;└─ **`backward_domain_mono`** — adds monotonicity of the six operators, and
derives `afilter_mono`/`bfilter_mono` generically. Why: the solver needs the transfer
function monotone; this hoists the shared induction out of every domain instance
(Sign, Interval interpret it).

- `assumes` `meet_mono`, `aval_abs_mono`, `inv_{less,plus,minus,times}_mono` — each
  operator is monotone in its arguments (in `fst`/`snd` conjunction form for the `inv_*`).

---

## 2. Transfer soundness — `Generic/Equations/Constraint_System.thy`

**`sound_transfer`** — a forward (intra-procedural) abstract transfer function that
soundly over-approximates the collecting semantics. Why: the entry point domains
interpret to get collecting soundness of the equation system.

- `fixes` `tf :: 'a domain_transfer` (record of `assign`/`assume`/`assume_not`/`enter`).
- `assumes` `tf_sound_assign`, `tf_sound_assume`, `tf_sound_assume_not`,
  `tf_sound_enter` — each concrete step stays inside `gamma` of the abstract result.

**`sound_effectful_transfer`** — the *interprocedural, side-effecting* transfer: each
edge is a strategy tree that may query/emit global contributions. Why: this is the
contract the TD-side solver bridge consumes; domains package their `etf` and discharge it.

- `fixes` `etf :: ('g::finite, 'a) effectful_domain_transfer`.
- `assumes` `etf_sound_{nop,assign,assume,assume_not,enter,combine}` — each edge/return
  tree, evaluated on a store in `gamma` of (local slot ⊔ global env), lands in `gamma` of
  its result; all under the `inr_slot_locals_bot` invariant (globals carry no locals).

&nbsp;&nbsp;└─ **`sound_effectful_transfer_framed`** — adds the enter upper bound: entering
a procedure resets locals to a fixed fresh frame (keeping only globals). Why: the keyed
generator seeds callee frames instead of folding enter edges, so it needs this bound.

- `fixes` `fresh_frame`. `assumes` `etf_enter_framed_le` (enter ≤ fresh_frame ⊔ globals,
  under both slot invariants).

&nbsp;&nbsp;└─ **`sound_effectful_transfer_framed_le`** — the *retain*-compatible variant:
the same bound under the weaker `inl_glob_le_glob_env` premise, so a spine whose local
slots carry globals can discharge it. Stronger contract; `framed_le_imp_framed` recovers
the publish version. Why: supports the retain analysis route.

- `fixes` `fresh_frame`. `assumes` `etf_enter_framed_glob_le`.

---

## 3. RHS generator hierarchy — `Generic/Solver/Core/TD_Side_RHS_Generator.thy`

Bundles the strategy-tree *shape* facts (dependency staticness, local-bot on globals,
solver-side monotonicity) so `unit`- and `mixed`-edge generators share them. The
`sound_<X>` names are interpretation-facing aliases of the corresponding `<X>` locale
(same parameters; they exist because interpretation targets use the `sound_` name).

**`sound_rhs_generator_base`** — the shared combine (procedure-return) tree shape.
Why: both edge shapes reuse the same combine tree; its facts are proved once here.

- `fixes` `etf`. `assumes` `comb` (`etf_combine` is the unit combine tree).

&nbsp;&nbsp;└─ **`sound_rhs_generator_static`** (= base) — adds `static_deps_comb` (the
combine's dependencies are static). No new parameters.

&nbsp;&nbsp;&nbsp;&nbsp;└─ **`sound_rhs_generator_mono`** — a *packaged* monotone equation
system. Why: feeds the solver interface's three mono obligations directly.

- `fixes` `T :: eqsT`. `assumes` `is_mono_eq`, `mono_sides`, `mono_deps`. Derives `threefold_mono`.

&nbsp;&nbsp;&nbsp;&nbsp;└─ **`unit_rhs_generator`** — per-edge trees are *unit*-global
edge trees (one anonymous global slot). Why: the standard non-relational edge shape.

- `fixes` `F` (per-action abstract state transformer). `assumes` `edge`
  (`apply_etf` is `unit_edge_tree (F a)`). Derives `cone_compatible`.
  - &nbsp;&nbsp;└─ **`sound_rhs_generator_unit`** (= `unit_rhs_generator`) — alias.
  - &nbsp;&nbsp;└─ **`unit_rhs_generator_mono`** — adds `F_mono` and discharges
    `is_mono_eq`/`mono_sides`/`mono_deps`/`threefold_mono` for `side_cfg_T_eff`. Why: turns
    a monotone `F` into the solver's monotonicity package with no per-domain proof.
    - &nbsp;&nbsp;&nbsp;&nbsp;└─ **`sound_rhs_generator_unit_mono`** (= `unit_rhs_generator_mono`) — alias.
    - &nbsp;&nbsp;&nbsp;&nbsp;└─ **`sound_rhs_generator_exec`** *(`Exec/Exec_Bridge.thy`)* —
      adds the executable `'a st` mirror and its `fun_of_st` commutation. Why: transports an
      executable post-solution to the abstract one for code generation.
      - `fixes` `etf_st`, `F_st`. `assumes` `edge_st`, `comb_st`, `commute`
        (`fun_of_st (F_st a s) = F a (fun_of_st s)`).

&nbsp;&nbsp;&nbsp;&nbsp;└─ **`mixed_rhs_generator`** — per-edge trees mix *local* and *unit*
edge trees depending on the action. Why: the relational/mixed-flow edge shape.

- `fixes` `F`. `assumes` `edge` (local vs unit tree by `local_edge_action a`).
  - &nbsp;&nbsp;└─ **`sound_rhs_generator_mixed`** (= `mixed_rhs_generator`) — alias.
  - &nbsp;&nbsp;└─ **`mixed_rhs_generator_mono`** — adds `F_mono`, discharges the mono package.
    - &nbsp;&nbsp;&nbsp;&nbsp;└─ **`sound_rhs_generator_mixed_mono`** (= `mixed_rhs_generator_mono`) — alias.

---

## 4. Solver interface — `Generic/Solver/Core/TD_Side_Eff_Interface.thy`

**`td_cfg_side_solver_eff`** — packages a concrete CFG + `etf` whose generated equation
system is monotone, and exposes the solved result (`solve`, `env_at`). Why: the boundary
where the vendored `TD.TD_side` solver is actually run; interprets `TD_side_mono` internally.

- `fixes` `g`, `etf`, `bot0`, `s0`, `gseed`. `assumes` `mono_eq`, `mono_sides`, `mono_deps`.
- `defines` `cfg_pkg_eff` (the packaged system), `stabl_at`, `nu_at`, `env_at` (projections
  of the solver's output).

---

## 5. Context and digest reads — `Generic/Solver/Context/`

**`context_domain`** *(`Context_Domain.thy`)* — the Goblint-style context interface:
how a context is prepared, selected at a call, and compared. Why: the abstract shape all
context-sensitivity routes share; `route` is the derived call-routing function.

- `fixes` `start_context`, `prep`, `ctx_sel`, `entdg`, `cmp`. No `assumes`.
- `defines` `route cc ctx a = ctx_sel cc ctx (prep cc a)`.

**`digest_global_read`** *(`Digest_Global_Read.thy`)* — the **generic digest kernel**:
a global read that joins the local slot with the `compatible`-filtered global partitions
selected by a point's digest. Why: the one abstraction over *how* globals are partitioned;
the mode family instantiates it. (After the RD removal, `mode` is its sole instance.)

- `fixes` `reader_digest :: pp ⇒ 'c ⇒ 'd`, `compatible :: 'd ⇒ 'g::finite ⇒ bool`. No `assumes`.
- `defines` `obs_digest` (local slot ⊔ `glob_env_cmp`-filtered globals).

**`value_digest_reader`** *(`Value_Digest_Reader.thy`)* — the **value-derived** digest
family: the digest is a decode of a ghost local, so it is a projection of the abstract
state (no second dataflow). Why: the generalized reader every value-projection domain
interprets (Sign's `mode` is the instance). Instantiates `digest_global_read` internally.

- `fixes` `decode :: 'd::sound_domain ⇒ 'm::finite`, `ghost :: vname`. No `assumes`.
- `defines` `vd_reader` (decode the ghost slot), `vd_obs` (`obs_digest` at this reader
  with equality compatibility); plus theorems `vd_obs_reduce`, `vd_collect_ctx_sound_bot`, …

---

## 6. Trace-level context transfer — `CFG/Collecting/CFG_Collect_Trace.thy`

**`context_transfer`** — abstracts a context assignment over *execution traces* (seed,
per-edge step, combine) with a compatibility invariant. Why: defines the context-annotated
collecting semantics (`trace_witness_ctx`) that the solver's context read is proved sound against.

- `fixes` `dg` (digest of a trace), `cmp`, `seed_ctx`, `step_ctx`, `comb_ctx`.
- `assumes` `seed_ok`, `step_ok`, `comb_ok` — the context stays `cmp`-compatible with the
  trace's digest across seeding, stepping an edge, and combining caller⌢callee traces.
- `defines` `trace_witness_ctx` (inductive: the context-indexed reachable-trace relation).
