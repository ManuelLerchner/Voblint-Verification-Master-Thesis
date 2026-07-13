# Compiler correctness: source-level soundness of `compile_prog`

> **Status (2026-07-13): complete for the headline finite-prefix theorem.**
> `Compiler_Correctness_Prototype.thy` proves the located weak simulation from
> IMP2 `psteps` through `compile_prog`, connects located CFG execution to
> `cfg_collect`, and instantiates the result with the verified side solver. The
> concrete theorem `concrete_source_reaches_side_analyse_eff` covers every finite
> source prefix, including prefixes of nonterminating executions. The optional
> `pbig` development and a standalone terminating-exit projection were not needed
> to close the source-to-analysis gap.

The implementation took the direct Phase-2 route after the located simulation
made Phase 1 redundant. This document retains the Phase-1 design as a possible
terminating-semantics corollary, but it is not part of the soundness dependency
chain.

## Problem statement

Before this migration, end-to-end soundness stopped at the compiled CFG's
collecting semantics:

```
analysis  >=  cfg_collect (compile_prog Pi ps main)
```

It did **not** relate the analysis to the source-language semantics. The missing
link was compiler correctness. There are two distinct strengths of it, and they
are not the same theorem:

- **Terminating exit correctness** (Phase 1): a complete source run that ends in
  store `t` has `t` collected at the CFG exit.
  `pbig Pi c s t ==> cfg_runs_to Pi ps c s t`.
- **Per-point reachability correctness** (Phase 2, the real target): *every* store
  reachable at *any* point of a source execution — including finite prefixes of a
  **nonterminating** run — is collected at the matching CFG point.
  `psteps Pi (c,s,[]) cfg' ==> store cfg' : cfg_collect g {s} (point-of cfg')`.

Phase 1 is **not sufficient** for the analysis thesis. The downstream soundness is
stated at every program point (`cfg_collect g S v` for all `v`), and it must hold
for programs that loop forever — where the big-step relation is empty and Phase 1
is vacuous. Phase 1 is the cheap, high-confidence first slice (it validates the
call/restore/combine correspondence on terminating runs and reuses the existing
`pcompletes_*` lemmas); Phase 2 is what actually discharges "analysis >= source
semantics."

Everything downstream of `cfg_collect` is already proved and CFG-parametric, so a
wrong `compile_prog` silently yields a vacuously-sound analysis. This work removes
`compile_prog` from the TCB.

## Decision (2026-07-10)

**Staged: Phase 1 (big-step, terminating) first, then Phase 2 (small-step,
per-point).**

- Phase 1 gives a fast, standard, HOL-IMP `ccomp_bigstep`-grade result and de-risks
  the algebra of enter/combine/restore before the harder relation work.
- Phase 2 is the target that matches the collecting-semantics thesis. It uses a
  **located concrete CFG semantics with an explicit call stack** and a source<->CFG
  **simulation relation**. We prove **finite-prefix (weak) simulation** — enough to
  connect source reachability to `cfg_collect`. A coinductive divergence-preservation
  theorem is **optional** and not on the critical path.

**Rejected framings.**

- *`pp_of` as a function of the residual source command.* Not well-defined: two
  identical `Assign x a` subterms compile to different nodes, and residual commands
  (`Seq c'' Restore`, unfolded `While`) carry no offset. The current point must come
  from the CFG configuration, not be reconstructed from the residual command. This is
  the concrete reason Phase 2 needs a located CFG semantics.
- *Big-step as the primary/only target.* Vacuous on nonterminating input; blind to
  internal points. Kept only as Phase 1.

## What already exists

**Source operational semantics** — `src/IMP2/IMP2_Proc.thy`:

- `pstep` : small-step over `(com * store * frame list)` with an **explicit call
  stack** (`frame list`). `Scope`/`Call` push `enter_state s` and save the caller
  frame; `Restore` pops via `<fr|s>`.
- `pcompletes Pi c s t == psteps Pi (c,s,[]) (SKIP,t,[])` — terminating run,
  empty stack to empty stack.
- Already proved: every big-step-shaped composition lemma —
  `pcompletes_{Seq,IfTrue,IfFalse,WhileFalse,WhileTrue,Scope,Call,Scope_Call}`,
  plus frame-extension lemmas (`psteps_frame_extend`, `psteps_frame_mono`). **These
  are the big-step introduction rules already discharged** — Phase 1's `pbig ==>
  pcompletes` is one existing lemma per case.

**Source-language top** — `src/IMP2/IMP2_Bridge.thy`:

- `backward_sim` : AFP IMP2 `big_step` ==> `pcompletes` (**done**). The forward
  direction (`pcompletes ==> big_step`) is explicitly open ("Track A");
  `docs/AFP_IMP2_FORWARD_SIM_MIGRATION.md`.

**CFG collecting** — `src/CFG/Collecting/CFG_Collect.thy`:

- `cfg_collect g S = lfp (cfg_collect_F g S)`, with `cfg_collect_eq_paths`:
  `cfg_collect = cfg_collect_paths`, defined by the inductive `cfg_witness`:
  - `entry`: `s : S` at `cfg_entry`;
  - `edge`: apply `edge_collect a` over `(u,a,v) : edges g`;
  - `combine`: `(c,ex,v) : combines g`, witness `s` at `c`, witness `t` at `ex`
    ==> witness `<s|t>` at `v`.
- `EA_Enter` transfer = `enter_state`; combine builds `<s|t>`. **These are the
  exact operators the source `Scope`/`Call`/`Restore` use** (`IMP2_Globals.thy`:
  `enter_state` keeps globals + zeroes locals; `<s|t>` = locals from `s`, globals
  from `t`; source `Restore` produces `<fr|s>` = combine of caller frame and
  current store — identical to the CFG `combine` of call-site and callee-exit).

**Exit projection** — `cfg_runs_to` in `CFG_Collect_Runs.thy`.

**Located CFG execution is implemented.** `Compiler_Correctness_Prototype.thy`
defines `cstep` with an explicit stack and proves that its reflexive-transitive
closure preserves `located_sound`. `control_at`, `frames_match`, and
`concrete_program_match` provide the source-to-CFG matching relation.

## Compiler pipeline (`src/CFG/IMP2_Proc_to_CFG.thy`)

- `compile Pi lay c n -> (n', en, ex, E, C)`: fresh-counter structural compiler.
  `Scope`/`Call` emit an enter edge `(n, EA_Enter, en_p)` and a combine triple
  `(n, ex_p, n+1)`.
- Two-pass whole-program build: `compile_procs_layout` (pass 1: assigns each proc
  `(en_p, ex_p, node-range)`, resolving calls through `known_proc_layout` stubs)
  -> `compile_procs_bodies` (pass 2: re-compiles each body against the finished
  layout, emitting the real `E, C`) -> `compile` on `main` -> `mk_cfg`.

**Invariants proved:** only `compile_counter_mono` (`n <= n'`) and finiteness
(`compile_finite`, `compile_procs_*_finite`, `compile_prog_finite`).

**Invariants assumed / never stated:** endpoint correctness, fragment embedding
(`E <= edges (compile_prog ...)`, `C <= combines ...`), layout-vs-body agreement
(pass-1 `(en_p, ex_p)` = pass-2 endpoints), node freshness/disjointness. None
exist yet. Phases 1 and 2 both need the embedding + endpoint-agreement lemmas
(they are compiler facts, independent of which semantics you simulate against).

---

# Phase 1 — terminating exit correctness (big-step)

```
AFP IMP2 big_step ──backward_sim (DONE)──▶ pcompletes ──(M1)──▶ pbig
pbig ──(compile_correct, terminating)──▶ cfg_runs_to = cfg_collect at exit
cfg_collect ──(DONE downstream)──▶ analysis
```

## (1) The minimal big-step theorem we can prove now

Introduce the inductive big-step whose constructors are exactly the proved
`pcompletes_*` lemmas (no `Restore` constructor — it is runtime-only; `Scope`/`Call`
bake the restore into their conclusion `<s|t'>`):

```isabelle
inductive pbig :: "proc_table => com => store => store => bool" for Pi where
  Skip:    "pbig Pi SKIP s s"
| Assign:  "pbig Pi (Assign x a) s (s(x := aval a s))"
| Seq:     "pbig Pi c1 s s2 ==> pbig Pi c2 s2 t ==> pbig Pi (Seq c1 c2) s t"
| IfTrue:  "bval b s  ==> pbig Pi c1 s t ==> pbig Pi (If b c1 c2) s t"
| IfFalse: "~bval b s ==> pbig Pi c2 s t ==> pbig Pi (If b c1 c2) s t"
| WhileF:  "~bval b s ==> pbig Pi (While b c) s s"
| WhileT:  "bval b s ==> pbig Pi c s s2 ==> pbig Pi (While b c) s2 t
              ==> pbig Pi (While b c) s t"
| Scope:   "pbig Pi c (enter_state s) t' ==> pbig Pi (Scope c) s (<s|t'>)"
| Call:    "Pi p = Some c ==> pbig Pi c (enter_state s) t'
              ==> pbig Pi (Call p) s (<s|t'>)"
```

- `pbig ==> pcompletes`: induction on `pbig`; each case is one existing lemma
  (`pcompletes_Seq`, `pcompletes_Call`, …). Near-free.
- `pcompletes ==> pbig`: the only genuinely new Phase-1 proof (HOL-IMP `small_to_big`
  analogue with frames; ~1 day). Uses `psteps_Seq_Restore_body` /
  `psteps_framed_entry` to peel a `Call`/`Scope` as one `pbig` step.

Then `compile_correct` (terminating form), inducting on `pbig`, threading `s :
cfg_collect g S en ==> t : cfg_collect g S ex`; the `Call`/`Scope` cases use the
enter edge + combine triple, so the summary shape of `cfg_witness` matches exactly.
Compose with `backward_sim` for `big_step ==> cfg_runs_to`.

**Honest scope caveat (must be stated at the theorem):** Phase 1 proves *only*
terminating exit correctness. It says nothing about nonterminating programs or
internal program points, and is therefore weaker than "analysis >= source
semantics." It is a validation slice, not the headline.

---

# Phase 2 — per-point reachability correctness (small-step, located CFG)

```
source psteps (explicit stack) ──sim relation──▶ located cstep (explicit stack)
located cstep ──(B1: one step = one edge/combine closure)──▶ cfg_collect at point
```

## (2) Required CFG configuration and transition rules

A **located** CFG configuration carries a program point, a store, and an explicit
call stack of `(return-point, caller-store)` pairs:

```isabelle
type_synonym cframe  = "pp * store"           (* return pp + caller store *)
type_synonym cconf   = "pp * store * cframe list"
```

Transition `cstep g :: cconf => cconf => bool`:

```isabelle
inductive cstep :: "cfg => cconf => cconf => bool" for g where
  Intra:  "(u, a, v) : edges g ==> a ~= EA_Enter ==> edge_step a s = Some s'
             ==> cstep g (u, s, st) (v, s', st)"
| Call:   "(c, EA_Enter, en_p) : edges g ==> (c, ex_p, ret) : combines g
             ==> cstep g (c, s, st) (en_p, enter_state s, (ret, s) # st)"
| Return: "(c, ex_p, ret) : combines g
             ==> cstep g (ex_p, t, (ret, cs) # st) (ret, <cs|t>, st)"
```

Notes:
- The `Call` rule pairs the enter edge and the combine triple by their shared call
  node `c` (the compiler emits exactly one of each per call site), pushes
  `(ret, s)`, and jumps to the callee entry with `enter_state s`.
- The `Return` rule fires at a callee exit when the stack top's return point matches
  a combine triple, producing `<cs|t>` — literally the source `Restore`'s `<fr|s>`
  (`cs = fr`, `t = s`). **The explicit stack is what dissolves the `layout_sound`
  mutual-recursion knot** that Phase 1's summary form needs.
- Assume/AssumeNot edges are ordinary `Intra` steps (`edge_step` returns `None` when
  filtered, so no `cstep` — the branch is simply not taken).

**B1 (located run -> collecting), the easy half:** each `cstep` is exactly one
`cfg_witness` closure step, so
`cstep g cf cf' ==> point-store of cf : cfg_collect g S (point of cf)
   ==> point-store of cf' : cfg_collect g S (point of cf')`,
lifted over `star cstep` by induction. Short; reuses `cfg_collect_edge`,
`cfg_collect_combine`.

## (3) Shape of the source<->CFG simulation relation

Relate source config `(c', s, frs)` to located config `(v, s, st)`. Two invariants:

- **Store equality:** the source store and CFG store coincide (`s` on both sides).
- **Stack correspondence:** the pending `Restore` markers in the residual command
  `c'` are in bijection with `frs` and with `st`; corresponding caller stores agree
  (`frs = map snd st`), and each `ret` in `st` is the return node compiled for that
  call/scope.
- **Focus correspondence:** the current point `v` is the compiled entry of the
  *active leaf* of `c'` — the leftmost statement about to execute — under the
  ambient offset. This is defined **relationally via `compile`**, not as a function
  of `c'` (see the rejected `pp_of`).

Structurally, a running config's residual command is a right-nested tower
`D_1[ Seq (D_2[ Seq ... Restore ]) Restore ]`: each active call/scope contributes a
`Seq _ Restore` wrapper, innermost-first, with one frame per wrapper. The relation
peels this tower in lockstep with `st`. This is a CompCert-style "matching states"
relation; building and proving it is the main Phase-2 burden.

## (4) One source step -> how many CFG steps?

**Zero or one** — a weak/star simulation:

| source step | CFG steps | note |
| --- | --- | --- |
| `Assign` | 1 | `Intra` EA_Assign |
| `IfTrue`/`IfFalse` | 1 | `Intra` EA_Assume / EA_AssumeNot |
| `Scope`/`Call` entry | 1 | `cstep.Call` (push + enter) |
| `Restore` | 1 | `cstep.Return` (combine) |
| `Seq1` (`Seq SKIP c2 -> c2`) | 0 or 1 | compiler's conditional nop edge (`if ex1 = en2 then {} else {(ex1, EA_Nop, en2)}`) |
| `Seq2` congruence | 0 | structural; the inner step does the work |
| `While` unfold | 0 | administrative; the following `If` step maps to the assume edge |

**Key consequence:** for the *reachability* theorem, stuttering (0-step) cases are
**harmless** — we only need `sim src' cfg` with the *same* `cfg`, so **no
well-founded measure is required**. A measure (e.g. residual-command size, with the
`While`-unfold/`If` pair handled together) is needed **only** for the optional
coinductive divergence theorem. Statement:

```isabelle
lemma phase2_step:
  "sim g (c',s,frs) (v,s,st) ==> pstep Pi (c',s,frs) (c'',s',frs')
     ==> EX v' st'. star (cstep g) (v,s,st) (v',s',st') & sim g (c'',s',frs') (v',s',st')"
```

Induct `star pstep` from the initial config to any reachable `cfg'`; combine with
B1 to land `store cfg' : cfg_collect g {s} (point of cfg')`. `cfg_runs_to` (hence
Phase 1's exit statement) falls out at `cfg' = (SKIP, t, [])`.

## (5) Smallest recursive example (call + restore + combine)

`Example_Inc_Proc` exercises call/restore/combine but is non-recursive.
`Example_Proc_Recursion_CFG`'s `f() { if (G<1) f() else G:=G }` recurses but
**does not terminate** (G never changes), so it is useless for Phase 1.

Smallest terminating recursive witness — a countdown:

```
int G;
void f() { if (G > 0) { G := G - 1; f() } }   (* implicit else SKIP *)
void main() { f() }
```

Run at `G = 1`: enter `f` (`G>0`), `G := 0`, recursive `Call f` (`G=0`, guard
false, skip), return (combine), return (combine). This exercises, twice over:
the self-recursive enter edge `(call_f, EA_Enter, en_f)` (the bug-fix edge, already
eval-checked in `Example_Proc_Recursion_CFG`), the `Restore`/combine at each level,
and a nested call stack of depth 2. Add it as `Example_Proc_Countdown` (or extend
the existing recursion theory) — it is the running example for both phases.

---

## Simulation relation summary (Phase 1 vs Phase 2)

| | Phase 1 (big-step) | Phase 2 (located small-step) |
| --- | --- | --- |
| source side | `pbig` (no stack, restore baked into `Scope`/`Call`) | `pstep` with explicit `frame list` |
| CFG side | `cfg_witness` = `cfg_collect` (summary) | new `cstep` with explicit `cframe list` |
| relation | none — direct structural induction; recursion closed by `layout_sound` mutual induction | `sim (c',s,frs) (v,s,st)`: store eq + stack bijection + focus-via-compile |
| recursion | `layout_sound` knot (needs step-count measure) | dissolved — stack is explicit on both sides |
| covers | terminating runs, exit only | all finite prefixes, every point (incl. nonterminating) |

## Reusable infrastructure

| Reusable | Where | Phase |
| --- | --- | --- |
| `pcompletes_{Seq,IfTrue,IfFalse,WhileFalse,WhileTrue,Scope,Call}` = `pbig` intro rules verbatim | `IMP2_Proc.thy` | 1 |
| `psteps_Seq_Restore_body`, `psteps_framed_entry`, `psteps_frame_extend/_mono` | `IMP2_Proc.thy` | 1, 2 |
| `cfg_collect_eq_paths`, `cfg_collect_edge`, `cfg_collect_combine`, `cfg_collect_entry` | `CFG_Collect.thy`, `CFG_Collect_Runs.thy` | 1, 2 |
| `edge_step`, `edge_collect_single` (single-store transfer) | `CFG_Collect_Trace.thy` | 2 |
| `enter_state`/`combine_states` algebra (`combine_after_enter_global_assign`, `combine_states_local/global_update`) | `IMP2_Globals.thy` | 1, 2 |
| **Hand-proved single-program instance** `pcall_global_increment_cfg_collect` + `cfg_runs_to_pcall_global_increment` — full worked template of the correspondence for one `Call` | `Example_Inc_Proc.thy` | 1 |
| eval-checked recursive CFG structure (self + mutual enter edges / combines) | `Example_Proc_Recursion_CFG.thy` | 2 |
| `backward_sim` (IMP2 `big_step` -> `pcompletes`) | `IMP2_Bridge.thy` | 1 |
| edge/combine-subset monotonicity pattern (`trace_witness_ext_edges`, `CFG_Prune`) | trace + prune | 1, 2 |

## Implemented proof chain

`Compiler_Correctness_Prototype.thy` contains the required Phase-2 components:

- `cstep`, `located_sound`, and `csteps_preserve_located_sound` connect located
  CFG runs to `cfg_collect`.
- `control_at` and `frames_match` express focus and stack correspondence without
  reconstructing a program point from a residual command.
- `control_step_simulation` proves one IMP2 step is simulated by zero or more CFG
  steps.
- `concrete_program_step_match` instantiates the simulation for the graph and
  layout produced by the two-pass compiler.
- `compiled_source_simulation.source_reaches_cfg_collect` lifts the result to all
  finite prefixes.
- `cfg_collect_prune_to_query` justifies solving the backward-reachable query cone.
- `concrete_source_reaches_side_analyse_eff` composes the concrete compiler
  simulation, collecting semantics, pruning, and side-solver soundness.

The compiler invariants used by the proof include procedure-layout completeness,
body/layout endpoint agreement, fragment embedding into the whole-program edge
and combine sets, source-command closure, and exact stack-site correspondence.

The remaining optional results are `pbig <-> pcompletes`, a named terminating-exit
projection, and coinductive divergence preservation. None is required for the
finite-prefix source-to-analysis theorem.

**Originally anticipated general compiler lemma:**

```isabelle
(* endpoints depend on lay only through None/Some case-split in Call *)
lemma compile_endpoints_lay_indep:
  "(ALL p. (lay1 p = None) = (lay2 p = None)) ==>
   compile Pi lay1 c n = (n1, en1, ex1, E1, C1) ==>
   compile Pi lay2 c n = (n2, en2, ex2, E2, C2) ==>
   n1 = n2 & en1 = en2 & ex1 = ex2"
```

The completed proof did not need this general layout-independence statement.
Instead, it proves the narrower two-pass facts used by the simulation:
`compile_procs_list_complete`, `compile_procs_list_body`, and
`compile_procs_list_fragment`, then packages them in `proc_layout_sound`.

## Residual assumptions and scope

`compile_prog` is no longer an unverified step between `pstep` and the analyzer.
The source-facing theorem still deliberately takes `pstep` as the operational
semantics of the procedural language. Relating `pstep` in the other direction to
AFP IMP2 big-step semantics remains the separate Track-A task documented in
`AFP_IMP2_FORWARD_SIM_MIGRATION.md`.

The proof establishes finite-prefix preservation. It does not claim a
step-for-step correspondence or coinductive divergence preservation; neither is
needed to cover every source state reachable in a finite number of steps.

## Milestone status

**Phase 1 (terminating exit correctness, optional):**

- **M1** — `pbig` + `pbig <-> pcompletes`. Gate: `big_step_imp_pbig` composes with
  `backward_sim`.
- **M2** — `cfg_witness` edge/combine monotonicity; restate `Example_Inc_Proc` as an
  instance of the general `compile_correct` shape (sanity template).
- **M3** — `compile_correct` (terminating) for a single ambient graph with a *given*
  sound layout (embedding + `layout_sound` as hypotheses). Induction on `pbig`.
- **M4** — shared compiler lemmas: `compile_endpoints_lay_indep` + fragment embedding
  for `compile_procs_layout` / `_bodies` (risks 1, 3).
- **M5** — discharge `layout_sound` for `compile_prog`; headline
  `pbig ==> cfg_runs_to`, and `big_step ==> cfg_runs_to`. **State the terminating-only
  caveat explicitly.**

**Phase 2 (per-point reachability correctness, complete):**

- **M6 (done)** — define `cstep`; prove B1 (`star cstep` -> `cfg_collect` at every
  point), using the concrete fragment-embedding lemmas.
- **M7 (done)** — define the matching relation; prove the weak simulation (zero or
  more CFG steps per source step; no measure needed for reachability).
- **M8 (done)** — finite-prefix reachability theorem: `psteps Pi (c,s,[]) cfg' ==>
  store cfg' : cfg_collect (compile_prog Pi ps c) {s} (point of cfg')`. Compose
  downstream for the full **analysis >= source semantics at every point, including
  nonterminating runs**.
- **M9 (optional)** — coinductive divergence preservation (needs the residual-size
  measure). Not on the critical path.

The implementation closed M6-M8 directly. M1-M5 remain useful only if a named
big-step or terminating-exit theorem is wanted independently of the stronger
small-step result.

## Related docs

- `docs/AFP_IMP2_FORWARD_SIM_MIGRATION.md` — the open `pcompletes -> big_step`
  ("Track A") forward-simulation direction; orthogonal to this compiler proof.
- `docs/IP_ONLY_CONSOLIDATION.md`, `docs/SESSION_DAG_MIGRATION.md` — the
  interprocedural language and session layout this rides on.
