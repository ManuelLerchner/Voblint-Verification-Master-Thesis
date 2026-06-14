# Migration — executable abstract domain, run the solver for real

Status: **PLANNED.** No code yet. This document scopes the work to make the IP
analysis *executable* end to end: feed a concrete IMP2 program to the vendored
`TD_side` solver, compute a concrete abstract result, and certify that result
sound via the soundness chain we already proved. Today every example
(`Example_Side_Proc_Global`, `Example_Trace_Digest_Precision`, ...) *assumes* a
post-fixpoint (`side_cfg_ip_solve_dom`) plus an operational run (`pruns_to_ip`)
and proves the assumed fixpoint sound. None compute. `rg 'value|export_code' src`
is empty.

Goal: one honest example — `Example_Side_Execute` — that runs the analyzer on a
real (trivial) program and gets `x |-> SPos`, certified sound, not invented.

---

## 0. The key fact — the solver is already code-ready; the domain is not

The vendored `TD_side` solver **already generates code.** `TD_side_upd_rule.thy`
defines `solve_c` as a `partial_function (option)` with `solve_rec_c.simps[code]`
and `solve_code_equation [code]`; `vendor/td-verification/Example_side.thy`
actually `value`s it on a concrete lock-set analysis. So the machinery to run
exists — our pipeline just never connects to it.

A live `export_code` / `value` probe on `inc_pi` (single global-increment call)
named exactly three gaps:

| # | What Isabelle said | Root cause |
| --- | --- | --- |
| **G1** | `cfg_edges_list`: *"Type nat x edge_action x nat not of sort finite"* | code eq is `if finite (edges g) then sorted_list_of_set (edges g) else []`; the `finite` guard + `sorted_list_of_set` over a bare `set` do not generate |
| **G2** | `td_cfg_side_ip_solver.side_sigma_at`: *"No code equations"* | the solver is wired through a **parameterized locale** interpretation; locale-qualified constants carry no code equations. The vendored `[code]` path is a **global** `defines`-interpretation |
| **G3** | (predicted from source, not yet observed — G2 short-circuits codegen first) | `TD_side.thy:42,64` decide fixpoint stabilization with HOL `=` on the domain. Our domain is `'a abs_state = vname => 'a` (`Abstract_Domain.thy`), a function over `string` — **no executable `equal`** |

G3 is the substantive one. G1/G2 are independent plumbing.

---

## 1. The key fact #2 — this is Nipkow's problem, and his fix transfers

HOL-IMP hits the **identical** wall. `Abs_Int0` uses `st = vname => 'av` and
states verbatim: *"not executable because of the comparison of abstract states,
i.e. functions."* That is G3 word for word.

His fix is `Abs_State.thy`:

```
type_synonym 'a st_rep = "(vname * 'a) list"            -- association list
quotient_type 'a st = "('a::top) st_rep" / eq_st         -- quotient by map_of-equality
less_eq_st_rep ps1 ps2 =
  (ALL x : set(map fst ps1) Un set(map fst ps2). fun_rep ps1 x <= fun_rep ps2 x)
top_st = []
```

The load-bearing move: `<=` ranges **only over the finite union of keys present**
in the two lists; absent variables default to `top`, so they drop out. That makes
`<=` decidable, hence `=` decidable via antisymmetry (`S1 <= S2 & S2 <= S1`) —
exactly like his value-level `equal_ivl i1 i2 = (i1 <= i2 & i2 <= i1)`. Our value
domain `sign` is easier still: a plain datatype, `equal` derived for free.

This is precisely what unblocks our solver. Once the domain is `sign st` instead
of `vname => sign`, the stabilization test `sigma (Inl x) = d_new` only inspects
the finitely many stored variables, and code generation succeeds.

### Two caveats specific to us

1. **Polarity is flipped — dualize the construction.** Nipkow is
   `semilattice_sup_top` (empty list = `top` = no info, analysis descends). Our
   pipeline is `bounded_semilattice_sup_bot`: `side_cfg_T_ip` joins **upward**
   from `bot0`. So we want absent-var default = `bot`, `[] = bot`, `sup` =
   key-union merge joining overlaps, and we must prove the
   `bounded_semilattice_sup_bot` instance. Mechanical, but a deliberate
   dualization — not a copy of `Abs_State`.

2. **Two layers joined by refinement — not a type swap.** `abs_state =
   vname => 'a` is hardwired (`Abstract_Domain.thy`) as the solver's domain `'d`,
   and the entire soundness chain is stated over it. Nipkow does **not** make
   `vname => 'av` executable; he keeps it as the abstract spec (`Abs_Int0`) and
   adds `st` as a separate executable layer (`Abs_State` / `Abs_Int1`), joined by
   `gamma_s` / `lookup` / `update` in the `Abs_Int` locale, then proves
   *executable analyzer refines abstract analyzer*. We owe the analogue.

---

## 2. The bridge obligation — what makes the number honest

A computed `sign st` is just a number until it is tied to the proved chain. The
connection is one lemma: the executable result, read back through `fun_rep`
(lookup with `bot` default), is a **post-solution of the abstract eqs**:

```
part_post_solution (side_cfg_T_ip g sign_tf (sup) bot0 s0)
                   (cfg_exit g)
                   (fun_rep o executable_sigma)
                   stabl
```

Given that, the existing `proc_global_side_sign_analysis` /
`side_ip_sign_analysis_sound` certify `fun_rep (computed)` for free — no new
soundness argument, just transport. This lemma is the executable-refines-abstract
theorem; it is the substance of the migration alongside the domain instance.

---

## 3. Slices (each additive + build-gated; example lands last)

* **S1 `Sign_St` executable domain.** Dualize `Abs_State`: `(vname * sign) list`
  quotient `sign st`, `bot`-default `fun_rep`, instances `order`,
  `bounded_semilattice_sup_bot`, and `equal` (via antisymmetry). Executable
  `lookup` / `update` / `sup` / `bot` / `restrict_local` / `restrict_global` (the
  last two become list filters on the global/local variable split). Gate: the
  instances + a handful of `value` sanity checks (`sup`, `<=`, `=`) build green.

* **S2 edge enumeration (G1).** A code equation for `cfg_edges_list` /
  `predecessor_list` that reads edges off the concrete `mk_cfg` / `mk_ip_cfg`
  build instead of `finite (edges g) ... sorted_list_of_set`. Gate:
  `value "predecessor_list probe_cfg (cfg_exit probe_cfg)"` returns a concrete
  list.

* **S3 global solver entry (G2).** A global (non-locale) executable entry point
  for `side_cfg_T_ip` over `sign st`, reusing the vendored `[code]` `solve`
  (`TD_side_always_join_Interp_solve`-style `defines` interpretation) rather than
  routing through `td_cfg_side_ip_solver`. Gate: `value` of the solver run on
  `inc_pi` terminates and returns a `sign st`.

* **S4 bridge lemma.** `part_post_solution` of the abstract eqs at the executable
  result under `fun_rep` (section 2). Transfer/simulation between the `sign st`
  eqs and the `vname => sign` eqs. Gate: lemma proved, sorry-free.

* **S5 `Example_Side_Execute`.** Tie it together: `value` the run (concrete
  `x |-> SPos`), then certify it sound by S4 + the existing soundness theorem on
  the same `inc_pi`. Replaces the "assume a fixpoint" shape with "compute and
  certify." Gate: full `Voblint_Formalization` build green, example included in
  `ROOT`.

Ordering: G1 (S2) and G2 (S3) are independent of the domain and could land first
to make the solver *callable*; it then hits G3 until S1 is in. S4 depends on S1
and S3. The example (S5) depends on all.

---

## 4. Risks

* **Polarity bugs.** Easiest mistake is to copy `Abs_State`'s `top`-default and
  get a domain whose `[]` means `top` while the solver seeds `bot`. Every
  instance lemma must be re-checked against `bounded_semilattice_sup_bot`, not
  `semilattice_sup_top`. nitpick the lattice laws before proving them.
* **Quotient code setup.** `equal` on a `quotient_type` needs an explicit `[code]`
  / `lifting` setup; lifting `equal` through the quotient is the fiddly part
  (cf. `equal_ivl`). Budget time here.
* **Bridge transfer (S4).** Relating the `sign st` eqs to the `vname => sign` eqs
  point-wise through `fun_rep` is the real proof. If the two constraint-system
  constructions drift structurally, the simulation breaks; keep
  `side_rhs_fold_ip` shared / parameterized over the state ops where possible
  rather than duplicating it at `sign st`.
* **Non-termination at runtime.** `solve_c` returns `None` (loops) if the eqs have
  no post-fixpoint reachable by the strategy. `inc_pi` is finite-height in `sign`
  and must converge; verify on the trivial program before anything larger.
* **`metis`/`smt` in the instance proofs.** Keep the lattice-law proofs structured
  and bounded — batch hang risk (see `CLAUDE.md` build-timeout policy).

---

## 5. Build gate

Interactive `value` success is **not** completion (`CLAUDE.md`: I/Q diverges from
batch). Each slice closes only on a green batch build:

```
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

The example carries a `value` and an `export_code`; both run at build time, so a
green build is also proof the pipeline executes.

---

## 6. Source pointers

* `vendor/td-verification/TD_side.thy:42,64` — the `=` stabilization checks (G3).
* `vendor/td-verification/TD_side_upd_rule.thy` — `solve_c`, `solve_code_equation
  [code]` (the code-ready solver).
* `vendor/td-verification/Example_side.thy` — the precedent: `value` of `TD_side`.
* `src/Analysis/Domains/Abstract_Domain.thy` — `abs_state = vname => 'a`.
* `src/CFG/CFG_Def.thy:145-214` — `cfg_edges_list` / `predecessor_list` /
  `combine_predecessor_list` (G1).
* `src/Analysis/Solver/TD_Side_IP_CFG.thy` — `side_cfg_T_ip` /
  `make_side_rhs_tree_ip` / `side_rhs_fold_ip` (the eqs to mirror at `sign st`).
* `src/Analysis/Solver/TD_Side_IP_Interface.thy` — `td_cfg_side_ip_solver` locale
  + `side_analyse_ip` (G2; the global entry replaces this routing).
* HOL-IMP `Abs_State.thy`, `Abs_Int0/1.thy`, `Abs_Int2_ivl.thy` — the precedent
  for the executable `st` and the abstract/executable refinement split.
