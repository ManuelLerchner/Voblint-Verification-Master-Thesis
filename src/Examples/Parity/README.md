# Examples / Parity

One theory, one program, one end-to-end claim. `Example_Parity_DG_Flagship.thy`
is the evidence that the domain-registration API is reusable rather than
Sign-shaped: it instantiates the same registration locale Sign uses in
production, at Parity, without copying a proof step out of Sign's file. Nothing
else lives here, because nothing else has to — a second domain that needed a
second copy of the plumbing would be the negative result.

| File | Role | What |
| --- | --- | --- |
| `Example_Parity_DG_Flagship.thy` | canonical spine | parity analysis of an even-step loop, executed and certified on the D/G spine; registers through `local_state_dg_exec_analysis` as `parity_ex_reg` with no copied `Hstep`/`Hcomb`, `strategy_tree`, or post-solution transport proofs |

The Parity member of the store-only check trio
(`Example_Parity_Checks_Store_Only.thy`) lives in `CLI/` alongside Sign's and
Interval's, so the three read together.

## Vocabulary

The theory uses these as given; they are local jargon, not English.

| Term | Meaning |
| --- | --- |
| Base construction | the D/G shape in which one local unknown per program point carries the *whole* abstract state — every VIMP variable, declared global or not — with no separate flow-insensitive `G` slot to reconstruct through. `local_state_dg_exec_analysis` is its registration locale. |
| ownership split | the other shape, and the other locale (`ownership_split_dg_exec_analysis`): locals in the local unknown, declared globals in a flow-insensitive side slot, recombined by `combine_env`. Interval's flagship registers that way. Parity does not, which is the point of reading the two files side by side. |
| classifier, `gs` | `vname => bool`, VIMP's own answer to *is this name a declared global*. `parity_gs` is `declared_global parity_program`: the program's `global` declaration decides, never the spelling of the name. |
| placed state, `exec_dg_st` | the executable carrier. Locations are *tagged*, so one name can occupy a local and a global slot at once; the classifier picks which slot a readback sees. This is why `parity_is_bot_exact` is an obligation and not a triviality — the bottom test must ignore the slots the readback drops. |
| local unknown | one solver variable per `(pp, ())`, holding a `parity exec_dg_st lifted`. The `lifted` wrapper adds `Bot` for *this point was never reached*. |
| routed unit context | the trivial context policy: the unknown's context component is `()`, so every program point has exactly one abstract state. The flagship runs at this policy only; the CLI also routes Parity through entry-state and call-string contexts. |
| `parity_lookup` | read one variable out of a solved local unknown. `Bot` reads back as `PTop`, so a lookup is only informative at a node known to be reachable. |

## The program, carried end to end

```c
global total;
void main() {
  x := 0;
  Gcount := 1;
  while (x < 20) { x := x + 2; Gcount := Gcount + 1 };
  total := x + Gcount
}
```

Three variables, chosen to separate the three things that can happen to a
parity across a loop. `x` steps by two, so it stays `PEven`. `Gcount` steps by
one, so the back edge joins odd against even and it reaches `PTop`. `total` is
the one declared global — despite the plain name, while `Gcount` stays local
despite the `G` prefix — and the loop never writes it, so it still holds the
zero-initialised `PEven` where the loop is left.

`compile_prog` numbers the program points in source order:

| point | what sits there |
| --- | --- |
| `0` | before `x := 0` |
| `1` | before `Gcount := 1` |
| `2` | the loop head, carrying the guard `x < 20` |
| `3` | the body's first point, before `x := x + 2` |
| `4` | before `Gcount := Gcount + 1`; its edge closes the loop back to `2` |
| `5` | where the guard's false edge leaves the loop |
| `6` | after `total := x + Gcount` |

The theory inspects `2` and `5`. That numbering is worth stating here because
nothing in the file's own text checks it: a lemma named for the loop head that
pins the wrong node still evaluates, and the build stays green.

The chain the theory then walks, one section each:

```text
parity_program              the VIMP source above, in program notation
  -> parity_pi              its procedure table
  -> parity_cfg             compile_prog; compiled_cfg gives finiteness and entry/exit
  -> parity_ex_reg          the registration, interpreted once at parity_gs
  -> parity_eqs             the routed equation system the locale owns
  -> parity_sol             what the vendored always-join solver computes, by eval
  -> parity_head_computed   x = PEven at 2, and three more readings
  -> parity_source_run_sound  every reachable VIMP store, at its matched point
```

Only two steps are this program's own work: `parity_wf` (the compiler's
well-formedness precondition) and `parity_is_bot_exact` (emptiness exactness on
the placed carrier). Everything between the equation system and the source-level
theorem is the locale's.

The solver is the plain always-join rule, with no widening: `parity` is a
four-element lattice, so the ascending chain terminates on its own. That is the
one place where reading this file next to Interval's flagship — which needs
warrowing — shows a real difference rather than a naming one.

`parity_head_excludes_odd_store` closes the file by rejecting a concrete store
from `parity_ex_reg`'s own concretization, the same one `parity_source_run_sound`
reads through. Without it the theorem could be true and empty.

## Session shape

```text
Voblint_Nonrelational
        |
Voblint_Analysis_Parity        parity_tf, parity_tf_st_for, cinit_parity_st
        |
Voblint_Examples_Parity        this directory
```

Everything else the theory imports comes from ancestors of that parent:
`Voblint_Soundness` (`Run_Analysis_Sound`: both registration locales and
`run_source_sound`), `Voblint_Compile` (`compile_prog`, `compiled_cfg`),
`Voblint_Exec` (the placed carrier and `gamma_exec`), `Voblint_Solver` (the
vendored always-join solver), and `Voblint_VIMP` (the `program { ... }`
notation). No sibling domain is in the closure, which is why a Parity witness
cannot accidentally depend on Interval's.

Role vocabulary: repository `README.md`.
