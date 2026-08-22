# Paper examples

Voblint's answers to the worked examples in

> H. Seidl, V. Vojdani, J. Erhard, M. Schwarz.
> *Mixed Flow-Sensitive Static Analysis: Engineering Modularity.*
> FM 2026, LNCS 16557, pp. 446-470.
> <https://doi.org/10.1007/978-3-032-26220-2_22>

the tutorial this formalization follows. Other groups are organized by which
part of the analyzer a case exercises; this one is organized by which passage
of the paper a case answers, so the same behavior may also be covered
elsewhere on its own axis. Each case's header names the passage and quotes
the claim it is measured against.

## Coverage

| Paper | Claim | Here |
| --- | --- | --- |
| Fig. 1, Example 1 | A flow-insensitive summary of `g` collects 1, -17 and 42, which suffices to falsify the error condition | `precision/01-fig1_sequential_globals.vimp` |
| Example 2 | Widening the accumulated value drives `g` to `[-inf,+inf]`, losing `g <= 42` | `known-imprecision/02-whole_global_widening.vimp` |
| Example 3 | A flow-insensitive analysis infers `h = [0,+inf]`, unable to tell one execution of line 4 from many | `precision/01-fig1_sequential_globals.vimp` |
| Example 5 | Fig. 1's side-effecting constraint system: one unknown per program point, plus `[g]` and `[h]` | `precision/01-fig1_sequential_globals.vimp`'s `EXPECT-GRAPH` block |
| Sect. 3 close | Contexts, by callstring or by tabulation, considerably increase precision | `known-imprecision/04-context_insensitive_calls.vimp` (the baseline they improve on) |
| Example 7 | 1-callstring: the context is the call site, `context(u,f,args) _ _ = u` | `precision/05-example7_one_callstring.vimp` |
| Example 8 | Partial tabulation: the context is the entered state, `C = D[start_f]` | `precision/06-example8_partial_tabulation.vimp` |
| Sect. 5.3 | Separating contributions by origin and widening per origin is "sufficient to recover a precise result in Example 1" | `precision/03-per_origin_widening.vimp` |

## What is not reproduced, and why

**Examples 4, 6, 9 (Figs. 2 and 3) need threads.** They turn on `create`,
on interference between threads, and on digests abstracting concurrent
traces. VIMP is single-threaded and has no `create`, so these have no
transcription -- not an imprecision to record, but a language feature this
formalization does not have.

**Examples 10-12 (Figs. 4-8) are Goblint's OCaml API.** They show how to
write the analysis from Example 4 against Goblint's `Spec` signature and
manager type. They describe an implementation, not an analysis result, so
there is nothing here for a `.vimp` fixture to assert.

## Why case 01 is more precise than Examples 2 and 3

Examples 2 and 3 are losses that follow from analyzing `g` and `h`
flow-insensitively, which the paper presents as a choice: "In principle, the
values of g and h could be analyzed flow-sensitively. For efficiency, we may
choose to analyze the values of one or both of them flow-insensitively."

The `voblint` CLI makes the other choice, and so does Goblint on
single-threaded code -- `base.ml` reads globals from local state without
publication at all (`docs/GOBLINT_ALIGNMENT_REGISTER.md`, D/G reconstruction
and publication timing, source-checked 2026-08-10). A declared global lives
in the same reachability-lifted local unknown as every other variable, so on
Fig. 1 case 01 answers `g == 42` and `h == 1` exactly, and answers the same
under all four of `--solver join|per-origin|warrow|warrow-per-origin`.
Nothing about a `global` here exercises the update rule.

So cases 02 and 03 stage the paper's widening chain on the unknown that does:
a procedure's `FunctionEntry` seed, side-effected once per call site, with
the paper's own three contributions in the paper's order. The result is the
paper's -- `[-inf,+inf]` under whole-value warrowing, `[-17,42]` per origin.

The flow-insensitive placement itself is formalized, just not selectable from
VIMP source or a CLI flag, so it has no fixture here.
`unit_dg_spec_placed` (`src/Core/Solver/Context/DG/DG_Framework.thy`) takes a per-variable
`keep_local`/`publish_side` placement, and `Example_Interval_Placement.thy`
evaluates a program with one global on each side: the published one reads
`[0,+inf]`, which is Example 3's answer for `h`, for Example 3's reason. See
`docs/PER_ORIGIN_WIDENING.md`.
