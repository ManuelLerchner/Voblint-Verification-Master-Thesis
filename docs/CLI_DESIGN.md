# CLI design: `voblint-verify`

Design only — no implementation in this pass. Scoped by issue #29 as a deliberate follow-up
once a generated, runtime-parametric analyzer API existed; it now does
(`analyse`/`Voblint_Analyse`, see `Example_Analysis_Dispatch.thy`).

Issue #97 ("External `.voblint` regression corpus with inline expectations and standalone
parser") already covers the standalone parser and `tests/regression/` corpus this design
shares a parser with — read that issue for the regression-corpus side (inline
`// PROVED`/`// REFUTED`/`// UNKNOWN` expectations, directory layout, CI wiring). This document
covers only the CLI itself; the parser it depends on is the same parser #97 needs, so that
issue's "Standalone parser" section is this design's parser section too, not a duplicate.

## Shape

```text
voblint-verify --analysis sign|interval --file test.voblint
voblint-verify --analysis sign|interval --file test.voblint --to-graphviz
```

- `--analysis sign|interval` selects the domain (`Sign_Analysis`/`Interval_Analysis`).
- `--file` is a `.voblint` source file.
- `--to-graphviz` additionally emits a `.dot` rendering of the compiled CFG.
- No other flags. A thin CLI over an existing verified API doesn't need more surface than that
  to be useful; add flags only when a concrete use needs them.

## Architecture

```text
.voblint text
    |
    |  unverified host-language parser (hand-written, new)
    v
imp_prog                              <- built via the already-exported AST
    |                                     constructors (Assign, Seq, Call, imp_prog.make,
    |                                     proc_decl_of, ...): the regression drivers
    |                                     (codegen/regression/{haskell,ocaml}) already
    |                                     construct imp_prog values this way by hand, so
    |                                     the constructor surface is proven sufficient.
    v
analyse Sign_Analysis|Interval_Analysis   <- verified, exported (Voblint_Analyse module)
    |
    v
check_report_entry list                   <- print via string_of_bexp/Check_Proved/etc.
    |
    v  (--to-graphviz only)
prog_cfg / cfg_intra_list / cfg_calls_list -> .dot
```

The parser is the only new component. Everything from `imp_prog` onward already exists and
is exported; the CLI is host-language plumbing over it, not new Isabelle proof work.

## Trust boundary

State this explicitly in the CLI's own `--help` output and README, not just here:

> Soundness applies to the `imp_prog` the parser produces, not to the claim that this
> `imp_prog` faithfully represents the text file the user wrote. The parser is unverified,
> the same way Goblint's own C frontend is unverified — parsing was never in the soundness
> scope of either project. A parser bug can change *which* program gets analyzed; it cannot
> invalidate the analyzer's soundness theorem for the AST actually produced.

The parser should build the exported AST directly (no second, parser-owned intermediate
representation) — one less place for the parsed program to diverge from what the verified
API actually consumes.

## Known safety requirement: Interval containment

`analyse Interval_Analysis` is sound but not proven total: it can still diverge on a
finite program whose global-writing transfer depends monotonically on the flow-insensitive
global summary's own current value (see the warrowing-backend work; the certified backend
already fixed the previously-documented crash cases, but totality itself is not a theorem).
Reproductions during development included process/backend crashes, not just long-running
computation, so the containment mechanism must be a killable subprocess, not an in-process
timeout:

```text
CLI parent
    |
    +-- spawn analyzer worker (separate process)
           |
           +-- analyse Interval_Analysis prog
```

Parent enforces:

- a wall-clock timeout;
- process termination on timeout;
- a controlled diagnostic on abnormal worker exit (crash or timeout), not a silent hang;
- a memory/resource bound, if easy on the target platform.

This is temporary containment for a CLI, not a fix. The fix (if one lands) is a proven-total
or explicitly-scoped-nonterminating backend at the Isabelle level; the subprocess boundary
exists only because a CLI is where an unsuspecting user actually hits the gap.

## Explicit non-goals (unchanged from issue #29)

- Parsing arbitrary C or another external source language.
- Verifying the parser itself.
- Runtime generation of proof objects.
- Comparison against Goblint's own output.
