# Voblint examples

`Voblint_Examples` is the leaf of the proof-session chain. It contains
executable runs, concrete regressions, and the narrative capstone. Nothing
depends on it at all: `Voblint_Codegen`'s parent is `Voblint_CLI`, not this
session, so every minute this session costs buys verification and exposition
only.

Folders are grouped by abstract domain, not by capability: every analysis in
this framework runs concretely inside Isabelle/HOL (the executable pipeline is
a whole-framework property, not a subset of examples), and every analysis is
built on the same procedure-aware CFG/D-G pipeline (interprocedural reasoning
is baseline, not opt-in). What actually varies between examples is which
domain they instantiate and whether their demo program happens to contain a
procedure call.

| Folder | Domain | Contents |
| --- | --- | --- |
| `Sign/` | Sign | codegen probes, procedure-call soundness spines |
| `Interval/` | Interval | codegen probes, flagship D/G runs, context-sensitive (call-string) D/G, procedure-call spines, backward-analysis trace soundness |
| `Congruence/` | Congruence | executable standalone arithmetic and backward-filtering regressions |
| `Parity/` | Parity | domain-registration validation flagship |
| `Product/` | Sign x Interval x Parity x Congruence | composite-domain regressions and refinement-mode witnesses |
| `Relational/` | relational | the generic pipeline and solver run against a non-`abs_state` order carrier |
| `CFG/` | domain-agnostic | compiler and collecting-semantics regressions; shared example programs |
| `Regression/` | domain-agnostic | dispatcher, result-table, compile and min/max acceptance witnesses. A regression that names a domain belongs with that domain, not here. |
| `Tooling/` | domain-agnostic | contextual GraphViz regression, solver buffering regressions, the strategy-tree demo |

Regressions live in this session, not upstream, on purpose: `VIMP` -> `CFG` ->
`Analysis` -> `Soundness` stay soundness-only, and concrete witness
programs remain at the proof chain's leaf. The codegen session consumes their
executable definitions without moving code export into the soundness chain.

`Voblint.thy` imports the curated examples and presents the complete certified
pipeline.

## What does not live here

A `value` or `ML_val ... writeln` runs the analyzer at build time and asserts
nothing, so a green build proves only that the code generator produced
something that ran. This session contains none. Anything worth pinning is a
`by eval` lemma; anything only observable as output -- rendered DOT, a report's
text -- is pinned by the executable corpus under `tests/regression/`, which
runs the same analysis through the code-generated CLI in milliseconds and
compares the result.
