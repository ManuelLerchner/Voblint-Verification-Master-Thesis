# Voblint examples

The examples are the leaf of the proof-session chain: executable runs,
concrete regressions, and the narrative capstone. Nothing depends on them at
all -- `Voblint_Codegen`'s parent is `Voblint_CLI`, not this session -- so
every minute they cost buys verification and exposition only.

One folder is one session, and a domain's folder is parented on that domain's
analysis session, so `Voblint_Examples_Sign` never pulls Interval or the
`int_dom` product into its closure. `CLI/` is the residue: the witnesses that
go through a codegen entry point, the `AnalysisConfig` dispatcher, or the
GraphViz render surface reach `Voblint_CLI`, which is parented on
`Voblint_Analysis_Int` and therefore does see every domain. Those live
together rather than being spread back through the domain folders, where they
would recouple each domain's session to all of them.

`Voblint_Examples` itself holds only `Voblint.thy`. Making `Voblint_Examples_CLI`
its parent rather than a listed session is not cosmetic: theories imported from an
ancestor come from that session's heap, while theories imported from a merely
listed session are re-elaborated in the importing one. The capstone imports ten
CLI witnesses, so this is the difference between building them once and twice.

| Session | Folder | Parent |
| --- | --- | --- |
| `Voblint_Examples_CFG` | `CFG/` | `Voblint_Compile` |
| `Voblint_Examples_Sign` | `Sign/` | `Voblint_Analysis_Sign` |
| `Voblint_Examples_Interval` | `Interval/` | `Voblint_Analysis_Interval` |
| `Voblint_Examples_Parity` | `Parity/` | `Voblint_Analysis_Parity` |
| `Voblint_Examples_Congruence` | `Congruence/` | `Voblint_Analysis_Congruence` |
| `Voblint_Examples_Int` | `Int/` | `Voblint_Analysis_Int` |
| `Voblint_Examples_Relational` | `Relational/` | `Voblint_Analysis_Relational` |
| `Voblint_Examples_Tooling` | `Tooling/` | `Voblint_Analysis_Interval` |
| `Voblint_Examples_CLI` | `CLI/` | `Voblint_CLI` |
| `Voblint_Examples` | `Voblint.thy` | `Voblint_Examples_CLI` |

`Voblint_Examples_Tooling` is parented on Interval because its solver- and
generator-layer witnesses need *some* domain to make the effect visible, not
because they are about intervals.

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
| `Int/` | Sign x Interval x Parity x Congruence | composite-domain regressions and refinement-mode witnesses |
| `Relational/` | relational | the generic pipeline and solver run against a non-`abs_state` order carrier |
| `CFG/` | domain-agnostic | compiler and collecting-semantics regressions; shared example programs |
| `Tooling/` | domain-agnostic | solver buffering regressions, per-origin widening, the strategy-tree and TD-program demos |
| `CLI/` | crosses every domain | codegen entry points, dispatcher and result-table witnesses, the contextual GraphViz regression |

Regressions live in these sessions, not upstream, on purpose: `VIMP` -> `CFG` ->
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
