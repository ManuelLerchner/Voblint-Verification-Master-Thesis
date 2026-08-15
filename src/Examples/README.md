# Voblint examples

`Voblint_Examples` is the leaf of the proof-session chain. It contains
executable runs, concrete regressions, visualizations, and the narrative
capstone. No soundness session depends on it; the downstream
`Voblint_Codegen` session imports its executable facade solely to export code.

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
| `Parity/` | Parity | domain-registration validation flagship |
| `Mixed/` | Relational (non-`abs_state`) | same generic pipeline/solver run against a non-`abs_state` carrier |
| `CFG/` | domain-agnostic | compiler and collecting-semantics regressions; shared example programs |
| `Tooling/` | domain-agnostic | Graphviz rendering demos, outside the proof spine |

Regressions live in this session, not upstream, on purpose: `VIMP` -> `CFG` ->
`Analysis` -> `Formalization` stay soundness-only, and concrete witness
programs remain at the proof chain's leaf. The codegen session consumes their
executable definitions without moving code export into the soundness chain.

`Voblint.thy` imports the curated examples and presents the complete certified
pipeline.
