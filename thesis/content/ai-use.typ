#import "../lib/stats.typ": _grouped as _n
#import "../lib/code.typ": isathm

// Aggregates only, written by tools/ai_use_stats.py from local session logs.
#let _ai = json("/shared/generated/ai-use-stats.json")

= Use of Generative AI <ai-use>

The Leiden Declaration on Artificial Intelligence and Mathematics recommends
that authors transparently disclose the automated tools they use, including
large language models and proof assistants @leiden26. This section follows
that recommendation.

Substantial parts of this work were done with generative AI tools, mainly
Anthropic's Claude, OpenAI's ChatGPT and Codex, and Cursor, under the author's
direction and review. The tools produced a large share of the
implementation-level material. The author chose the research questions,
selected and revised the designs, and approved the definitions and theorem
statements.

In the Isabelle development, the tools generated many of the proofs, carried out
refactorings across the theories, and turned tactic-style proofs and
Sledgehammer output into structured Isar. They proposed designs and wrote the
planning documents preceding larger changes. They also worked on the
executable tooling around the formalization: the command-line interface, the
website, the regression suite with its ports of Goblint's regression tests,
and the checks that keep this thesis consistent with the sources. For the
thesis itself, they searched the literature, checked citations and claims
against the cited sources, and drafted and revised the chapter plan, the text
and the figures. Most of this
work ran in agent sessions with shell access.

Separately, Grammarly was used to check spelling and grammar of the thesis
text. The Isabelle interfaces of AutoCorrode @autocorrode, used following the
human-guided workflow of #cite(<kappelmann26>, form: "prose"), served as
proof-development tooling. They are not generative AI systems.

The assistance extended to design. The supervisors suggested replacing the state-based concrete semantics with a
trace-based semantics, using the local traces of
#cite(<schwarz21>, form: "prose") as inspiration. The author and supervisors
adopted this change because the work set out to formalize calling contexts,
and the state-based collecting semantics used in the prototype records the
stores reaching a node but not which activation holds each store
(@sec:why-traces). The requirements for the activation-local traces of
@sec:ltr were then developed interactively with language models: the
operations generating the trace set, that a callee trace starts only at a
call, that a trace keeps its call history, and that a calling context is read
from the trace.

For the analysis framework, agents read Goblint's OCaml sources to find the
interfaces that the formalization could approximate: the split into local and
global unknowns, unknowns indexed by node and context, and the enter/combine
protocol at calls (@app:goblint-alignment). Goblint offered a working architecture whose parts correspond to standard
constructions of abstract interpretation. @sec:eval-1161 discusses one
implementation defect found during this work. The source language, its compiler to the control-flow graph, the traces, the
coverage contract and the proofs have no counterpart in Goblint. The solver
and its partial-correctness proof are taken from #cite(<tilscher26>, form: "prose") and were not written for this work.

A major part of the development effort concerned finding suitable definitions,
interfaces, invariants and locale boundaries rather than individual proof
steps. In the first weeks, a small prototype mirrored Goblint's
structure with unproved placeholders (`sorry`). Once the definitions and locale boundaries were settled, most
remaining proof obligations were short and were discharged with substantial
agent assistance. Some proofs remain
long, among them #isathm("routed_node_rhs_buffered_correspondence"),
#isathm("intra_step_simulation") and
#isathm("refine_ivl_with_congruence_mono").

The assistants' output was not reliable on its own. Agents stated wrong
lemmas. They also added a premise to the end-to-end theorem that no program
satisfied, which made the theorem vacuous until the solver run was redesigned. Audits of the theorem statements and full
batch builds found these errors, and the non-vacuity witnesses of
@sec:nonvacuity now show that the premises of the main theorems can be met.

The table below quantifies the recorded part of the assistance, following the
session-log analysis of #cite(<bryant26munkres>, form: "prose", supplement: [Section 5]).
The counts measure interaction with the tools, not authorship or the share of
the work that the tools produced.

#let _cc = _ai.claude_code
#let _cx = _ai.codex
#let _row(label, key, codex: true) = (
  label,
  ..(_cc.top_level, _cc.subagents).map(s => _n(s.at(key))),
  ..(_cx.top_level, _cx.subagents).map(s => if codex { _n(s.at(key)) } else [--]),
)
#v(0.4em)
#block(breakable: false, width: 100%)[
  #align(center, table(
    columns: 5,
    align: (left, right, right, right, right),
    stroke: none,
    table.hline(),
    [], table.cell(colspan: 2, align: center)[*Claude Code*],
    table.cell(colspan: 2, align: center)[*Codex*],
    [], [main], [subagent], [main], [subagent],
    table.hline(stroke: 0.5pt),
    .._row([sessions], "sessions"),
    .._row([assistant messages], "assistant_messages"),
    .._row([tool calls], "tool_calls"),
    .._row([#h(1em) shell], "bash", codex: false),
    .._row([#h(1em) Isabelle batch builds], "isabelle_builds"),
    .._row([#h(1em) Isabelle server (I/Q, PIDE)], "isabelle_mcp"),
    .._row([#h(1em) file edits and writes], "edits"),
    table.hline(),
  ))
  #v(0.4em)
  #set text(size: 0.9em)
  Recorded automated-assistant activity during development, counted on #_ai.snapshot from the
  local session logs (#_cc.top_level.first_day to #_cc.top_level.last_day for
  Claude Code, #_cx.top_level.first_day to #_cx.top_level.last_day for Codex).
  No local logs are available for earlier Claude Code sessions, ChatGPT in
  the browser, or Cursor, so these are not counted. The author sent
  #_n(_cc.top_level.human_messages) messages to Claude Code and
  #_n(_cx.top_level.human_messages) to Codex. Shell edits count as shell calls.
  Interactions through the Isabelle server, including theory edits, count as
  server calls. Co-author lines in commit messages were not kept consistently
  and are not used as a measure.
]
#v(0.8em)

The author set the research direction, revised and settled the requirements,
chose among the designs that the assistants proposed, approved the definitions
and theorem statements, interpreted the results, and reviewed the development
and thesis text. The author is solely
responsible for the claims, framing, and treatment of related work.

Every theorem in the development is accepted by Isabelle/HOL. Proofs by
evaluation, used for some facts about fixed programs, additionally rely on
Isabelle's code generator (@tab:oracles-audit). This establishes the stated
propositions relative to their definitions and assumptions, but not that those
definitions capture the intended language or analysis. Definitions and theorem
statements were therefore also checked against example programs, the
regression suite, and the documented differences between VIMP and C11. Claims
attributed to related work were checked against the cited sources. Agents
performed much of this checking, but the author reviewed and remains
responsible for the resulting claims.
