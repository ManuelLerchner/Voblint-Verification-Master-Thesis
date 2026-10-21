#import "../lib/stats.typ": _grouped as _n

// Aggregates only, written by tools/ai_use_stats.py from local session logs.
#let _ai = json("/shared/generated/ai-use-stats.json")

= Use of Generative AI <ai-use>

The Leiden Declaration on Artificial Intelligence and Mathematics recommends
that authors transparently disclose the automated tools they use, including
large language models @leiden26. This section follows that recommendation.

Substantial parts of this work were carried out with generative AI tools,
primarily Anthropic's Claude, OpenAI's ChatGPT and Codex, and Cursor. Under the
author's supervision, these tools contributed a large share of the
implementation-level material. The author chose the research direction,
selected and revised the designs, and approved the definitions and theorem
statements.

In the Isabelle development, the tools generated many proofs, carried out
refactorings across theories, and transformed tactic-style proofs and
Sledgehammer output into structured Isar. They proposed designs and drafted
planning documents for larger changes. For the thesis, they assisted with
literature searches, checked citations and claims against cited sources, and
drafted and revised the chapter structure, text, and figures.

Separately, Grammarly was used to check spelling and grammar in the thesis text.
The Isabelle interfaces of AutoCorrode @autocorrode and the Isabelle PIDE MCP server
@pidemcp served as proof-development infrastructure, and the proof work followed the human-guided workflow proposed
by Kappelmann et al. @kappelmann26.

The assistance also extended to design. To formalize calling contexts, the
concrete semantics is based on traces instead of states, inspired by the local
traces of Schwarz et al. @schwarz21. Language models helped adapt the
thread-local setting of that work to procedure activations. The requirements for
the activation traces of @sec:activation-trace were evaluated and refined in
collaboration with agents: how traces are generated, that a callee trace begins
only at a call, that a trace retains its call history, and that calling contexts
are derived from traces.

For the Isabelle development of the analysis framework, agents inspected
Goblint's OCaml sources to identify interfaces the formalization could approximate, such as local and global
unknowns, unknowns indexed by node and context, and the enter/combine protocol
at calls (@sec:rel-goblint). The source language and its compilation, the
activation traces, the coverage contract, and the corresponding proofs have no
direct counterpart in Goblint and were developed for this work.

A major part of the development effort concerned finding suitable definitions,
interfaces, invariants, and locale boundaries rather than discharging individual
proof steps. During the first weeks, a small prototype mirrored Goblint's
structure while leaving proof obligations as `sorry`. Once the definitions and
locale boundaries had stabilized, many of the remaining proof obligations were
short and were discharged with substantial agent assistance.

Throughout the project, the author also explored how such tools can be used
responsibly and correctly in a formal development of this size. Agent output was
treated as a proposal until Isabelle, a test or the author's review confirmed it. This
caution was necessary, since the assistants' output was not reliable on its own. Agents proposed incorrect
lemmas and, in one case, introduced a premise into the end-to-end soundness theorem that
no program satisfied, making the theorem vacuous until the solver run was
redesigned. Audits of theorem statements and full batch builds exposed these
errors. The non-vacuity instances of @sec:nonvacuity now demonstrate that the
premises of the end-to-end soundness theorem and its companions can be satisfied.

Agents also wrote much of the tooling around the formalization, such as the
command-line tool, the project site, and the regression corpus with its ports of
Goblint regression tests. They also wrote the checks that keep the theories, the
generated material, the analyzer, the project site, and this thesis consistent
(@sec:voblint-repo). These checks proved especially useful because they replaced
repeated manual inspection with conditions that every change had to satisfy, and
they exposed errors that manual reading had missed.

The table below quantifies the recorded part of this assistance, following the
session-log analysis of Bryant et al. @bryant26munkres[Section 5]. The counts
measure interaction with the tools, not authorship or the proportion of the work
attributable to them.

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

Isabelle/HOL accepts every theorem in the development. Proofs by evaluation,
used for some facts about fixed programs, additionally rely on Isabelle's code
generator (@fig:intro-trust). This establishes the stated propositions
relative to their definitions and assumptions, but does not establish that those
definitions faithfully capture the intended language or analysis. Definitions
and theorem statements were therefore also checked against example programs, the
regression corpus, and the documented differences between VIMP and C11, much as a human
audit checks the statements of AI-generated formal proofs @hales26lean[Sec. "Is Lean reliable?"].
Related-work claims were checked against the cited sources, often with agent
assistance and subsequent author review.

Responsibility for the final claims, framing, and treatment of related work lies
with the author alone.
