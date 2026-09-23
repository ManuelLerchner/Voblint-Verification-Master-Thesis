#import "../lib/stats.typ": _grouped as _n

// Aggregates only, written by tools/ai_use_stats.py from local session logs.
#let _ai = json("/shared/generated/ai-use-stats.json")

= Use of Generative AI <ai-use>

The Leiden Declaration on Artificial Intelligence and Mathematics recommends
that authors transparently disclose the automated tools they use, including
large language models and proof assistants @leiden26. This section follows
that recommendation. Substantial parts of this work
were carried out with generative AI tools, primarily Anthropic's Claude and
OpenAI's ChatGPT and Codex, working under the author's direction and review.
The AI contributions include large parts of the
Isabelle mechanization, among them proofs, refactorings across the development,
and the translation of tactic-style proofs and Sledgehammer output into
structured Isar; the executable tooling around the formalization, including the
command-line interface, the website, and the checks that keep this thesis
consistent with the sources; literature search; and first drafts and revisions
of this thesis's text and figures. Grammarly was used to check spelling and
grammar of the thesis text. The Isabelle interfaces of AutoCorrode
@autocorrode, used following the human-guided workflow of
#cite(<kappelmann26>, form: "prose"), served as development tooling for this
work on the theories.

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
  Assistant activity on this repository, counted on #_ai.snapshot from the
  local session logs (#_cc.top_level.first_day to #_cc.top_level.last_day for
  Claude Code, #_cx.top_level.first_day to #_cx.top_level.last_day for Codex).
  No local logs are available for earlier Claude Code sessions, ChatGPT in
  the browser, or Cursor, so these are not counted. The author sent
  #_n(_cc.top_level.human_messages) messages to Claude Code and
  #_n(_cx.top_level.human_messages) to Codex. Shell edits count as shell calls.
  Interactions through the Isabelle server, including theory edits, count as
  server calls.
]
#v(0.8em)

The author determined the research direction, decided the architecture, approved and revised the definitions and theorem statements, and reviewed the
development and thesis text. The author is solely responsible for the claims,
framing, and treatment of related work.

Every theorem in the development is accepted by Isabelle/HOL. Proofs by
evaluation, used for some facts about fixed programs, additionally rely on
Isabelle's code generator (@tab:oracles-audit). This establishes the stated
propositions relative to their definitions and assumptions, but not that those
definitions capture the intended language or analysis. Definitions and theorem
statements were therefore also checked against example programs, the
regression suite, and the documented differences between VIMP and C11. Claims
attributed to related work were checked against the cited sources.
