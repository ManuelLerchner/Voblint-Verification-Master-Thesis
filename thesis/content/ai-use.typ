#import "../lib/stats.typ": _grouped as _n

// Aggregates only, written by tools/ai_use_stats.py from local session logs.
#let _ai = json("/shared/generated/ai-use-stats.json")

= Use of Generative AI <ai-use>

The Leiden Declaration on Artificial Intelligence and Mathematics recommends
that authors transparently disclose the automated tools they use, including
large language models @leiden26. This section follows that recommendation.

Substantial parts of this work were carried out with generative AI tools,
primarily Anthropic's Claude, OpenAI's ChatGPT and Codex, and Cursor. Under the author's
supervision, the tools produced a large share of the implementation-level
material.

The author's own contribution lies mainly in the design of the formalization
and in the review of what it proves. On the design side, this
includes modeling the overall architecture on Goblint's and adapting the local
traces of Schwarz et al. @schwarz21 to activation traces. It also includes
splitting soundness into independent obligations for the abstract operations,
the calling contexts, and the solver. The review concerns the definitions,
assumptions, and theorem statements, which Isabelle cannot check against their
intended meaning.

In the Isabelle development, AI agents generated many proofs, carried out
refactorings across theories, and transformed tactic-style proofs and
Sledgehammer output into structured Isar. Once the definitions and locale
boundaries had stabilized, many of the remaining obligations followed from the
invariants in a few steps, and agents discharged them with little guidance.
Agents also proposed designs and drafted planning documents for larger changes,
which the author accepted, changed, or rejected. For the thesis, agents assisted with literature searches,
checked citations and claims against the cited sources, and drafted and revised
the chapter structure, text, and figures under the author's review. Agents also
wrote the command-line tool and the project site.

Separately, Grammarly was used to check spelling and grammar in the thesis text.
The Isabelle interfaces of AutoCorrode @autocorrode and the Isabelle PIDE MCP server
@pidemcp served as proof-development infrastructure, and the proof work followed the human-guided workflow proposed
by Kappelmann et al. @kappelmann26.

For the analysis framework, agents inspected Goblint's OCaml sources to
identify interfaces the formalization could approximate (@sec:rel-goblint).
Examples are local and global unknowns, unknowns indexed by node and context,
and the enter/combine protocol at calls. The source language and its
compilation, the activation traces, the coverage contract, and the
corresponding proofs have no direct counterpart in Goblint and were developed
for this work.

Throughout the project, the author also investigated how to detect and correct errors
introduced by agents in a formal development of this size. Agent output
was checked before it was accepted, by Isabelle, by tests, or by manual review,
depending on the kind of change. Agents
proposed incorrect lemmas. In one case, an agent introduced a premise into the
end-to-end soundness theorem that no program satisfied. The theorem was
therefore vacuous until the solver run was redesigned. The
author's audits of theorem statements and full batch builds exposed these
errors. The non-vacuity instances of @sec:nonvacuity now show that the premises
of the end-to-end soundness theorem and its companions can be satisfied.

To detect errors and check consistency across the project, the author directed
the development of extensive tooling, much of it implemented by agents (@sec:voblint-repo). A regression corpus, including
ports of Goblint regression tests, records the expected analyzer output, and
`isar-tools` finds duplicated and unused lemmas in the proofs. Automated checks
compare the theories, the generated material, the analyzer, the project site,
and the text of this thesis with each other. These checks exposed errors that
manual reading had missed.

#let _cc = _ai.claude_code
#let _cx = _ai.codex

@fig:ai-sessions quantifies the recorded part of this assistance using
session-log counts, following Bryant et al. @bryant26munkres[Section 5]. The counts
measure interaction with the tools, not authorship or the proportion of the work
attributable to them. Earlier Claude Code sessions, ChatGPT in the browser, and Cursor left no
local logs and are not counted. The author sent #_n(_cc.top_level.human_messages)
messages to Claude Code and #_n(_cx.top_level.human_messages) to Codex.
Co-author lines in commit messages were not kept consistently and are not used
as a measure.

#let _row(label, key, codex: true) = (
  label,
  ..(_cc.top_level, _cc.subagents).map(s => _n(s.at(key))),
  ..(_cx.top_level, _cx.subagents).map(s => if codex { _n(s.at(key)) } else [--]),
)
#figure(
  table(
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
  ),
  kind: table,
  caption: [Recorded assistant activity, counted on #_ai.snapshot from local session
    logs (#_cc.top_level.first_day to #_cc.top_level.last_day for Claude Code,
    #_cx.top_level.first_day to #_cx.top_level.last_day for Codex). Rows count tool
    calls, not distinct changes or successful builds. Shell edits count as shell calls,
    theory edits through the Isabelle server as server calls.],
) <fig:ai-sessions>

Isabelle/HOL accepts every theorem in the development. Proofs by evaluation,
used for some facts about fixed programs, additionally rely on Isabelle's code
generator. This establishes the stated propositions
relative to their definitions and assumptions, but does not establish that those
definitions faithfully capture the intended language or analysis. Definitions
and theorem statements were therefore also checked against example programs, the
regression corpus, and the documented differences between VIMP and C11, much as a human
audit checks the statements of AI-generated formal proofs @hales26lean[Sec. "Is Lean reliable?"].
The author reviewed the related-work claims against the cited sources, often after a first check by an agent. Responsibility for the final claims, framing, and treatment of related work lies
with the author alone.
