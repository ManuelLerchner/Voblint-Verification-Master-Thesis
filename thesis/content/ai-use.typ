#import "../lib/stats.typ": _grouped as _n

// Aggregates only, written by tools/ai_use_stats.py from local session logs.
#let _ai = json("/shared/generated/ai-use-stats.json")

= Use of Generative AI <ai-use>

This statement follows the recommendation to disclose tool use transparently,
which #cite(<tao26ai>, form: "prose", supplement: [Section 8]) quotes from the
Leiden Declaration on AI and mathematics; Tao names covert use, concealed to
avoid criticism, as the case to avoid. Substantial parts of this work
were carried out with generative AI tools, primarily Claude (Anthropic) and
ChatGPT and Codex (OpenAI), working under the author's direction and review.
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
work on the theories; no theorem depends on them. Part of the assistance is
recorded in the repository history, where commits carry a co-author trailer
naming the assisting model; a commit without such a trailer is not necessarily
unassisted. TODO: author to confirm or correct this list and its proportions,
and to add any results obtained without assistance.

The table below quantifies the part of the assistance that left a record,
following the session-log analysis of #cite(<bryant26munkres>, form: "prose", supplement: [Section 5]). The git history runs from #_ai.git.first_month to
#_ai.git.last_month; of its #_n(_ai.git.commits) commits on the main and
writing branches, #_n(_ai.git.ai_trailer) carry a co-author trailer naming an
assistant. The session logs cover much shorter windows. Claude Code keeps
transcripts for about a month, so its logs begin on
#_ai.claude_code.top_level.first_day; the Codex logs begin on
#_ai.codex.top_level.first_day. Earlier Claude Code sessions, ChatGPT used
through its web interface, and Cursor left no local log and are not counted.
In both logs most tool calls went to the shell or to the Isabelle server, and
Isabelle batch builds were a small fraction of them.

#let _cc = _ai.claude_code
#let _cx = _ai.codex
#let _row(label, key, codex: true) = (
  label,
  ..(_cc.top_level, _cc.subagents).map(s => _n(s.at(key))),
  ..(_cx.top_level, _cx.subagents).map(s => if codex { _n(s.at(key)) } else [--]),
)
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
  #set text(size: 0.9em)
  Assistant activity on this repository, counted on #_ai.snapshot
  from the local session logs, which cover #_cc.top_level.first_day to
  #_cc.top_level.last_day for Claude Code and #_cx.top_level.first_day to
  #_cx.top_level.last_day for Codex. Subagent sessions are started by a main
  session. The author wrote #_n(_cc.top_level.human_messages) prompts to
  Claude Code and #_n(_cx.top_level.human_messages) to Codex main sessions.
  A batch build is a tool call whose command runs `isabelle build`. Edits made
  through the shell count as shell commands; Isabelle theory edits count as
  server calls. Codex also runs tool calls from scripts, so its shell commands
  are not separated. No cost estimate is given.
]
#v(0.8em)

Corrections to the assistants' behaviour were turned into written rules, as
#cite(<bryant26munkres>, form: "prose", supplement: [Section 5.2]) report for
their instruction file. The four instruction files for the assistants changed
in #_n(_ai.rule_files.commits) commits. Their diffs add, among others, a ban
on editing theory files outside the Isabelle server, justified by stale
buffers and "phantom fixes"; the rule that a theorem is done only when its
statement is proved and the batch build passes, which rejects a green build in
which the requested theorem is absent; a ban on checked-in `sorry` and unattributed
Sledgehammer calls; and, for this thesis, the requirement that repository
figures, theorem statements, and analyzer output be generated from the sources
instead of typed, together with the claim discipline that separates proved,
tested, and trusted.

The author chose the research direction and the architecture of the
formalization, fixed the definitions and theorem statements and revised them,
reviewed and edited throughout, and is solely responsible for the thesis's
claims, framing, and treatment of related work.

Isabelle/HOL checked every proof in the development. Some facts
about fixed programs are proved by evaluation, which trusts Isabelle's code
generator; among them are the routed obligations of the mixed-flow instance
(@sec:mixed-flow). @tab:oracles-audit lists which audited theorems depend on
this oracle. This checking establishes the stated propositions relative to their
definitions and assumptions. It does not establish that those definitions
capture the intended language or analysis, or that their interpretation in this
thesis is correct. Definitions and theorem statements were therefore checked
separately against example programs, the regression suite, and a review of
where the formal language departs from C11. The claims attributed to cited work
were checked against the cited source, often only against its abstract and the
sections the thesis relies on.

TODO: agree in writing with the supervisors which AI uses are permitted for
this thesis, and align this statement with that agreement. The TUM CIT thesis
information event for the summer semester of 2026 gives example rules under
which AI may not generate text or code, only support language, translation, and
review, and requires every use to be acknowledged; the binding rules are set by
the chair and supervisor. The declaration of authorship (APSO §18 (9)) requires
that all aids used are listed.
