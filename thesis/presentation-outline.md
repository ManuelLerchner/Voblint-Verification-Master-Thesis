# Thesis presentation outline

Working title: **Voblint: Verifying a Context-Sensitive Abstract Interpreter**

Target: **20 minutes, excluding questions**, 26 main slides planned at exactly 20:00. Audience: computer-science students and
examiners who know programming but not necessarily abstract interpretation,
Isabelle, or proof assistants.

This replaces the first text-heavy draft. The slides should rely on figures, so
each slide carries at least one figure, often two. On-slide text is at most the
title, which states the slide's claim, plus one line. The argument lives in the
speaker notes.

## What the audience should take away

1. Machines now check large proofs in mathematics and in industrial software.
   A checker, however, establishes only that the proof proves the statement as
   written. Whether the statement and definitions say what we mean stays a
   human question.
2. A static analyzer answers questions about all runs at once, and analyzers
   have bugs that give confident wrong answers.
3. Calling contexts are what make interprocedural analysis precise, and they
   also make its soundness proof hard.
4. Voblint proves soundness as a chain of set inclusions from source executions
   to the analyzer's report, and it names exactly what stays outside the proof.
5. The analyzer runs (in the browser), it is precise on examples, and it was
   expensive to build, with substantial AI assistance.

Point 1 is the frame for the whole talk. The trust-boundary slide (14) answers
it for Voblint.

## Narrative

The opening follows the thesis introduction (wrong answers from analyzers,
machine-checked proofs, the kernel checking only against definitions, Goblint's
modular architecture, the verdicts). The ending follows the thesis conclusion
(relevance to Goblint, limitations, extensions towards C). In between, the
explanation pattern of Tom Wheeler's Temporal introduction: a small example,
complexity that piles up, then the formal answer. The demo is live in the
browser playground; the deck stays a PDF.

| # | Slide | Time | Figure | Source |
| --- | --- | --- | --- | --- |
| 1 | Title | 0:20 | banner | |
| 2 | Tests check some runs | 0:30 | explainer `runs` | thesis §1.1 |
| 3 | Goblint | 0:40 | logo, checked properties | thesis §1.4 |
| 4 | Confident wrong answers | 0:45 | remainder bug | thesis ch. 1, Goblint issue 1156 |
| 5 | Proofs, checked by machines | 0:40 | timeline | see below |
| 6 | The checker checks the proof, not the definitions | 0:50 | checked chain | see below |
| 7 | Goblint's architecture splits the proof | 0:40 | pipeline | thesis §1.3, §1.4 |
| 8 | Four verdicts | 0:35 | playground `clamp` | thesis §1.5.1 |
| 9 | VIMP, a small C | 0:45 | grammar, explainer `island` | thesis §3.1, §3.7 |
| 10 | A question about every run | 0:40 | bump, abstract values | `contexts.vimp` |
| 11 | From the graph to equations | 0:45 | counting loop, equations | thesis ch. 2, site |
| 12 | How many copies of a procedure (4-step build) | 1:00 | context grid | claims `ctx-demo-*` |
| 13 | Why we need a trace semantics (4-step build) | 1:20 | CFG, split graph, flat run, datatype | thesis §4.1, §15.1 |
| 14 | Activation traces on the example (3-step build) | 0:55 | activations, per-context sets | thesis ch. 4 |
| 15 | Five local obligations | 1:05 | obligations, contract diagram | `activation_coverage` |
| 16 | Chain of set inclusions (4-step build) | 0:45 | nested sets | thesis ch. 10 |
| 17 | The end-to-end theorem | 0:50 | generated statement | `run_voblint_source_sound` |
| 18 | What is proved, what is trusted | 0:40 | trust pipeline | site, thesis trust figure |
| 19 | The remainder bug against an obligation | 0:45 | side by side, claim verdicts | `prefix_congruence_mod_unsound` |
| 20 | Parts of the formalization | 0:25 | site treemap | thesis `fig:intro-corpus` |
| 21 | What runs, what holds it up | 0:30 | iceberg | `stat()` |
| 22 | What Voblint supports | 0:40 | domain cards, settings | thesis ch. 11 |
| 23 | Now: the playground | 2:10 | example links | claims, playground |
| 24 | Relevance to Goblint, limits | 0:40 | alignment counts | thesis §15.2 |
| 25 | Outlook | 0:40 | three effort tiers | thesis §15.3 |
| 26 | Conclusion | 0:25 | statement | thesis ch. 15 |

Total 20:00, with no slack. If the demo runs long, move slide 20 or 21 to backup.

## Sources for slides 3 and 4

**Checked** means the primary source was read on the given date; **to check**
means only a lead.

- Kepler conjecture (Flyspeck), HOL Light and Isabelle. **Checked**
  2026-11-28 at [arXiv 1501.02155](https://arxiv.org/abs/1501.02155),
  submitted January 2015.
- Liquid Tensor Experiment, Lean, completed 14 July 2022. **Checked**
  2026-11-28 at the [Lean blog](https://leanprover-community.github.io/blog/posts/lte-final/).
- BB(5) = 47,176,870, Coq. **Checked** 2026-11-28 at
  [arXiv 2509.12337](https://arxiv.org/abs/2509.12337); the slide uses the
  2025 preprint date.
- seL4 (`klein09`) and AWS Nitro (`aws26nitro`): checked in
  `docs/THESIS_READING_NOTES.md`. CompCert (`leroy09`): thesis citation.
- Navier–Stokes with smooth forcing, OpenAI, 8 September 2026, Lean:
  **checked** 2026-09-21 in the reading notes (`openai26ns*`); its review is
  self-assessed.
- Riemann Hypothesis, Lean library released by Levent Alpöge on
  20 November 2026, credited "with Claude" in the cleanup repository. On
  21 November the Lean FRO and the Mathlib Initiative certified that it
  compiles, passes the kernel and independent checkers, and proves Mathlib's
  `RiemannHypothesis`. **Checked** 2026-11-28 at the
  [Lean blog](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)
  and the [repository](https://github.com/leanprover-community/riemann-hypothesis).
  Recheck the status the week of the talk.
- [Bastounis, Circelli, Hansen, arXiv 2610.08144](https://arxiv.org/abs/2610.08144)
  (6 October 2026): the slide quotes the abstract, **checked** 2026-11-28.
  Read the paper before discussing its argument.
- Not on the slides until checked: Four Colour Theorem, Feit–Thompson, Fermat's
  Last Theorem in Lean (Anthropic, September 2026), the unforced Navier–Stokes
  result (Buckmaster and Alpöge, 20 November 2026; secondary sources only),
  the Axiom formalizations, AWS Cedar.
