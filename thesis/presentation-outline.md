# Thesis presentation outline

Working title: **Voblint: Verifying a Context-Sensitive Abstract Interpreter**

Target: **20 minutes, excluding questions**, 25 main slides planned at 19:05. Audience: computer-science students and
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

| # | Slide | Time |
| --- | --- | --- |
| 1 | Voblint | 0:20 |
| 2 | Tests check some runs. An analysis covers all of them. | 0:30 |
| 3 | Goblint: an abstract interpreter for C | 0:35 |
| 4 | But analyzers are programs, and they give confident wrong answers | 0:45 |
| 5 | Fixing one bug does not rule out the next: proofs, checked by machines | 0:40 |
| 6 | The checker checks the proof, not the definitions | 0:50 |
| 7 | Goblint's architecture lets the proof split along its modules | 0:40 |
| 8 | What the user sees: four verdicts | 0:35 |
| 9 | Our language: VIMP, a small C | 0:45 |
| 10 | Calling contexts decide precision | 1:10 |
| 11 | Layer 1: one state per node | 0:40 |
| 12 | Layer 2: one state per (node, context) | 0:40 |
| 13 | Layer 3: a run as a flat list? | 0:40 |
| 14 | Layer 4: activation traces | 0:45 |
| 15 | Activation traces on the example | 0:50 |
| 16 | The proof contract: five local obligations | 1:05 |
| 17 | The end-to-end theorem | 0:50 |
| 18 | Now: the formalization | 1:30 |
| 19 | What is proved, what is trusted | 0:40 |
| 20 | What runs, and what holds it up | 0:30 |
| 21 | What Voblint supports, all covered by the theorem | 0:35 |
| 22 | Now: the playground | 1:50 |
| 23 | Relevance to Goblint, and limits | 0:40 |
| 24 | Outlook: towards C and Goblint | 0:35 |
| 25 | Conclusion | 0:25 |

Total 19:05. Figures and sources are named in each slide's `sources:` line and speaker notes in `presentation/slides.typ`.

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
