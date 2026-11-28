# Thesis presentation outline

Working title: **Voblint: Verifying a Context-Sensitive Abstract Interpreter**

Target: **20 minutes, excluding questions**, 17 main slides planned at 18:00,
leaving two minutes for the demo and pauses. Audience: computer-science students and
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

The talk follows the explanation pattern of Tom Wheeler's Temporal
introduction: start from why the tool has to exist, give a small relatable
example, let the complexity pile up ("how hard could it be?"), show the failure
the extra machinery still misses ("is it correct now? No."), name the concept
by comparing the ordinary and the new approach side by side, separate what the
user sees from what holds it up ("above and below the line"), then demo.

| # | Slide | Time | Figure | Source status |
| --- | --- | --- | --- | --- |
| 1 | Title | 0:20 | logo | |
| 2 | Tests check some runs | 1:00 | explainer `runs` | thesis figure |
| 3 | Machines now check large proofs | 1:00 | timeline (new) | see below |
| 4 | The checker checks the proof, not the question | 1:15 | checked chain (new) | see below |
| 5 | A question about every run | 1:00 | bump program, abstract values (new) | `contexts.vimp` |
| 6 | Merging calls loses precision | 1:10 | playground `contexts` crops | playground manifest |
| 7 | Infinitely many contexts | 0:45 | explainer `infinite` | thesis figure |
| 8 | Is it correct now? No. | 1:00 | remainder bug (new) | Goblint issue 1156, PR 1161 |
| 9 | The same bug, with a proof obligation | 1:15 | side by side (new), claim verdicts | `prefix_congruence_mod_unsound`, claims `goblint-1161-*` |
| 10 | Soundness is a chain of set inclusions | 1:30 | checklist build, nested sets (new) | chapter 10 |
| 11 | What you see, and what holds it up | 1:00 | playground `clamp`, explainer `metro` | thesis figures |
| 12 | What is trusted, not proved | 1:10 | checked chain, explainer `island` | chapters 1, 3, 12 |
| 13 | The proved analyzer runs in your browser | 2:30 | explainer `build`, live demo | chapter 12 |
| 14 | Watching the solver work | 0:50 | playground `solve-replay-still` | playground manifest |
| 15 | Combining domains proves more | 0:45 | playground `int-refinement` | playground manifest |
| 16 | What it took | 0:50 | explainer `strata` | thesis figure |
| 17 | So what is Voblint? | 0:40 | statement | |

Total 18:00; the remaining two minutes absorb the live demo.

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

## Backup slides

Built: the inherited/new split. Candidates for more:

- Headline theorem, generated with `proved(...)`.
- Why TOTAL is necessary: the machine-checked counterexample.
- Context precision versus cost: `ctx-nest-k1` and `ctx-nest-k2` claims, and the
  explainer cost charts.
- Machine-integer follow-up (PR #357), at a pinned revision.
- Related work: the explainer paper timeline (1977 to 2026, adapt) and the
  inherited/new split (Goblint, Schwarz et al. 2021, Tilscher, Graß and Seidl
  2026).
