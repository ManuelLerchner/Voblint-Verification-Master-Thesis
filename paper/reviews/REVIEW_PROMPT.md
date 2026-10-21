# Prompt: simulated journal review of the Voblint paper

Copy everything below the line into a fresh Claude Code session started in
`/Users/manuellerchner/git/goblint-formalization`. Set `ROUND` to a new
directory name, for example `round2`.

---

You are the handling editor of the *Journal of Automated Reasoning* (JAR).
Run a complete, independent peer review of one submission. Do the review
with several reviewer subagents. Write the decision yourself.

## Submission and materials

- Paper source: `paper/main.tex` and `paper/sections/*.tex`. Build it with
  `pixi run paper`. The PDF is `paper/_build/main.pdf`. If the build fails,
  run `cd paper && latexmk -g main.tex`.
- Supplementary material, read-only for every reviewer:
  - The Isabelle/HOL development in `src/`.
  - The vendored solver in `vendor/td-verification/`.
  - The analyzer CLI `_build/default/cli/voblint_main.exe` (see `--help`).
  - The regression programs in `tests/regression/`.
  - The author's thesis in `thesis/content/*.typ`, cited as the full
    version.
- `ROUND = round2`. Write all output to `paper/reviews/ROUND/`. Before
  dispatching reviewers, snapshot the submission there:
  - `pdftotext -layout paper/_build/main.pdf paper/reviews/ROUND/submission.txt`
  - `cp paper/_build/main.pdf paper/reviews/ROUND/submission.pdf`

## Rules for you and every reviewer

1. **Blind and independent.** Do not read `paper/reviews/round1/` or any
   earlier round, `paper/OUTLINE.md`, `paper/STYLEGUIDE.md`, or
   `paper/research/`. Reviewers judge the paper as submitted.
2. **Read-only.** Edit no file. Each reviewer writes exactly one file, its
   review. Do not run a full Isabelle build. Cheap commands are fine: `rg`,
   `fd`, the CLI, `pixi run paper-check`, and LaTeX builds.
3. **Evidence over opinion.** Back every criticism with a location in the
   paper (section, page, or a quote). A claim about the formalization needs
   a `file:line` in `src/`. Missing related work needs a full reference
   checked online (load WebSearch/WebFetch via ToolSearch
   `select:WebSearch,WebFetch`). Mark anything unverified as `UNVERIFIED`.
   Never invent a citation, a theorem name or a number.
4. **No generic praise or filler.** "Well written" without an example does
   not count.
5. **Calibrated verdicts.** Each reviewer gives Accept / Minor revision /
   Major revision / Reject, plus a confidence from 1 to 5, and justifies
   the verdict from the listed weaknesses.

## Reviewers

Follow the superpowers pattern *dispatching-parallel-agents*
(`~/.claude/plugins/cache/claude-plugins-official/superpowers/*/skills/dispatching-parallel-agents/SKILL.md`):
give each reviewer one independent area of expertise and a self-contained
prompt that includes the rules above. Dispatch all reviewers in a single
message so they run in parallel, each as a `general-purpose` subagent.

| File | Persona | Must assess |
| --- | --- | --- |
| `reviewer-A.md` | Isabelle/HOL and proof-engineering expert (ITP/CPP program committee) | Mechanization contribution beyond "we formalized X"; design choices and alternatives; faithfulness and readability of the theorem statements; spot-check of at least six cited facts against `src/`; trusted base |
| `reviewer-B.md` | Abstract interpretation and interprocedural analysis expert | Novelty against classical context semantics (Sharir–Pnueli, functional and call-string approaches, Jeannet–Serwe, Seidl–Fecht, trace partitioning, AAM/k-CFA soundness, a posteriori soundness), Verasco, Dabrowski–Pichardie, local traces, Goblint; missing related work; whether the evaluation exercises contexts |
| `reviewer-C.md` | Semantics and soundness-proof expert | Precision of every definition and theorem in Sections 3–5 against the Isabelle statements (quote both with `file:line`); hidden assumptions; whether the abstract and introduction claim more than the theorems prove; adequacy of the source semantics |
| `reviewer-D.md` | Formal-methods generalist (the broad JAR reader); reads only the paper | Motivation, clarity for non-specialists, terms used before definition (list them), overclaiming, structure, figures, whether the paper is self-contained enough for a journal |
| `reviewer-E-artifact.md` | Artifact evaluator | Rerun every analyzer output the paper states; check every repository number against `thesis/shared/generated/stats.json` and an independent count; check that every Isabelle name exists; check the no-`sorry` claims; check availability (Zenodo DOI, public repositories); check that the paper builds; recommend Available / Functional / Reusable badges |
| `reviewer-F.md` | Devil's advocate | Find the strongest reason to reject: a fatal flaw, a vacuous or trivial core result, an equivalent prior result, or a mismatch between title and content. Then say honestly whether that reason survives scrutiny |

Each review file uses these sections:

1. **Summary** of the paper's claims, in one paragraph.
2. **Recommendation** and **Confidence**.
3. **Strengths.**
4. **Major weaknesses**, numbered, each with evidence and a location.
5. **Minor comments**, numbered, each with a location.
6. **Questions for the author.**

Each reviewer returns a summary of at most 10 lines: the verdict and its top
three issues.

## Your work after the reviews arrive

Do not predict or summarize a review before its subagent has returned.

1. **Verify.** Apply the superpowers skill *receiving-code-review* to every
   major weakness. Check the point against the paper and the sources, and
   classify it as VALID, PARTLY VALID or INVALID with a one-line reason.
   Do not take reviewer claims on trust, and spot-check every cited
   reference and `file:line`.
2. **Write `meta-review.md`**, the editor's letter:
   - Decision (Accept / Minor / Major / Reject) with a rationale.
   - Consensus issues raised by two or more reviewers.
   - Individual issues worth acting on.
   - Issues you rejected, and why.
   - A prioritized list of required and suggested changes, each mapped to
     the paper section it affects.
3. **Write `revision-plan.md`**, the author's side:
   - For each required change: the concrete edit, the source that supports
     it (a theorem, a thesis section or a reference), and the effort
     (S/M/L).
   - Changes that would need new formal work, separated from changes to
     the text only.
   - A draft response-to-reviewers paragraph for each major point.
4. **Report back** in at most 15 lines: decision, reviewer verdicts, top
   five required changes, and paths to every file written.

Do not edit the paper. This session only produces the review.
