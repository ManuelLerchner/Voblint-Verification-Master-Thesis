# Paper style guide

Combines the CFPs, the writing guidance and the structure of ~12 published
mechanization papers surveyed in `research/`. Tags: **[V]** checked on an
official page, **[S]** secondary source, **[U]** unverified. The repository
`CLAUDE.md` still governs claim discipline and prose style; this file adds
only what changes when the thesis becomes a paper.

## 1. Thesis vs. paper

| | Thesis | Paper |
| --- | --- | --- |
| Reader | CS reader new to the repository | expert reviewer with 30 minutes |
| Goal | explain the formalization | convince that one idea is new, correct, useful |
| Length | ~200 pp | 16 pp (ITP) / 18–20 pp (LNCS) |
| Background | taught from first principles | cited; at most one page of notation |
| Coverage | every layer | the layers the key idea needs; the rest is one sentence plus a citation of the full version |
| Proofs | proof architecture per chapter | one proof sketch for the central theorem, the rest "mechanized, see `Theory`" |

Rule of thumb: if removing a paragraph does not weaken the contribution list,
remove it.

## 2. Venue format

| Venue | Class | Body limit | Appendix | Review | Artifact |
| --- | --- | --- | --- | --- | --- |
| ITP [V] | `lipics-v2021` | 16 pp excl. refs | **forbidden** | lightweight double-blind | anonymised supplementary material **mandatory** |
| CPP [V] | `acmart` `sigplan,10pt` | 12 pp excl. refs | unlimited, body self-contained | lightweight double-blind | encouraged, uploaded archive (no URL) |
| SAS [V] | LNCS | "no page limit" (recheck) | ? | double-blind + rebuttal | optional AE (VM) |
| VMCAI [V] | LNCS | 20 pp excl. refs | allowed, not read | double-blind | optional AE, may influence decision |
| CAV [S] | LNCS | 18 pp excl. refs, appendices | allowed | anonymised | optional AE |

Expected next deadlines [U]: CAV ≈ late Jan 2027, ITP ≈ Feb 2027, SAS ≈
Apr/May 2027, CPP ≈ Sep 2027, VMCAI ≈ Sep 2027.

Lightweight double-blind means: `anonymous` class option, self-citation in the
third person ("Voblint [Lerchner 2026] proves…" becomes "the Voblint
thesis [X] proves…"), no repository URLs in the body, important background
references kept.

LIPIcs metadata [V]: `\relatedversion` (full version / thesis), `\supplementdetails`
with a Zenodo or Software Heritage DOI, `\ccsdesc`, `\keywords`, and a
**"Declaration about GenAI/LLM use"**. Every ITP 2026 paper checked carries
one. This project used Claude Code and Codex for proofs and prose, so the
declaration must be substantive: what was generated, for which artifacts, and
how humans reviewed it (the thesis `content/ai-use.typ` is the source).

## 3. Structure

Observed in nearly every surveyed paper, and recommended by Peyton Jones and
Dreyer:

1. **Abstract**, 120–200 words, Context → Gap → Innovation → evidence.
   No citations, no Isabelle identifiers.
2. **Introduction**, ≤ 1.5 pp. Problem with a concrete example, the gap, the
   idea, then a bulleted contribution list with forward references. No
   "rest of this paper" paragraph.
3. **Overview / main ideas** section with one running example, before any
   general definition.
4. **Technical sections**, ordered by the argument, not by Isabelle sessions.
5. **Mechanization** section: size, architecture, design choices with the
   alternatives considered, proof-assistant feedback, trust base.
6. **Evaluation**: what each experiment shows and whether it is
   machine-checked, executable, or empirical.
7. **Related work** just before the conclusion, as comparisons, not a list.
8. **Conclusion** with limitations, ≤ 0.5 pp.
9. Data availability and GenAI declaration.

## 4. Contributions

- Each bullet is refutable and points to its section: "We prove that … (§3)".
- Each bullet says what is new and what is inherited. The inherited parts
  (TD solver, side-effecting constraint systems, local traces, D/G
  architecture, widening, reduced product) are named once, together.
- Novelty phrasing: "to our knowledge, no prior mechanization …", backed by
  the related-work search. Never "first" without the qualifier.
- Three to four bullets. Engineering (code generation, playground, regression
  corpus) is evidence, not a contribution.

## 5. Formal content

- Mathematics first, Isabelle second. Pattern from ITP 2026 papers [V]: an
  idea in conventional notation, then one sentence naming the theory and
  constant that mechanize it.
- Theorems in the body are generated from the theories, never retyped
  (`sugar.pdf` [V]: "No typos, no omissions, no sweat"). Show at most three
  verbatim Isabelle statements; the headline theorem is one of them.
- Explain Isabelle notation once in a short paragraph before first use.
  Reviewers reject unfamiliar symbols (`⟦ ⟧ ⟹`) without explanation [V].
- Link theory names to the HTML browser in the camera-ready version only
  (links de-anonymise).
- State partial correctness, scalar language, and trusted components in the
  same paragraph as the headline theorem, not in a later limitations section.
- Report formalization size from `thesis/shared/generated/stats.json`
  (non-blank lines, theories, proofs), with the vendored solver counted
  separately. Proof effort in person-months only if it can be backed.

## 6. Figures

- Budget: 4–6 figures. Each must replace at least half a page of prose.
- Captions are self-contained: what objects, what notation, what the figure
  establishes.
- Reuse thesis figures only after redrawing for the venue width
  (LIPIcs body ≈ 13.5 cm; LNCS ≈ 12.2 cm) and checking grayscale legibility.
- Plots follow the SIGPLAN empirical checklist [V]: no truncated axes,
  distributions not just means, stated platform and repetitions.

## 7. Evaluation discipline

From the SIGPLAN checklist [V], items that apply here:

- Claims explicit and scoped. A precision witness is one program, not a
  dominance result.
- Comparison with Goblint names revision, flags, and what the outputs show.
  Architectural correspondence ≠ operational equivalence.
- Runtime numbers state platform, repetitions, and summary statistic.

## 8. Prose

Repository `CLAUDE.md` rules apply, and so do the author preferences in
`thesis/CLAUDE.md` (no RQ/K labels, citations as support rather than
sentence subjects, motivate before defining, discourse markers). Additional paper-specific rules from
Dreyer [V]:

- Old to new: start sentences with what the reader knows.
- One paragraph, one point.
- One name per concept, fixed in the overview and never varied
  ("activation trace", not "local trace", "call trace", "lineage").
- Just in time: define a notion in the paragraph that first needs it.

Avoid phrasing imported from informal summaries of this work. In particular:

- "stack induction nightmare", "elegantly", "milestone", "blueprint for
  verifying real-world analyzers": unsupported evaluation.
- "the activation trace *is* the context": wrong. A context policy relates
  traces to contexts; one trace may belong to several contexts.
- "fully verified": always give the boundary instead.

## 9. Bibliography

- Every entry checked against Crossref or the publisher page;
  `research/related-papers.md` marks the two unverified LNCS volume numbers.
- AFP entries as `@article{…, journal = {Archive of Formal Proofs},
  note = {\url{…}, Formal proof development}, ISSN = {2150-914x}}` [V].
- Do not cite a paper for a claim without having read the relevant passage.
  Some entries in `research/related-papers.md` are "summary from memory".

## 10. Model paper: Lammich, Isabelle Workshop 2026

Lammich, *Designing a Verification Condition Generator with Eisbach and a bit
of Isabelle/ML: An experience report* (Isabelle Workshop 2026, LIPIcs format,
14 pp,
<https://files.sketis.net/Isabelle_Workshop_2026/Isabelle_2026_paper15.pdf>).
We adopt its style. We copy none of its text.

What it does, and what we take:

| Pattern in the model paper | How we apply it |
| --- | --- |
| Abstract in three short paragraphs: what was built, what reusable pieces came out of it, why they matter beyond this project | Same three moves: the gap and activation traces; the contract, the seams and the end-to-end theorem; what transfers to other verified analyzers |
| One sentence separates this paper from a companion paper ("rather than X, this paper concentrates on Y") | One sentence on the thesis: it holds the full development; the paper covers the semantic idea and how the proof is put together |
| Contribution bullets start with a verb ("We present", "We identify", "We describe", "We discuss") | Rewrite our bullets in that form, keeping the forward references |
| Overview section opens on the actual formal object with its real syntax, then "Here, ... is ..." for every symbol | Show `activation_coverage` or the trace datatype first, then explain each part in the next sentence |
| Each Isabelle listing is followed by a "That is, ..." gloss in plain words | Add a one-sentence gloss after each generated snippet |
| Every non-standard combinator is defined in the sentence after its first use | Same for `caller_of`, `admits_call_context`, `combine`, `part_post_solution` |
| Candid design notes: "a rather arbitrary design decision", "we experimented with ..., the problem was ..., we decided against" | Say which choices were forced and which were arbitrary; report the inlined-call prototype and why we dropped it |
| Limitations sit next to the feature they concern: "Currently ... works as long as ...; it will most likely not work with ..." | Move the caveats for the entry-state policy, termination and routing into the sections that introduce them |
| "We leave it to future work to ..." at the point where the gap shows | Same, instead of collecting all future work at the end |
| Short "User interface" subsections: how someone actually uses the artifact | One paragraph on how a user runs the analyzer and reads verdicts, and on how a domain author adds a domain (what they must prove) |
| Closing catalogue of reusable tools and patterns, each with a "(cf. Section n)" back-reference | A short "Reusable patterns" section: solver as a locale parameter, relational context policy plus a totality obligation, two-default quotient state, generated statements in the paper |
| Plain, first-person-plural, modest voice: no "novel", no "elegant"; claims kept to what was built | Already our rule (§8); keep it |
| Real code listings with line numbers | Our snippets come from the theories and stay generated (§5); add line numbers when the gloss refers to a line |

What we do not take:

- The *experience report* framing. That genre fits the Isabelle Workshop.
  For ITP or a journal, the paper stays a research paper with a theorem.
  Choosing the Isabelle Workshop as the venue would make the framing
  available, at the cost of the archival weight of a main venue.
- Method-level proof-engineering detail. Our contribution is semantic. We
  show proof scripts only where a design choice depends on them.

## 11. Model paper: Zhao, Isabelle Workshop 2026

Zhao, *Mechanising Local Rely-Guarantee Reasoning over the seL4 Trace Monad*
(Isabelle Workshop 2026, 17 pp,
<https://files.sketis.net/Isabelle_Workshop_2026/Isabelle_2026_paper14.pdf>).
Its situation is close to ours: it mechanizes a trace-based theory adapted
from earlier paper work. It handles credit and status in a way that answers
the round-1 reviewers' novelty criticism, so we adopt those parts of its
style. We copy none of its text.

| Pattern in the model paper | How we apply it |
| --- | --- |
| The abstract states the choice of theory and why it fits ("we follow X because ..."), then lists what the development has with (i), (ii), (iii) | "We adapt Schwarz et al.'s local traces to activations because a return must resume its creating caller"; then (i) contract, (ii) routed equations and certificate, (iii) end-to-end theorem about the exported analyzer |
| Every section opens by naming its ingredients and their origin: "the first two are adopted from [8, 26] …; the third, which we introduce to adapt …" | Open Sections 3–5 the same way: valid traces adapted from local traces [schwarz21]; context policies from call strings and entry states [sharir81]; the totality obligation and the relational policy are ours; the certificate is from [tilscher26] |
| A background figure marks which primitives are upstream and which are "introduced in this paper" | Mark in Figure 2 (the seams) and in the overview which parts are inherited (solver, constraint systems, D/G split) and which are ours |
| Definitions in conventional mathematics, each followed by a one-line gloss of what it buys | Same for valid traces, `activation_context_rel`, the five obligations |
| Numbered lemmas, each with a one-line statement, a one-line reading, and "we use this to prove … in § n" | State the supporting facts (`node_collect_eq_Union_activation_collect`, `live_unknowns_cover`, `source_run_has_activation_trace`) this way and say which theorem consumes each |
| A coverage table: one row per construct, listing the premises it needs | A table with one row per obligation (Init … Total) and the equation part or routing condition that discharges it. It also answers reviewer 3's request to show Theorem 2's hypotheses |
| A short "Outline." paragraph at the end of the introduction | Allowed here. The workshop style uses it, and it helps a journal reader. Keep it to two or three lines and do not repeat the contribution list |
| Related work grouped by line, then a closing paragraph "Differences from prior work" | Add that closing paragraph: what we inherit, and the one combination that is ours |
| The conclusion has a "Mechanisation scale" table with lines per component and "All entries are sorry-free" | Per-layer line table generated from the repository (the reviewers asked for per-layer effort data), and the sorry-free claim scoped to the theories actually imported |
| Honest status: "This is a first step …; coverage is still modest" | Say this plainly about the scalar language and the single per-node guarantee |
| Next steps as short titled paragraphs, each naming the concrete obstacle and a possible route | "Per-context certification", "Memory and the caller-locals assumption", "Termination" |

Combined with §10, the paper's voice is plain first-person plural. Each
construction comes with its origin and its reason. The formal object comes
first and a gloss follows it. Limitations sit where they apply. The paper
closes on scale and concrete next steps.
