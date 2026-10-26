# Venue rules and writing conventions for a paper from the Voblint thesis

Research date: 2026-10-21. Legend: **[V]** verified on an official page fetched during this session (URL given); **[S]** taken from a search snippet or mirror, not from the official page; **[U]** unverified, check before relying on it.

Today is 2026-10-21. Several 2026/2027 deadlines have already passed (CPP 2027, VMCAI 2027, ETAPS 2027, OOPSLA 2027 R1). Dates below show the yearly rhythm; the next open slots are listed in section 1.10.

---

## 1. Venue rules

### 1.1 ITP 2026 (LIPIcs, at FLoC 2026, Lisbon)  [V]

Source: <https://itp-conference-2026.github.io/cfp.html> (also the CFP mail at <http://www.mail-archive.com/hol-info@lists.sourceforge.net/msg06781.html>)

- Categories: regular papers and short papers.
- Regular: "no more than 16 pages in length excluding bibliographic references". **No appendix.**
- Short: "no more than 6 pages ... excluding bibliographic references and may consist of an extended abstract", with "Short paper" as a subtitle, no appendix, published in the main proceedings, presented as short talks. Meant for "interesting work that is still ongoing and not fully mature".
- Template: LaTeX with `lipics-v2021` (v2021.1.3). Submitted as PDF.
- Review: lightweight double-blind for both categories. Use the class's `anonymous` option. Cite your own work in the third person. Do not omit or anonymize important background references. Posting drafts online and giving talks are allowed.
- **Supplementary material is mandatory**: "anonymised supplementary material containing verifiable evidence of a suitable implementation", e.g. the formalization's source files.
- Dates: abstract 12 Feb 2026, paper 19 Feb 2026, notification 26 Apr 2026, camera-ready 24 May 2026, conference 26–29 Jul 2026. Earlier years: deadlines fall in Feb–Mar.
- Topics include "formalizations of computational models" and "proof pearls". The CFP gives no separate proof-pearl rules and no review criteria.
- No artifact-evaluation track. The mandatory supplementary material takes its place.
- History: ITP 2023 and 2024 used 16 pp + no appendix too [S] (<https://mizar.uwb.edu.pl/ITP2023/cfp.html>, <https://viam.science.tsu.ge/itp2024/cfp>). ITP 2025 introduced lightweight double-blind review [S].
- ITP 2027: no CFP found. [U]

LIPIcs metadata (series page <https://drops.dagstuhl.de/entities/series/LIPIcs>, author instructions <https://submission.dagstuhl.de/styles/instructions/lipics>) [V]:

- `\relatedversion` is mandatory when a related version exists (full version, e.g. arXiv), with a persistent URL.
- Use `\supplementdetails` for code and data, with a category such as "Software" plus a free subcategory such as "Source Code". Prefer archival hosting (Zenodo, Software Heritage). `swhid` is optional. ITP 2026 papers fill this with Zenodo or AFP links, e.g. "Software (Formalized proof): <https://isa-afp.org/entries/>..." (LIPIcs.ITP.2026.3).
- Mandatory macros: `\title`, `\author`, `\authorrunning`, `\Copyright`, `\ccsdesc`, `\keywords`, plus the abstract.
- GenAI: see section 3.6. In practice every ITP 2026 paper we checked has a front-matter field "Declaration about GenAI/LLM use".

### 1.2 CPP 2027 (ACM SIGPLAN, co-located with POPL 2027, Mexico City)  [V]

Source: <https://popl27.sigplan.org/home/CPP-2027> (CPP 2026: <https://popl26.sigplan.org/home/CPP-2026>)

- Length: "should not exceed 12 pages, including tables and figures", excluding the bibliography and clearly marked appendices. The paper must be "self-contained without the appendices". "Shorter papers are welcome and will be given equal consideration."
- Template: `\documentclass[sigplan,10pt,anonymous,review]{acmart}`.
- Review: lightweight double-blind. Rules as for ITP (third-person self-citation, keep important background references).
- Supplementary material (proof scripts, data) is "strongly encouraged". Upload it at submission time as an archive, **not a URL**. Reviewers see anonymous material from the start and non-anonymous material only after first-round reviews.
- No formal artifact-evaluation track on the page.
- Dates (CPP 2027): abstract 3 Sep 2026, paper 10 Sep 2026, notification 10 Nov 2026, camera-ready 25 Nov 2026, conference 11–12 Jan 2027. **Rhythm: deadline in early-to-mid September, conference in January with POPL.** CPP 2028 should therefore have a deadline around Sep 2027. [U]
- No separate paper tracks. About 10% of papers receive a Distinguished Paper award.
- **Review guidance for formalization papers (verbatim from the CFP):** authors should
  - "Thoroughly discuss the theory or design choices underpinning the formalization."
  - "Provide a detailed explanation of the formalization decisions, including alternative approaches"
  - "Examine related literature on formalization choices and techniques."
  - "Compare the design choices to those made in other libraries."
  - "Offer feedback on the features of the computer proof assistant used, noting any that are missing."
  - "Draw conclusions that can guide future formalization efforts in the same or other proof assistants."
- AI: CPP follows the ACM policy. Authors take "responsibility for the veracity and correctness of all material". The work must not be "primarily the result of the tool's generative capabilities". Violations may lead to desk rejection.
- Under high review load, papers with two negative reviews may be rejected early.
- CPP 2026 is Gold Open Access with authors keeping copyright under a CC license (CC-BY recommended). [V, CPP 2026 page]

### 1.3 SAS 2026 (Springer LNCS, at SPLASH/ISSTA 2026, Oakland)  [V]

Source: <https://conf.researchr.org/home/splash-issta-2026/sas-2026> ; announcement <https://www.sigplan.org/announce/2026-03-17-sas-2026/>

- Page limit: the page says "We do not impose a page limit for submitted papers", and regular and NEAT papers share the same limits. **Surprising; recheck before submitting.** [V as quoted, U whether the page is final]
- Template: Springer LNCS proceedings templates.
- Categories: Regular papers, double-blind with rebuttal, judged on significance, relevance, correctness, originality and clarity. **NEAT** papers (New questions/areas, Experience/industrial reports, Announcements, Tool papers) are single-blind and titled "NEAT: <title>".
- Artifacts: optional, evaluated concurrently with review, submitted as a VM image. No badges mentioned.
- Dates (2026): registration 1 May, paper 7 May, artifact 8 May, rebuttal 16–19 Jun, notification 4 Jul, camera-ready 20 Jul. Conference 6–8 Oct 2026. **Rhythm: deadline in late April or early May, conference in October.**
- 2026 special topics: Static Analysis and AI, Static Analysis and Education.
- No AI-authorship policy on the page. Springer's policy applies (section 3.6).

### 1.4 VMCAI 2027 (Springer LNCS, co-located with POPL 2027)  [V]

Source: <https://conf.researchr.org/home/VMCAI-2027>

- Regular 20 pp, tool 12 pp, case study 20 pp, **all excluding references**. A clearly marked appendix may follow the references. It does not count against the limit, and reviewers need not read it.
- LNCS. Regular papers are double-blind.
- Artifacts: "optional, but highly encouraged". AE is single-blind and runs alongside paper review, and "its outcome may influence the final acceptance decision". Artifacts must pass a smoke test.
- Dates: paper registration 23 Sep 2026, submission 30 Sep 2026 (one mirror says 16 Sep [S]), notification 6 Nov 2026, conference Jan 2027. **Rhythm: deadline in late September.**
- Regular papers must "identify and justify an advance" in verification, abstract interpretation or model checking.

### 1.5 ETAPS 2027: ESOP and TACAS (Copenhagen, Apr 2027)  [V]

Source: <https://etaps.org/2027/cfp>

- ESOP: regular research papers at most 25 pp, experience reports and "fresh perspectives" papers at most 15 pp, all **excluding the bibliography**. "There is no page limit at the submission time." ESOP may be submitted in formats other than LNCS. Two rounds: R1 submission 28 May 2026, R2 submission 15 Oct 2026.
- TACAS: regular research, case-study and regular tool papers at most 18 pp plus an optional appendix. Tool demonstration papers at most 6 pp plus an optional appendix. LNCS (`llncs.cls`). Artifacts are **mandatory for tool papers** (deadline 29 Oct 2026) and voluntary for research papers. At most 5 submissions per author.
- ETAPS conferences review double-blind (for TACAS, regular research papers only). Non-compliance may lead to desk rejection.
- Gold OA under CC-BY, and authors keep copyright.
- Voluntary AE runs after acceptance (Jan 2027) and does not affect the decision.
- No AI policy on the page. Springer's policy applies.

### 1.6 CAV 2026 (LNCS)  [S]

Sources: <https://www.sigplan.org/announce/2025-11-21-cav-2026/> , <https://conferences.i-cav.org/2026/artifacts>

- Regular 18 pp, anonymized. Short tool, short application and industrial experience/case-study papers 10 pp each. Limits exclude references and appendices. LNCS.
- Deadline 28 Jan 2026. Two-stage review with early rejections around 4 Mar 2026.
- 2026 artifacts were optional, encouraged for tool papers, and did not affect decisions. Badges: Available, Functional, Reusable.
- The Isabelle TD-solver paper (Stade, Tilscher, Seidl) appeared at CAV 2024, LNCS pp. 303–324, DOI 10.1007/978-3-031-65627-9_15 [V via AFP entry page]. So CAV has accepted Isabelle solver verification closely related to this work.

### 1.7 POPL 2027 / OOPSLA 2027 (PACMPL, acmart `acmsmall`)  [V]

- POPL 2027 (<https://popl27.sigplan.org/track/POPL-2027-popl-research-papers>): "no more than 25 pages of text, excluding bibliography, using the PACMPL format" (`acmart`, `acmsmall`). Appendices go only into supplementary material. **Full double-blind until conditional acceptance.** Mechanized proof scripts are strongly encouraged when proofs are a main contribution. AE is voluntary, runs after conditional acceptance and does not affect the decision. Dates: submission 9 Jul 2026, response 7–10 Sep, notification 5 Oct, revision 26 Oct, final 9 Nov 2026. The paper "must explain its scientific contribution in both general and technical terms". The page also states that "ACM no longer requires disclosure of the use of AI in writing a submission."
- OOPSLA 2027 (<https://2027.splashcon.org/track/splashoopsla2027>): initial submissions at most **23 pp** using the template, excluding required statements, references and supplementary material. Revisions may use up to 25 pp. Template `\documentclass[acmsmall,screen,review,anonymous]{acmart}`. Double-blind until acceptance. Two rounds: R1 14 Oct 2026, **R2 7 Apr 2027**. Major revisions move to the next round. **A Data-Availability Statement before the references is required.** Papers whose claims imply an artifact must explain if none is provided. On AI: authors may use AI tools under the ACM authorship policy. Fabricated references or claims are grounds for desk rejection, and **automated reference checks are run**. Reviewers must not upload submissions to AI services.

### 1.8 Journals

- **LMCS** [V] (<https://lmcs.episciences.org/page/authors-information>): submissions "should not exceed 50 pages", and longer papers need a justification to the editor. Use the journal's own LaTeX style (<https://lmcs.episciences.org/page/authors-latex-style>). **Authors must first post the paper on arXiv/CoRR with TeX sources, with subject cs.LO included.** Usually 2–3 referees. Diamond open access, CC BY 4.0. Anonymity and AI policy are not stated on that page. [U]
- **JAR (Springer)**: the official guidelines page (<https://link.springer.com/journal/10817/submission-guidelines>) blocked automated fetching. Length limit, template (presumably the Springer Nature `sn-jnl` template) and review mode are **[U]**. Springer journals generally require a Data Availability statement and a Competing Interests declaration. [U for JAR specifically]
- **TOPLAS (ACM)**: the author guidelines page (<https://dl.acm.org/journal/toplas/author-guidelines>) blocked fetching. **[U]** The ECOOP 2027 CFP states that under TOPLAS policy an extended version of a conference paper needs "at least 30% new material" [S] (<https://2027.ecoop.org/track/ecoop-2027-technical-papers>). Template `acmart`/`acmsmall` [U].

### 1.9 Summary table

| Venue | Format | Limit (body) | Refs | Appendix | Review | Code/proofs | Typical deadline |
| --- | --- | --- | --- | --- | --- | --- | --- |
| ITP | lipics-v2021 | 16 pp (short 6) | excl. | **forbidden** | lightweight DB | **mandatory** anonymised supp. | Feb |
| CPP | acmart sigplan 10pt | 12 pp | excl. | allowed, unlimited, self-contained body | lightweight DB | encouraged, archive upload | early Sep |
| SAS | LNCS | "no page limit" (recheck) | ? | ? | DB (regular), SB (NEAT) | optional AE, VM | late Apr/May |
| VMCAI | LNCS | 20 pp (tool 12) | excl. | allowed, not read | DB | optional AE, may influence decision | late Sep |
| ESOP | any/LNCS | 25 pp (exp. 15) | excl. | – | DB | voluntary AE post-accept | May (R1) / Oct (R2) |
| TACAS | LNCS | 18 pp (+app.) | excl. | optional | DB (regular) | mandatory for tool papers | mid Oct |
| CAV | LNCS | 18 pp | excl. | excl. | anonymized | optional AE | late Jan [S] |
| POPL | acmsmall | 25 pp | excl. | supplementary only | full DB | voluntary AE post-accept | early Jul |
| OOPSLA | acmsmall | 23 pp (rev. 25) | excl. | supplementary | DB | AE for accepted; DAS required | Oct (R1) / Apr (R2) |
| LMCS | lmcs.cls | ≤50 pp | – | – | not stated | arXiv mandatory | rolling |
| JAR / TOPLAS | Springer / acmsmall | [U] | | | | | rolling |

### 1.10 Next open slots from 2026-10-21 (projected from yearly rhythm; all [U] until the CFPs appear)

- CAV 2027 ≈ late Jan 2027. ITP 2027 ≈ Feb 2027. ESOP 2028 R1 ≈ May 2027. OOPSLA 2027 R2 = 7 Apr 2027 [V]. SAS 2027 ≈ Apr/May 2027. POPL 2028 ≈ Jul 2027. CPP 2028 ≈ Sep 2027. VMCAI 2028 ≈ Sep 2027. Journals accept submissions at any time.

---

## 2. Writing guidance

### 2.1 Simon Peyton Jones, "How to write a great research paper"  [V]

Slides: <https://www.microsoft.com/en-us/research/wp-content/uploads/2016/07/How-to-write-a-great-research-paper.pdf> (talk page: <https://www.microsoft.com/en-us/research/academic-program/write-great-research-paper/>). Read from the extracted slide text.

The seven points, verbatim from the summary slide: 1. Don't wait: write. 2. Identify your key idea. 3. Tell a story. 4. Nail your contributions. 5. Related work: later. 6. Put your readers first (examples). 7. Listen to your readers.

Supporting advice from the slides:

- The paper should have one clear, sharp idea ("one ping").
- Narrative: here is a problem, it is interesting and unsolved, here is my idea, my idea works (details, data), here is how it compares with other approaches.
- Proposed structure: abstract (4 sentences), introduction (1 page), problem (1 page), idea (2 pages), details (5 pages), related work (1–2 pages), conclusion (0.5 page).
- Introduction: describe the problem, state your contributions, "and that is all". Introduce the problem with an example.
- Write the contribution list first, as a bulleted list. Contributions "should be refutable", e.g. "We prove that the type system is sound ... (Section 4)". Forward-reference the evidence for each claim. Avoid a "rest of this paper is structured as follows" paragraph.
- Related work goes at the end, because the reader must know the problem before comparisons make sense. Be generous to competing work and acknowledge your weaknesses.
- Lead with intuition and examples before the general case. "Do not recapitulate your personal journey of discovery."
- Use the active voice and simple, direct language.

### 2.2 Derek Dreyer, "How to Write Papers So People Can Read Them"  [V]

Slides (PLMW@POPL 2016): <https://people.mpi-sws.org/~dreyer/talks/talk-plmw16.pdf>. SIGPLAN's author page links this talk and SPJ's (<https://www.sigplan.org/Resources/Author/>). The talk was given again at PLMW@POPL 2025 (<https://popl25.sigplan.org/details/PLMW-POPL-2025/1/How-to-Write-Papers-So-People-Can-Read-Them>).

The principles, verbatim from the summary slide: **Old to new. One paragraph, one point. Name your baby** (give unique names to things and use them consistently). **Just in time** (give information precisely when needed). **CGI model for abstract/intro** (Context, Gap, Innovation). **Have a "main ideas" section. Compare with related work at the end.**

- Proposed structure: abstract (1–2 paragraphs), intro (1–2 pp), main ideas (2–3 pp), technical meat (4–6 pp), related work (1–2 pp).
- The "main ideas" section uses concrete examples and high-level intuition and does not need to show the general solution. It gives readers a takeaway and serves as scaffolding for the technical sections.
- Related work should give "real comparisons, not a 'laundry list'".
- Dreyer notes that SPJ's "start with a concrete example" introduction "often doesn't work" because it assumes the reader already has the context.
- The talk draws on Williams, *Style: Toward Clarity and Grace*, and Ramsey, "Learn technical writing in two hours per week".

### 2.3 SIGPLAN Empirical Evaluation Checklist  [V]

<https://www.sigplan.org/Resources/EmpiricalEvaluation/> ; categories copied from the source YAML (<https://github.com/SIGPLAN/empirical-evaluation>, checklist/checklist.yml). Current version dated Oct 26, 2018. Committee chaired by Steve Blackburn, with Hauswirth, Berger, Hicks, and Krishnamurthi as external collaborator. Subtitle: "meant to support informed judgement, not supplant it."

1. Clearly Stated Claims: claims not explicit / not appropriately scoped / fails to acknowledge limitations.
2. Suitable Comparison: inappropriate baseline / unfair comparison.
3. Principled Benchmark Choice: inappropriate suite / unjustified non-standard suite / kernels instead of full applications.
4. Adequate Data Analysis: too few trials / inappropriate summary statistics / no data distribution.
5. Relevant Metrics: indirect proxy metric / fails to measure all important effects.
6. Appropriate and Clear Experimental Design: not repeatable / unreasonable platform / ignores key parameters / gated workload generator / tested on training set.
7. Appropriate Presentation of Results: misleading summary / truncated axes / ratios plotted incorrectly / inappropriate precision.

Relevance: the thesis's profiling/scaling and Goblint-comparison evaluation would be reviewed against items 1, 2, 4 and 7.

### 2.4 Isabelle conventions for presenting formalizations

- **LaTeX Sugar for Isabelle Documents** (Haftmann, Klein, Nipkow, Schirmer; shipped as `doc/sugar.pdf`, copy dated Jan 18 2026 in Isabelle2025-2) [V, read locally from /Applications/Isabelle2025-2.app/doc/sugar.pdf]:
  - Generate theorems with antiquotations, e.g. `@{thm[display] ...}`: "No typos, no omissions, no sweat."
  - Import `HOL-Library.LaTeXsugar` and selectively `OptionalSugar` to get "ordinary looking mathematics that hides the fact that it was typeset by a machine".
  - It warns about the "common referee", who refuses unfamiliar notation such as `⟦ ⟧ ⟹`.
  - Techniques covered: `[no_vars]` to remove `?` schematic variables, `mode=Rule` with `mathpartir` for inference rules, `const_typ`, η-expansion control, multiple theorems with `display`.
  - Relevance: the thesis uses Typst with generated `thy(...)`/`proved(...)`. A LaTeX paper would need either an Isabelle document session with Sugar or the same generation pipeline retargeted to LaTeX.
- **Isar Reference Manual, Document Preparation chapter**: the document system is PDF-LaTeX based and can "produce papers, books, theses etc. from Isabelle theory sources" [S] (<https://isabelle.in.tum.de/repos/isabelle/file/34978e1b234f/src/Doc/Isar_Ref/Document_Preparation.thy>).
- **Citing AFP entries** [V] (<https://isa-afp.org/help/>, e.g. <https://isa-afp.org/entries/Top_Down_Solver.html>): use `@article{<Name>-AFP, author, title, journal = {Archive of Formal Proofs}, month, year, note = {\url{https://isa-afp.org/entries/<Name>.html}, Formal proof development}, ISSN = {2150-914x}}`. The AFP entry page in turn lists related publications.
- **Practice in ITP 2026 Isabelle papers** [V, read from PDFs]:
  - LIPIcs.ITP.2026.14 (Certified Infinite Descent) pairs each topic with a "Underlying Mathematical Theory" subsection and an "Isabelle Mechanization" subsection. Theory names in headings link to the HTML browser (`isadoc{Sloped_Graphs}`).
  - LIPIcs.ITP.2026.27 (Fractional Separation Logic in Isabelle LLVM) has a short "Isabelle/HOL Notation" paragraph explaining `'a`, `⇒` and currying before use.
  - LIPIcs.ITP.2026.3 cites the AFP entry as its supplementary material.

### 2.5 What counts as a contribution in a mechanization paper

- No official ITP review criteria were found. The CPP CFP criteria (section 1.2) are the closest official statement. They value design choices with alternatives, comparison with other libraries, feedback on the proof assistant, and lessons that transfer to other formalizations. They say nothing about "we mechanized X" alone.
- The POPL CFP asks the paper to "explain its scientific contribution in both general and technical terms" and encourages mechanized proofs when proofs are central.
- A web search found no authoritative blog or guide specific to ITP/CPP reviewing. [U] Candidate references not fetched: Ringer, Palmskog, Sergey, Gligoric, Tatlock, "QED at Large: A Survey of Engineering of Formally Verified Software" (FnTPL 2019), for proof-engineering vocabulary. [U, not fetched]
- Observed practice (section 2.6): papers report LoC (Verasco: "about 34 000 lines" of Coq plus 6 000 lines of OCaml; real QE CPP 2023: "approximately 8500 lines"; ITP26.14: "~1.3k LOC" for its hardest theory; ITP26.11: per-component LoC). They discuss formalization challenges explicitly ("Formalization Details / Challenges / High Level Proof Techniques / Library Extensions / Code Export" in real QE, CPP 2023) and include case studies or an evaluation.

### 2.6 Example paper structures (fetched and outlines extracted)

Abstract word counts are approximate (pdftotext, may include a few stray words).

| Paper | Venue | Pages | Abstract | Structure | Contributions list | Related work |
| --- | --- | --- | --- | --- | --- | --- |
| Lammich, Fractional Separation Logic in Isabelle LLVM (LIPIcs.ITP.2026.27) | ITP 26 | 18 | ~120 w | Intro; Fractional Separation Algebra; Isabelle LLVM Integration; Automation; Case Study; Conclusion | yes: "In summary, this paper makes the following contributions:" + 4 bullets | inside intro/conclusion, no section |
| Wright et al., Certified Infinite Descent Criteria in Isabelle/HOL (ITP.2026.14) | ITP 26 | 18 | ~160 w | Intro; then per topic "Underlying Mathematical Theory" / "Isabelle Mechanization"; Conclusion | prose | no separate section |
| Yan et al., Automated Verification of Robot Software Models ... Isabelle/HOL (ITP.2026.10) | ITP 26 | 21 | ~160 w | Intro; Background; 3 theory sections; Mechanised analysis in Isabelle/HOL; Case studies and evaluation; Related work; Conclusions | prose ("Our main contribution is ...") | before conclusion |
| B3 VCG formalization (ITP.2026.11, Dafny) | ITP 26 | 19 | ~250 w | Intro; Overview of semantics; VCG + soundness; Implementation/Mechanization (with LoC); Related Work; Conclusion | yes: "In summary, our contributions in this paper are:" | before conclusion |
| Apply2Isar (ITP.2026.18) | ITP 26 | 20 | ~110 w | Intro; Preliminaries; **Motivating Example and Overview**; Implementation Challenges; Evaluation; Future and Related Work; Conclusion | – | before conclusion |
| Lin et al., Don't Sweat Interaction Trees (ITP.2026.16, Rocq) | ITP 26 | 21 | ~170 w | Intro; **Motivating Example**; Language Definition; Main technique; Case Study; Related Work; Conclusion | – | before conclusion |
| Nezamabadi et al., Verified VCG and Verified Compiler for Dafny (arXiv 2512.05262) | CPP 26 | 16 | ~180 w | Intro; Semantics; Verified Compiler; Verified VCG; Putting It All Together; Related Work; Conclusion | yes ("following contributions:") | before conclusion |
| Logical Pinning (arXiv 2509.23229) | CPP 26 | 15 | ~350 w | Intro; **Overview and Key Ideas**; Background; Model; Case Studies; Discussion; Other Related Work; Conclusion; appendices A–C | yes ("Contributions.") | before conclusion; **has Data Availability Statement** |
| Real QE in Isabelle/HOL (arXiv 2209.10978) | CPP 23 | 14 | ~400 w (likely includes keywords) | Intro; Algorithm; **Formalization Details** (Challenges, Proof Techniques, Library Extensions, Code Export); Related Work; Conclusion | numbered "(1) ... (2) ..." in a paragraph | before conclusion; LoC given |
| Verasco (Jourdan et al.) | POPL 15 | 13 | – | Intro; Architecture; ...; Abstract interpreter; State domain; Numerical domains; ...; **Implementation and mechanization** (LoC); **Experimental results**; Related work; Conclusions | prose | near end |
| Michelland, Zakowski, Gonnord, Abstract Interpreters: A Monadic Approach (ICFP 24) | PACMPL | 28 | – | Intro; Background; **A Taste of Our Library**; Design; Implementation; Layered Proof of Soundness; Related Work; Conclusion | – | before conclusion |
| Franceschino, Pichardie, Talpin, Verified Functional Programming of an Abstract Interpreter (SAS 21) | LNCS | 20 | – | ... "This paper makes the following contributions." | yes | – |

Patterns:

- Related work almost always appears as a section just before the conclusion. Short ITP papers sometimes fold it into the introduction.
- Most papers have an overview, "motivating example" or "taste of" section as Section 2 or 3, usually after a short background section.
- An explicit contribution list ("In summary, ... the following contributions:") is common but not universal in ITP.
- Formalization statistics (LoC, hardest part) appear in an "Implementation/Mechanization" or "Formalization Details" section.
- Abstracts run about 100–250 words.

---

## 3. Conventions

### 3.1 Abstract length

- SPJ recommends 4 sentences. Dreyer recommends 1–2 paragraphs following CGI. Observed ITP/CPP abstracts run about 100–250 words. No venue page fetched states a word limit. [U per venue; LIPIcs/ACM may cap metadata abstracts, not checked]

### 3.2 Contribution bullets

- SPJ recommends a refutable bulleted list with section forward references, and no "rest of the paper" paragraph. Common in CPP and in about half of the ITP 2026 papers checked.

### 3.3 Overview / running example

- Dreyer recommends a "main ideas" section. SPJ recommends "use an example to introduce the problem". Observed as "Motivating Example", "Overview and Key Ideas", "A Taste of Our Library" or "Motivating Example and Overview".

### 3.4 Theorem presentation

- LIPIcs environments are marked with ▶ ("▶ Theorem 1 (Soundness of VCG for procedures)"). Isabelle papers typeset generated statements with Sugar, explain notation up front (ITP26.27 "Isabelle/HOL Notation"), link theory names to HTML (ITP26.14) and split math from mechanization (ITP26.14).

### 3.5 Figures

- SPJ: "Find out how to draw pictures, and use them." SIGPLAN: credit third-party figures in the caption. Empirical checklist item 7 covers plots.

### 3.6 AI-use disclosure

- **ACM (CPP, POPL, OOPSLA, TOPLAS):** the POPL 2027 CFP quotes that "ACM no longer requires disclosure of the use of AI in writing a submission" [V via POPL CFP]. Secondary sources say disclosure is still required when AI is used in the research itself (code, analysis, figures) [S] (<https://2027.sigcse-ts.acm.org/info/policies-ai>, <https://recommender-systems.com/news/2026/06/09/acm-new-ai-policy-discussed/>). The ACM policy page itself returned 403. [U for exact wording] Authors remain responsible for all content. OOPSLA desk-rejects fabricated references and runs automated reference checks.
- **LIPIcs / Dagstuhl (ITP)** [V] (<https://drops.dagstuhl.de/docs/gen-ai>):
  - "Any substantive use of Generative AI" must be "fully disclosed", including text generation, data analysis, image creation and interpreting findings. Place it "in a suitable section of the manuscript (e.g., acknowledgments or before the references)".
  - Content: the type and purpose of use and the extent of human review. The tool, version and date are optional.
  - "Minor spelling, grammar, or stylistic corrections ... do not require disclosure." GenAI cannot be listed as an author.
  - ITP 2026 papers all carry a "Declaration about GenAI/LLM use" front-matter field. Examples range from "No GenAI has been used" to "We used Codex and Claude Code to help prove facts about association lists ... all the theorems and lemmas are stated manually" (ITP.2026.16).
  - **Relevance: the repository uses Claude Code for proof and thesis work, so an ITP/LIPIcs paper needs a substantive declaration.**
- **Springer (LNCS: SAS, VMCAI, ESOP, TACAS, CAV; JAR)** [S, quoted from https://www.springer.com/us/editorial-policies/artificial-intelligence--ai-/25428500]:
  - LLMs "do not currently satisfy our authorship criteria".
  - Use "should be properly documented in the Methods section (and if a Methods section is not available, in a suitable alternative part)". Book or proceedings authors document it in the acknowledgements [S].
  - "AI assisted copy editing" needs no declaration.
  - The policy covers the writing process. Springer Nature journals do not permit AI-generated images.

### 3.7 Data availability / artifacts

- OOPSLA 2027 requires a Data-Availability Statement before the references [V]. The CPP 2026 Logical Pinning paper includes one voluntarily.
- LIPIcs uses `\supplementdetails` and prefers archival DOIs (Zenodo, Software Heritage) [V]. ITP requires anonymised supplementary material at submission [V].
- CPP requires an uploaded archive and no URLs [V].
- Springer journals usually require a Data Availability statement [U for JAR].
- Recommended for any venue: cite a Zenodo DOI for the exact Isabelle release + AFP version, plus the AFP entry if one is submitted.

### 3.8 Related-work placement

- SPJ and Dreyer both say: at the end. Observed: a section just before the conclusion in nearly every paper examined.

---

## 4. Fit notes for this thesis (interpretation, not sourced)

- **ITP (16 pp, no appendix, mandatory supplementary material, Isabelle-heavy audience):** a natural home for the D/G framework, activation-trace contract and solver-integration story. The page limit forces one central idea, such as the end-to-end activation_coverage chain. Needs a substantive GenAI declaration.
- **CPP (12 pp + unlimited appendix):** the review criteria reward formalization design choices and lessons, e.g. separate trace/context/routing concerns, locale architecture, code generation of `run_voblint`, the trust boundary. Deadline ≈ Sep 2027.
- **SAS / VMCAI (LNCS, AI audience):** favour the analysis contribution (verified Goblint-style interprocedural analysis with contexts, replayed Goblint unsoundness) over proof engineering. VMCAI artifact evaluation can influence acceptance.
- **CAV:** precedent in the TD solver verification (CAV 2024). 18 pp.
- **POPL/OOPSLA:** require a stronger general PL contribution. OOPSLA R2 (7 Apr 2027) is the nearest PACMPL slot.
- **LMCS / JAR / TOPLAS:** suit the full thesis-scale story. LMCS requires arXiv first. TOPLAS extensions of a conference paper need ≥30% new material [S].
