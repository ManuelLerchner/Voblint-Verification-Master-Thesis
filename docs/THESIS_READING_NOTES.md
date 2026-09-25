# Thesis source review

Reviewed on 2026-09-21. Inputs were the browser bookmark export (both the
Thesis folder and research links elsewhere), the sibling
`goblint-formalization-kb` vault, and the primary sources linked below.
The bookmark export contains unrelated personal material and is not copied
into this repository. These notes support the frozen
[thesis blueprint](THESIS_BLUEPRINT.md); they do not propose more chapters.

This is a relevance review of abstracts and selected sections, not a claim to
have read every saved paper in full. Before citing a detailed theorem or
comparison in thesis prose, read the relevant statement and assumptions.
BibTeX keys below refer to `thesis/literature.bib`.

## Sources added to the bibliography

### Analysis architecture and semantic views

- **`seidl26` — Mixed Flow-Sensitive Static Analysis: Engineering Modularity.**
  Read the introduction and the framework sections. Side-effecting constraints
  separate analysis specifications from solving; digests and update rules refine
  different parts of this architecture. Use in Chapters 6–8 and 13 to attribute
  the architectural split. Do not present mixed flow-sensitivity as a Voblint
  invention. [Publisher text](https://doi.org/10.1007/978-3-032-26220-2_22).
- **`schwarz21` — Improving Thread-Modular Abstract Interpretation.**
  Read the introduction and semantic setup. Local traces provide a concrete
  basis for comparing thread-modular analyses. Use in Chapters 4 and 13 to
  explain the origin of the local perspective. Voblint's procedure activations
  require their own semantics and proof; the concurrency results do not transfer
  automatically. [Paper](https://arxiv.org/abs/2108.07613).
- **`schwarz24digest` — The digest framework.**
  Read the introduction and framework setup. Abstract execution histories refine
  which thread observations can interact. Use in Chapters 7 and 13 when comparing
  admissibility and history-sensitive analysis. Keep thread interference separate
  from sequential call/return routing.
  [Publisher text](https://doi.org/10.1007/s10009-024-00773-y).
- **`rival07` — The trace partitioning abstract domain.**
  Read the motivating examples and semantic setup. Partitioning execution
  histories can retain distinctions lost by joining states at a program point.
  Use in Chapters 4, 7, and 13. Compare partitions with Voblint's potentially
  overlapping context relations before making a novelty claim.
  [Author PDF](https://www.di.ens.fr/~rival/papers/toplas07.pdf).
- **`cousot02` — Constructive design of a hierarchy of semantics.**
  Read the abstract and contents from the KB's saved paper. It derives semantic
  views of transition systems by abstraction. Useful background for Chapters 2
  and 4, especially the distinction between executions and collecting semantics.
  TODO: select and read the exact construction before citing a technical result.
  Saved source: `raw/papers/Cousot-TCS-02-v277p47-103-2002.pdf` in the KB.
- **`schwarz25phd` — Thread-Modular Abstract Interpretation: The Local Perspective.**
  Checked the title page and abstract. This extended account connects local
  semantics, relational analyses, and digests. Use as a navigation source for
  Chapters 4 and 13, then read the relevant chapter for each claim.
  [TUM dissertation](https://mediatum.ub.tum.de/doc/1765098/n8cop1l4luxwzq7hmzpv376a6.tmai-local-perspective-schwarz.pdf).

### Solving and termination

- **`seidl21` — Three improvements to the top-down solver.**
  Read the abstract, introduction, and semantic correspondence discussion.
  The paper treats nonmonotone right-hand sides, space usage, and side effects.
  Useful for Chapter 8 and the limits in Chapter 14. Distinguish the algorithms
  discussed here from the particular vendored solver. The journal issue is
  dated 2021; first online publication was in February 2022.
  [Publisher](https://doi.org/10.1017/S0960129521000499).
- **`stade24` — The Top-Down Solver Verified.**
  Read the abstract and verification overview. The proof relates an optimized
  solver to a simpler formulation. Use in Chapter 8 to explain the inherited
  verification line; cite `tilscher26` for the mixed flow-sensitive solver used
  here. [Publisher](https://doi.org/10.1007/978-3-031-65627-9_15).
  The corresponding [AFP entry](https://isa-afp.org/entries/Top_Down_Solver.html)
  is a formal artifact, not another independent result.
- **`erhard25` — Context Gas and friends.**
  Read the introduction, context mechanisms, and finiteness discussion.
  Bounding growth within a domain does not alone bound the number of contexts
  created by an analysis. Use in Chapters 7, 8, and 14 to explain the separate
  context-finiteness problem. This paper does not discharge Voblint's
  per-program termination premise.
  [Paper](https://mediatum.ub.tum.de/doc/1792164/1792164.pdf).
- **`kocal26` — Same Engine, Multiple Gears.**
  Read the abstract and introduction. It compares parallel fixpoint iteration
  at different granularities. Optional future-work reference for Chapter 14;
  Voblint's present proof does not establish a parallel implementation correct.
  The bibliography identifies the extended preprint explicitly.
  [Preprint](https://arxiv.org/abs/2602.06680).

### Verified interpreters and foundations

- **`michelland24` — Abstract Interpreters: A Monadic Approach to Modular Verification.**
  Read the introduction from the KB's saved `raw/papers/monadic_ia.pdf`.
  Monadic structure separates reusable control-flow machinery from semantic
  operations in verified abstract interpreters. A direct modularity comparison
  for Chapters 6 and 13. The venue is PACMPL **ICFP 2024**, not OOPSLA as one
  KB bibliography note states. [Publication](https://doi.org/10.1145/3674646).
- **`blazy13` — Formal Verification of a C Value Analysis Based on Abstract Interpretation.**
  Read the introduction and domain-interface discussion. The CompCert-based
  value analysis combines domain interfaces with validation of computed
  invariants. Use in Chapter 13 to distinguish verification of a solver from
  verification of a result checker. The venue is **SAS 2013**, correcting the
  blueprint's former NFM attribution.
  [Author PDF](https://davidpichardie.github.io/papers/sas13.pdf).
- **`rival20` — Introduction to Static Analysis.**
  Checked the title page and contents of the KB's saved book. Useful for Chapter
  2 and for organizing the comparison of compositional and transition-based
  analysis. Read the relevant sections before citing their technical claims.
  The title page lists Xavier Rival before Kwangkeun Yi.
  [Publisher](https://mitpress.mit.edu/9780262043410/introduction-to-static-analysis/).

### AI-use disclosure

- **`kappelmann26` — Just Type It in Isabelle!**
  Read the abstract and introduction describing the human-guided formalization
  experiments; checked the current arXiv version and author list. Cite as
  methodological inspiration in the development-tooling discussion. It does not validate
  this thesis's definitions or measure this project's productivity.
  [Version 3](https://arxiv.org/abs/2604.15713v3).
- **`autocorrode` — AutoCorrode software repository.**
  Checked the project README and local I/Q documentation. Cite the tooling used
  for interaction with Isabelle separately from the methodological paper.
  [Repository](https://github.com/awslabs/AutoCorrode).

## Existing references and corrections

The bookmark collection also contains sources already represented by
`apinis12`, `jourdan15`, `sotin11`, `schwarz23`, `grass24`, and `nipkow14`.
Repeated arXiv links, publisher/HAL pairs, and duplicate local PDFs do not need
new bibliography entries.

Verasco's paper describes modular abstract-domain interfaces. The blueprint's
former phrase “monolithic proof” was unsupported and has been removed. The
useful comparison is the iterator and semantic architecture, with each
project's modularity described precisely.
[Verasco paper](https://xavierleroy.org/publi/verasco-popl2015.pdf).

The existing `tilscher26` author list agrees with the KB's saved
`td-side-verified.pdf`: Sarah Tilscher, Alexandra Graß, and Helmut Seidl.
Do not import conflicting author lists from wiki summaries.

Checked versions (2026-09-22):

- `cachera05` replaces `cachera04`: Cachera, Jensen, Pichardie and Rusu,
  "Extracting a Data Flow Analyser in Constructive Logic", TCS 342(1):56-78,
  DOI 10.1016/j.tcs.2005.06.004. The journal version was read.
- `sotin11`: the HAL preprint was read, not the Springer version.
- `schwarz26vmcai`: LNCS pp. 309-334, DOI 10.1007/978-3-032-15700-3_15. Only
  the abstract was read.

## How to use the knowledge base

Use the vault to locate primary papers, recover research questions, and follow
links between ideas. Its saved monadic-interpreter paper was especially useful
when the public full-text endpoints were unavailable.

The old thesis structure and project instructions describe earlier IMP2-based
plans and superseded designs. Keep `docs/THESIS_BLUEPRINT.md` as the structural
plan and the current Isabelle development as formal evidence. Meeting notes
record discussions and intentions; they do not establish theorem completion.
No vault files were changed in this review.

The saved paper *Proving Total Correctness of Top-Down Solvers with Widening
and Narrowing* is a relevant follow-up for Chapter 8. Its assumptions must be
read before applying it to this development. TODO: reconcile the publisher's
online and issue dates before adding its final bibliographic record.

## Material kept outside the bibliography for now

- **Exposition examples:** Graß, From, and Rõtov are discussed in blueprint
  Section 11.1. Zimmerer's numerical-integration bachelor's thesis is another
  possible presentation example; only its title and scope were checked.
- **Adjacent verification:** FormalSSA, Simpl, Viper/Schwerhoff, CompCert,
  seL4, and the Aeneas/SymCrypt paper may support particular comparisons.
  Their presence in the bookmarks alone does not justify new related-work
  sections. CompCert already has `leroy09`.
- **Broader AI material:** the Munkres autoformalization paper remains a lead.
  Tao and Paulson now support the introduction as documented below; they do
  not establish facts about Voblint.
- **Development aids:** Isabelle manuals, tutorials, graph viewers, Goblint's
  first-analysis guide, and the Lean Hitchhiker's Guide are useful while working.
  Cite an exact version or section only when thesis prose relies on it.
- **Out-of-scope semantics:** relaxed-memory compiler transformations concern
  a different language and execution model. No direct claim is drawn from them.
- **Private chats and generated summaries:** use them as search leads only.
  Unrelated personal bookmarks are excluded.

## Suggested reading order

For the next draft of Chapter 9, first inspect the actual result theorem and
its dependencies; another general literature pass is unnecessary. For related
work, prioritize `seidl26`, `tilscher26`, `michelland24`, `jourdan15`, and
`blazy13`. For the context and termination discussion, prioritize `erhard25`
and `rival07`. The broader sources can wait until a specific paragraph needs
them.

## AI, formal mathematics, and industrial verification

Reviewed 2026-09-21 for the introduction. These sources motivate checked
reasoning; they do not supply evidence for Voblint's theorems.

- **OpenAI, Navier–Stokes (`openai26ns`, `openai26nspaper`,
  `openai26nslean`).** Read the announcement, paper abstract and Theorem 1.1,
  reference list, artifact README, formalization metadata, and comparator
  wrapper. The introduction attributes the release to OpenAI. The theorem
  concerns smooth forcing, initially stationary fluid, and bounded energy.
  The artifact metadata describes its review as self-assessed. We have not
  independently rebuilt Lean or run the comparator. Do not imply prize
  acceptance or independent certification from this source review.
  [Announcement](https://openai.com/index/navier-stokes-solution/),
  [paper](https://cdn.openai.com/pdf/32d9f210-8b73-45e0-91bc-82a30aef8a9a/navier-stokes.pdf),
  [artifact](https://github.com/openai/NavierStokesAndEuler).
- **Fefferman (`feffermanNS`).** Followed the announcement's primary reference
  and read the problem alternatives A–D. C/D permit external forcing. This
  explains the scope qualification in the opening. The upload-directory date
  is not used as a publication year.
  [Problem statement](https://www.claymath.org/wp-content/uploads/2022/06/navierstokes.pdf).
- **Tao (`tao26ai`).** Read the essay's discussion of verification, exposition,
  interpretation, and responsibility, plus its references. Useful for keeping
  proof production distinct from an adequate statement and readable account.
  His living AI-views page is an author-reviewed AI-assisted summary and a
  route to primary sources, not an independent empirical study.
  [Essay](https://arxiv.org/abs/2608.16753),
  [views](https://teorth.github.io/tao-web/ai-views.html).
- **Mathlib (`mathlib2020`).** Read the repository's citation instructions and
  the cited paper's abstract and introduction. The requested 2020 citation
  describes the Lean 3 library; do not use it for contemporary Lean 4 counts.
  Reusable mathematical infrastructure is the relevant connection.
  [Repository](https://github.com/leanprover-community/mathlib4).
- **PFR (`pfr`).** Read the README and CITATION.cff; followed the original
  Marton-conjecture paper. Useful as an example of collaborative formalization
  and its blueprint. The citation file's 2023 release date is not a completion
  date. This project is not evidence that AI originated the mathematical proof.
  [Repository](https://github.com/teorth/pfr).
- **Tao's Analysis I.** Read the README and formalization conventions. Useful
  for mapping textbook exposition to Lean and explaining semantic conventions.
  Exercises deliberately contain `sorry`; do not describe the entire repository
  as a completed proof artifact. No thesis claim currently needs a bibliographic
  entry for it. [Repository](https://github.com/teorth/analysis).
- **Nitro (`aws26nitro`).** Read both Amazon Science articles and the
  whitepaper's proof-stack, specification, and conformance discussion. The
  whitepaper is the thesis citation for implementation refinement and its
  boundary. This is an industrial Isabelle example, not evidence of an
  LLM-generated verification. Avoid transferring its isolation guarantee to
  the full AWS stack.
  [Paulson article](https://www.amazon.science/blog/isabelle-hol-the-proof-assistant-behind-the-nitro-isolation-engine),
  [Mulligan and Chong article](https://www.amazon.science/blog/ec2s-formally-verified-isolation-engine-provides-mathematical-assurance-of-virtual-machine-isolation),
  [whitepaper](https://d1.awsstatic.com/onedam/marketing-channels/website/aws/en_US/whitepapers/compliance/nitro-isolation-engine-whitepaper.pdf).
- **Paulson, Nipkow, and Wenzel (`paulson19`).** Followed the Nitro article's
  scholarly reference and checked the abstract and publisher metadata.
  Useful for the LCF architecture and separating proof search from inference.
  [Article](https://doi.org/10.1007/s00165-019-00492-1).
- **Kleppmann, distributed systems.** Resolved the supplied Hacker News item
  through its API to the original guest article. Read its invariant argument
  over event sequences and distinction between safety and liveness. It is an
  exposition example, not a new AI result; cite the author article if later used.
  [Primary article](https://lawrencecpaulson.github.io/2022/10/12/verifying-distributed-systems-isabelle.html).

The citation search also found Avigad's *Mathematics and the formal turn*
(DOI 10.1090/bull/1832). Its abstract and metadata were checked; full article
review remains a follow-up. Fluid-mechanics references were not added merely
because they occur in the Navier–Stokes paper.

## Velvet and Loom

The [Velvet site](https://velvetprover.dev/) links the
[tool paper](https://verse-lab.org/papers/velvet-cav26.pdf) (`velvet26`) and
[foundational paper](https://verse-lab.org/papers/loom-popl26.pdf) (`loom26`).
Read the tool paper's introduction and Sections 2.1–2.4, and Loom's abstract,
introduction, and semantic overview. Velvet combines contract-based verification
conditions, executable programs, testing, and interactive Lean proofs. Its
comparison with Voblint belongs under verification architecture: supplied
contracts and invariants versus computed abstract summaries.

The tool paper explicitly says that its current SMT results are trusted;
Lean-SMT reconstruction is possible. Thus, foundational verification-condition
generation does not imply that every automation configuration has the same
trust boundary. The homepage's broad kernel-checking description must not erase
this backend qualification. Neither paper establishes an empirical benefit from
LLMs merely because an AI agent can use the interactive interface.

## Draft integration status

The 2026-09-21 drafting pass populated all fifteen chapters and the five planned
reference appendices. The added engineering chapter follows the author's
explicit request. The main contribution is the Isabelle verification; the
manuscript explains its contracts and important proof insights alongside the
formal artifact rather than rebuilding every proof in prose.

Formal-source review used existing rendered Isabelle sources and exported
statements. The I/Q and I/R endpoints were unavailable. The thesis facts check
queried the built Isabelle session successfully; no Isabelle theories were
modified by this drafting pass. Source/reference checks establish correspondence
of named entities and generated evidence, not correctness of every prose
interpretation. Author and supervisor review remain necessary before submission.

The evaluation distinguishes the 87 selected replayed regression cases from the
289-file corpus inventory. It does not report a new whole-suite benchmark or a
fresh execution of the historical Goblint revision. Personal acknowledgements
remain for the author.

## Bookmark follow-up, 2026-09-22

Second pass over the bookmark export for sources the first review missed.

- **`seidl12compiler` — Compiler Design: Analysis and Transformation.**
  Read Sections 2.2 and 2.5–2.9 of the author's copy. Section 2.2 defines
  concrete `enter` and `combine`; Section 2.6 abstracts them, with a binary
  `combine` of the pre-call value and the callee's exit value. Section 2.8
  sets up unknowns per program point and entry state and solves them on demand
  with a local solver; Section 2.9 gives call strings bounded to depth $d$.
  Cited in Chapter 2 (context designs, demand-driven solving) and Chapter 6
  (binary return). [Publisher](https://doi.org/10.1007/978-3-642-17548-0).
- **`klein09` — seL4: Formal Verification of an OS Kernel.**
  Read the abstract and introduction. The C implementation is proved against an
  abstract specification in Isabelle/HOL; compiler, assembly code, boot code,
  cache management and hardware are assumed correct. Cited in Chapter 1 as an
  Isabelle verification with an explicit trust boundary.
  [Publisher](https://doi.org/10.1145/1629575.1629596).
- **`buchwald16` — Verified Construction of Static Single Assignment Form.**
  Read the AFP abstract (`Formal_SSA`) and the repository README; the paper
  text was not accessible. SSA construction is defined over an abstract CFG
  fixed by a locale, instantiated for a While language, and extracted to OCaml
  through a further instantiation to replace CompCertSSA's unverified
  construction. Cited in Chapters 1 and 13 as an Isabelle precedent for
  generated code inside a verified toolchain.
  [Publisher](https://doi.org/10.1145/2892208.2892211).
- **`paulson26broken` — Broken Proofs and Broken Provers (blog).**
  Read in full. LCF-style systems have a strong soundness record; Isabelle's
  known soundness bugs were in overloaded-definition checks (2005, 2015) and,
  in February 2025, in normalisation by evaluation, which bypasses the kernel.
  Cited in Chapter 2 next to proof by evaluation.
  [Post](https://lawrencecpaulson.github.io/2026/01/15/Broken_proofs.html).
- **`ho26aeneas` — Scaling Verification of Cryptographic Software with Aeneas,
  Rust, and Lean.** Read the abstract. Agents write proofs about SymCrypt's
  Rust code that the Lean kernel checks; formalizing the standards still needs
  expert design and review. arXiv preprint, not peer reviewed. Cited in
  Chapter 1. [Preprint](https://arxiv.org/abs/2609.15648).
- **`mine13` — Abstract Domains for Bit-Level Machine Integer and
  Floating-point Operations.** Read the abstract and introduction. Most numeric
  domains abstract ideal integers; programs relying on wrap-around need
  dedicated domains. Candidate for the unbounded-integer limitation in
  Chapters 3 and 14; not yet cited. Published in EPiC 17 (2013), from the
  WInG 2012 workshop. [Publisher](https://doi.org/10.29007/b63g).
- **`schirmer08simpl` — Simpl (AFP).** Read the AFP abstract. Simpl has
  mutually recursive procedures, local and global variables and unbounded
  nondeterminism, and is parametric in the state space. It is a candidate
  source semantics that the IMP2 argument of `@sec:vimp-vs-c` does not yet
  address; not yet cited.
  [AFP entry](https://isa-afp.org/entries/Simpl.html).

Checked and not added: the SOAP 2024 proceedings contain *When to Stop Going
Down the Rabbit Hole* (doi 10.1145/3652588.3663321), the workshop version
that `erhard25` extends (its introduction lists the additions);
`hal-04628727` is `michelland24`; mediaTUM 1792164 is `erhard25`; arXiv
2108.07613 is `schwarz21`; Springer 978-3-642-19718-5_24 is `sotin11`. Not
relevant: arXiv 2109.05237 (physics-based deep learning), 978-3-642-11970-5_7
(relaxed memory transformations), the numerical-integration thesis. Not
citable publications: repositories (l4v, archive of graph formalizations,
td-verification, now 404), community conventions and cookbook, the Goblint
Zulip upload, and the Isabelle manuals `locales.pdf` and `classes.pdf`, whose
primary papers `ballarin14` and `haftmann07` are cited. The Masaryk thesis
*Integer Abstract Domains* is a student thesis on standard domains already
cited from primary sources. mediaTUM 1782419 could not be identified: the
server blocks automated access.
