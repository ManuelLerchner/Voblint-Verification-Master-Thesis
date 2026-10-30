# Thesis source audit: analyzers, semantics and verification infrastructure

Audit date: 2026-10-28. Read the exact surrounding paragraphs for every assigned
citation occurrence in `output/pdf/source-audit/thesis-citations.json`, including
both comparison tables. Read `thesis/CLAUDE.md` and `thesis/README.md`. No prose,
bibliography, generated material or tracked Isabelle theories changed.

The 12 sources shared with the paper reuse verified evidence from
`paper/reviews/source-audit-analyzers.md`; their thesis occurrences were checked
individually. Locations below are the inventory's snapshot and may move during
concurrent edits. **Supported** concerns the external-source claim, not independent
verification of Voblint's theorem, experiment or implementation.

## Priority corrections

1. `14-related.typ:24,27`: Blanchet03 function handling/nonrecursion is §5.4,
   not §5.3. Inlining is itself context-sensitive handling. Remove the inference
   “therefore need no context policy”; the pinned IKOS documentation even names
   its call-context data structure.
2. `14-related.typ:165` and table caption: a functional context selector is not
   the definition of object sensitivity. Describe Dabrowski's generic policy.
3. `14-related.typ:211`: Michelland derives two interpreters from a shared
   denotation; “sharing one interpreter” misstates the construction.
4. `14-related.typ:218`: the collective negatives about no extracted analyzer
   and no caller-chain semantics are not established by the cited AFP abstracts.
   Prefer specific positive comparisons, particularly for Wasserrab's slicing
   preservation theorem. Breitner even includes computability theories.
5. `03-program-model.typ:196`: determinism does not imply absence of input.
   State that IMP2 lacks a nondeterministic input constructor. The shallow
   syntax is awkward for the intended analyzer, not impossible to adapt.
6. `15-conclusion.typ:180`: the cited C infrastructure does not establish absence
   of a “commonly accepted C11 semantics”. State VIMP's missing translation and
   the concrete limitations of candidate semantics.
7. `appendix-tooling.typ:85`: CPDT demonstrates dependent heterogeneous lists,
   not impossibility of heterogeneous encodings in HOL. Narrow the claim.
8. Comparison tables combine axes with different meanings: recursion covered
   vs calls interpreted exactly; object sensitivity vs functional policies;
   generic solver vs verified syntax-directed fixpoint computation; executable
   demonstration vs absence of extraction. These distinctions cannot support
   the broad novelty negatives without more precise definitions.

## Per-source findings and occurrence inventory

### `blazy13` — Supported prose; qualify table boundary

Occurrences: `thesis/content/14-related.typ`:122,125,159.

Primary source: [blazy13](https://davidpichardie.github.io/papers/sas13.pdf).

§4 (PDF pp. 11–12) explicitly validates untrusted OCaml results and falls back to top on rejection. §2 (PDF pp. 4–5) uses CFG, a Cminor-derived language; the experimental inlining pass was adapted from RTL but its correctness proof was left for future work. Table labels checked/executable/intraprocedural are supported. Recursive CFG execution is included in the language-level semantics, but the table must not imply a verified interprocedural inlining pipeline. Add the CFG trust limitation if claiming source-to-executable certification. The claim that a verified solver proof is tied to its algorithm is an interpretation; interfaces can support replacement algorithms, as the next solver paragraph itself explains.

### `jourdan15` — Supported; keep historical scope

Occurrences: `thesis/content/14-related.typ`:110,116,157,347; `thesis/content/01-introduction.typ`:258; `thesis/content/15-conclusion.typ`:20; `thesis/content/02-background.typ`:334; `thesis/content/07-cooperation.typ`:210.

Primary source: [jourdan15](https://davidpichardie.github.io/papers/popl15.pdf).

Abstract and §4 support C99 scope excluding recursion/allocation, structural C#minor iteration, per-call-site reanalysis and recursive-call alarms. §2 explicitly omits an abstraction function; §7 specifies channel-aware transfers assuming channel correctness and threads the first component’s output channel to the second. Thus occurrences in background, cooperation and related work are supported. Introduction and conclusion comparisons are accurate for the named examples but do not establish the general absence-of-prior-work claim. The trust statement concerns the verified analyzer function and its extracted implementation, not every parser/printer/toolchain component.

### `jourdan16phd` — Supported

Occurrences: `thesis/content/14-related.typ`:119.

Primary source: [jourdan16phd](https://jhjourdan.mketjh.fr/thesis_jhjourdan.pdf).

§3.1.2 explicitly says termination is established on paper but not formally; §4.3.1 footnote 13 describes extracted infinite fuel. §1.2.3 also explains why a terminating extracted run consumes only a finite portion, covered by the fuel-parametric theorem. The cited sections support the thesis claim. Metadata: Jacques-Henri Jourdan, Université Paris Diderot (Paris 7), 2016; author copy title/date agree with HAL record.

### `nipkow12` — Supported

Occurrences: `thesis/content/14-related.typ`:199; `thesis/content/02-background.typ`:334.

Primary source: [nipkow12](https://www21.in.tum.de/~nipkow/pubs/itp12.pdf).

§5.2 gives the concretization-only Val-abs interface and explicitly drops alpha. Annotated IMP commands and generic abstract interpretation are supported. The 2012 paper is solely by Nipkow; Klein coauthors the 2014 book. Grouped attribution is understandable, but “Nipkow develops ...; the book with Klein ...” would be exact. The article does not support any broad novelty inference beyond its actual procedure-free language.

### `nipkow14` — Supported section references; table executability needs scope

Occurrences: `thesis/content/12-executable.typ`:79; `thesis/content/abstract.typ`:51; `thesis/content/14-related.typ`:167,199,205,391; `thesis/content/05-domains.typ`:96,480,684,717,873,899,920; `thesis/content/01-introduction.typ`:33; `thesis/content/03-program-model.typ`:369,427,466; `thesis/content/15-conclusion.typ`:21; `thesis/content/appendix-isabelle.typ`:10,36; `thesis/content/02-background.typ`:196,214,237.

Primary source: [nipkow14](https://concrete-semantics.org/concrete-semantics.pdf).

Checked every cited section: §2.3.4 recursion, §7.3 small-step configurations, §9.1.2 progress, Defs. 10.23/10.26 orders/monotonicity, Def. 13.1 complete lattices, Fig. 13.5 concretization, §13.5 generic interpreter and forward evaluation, §13.6 finite association lists with top default/quotient, §13.7 lifting/backward filters, §13.8.1 interval quotient, §13.8.3 inverse interval arithmetic. They support the external claims; Voblint-specific generalizations need local proof evidence. The book makes the interpreter executable in §13.6, so the table’s “in prover” should mean the demonstrated interface, not inability to extract/run code. §13.5.9 explicitly separates logical termination from executable code-generation assumptions. “Computes ... by recursion over command structure” describes Step, while whole-program iteration computes the fixed point.

### `franceschino21` — Supported

Occurrences: `thesis/content/14-related.typ`:171,216.

Primary source: [franceschino21](https://lucas.franceschino.fr/static/abint-draft.pdf).

§1 links the resulting analyzer as a web application; §2’s statement datatype has no procedure calls; §8 is syntax-directed iteration. Supports table and browser claim. The cited author PDF is a prepublication draft with anonymous artifact links; the source nevertheless explicitly reports the web application. The current artifact URL is separate reproducibility evidence. No source-level procedure recursion is introduced by recursive F* implementation functions.

### `cachera05` — Supported narrow claims; qualify exclusivity

Occurrences: `thesis/content/14-related.typ`:142,161,375.

Primary source: [cachera05](https://hal.science/inria-00564611/file/extract-tcs.pdf).

§2.2 (manuscript p. 5) combines one heap abstraction with local/stack abstractions indexed by method and program point, supporting mixed sensitivity and context-insensitivity. §3.2 (pp. 12–13) gives a verified round-robin solver for ordinary monotone inequations over ascending-chain-condition lattices; §2 includes calls/returns, including recursive execution. The external claims and table row are supported. “Only Cachera et al. compute the fixpoint with a verified solver” depends on distinguishing a generic constraint solver from verified syntax-directed iterators, which also compute fixpoints; say “generic inequation solver” to avoid manufacturing an absolute distinction.

### `cachera10` — Supported

Occurrences: `thesis/content/14-related.typ`:163,215.

Primary source: [cachera10](https://davidpichardie.github.io/papers/itp10.pdf).

§3 defines a procedure-free While language; §§1/6 explain the executable Coq abstract interpreter, extraction to OCaml, and syntax-directed widening/narrowing iteration. Supports table and executable claim. Its verified iteration algorithm must not be overlooked when making an unqualified claim that only Cachera2005 verifies fixpoint computation.

### `michelland24` — Needs narrowing

Occurrences: `thesis/content/14-related.typ`:211.

Primary source: [michelland24](https://cambium.inria.fr/~yzakowsk/papers/monadic-ai.pdf).

§1 (p. 257:2), §3/Fig. 5 and §8 derive two interpreters from a shared denotation and compose soundness proofs for effect handlers/control-flow combinators. Replace “sharing one interpreter between the concrete and abstract semantics” with “deriving concrete and abstract interpreters from a shared denotation”. The combined attribution to Keidel and Darais needs their separate audit. Metadata matches the paper’s own author order (Michelland, Zakowski, Gonnord); add article 257/28 pages if completing the entry.

### `dabrowski09` — Supported prose; table definition wrong

Occurrences: `thesis/content/14-related.typ`:165,376,382.

Primary source: [dabrowski09](https://davidpichardie.github.io/papers/tphols09.pdf).

§4/Fig. 6 defines a generic CONTEXT interface with method/pointer contexts and make_call_context, accepting caller method/site/context and receiver pointer-context. §7 explicitly says the logical constraints are non-executable. The mixed-sensitivity and non-executable prose is supported. The table caption’s definition of “object-sensitive” as “computes contexts by a function” is wrong: functional context selection is more general. Use “functional policy” for this interface, or describe a particular object-sensitive instantiation. “Closest precedent” is the author’s judgment. A function selecting one context per concrete call does not imply that an abstract call state always has only one possible callee/context.

### `lammich07afp` — Supported positive claim; negatives unverified

Occurrences: `thesis/content/14-related.typ`:169,218.

Primary source: [lammich07afp](https://isa-afp.org/entries/Program-Conflict-Analysis.html).

The official entry proves soundness and precision for conflict analysis with procedures, thread creation and monitors, using a flowgraph model with nondeterministic branching and exact call/return behavior. This supports prior mechanized interprocedural analysis and the table’s model-relative “exact”. The entry does not establish the table’s full “one summary per procedure / specified / no executable” classification, nor the prose’s universal absence of caller-chain representations. Mark these unverified or replace with the positively documented result. Do not infer absence from silence in an AFP abstract.

### `breitner10afp` — Supported positive claim; negative comparison unverified

Occurrences: `thesis/content/14-related.typ`:218.

Primary source: [breitner10afp](https://isa-afp.org/entries/Shivers-CFA.html).

The official entry formalizes Shivers’ algorithms/proofs in HOLCF for safe functional-program control-flow approximation. This supports prior mechanized analysis; clarify HOLCF if useful. The entry includes Computability and AbsCFComp theories, so its abstract alone cannot establish “no extracted analyzer”. Neither does it prove absence of any caller-chain-equivalent representation. Narrow the comparison to the documented language/analysis objective, or inspect the full development before asserting these negatives.

### `wasserrab09afp` — Supported positive claim; preserve distinct objective

Occurrences: `thesis/content/14-related.typ`:218.

Primary source: [wasserrab09afp](https://isa-afp.org/entries/HRB-Slicing.html).

Official entry and published FundamentalProperty theory prove HRB static interprocedural slicing correct via weak simulation and preservation of values used at the criterion along valid paths. A While-with-procedures instantiation is documented. It is valid prior interprocedural verification, but not the same theorem as abstract-state coverage. Current shared sentence asserts no extraction and no caller-chain semantics for three entries without sufficient evidence. Replace the collective negative with the specific slicing objective, or remove this peripheral comparison. Actual theorem checked: <https://isa-afp.org/browser_info/current/AFP/HRB-Slicing/FundamentalProperty.html>.

### `compcertKildall` — Supported, slight overstatement

Occurrences: `thesis/content/14-related.typ`:238.

Primary source: [compcertKildall](https://compcert.org/doc/html/compcert.backend.Kildall.html).

DATAFLOW_SOLVER exposes fixpoint together with fixpoint_solution, fixpoint_entry and fixpoint_invariant. The modular-interface claim is supported. Clients rely on more than just the literal post-fixpoint property: entry coverage and invariant preservation are also exported. Prefer “specified properties of the result” over “only on fixpoint properties”. The page is live documentation; record a revision if exact implementation/version matters.

### `leroy09` — Supported with standard theorem qualifications

Occurrences: `thesis/content/14-related.typ`:98,103; `thesis/content/01-introduction.typ`:257; `thesis/content/03-program-model.typ`:773,885.

Primary source: [leroy09](https://xavierleroy.org/publi/compcert-CACM.pdf).

Abstract/§3 describe the historical Clight-to-PowerPC compiler and extraction; §4.3 shows simulations; §5 lists the semantics, parser, assembler/linker and extraction/Caml stack as trusted. Claims match the 2009 version. Semantic preservation applies when compilation succeeds and the source behavior is defined; avoid an unconditional statement about arbitrary C execution. “Analyzer soundness is weaker than compiler correctness” is an informal comparison of different specifications, not a theorem supplied by this source. Better explain overapproximation directly. The source does not itself establish VIMP adequacy or the absence of alternative semantics.

### `klein09` — Supported

Occurrences: `thesis/content/01-introduction.typ`:49.

Primary source: [klein09](https://isabelle.in.tum.de/~kleing/papers/sosp09.pdf).

§§4.4–4.5 (PDF pp. 7–8) give C-to-abstract refinement and explicitly list compiler, assembly, hardware, boot/initialization, cache/TLB treatment and C99-model adequacy assumptions. The introduction accurately summarizes the 2009 result. Metadata title, author list, SOSP2009 pp. 207–220 and DOI match. Scope the description historically, since subsequent seL4 work strengthened parts of the verification stack.

### `schirmer08simpl` — Supported syntax comparison; avoid impossibility wording

Occurrences: `thesis/content/03-program-model.typ`:203,884.

Primary source: [schirmer08simpl](https://isa-afp.org/entries/Simpl.html).

Published Language theory defines Basic as a state function, Spec as a state relation, conditions as state sets, primitive Call and derived call with initialization/return handling. This supports the shallow-embedding comparison and nondeterministic/parameter features. “Do not allow this” is too broad: semantic embeddings can be reified or restricted; say their existing syntax does not expose an executable operator tag. Official Language HTML was read through curl after web retrieval failed. Metadata: Norbert Schirmer, 29 February 2008, AFP title matches.

### `lammich19imp2` — Supported facts; causal wording needs correction

Occurrences: `thesis/content/03-program-model.typ`:196.

Primary source: [lammich19imp2](https://isa-afp.org/browser_info/current/AFP/IMP2/Syntax.html).

Published Syntax gives Binop (int ⇒ int ⇒ int), PCall pname without arguments/results; Semantics uses a deterministic small-step function. A generic executable equality test cannot identify arbitrary HOL functions. However “deterministic, so it has no input” is not logically valid: deterministic semantics can model an input stream in the state. Say “its syntax has no nondeterministic input command”. Passing parameters through variables is a derived encoding, not a lack of procedure support. Syntax/Semantics were retrieved successfully with curl. AFP metadata Lammich/Wimmer, 15 January 2019 matches.

### `brecknell24autocorres2` — Supported infrastructure; negative C11 claim unverified

Occurrences: `thesis/content/03-program-model.typ`:884; `thesis/content/15-conclusion.typ`:180.

Primary source: [brecknell24autocorres2](https://isa-afp.org/entries/AutoCorres2.html).

AFP documents AutoCorres2 as a C-verification tool and its C parser/translation infrastructure; the published CTranslationInfrastructure contains the Simpl syntax bridge. Thus the suggested comparison target is legitimate. The conclusion’s “no commonly accepted C11 semantics exists in Isabelle” is not established by this entry, which is positive evidence about one tool, not a survey or consensus measure. Narrow to the concrete missing validation: VIMP has not been related to AutoCorres2’s supported C semantics. Entry metadata, 13 authors and April 2024 match.

### `tuong19isabellec` — Does not establish the cited broad negative

Occurrences: `thesis/content/15-conclusion.typ`:180.

Primary source: [tuong19isabellec](https://usr.lmf.cnrs.fr/~wolff/papers/conf/2019-fide-isabelle_c.pdf).

Abstract and §§1/6 describe C11 syntax integrated with Isabelle/PIDE and independently chosen semantic backends/fragments. This supports distinguishing C11 parsing from one comprehensive C11 semantics. It does not establish that no commonly accepted semantics exists. Replace the conclusion’s consensus claim with precise limitations of the candidate semantics and VIMP’s lack of a translation. Metadata: Tuong/Wolff, EPTCS310 pp.13–28, 2019, DOI10.4204/EPTCS.310.3 matches published record.

### `necula02` — Supported cited normalization; local comparison separate

Occurrences: `thesis/content/03-program-model.typ`:874.

Primary source: [necula02](https://people.eecs.berkeley.edu/~necula/Papers/cil_cc02.pdf).

§3 and Fig.4 explicitly separate side-effect-free expressions, instructions including calls, and control-flow statements. Call has an optional destination. Supports the CIL normalization claim. The assertion that every current Goblint edge except two has a VIMP counterpart requires the pinned Goblint source and VIMP definitions, not this 2002 paper; that local correspondence is outside this source audit. Metadata title, four authors, CC2002 pp.213–228 and DOI match.

### `le22` — Supported model claim; table scope needs clarification

Occurrences: `thesis/content/14-related.typ`:22,60.

Primary source: [le22](https://people.mpi-sws.org/~dreyer/papers/finding-real-bugs/paper.pdf).

Intro pp.81:2–3 and Theorem4.1 give underapproximate soundness of the model, explicitly separate implementation false positives. §3.1 assumes nonrecursive procedures; implementation uses bounded unrolling. §4 computes reusable sets of procedure summaries. The table’s “C” understates the evaluated C/C++ scope; “pure conditions” covers only its relational numeric facts, not the spatial ISL heap assertions. “one domain” is an interpretation rather than an explicit architectural exclusion. Keep formal-model versus production-implementation guarantees distinct. Metadata six authors, PACMPL6 OOPSLA1 article81, DOI match.

### `laspina25` — Supported

Occurrences: `thesis/content/14-related.typ`:238.

Primary source: [laspina25](https://link.springer.com/content/pdf/10.1007/978-3-031-91121-7_4.pdf).

§2.2, printed pp.94–95, describes CompCert’s common solver interface and replacing Kildall with verified Bourdoncle strategies without changing client proofs. Supports modularity. Its domains are pseudo-semilattices (upper-bound joins, not necessarily least upper bounds), so do not strengthen solver assumptions casually. Metadata authors, ESOP2025 pp.91–118 and DOI suffix `_4` match; suffix `_5` is a separate artifact description with the same title. Add LNCS15695 if completing metadata.

### `brat14` — Supported inlining; supplement table with pinned documentation

Occurrences: `thesis/content/14-related.typ`:24,58.

Primary source: [brat14](https://jorgenavas.github.io/papers/ikos-sefm14.pdf).

§3, PDF p.5, describes full function-call expansion in the specific buffer-overflow analyzer. It supports the historical inlining claim, not every IKOS configuration. Current pinned README documents APRON wrappers, named reduced products and recursion assumptions (arbitrary memory update, exceptions, initialized returns). It also lists call_context.hpp, so “needs no context policy” is misleading. Prefer “inlining-based call handling” without denying context representation. The table’s “fixed products” is supported as listed configurations, not an impossibility of extending IKOS. Metadata authors/SEFM2014 pp.271–277/DOI match.

### `blanchet03` — Wrong section pointer; broader claim needs narrowing

Occurrences: `thesis/content/14-related.typ`:24,27; `thesis/content/13-evaluation.typ`:550,600,602.

Primary source: [blanchet03](https://www.di.ens.fr/~cousot/COUSOTpapers/publications.www/BlanchetCousotEtAl-PLDI03-USletter.pdf).

Function calls and lack of recursion are in §5.4 (PDF p.4), not §5.3. The source explicitly describes inlining-equivalent handling as context-sensitive/polyvariant, contradicting the inference that inlining needs no context policy. §7.1.2 thresholds, §7.1.3 delayed widening and §7.1.5 delaying branch joins support the evaluation’s technique references. They do not verify the Goblint-specific thresholds/results; those need the experiment. Metadata eight authors, PLDI2003 pp.196–207 and DOI match.

### `mopsa-manual` — Supported, version/date scope needed

Occurrences: `thesis/content/14-related.typ`:28.

Primary source: [mopsa-manual](https://mopsa.gitlab.io/mopsa-analyzer/user-manual/).

Current Overview/Limitations explicitly says no recursive functions for C and Python, and states the intended soundness/termination claims. Supports the recursion limitation. This is maintained documentation, so distinguish what was true on the access date from permanent inability. It does not support the global statement that inlining requires no context policy. Corporate author/title/URL match; no fixed release is recorded.

### `eva-manual` — Supported calls/recursion/APRON; combination claim unverified here

Occurrences: `thesis/content/14-related.typ`:24,27,54.

Primary source: [eva-manual](https://www.frama-c.com/download/frama-c-eva-manual.pdf).

Manual title is Frama-C33.0 Arsenic with the three named authors. §5.3 gives semantic call inlining; §6.3.9 supports contracts plus optional bounded unrolling and warns that inferred fallback specs are not guaranteed correct. §6.7.7 supplies APRON domains. The table’s “contract” should say “unroll/contract” for completeness. “Domains communicate through abstract expression values” was not established by the cited user manual text; cite the architecture paper/source instead. “Sound” is conditional on correct specifications and the analysis assumptions, as the manual states.

### `chlipala13cpdt` — Supported dependent encoding; HOL impossibility unsupported

Occurrences: `thesis/content/appendix-tooling.typ`:85.

Primary source: [chlipala13cpdt](https://adam.chlipala.net/cpdt/cpdt.pdf).

§9.2, pp.169–171, defines heterogeneous lists indexed by a list of types and typed selectors, directly supporting the possible dependent representation. It does not prove that HOL cannot express any heterogeneous structure: records/products, sums and encodings remain possible. Replace “HOL’s simple types cannot” with “HOL does not directly provide this dependent type-indexed representation; this development uses a fixed product”. Metadata author/title/MIT Press2013 correct; live author PDF is a maintained 2019 version, so identify edition if exact pagination matters.

## Metadata and remaining evidence boundaries

The original twelve references have the same bibliographic fields as the paper
except the Franceschino artifact note; no conflicting author/title/year/DOI field
was found. Relevant optional additions remain article numbers and LNCS volumes.
AFP titles/authors/dates were checked against official entries. Do not interpret
these metadata checks as independent reconstruction of every theorem in an AFP
entry.

The pinned IKOS source used for additional evidence is
[analyzer README](https://github.com/NASA-SW-VnV/ikos/blob/ac7f7c1738976cabc58c6a53413df6e458995c38/analyzer/README.md).
Author PDFs and official published HTML were preferred. Some web-renderer fetches
failed (IMP2, Simpl, several PDFs), but direct downloads succeeded and their text
was inspected. seL4 was read through the web PDF after its shell download timed
out. No access failure was silently treated as supporting evidence.

Still unverified: the three AFP developments' collective non-extraction and
caller-chain absence claims; Lammich's exact table classification beyond the
official abstract; Eva's domain-combination mechanism from the user manual;
exclusive “no prior work”/“only one verified solver” claims; the consensus claim
about C11 semantics. These require narrowing or targeted additional evidence,
not an assertion that an inaccessible or silent source agrees.

Repository-specific theorem statements, current Goblint edge correspondence,
precise benchmark outcomes, and the soundness of Voblint's HOL encodings remain
outside this literature audit. No document build is needed for this standalone
Markdown review; prose changes made from it require the usual thesis checks.
