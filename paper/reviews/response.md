# Response to reviewers (rounds 1 and 2)

The revision addresses the consensus points of both rounds. We checked every
point against the theories before acting on it. Two points rested on a wrong
diagnosis and are answered below without a change.

## Changes

| Point | Raised by | Change |
| --- | --- | --- |
| The per-context claim exceeds the theorems | R1–R4, B, D, F | New title. Abstract, introduction and §5 now state the guarantee as per program point. §5 cites `context_sound` and says that no theorem certifies an individual context's row. The conclusion names per-context certification as future work |
| The entry-state policy depends on the solution | R1–R3, B, D, F | §4.2 gives the policy (`routed_entry_context_rel`) as a formula, explains why it is not circular, relates it to a posteriori soundness [Might–Manolios], and states that 𝒜 is relative to the analysis under this policy |
| The displayed Return obligation is not the proved one | R1, R3, A, C | §3.3 shows Return as proved: quantified over every procedure and entered store admitted at the call site. The return rule's edge freedom is explained, with `calls_source_unique` for compiled graphs |
| Theorem 2's hypotheses are hidden | R1, R3, R4, C, D | Table 1 lists every hypothesis of `routed_context` and `dg_context_activation`. The proof sentence says which hypothesis discharges which obligation |
| The Theorem 1 proof sketch is thin | R3, C | The proof idea names the caller-chain invariant (`caller_chain_closure`) and both uses of Total |
| The solver bridge glosses over `live_unknowns` | F, C | §4.3 defines the live set, states what `live_unknowns_cover` proves, and qualifies "reaches its result" as structural reachability |
| Classical context semantics is missing | R2, R4, B | New related-work paragraph on Sharir–Pnueli, Knoop–Steffen, Reps et al., Jeannet–Serwe, Van Horn–Might and Might–Manolios, plus a "Differences from prior work" paragraph. The introduction positions the work as the mechanized connection |
| The evaluation does not exercise contexts | R1, R2, R4, B, D | New Table 3: one recursive program under all four context policies, generated from registered claims. The Goblint bug is now presented as domain-level evidence that involves no contexts. The k=2 theorem is restated as a comparison of two solutions computed by `eval` |
| The flavors table cannot be assessed and tests no claim | R2, B, D | Replaced by a two-sentence summary, with a pointer to the thesis for the Goblint comparison |
| The trace hook is missing from the trust boundary | R1, A | §5 text and Figure 3 now show the hook as trusted |
| Undefined notation | R3, R4, C, D | 𝒢, `intra`/`calls`, ℛ/𝒱, entry pair, unit policy, warrowing, update rules and γ with ρ are all defined before use. The Isabelle notation of Theorem 3 is explained |
| VIMP adequacy is incomplete | R3, C | §5 lists the semantic choices: unbounded integers, `x/0 = 0` and `x%0 = x`, both operands of `&&`/`\|\|` evaluated, failed checks continue, locals of `main` unconstrained but callee locals zero, and built-in calls |
| Overstatements | R1, R5, C | "could not have been registered" and "each box is proved without reference to the others" are gone, and "a context function would suffice" is rewritten |
| Runtime units and fixtures | E, R5 | "cases" instead of "runs", and the 369 fixtures are defined as those without their own timeout |
| The frame-stack alternative is missing | R1, R2 | §6 discusses frame stacks with ghost contexts. It also says that only the inlining prototype was actually implemented |
| Per-layer effort data | R1 | Table 2, generated from `scripts/pages_stats.py`, with the generated grammar theory's exclusion stated |
| Data availability is self-contradictory | R5, A, D, E, F | Rewritten. The archive predates the claims used here, a new archive will accompany the final version, and the solver is not yet public |
| §6 reads like project notes | R4 | The linter and agent details are removed. The feedback paragraph keeps the points that apply to Isabelle generally |

## Points not acted on

- **"`Arithmetic_Diagnostics.thy` is missing from its ROOT, so the theory count
  is off by one"** (R1, R5). The theory is already counted: `isar stats` places
  it in `Voblint_CLI`. The 213 versus 212 difference comes from
  `VIMP_Grammar_Generated.thy`, which is generated from
  `manifests/vimp-grammar.yaml` and excluded by the counter, as round-2
  reviewer E observed. We tried adding the theory to the ROOT, and the full
  batch build passed, but we reverted the change because it fixed nothing.
  The paper now states the exclusion.
- **"`pages_stats.py` reports zero solver theories on a clone without the
  submodule"** (R5). `pages_stats.py` already refuses to run in that case
  (lines 359–366).
- **"Make `pixi run paper` re-run the analyzer"** (E). The paper now attributes
  the re-check to `pixi run thesis-claims`, which does re-run it. The paper
  build only renders the stored claim outputs.

## Open, outside the text

- Publishing the vendored solver needs the agreement of its authors.
- A fresh Zenodo archive should be cut once this branch is merged.
- A per-context theorem about `run_voblint` would restore the stronger claim
  (future work, formal effort L).

## Round 3

Two independent round-3 runs (returning reviewers with a new blind reviewer G,
and a fully blind run with its own editor) found no formal error. Below are
the changes, then the points not acted on. Table numbers refer to the revised
paper.

| Point | Raised by | Change |
| --- | --- | --- |
| Congruence attribution | A, E, G | §7 names the obligation `mod_sound` of `sound_arith_ops` and the lemma `congruence_mod_sound` that discharges it for the shipped operator |
| Table 1 incomplete; `post_bounded` understated | A, C, D | Table 1 lists every assumption of both locales, including `cmb_wf`, `extra_wf`, `is_bot_bot`, `sg_cov` and `sg_uncov`, over an explicitly named set *W*. It states both bounds of `post_bounded` and the query membership. The theorem statement and the caption give `init_env_le` as ρ₀ ≤ ρ |
| Transfer environment; ownership of the entry obligation | blind editor | §4.1 says that transfer outputs are read in the previous global values joined with the publications, and that entry coverage belongs to the routing conditions, not to `analysis_contract` |
| "Every post-solution" in the abstract | C | The abstract now names the routing condition |
| Call equations and a worked call | blind A, D, F | §4.2 displays the call contribution (publish the seed, read the result, combine; bottom case) with `bump(5)` as the example. The overview now points to it instead of repeating it |
| Source rules and `at_node` | blind D | §5 gives the call/restore rules, the stuck cases, and the definition of `at_node`, with the repeated-command example |
| Live-set bridge | F, blind A | §4.3 explains continuation → callee result (non-bottom entry, `sol_vars_callee_result`) → callee entry, the bottom case, and non-returning activations |
| Single enter alternative; overlapping example | A, B, C, D | §3.2 says that shipped analyses return one alternative and cites the overlapping-enter regression (`ov_two_contexts_admitted`) |
| Might–Manolios mischaracterized | B | Corrected in §8, and the duplicate in §4.2 was removed |
| `context_sound` cited as a fact | B | §5 cites the theorem `run_voblint_contexts` and the predicate `context_sound` |
| Proof idea cites the generic principle | A | Cites `caller_chain_covered` as an instance of `caller_chain_closure`, and `activation_context_rel_caller_entryI` |
| Undefined terms and overloaded symbols | A, C, D | `path_of`, `extend`, `entry_g`, `c_0`, `Some`, post-solution, locale and Int are defined. The entry state is now *d*, the residual command *r*, and the key set of Theorem 2 *W* |
| "Two combine operations" | A, D | `combine_env` and `combine_assign` are both described |
| §3 versus §6 on frame stacks | B | §3 now says that frames could carry ghost contexts (§6) |
| Knoop–Steffen under-credited | B | Their stacks for recursive locals are credited in §8 |
| Breitner, Lammich–Müller-Olm precision | G | Added to §8, checked against the AFP entries |
| Dabrowski–Pichardie "no solver" | G | Cited with locator [§7], as in the thesis |
| Running-time population | B, E, blind editor | §7 states the rule from `scripts/profile_corpus.py` (380 fixtures without their own timeout, 11 ill-formed, 369 left), the median over three repetitions, failure handling, and that all 21 timeouts are entry-state cases on seven recursive fixtures. It also says that call strings of length 2 were not profiled |
| Cost per policy | B, D, E, blind editor | New Table 4, generated from the committed profiling snapshot by `paper/tools/costs.py` |
| Context counts | B | Table 3 has a context column, generated from new `--dot` claims |
| Diverging example | G | §7 names a fixture that is proved without contexts and does not terminate under entry-state contexts. §9 cites Goblint's `ana.context.widen` and context gas, checked in its options schema at revision `6127869c` |
| "Five of eight" unverifiable | B, E, D | Removed. The thesis carries the flavors comparison |
| Removed vendored assumption not named | A | Named in §6 (stabilization assumptions of the widening and narrowing classes) |
| Boolean claim too operational | blind editor | "pure and total; no evaluation order to model" |
| Heap sentence | A, B, D, F | Pointers into frames and threads break the assumption; a heap without them needs a richer store model |
| Trace hook scope | A | §5 and Figure 2 say that it is called by the solve, the routing and the report construction |
| Figure 2 overlap; parser "trusted" | D | Hook moved below the proved zone. §1 calls the parser and printer unverified |
| `scale.py` bypasses the guard; `paper` task | E | `scale.py` checks the solver checkout itself; `pixi run paper` runs every generator |
| Data availability | E, blind editor | Rewritten: what the archive lacks, that the paper's scripts will be released with it, and that the solver is planned for the AFP |

## Round 3: points not acted on

- **Seidl–Fecht** (requested in every round). Neither the paper nor its
  abstract could be retrieved from this environment. Citing a paper we have
  not read would break our own rule, so the citation waits until the full text
  is in hand.
- **A per-context theorem.** Pending as formal work (stacked PR 4). If it
  lands, the title and contribution 1 will be strengthened.
- **Journal format.** The paper stays an ITP paper. The extended version the
  journal reviewers describe is future work.
- **Profiling call strings of length 2.** This needs a new measurement
  campaign. We state that it was not profiled.
