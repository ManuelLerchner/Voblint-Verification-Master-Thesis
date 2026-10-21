# Reviewer 5: Artifact Evaluation

Submission: "Calling Contexts Made Concrete: End-to-End Soundness of a Goblint-Style Analyzer in Isabelle/HOL" (JAR).
Artifact: repository at HEAD `02e48d860` (working tree; `paper/` is staged, not committed), Zenodo concept DOI 10.5281/zenodo.23260696.
Evaluation date: 2026-10-21. macOS, Isabelle2025-2 and OCaml 5.4.1 installed. No Isabelle build was run (out of scope for this review); CI results for HEAD were inspected instead.

## Summary

Every analyzer output the paper states was reproduced with the CLI, including all 32 Voblint cells of Table 1. The full regression corpus (386 fixtures) passes, and the thesis claim registry (144 claims) still matches CLI output. All 60+ Isabelle names cited in the paper exist in `src/` or the vendored solver. No `sorry`, `oops`, `axiomatization` or `quick_and_dirty` occurs in `src/` or in the 7 reused solver theories. The repository statistics in Section 6 match a fresh measurement exactly; an independent count differs by one theory that the counting tool skips. The paper builds from `latexmk`. CI at HEAD reports `isabelle-build` and `codegen-check` green.

The artifact is not reproducible from public sources. The submodule `vendor/td-verification`, which holds the reused solver theories, points to a private repository (HTTP 404). In the Zenodo archive v2.2.0 that the DOI resolves to, `vendor/td-verification/` is an empty directory. The Data Availability statement says the vendored solver theories are archived on Zenodo, which the archive contradicts. The archive also predates the flavors fixtures, the Goblint results, and the profiling snapshot behind Section 7, so Table 1 and the running-time paragraph cannot be reproduced from the archived version.

## Badge recommendation

| Badge | Award | Reason |
| --- | --- | --- |
| Available | **No** (yes after fix) | DOI resolves, GitHub repository is public, license BSD-3. The archived record omits the solver theories (empty submodule directory) and predates the Section 7 evidence. The submodule repository is private. |
| Functional | **Partial: CLI yes, proof no** | CLI claims reproduce exactly. A reviewer cannot rebuild the Isabelle development, regenerate the OCaml, or confirm `codegen/generated` matches the theories without the private submodule. That evidence comes only from the author's CI logs. |
| Reusable | **No** (yes after fix) | Good structure: claim registry, drift checks, regression runner, pinned profiling snapshot. A public rebuild is impossible, and the AFP version is not pinned. |

## Checked claims

| # | Claim (paper location) | How checked | Result |
| --- | --- | --- | --- |
| 1 | Fig. 1: entry-state + Interval proves `a == 6`, `b == 5` | `voblint_main.exe --analysis interval --context entry-state --globals warrow docs/readme-figures/contexts.vimp` | PROVED, PROVED. Match |
| 2 | Fig. 1 states: pp2 `a,b ∈ ⊤`; pp3 `a ∈ [6,6]`; contexts `[5,5]`, `[4,4]`; `n` at entry/exit | `--verbose` trace | route `-> context [[5,5]]`, `[[4,4]]`; pp3 `a=[6,6]`; exit_bump `n=[5,5]` / `[4,4]`. Match |
| 3 | Fig. 1 caption: without contexts both UNKNOWN | `--context none` | UNKNOWN, UNKNOWN (`a=[-∞,6]`, `b=[-∞,6]`). Match |
| 4 | §7 k=2: call strings of length 1 lose both signs, length 2 proves both checks | CLI with `--context call-string --context-depth 1/2` on `tests/regression/17-call-string/known-imprecision/06-...vimp` | k=1 UNKNOWN×2 (`⊤`); k=2 PROVED×2. Match |
| 5 | §7 k=2 theorem `sign_k2_strictly_more_precise_than_k1_at_g` | read `src/Examples/Sign/CallString/Example_Sign_DG_CallString_K2.thy:291` | Exists. Statement concerns g's entry. Proved on a hand-assembled equation system solved with the always-join rule, not on `run_voblint`. The checks are not part of the theorem (Problem 6) |
| 6 | §1/§7 Goblint #1156: `c % 2` for `c ∈ {−5,−7}` is −1 | CLI on `tests/regression/24-site-figures/precision/04-goblint_1161_congruence_mod.vimp` | `int`: REFUTED `== 1`, PROVED `== -1`. `congruence` alone: UNKNOWN both. Consistent with the paper (it states no Voblint verdict here) |
| 7 | `prefix_congruence_mod_unsound`, `congruence_mod_sound` | read `Example_Non_Vacuity.thy:357`, `Congruence_Arithmetic.thy:766,850` | Exists and matches the prose. `congruence_mod_sound` is the lemma that discharges the `mono_arith_ops` assumption, not the obligation itself (Problem 7) |
| 8 | Table 1, Voblint rows (32 cells) | CLI with each domain (`sign`, `interval`, `int`, `int,order`) on each of the 7 `tests/regression/28-flavors` programs mapped in `thesis/shared/claims.toml` | All 32 cells match |
| 9 | §7 Int on "not ind." has an even value in `[2,4]` | CLI `--analysis int` | `signs:+; intervals:[2,4]; parities:2ℤ; congruences:2ℤ`. Match |
| 10 | §7 "Sign keeps i ≥ 0" | CLI `--analysis sign --verbose` vs `int --verbose` at loop head | Standalone Sign: `i=⊤`. Sign component inside Int: `≥0`. `--int-refinement never`: UNKNOWN. Wording needs clarification (Problem 8) |
| 11 | §7 Interval proves `i >= 0` on reset; Goblint Interval does not | CLI + `results.tsv` | Voblint PROVED; tsv `narrow_works_lb interval i >= 0: is unknown`. Match |
| 12 | Table 1, Goblint rows; revision 6127869c | `thesis/shared/code/goblint-flavors/results.tsv`, `run.sh` | Table matches the recorded tsv; revision stated in `run.sh`. **Not reproduced**: Goblint not installed, and no pinned build recipe (Problem 5) |
| 13 | "Voblint's verdicts, which the build re-checks against the analyzer" | `pixi run python3 thesis/tools/claims.py --check`; `tests/run.py` | `144 claim(s) still match the CLI`; `386 passed in 5.70s` |
| 14 | 212 theories, 59,107 lines, 39,236 formal, 2,683 proved statements | `stats.json` + fresh `thesis/tools/stats.measure()` | Fresh measurement equals `stats.json` exactly |
| 15 | Same, independent count | `fd -e thy . src \| wc -l` → 213; lines 59,361; `rg` lemma/theorem/corollary → 2,690 | Off by one theory: `src/Executable_Surface/CLI/Arithmetic_Diagnostics.thy` (269 lines, 8 statements) is loaded by import but missing from its ROOT, so the counter skips it (Problem 4) |
| 16 | 7 reused solver theories, 9,533 lines | `cat` of the 7 imported theories `\| wc -l` | 9,533. Match |
| 17 | 14,095 generated, 4,919 handwritten OCaml lines | `wc -l codegen/generated/ml/Voblint_Generated.ml`; `cli/**/*.ml` minus the grammar-generated files | 14,095 / 4,919. Match |
| 18 | §7 profiling: 369 fixtures, 15 configurations, 5,535 runs, median 0.23 ms, p95 1.48 ms, 21 timeouts, exponents 2.01–2.86 | `thesis/shared/generated/profiling.json` (snapshot `pages/data/profiling/2026-10-21-17fcb363d.json`) | All match (median 0.235). Snapshot at `17fcb363d`, 8 commits before HEAD. 369 = 386 fixtures minus those with a `--timeout` PARAM, which the paper does not say (Problem 9). Not re-run |
| 19 | Cited Isabelle names exist | `rg -w` over `src/`, `vendor/td-verification` for every name in the paper | All found. `depL` is `dep\<^sub>L`; `routing_adequate`/`routing_total` are locale assumption names in `Routed_Context.thy:86,104` |
| 20 | Non-vacuity: `nv_source_certified`, `nv_check_proved_sound`, `nv_dead_unreached`, `unknown_everywhere_sound` | read `Example_Non_Vacuity.thy` | Exist. `nv_config` = Interval, Warrow, EntryState, as stated |
| 21 | "contains no sorry" (§1); "Neither Voblint nor the reused solver theories contain sorry or oops" (§6) | `rg -n -w 'sorry\|oops\|quick_and_dirty\|axiomatization'` | `src/`: none. Reused 7 theories: none. `vendor/td-verification/TD_plain_warrow.thy:354,411` contain `sorry`, in a theory the TD session does not load (Problem 10) |
| 22 | Five update rules | CLI `--help` | `join\|per-origin\|warrow\|warrow-per-origin\|bounded-narrowing`. Match |
| 23 | Zenodo DOI resolves | WebFetch | Concept DOI → record 23484950, v2.2.0, 2026-10-19, BSD-3, one GitHub release zip |
| 24 | Zenodo archive contents | download, `md5` = 882281371606554a59e2a77b9bc1cf14 (matches record), `unzip -l` | `vendor/td-verification/` present only as an empty directory (Problem 1) |
| 25 | GitHub repo public | `gh repo view` | `PUBLIC`, HTTP 200 |
| 26 | Paper builds | `pixi run paper-check`; `cd paper && latexmk -g main.tex` | Both pass; only stmry font-size warnings |
| 27 | Isabelle build, codegen agree with theories | `gh run list` / `gh run view` for HEAD `02e48d860` | CI: `isabelle-build`, `codegen-check`, `thesis-facts` success. Not reproduced locally |

## Problems found

1. **Solver theories missing from the archive and from public sources.** `.gitmodules` points `vendor/td-verification` to `https://github.com/ManuelLerchner/td-verification`:

   ```text
   $ curl -s -o /dev/null -w '%{http_code}' https://github.com/ManuelLerchner/td-verification   → 404
   $ curl -s -o /dev/null -w '%{http_code}' https://github.com/stilscher/td-verification        → 404
   $ unzip -l Voblint-Verification-Master-Thesis-v2.2.0.zip | rg vendor/td-verification
            0  10-19-2026 23:45   .../vendor/td-verification/
   ```

   GitHub release zips never include submodule contents. The Data Availability statement ("the vendored solver theories ... are archived on Zenodo") is therefore false for the archived record. The next sentence concedes the source is not public, but it contradicts the first. Without these theories nothing builds, codegen cannot be regenerated, and Theorem 3 cannot be checked.

2. **The archived version predates the paper's evidence.** The DOI resolves to v2.2.0 (`9f92b8678`, 2026-10-19), 35 commits before HEAD. Missing in v2.2.0:

   ```text
   MISSING in v2.2.0: thesis/shared/code/goblint-flavors/results.tsv
   MISSING in v2.2.0: pages/data/profiling/2026-10-21-17fcb363d.json
   MISSING in v2.2.0: scripts/profile_corpus.py
   ```

   `tests/regression/28-flavors/` is also absent, and `git diff --stat v2.2.0 HEAD -- src vendor cli tests/regression` reports 54 changed files, including theory moves in `src/Analyses/*`. Table 1, the running-time paragraph, and possibly the Section 6 counts cannot be reproduced from the archive. The paper cites the concept DOI, so the resolved version will keep changing. The `paper/` directory itself is uncommitted.

3. **A fresh public clone builds the paper with wrong numbers and no error.** `scripts/pages_stats.py` computes `solver.used.*` only `if solver`. With the submodule directory empty, `theory_sizes` returns nothing, so the paper would print "reuses 0 theories (0 lines)" without failing. The `paper` pixi task also does not depend on `thesis-stats-write`. `paper/README.md` says to run `thesis-draft` (a full Typst thesis build) first, although `thesis-stats-write` suffices.

4. **Theory count skips one loaded theory.** `src/Executable_Surface/CLI/Arithmetic_Diagnostics.thy` is imported by `Analysis_Run` but not listed in `src/Executable_Surface/CLI/ROOT`, and isar-tools counts only ROOT-listed theories. The true figures are 213 theories, about 59,370 lines and about 2,691 proved statements. The deviation is small, but the paper presents these counts as exact. Either list the theory in ROOT or count imported theories.

5. **The Goblint half of Table 1 is a recorded snapshot.** `thesis/shared/code/goblint-flavors/run.sh` names revision `6127869c56c6` "built with Apron", but the artifact gives no build recipe, opam lock, or container. Goblint is not part of CI (`run.sh`: "Goblint is not part of CI"). A reviewer can check only that the table matches `results.tsv`. The paper should label these rows as recorded output and give a reproducible Goblint setup.

6. **The k=2 paragraph is labeled "machine-checked for one program" but mixes two kinds of evidence.** `sign_k2_strictly_more_precise_than_k1_at_g` concerns the sign of `p` at g's entry. It is proved on `sign_nest_2_eqs`, which is assembled from framework constants and solved with `TD_side_always_join_Interp_solve`, not with `run_voblint`. Its program `sign_nest_program` contains no checks. "Proves both checks" is CLI output on `tests/regression/17-call-string/precision/05-callstring_graph_sign.vimp` (default rule warrow), which counts as executable evidence. State the two separately.

7. **`congruence_mod_sound` is named as the obligation, but it is a lemma.** The obligation is the remainder assumption of locale `mono_arith_ops`. `congruence_mod_sound` (`Congruence_Arithmetic.thy:766`) discharges it in `interpretation congruence_arith: mono_arith_ops` (line 850). The claim "the defective operator could not have been registered" holds through that locale, so the locale should be cited.

8. **"Sign keeps i ≥ 0" holds only inside the product.** Standalone `--analysis sign` gives `i=⊤` at the loop head and at the check. Inside Int, the sign component reads `≥0` at the loop head. `--int-refinement never` leaves the check UNKNOWN. The gain comes from mutual refinement, which the sentence should say.

9. **The 369 fixtures need a definition.** The corpus has 386 fixtures (`stats.json corpus.cases`, `tests/run.py`: `386 passed`). `scripts/profile_corpus.py:1015` excludes fixtures whose PARAM line sets `--timeout`. The paper should say so and name the profiled commit `17fcb363d`.

10. **The no-sorry claim needs scoping for the vendored directory.** A reviewer who runs `rg sorry vendor/` finds `TD_plain_warrow.thy:354,411`. This theory is not loaded by session TD and not imported by Voblint, so the paper's claim about the *reused* theories is accurate. State that the 7 imported theories were checked, and note that the vendored directory contains unused, unfinished variants.

11. **Venue metadata.** The PDF carries LIPIcs/ITP 2027 front matter ("Interactive Theorem Proving (ITP 2027)", DOI `10.4230/LIPIcs.ITP.2027.1`, placeholder editors "John Q. Open and Joan R. Access"), yet the submission goes to JAR.

12. **Missing reproduction guide.** Neither `README.md` nor `paper/README.md` maps paper claims to commands. The mapping exists implicitly in `thesis/shared/claims.toml`, `tests/regression/28-flavors/README.md` and `thesis/shared/profiling.toml`. The AFP version is not pinned (README: "an AFP checkout"). Locally, `pixi run cli-build` warns `codegen/generated/ is stale` because the local stamp differs from the sources. Only the CI `codegen-check` shows that the checked-in OCaml matches the theories, and a reviewer without the submodule cannot repeat it.

## Recommendations

1. Make the solver fork public, or vendor the 7 used theories as plain files, keeping their upstream license and attribution. Then mint a new Zenodo version from a tag that contains `paper/`, the flavors fixtures, `results.tsv`, and the profiling snapshot. Cite that **version** DOI, not the concept DOI.
2. Fix the Data Availability statement to match what the archive contains.
3. Make `pages_stats.py` fail when `vendor/td-verification` is empty, and make the `paper` task depend on `thesis-stats-write`.
4. Add `Arithmetic_Diagnostics` to the CLI ROOT, or count imported theories, then regenerate the statistics.
5. Add an `ARTIFACT.md` (or a README section) that lists each paper claim with its command and expected output, using `claims.toml` entries. Include Isabelle2025-2, the AFP release or hash, the OCaml/dune versions, the expected build time, and the Goblint build recipe for the 6127869c rows.
6. Correct the prose points in Problems 6–10 and replace the LIPIcs front matter with JAR's format.

After 1–3 the artifact would qualify for Available and Functional. The claim registry and drift checks are strong reusability features once a public rebuild works.
