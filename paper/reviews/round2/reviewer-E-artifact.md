# Summary

The local artifact provides substantial executable evidence for the paper: all 31 reruns of the registered running-example/flavors claims matched their recorded output, the call-string precision witness reproduced, the dead-check example reproduced, and the paper rebuilt. The public deposit is materially less complete than the supplied working tree: its solver submodule is empty and the comparison scripts are absent. This prevents an independent public-source reconstruction of the central result. My assessment concerns the frozen round-2 submission, supplemented by the current local sources; it is not an Isabelle proof certification.

## Recommendation

**Major revision. Confidence: 4/5.**

Badges: **Available: withhold for the complete claimed artifact** (a persistent but incomplete archive exists); **Functional: withhold pending a clean build from the released artifact** (local CLI functionality demonstrated); **Reusable: withhold** until dependencies, exact submission revision, and reproduction entry points are bundled and documented. These are artifact recommendations, not a rejection of the mathematical contribution.

## Strengths

- The checked-in claim machinery gives precise commands and deterministic outputs. All Voblint verdict cells in Table 1 reproduced locally.
- The manuscript distinguishes solver partial correctness, executable trust, and non-vacuity. Named non-vacuity and context witnesses exist in the source.
- Seven reused solver theories can be identified through imports; no `sorry` or `oops` occurs in them or in `src/`.
- The LaTeX document and generated-snippet/bibliography checks complete successfully. The public project repository and persistent Zenodo record are reachable.

## Major weaknesses

1. **The advertised archive does not contain the solver or the comparison reproduction scripts.** Location: Data availability, `paper/sections/statements.tex:2–7`, and first-page supplementary-material link. The paper says the vendored solver theories and scripts regenerating every quoted analyzer output are archived. On inspection, concept DOI [10.5281/zenodo.23260696](https://doi.org/10.5281/zenodo.23260696) resolves through the API to v2.2.0, record [23484950](https://zenodo.org/records/23484950), commit-prefix `9f92b86`. Its ZIP contains 1,635 members, but the only solver member is the empty directory `ManuelLerchner-Voblint-Verification-Master-Thesis-9f92b86/vendor/td-verification/`. There is no `paper/`, no `thesis/shared/code/goblint-flavors/run.sh`, and no corresponding `results.tsv`. The unauthenticated [solver repository API](https://api.github.com/repos/ManuelLerchner/td-verification) returns HTTP 404. The acknowledged private dependency is therefore a real blocker, and the preceding archive claim is inaccurate. This dependency is substantive: `src/Abstract_Interpreter/Solver/TD_Solver_Bridge.thy:2` imports `TD.TD_side_Interface`; `src/Abstract_Interpreter/Domain/Lattice/Abstract_Domain.thy:2` imports `TD.Warrowing`. Release a self-contained, licensed snapshot with the exact solver revision and the paper's scripts, and cite a version DOI.

2. **The paper build does not perform the analyzer re-check that the evaluation attributes to it.** Location: Section 7, `paper/sections/evaluation.tex:49–51`. `pixi.toml:168–172` makes `paper-check` check snippets and bibliography, while `paper` renders statistics and the flavors table from existing generated files. `paper/tools/flavors.py:50–62` reads stored text; it does not run the analyzer. The separate thesis claims command can do so, and my independent reruns passed, so this is a reproducibility-wiring issue rather than an observed wrong verdict. Add the relevant claim checks to the paper target or state the separate command explicitly. The Goblint cells additionally depend on recorded TSV output and are not checked by that target.

## Minor comments

1. **Define the measurement unit.** Section 7's running-time paragraph calls 5,535 entries “runs” while also specifying three repetitions. The snapshot has 5,535 valid fixture/configuration cases; successful cases each store the median of three executions (`scripts/profile_corpus.py:189–206`). A timeout returns early. Thus “21 of 5,535 configurations timed out; successful timings are medians of three repetitions” is more precise. The median across stored case medians is 0.235 ms, formatted as 0.23 ms; the 95th-percentile value is 1.48 ms. The historical timing campaign was not rerun.

2. **State the source-count scope.** Section 6's 212 theories/59,107 lines agrees with `stats.json`, but a literal recursive source count gives 213/59,361. The difference is exactly the 254-line generated `src/Program_Model/VIMP/VIMP_Grammar_Generated.thy`. This is a scope convention, not evidence of drift. The “formal text” and “proved statements” counts need their parser/counting convention documented; see independent-count limitations below.

3. **Pin the artifact corresponding to the submitted paper.** The public archive has 212 source theory files and no paper directory, whereas the review working tree includes the paper and current generated sources. A version/commit mapping would let readers distinguish intentionally older archived material from unavailable paper evidence.

4. **Public build status is not established by local execution.** The checked local executable may have been built with the private dependency already present. No Isabelle rebuild was performed, as requested by the review protocol. The two `sorry` occurrences found in `vendor/td-verification/TD_plain_warrow.thy:354,411` are outside the seven reused theories; they do not contradict the carefully scoped manuscript sentence. Avoid broadening that sentence to the entire vendored directory.

## Questions for author

- Can the seven reused solver theories, their dependency closure and license be included in the versioned public archive before publication?
- Which immutable revision generated the frozen paper, the local CLI, and the Goblint comparison? Can one documented command rebuild and check all three?
- Can the exact Goblint 6127869c executable/environment and raw logs be supplied, including Apron support and configuration flags?
- What precisely is excluded from “formal text” and counted as a “proved statement”? Can the source counter expose a per-file inventory?

## Commands and evidence

All shell commands were prefixed with `rtk` / `rtk proxy`. Reads were limited to the submission and allowed supporting sources. No earlier reviews or forbidden planning/style material was read. No tracked proof file was edited and no Isabelle build ran. `docs/ISABELLE_AGENT_NOTES.md` was read before disk source inspection under the review's explicit exception.

## Frozen input and build

- Frozen PDF SHA-256: `4727dc597eabdca81bd617a2a05c5c07b6fad8a738507d8665ddacb198f62e9f`.
- Frozen extracted text SHA-256: `44a2683a481d607328a43f0ea8615bc24811fe14f557567102e30ac3c19b6ded`.
- `rtk proxy python3 tools/snippets.py --check`: exit 0.
- `rtk proxy python3 tools/bib.py --check`: exit 0.
- `rtk proxy latexmk -g -interaction=nonstopmode -halt-on-error main.tex`: exit 0; 17-page `_build/main.pdf`. Font-size substitution and underfull-vbox warnings remain. Frozen files were not overwritten.

## Analyzer outputs

The CLI was inspected with `../_build/default/cli/voblint_main.exe --help`. A Python harness read `thesis/shared/claims.toml`, ran the existing executable with each registered argv from repository root, and compared stdout+stderr (trailing newline normalized) to `thesis/shared/generated/<key>.txt`.

- Keys: `pg-contexts-none`, `pg-contexts-entry`; every `flavors-*` key (29 keys, including the additional no-refinement diagnostic).
- Result: **31/31 exit 0 and exact matches**. This includes all four Voblint settings over seven flavors programs, yielding every Voblint Table 1 cell. Figure 1's context-free checks are UNKNOWN; entry-state checks are PROVED.
- Additional commands: `rtk proxy ../_build/default/cli/voblint_main.exe --analysis sign --context call-string --context-depth K ../tests/regression/17-call-string/precision/05-callstring_graph_sign.vimp`, for K=1 and K=2. Both return normally; K=1 yields two UNKNOWN checks and K=2 two PROVED checks, with `x=+` and `y=-`. Formal anchor: `src/Examples/Sign/CallString/Example_Sign_DG_CallString_K2.thy:291`.
- The concrete program in `src/Examples/Capstone/Example_Non_Vacuity.thy:223–230` was transcribed into `/tmp/reviewer-e-dead.vimp` and run with `--analysis interval --globals join`: `x == 0` is REFUTED, `x == 5` is DEAD. The formal non-vacuity endpoints exist at lines 151, 191 and 254 of that theory. The main running-example reruns cover its PROVED outcomes.
- **UNVERIFIED: all Goblint Table 1 cells.** The exact Goblint binary was not available: direct likely paths and `rtk proxy fd -t f '^goblint(\.exe)?$' /Users/manuellerchner/git /private/tmp` found none. The supplied `thesis/shared/code/goblint-flavors/run.sh` records the requested flags and revision `6127869c56c6`, but stored TSV is not a rerun. I do not claim independent reproduction of these outputs or the historical bug replay.
- **UNVERIFIED: historical performance executions.** Independent reduction of the pinned snapshot was performed instead; timings were not remeasured.

## Numbers and formal-source checks

Every `\stat{...}` used by the paper was compared with the corresponding generated source. Repository figures match `thesis/shared/generated/stats.json`: 212 theories, 59,107 lines, 39,236 formal-text lines, 2,683 proved statements, seven used solver theories/9,533 lines, 14,095 generated OCaml lines and 4,919 handwritten OCaml lines. Profiling figures come from `profiling.json`, not `stats.json`.

Independent filesystem counts establish 213 `.thy` files/59,361 lines, or exactly 212/59,107 after excluding the generated grammar theory; 14,095 generated OCaml lines; 4,919 CLI `.ml` lines after the documented generated-printer exclusion; and seven solver theories/9,533 lines. The seven files are Basics_side, Warrowing, Destabilization_side, TD_side, Update_rules, TD_side_upd_rule, TD_side_Interface. Their imports were inspected. There are 386 current regression fixtures; this is not the historical profiling population.

**UNVERIFIED independent parser-level counts:** 39,236 formal-text lines and 2,683 statements match the generated source, but a naive declaration-line scan yields 2,690 and a comment/cartouche-stripping approximation yields 2,673. Neither is a sound Isabelle parser. I therefore do not treat either discrepancy as a manuscript error or claim independent confirmation of these two numbers.

Independent reduction of `pages/data/profiling/2026-10-21-17fcb363d.json` gives 369 valid fixtures, 15 domain/context settings, 5,535 cases, 21 timeout cases, median 0.235 ms and p95 1.48 ms. Metadata records Apple M4 Pro, three repetitions and 30-second timeout. Independent log-log fits for n >= 100 reproduce exponents 2.01–2.86 (eight scaling families). The source snapshot contains 5,700 rows before invalid cases are excluded and metadata lists 380 selected fixtures.

All 46 distinct `\isaname{...}` references in the paper have matching source occurrences in `src/` or the solver; source-existence checking is not proof replay. Central endpoint: `src/Executable_Surface/CLI/Analysis_Certified.thy:196`. `rg -n '\b(sorry|oops)\b' ../src ../vendor/td-verification --glob '*.thy'` found only the two unused solver occurrences identified above. The seven imported solver files and all project source theories have no matches.

## Online availability

- [Public project repository](https://github.com/ManuelLerchner/Voblint-Verification-Master-Thesis): reachable and marked Public.
- `rtk proxy curl -L -s -o /tmp/reviewer-e-zenodo.json -w '%{http_code}\n' https://zenodo.org/api/records/23260696`: HTTP 200, v2.2.0, concrete DOI `10.5281/zenodo.23484950`.
- [Downloaded ZIP](https://zenodo.org/api/records/23484950/files/ManuelLerchner/Voblint-Verification-Master-Thesis-v2.2.0.zip/content): saved as `/tmp/reviewer-e-artifact.zip`, 20,850,703 bytes. SHA-256 `5b610e51cecb78dbcd55a757f4f887479bb05828408845e8ab8b094ef9903616`; API reports MD5 `882281371606554a59e2a77b9bc1cf14`.
- Python `zipfile.ZipFile(...).namelist()` inspection: 1,635 members, zero files under `vendor/td-verification`, zero `paper/` members. `thesis/shared/claims.toml` and the named non-vacuity/certified-source theories are present; Goblint flavors comparison scripts/results are absent.
- `rtk proxy curl -L -s -o /tmp/reviewer-e-td.json -w '%{http_code}\n' https://api.github.com/repos/ManuelLerchner/td-verification`: HTTP 404. This establishes lack of unauthenticated availability, not nonexistence.
- Other scholarly references were outside this artifact evaluator's independently verified scope. **UNVERIFIED** here; no claims of literature verification are implied by the bibliography consistency check.
