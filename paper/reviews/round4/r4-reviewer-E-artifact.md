# Round 4, returning reviewer E (artifact)

## Summary

I re-evaluated the revised 19-page submission (`paper/reviews/round4/submission.pdf`, SHA-256 `078817197625ef43ab9af679cf0e7852410ea75922ba9a6f6d2d574e6eda0195`) against the local checkout at `2127b9b76` (branch `paper/itp-draft`, not pushed), the public GitHub repository, and the Zenodo record. I did not run a full Isabelle build. Every analyzer output and number in the paper reproduces. That covers Figure 1, Table 3 including the new context column, Table 4 (from an independent reduction of the snapshot), the profiling population, Table 2 and every `\stat` value. `scale.py` now refuses to run without the solver checkout, which I tested without touching the vendor directory. A fresh LaTeX build gives a PDF whose text is identical to the submission. `paper-generated` leaves `paper/` clean.

Most round-3 points are fixed. Two availability problems remain, and the revision now discloses both honestly. The modified solver is still not public (GitHub API: HTTP 404), and the paper's Table 3 claims and table scripts exist only on an unpushed branch. I found three new problems. Table 3 and Table 4 both have a column headed "Contexts", but the two columns count different things and disagree on the same fixture. `pixi run paper` fails on a clean checkout because `\stat` reads a gitignored file that only a thesis build produces. The paper calls the lexer and parser handwritten, but both are generated from a grammar manifest by a project script and Menhir.

Recommendation: minor revision for the paper text. The artifact still cannot get Available as long as the solver is private.

## Badges

| Badge | Round 3 | Round 4 | Reason |
| --- | --- | --- | --- |
| Available | no | no | Solver repository `ManuelLerchner/td-verification` returns 404; Zenodo latest is v2.2.0 (record 23484950), which predates the paper tooling; `paper/itp-draft` is not on GitHub (`git ls-remote` shows only `main` at `02e48d860`) |
| Functional | CLI only | local yes, public CLI only | All claims, tables and stats reproduce locally; the theories cannot be built from public sources |
| Reusable | no | no | Needs the solver, a paper-sized check target, and a self-contained `paper` task |

## Resolution of round-3 points

| Round-3 point | Status | Evidence |
| --- | --- | --- |
| Solver missing from archive and not public | NOT RESOLVED (now disclosed) | GitHub API for `ManuelLerchner/td-verification`: 404 today. Data availability statement says so and promises an AFP entry |
| Archive is not a snapshot of the paper's experiments | NOT RESOLVED (now disclosed) | `git diff origin/main HEAD` shows that the 8 `ctx-mutual-*` claim registrations and outputs, `pixi.toml` paper tasks and all of `paper/` are unpushed. `src/` is identical to public `main`. The statement says they "will be released together with this paper" |
| Data statement inaccurate | RESOLVED, with one front-matter inconsistency | Every sentence of the new statement checks out (see below). The p. 1 "Supplementary Material" line and the "Related Version … full formalization" link remain unqualified |
| `scale.py` bypasses the `pages_stats.py` guard | RESOLVED | `paper/tools/scale.py:43` checks `TD_DIR/ROOT`. Tested with `TD_DIR` patched to a missing and to an empty directory: rc 1, `collect()` not called, nothing written. Real path: rc 0, output byte-identical to the committed `scale.tex` |
| `pixi run paper` does not run the generators | PARTLY | `pixi.toml:169` now runs `stats.py`, `contexts.py`, `costs.py`, `scale.py` and depends on `paper-check`. However `stats.py` reads `thesis/shared/generated/stats.json`, which is gitignored (`.gitignore:57`) and written only by a thesis build. With it absent, `stats.py` exits 1 ("run pixi run thesis-draft first"), so a clean checkout cannot build the paper with `pixi run paper` alone |
| Table numbers swapped in `response.md` | RESOLVED | Round-2 rows now read "New Table 3" (contexts) and "Table 2" (size), matching the paper |
| Congruence attribution | RESOLVED | `mod_sound` is an assumption of `sound_arith_ops` (`src/Analyses/Shared/Nonrelational/Abstract_Arithmetic.thy:65,120`), discharged by `congruence_mod_sound` (`Congruence_Arithmetic.thy:766`); §7 now says exactly this |
| Benchmark denominator and quantile population | RESOLVED | §7 states 380 → 11 excluded → 369 fixtures, 5,535 cases, median of three repetitions, failure in any repetition, successful-case quantiles |
| "Five of eight" flavors claim unverifiable | RESOLVED (removed) | §7 now only points to the thesis |
| Paper-sized verification command | NOT RESOLVED | `paper-check` still checks only snippets and bibliography (`pixi.toml:168`). The 8 Table 3 claims are checked only by the thesis-wide `claims.py --check` (152 claims) |

## Claim check

| Claim | Command | Result |
| --- | --- | --- |
| All registered analyzer outputs current | `pixi run python3 thesis/tools/claims.py --check` | 152 claims match the CLI |
| Fig. 1: no contexts, both checks UNKNOWN | `voblint_main.exe --analysis interval --globals warrow --context none docs/readme-figures/contexts.vimp` | UNKNOWN `a=[-∞,6]`, UNKNOWN `b=[-∞,6]`; byte-identical to `pg-contexts-none.txt` |
| Fig. 1: entry states, both PROVED | same with `--context entry-state` | PROVED `[6,6]`, PROVED `[5,5]`; byte-identical to stored claim |
| Fig. 1 node states (pp2 ⊤, pp3 `a∈[6,6]`, bump contexts `[5,5]`/`[4,4]`, `n` at exit) | same with `--graph-snapshot` | All match. pp0 and the unreachable pp1 of `bump` exist and are omitted, as the caption says |
| Table 3 verdicts and values | 4 CLI runs on `17-call-string/precision/09-depth2_mutual_recursion_in_loop.vimp` (none, cs-1, cs-2, entry) | UNKNOWN/UNKNOWN `[1,12]` twice; PROVED `[2,2]`, PROVED `[1,1]` twice; all byte-identical to `ctx-mutual-*.txt` |
| Table 3 concrete values (res1 = 2, res2 = 1; chain three calls deep) | Reading of the program | f(2)→g(1)→f(0)=2, g(2)→f(1)→g(0)=1. Correct |
| Table 3 context column 2/4/6/6 | 4 `--dot` runs, compared byte-for-byte with `ctx-mutual-*-dot.txt`; independent count of `subgraph cluster` minus main | 3−1, 5−1, 7−1, 7−1 = 2/4/6/6. `contexts.py`'s regex `label="[fg] / …"` gives the same. Labels: none `f/unit`, `g/unit`; cs-1 four single sites; cs-2 six site pairs; entry `[0,0]`, `[1,1]`, `[2,2]` for each of f, g |
| Table 4 (all 21 cells) | `costs.py` rerun plus an independent reduction with `statistics.median` and nearest-rank p95 | Medians 0.225/0.236/0.246 → 0.23/0.24/0.25; p95 1.131/1.470/3.144; max 5.593/10.517/1106.0 → 6/11/1106; max contexts 1/23/302; cases 1845 each (entry: 1824 ok + 21 timeouts). All match. `costs.py`'s `int(q·n)` index coincides with nearest rank for both n |
| 380 fixtures, 15 configurations | snapshot `meta` | `fixtures: 380`, 5 domains × 3 contexts, `reps: 3`, `timeout_s: 30`, `cpu: Apple M4 Pro`, commit `17fcb363d`. 386 corpus files minus those whose `PARAM` sets `--timeout` |
| 11 excluded, 369 left, 5,535 cases | snapshot reduction | 11 fixtures with `invalid` in all 15 configurations; 369 × 15 = 5,535; `\stat{prof.fixtures}`=369, `\stat{prof.runs}`=5,535 |
| 21 timeouts, all entry-state, Interval/Int/Congruence, seven fixtures | snapshot reduction | 21 = 7 fixtures × {congruence, interval, int}, all `entry-state`. Each fixture recurses on a growing argument |
| Median of three repetitions; failure in any repetition fails | `scripts/profile_corpus.py:189–208` | `timed_reps` returns the failing status on the first nonzero exit and the median otherwise. Matches |
| `13-recursion_grows_warrow` proved without contexts, diverges with entry states | CLI, `--context none`; `--context entry-state --timeout 10` | PROVED `x=[0,+∞]`; killed after 10 s (exit 3). Consistent with the claim (see Problems on wording) |
| Scaling exponents 2.01–2.86, evaluations about linear | Independent log-log least-squares fit of `scaling` rows with n ≥ 100 | Time slopes 2.01 (procedures) to 2.86 (call-sites-k1), exact match. Evaluation slopes 0.94–1.00 in my fit, 0.86–0.99 in `profiling.json`; "about linearly" holds either way. `profiling.py --check` passes |
| Table 2 theories and lines | `fd -e thy` per directory, excluding `VIMP_Grammar_Generated` | 27/9,999; 67/21,212; 70/15,815; 15/4,956; 33/7,125; total 212/59,107. Match |
| Table 2 solver row | Import closure from `TD_side_Interface`, `Basics_side`, `Warrowing` | 7 theories, 9,533 lines. Match. Proved counts (466 … 2,683; 168) come from the parser-based counter, which I verified in round 3; `src/` and the vendor pin `c3ebe448` are unchanged since |
| No `sorry`/`oops` in Voblint or imported solver | `rg -w 'sorry\|oops'` | None in `src/`. Two in `TD_plain_warrow.thy:354,411`, outside the import closure. Matches §6 |
| 14,095 generated, 4,919 handwritten OCaml | `wc -l` | `Voblint_Generated.ml` 14,095; `cli/**/*.ml` without generated `vimp_printer.ml`: 4,919. Match |
| Regenerate cleanly | `pixi run paper-generated`, then `git status`/`git diff -- paper` | No diff under `paper/` |
| Paper checks and build | `pixi run paper-check`; `pixi run paper`; fresh `latexmk -outdir` in a temp dir | All succeed. 19 pages; only `stmry` font-size substitution warnings; no undefined references or overfull boxes. `pdftotext` of the fresh build is identical to the submission's |

### Data availability statement, sentence by sentence

| Sentence | Check | Verdict |
| --- | --- | --- |
| Development and regression corpus public on GitHub | Repo is public (API `private: false`). `git diff origin/main HEAD -- src tests` is empty, and `origin/main` equals remote `main` (`02e48d860`) | Accurate |
| An earlier version is archived on Zenodo | Concept DOI resolves to v2.2.0, record 23484950, 2026-10-19 | Accurate |
| Archive lacks the solver, the Table 3/4 claims and profiling data, and the table scripts | Round-3 inspection of the same v2.2.0 ZIP | Accurate. The profiling snapshot and `profile_corpus.py` are on public `main`; the Table 3 claims and `paper/tools` are not public anywhere yet |
| Solver not yet public; AFP planned; theories not buildable from public sources | 404 confirmed; plan unverifiable | Accurate |

## Problems

1. **The two "Contexts" columns count different things and disagree** (Tables 3 and 4, §7). Table 3 counts the (procedure, context) clusters of f and g in the `--dot` graph. Table 4 uses the snapshot's `contexts` field. `profile_corpus.py:176–186` computes that field as the number of distinct context values over all solved unknowns, so `main`'s root context is included and values shared by different procedures count once. For the Table 3 fixture under Interval, the snapshot records 1/5/4 (none/cs-1/entry) where Table 3 prints 2/4/6. A reader who compares the two tables sees a contradiction. Name the unit in both headers or captions, for example "copies of f, g" and "distinct context values". Alternatively, count the same thing in both tables.

2. **`pixi run paper` is not self-contained.** The paper's `\stat` values (`generated_ocaml`, `handwritten_ocaml`) come from `thesis/shared/generated/stats.json`. That file is gitignored and produced only by a thesis build, and `stats.py` exits 1 when it is missing (simulated). `stats.py` also does not check that the file is current. In this checkout the values happen to be correct. Add a step that writes `stats.json` from `scripts/pages_stats.py` to the `paper` task, or make `paper` depend on the step that produces it.

3. **The lexer and parser are not handwritten.** `cli/frontend/vimp_parser.mly` and `vimp_lexer.mll` are headed "GENERATED by scripts/gen_vimp_menhir.py from manifests/vimp-grammar.yaml", and `vimp_printer.ml` comes from `scripts/gen_vimp_printer.py`. §1 ("The parser and the report printer are unverified handwritten code"), §5 and the Figure 2 caption ("Dashed boxes are handwritten code") are therefore inaccurate. Strictly, the trusted base also contains the generator scripts, Menhir and ocamllex. The "4,919 lines of handwritten OCaml parse programs" sentence (§6) is also loose: the handwritten parse code is about 165 lines of glue (`vimp_frontend.ml`, `vimp_positions.ml`). This is wording, not unsoundness. However, the trust boundary is the one place where wording carries the claim. Note also that the "report printer" in §1 is the handwritten renderer under `cli/render`, which is a different file from the generated `vimp_printer.ml` (the program printer).

4. **"Does not terminate" overstates the evidence** (§7, `13-recursion_grows_warrow`). The snapshot shows a 30 s timeout, and I reproduced a 10 s timeout. Entry-state contexts `[n,n]` grow without bound, so divergence is very plausible, but no theorem and no measurement establishes it. "times out (30 s); its entry states grow without bound" says what was observed.

5. **"Eleven fixtures are ill-formed programs."** Three of the 11 (`00-sanity/02-malformed`, `09-parser/02-missing_main`, `09-parser/03-illegal_character`) fail to parse (exit 2). The rest are rejected as ill-formed (exit 4). Write "unparsable or ill-formed".

6. **Front matter still advertises the archive without qualification.** The p. 1 "Supplementary Material: Software (Isabelle/HOL formalization and analyzer)" cites the v2.2.0 record. The "Related Version: … full formalization" link points to a repository whose solver submodule is private. The data statement qualifies both, but the front matter should cite the version DOI and say "without the vendored solver", or point to the statement.

7. **Paper-sized check still missing** (carried over). The evidence for Table 3 can drift without `paper-check` noticing, and `pixi run paper` regenerates tables from stored claim outputs without re-running the analyzer.

8. **Minor robustness in `costs.py`.** "Cases" is `ok + timeout`. Any other failure status (`rejected`, `exit N`) of a valid fixture would silently disappear from the denominator. None occurs in this snapshot. Count every non-`invalid` row, or assert that only these statuses occur. The scaling exponents rest on three to five points per family (n ≥ 100). Saying so would put "fitted exponents" in proportion.

Side note: during this review `thesis/literature.bib` gained an uncommitted `seidl00`/`fecht98` entry that I did not make (probably a concurrent session). I left it untouched. It does not affect the paper build, since the paper cites neither key and `paper-generated` left `paper/` clean.

## Recommendations

1. Publish the solver revision `c3ebe448` (or archive it with its license in the next Zenodo version) and cite that version DOI. This is the only blocker for Available.
2. Push the paper branch or tag a release containing `paper/`, the `ctx-mutual-*` registrations and the snapshot, and point the front matter at it.
3. Label the two "Contexts" columns with their units (Problem 1).
4. Correct "handwritten" for the lexer/parser and the 4,919-line sentence, and list the grammar generator and Menhir in the trusted base (Problem 3).
5. Make `pixi run paper` produce `stats.json` itself, and add a `paper-claims` check over the 8 Table 3 claims and Figure 1's two claims (Problems 2 and 7).
6. Make the wording fixes for Problems 4 and 5.
