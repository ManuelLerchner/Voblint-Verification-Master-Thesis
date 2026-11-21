# conda-forge OCaml packaging tracker

Working notes on moving the OCaml toolchain from opam to conda-forge. The
package list and dependencies the thesis shows live in
`manifests/conda-forge-ocaml.toml`; `pixi run thesis-conda-write` records which
of them conda-forge publishes. This file keeps the reasoning, upstream state
and open decisions behind that list.

Goal: every OCaml tool and library Voblint builds with installs through
`pixi.toml`, so `ocaml-deps-install` (opam) and `ocaml/setup-ocaml` in CI can go.
Targets `osx-arm64`, `osx-64`, `linux-64`, matching `[workspace].platforms`.

Snapshot: 2026-11-20. Package tables below were written on 2026-09-18 from the
local opam switch (`~/.opam/5.4.1`), so their versions are known to build
Voblint; current conda-forge state is in "Status 2026-11-20" and the checklist.

## Status 2026-11-20

`pixi run thesis-conda-write` records 17 of the 25 manifest packages as
available on all three platforms. Still missing: `ocaml-findlib`,
`ocaml-zarith`, `ocaml-zarith-stubs-js`, `ocaml-dune-build-info`,
`ocamlformat`, `ocaml-js-of-ocaml-compiler`, `ocaml-js-of-ocaml`,
`ocaml-wasm-of-ocaml-compiler`.

conda-forge now ships `ocaml` 5.5.2 and `ocaml-dune` 3.25.0.

| Feedstock | From | State |
| --- | --- | --- |
| tier-0 libraries (10) | staged-recipes#34872 | merged 2026-10-13, published |
| `ocaml-ppxlib` | staged-recipes#35158 | published 0.38.0 build 1 on all platforms, win-64 gcc and vs2022 included |
| `ocaml-sedlex` | staged-recipes#35158 | published 3.7 for linux-64, osx-64, osx-arm64; MementoRC's #2 enables win and more linux arches |
| `ocaml-dune-configurator` | staged-recipes#35158 | published 3.24.2; MementoRC's #3 (more platforms, per-toolchain pins) green and mergeable |
| `ocaml-ocplib-endian` | staged-recipes#35158 | published 1.2 build 1 on all platforms |
| `ocaml-lwt-split` (`ocaml-lwt`, `ocaml-lwt-ppx`) | staged-recipes#35158 | published 6.1.2; MementoRC's #2 waits on dune-configurator#3 and fails on s390x (`gcc_linux-s390x 15.*` does not exist) |

lwt, dune-configurator and ocplib-endian are not Voblint dependencies; they came
from staged-recipes#35153 (semgrep, MementoRC, still open) because `lwt_ppx`
needs ppxlib.

Fixes after the first feedstock CI runs, all merged:

- win-64 builds exited 127 at the first `mkdir` in `build.sh`. `m2-bash` ships
  no `mkdir` or `cat`; they are in `m2-coreutils`. staged-recipes passed because
  its CI base env had coreutils on PATH. Each recipe now lists `m2-coreutils`.
- `ocaml-dune-configurator`, `ocaml-ocplib-endian` and `ocaml-lwt-split` had no
  `provider: osx_arm64: default`, so no osx-arm64 job existed. staged-recipes
  CI never builds osx-arm64, so it could not catch this.
- sedlex and lwt failed to solve because staged-recipes builds a PR's recipes in
  one job against each other, while the feedstocks build in parallel against the
  published channel. A CI restart after the dependency reached the CDN index
  (30-60 min after upload) fixed both.

Open problem: the first win-64 builds `ocaml-ppxlib-0.38.0-he42b7ba_0` and
`ocaml-dune-configurator-3.24.2-he42b7ba_0` are gcc-built but pin only
`ocaml >=5.5.1,<5.5.2.0a0`, without the toolchain track. sedlex#2's vs2022
lane resolved the gcc ppxlib and failed to link (`ppxlib_metaquot.lib` not
found; gcc ships `.a`). Mark both broken via admin-requests once
dune-configurator build 1 is published. ocaml-feedstock#224 (closes #223) makes
the `ocaml` run_export carry the track (`ocaml >=5.5.2,<5.5.3.0a0 gcc_*`), so
new builds get it without hand-written pins. #224 also renames the MSVC track
`vs2022` to `vs`; the MNT PRs above still use `vs2022`.

## Who needs what

| Consumer | pixi task | OCaml packages |
| --- | --- | --- |
| Native CLI, regressions, property tests | `cli-build`, `codegen-regression`, `property-test` | ocaml, dune, menhir/menhirLib, str (ships with ocaml), zarith |
| Browser build (wasm) for the pages site | `pages-site-build` input | js_of_ocaml, wasm_of_ocaml-compiler, zarith_stubs_js, binaryen |
| Formatting | `ocaml-format`, `ocaml-format-check` | ocamlformat 0.29.0 (pinned in `.ocamlformat`) |

## Already usable from conda-forge

Checked with `pixi exec --spec ocaml --spec ocaml-dune --spec ocaml-menhir
--spec ocaml-cppo --spec ocamlbuild --spec gmp`: the set resolves together on
osx-arm64 with OCaml 5.4.0.

| conda package | Version | Covers | Notes |
| --- | --- | --- | --- |
| `ocaml` | 5.4.0 | compiler, `str` | weak run-export `>=5.4.0,<5.4.1` |
| `ocaml-dune` | 3.24.2 build 2 | `dune` binary only | no `dune-configurator`, `dune-build-info`, `csexp` outputs; `dune --version` printed `n/a`. glibc and `OCAMLPATH` bugs fixed upstream |
| `ocaml-menhir` | 20250912 | menhir, menhirLib, menhirSdk, menhirCST | opam has 20260209; Voblint sets no lower bound |
| `ocaml-cppo` | 1.8.0 | cppo | not needed by Voblint directly |
| `ocamlbuild` | 0.16.1 | ocamlbuild | build dep of topkg-based packages |
| `gmp` | 6.3.0 | zarith C dep | |
| `binaryen` | 121 | wasm_of_ocaml | already in `pixi.toml` (`>=119`) |

## Existing feedstocks to update

| Feedstock | conda-forge now | Target | License | Blocks |
| --- | --- | --- | --- | --- |
| `ocaml-findlib` | 1.9.8 on linux-64 and osx-64, no osx-arm64 (2026-11-20) | osx-arm64 build | MIT | zarith, topkg chain, ocp-indent |
| `ocaml-zarith` | 1.12 (2021), no osx-arm64 (2026-11-20) | 1.14 | LGPL-2.0-only WITH OCaml-LGPL-linking-exception | native CLI |
| `ocaml-dune` | dune 3.25.0 only | add output `ocaml-dune-build-info` (same source, 3.x); `dune-configurator` became its own feedstock via staged-recipes#35158 | MIT | ocamlformat |
| `ocaml-menhir` | 20250912 | 20260209 (optional) | GPL-2.0-only / LGPL-2.0-only WITH exception | nothing |

ocamlfind 1.9.8 declares `ocaml < 5.5.0~`; a 5.5 migration needs the next
findlib release.

## New feedstocks

Naming follows the existing `ocaml-<opam name>` convention, `_` -> `-`.

### Shared libraries

| # | Feedstock | opam package | Version | License | OCaml deps (runtime) |
| --- | --- | --- | --- | --- | --- |
| 1 | `ocaml-csexp` | csexp | 1.5.2 | MIT | — |
| 2 | `ocaml-cmdliner` | cmdliner | 2.1.1 | ISC | — |
| 3 | `ocaml-sexplib0` | sexplib0 | v0.17.0 | MIT | — |
| 4 | `ocaml-stdlib-shims` | stdlib-shims | 0.3.0 | LGPL-2.1-only WITH exception | — |
| 5 | `ocaml-ppx-derivers` | ppx_derivers | 1.2.1 | BSD-3-Clause | — |
| 6 | `ocaml-compiler-libs` | ocaml-compiler-libs | v0.17.0 | MIT | — |
| 7 | `ocaml-ppxlib` | ppxlib | 0.38.0 | MIT | 3, 4, 5, 6 |
| 8 | `ocaml-gen` | gen | 1.1 | BSD-2-Clause | 15 |
| 9 | `ocaml-sedlex` | sedlex | 3.7 | MIT | 7, 8 |
| 10 | `ocaml-yojson` | yojson | 3.0.0 | BSD-3-Clause | — |
| 11 | `ocaml-re` | re | 1.14.0 | LGPL-2.1-or-later WITH exception | — |
| 15 | `ocaml-seq` | seq | 0.3.1 | LGPL-2.1-or-later WITH exception | — |

`ocaml-compiler-libs` risks reading as part of the compiler package; ask
conda-forge reviewers before claiming the name.

`ocaml-compiler-libs` (#6) was blocked by ocaml-feedstock#132 until 2026-09-18.
Fixed by #134 in `ocaml` build 8, verified against the published package. It is
now in staged-recipes#34872 and builds. **Tiers 1-3 are no longer gated on
anything upstream.**

`ocaml-seq` (15) is upstream's compatibility shim. `Seq` has been in the stdlib
since 4.07 and the package installs only a META, but `gen` declares
`(libraries seq)` and will not build without it.

### Browser build

| # | Feedstock | Outputs | Version | License | Deps |
| --- | --- | --- | --- | --- | --- |
| 12 | `ocaml-js-of-ocaml` | `ocaml-js-of-ocaml-compiler`, `ocaml-js-of-ocaml`, `ocaml-wasm-of-ocaml-compiler` | 6.4.1 | GPL-2.0-or-later, LGPL-2.1-or-later WITH exception | 2, 6, 7, 9, 10, menhir, binaryen (wasm output) |
| 13 | `ocaml-zarith-stubs-js` | — | needs release | MIT | — |

All three js_of_ocaml outputs come from one repo at one version
(`js_of_ocaml {= version}`), so one feedstock with multiple outputs matches
upstream. js_of_ocaml-compiler 6.4.1 caps `ocaml < 5.6`.

**Blocker (#13):** `voblint.opam` pins zarith_stubs_js to
`c8e2e3eb062eee373625f9aecca88168103e4e93` because v0.17.0 lacks the wasm
runtime declaration. conda-forge builds from release tarballs. Options: ask
Jane Street for a tagged release, or carry the upstream diff as a recipe patch
on v0.17.0 (acceptable on conda-forge if the patch is an upstream commit).

### Formatter

| # | Feedstock | Version | License |
| --- | --- | --- | --- |
| 14 | `ocamlformat` | 0.29.0 | MIT, LGPL-2.1-only WITH exception |

ocamlformat pulls deps nothing else here uses:

| opam package | Version | License | Build system |
| --- | --- | --- | --- |
| base | v0.17.3 | MIT | dune (+ dune-configurator) |
| ocaml_intrinsics_kernel | v0.17.1 | MIT | dune |
| stdio | v0.17.0 | MIT | dune |
| dune-build-info | 3.22.0 | MIT | dune |
| either | 1.0.0 | MIT | dune |
| fix | 20250919 | LGPL-2.0-only | dune |
| ocaml-version | 4.0.4 | ISC | dune |
| ocp-indent | 1.9.0 | LGPL-2.1-only WITH exception | dune (+ findlib) |
| camlp-streams | 5.0.1 | LGPL-2.1-only WITH exception | dune |
| astring | 0.8.5 | ISC | topkg |
| fpath | 0.7.3 | ISC | topkg |
| topkg | 1.1.1 | ISC | ocamlbuild + findlib |
| uutf | 1.0.4 | ISC | topkg |
| uucp | 17.0.0 | ISC | topkg |
| uuseg | 17.0.0 | ISC | topkg |

It also uses the shared 1, 2, 11, menhir.

**Decision open:** bundle these into the `ocamlformat` recipe as extra
sources (one feedstock, binary output, no OCaml run dep) or split them into
~15 more `ocaml-*` feedstocks. Bundling avoids OCaml-bump rebuild cascades for
a leaf tool; splitting is what a reviewer may ask for if the libraries have
other users. Default: bundle.

## Upstream status

All blockers resolved 2026-09-17/18. MementoRC fixed both reported bugs within a
day of filing.

| Item | Where | State |
| --- | --- | --- |
| `ocaml-dune` needs glibc 2.38 undeclared | ocaml-dune-feedstock#17 | merged, published as build 1/2 |
| cross bootstrap misses `boot/pps.ml` | ocaml-dune-feedstock#18 | merged |
| `OCAMLPATH` exposes only the active env | ocaml-dune-feedstock#19 | fixed by #20, published |
| `ocamlcommon.cmxa` NUL-padded `-L` | ocaml-feedstock#132 | fixed by #134, `ocaml` build 8, published |
| macOS `CONDA_OCAML_*` point at a nonexistent `-gcc` | ocaml-feedstock#101 | closed 2026-09-24; not yet checked whether the workaround below can go |
| tier 0 recipes (10 packages) | staged-recipes#34872 | merged 2026-10-13 |
| ppxlib, sedlex, lwt, dune-configurator, ocplib-endian | staged-recipes#35158 | merged 2026-11-19 |
| `ocaml-patricia-tree` | staged-recipes#34850 | open, ready for review since 2026-09-17 |
| findlib osx-arm64 | ocaml-findlib-feedstock#20 (cross lanes), #19 (ARM migrator) | open |
| zarith 1.14 + osx-arm64 | ocaml-zarith-feedstock#7 | open, needs findlib on osx-arm64 |
| win toolchain track in the `ocaml` run_export | ocaml-feedstock#223 / #224 | #224 open, CI green, reviewers isuruf and dslarm |
| zarith_stubs_js release with the wasm runtime | janestreet/zarith_stubs_js#16 | open since 2026-09-14, no reply; `main` is at `v0.18~preview`, so the fix likely ships with Jane Street's v0.18 batch (no date announced) |

MementoRC is listed as co-maintainer on all ten tier-0 recipes.

Only workaround still carried: every recipe exports `CONDA_OCAML_CC`/`MKEXE`/`MKDLL`
on osx for #101. Needed by all of them, not just those linking executables,
because dune builds a `.cmxs` for every public library. Remove once #101 lands.

Recipe conventions settled while building these:

- `${{ stdlib("c") }}` only. `${{ compiler("c") }}` is redundant because
  `${{ compiler("ocaml") }}` already pulls the C toolchain and its activation.
  Verified on both linux and osx.
- a library whose generated META has a non-empty `requires` needs those packages
  in `run`, not only `host`. `ocaml-gen` needs `ocaml-seq` for this reason.

## Build order

```text
tier 0  ocaml-findlib*  ocaml-dune*(+configurator, build-info)  csexp  cmdliner
        sexplib0  stdlib-shims  ppx-derivers  compiler-libs  gen  yojson  re
tier 1  ocaml-zarith*  ppxlib
tier 2  sedlex
tier 3  js-of-ocaml (3 outputs)          ocamlformat (bundled)
tier 4  zarith-stubs-js (after release or patch)
```

`*` = update to an existing feedstock. Tier-0 packages go into one
staged-recipes PR where possible; staged-recipes builds them in dependency
order.

## Upkeep

- Every OCaml patch release: the `ocaml` run-export pin triggers a migration
  PR on each library feedstock (1–13). Merging is manual unless automerge is
  enabled.
- ocamlformat bundled: rebuild only on its own release (~2/year).
- Voblint's `.ocamlformat` pin and `pixi.toml` pin must move together.

## Checklist

- [ ] Decide ocamlformat bundle vs split
- [ ] Ask conda-forge (`@conda-forge/ocaml`) about `ocaml-compiler-libs` naming
- [x] Ask upstream for a zarith_stubs_js release with the wasm runtime (janestreet/zarith_stubs_js#16)
- [ ] zarith_stubs_js: wait for v0.18, or patch v0.17.0 with the upstream wasm commits (`58891805`, `b1403f31`; check they apply)
- [ ] `ocaml-findlib` 1.9.8 PR
- [x] Report `OCAMLPATH` gap (ocaml-dune#19) and `.cmxa` relocation (ocaml#132)
- [x] Submit `ocaml-compiler-libs` (in #34872)
- [ ] Drop the osx `CONDA_OCAML_*` workaround (ocaml-feedstock#101 closed 2026-09-24; recheck)
- [x] Unskip win: ppxlib, dune-configurator, ocplib-endian, lwt build win-64 (gcc track); sedlex via MementoRC's #2
- [ ] `ocaml-zarith` 1.14 PR merged (#7 open)
- [ ] `ocaml-dune` output `ocaml-dune-build-info`
- [x] staged-recipes: tier 0 new packages (#34872, merged 2026-10-13)
- [x] staged-recipes: ppxlib (#35158, merged 2026-11-19)
- [x] staged-recipes: sedlex (#35158, merged 2026-11-19)
- [x] Feedstock fixes after first CI: `m2-coreutils` on win, osx-arm64 lanes (ppxlib#1, dune-configurator#1, ocplib-endian#1, lwt-split#1)
- [ ] Mark win-64 `he42b7ba_0` builds of ppxlib and dune-configurator broken (no toolchain track)
- [ ] Review ocaml-feedstock#224 (asked by MementoRC)
- [ ] staged-recipes: js-of-ocaml 6.4.1 (#35750, draft; local osx-arm64 build and tests pass; merge after win is enabled once sedlex has win-64)
- [ ] staged-recipes: ocamlformat
- [ ] staged-recipes: zarith-stubs-js
- [x] Local `rattler-build` pass on osx-arm64 for each recipe before PR (#35158 recipes and the feedstock fixes)
- [ ] Switch `pixi.toml` native stack (ocaml, ocaml-dune, ocaml-menhir, ocaml-zarith)
- [ ] Switch browser stack; drop `pin-depends` from `voblint.opam`
- [ ] Switch ocamlformat; drop `ocaml/setup-ocaml` from CI
- [ ] Delete `ocaml-deps-install` or keep `voblint.opam` for opam users
