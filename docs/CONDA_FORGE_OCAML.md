# conda-forge OCaml packaging tracker

f
Local working notes, excluded via `.git/info/exclude`. Not committed.

Goal: every OCaml tool and library Voblint builds with installs through
`pixi.toml`, so `ocaml-deps-install` (opam) and `ocaml/setup-ocaml` in CI can go.
Targets `osx-arm64`, `osx-64`, `linux-64`, matching `[workspace].platforms`.

Snapshot: 2026-09-18. Versions in the tables are what the local opam switch
(`~/.opam/5.4.1`) has installed, so they are known to build Voblint.

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
| `ocaml-findlib` | 1.8.1, OCaml 4.14 only, no osx-arm64 | 1.9.8 | MIT | zarith, topkg chain, ocp-indent |
| `ocaml-zarith` | 1.12 (2021), OCaml 4.11 only, no osx-arm64 | 1.14 | LGPL-2.0-only WITH OCaml-LGPL-linking-exception | native CLI |
| `ocaml-dune` | dune only | add outputs `ocaml-dune-configurator`, `ocaml-dune-build-info` (same source, 3.x) | MIT | ppxlib-free chain via `base`; ocamlformat |
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
| macOS `CONDA_OCAML_*` point at a nonexistent `-gcc` | ocaml-feedstock#101 | still open; workaround still needed |
| tier 0 recipes (10 packages) | staged-recipes#34872 | ready for review, CI green, `help-c-cpp` pinged |
| `ocaml-patricia-tree` | staged-recipes#34850 | ready for review since 2026-09-17 |

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
- [ ] Ask upstream for a zarith_stubs_js release with the wasm runtime
- [ ] `ocaml-findlib` 1.9.8 PR
- [x] Report `OCAMLPATH` gap (ocaml-dune#19) and `.cmxa` relocation (ocaml#132)
- [x] Submit `ocaml-compiler-libs` (in #34872)
- [ ] Drop the osx `CONDA_OCAML_*` workaround once ocaml-feedstock#101 lands
- [ ] Consider unskipping win once tier 0 is merged
- [ ] `ocaml-zarith` 1.14 PR
- [ ] `ocaml-dune` extra outputs PR
- [x] staged-recipes: tier 0 new packages (#34872, ready for review, green)
- [ ] staged-recipes: ppxlib
- [ ] staged-recipes: sedlex
- [ ] staged-recipes: js-of-ocaml
- [ ] staged-recipes: ocamlformat
- [ ] staged-recipes: zarith-stubs-js
- [ ] Local `rattler-build` pass on osx-arm64 for each recipe before PR
- [ ] Switch `pixi.toml` native stack (ocaml, ocaml-dune, ocaml-menhir, ocaml-zarith)
- [ ] Switch browser stack; drop `pin-depends` from `voblint.opam`
- [ ] Switch ocamlformat; drop `ocaml/setup-ocaml` from CI
- [ ] Delete `ocaml-deps-install` or keep `voblint.opam` for opam users
