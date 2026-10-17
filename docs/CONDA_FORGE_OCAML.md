# conda-forge OCaml packaging tracker

Working notes on moving the OCaml toolchain from opam to conda-forge. The
package list and dependencies the thesis shows live in
`manifests/conda-forge-ocaml.toml`; `pixi run thesis-conda-write` records which
of them conda-forge publishes. This file keeps the reasoning, upstream state
and open decisions behind that list.

Goal: the OCaml tools and libraries Voblint builds with install through
`pixi.toml`, so `ocaml-deps-install` (opam) and `ocaml/setup-ocaml` in CI can
shrink to the formatter. Targets `osx-arm64`, `osx-64`, `linux-64`, matching
`[workspace].platforms`.

Snapshot: 2026-10-14. Versions are what the local opam switch (`~/.opam/5.4.1`)
has installed, so they are known to build Voblint.

## Who needs what

| Consumer | pixi task | OCaml packages |
| --- | --- | --- |
| Native CLI, regressions, property tests | `cli-build`, `codegen-regression`, `property-test` | ocaml, dune, menhir/menhirLib, str (ships with ocaml), zarith |
| Browser build (wasm) for the pages site | `pages-site-build` input | js_of_ocaml, wasm_of_ocaml-compiler, zarith_stubs_js, binaryen |
| Formatting | `ocaml-format`, `ocaml-format-check` | ocamlformat 0.29.0 (pinned in `.ocamlformat`) |

**Scope decision (2026-10-13):** ocamlformat is deferred and stays on opam.
`ocaml/setup-ocaml` remains in CI for the format check only. This drops the
dune extra outputs and the ~15-package ocamlformat stack from the plan.

## Remaining path

```text
native   findlib 1.9.8 (ocaml-findlib-feedstock#15) + osx-arm64 for findlib
           -> zarith 1.14 (ocaml-zarith-feedstock#7, draft)
           -> switch pixi.toml native stack

browser  ppxlib + sedlex (staged-recipes#35158, in review)
           -> js-of-ocaml (3 outputs, staged-recipes)
         zarith-stubs-js (upstream release or patch)
           -> switch browser stack, drop pin-depends
```

Next blockers:

1. **staged-recipes#35158** (ppxlib, sedlex): CI and linter green, out of
   draft, `help-c-cpp` pinged 2026-10-13. Waiting on review.
2. **findlib**: #15 (1.9.8, recipe v1) is open and waits on isuruf or slel.
   #16-#18 were closed on 2026-10-13, so nothing adds osx-arm64; the bot's
   "ARM OSX Migrator" #12 has been open since January. zarith#7 needs both.
   isuruf removed MementoRC as maintainer of findlib and zarith.
3. **zarith-stubs-js**: janestreet/zarith_stubs_js#16 (filed 2026-09-14) has no
   reply. Latest tag is still v0.17.0.

## Published on conda-forge

All published for `linux-64`, `osx-64` and `osx-arm64`.

| conda package | Version | Covers | Notes |
| --- | --- | --- | --- |
| `ocaml` | 5.4.0 | compiler, `str` | weak run-export `>=5.4.0,<5.4.1` |
| `ocaml-dune` | 3.24.2 | `dune` binary only | no `dune-configurator`, `dune-build-info`, `csexp` outputs |
| `ocaml-menhir` | 20250912 | menhir, menhirLib, menhirSdk, menhirCST | opam has 20260209; Voblint sets no lower bound |
| `ocaml-cppo` | 1.8.0 | cppo | not needed by Voblint directly |
| `ocamlbuild` | 0.16.1 | ocamlbuild | build dep of topkg-based packages |
| `gmp` | 6.3.0 | zarith C dep | |
| `binaryen` | 121 | wasm_of_ocaml | already in `pixi.toml` (`>=119`) |
| `ocaml-csexp` | 1.5.2 | csexp | staged-recipes#34872 |
| `ocaml-cmdliner` | 2.1.1 | cmdliner | staged-recipes#34872 |
| `ocaml-sexplib0` | v0.17.0 | sexplib0 | staged-recipes#34872 |
| `ocaml-stdlib-shims` | 0.3.0 | stdlib-shims | staged-recipes#34872 |
| `ocaml-ppx-derivers` | 1.2.1 | ppx_derivers | staged-recipes#34872 |
| `ocaml-compiler-libs` | v0.17.0 | ocaml-compiler-libs | staged-recipes#34872 |
| `ocaml-seq` | 0.3.1 | seq | staged-recipes#34872 |
| `ocaml-gen` | 1.1 | gen | staged-recipes#34872 |
| `ocaml-yojson` | 3.0.0 | yojson | staged-recipes#34872 |
| `ocaml-re` | 1.14.0 | re | staged-recipes#34872 |

The ten #34872 packages were merged 2026-10-13. Staged-recipes created their
feedstocks for `linux-64` and `osx-64` only; osx-arm64 was added by one manual
PR per feedstock (`provider: osx_arm64: default`, native `macOS-15-arm64`
runner), all merged the same day. We are listed maintainers on all ten, so
manual PRs were faster than the pinning-feedstock `osx_arm64.txt` migrator,
which produces the same `conda-forge.yml` change but waits on core review and
bot cadence.

## In review

| Feedstock | Version | License | Deps | Where |
| --- | --- | --- | --- | --- |
| `ocaml-ppxlib` | 0.38.0 | MIT | sexplib0, stdlib-shims, ppx-derivers, compiler-libs | staged-recipes#35158 |
| `ocaml-sedlex` | 3.7 | MIT | ppxlib, gen | staged-recipes#35158 |
| `ocaml-patricia-tree` | | | | staged-recipes#34850 (open since 2026-09-17) |

Both #35158 recipes carry a `conda-forge.yml` with `provider: osx_arm64:
default`, which staged-recipes merges into the new feedstock, so they start
with osx-arm64 and need no follow-up PR. Both built and passed their strict
`package_contents` tests locally on osx-arm64 and in CI on linux-64 and osx-64.

**Open license question:** ppxlib's `astlib` contains 15 files copied from the
OCaml compiler under LGPL-2.1 with the OCaml linking exception; upstream
declares MIT only. The recipe keeps `license: MIT` to match upstream. If a
reviewer asks, switch to `MIT AND LGPL-2.1-only WITH
OCaml-LGPL-linking-exception` and package the OCaml license file.

## Still to package

### Existing feedstocks

| Feedstock | conda-forge now | Target | Owner | Blocks |
| --- | --- | --- | --- | --- |
| `ocaml-findlib` | 1.8.1, OCaml 4.14 only, no osx-arm64 | 1.9.8 | #15 (MementoRC); osx-arm64 open (#12) | zarith |
| `ocaml-zarith` | 1.12 (2021), OCaml 4.11 only, no osx-arm64 | 1.14 | #7 (us, draft) | native CLI |

ocamlfind 1.9.8 declares `ocaml < 5.5.0~`; a 5.5 migration needs the next
findlib release.

ocaml-zarith-feedstock#7 is a v1 recipe for 1.14 with osx-arm64, superseding
bot PRs #3 and #4. It builds and passes its tests locally on osx-arm64 against
findlib 1.9.8 built from MementoRC's branch, and stays a draft until findlib
1.9.8 is published for all three platforms. Then rerun CI, mark it ready and
ask isuruf for review. Maintainer: isuruf only. Windows is skipped.

The recipe builds with `LIBS=-lgmp LDFLAGS=` and `LIBRARY_PATH=$PREFIX/lib` so
that `ocamlmklib` records no `-L` in `zarith.cma`/`.cmxa`, and its package test
checks that with `ocamlobjinfo`. See "Prefix paths in OCaml archives" below.

### Browser build

| Feedstock | Outputs | Version | License | Deps |
| --- | --- | --- | --- | --- |
| `ocaml-js-of-ocaml` | `ocaml-js-of-ocaml-compiler`, `ocaml-js-of-ocaml`, `ocaml-wasm-of-ocaml-compiler` | 6.4.1 | GPL-2.0-or-later, LGPL-2.1-or-later WITH exception | cmdliner, compiler-libs, ppxlib, sedlex, yojson, menhir, binaryen (wasm output) |
| `ocaml-zarith-stubs-js` | | needs release | MIT | |

All three js_of_ocaml outputs come from one repo at one version
(`js_of_ocaml {= version}`), so one feedstock with multiple outputs matches
upstream. js_of_ocaml-compiler 6.4.1 caps `ocaml < 5.6`. Starts once sedlex is
published.

**Blocker (zarith-stubs-js):** `voblint.opam` pins zarith_stubs_js to
`c8e2e3eb062eee373625f9aecca88168103e4e93` because v0.17.0 lacks the wasm
runtime declaration. conda-forge builds from release tarballs. Options: wait
for janestreet/zarith_stubs_js#16, or package v0.17.0 with the upstream commit
as a recipe patch (acceptable on conda-forge when the patch is an upstream
commit).

### Deferred: ocamlformat

Not pursued for now. For reference, ocamlformat 0.29.0 needs, beyond shared
packages already published (csexp, cmdliner, re, menhir):

| opam package | Version | License | Build system |
| --- | --- | --- | --- |
| dune-build-info | 3.22.0 | MIT | dune (new `ocaml-dune` output) |
| base | v0.17.3 | MIT | dune (+ dune-configurator, new `ocaml-dune` output) |
| ocaml_intrinsics_kernel | v0.17.1 | MIT | dune |
| stdio | v0.17.0 | MIT | dune |
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

MementoRC's semgrep work (staged-recipes#35153, opened 2026-10-12, lists us as
co-maintainer) adds topkg, astring, fpath, uutf and uucp among 13 dbuenzli
libraries, with more announced. If that lands, ocamlformat may become a small
leaf recipe instead of a bundle; revisit then.

## Upstream fixes

| Item | Where | State |
| --- | --- | --- |
| `ocaml-dune` needs glibc 2.38 undeclared | ocaml-dune-feedstock#17 | merged |
| cross bootstrap misses `boot/pps.ml` | ocaml-dune-feedstock#18 | merged |
| `OCAMLPATH` exposes only the active env | ocaml-dune-feedstock#19 | fixed by #20 |
| `ocamlcommon.cmxa` NUL-padded `-L` | ocaml-feedstock#132 | fixed by #134, `ocaml` build 8 |
| macOS `CONDA_OCAML_*` point at a nonexistent `-gcc` | ocaml-feedstock#101 | closed 2026-09-24; workaround dropped from all recipes |
| `ocamlmklib` calls compilers from the feedstock's build dir | ocaml-feedstock#188 | fixed by #189, `ocaml` build 11; zarith workaround dropped |
| `ocamlmklib` records `-L$PREFIX/lib` in archives | ocaml-feedstock#191 | open, filed 2026-10-14 with a tested patch |
| warn on prefix paths in OCaml archives | prefix-dev/rattler-build#2866 | open; wolfv points to a fix in the `ocaml` package |

### Prefix paths in OCaml archives

`.cma`/`.cmxa` store their C link flags as marshalled strings, and
`ocamlmklib -L<dir>` records `<dir>` there. With the default `LDFLAGS` that is
`-L$PREFIX/lib`, so the archive is marked for binary prefix replacement. On
install, relocation pads up to the next NUL byte, which in marshalled data lies
past the end of the string. Tested on zarith 1.14 (osx-arm64, pixi): the
relocated archive lost `-lzarith` from its C objects and its dllibs, native
links fail with `Invalid argument` and bytecode links with `The external
function ml_z_equal is not available`. Truncating flags at NUL cannot repair
that.

A patched `ocamlmklib` that keeps `-L$PREFIX/lib` for its own C link but does
not record it fixed zarith, given `-L$PREFIX/lib` in the link wrappers during
the build (or `LIBRARY_PATH`). Separately, `conda-ocaml-mkdll` never adds
`-L$CONDA_PREFIX/lib`, so `ocamlopt -shared` against zarith fails in user envs
even with #7's package. Both are in #191. Test packages, the patched
`ocamlmklib` and scripts are in the session scratchpad, not the repo.

MementoRC is promoting an ocaml-feedstock refactor in stacked PRs #178-#187
(new architecture lanes, including an osx-arm64 -> osx-64 reciprocal cross
lane in #182). Downstream library feedstocks build natively and do not depend
on it.

Recipe conventions settled while building these:

- `${{ stdlib("c") }}` only. `${{ compiler("c") }}` is redundant because
  `${{ compiler("ocaml") }}` already pulls the C toolchain and its activation.
- a library whose installed META has a non-empty `requires` needs those
  packages in `run`, not only `host`. `ocaml-gen` needs `ocaml-seq`; ppxlib and
  sedlex carry their META requirements as run deps.
- per-recipe `conda-forge.yml` with `provider: osx_arm64: default` gives a new
  feedstock osx-arm64 from its first build, once its deps exist there.
- rerender with the current conda-smithy (2026.9.23 at time of writing).
- a library built with `ocamlmklib` must not record a prefix `-L` in its
  archives until #191 is fixed: build with `LDFLAGS=` plus `LIBRARY_PATH`, and
  check `ocamlobjinfo` in the package test.

## Lessons from round 1

- A feedstock whose dependency comes from the same staged-recipes PR can fail
  its first build if it starts before that dependency is uploaded (`ocaml-gen`
  vs `ocaml-seq`). Rerun after the dependency is published.
- Upload to anaconda.org is not availability: the conda-forge CDN index lagged
  35-50 minutes on 2026-10-13. Check with an empty solver cache
  (`PIXI_CACHE_DIR=$(mktemp -d) pixi search -p <subdir> <pkg>`) before
  rerunning dependent CI.
- A merge to a feedstock's main does not always trigger Azure (stdlib-shims);
  an empty-commit PR fixes it.
- Azure macOS runners occasionally fail with `curl: (6) Could not resolve host:
  github.com` before the build starts. Infrastructure flake; nothing to fix.

## Upkeep

- Every OCaml patch release: the `ocaml` run-export pin triggers a migration
  PR on each library feedstock. Merging is manual unless automerge is enabled.
- We co-maintain the #34872 feedstocks, #35158 once merged, and the #35153
  feedstocks if listed there.

## Checklist

- [x] Report `OCAMLPATH` gap (ocaml-dune#19) and `.cmxa` relocation (ocaml#132)
- [x] staged-recipes: tier 0 base libraries (#34872, merged 2026-10-13)
- [x] osx-arm64 on the ten #34872 feedstocks (merged 2026-10-13)
- [x] Drop the osx `CONDA_OCAML_*` workaround (ocaml-feedstock#101 closed)
- [x] Decide ocamlformat: deferred, stays on opam
- [ ] staged-recipes: ppxlib + sedlex (#35158, in review)
- [ ] Settle ppxlib license if a reviewer raises it
- [ ] `ocaml-findlib` 1.9.8 (#15) and osx-arm64 for findlib
- [x] `ocaml-zarith` 1.14 PR (#7, v1, osx-arm64), draft until findlib is published
- [ ] Mark zarith#7 ready once findlib 1.9.8 is on all three platforms
- [x] Report the `ocamlmklib` archive `-L` (ocaml-feedstock#191, rattler-build#2866)
- [ ] staged-recipes: js-of-ocaml (after sedlex is published)
- [ ] staged-recipes: zarith-stubs-js (after release, or with patch)
- [x] Reply on staged-recipes#35153: confirm co-maintainership, share our plan
- [ ] Ask conda-forge (`@conda-forge/ocaml`) about `ocaml-compiler-libs` naming
- [ ] Consider unskipping win
- [ ] Switch `pixi.toml` native stack (ocaml, ocaml-dune, ocaml-menhir, ocaml-zarith)
- [ ] Switch browser stack; drop `pin-depends` from `voblint.opam`
- [ ] Decide whether `ocaml-deps-install` stays for ocamlformat and opam users
