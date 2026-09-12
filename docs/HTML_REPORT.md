# The HTML result viewer

`--html` writes a browsable result directory. The graph stays sparse, and each
node's full abstract state lives in its own document you reach by clicking that
node.

```bash
pixi run voblint --analysis int --html FILE.vimp
pixi run html-report-serve
```

`pixi run html-report-serve` serves the existing `build/report/` on
<http://localhost:8080/index.xml> and opens it without changing its contents.
`pixi run html-report-serve DIR` serves a custom report directory;
`OUTDIR=DIR` also overrides the default. `PORT=9000` moves the port,
and `NO_OPEN=1` skips the browser. If no report exists, the task asks you to
generate one first.

`--html` writes `build/report/`; `--html-out DIR`
overrides the location. It needs `dot` on PATH and the `vendor/g2html`
submodule.

## Why a separate viewer at all

A product domain does not fit on a graph. `--analysis int` prints one variable
as `sign=Positive, ivl=[1,1], parity=Odd, congruence==1`, and a whole program of
those is unreadable. The XML report separates graph from state the way Goblint's
own HTML output does.

`--analysis` takes a comma list, which puts every named domain in the same
report, one `<analysis>` block per node, which is the element Goblint uses for
exactly this. `--analysis int,interval,sign,parity` shows `int: PROVED` beside
`interval: UNKNOWN` on the same node, so a precision claim is readable in place
instead of across four runs. It needs `--html` and `--context none`: node
identifiers depend on the context, so they only agree across domains when the
context does.

The entry point is `index.xml`, not an `.html` file, and it renders only when
served, because browsers refuse to apply its stylesheet over `file://`.

The frontend is [g2html](https://github.com/goblint/g2html)'s `resources/`,
vendored as the `vendor/g2html` submodule and used unmodified: Voblint emits the
XML vocabulary its stylesheets already consume. A web server is required because
browsers refuse the cross-document loads that frontend performs over `file://`
-- the same reason Goblint's own documentation says to serve its result
directory.

## Browser XSLT is being removed

Chrome removes XSLT in M155/M158 (November 2026); Firefox and Safari have
announced the same direction. This frontend depends on it at every level:
`index.xml` carries an `<?xml-stylesheet?>` processing instruction, and each
pane is an `<iframe src="....xml">` whose stylesheet the browser applies on
load. When XSLT goes, the report renders as raw XML.

Nothing here works around it yet, and the workaround is not a script tag.
Three routes, none free:

* **Run g2html proper.** The vendored submodule is a *converter*, "Goblint XML
  result to HTML converter", and emitting static HTML is what it is for.
  Deprecation-proof and uses the stylesheets unmodified, at the cost of a JDK
  and `ant` in the toolchain.
* **Pre-render here.** `xsltproc` (from `libxslt`) can transform each document,
  but `script.js` sets iframe sources to `.xml` paths, so the frontend would
  have to be patched rather than vendored unmodified, and being unmodified is
  what makes it Goblint's viewer rather than a fork of it.
* **Polyfill.** A WASM libxslt shim restores the browser API, at the cost of
  committing a JavaScript/WASM blob, the thing the submodule exists to avoid.

Until then, any browser that still applies XSLT renders the report.
