#!/usr/bin/env python3
"""Emit a result directory that Goblint's HTML frontend can browse.

Prototype for issue #146. The frontend is g2html's `resources/` (vendored at
vendor/g2html), used unmodified: this script only writes the XML and graph
artifacts those stylesheets already consume, in the layout Goblint's own
`result=html` output produces.

    result/
      index.xml                  report.xsl   -- entry point
      nodes/<id>.xml             node.xsl     -- one document per CFG node
      nodes/globals.xml          globals.xsl
      files/<src>.xml            file.xsl     -- source listing
      dot/<src>/<fun>.dot
      cfgs/<src>/<fun>.svg       rendered by `dot -Tsvg`
      <g2html resources/ copied in>

Abstract states live in nodes/<id>.xml, never in DOT node labels -- that
separation is the point of the exercise, and what keeps the CFG legible for a
product domain like int_dom.

This reads voblint's --graph-snapshot output, which is the graph the Isabelle
side already builds internally, serialized as text. Parsing it back is
prototype scaffolding: the emitter moves into cli/ once that graph is exported
as a value rather than as rendered text.
"""

import argparse
import html
import re
import shutil
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
ASSETS = REPO_ROOT / "vendor" / "g2html" / "resources"


# --------------------------------------------------------------------------
# --graph-snapshot -> graph
# --------------------------------------------------------------------------

def parse_snapshot(text):
    clusters, nodes, edges = [], {}, []
    section = cur_cluster = cur_node = None
    for raw in text.splitlines():
        if not raw.strip():
            continue
        if raw[0] not in " \t":
            section = raw.rstrip(":")
            continue
        indent = len(raw) - len(raw.lstrip())
        line = raw.strip()
        if section == "clusters":
            if indent == 2 and line.endswith(":"):
                cur_cluster = {"id": line[:-1], "nodes": []}
                clusters.append(cur_cluster)
            elif cur_cluster is not None:
                cur_cluster["nodes"].append(line)
        elif section == "nodes":
            if indent == 2:
                nid, _, label = line.partition(": ")
                cur_node = {"id": nid, "label": label, "state": []}
                nodes[nid] = cur_node
            elif cur_node is not None:
                var, _, val = line.partition("=")
                cur_node["state"].append((var, val))
        elif section == "edges":
            m = re.match(r"(\S+) -> (\S+)(?:: (.*))?$", line)
            if m:
                edges.append({"src": m.group(1), "dst": m.group(2),
                              "label": m.group(3) or ""})
    return clusters, nodes, edges


# A product domain renders flat: "sign=Top, ivl=[-inf,+inf], parity=Top,
# congruence==0 (mod 1)". Split it back into components so node.xsl gets a
# nested <map> to fold, instead of one wide line. Splitting only before a
# "word=" keeps interval bounds like [-inf,+inf] intact.
COMPONENT = re.compile(r",\s+(?=[a-z_]+=)")


def components(value):
    out = []
    for part in COMPONENT.split(value):
        k, sep, v = part.partition("=")
        if not sep:
            return None
        out.append((k, v))
    return out or None


# --------------------------------------------------------------------------
# graph -> result/
# --------------------------------------------------------------------------

def esc(s):
    return html.escape(str(s), quote=True)


def xmlify(name):
    """Goblint's path-segment escaping for file names used as directories."""
    return name.replace("/", "%2F")


def node_xml(node, source_file, fun, analysis):
    """One <loc><call> document, in the vocabulary node.xsl matches.

    <map> is alternating <key>/value siblings; node.xsl folds a value holding
    a nested <map> and renders it inline otherwise.
    """
    body = ["<map>"]
    for var, val in node["state"]:
        body.append(f"<key>{esc(var)}</key>")
        comps = components(val)
        if comps:
            body.append("<value><map>")
            for k, v in comps:
                body.append(f"<key>{esc(k)}</key><value>{esc(v)}</value>")
            body.append("</map></value>")
        else:
            body.append(f"<value>{esc(val)}</value>")
    body.append("</map>")
    inner = "\n".join(body)
    # node.xsl only displays the location attributes; VIMP has no source spans
    # to fill them with yet, so they stay at zero and the source view stays
    # unlinked (issue #146 phase 2).
    return f"""<?xml version="1.0" ?>
<?xml-stylesheet type="text/xsl" href="../node.xsl"?>
<loc><call id="{esc(node['id'])}" file="{esc(source_file)}" fun="{esc(fun)}" \
line="0" order="0" column="0" endLine="0" endColumn="0" synthetic="false">
<context><analysis name="program point"><value>{esc(node['label'])}</value></analysis></context>
<path>
<analysis name="{esc(analysis)}"><value>
{inner}
</value></analysis>
</path>
</call></loc>
"""


def index_xml(source_file, funs):
    fs = "\n".join(f'<function name="{esc(f)}"/>' for f in funs)
    return f"""<?xml version="1.0" ?>
<?xml-stylesheet type="text/xsl" href="report.xsl"?>
<report><file name="{esc(source_file)}">
{fs}
</file></report>
"""


def globals_xml():
    return """<?xml version="1.0" ?>
<?xml-stylesheet type="text/xsl" href="../globals.xsl"?>
<globs><analysis name="globals"><value><map></map></value></analysis></globs>
"""


def file_xml(source_text):
    """Source listing for file.xsl.

    ns/wrn are spliced verbatim into an onclick="select_line(nr,ns,wrn)"
    attribute, so they must read as JS array literals. Both stay empty while
    VIMP carries no source spans: with no positions there is nothing to map a
    line back to a CFG node with.
    """
    lines = [f'<ln nr="{i}" ns="[]" wrn="[]" ded="false">{esc(text)}</ln>'
             for i, text in enumerate(source_text.splitlines(), start=1)]
    body = "\n".join(lines)
    return f"""<?xml version="1.0" ?>
<?xml-stylesheet type="text/xsl" href="../file.xsl"?>
<file>
{body}
</file>
"""


def html_dot(clusters, nodes, edges):
    """DOT carrying short labels and the frontend's click hooks.

    id/URL mirror goblint's cfgTools.fprint_fundec_html_dot: graphviz turns
    them into <g id="a_N"><a xlink:href="javascript:show_info('N')">, which is
    the handle script.js selects on to load and highlight a node.
    """
    out = ["digraph AnalysisCFG {",
           '  graph [rankdir=TB,newrank=true,splines=polyline,nodesep=0.4,'
           'ranksep=0.5,fontname="Menlo"];',
           '  node [shape=box,style=filled,fillcolor=white,fontname="Menlo",'
           'fontsize=11,id="\\N",URL="javascript:show_info(\'\\N\');"];',
           '  edge [fontname="Menlo",fontsize=9,arrowsize=0.7];']
    for c in clusters:
        out.append(f"  subgraph {c['id']} {{")
        out.append("    style=rounded; color=gray70;")
        for nid in c["nodes"]:
            label = nodes[nid]["label"] if nid in nodes else nid
            out.append(f'    {nid} [label="{label}"];')
        out.append("  }")
    for e in edges:
        label = e["label"].replace('"', '\\"')
        out.append(f'  {e["src"]} -> {e["dst"]} [label="{label}"];')
    out.append("}")
    return "\n".join(out) + "\n"


def main():
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("source", type=Path, help="FILE.vimp to analyse")
    ap.add_argument("outdir", type=Path, help="result directory to write")
    ap.add_argument("--analysis", default="int",
                    help="abstract domain (default: int)")
    ap.add_argument("--cli", type=Path, default=REPO_ROOT / "cli" / "voblint")
    args = ap.parse_args()

    if not ASSETS.is_dir():
        sys.exit(f"{ASSETS} is missing -- run: git submodule update --init vendor/g2html")

    cmd = [str(args.cli), "--analysis", args.analysis, "--dot-full",
           "--graph-snapshot", str(args.source)]
    proc = subprocess.run(cmd, capture_output=True, text=True)
    if proc.returncode != 0:
        sys.exit(f"voblint failed:\n{proc.stderr}")
    clusters, nodes, edges = parse_snapshot(proc.stdout)

    fun = "main"
    source_file = args.source.name
    seg = xmlify(source_file)
    outdir = args.outdir

    if outdir.exists():
        shutil.rmtree(outdir)
    for sub in ("nodes", "files", f"dot/{seg}", f"cfgs/{seg}"):
        (outdir / sub).mkdir(parents=True)

    (outdir / "index.xml").write_text(index_xml(source_file, [fun]))
    (outdir / "nodes" / "globals.xml").write_text(globals_xml())
    for nid, node in nodes.items():
        (outdir / "nodes" / f"{nid}.xml").write_text(
            node_xml(node, source_file, fun, args.analysis))
    (outdir / "files" / f"{seg}.xml").write_text(file_xml(args.source.read_text()))

    dot_path = outdir / "dot" / seg / f"{fun}.dot"
    dot_path.write_text(html_dot(clusters, nodes, edges))

    # Without a working graphviz the report still carries every abstract state
    # and every node document; only the CFG pane is empty. Degrade loudly
    # rather than refuse -- and never with a traceback, which buries the one
    # line that says what to install.
    svg = subprocess.run(["dot", "-Tsvg", str(dot_path), "-o",
                          str(outdir / "cfgs" / seg / f"{fun}.svg")],
                         capture_output=True, text=True) \
        if shutil.which("dot") else None
    if svg is None:
        print("warning: `dot` is not on PATH -- wrote dot/ but no cfgs/*.svg,"
              " so the CFG pane will be empty", file=sys.stderr)
    elif svg.returncode != 0:
        print(f"warning: `dot -Tsvg` failed, so the CFG pane will be empty:\n"
              f"{svg.stderr.strip()}", file=sys.stderr)

    for asset in sorted(ASSETS.iterdir()):
        if asset.is_file():
            shutil.copy2(asset, outdir / asset.name)

    print(f"wrote {outdir}: {len(nodes)} nodes, {len(edges)} edges")


if __name__ == "__main__":
    main()
