# CFG (core)

**Main contribution:** Control-flow graphs as labelled graphs over program points,
compilation from IMP2 (`to_cfg`), and path infrastructure (`cfg_path`, offsets) used
by collecting semantics and the analyzer.

**Theories**

| File | Role |
| --- | --- |
| `CFG_Def.thy` | `cfg`, `pp`, edge actions (`EA_Assign`, `EA_Assume`, …) |
| `CFG_Path.thy` | `cfg_path`, `offset_path`, `cfg_path_offset` (nested compile shifting) |
| `IMP2_to_CFG.thy` | `to_cfg`, `offset_edges`, structural compilation lemmas |
| `CFG_GraphViz.thy` | Pretty-printing / Graphviz export (tooling) |

Path store folding uses `edges_collect` in [`Collecting/CFG_Edges_Collect.thy`](Collecting/CFG_Edges_Collect.thy).

**Collecting semantics** (fixpoint over stores, `runs_to`, small-step bridge) live in
[`Collecting/`](Collecting/) — import **`CFG_Runs_To_Bridge`** for the full chain.

**Key concepts:** `cfg_entry`, `cfg_exit`, `to_cfg c`, labelled paths with action lists.
