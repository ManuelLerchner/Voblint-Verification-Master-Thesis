# CFG (core)

**Main contribution:** Control-flow graphs as labelled graphs over program points,
interprocedural compilation from IMP2 with procedures (`compile_prog`), path
infrastructure (`cfg_path`, offsets), and reachability pruning.

**Theories**

| File | Role |
| --- | --- |
| `CFG_Def.thy` | `cfg`, `pp`, edge actions (`EA_Assign`, `EA_Assume`, `EA_AssumeNot`, `EA_Nop`, `EA_Enter`); `combines` triples |
| `CFG_Path.thy` | `cfg_path`, `offset_path`, `cfg_path_offset` (nested compile shifting) |
| `IMP2_Proc_to_CFG.thy` | `compile_prog pi ps c :: cfg`; whole-program layout with enter edges and combine triples; `compile` on `com` |
| `CFG_Prune.thy` | `ip_reaches`, reachability pruning (`CFG_Prune`); used by solver soundness |
| `CFG_GraphViz.thy` | Pretty-printing / Graphviz export (tooling) |

Path store folding uses `edges_collect` in [`Collecting/CFG_Collect_Edges.thy`](Collecting/CFG_Collect_Edges.thy).

**Collecting semantics** (IP fixpoint over stores, trace, unified locale) live in
[`Collecting/`](Collecting/) — import **`CFG_Collect_IP`** for interprocedural semantics
or **`CFG_Collect_Unified`** for the locale.

**Key concepts:** `cfg_entry`, `cfg_exit`, `edges g`, `combines g`; `compile_prog pi ps c`
produces a single flat CFG with call-site / procedure-exit combine triples.
