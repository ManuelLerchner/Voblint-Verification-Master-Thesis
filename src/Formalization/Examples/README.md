# Examples

**Main contribution:** Executable smoke tests and small demonstrations — code
generation, sanity checks on collecting vs paths, and sample analyses. Built as
separate `ROOT` targets; not imported by `Goblint_Formalization.thy`.

**Theories**

| File | Role |
| --- | --- |
| `Example_Sign_Analysis.thy` | Runnable sign analysis (`TD_Interface`, `Sign_Domain`) |
| `Example_Interval_Analysis.thy` | Runnable interval analysis (`TD_Interface`, `Interval_Domain`) |
| `Example_Interval_Widen.thy` | Interval analysis with widening (`TD_Widen_Interface`) |
| `Example_CFG_Collecting_Equiv.thy` | Collecting vs path checks (`CFG_Runs_To_Bridge`) |
| `Example_GraphViz.thy` | CFG Graphviz output (`CFG_GraphViz`, `IMP2_to_CFG`) |
| `Example_NonTerminating_Safe.thy` | Partial / non-terminating run illustration (`Pipeline`) |

**Session entry points** (see `ROOT`): `Example_Sign_Analysis`, `Example_Interval_Analysis`,
`Example_Interval_Widen`, `Example_CFG_Collecting_Equiv`, `Example_GraphViz`,
`Example_NonTerminating_Safe`, plus main target `Goblint_Formalization`.
