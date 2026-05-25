# CFG representation survey

Decision record for [issue #28](https://github.com/ManuelLerchner/goblint-formalization/issues/28) and [issue #27](https://github.com/ManuelLerchner/goblint-formalization/issues/27). Source: [wimmers/archive-of-graph-formalizations](https://github.com/wimmers/archive-of-graph-formalizations) (June 2024).

## Current choice

This repo uses **labelled edge triples** `(pp × edge_action × pp) set` in `src/CFG/CFG_Def.thy` (`cfg_edges`). The collecting semantics and `cfg_path` infrastructure are proved against that representation; the IMP2↔CFG bridge is closed.

**Do not swap** to AFP `Graph_Theory` (Noschinski) unless a future proof needs `awalk`/`apath` lemmas that are cheaper to import than to reprove. See issue #27.

## Comparison table

| Style | Carrier | Labels | Suits our CFG? |
| --- | --- | --- | --- |
| Abstract arcs + tail/head | `pre_digraph`, `fin_digraph` (`Graph_Theory`) | Side function on arcs | Yes (extra indirection) |
| Relation | `'v ⇒ 'v ⇒ bool` (`TA_Graphs`) | No | No |
| Pair set | `('v × 'v) set` (`DDFS`, `pair_digraph`) | No | Yes (lose `Assign`/`Assume` on edges) |
| **Triple set** | `(pp × edge_action × pp) set` | **On edge** | **Yes (current)** |
| Adjacency matrix | Floyd–Warshall style | Optional | Overkill for sparse CFGs |

## Reachability (optional import)

`TA_Graphs` relational `reaches` could discharge TD `td_cfg_in_reach` (P2) if we project labelled triples to `'pp ⇒ 'pp ⇒ bool`. Not started; tracked as [issue #8](https://github.com/ManuelLerchner/goblint-formalization/issues/8).

## KB

Full archive index lives in the KB repo (`goblint-formalization-kb`); ingest `archive-of-graph-formalizations/README.md` there when extending related work.
