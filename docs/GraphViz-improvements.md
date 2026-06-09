# Migration: Procedure-Aware GraphViz Visualization

## Context

The current GraphViz exporter (`CFG_GraphViz.thy`) operates on the final `cfg` produced by `compile_prog`.

The exported graph contains:

* CFG edges (`edges`)
* interprocedural return relations (`combines`)
* global entry and exit nodes

Example output:

```dot
9 -> 0  [label="enter"]
11 -> 3 [label="enter"]

2 -> 10 [style=dashed,color=blue,label="combine via call@9"]
8 -> 12 [style=dashed,color=blue,label="combine via call@11"]
```

While the interprocedural structure is present, the visualization does not indicate which nodes belong to which procedure.

---

## Problem

GraphViz procedure clustering requires procedure ownership information.

Example:

```dot
subgraph cluster_main { ... }
subgraph cluster_p    { ... }
subgraph cluster_q    { ... }
```

The current `cfg` representation does not contain a mapping:

```isabelle
pp ⇒ procedure
```

As a result, once `compile_prog` has produced a CFG, the GraphViz layer cannot determine whether a node belongs to:

* main
* procedure `p`
* procedure `q`
* another procedure

Node numbering currently appears grouped by procedure, but this is an implementation detail and should not be relied upon.

---

## Options Considered

### Option 1: Extend CFG with procedure ownership

Add metadata describing the owning procedure for each program point.

Example:

```isabelle
proc_of :: pp ⇒ pname option
```

where:

```isabelle
None      = main
Some "p"  = procedure p
Some "q"  = procedure q
```

Advantages:

* robust
* explicit
* enables GraphViz clusters
* useful for future analyses

Disadvantages:

* requires changes to CFG generation

---

### Option 2: Export procedure regions separately

Keep `cfg` unchanged but extend the compiler result with metadata.

Example:

```isabelle
proc_regions ::
  (pname option × pp set) list
```

Example value:

```isabelle
[
  (None, {9,10,11,12,13,14}),
  (Some ''p'', {0,1,2}),
  (Some ''q'', {3,4,5,6,7,8})
]
```

Advantages:

* minimal impact on CFG definition
* enough for GraphViz clustering

Disadvantages:

* metadata maintained separately

---

### Option 3: Infer clusters from numbering

Detect procedure boundaries from generated node IDs.

Advantages:

* no compiler changes

Disadvantages:

* fragile
* depends on allocation order
* likely to break during refactoring

Not recommended.

---

## Recommended Approach

Implement Option 2 first.

Procedure ownership is only needed for visualization, so extending the compiler output with procedure-region metadata provides the best cost/benefit ratio.

Once region information is available, `CFG_GraphViz` can emit:

```dot
subgraph cluster_main {
  label="main";
}

subgraph cluster_p {
  label="p";
}

subgraph cluster_q {
  label="q";
}
```

while preserving the existing CFG and `combines` representation.

---

## Short-Term Improvement

Before adding clustering support, improve readability by highlighting procedure boundaries:

* procedure entry nodes: green boxes
* procedure exit nodes: red boxes
* call edges: thicker/different color
* combine edges: dashed blue

This can be implemented entirely in `CFG_GraphViz` and requires no CFG changes.
