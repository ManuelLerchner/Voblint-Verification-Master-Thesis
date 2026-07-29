# Migration: monolithic session → 4-session DAG

Status: **DONE** 2026-06-12. 4-session DAG live; qualified imports applied; bootstrap build green.

> The DAG has since grown a 5th leaf session `Voblint_Examples` (`src/Examples/`):
> the `Example_*`/`Exec_*` witnesses and the `Voblint` capstone were split out of
> `Voblint_Formalization`, which now holds soundness theorems only. This
> historical record documents the original monolith → 4-session split.

## Problem

The repo currently builds one monolithic `Voblint_Formalization` session spanning
`src/` via the `directories` keyword. Isabelle has no heap-caching boundary inside
a session, so any change anywhere rebuilds everything. As the theory count grows,
this turns every proof edit into a full rebuild.

## Proposed Solution

Split into a 4-session DAG. Isabelle caches a heap per session and only rebuilds
sessions whose transitive dependency on the changed theory is non-empty.

```
Voblint_VIMP          HOL-IMP base; no external solver deps
       |
Voblint_CFG           CFG + Collecting; adds Dijkstra_Shortest_Path
       |
Voblint_Analysis      Domains + Equations + Solver; adds TD
       |
Voblint_Formalization Pipeline + Examples; umbrella (existing name retained)
```

## Blocker: Isabelle cross-session bare-name resolution

The migration was implemented and tested. It fails because **Isabelle requires source
`.thy` files to be present in a session's own `directories` for all imported theories,
even those from parent sessions or `sessions` dependencies**.

Bare-name imports (`imports VIMP_Syntax`) only resolve automatically for:

- Theories defined in the **current session's directories**
- Standard library sessions (HOL, HOL-IMP, HOL-Library) that ship as part of the
  Isabelle installation and are in the built-in source search path

Custom sessions like `Voblint_VIMP` are NOT in the built-in search path. A child
session `Voblint_CFG = "Voblint_VIMP" +` cannot resolve `VIMP_Syntax` by bare name
even when `Voblint_VIMP`'s heap exists, because Isabelle looks for `VIMP_Syntax.thy`
in `Voblint_CFG`'s declared directories (`src/CFG/`, `src/CFG/Collecting/`) and
finds nothing.

Evidence: `Voblint_CFG.VIMP_Syntax` appears in errors (Isabelle tries to create it
as a new theory in CFG, not use `Voblint_VIMP.VIMP_Syntax`).

The original plan stated "Theory file changes: None" — this was incorrect.

## What was achieved instead

The build command was updated to add `-N` (use all CPU cores within a session).
This gives parallelism within the monolithic session at zero structural cost:

```bash
# Updated (in AGENTS.md)
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

## Proposed ROOT (for future implementation with qualified imports)

If the 4-session DAG is pursued, theory source files must use QUALIFIED cross-session
imports. The ROOT structure with a linear parent chain would be:

```isabelle
session Voblint_VIMP in "src/VIMP" = "HOL-IMP" +
  description "IMP2 syntax, small-step, and procedure language"
  theories
    HOL_IMP_Countable
    VIMP_Syntax
    VIMP_Globals
    VIMP_Expr
    VIMP_Proc

session Voblint_CFG in "src/CFG" = "Voblint_VIMP" +
  description "CFG construction and collecting semantics"
  sessions
    "Dijkstra_Shortest_Path"
  directories
    "Collecting"
  theories
    CFG_Def
    CFG_Path
    CFG_GraphViz
    VIMP_Proc_to_CFG
    CFG_Collect_Core
    CFG_Collect_Edges
    CFG_Collect_Trace
    CFG_Collect_IP
    CFG_Prune
    CFG_Collect_IP_Adeq
    CFG_Collect_Unified
    CFG_Collect_Trace_IP

session Voblint_Analysis in "src" = "Voblint_CFG" +
  description "Abstract domains, constraint systems, and TD solver bridge"
  sessions
    TD
  directories
    "Domains"
    "Equations"
    "Solver"
  theories
    Abstract_Domain
    Sign_Domain
    Constraint_System
    Constraint_System_Sound
    Constraint_System_IP_Sound
    Analysis_Sound
    TD_Side_CFG
    TD_Side_IP_Bounds
    TD_Side_IP_Interface
    TD_Side_IP_Soundness
    Sign_Side_IP_Soundness

session Voblint_Formalization in "." = "Voblint_Analysis" +
  description "End-to-end soundness pipeline and examples"
  directories
    "src/Pipeline"
    "src/Examples"
  theories
    Trace_IP_Analysis_Sound
    Example_Proc_GraphViz
    Example_Side_Proc_Global
    Example_Trace_Digest_Precision
```

### Required theory file changes (summary)

Every bare-name import that crosses a session boundary must become a qualified import.

**In `Voblint_CFG` theories** — qualify IMP2 imports:

| File | Import to change |
|------|-----------------|
| `CFG_Def.thy` | `VIMP_Syntax` → `"Voblint_VIMP.VIMP_Syntax"` |
| `VIMP_Proc_to_CFG.thy` | `VIMP_Proc` → `"Voblint_VIMP.VIMP_Proc"` |
| `CFG_Collect_Edges.thy` | `VIMP_Expr`, `VIMP_Globals` → qualified |
| `CFG_Collect_Trace.thy` | `VIMP_Globals` → `"Voblint_VIMP.VIMP_Globals"` |
| `CFG_Collect_IP_Adeq.thy` | `VIMP_Proc` → `"Voblint_VIMP.VIMP_Proc"` |

**In `Voblint_Analysis` theories** — qualify CFG + IMP2 imports:

| File | Imports to change |
|------|------------------|
| `Sign_Domain.thy` | `VIMP_Expr`, `VIMP_Globals` → qualified (IMP2) |
| `Constraint_System.thy` | `CFG_Def`, `VIMP_Globals`, `VIMP_Expr` → qualified |
| `Constraint_System_Sound.thy` | `CFG_Collect_Core` → `"Voblint_CFG.CFG_Collect_Core"` |
| `Constraint_System_IP_Sound.thy` | `CFG_Collect_IP` → `"Voblint_CFG.CFG_Collect_IP"` |
| `Analysis_Sound.thy` | `CFG_Collect_Unified` → `"Voblint_CFG.CFG_Collect_Unified"` |
| `TD_Side_CFG.thy` | `VIMP_Globals` → `"Voblint_VIMP.VIMP_Globals"` |
| `TD_Side_IP_Bounds.thy` | `CFG_Collect_IP` → `"Voblint_CFG.CFG_Collect_IP"` |
| `TD_Side_IP_Soundness.thy` | `CFG_Prune` → `"Voblint_CFG.CFG_Prune"` |

**In `Voblint_Formalization` theories** — qualify Analysis + CFG imports:

| File | Imports to change |
|------|------------------|
| `Trace_IP_Analysis_Sound.thy` | `Analysis_Sound`, `CFG_Collect_Trace_IP` → qualified |
| `Example_Proc_GraphViz.thy` | `CFG_GraphViz`, `VIMP_Proc_to_CFG` → qualified |
| `Example_Side_Proc_Global.thy` | `Sign_Side_IP_Soundness`, `CFG_Collect_IP_Adeq` → qualified |
| `Example_Trace_Digest_Precision.thy` | `Sign_Domain` → `"Voblint_Analysis.Sign_Domain"` |

Approximately 20 import-line changes across 13 theory files. No proof changes needed —
qualification affects only the `imports` header, not definitions or lemma bodies.

## Build command changes

Add `-N` (use all CPU cores within a session). No other change.

```bash
# Before
isabelle build -v -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization

# After (already applied in AGENTS.md)
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -D . Voblint_Formalization
```

With the future 4-session split, sub-layer builds become possible:

```bash
isabelle build -v -N -d ~/afp/thys -d vendor/td-verification -d . Voblint_CFG
```

Note: use `-d .` (lowercase) when specifying a sub-session to avoid validating all
sessions in ROOT simultaneously.

## What ROOTS gives (and why we don't need it yet)

AutoCorrode uses a `ROOTS` file because each component has its own sub-directory
`ROOT`. Our single top-level `ROOT` already contains all sessions; the `-D .`
flag discovers it. A `ROOTS` file would only be needed if we scatter `ROOT` files
into `src/VIMP/ROOT`, `src/CFG/ROOT`, etc. That's an optional further step but
not required for the DAG build-time benefit.

## AFP IMP2 rebase migration interaction

`docs/AFP_IMP2_REBASE_MIGRATION.md` adds `IMP2_Bridge.thy` to `src/VIMP/`. It
also requires the AFP `IMP2` session as a dependency. Under the split, this lands
cleanly in `Voblint_VIMP`:

```isabelle
session Voblint_VIMP in "src/VIMP" = "HOL-IMP" +
  sessions
    "IMP2"          (* AFP — add when IMP2_Bridge.thy is merged *)
  theories
    HOL_IMP_Countable
    VIMP_Syntax
    VIMP_Globals
    VIMP_Expr
    VIMP_Proc
    IMP2_Bridge     (* add after Phase 1 of AFP IMP2 rebase *)
```

## Rollout steps (if pursuing the 4-session split)

1. **Apply qualified imports** — update the ~20 import lines listed above via I/Q.
2. **Edit `ROOT`** — replace with the four-session block above (linear parent chain).
3. **Heap flush** — `isabelle build -d .` builds each session from scratch once.
   Use `-d .` (not `-D .`) when building sub-sessions to avoid validating downstream
   sessions whose heaps don't exist yet.
4. **Smoke-test incremental** — touch one theory in `src/CFG/`, rerun build for
   `Voblint_CFG`. Verify only CFG and its dependents rebuild.
5. **CI** — adjust the build target if CI currently names `Voblint_Formalization`
   explicitly (it does, so no change needed there).

## Expected build-time impact

| Change | Before | After (estimate) |
|--------|--------|-----------------|
| Touch `src/Domains/Sign_Domain.thy` | Full rebuild (all ~35 theories) | `Voblint_Analysis` + `Voblint_Formalization` only (~15 theories) |
| Touch `src/VIMP/VIMP_Proc.thy` | Full rebuild | All 4 sessions (full rebuild — IMP2 is the root) |
| Touch `src/Examples/Example_Side_Proc_Global.thy` | Full rebuild | `Voblint_Formalization` only (~5 theories) |

The biggest win is mid-stack edits (Domains, Equations, Solver, CFG) where the
current monolith forces unnecessary rebuilds of unrelated layers.
