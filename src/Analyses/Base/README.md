# Analyses / Base

`Voblint_Analysis_Base` is what every concrete domain starts from. It contains no
lattice, no transfer function and no soundness theorem about any particular
abstraction — only the things all of them would otherwise each rewrite.

It is the parent session of `Voblint_Analysis_Sign`, `_Interval`, `_Parity`,
`_Congruence`, `_Relational` and `_Int`. Nothing here may mention a concrete
domain; if a definition needs to know whether values are signs or intervals, it
belongs one level down.

## Vocabulary

| Term | Meaning |
| --- | --- |
| reuse locale | a locale a domain *interprets* to obtain a family of derived operations, rather than redefining them. `Abstract_Arithmetic`, `Special_Ops`, `Numeric_Ops`, `Exec_Backward` are these. |
| analysis surface | the published shape of a finished analysis — the report a caller reads — independent of which domain produced it (`Analysis_Surface`) |
| routing policy | how a call site maps to a context: none, the entered abstract value, or a bounded call string |
| context space | the set a policy's contexts are drawn from. Finiteness of the solved key set is a property of this set, not of the solver. |

## Folders

| Folder | Holds |
| --- | --- |
| `Reuse/` | the base-level locales every domain interprets: derived arithmetic, special-call dispatch, numeric queries, executable backward filtering, and the published analysis surface |
| `Config/` | `analysis_domain`, `solver_choice`, `context_mode` and `resolve_analysis_config` — which (domain, solver, context) triples are legal, decided in one place |
| `Context/` | the concrete routing policies over a compiled program (call-string and entry-state), plus the finiteness arguments their key spaces need |
| `Reporting/` | generic GraphViz rendering of an analysis result, domain-independent |

## Worked example: how a domain uses this session

Sign interprets `Reuse/Abstract_Arithmetic` at its own lattice and gets derived
arithmetic without restating it; `Reuse/Numeric_Ops` gives it the executable
numeric queries its check discharge needs; `Context/Call_String_Routed_Context`
supplies the routing policy `Sign_Analyses` instantiates for its `k`-bounded
run; `Config/Analysis_Config` is where `Sign_Analysis` appears as a selectable
value at all. Sign contributes the lattice and the transfer functions; every
other piece of that sentence is this session's.

## Why the finiteness theories are here and not in Framework

`Context_Space_Finite` and `Call_String_Context_Finite` are about a *compiled*
program, so they need `Voblint_Compile`, which the framework deliberately never
sees. They are domain-generic all the same, which is why they sit at the base of
the analysis layer rather than inside any one domain.
