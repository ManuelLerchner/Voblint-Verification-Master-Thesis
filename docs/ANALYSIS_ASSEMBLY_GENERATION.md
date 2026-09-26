# Analysis registration generation

`manifests/analyses.yaml` is the registry. It answers one question: which
verified implementation is this domain? Each entry names the domain (`name`),
its abstract value type (`value_type`), the prefix its own constants and facts
share (`impl`, defaulting to the lowercased name), the domain theories the
registrations cite (`imports`), and, optionally, the context policies it
registers at (`contexts`, default `[unit]`), the constructor that wraps its
values for display (`value_constructor`), and `roles` overrides for an operation
or fact whose spelling does not follow that prefix.

```text
manifests/analyses.yaml
       |
       +-- scripts/gen_analysis_assembly.py
             +-> src/Analyses/<Domain>/generated/<Domain>_Analyses.thy
             +-> src/Executable_Surface/CLI/generated/MCP_Carrier.thy
```

Every domain gets the same theory. It holds one `global_interpretation` per
listed context policy, all over the single rule-parametric solver
interpretation `TD_side_rule_Interp`. Every domain lists `unit`; Interval also
lists `entry-state` and `call-string`, which its examples read:

| Registration | Locale | Context policy | Parameters |
| --- | --- | --- | --- |
| `<d>_rule` | `unit_dg_analysis` | unit | `r` |
| `<d>_es_rule` | `routed_dg_analysis` | entry state | `r` |
| `<d>_cs_rule` | `routed_dg_analysis` | call string | `k r` |

`r :: globals_rule` is the global update rule, so one registration serves every
solver discipline; `k` is the call-string bound. None of them has a `defines`
clause: a caller reads the locale's own constants and facts under the
qualifier, as in `sign_rule.result Globals_Join gs p` or `sign_rule.source_sound`.

Theory names, paths, imports, binders and the entire proof text are derived by
convention, identically for every domain. Domain rationale -- why a lattice has
finite height, why a solver choice matters here -- belongs in that domain's
README.

## What is generated, and what is not

Generated: the interpretations and the twelve obligation discharges of
each. Between the contexts only the context terms differ -- global and
seed keys, the executable and abstract route -- together with obligation 4, the
routing agreement.

Not generated, ever: the mathematics. Every obligation is discharged by citing
a fact the registry only *names* -- the domain's own, or the rule-parametric
`TD_side_rule_Interp` instance for the three solver contracts, since solver
correctness belongs to the solver. No axiom, no `sorry`, no assumption, no
coverage or termination claim. The generator may only move a name into a
position Isabelle checks.

## The registration interface

Because the proof text is uniform, a domain has to satisfy the shape it cites
into. Each role has a conventional spelling built from `impl`:
`<impl>_tf_st_for`, `cinit_<impl>_st`, `<impl>_tf.is_sound_transfer_for`,
`<impl>_tf_st_for_commute`, and so on. The classifier and the initial-state fact
use the lowercased domain name (`interval_classify_check`,
`interval_cinit_gamma`) even where `impl` differs (`ivl`).

Obligation 2 carries a liveness premise, so the fact named for it must be
registration-shaped -- premise and all. Sign's and Interval's commutation
theorems already are. Parity's is stronger: unconditional, and therefore not
citable into the chained proof. Parity keeps its stronger theorem and supplies a
registration-shaped corollary, which the registry names under
`roles: tf_commute: parity_tf_st_for_commute_if_live`.

A role may also be an application `{const, args}` for an operation that takes a
configuration argument. Int registers at its most precise refinement mode this
way: `tf_st: {const: int_tf_st_for, args: [Refine_Fixpoint]}`, and likewise for the
two entry transfers, assignment, special calls, branch and return. The renderer quotes the
application, so the interpretation still receives one argument. A fact takes no
arguments, so an applied fact role is a registry error.

## The combined state

`MCP_Carrier.thy` is generated from the same registry, in registry order. It
holds the `analysis_domain` datatype, one constructor per domain, and the
combined state `mcp_st`: a nested product with one lifted field per domain,
each field carrying that domain's `exec_dg_st`. Beside it comes the per-domain
dispatch the combined state needs, one equation per domain each:
`mcp_component_of` (a field's transfer, lensed into the product), the field
concretization and liveness readers, `val_answer` (a field's answer to a
query), `value_of` (a field's value for display, wrapped in the domain's
`value_constructor`), `mcp_init` (active fields start at the domain's initial
state, inactive ones at `Bot`) and the readers for the formals a context is
keyed by. The lemmas `mcp_component_of_sound`, `mcp_init_sound` and
`val_answer_sound` are proved by case analysis over the domain, citing only
facts the domains already export.

What does not depend on the domain list is handwritten: `MCP_Field.thy` (one
field's lens laws) and `MCP_Analyses.thy` (normalization to `Bot`, the met
answer, `mcp_classify`, and the three registrations `mcp_rule`, `mcp_es_rule`
and `mcp_cs_rule` over the activation list `as`).

The registry is not yet the only place a new domain is named. The display
union `abstract_value` in `Dispatch_Carrier.thy`, with its imports, rendering
and ordering key, is handwritten, and so is the domain list in
`tests/test_analysis_registry.py`. Adding a domain means a manifest entry plus a
constructor and its cases there.

## How the CLI reads them

`analysis_result` in `Analysis_Run` is handwritten and reads only the combined
registrations: three equations, one per context policy, none naming a domain or
a rule. The activation list, the rule and the call-string bound are arguments,
so there is no support table to generate and no default.

A call-string bound needs no guard. `cs_route k u ctx d ca = take k (u # ctx)`,
so `k = 0` routes every activation to `[]` -- as well-defined as any other bound,
and finite by the same `length (cs_route k ...) \<le> k`. The result is a table
keyed by call strings that all happen to be empty, which is *not* `Ctx_None`:
that solves a flat system and publishes at `unit`.

## What this costs

The tooling is about 970 lines -- a 61-line registry, a 784-line generator and
127 lines of hand-written expectations -- plus this document. It produces about
490 lines of per-domain theory (about 80 per unit-only domain, 172 for Interval)
and the 276-line combined state.

Two different things are at work and they are worth keeping apart. The
*assembly* -- `routed_dg_analysis` and its unit instance `unit_dg_analysis` --
removes repeated implementation and repeated reasoning: the equation system, the
solve, the reader, the result table and the soundness transport are constructed
and proved once. The *generator* removes repeated registration text. A new
domain becomes cheaper to integrate through both, and neither removes the
domain's own mathematics.

The failure mode to watch is not a domain needing a shape of its own. A domain
can legitimately fall outside the supported family -- `unit_dg_analysis` states
its own scope, and a relational carrier is outside it by construction. The
warning signs are semantic exceptions and per-domain overrides of the proof text
accumulating *inside* the generator, at which point the registry has become a
second programming language and the uniform shape is a fiction. A `roles` entry
renames an argument; it never changes a proof step.

## Validation

The generator refuses a registry that is not valid policy: a duplicated domain
name or value type; a domain without the `unit` context, or with an unknown
one; a `roles` override naming an unknown role; an applied role
that is not exactly `const` plus a non-empty `args` of constant names; an
applied fact role. Rendering also refuses a generated line over 100 symbols or
with non-ASCII content.

## Independent expectations

`tests/test_analysis_registry.py` is deliberately not derived from the registry.
It writes the support policy out by hand and checks the emitted theory text
against it: every domain has its unit registration, the combined state has
`mcp_rule` and `mcp_es_rule` for `as r` and `mcp_cs_rule` for `as k r`, every
domain is a field of the combined state, and `run_voblint` passes the rule
through without naming a `Globals_*` constructor. A registry change that drops a
registration, drops a domain from the combined state or pins a rule fails
them.

## Drift

```bash
pixi run assembly-generate # regenerate
pixi run assembly-check   # fail if the checked-in theories are stale
```

`--check` diffs regenerated output against the checked-in files itself, so it
needs neither git nor Isabelle, and it runs in `verify`, the pre-commit hook and
GitHub CI. `--out DIR` renders into another directory and leaves the tree alone.

The generator is a host writer, and a running Isabelle session keeps serving
the bytes it loaded; `docs/ISABELLE_AGENT_NOTES.md` covers comparing the buffer
against disk after a regeneration. Two further hazards belong to the project
contract. A `theories` entry is a theory name, never a path -- a slash there
fails the whole session at load, so jEdit does not start and the mistake looks
like a dead editor; `pixi run sessions-check` catches it without Isabelle. And a
theory that loads as `Draft.<name>` is not verified in its session: a draft node
resolves imports without consulting the session, and saving from one rewrites
same-session imports into session-qualified form, which the drift check catches
but only after the fact.
