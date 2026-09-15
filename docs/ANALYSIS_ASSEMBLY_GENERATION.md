# Analysis registration generation

`manifests/analyses.yaml` is the registry. It answers one question: which
verified implementation is this domain? Each entry names the domain (`name`),
its abstract value type (`value_type`), the prefix its own constants and facts
share (`impl`, defaulting to the lowercased name), the domain theories the
registrations cite (`imports`), and, optionally, `roles` overrides for an
operation or fact whose spelling does not follow that prefix.

```text
manifests/analyses.yaml
       |
       +-- scripts/gen_analysis_assembly.py
             +-> src/Analyses/<Domain>/generated/<Domain>_Analyses.thy
```

Every domain gets the same theory. It holds three `global_interpretation`s, all
over the single rule-parametric solver interpretation `TD_side_rule_Interp`:

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

Generated: the three interpretations and the twelve obligation discharges of
each. Between the three contexts only the context terms differ -- global and
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

## How the CLI reads them

`analysis_result` in `Analysis_Run` is handwritten and reads only these: fifteen
equations, one per domain and context policy, none naming a rule. A gap between
a domain and a rule cannot be expressed, so there is no support table to
generate, and no default: the CLI picks the rule in OCaml. `abstract_value`,
which names each domain's abstract value type, is handwritten in
`Dispatch_Carrier`.

A call-string bound needs no guard. `cs_route k u ctx d ca = take k (u # ctx)`,
so `k = 0` routes every activation to `[]` -- as well-defined as any other bound,
and finite by the same `length (cs_route k ...) \<le> k`. The result is a table
keyed by call strings that all happen to be empty, which is *not* `Ctx_None`:
that solves a flat system and publishes at `unit`.

## What this costs

The tooling is about 480 lines -- a 53-line registry, a 331-line generator and
98 lines of hand-written expectations -- plus this document. It produces about
860 lines of theory across five domains, roughly 170 each.

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
name or value type; a `roles` override naming an unknown role; an applied role
that is not exactly `const` plus a non-empty `args` of constant names; an
applied fact role. Rendering also refuses a generated line over 100 symbols or
with non-ASCII content.

## Independent expectations

`tests/test_analysis_registry.py` is deliberately not derived from the registry.
It writes the support policy out by hand -- every domain answers every global
update rule at every context policy -- and checks the emitted theory text
against it: each of the fifteen (domain, context) pairs has exactly one
rule-parametric registration with the expected locale and `for` parameters, and
`analysis_result` has one equation per domain and context policy, none naming a
`Globals_*` constructor. A registry change that drops a registration or pins a
rule fails them.

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
