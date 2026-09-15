# Analysis registration generation

`manifests/analyses.yaml` is the registry. It answers three questions and nothing
else:

1. Which verified implementation is this domain?
2. Which solver and context registrations does it carry?
3. Which API capabilities does each published combination expose?

```text
manifests/analyses.yaml
       |
       +-- scripts/gen_analysis_assembly.py
             +-> src/Analyses/<Domain>/generated/<Domain>_Assembly.thy
             +-> src/Analyses/<Domain>/generated/<Domain>_Analyses.thy
                   (Interval: Interval_Contextual_Assembly.thy)
             +-> src/Analyses/<Domain>/generated/<Domain>_Checks.thy   (not Int)
             +-> src/Analyses/<Domain>/generated/<Domain>_Entry.thy    (not Int)
```

How those choices become theories, bindings and proofs is
the generator's decision. Theory names, paths, imports, interpretation binders,
published prefixes, which route publishes the full name set, the
equation-agreement lemmas and the entire proof text are derived by convention,
identically for every domain. Domain rationale -- why a lattice has finite
height, why a solver choice matters here -- belongs in that domain's README.

## What is generated, and what is not

Generated: the `global_interpretation` of `unit_dg_analysis` per published
route, its `defines` block, the `[code_unfold]` declaration a named `dg_spec`
needs, the lemmas relating each sibling discipline's equation system to the
production one, the contextual `routed_dg_analysis` registrations with their
published constants and re-exports, the rule-parametric registrations
`run_voblint` reads, and the published runtime names and entry endpoints of
every domain but Int.

Not generated, ever: the mathematics. Every obligation is discharged by citing
a fact the registry only *names* -- the domain's own, or a `TD_side_upd_rule`
instance for the three solver contracts, since solver correctness belongs to
the solver. No axiom, no `sorry`, no assumption, no coverage or termination
claim. The generator may only move a name into a position Isabelle checks.

## The registration interface

Because the proof text is uniform, a domain has to satisfy the shape it cites
into. Obligation 2 carries a liveness premise, so the fact named for it must be
registration-shaped -- premise and all. Sign's and Interval's commutation
theorems already are. Parity's is stronger: unconditional, and therefore *not*
citable into a chained proof, which failed with `Failed to apply initial proof
method` at both of its interpretations.

The fix is not a per-domain proof switch. The domain keeps its stronger theorem
and supplies a registration-shaped corollary, and the registry names that
corollary under `legacy.facts`. Registration cites a registration-shaped fact;
the domain keeps the sharper one.

## The legacy block

`legacy:` is quarantined on purpose. It maps the uniform interface onto
spellings that predate it: `ivl` where the interface says `Interval`, binders
like `interval_warrow_asm`, published prefixes like `interval_td`, report names
like `analyse_interval_report`. Every entry is a rename waiting to happen,
not an extension point. Nothing outside `legacy:` names an identifier a
convention could have produced.

Int has a generated assembly and generated contextual registrations, but no
`checks:` or `entry:` block: `Int_Checks` and `Int_Entry` carry proofs rather
than bindings, so its report names stay under `legacy.routes`.

## The rule-parametric registrations

Beside the per-discipline instances, every domain carries one registration per
context policy with the global update rule left as a parameter, all over the
single `TD_side_rule_Interp` solver interpretation: `<d>_rule` of
`unit_dg_analysis` for `r` in `<Domain>_Assembly`, and `<d>_es_rule` for `r` and
`<d>_cs_rule` for `k r` of `routed_dg_analysis` in the contextual theory. They
publish no names of their own.

`analysis_result` in `Analysis_Run` is handwritten and reads only these: fifteen
equations, one per domain and context policy, none naming a rule. A gap between
a domain and a rule cannot be expressed, so there is no support table to
generate, and no default: the CLI picks the rule in OCaml. `abstract_value` and
`tag_states`, which name each domain's abstract state type, are handwritten in
`Dispatch_Carrier`.

A call-string bound needs no guard. `cs_route k u ctx d ca = take k (u # ctx)`,
so `k = 0` routes every activation to `[]` -- as well-defined as any other bound,
and finite by the same `length (cs_route k ...) \<le> k`. The result is a table
keyed by call strings that all happen to be empty, which is *not* `Ctx_None`:
that solves a flat system and publishes at `unit`.

## What this costs

The tooling is about 3300 lines -- registry, generator, ROOT lint, hand-written
expectations, this document. It produces about 5100 lines of theory across five
domains. Both numbers are in the repository, so the
repository grows; generation replaces handwritten lines with generated ones
rather than removing them.

What it removed at adoption was 393 manually maintained occurrences, counted
against the tree as it stood then rather than estimated:

| | count |
| --- | --- |
| obligation discharges (14 interpretations x 10) | 140 |
| publication-name bindings | 119 |
| dispatcher equations across the four tables | 70 |
| resolver equations | 55 |
| equation-agreement lemmas | 9 |

Those are repeated sites rather than independent decisions -- many follow from
one choice, which is the point: they had to agree with each other and were kept
in agreement by hand. They now follow from five registry entries.

So the value is consistent registration and cheap updates, not fewer lines.

Two different things are at work here and they are worth keeping apart. The
*assembly* -- `unit_dg_analysis` itself -- removes repeated implementation and
repeated reasoning: the equation system, the solve, the reader, the result
table and the soundness transport are constructed and proved once. The
*generator* removes repeated registration text. A new domain becomes cheaper to
integrate through both, and neither removes the domain's own mathematics.

The failure mode to watch is not a domain needing a shape of its own. A domain
can legitimately fall outside the supported family -- `unit_dg_analysis` states
its own scope, and a relational carrier or a multi-context policy is outside it
by construction. Nor is a growing `legacy:` block, by itself: stable public-name
mappings grow with the number of supported domains, which is what they are for.
The warning signs are semantic exceptions and per-domain overrides of the proof
text or the template, accumulating *inside* the generator, at which point the
registry has become a second programming language and the uniform shape is a
fiction.

Int shows the interface stretching without breaking. Its `refine_mode` enters
the registry as applied roles (`{const, args}`) and one `generalize:` entry, both
rendered by the same proof text; what stays hand-written (`Int_Checks`,
`Int_Entry`) is there because it proves something, not because the template
could not express it.

## Validation

The generator refuses a registry that is not valid policy: a duplicated domain
name, value type, report tag, binder or published prefix; a domain publishing no
route; a route naming an unknown solver; entry endpoints or published names for
an unpublished route; a legacy name for an unpublished route; a route naming a
report but no state report; a domain without a generated assembly and no legacy
names. Rendering
also refuses a contextual route that publishes through `defines` and lists a
first solver other than its default, because that solver owns the unsuffixed
binder and every alias defined from it.

## Independent expectations

`tests/test_analysis_registry.py` is deliberately not derived from the registry.
It writes the support policy out by hand -- every domain answers every global
update rule at every context policy -- and checks the emitted theory text
against it: each of the fifteen (domain, route) pairs has exactly one
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
needs neither git nor Isabelle, and it runs in `verify` and GitHub CI.

Adoption is per output. An unadopted output renders under `--out`, is never
written into the tree, and is required by the drift check to be *absent*, so it
can neither be planted accidentally nor escape freshness checking once it is
real.

Two hazards the adoption turned up, both now in the project contract rather than
only here. A `theories` entry is a theory name, never a path -- a slash there
fails the whole session at load, so jEdit does not start and the mistake looks
like a dead editor; `pixi run sessions-check` catches it without Isabelle. And a
theory that loads as `Draft.<name>` is not verified in its session: a draft node
resolves imports without consulting the session, and saving from one rewrites
same-session imports into session-qualified form, which the drift check catches
but only after the fact.
