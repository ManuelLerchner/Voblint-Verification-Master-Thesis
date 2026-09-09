# Analysis registration generation

`assembly/analyses.yaml` is the registry. It answers four questions and nothing
else:

1. Which verified implementation is this domain?
2. Which solver and context combinations does it publish?
3. Which combination is the default?
4. Which API capabilities does each published combination expose?

```text
assembly/analyses.yaml
       |
       +-- scripts/gen_analysis_assembly.py
             +-> src/Analyses/<Domain>/generated/<Domain>_Assembly.thy
             +-> src/Executable_Surface/CLI/generated/Dispatch_Tables.thy
             +-> src/Executable_Surface/CLI/generated/Config_Tables.thy
```

How those choices become theories, bindings, proofs and dispatch equations is
the generator's decision. Theory names, paths, imports, interpretation binders,
published prefixes, which route publishes the full name set, the
equation-agreement lemmas and the entire proof text are derived by convention,
identically for every domain. Domain rationale -- why a lattice has finite
height, why a solver choice matters here -- belongs in that domain's README.

## What is generated, and what is not

Generated: the `global_interpretation` of `unit_dg_analysis` per published
route, its `defines` block, the `[code_unfold]` declaration a named `dg_spec`
needs, the lemmas relating each sibling discipline's equation system to the
production one, and the CLI's dispatch and resolver tables.

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
like `analyse_interval_td_report`. Every entry is a rename waiting to happen,
not an extension point. Nothing outside `legacy:` names an identifier a
convention could have produced.

Int sits in the registry as `assembly: false` -- registered for dispatch, not
migrated onto the shared assembly, so all of its route names are legacy.

## The dispatcher tables

`analyse`, `analyse_with_solver`, `analyse_with_state` and
`analyse_with_state_default` are one table read four ways, plus the agreement
lemmas pinning each domain's default. Sixty equations, and the `None` entries
are the part that rots: a pairing answers `None` because the registry publishes
no route for it, not because someone remembered to write it down in four
places.

Generation reproduces all sixty handwritten equations exactly. It also fixes two
things they had drifted on: 68 lines in `Analyse_Dispatch` and 51 in
`Analysis_Config` run past the 100-symbol layout rule, and
`analyse_with_solver_parity_default` is missing while the other three domains'
default-agreement lemmas exist.

`Dispatch_Tables` needs `abstract_value` and `tag_states` in scope. Those are
handwritten and stay so -- the datatype names each domain's abstract state
type, which is not registration -- so adopting it means splitting them out of
`Analyse_Dispatch` into a small carrier theory.

## The resolver

`resolve_analysis_config` is the same support question in a third dimension:
domain, solver, context. `Ctx_None`'s support is not declared separately -- it
is exactly the set of routes the domain publishes, which is what the dispatcher
reads too, so the two cannot disagree. Only the context modes carry their own
entry, because a routed instance at a context is different work from a solved
table at `Ctx_None`, and a domain can have one without the other. A domain that
names no contexts answers `None` at every contextual cell.

Equivalence was checked by evaluating both tables at every point -- four
domains, five solver selections including the implicit one, `Ctx_None`,
`Ctx_EntryState`, and `Ctx_CallString` at `k = 0` and `k > 0`. Eighty points.
Diffing the text would not have established this: the two use different pattern
styles and reach the same answers.

All eighty agree: replacing the handwritten resolver with the generated one
changes no answer at any point of the space.

### The bound below which a domain publishes nothing

A call-string context carries `min_bound`, the shortest bound its domain
publishes. It is 1 everywhere today, which the generated table expresses with
the same `if k = 0 then None` guard the handwritten one uses.

That guard is a usability decision, not a soundness one, and the registry says
so where it is set. `cs_route k u ctx d ca = take k (u # ctx)`, so `k = 0`
routes every activation to `[]` -- as well-defined as any other bound, and
finite by the same `length (cs_route k ...) \<le> k`. `Analysis_Config`'s own
prose already concedes this and rejects the value on usability grounds. Those
seven guards, and the four `analyse_config_ctx` premises that follow from them,
are the only nonzero-`k` hypotheses in the tree outside the CLI's two files;
`Call_String_Context` and `Call_String_Routed_Context` have none.

Lowering `min_bound` to 0 is therefore a behaviour change, not a table swap. A
caller selecting `call-string=0` would get a result table keyed by call strings
that all happen to be empty, which is *not* `Ctx_None` -- that solves a flat
system and publishes at `unit`. Collapsing the two would need a theorem relating
the two unknown spaces, which nobody has written. So it belongs in its own
change, with its own justification, its own revised theorems (the pinned
`..._callstring_zero_invalid` lemma inverts) and a witness showing what the
`k = 0` table actually contains. Adoption of the resolver preserves today's
behaviour exactly.

## What this costs

The tooling is 1290 lines -- registry, generator, ROOT lint, hand-written
expectations, this document. It produces 845 lines of theory. Both numbers are
in the repository, so the repository grows by about 1290 lines; generation
replaces handwritten lines with generated ones rather than removing them.

The figure that matters for maintenance is different, and only holds once the
handwritten originals are actually deleted: 1290 lines that are maintained
against 845 that are not, a net increase of about 445 in source anyone edits.
Generation is not a size reduction under any accounting, and no volume of output
would make it one.

What it does remove is 225 manually maintained occurrences: eight
interpretations discharging ten obligations each, a support matrix written out
four separate times (16 + 16 + 4 dispatcher equations and 40 resolver
equations), and 69 publication-name bindings. Those are repeated sites rather
than independent decisions -- many follow from one choice, which is the point:
they had to agree with each other and were kept in agreement by hand. They now
follow from four registry entries. The `None` entries are the sharpest case: a
pairing is unsupported because no route is published, which four handwritten
tables previously stated separately and could disagree about silently.

So the value is consistent registration and cheap updates, not fewer lines.

The failure mode to watch is not a domain needing a shape of its own. A domain
can legitimately fall outside the supported family -- Int does today, and its
`assembly: false` entry says so without distorting anything. The warning sign is
arbitrary exceptions accumulating *inside* the generator, one per domain, at
which point the registry has become a second programming language and the
uniform proof text is a fiction.

## Validation

The generator refuses a registry that is not valid policy: a duplicated domain
name, value type, report tag, binder or published prefix; a domain publishing no
route; a route naming an unknown solver; a context default outside its own
supported set; a legacy name for an unpublished route; a route naming a report
but no state report; a dispatch-only domain with no legacy names.

## Independent expectations

`tests/test_analysis_registry.py` is deliberately not derived from the registry.
It writes the support policy out by hand -- each domain's default, Sign's and
Parity's rejection of both widening rules, Parity's absence at both contexts,
Int's per-origin gap at a context but not at `Ctx_None`, `k = 0` resolving like
any other bound -- and checks the generated theories against it, including that
the resolver and the dispatcher agree on which pairings are supported. Sixty-one
expectations. A registry change that alters what the CLI offers fails them, and
the expectation is then updated deliberately.

## Drift

```bash
pixi run gen-assembly     # regenerate
pixi run assembly-check   # fail if the checked-in theories are stale
```

`--check` diffs regenerated output against the checked-in files itself, so it
needs neither git nor Isabelle, and it runs in `ci`.

`cli_adopted: false` in the registry says the two CLI tables are generated but
not adopted: `Analyse_Dispatch` and `Analysis_Config` still own those equations
by hand. An unadopted output renders under `--out` and is never written into the
tree or demanded by the drift check, so neither an accidental run nor the ci
gate can plant a theory nobody decided to adopt. Flip the flag in the commit
that checks them in.

Two hazards the adoption turned up, both now in the project contract rather than
only here. A `theories` entry is a theory name, never a path -- a slash there
fails the whole session at load, so jEdit does not start and the mistake looks
like a dead editor; `pixi run root-entries` catches it without Isabelle. And a
theory that loads as `Draft.<name>` is not verified in its session: a draft node
resolves imports without consulting the session, and saving from one rewrites
same-session imports into session-qualified form, which the drift check catches
but only after the fact.
