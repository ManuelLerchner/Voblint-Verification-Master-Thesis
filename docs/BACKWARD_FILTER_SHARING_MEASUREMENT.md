# Sharing the backward-filter recursion: a measurement

`afilter` and `afilter_st` are the same five-clause recursion over `exp`,
differing only in how they read and write one variable, and each pair is joined
by a commutation proof that walks the expression a third time. Seven such
recursions exist across `Backward_Domain` and `Exec_Backward`. This note records
what it cost to share one of them, so the question does not have to be reopened
from scratch.

**Outcome: not adopted.** The production definitions are unchanged. The
prototype was removed from `src/` after measuring; only this note remains.

## What was built

An interface supplied as data, so the algorithm carries no proof premises and
its code equation stays clean:

```isabelle
record ('s, 'a) state_ops =            (* plain *)
  so_read  :: "'s => vname => 'a"
  so_write :: "vname => 'a => 's => 's"

record ('s, 'a) narrow_ops =           (* lifted: failure is its own operation *)
  no_read   :: "'s => vname => 'a"
  no_narrow :: "vname => 'a => 's => 's lifted"
```

with the laws in a locale beside it, not on the algorithm:

```isabelle
read_rb:   "so_read A (rb s) = so_read C s"
write_rb:  "rb (so_write C x a s) = so_write A x a (rb s)"
narrow_rb: "map_lift rb (no_narrow C x a s) = no_narrow A x a (rb s)"
```

The numeric operations are *not* re-abstracted: both instances receive the same
`'a backward_exec_ops` value, so no "these fields agree" assumption is needed.

Both existing constants came back as instances, each by a one-line induction,
and `write_rb` needed no new proof --- `fun_of_resolved_st_q_for_update` already
exists and is `[simp]`.

## Measured cost

Plain arithmetic slice:

| | baseline | prototype |
| --- | --- | --- |
| recursion, abstract + executable | 13 + 23 = 36 | generic 25 + record 6 + instances 6 = 37 |
| bridge | `afilter_st_commute` 30 | shared 12 (once) + 9 per instance |

Lifted arithmetic slice --- the one that decides it:

| Part | Lines | Paid |
| --- | --- | --- |
| `record narrow_ops` | 3 | once |
| `fun afilter_lift_gen` (+ `Bot` lemma) | 34 | once |
| `locale narrow_readback` + shared bridge | 23 | once |
| instances + selector equations | 16 | per instance |
| exec instance lemma | 4 | per instance |
| locale discharge | 9 | per instance |
| derived representation bridge | 6 | per instance |
| semantic: `afilter_lift_abs_step` + normalize | 37 | once, abstract |
| **total** | **132** | vs **76** baseline |

Baseline is `afilter_st_lift_with` (32) plus `afilter_st_lift_correct` (44).

At one executable representation the abstraction costs about 56 lines more than
it saves. Roughly 60 lines are one-time, 37 are the semantic argument, and
around 35 recur per instance, which puts break-even near a third
representation. **Treat that as an estimate, not a result**: it assumes each new
representation would otherwise repeat the whole baseline, and that every
instantiation costs the same. Neither was measured.

## The finding worth keeping

Separating the interface separated the proof, and exposed an asymmetry the
fused proof hides:

> Representation correspondence needs only the read and narrow laws.
> Early-failure equivalence additionally needs reductivity and emptiness
> preservation (`afilter_reductive`, `is_empty_state_antimono`).

`afilter_st_lift_correct` proves both at once in one 44-line induction, so the
semantic half is already paid for there --- it is not free work the current
design avoids, only work it does not name. The lifted filters are therefore not
the plain ones over a different state: the executable one collapses to `Bot` at
the leaf that empties, the abstract statement normalizes once at the end, and
they agree only on live inputs. Any future sharing must preserve that
difference rather than assume the two are instances of one thing.

## Two proof-engineering traps, both hit

- A locale-derived bridge whose discharge lemma leaves a schematic variable
  (`?gs` here) will absorb the first `[of ...]` argument into that slot. Use
  `where name = ...` instead of positional instantiation.
- Unfolding a record definition (`abs_nops_def`) inside a case proof replaces
  the record with a literal, after which every lemma stated over the *named*
  record stops matching. Prove selector equations (`no_read abs_nops = ...`)
  and leave the definition folded.

## What was never tested

The experiment stopped after lifted arithmetic. Untested, and required before
any migration:

- a Boolean join case (`Or True`), which adds a join law and its own precision
  argument;
- public-equation recovery --- the prototype *recovered* `afilter`/`afilter_st`
  rather than defining them as instances, so "the semantic equations still read
  as the semantics" was never demonstrated;
- code generation of an actual specialization, not just of the generic
  algorithm;
- a batch build: the prototype was never listed in a `ROOT`, so no green build
  ever covered it.

## If this is reopened

A second non-`abs_state` representation is the trigger, and it is not automatic:
this interface models pointwise reads and updates, so a relational carrier
counts only if it can satisfy the laws and support the filtering algorithm at
all. Check that before counting it as an instance. Shared recursion also
prevents structural drift only --- instances still supply their own operations,
and the existing correspondence proofs already protect the relationship they
state.
