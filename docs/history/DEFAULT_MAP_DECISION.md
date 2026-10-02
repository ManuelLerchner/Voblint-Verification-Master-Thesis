# Factoring the carrier as `default_map × default_map`: not done

Decided 2026-10-02, after measuring; nothing was implemented.

## The proposal

`default_st` is one quotient over a pair of dictionaries, local and global,
identified by agreement of every lookup
(`src/Abstract_Interpreter/Exec/State/Default_St_Base.thy`). The proposal was to
quotient one dictionary instead, `default_map = default_dict / ∼`, and build the
state as `default_map_L × default_map_G`. Respectfulness would then be proved
once per dictionary operation, and the ownership projections
(`restrict_local_default_st`, `restrict_global_default_st`,
`combine_default_st`) would become tuple operations.

The criterion was a clear reduction of representation and proof machinery,
with nothing above the readback ρ changing.

## What the measurement found

Measured on the branch of #290: the five `Default_St_*` theories and
`Ownership_Split_Exec` have 1777 lines; 15 `eq_default_st_rep_*` lemmas,
13 `lift_definition`s, 20 uses of `transfer`. The blocks that exist because the
quotient is over the whole pair come to about 420 lines:

| Block | Lines | Under the proposal |
|---|---|---|
| `eq_default_st_rep_*` respectfulness lemmas | ~105 | mostly gone; lookup, update, the pointwise combinator and the emptiness test need one each on `default_map` |
| raw definitions and their lookup lemmas (restrict, combine, assign, bind, enter, join, widen, narrow) | ~110 | componentwise definitions and lookup lemmas, about half the size |
| emptiness-test soundness and exactness (`Default_St_Reachability`) | ~140 | stays: the argument is about each dictionary's default and entries |
| readback lemmas (`default_st_rep_to_fun_*`) | ~65 | stay, componentwise |
| class instances | — | added: instances on `default_map`, then componentwise instances on the pair (bot, order, sup, widen, narrow, equal) |

The estimate is between about 100 lines saved and break-even, at most 6% of
the carrier. Respectfulness is already cheap: one congruence lemma for the
pointwise combinator serves join, widening and narrowing. The hard proofs are
semantic and survive either representation. The one qualitative gain is that
the projection laws (idempotence, annihilation, `combine` of the two
projections) would follow by `simp`; today three of them are proved by
extensionality in `src/Examples/Sign/Example_Sign_Mixed_Flow.thy`.

## Decision

Not worth changing a carrier every executable analysis runs on. The projection
laws a generic ownership-split wrapper needs can be proved over the current
quotient. Reopen this only with new evidence: repeated cost that comes from the
whole-pair quotient specifically.
