# Digest-spine removal handoff

Status: **DONE (2026-07-18).** The removal this handoff planned is fully executed
across Stages 0–5 — `Voblint_Formalization` batch-green, 0 `sorry`, 0 `oops`, and
no live `.thy` references to any removed symbol. Outcome record:
docs/DIGEST_SPINE_REMOVAL_PLAN.md (Stage 6). Archive tag
`archive/relational-digest-experiment` (`4779e90f`) is the recovery point. This
document is retained as the historical handoff.

This handoff is for the next agent performing the relational digest-spine removal.
Read this document with:

* docs/DIGEST_SPINE_REMOVAL_PLAN.md — authoritative migration plan;
* docs/ABSTRACT_CONTEXT_AUDIT.md — evidence that retained analysis is genuinely
  context-sensitive; and
* docs/CONTEXT_POLICY_MIGRATION.md — superseded relational design proposal and
  decision history.

## Executive decision

Retire the relational digest experiment from the main development. Retain the
Goblint-faithful functional context-sensitive architecture.

The retained model is:

~~~text
valid_ltr
  → collect_by
  → cfg_collect_ctx_act through key enterc seedc
  → functional keyed generator and reads
  → TD-side solver soundness

cfg_collect remains the plain collecting endpoint.
~~~

The cleanup removes relational compatibility and history-digest semantics. It does
not remove context sensitivity.

## Settled decisions

| Topic | Decision |
| --- | --- |
| Concrete witness | Keep valid_ltr as the interprocedural execution witness. |
| Generic collection | Keep collect_by. It exists in CFG_Local_Trace. |
| Activation collection | Keep cfg_collect_ctx_act as the key projection of valid_ltr. |
| Plain collection | Keep cfg_collect as the stable context-insensitive endpoint. |
| Context-sensitive abstraction | Retain exact functional keys, keyed unknowns, functional callee routing, and caller-context restoration. |
| Relational digest | Remove cmp-based compatibility, trace_witness, cfg_collect_trace, cfg_collect_ctx, proc_entry trace seeding, and value-history semantics. |
| ContextPolicy design | Do not implement it now. It is a valid general design only if relational digest semantics becomes a project goal again. |
| Generator/read infrastructure | Extract non-digest pieces first; never retain a relational theorem merely with equality supplied as a degenerate parameter. |
| Documentation | Treat the removal plan as current. Preserve the two prior documents as decision history until Stage 6 writes the outcome record. |

## What succeeded and what was not adopted

The initial unification proposal had two separable parts.

1. It introduced valid_ltr, collect_by, and the activation collector as the
   functional witness/key architecture.
2. It proposed reconstructing relational digest collecting through dg o flatten and
   unifying the flat trace spine with valid_ltr.

Only the first part is retained. collect_by exists, and cfg_collect_ctx_act is
already proved equal to its valid_ltr/key instance.

The flatten-based relational digest reconstruction is not the target architecture.
Do not describe valid_ltr or collect_by as failed. The project deliberately decided
that relational digest precision is outside the Goblint-faithful main line.

## Verified current facts

These facts were checked through Isabelle I/Q. Recheck them after edits.

| Fact | Location |
| --- | --- |
| collect_by is defined over a witness set, node observer, store observer, and context observer. | CFG_Local_Trace.thy, around line 626 |
| cfg_collect_ctx_act has argument order enterc, seedc, g, S, v, c. | CFG_Local_Trace.thy, around line 648 |
| cfg_collect_ctx_act equals collect_by over valid_ltr, sink_node, sink_store, and key enterc seedc. | CFG_Local_Trace.thy, around line 653 |
| valid_ltr has root, intra, call, and return constructors. | CFG_Local_Trace.thy, around lines 127–148 |
| dg_postfix_c_collect_sound is a per-key theorem over plain cfg_collect. | DG_Context_Soundness.thy, around line 141 |
| dg_collect_ctx_sound is the relational DG endpoint and takes dg, cmp, rt, and entdg. | DG_Route_Soundness.thy, around line 21 |
| activation_collect_sound is the retained generic activation endpoint. | Activation_Backbone.thy, around line 40 |
| side_cfg_T_eff_cmp and its seeded variant are mixed generator infrastructure. | TD_Side_Eff_Cmp_Gen.thy, around lines 58 and 97 |
| interval and executable Sign DG flagships conclude over cfg_collect. | Example_Interval_DG_Flagship.thy around line 256; Exec_Sign_DG_Run.thy around line 136 |

Important distinction: a plain cfg_collect theorem does not prove an import-free
digest removal path. For example, Exec_Sign_DG_Run imports Sign_Exec_Sound, which
currently imports CFG_Collect_Trace. The Stage 1 ledger must classify whether each
such edge is semantic or only theorem placement.

Likewise, the activation collector flagship imports Interval_Point_Digest. Do not
assume an activation theorem is digest-independent before classifying the imported
facts it consumes.

## Non-negotiable preservation obligations

Keep named replacements for all retained endpoints before deleting theories.

~~~text
plain collecting:
  cfg_collect g S v ⊆ gamma (meaning sigma v)

activation collecting:
  cfg_collect_ctx_act enterc seedc g S v c
    ⊆ gamma (meaning_ctx sigma v c)

per-key DG plain endpoint:
  cfg_collect g S0 v ⊆ dg_gamma_c sigma ctx v
~~~

Preserve the solver chain:

~~~text
computed solver result
  → partial/post solution
  → abstract semantic post-solution
  → collecting soundness
~~~

Also preserve functional call/return behavior, parameter transfer, destination-aware
returns, and global/local routing required by the ongoing parameter/return work.

## Scope

### Retain

* valid_ltr, collect_by, cfg_collect_ctx_act, and cfg_collect;
* Activation_Backbone and Activation_Local_Sound;
* DG_Framework, DG_Soundness, DG_Context_Soundness;
* executable D/G bridges and maintained Sign/Interval flagships;
* source activation soundness;
* non-digest functional keyed generator, read, and combine infrastructure after
  extraction.

### Remove after dependencies are severed

* trace_witness and trace_witness_ctx;
* cfg_collect_trace and cfg_collect_ctx;
* Ctx_Collect_Backbone;
* relational cmp and gcmp APIs;
* proc_entry trace constructors;
* value-history digest collection and readers;
* relational DG route soundness;
* digest precision examples and relational executable examples.

### Split before deciding

* TD_Side_Eff_Cmp_Gen;
* TD_Side_Eff_Cmp_Pull;
* TD_Side_Eff_Cmp_Sound;
* Clean_RRead_Sound;
* Seed_EnterMono_Lift;
* Digest_Global_Read;
* shared portions of CFG_Collect_Trace.

Classify individual definitions/theorems:

~~~text
D1 generic generator infrastructure
D2 functional activation/keyed-read infrastructure
D3 relational digest infrastructure
D4 dead compatibility wrapper
~~~

Move D1 to neutral retained theories. Restate D2 directly over cfg_collect_ctx_act
or cfg_collect. Delete D3 and D4 only after call sites move.

## Migration order

### Stage 0 — archive

Create the user-approved archive tag or branch for the digest experiment. Record its
actual revision in the removal plan. Do not retain dead code in the main session for
archival reasons.

### Stage 1 — dependency and theorem ledger

This is the next action. Do not delete or rename anything before it.

For every retained use of a Category C or D theory, record:

~~~text
current theorem
defining theory
premises
semantic endpoint
activation or executable call site
replacement theorem
destination theory
classification D1/D2/D3/D4
~~~

Produce direct and transitive importer lists for:

~~~text
CFG_Collect_Trace
Ctx_Collect_Backbone
DG_Route_Soundness
Value_Digest_Reader
Digest_Global_Read
TD_Side_Eff_Cmp_Gen
TD_Side_Eff_Cmp_Sound
Clean_RRead_Sound
Seed_EnterMono_Lift
Interval_Point_Digest
~~~

For Goblint-alignment claims, pin a Goblint revision and record source locations.
Statements such as “no Goblint counterpart” are hypotheses until supported this way.

### Stage 2 — rebase trace consumers

Move Category B final-store statements to cfg_collect when witness structure is
irrelevant. Use valid_ltr only when a theorem genuinely needs activation structure.

Migrate examples first, then generic Sign and mixed-flow results, then split
Trace_Analysis_Sound. Preserve store-level conclusions with named replacements.

Gate before Stage 3:

* every changed theory has empty I/Q error diagnostics;
* no Category B theory imports CFG_Collect_Trace solely for cfg_collect_trace;
* no Category B theorem mentions trace_witness; and
* run the full project build.

### Stage 3 — functional extraction

Create neutrally named functional keyed-read/generator theories. Remove cmp from
retained signatures; use exact key equality in the functional interface rather than
a relational equality instance.

The activation and executable paths should no longer import Ctx_Collect_Backbone or
mention cfg_collect_ctx.

### Stage 4 — sever generator dependencies

Make retained generator/realization code depend only on exact keys, functional
enter routing, call/return combine, required global layout, cfg_collect, and
cfg_collect_ctx_act.

Pay special attention to rt, cmb, gkey, former gcmp, enterc, seedc, and
destination-aware return routing.

Gate before Stage 5:

* functional keyed paths are I/Q clean;
* no retained signature exposes cmp = equality; and
* run the full project build.

### Stage 5 — delete relational spine

Delete Category C only after the ledger is complete and retained replacements build.
For CFG_Collect_Trace, move only definitions with live non-digest users; delete
trace_witness, cfg_collect_trace, cfg_collect_ctx, proc_entry constructors, and
digest-only projection/adequacy facts.

Gate before Stage 6:

* grep finds no live relational digest references;
* changed theories are I/Q clean; and
* run the full project build.

### Stage 6 — session and documentation cleanup

Update ROOT files, aggregate theories, READMEs, dependency diagrams, GraphViz
renderers, and migration documents. Record the archival reference, retained
machinery, and deliberately removed capabilities.

### Stage 7 — final validation

Run the full project build and verify executable Sign, interval flagship,
activation flagship, source lift, and parameter/return examples. Confirm no new
sorry, oops, excluded sessions, or generated proof artifacts.

## Verification workflow

Use I/Q for theory reads, edits, diagnostics, and proof exploration. Do not read or
write theory files through host filesystem tools.

Use this validation cadence:

~~~text
within a stage: I/Q diagnostics and affected-session checks
after Stage 2: full project build gate
after Stage 4: full project build gate
after Stage 5: full project build gate
Stage 7: full project build and executable/flagship validation
~~~

Batch builds are gates, not an inner proof-debugging loop.

## Abort conditions

Stop and report before redesigning if any retained flagship truly needs:

* relational cmp compatibility;
* one concrete execution in multiple abstract context slots;
* trace_witness.proc_entry;
* digest history;
* relational global-read filtering;
* a weaker main cfg_collect guarantee;
* stronger assumptions than the current functional flagship supplies; or
* relational machinery for destination-aware returns.

An import edge alone is not an abort condition. Classify the theorem use first.

## First command sequence

1. Inspect current git status. Preserve unrelated edits, especially any user work in
   CFG_Local_Trace.thy.
2. Authenticate I/Q and open the theories named in the Stage 1 ledger.
3. Build the importer and theorem-use ledger without editing theories.
4. Report the ledger, semantic versus placement dependencies, and the proposed
   smallest Stage 2 slice.
5. Wait for authorization before deleting files, creating archival refs, or starting
   the source migration.

## Current documentation state

The three decision documents are new in the working tree:

* ABSTRACT_CONTEXT_AUDIT.md;
* CONTEXT_POLICY_MIGRATION.md; and
* DIGEST_SPINE_REMOVAL_PLAN.md.

The removal plan is the current architecture. The audit and ContextPolicy document
remain useful history explaining why relational contexts were considered and why the
project pivoted. Do not silently rewrite historical claims; Stage 6 should add a
short outcome record and update current-facing documentation.

