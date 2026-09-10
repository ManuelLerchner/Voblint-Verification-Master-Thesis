# Analysis manager migration: should `gs` become a record?

Research question: is the in-flight `gs :: vname => bool` explicit-parameter
migration the right final shape, or should it converge toward a Goblint-style
manager record (`man`) bundling `gs` and other configuration, threaded through
`pstep`/`cstep`/transfer functions?

Recommendation: continue Option A (keep `gs` as its own explicit parameter).
Do not introduce a manager record or a configuration locale. Details below.

**Status:** completed in commits `e10b145d` and `7b5c049` (section 10).

## 0. Where the migration actually stands right now

This matters because part of the task brief's background is stale relative to
the live working tree, and the staged plan in section 4 has to start from the
real state, not the assumed one.

- Commit `49c84bc` widened `pstep`/`pcompletes`/`psteps`
  (`src/VIMP/VIMP_Proc.thy`) to take `gs` explicitly.
- Commit `3d3ab7b` widened `combine_collect`/`call_enter`
  (`src/CFG/CFG_Def.thy`) to take `gs`, and its commit message claims `cstep`
  was propagated too.
- As of this investigation, `git status` shows exactly one modified file:
  `src/CFG/Compiler/Located_Exec.thy`, uncommitted. `git diff` on it shows
  `cstep`'s signature and all three rule bodies (`Intra`/`Call`/`Return`)
  changing from a bare `cstep :: cfg => cconf => cconf => bool` (with `for g`)
  to `cstep :: (vname => bool) => cfg => cconf => cconf => bool` (with
  `for gs and g`), replacing the literal `call_enter is_global ...` /
  `combine_collect is_global ...` inside the rule bodies with `call_enter gs
  ...` / `combine_collect gs ...`. This is exactly the "paused mid-edit" work
  the task background described -- it is real, uncommitted, and not yet
  propagated to callers.
- Six files call `cstep` and will break once this lands, because `cstep` gains
  a leading positional argument: `src/CFG/Compiler/Control_Residual.thy`,
  `src/CFG/Compiler/Control_Simulation.thy`, `src/CFG/Compiler/Located_LTR.thy`,
  `src/Examples/CFG/Example_Compile_Baseline.thy`,
  `src/Examples/CFG/Example_Compile_Regression.thy`,
  `src/Examples/CFG/Example_Control_Simulation_Regression.thy` (148 combined
  `cstep` occurrences across these six plus `Located_Exec.thy` itself).
- Nothing downstream of `cstep` has been touched (`git status` confirms no
  other file is dirty), so the next batch build will fail the moment this
  edit is saved, until those six files are updated to pass `gs` (in practice
  `is_global`) positionally.
- `src/Examples/CFG/Example_Inc_Proc.thy` is the one place that actually
  supplies something other than `is_global`: it proves the source-level
  theorem again with `gs = declared_global inc_program` instead of
  `gs = is_global`, using the `declared_global :: imp_prog => vname =>
  bool` classifier defined in `src/VIMP/VIMP_Notation.thy` (`declared_global p
  x <-> x : set (declared_global_vars p)`, `declared_global_vars` a field of
  the `imp_prog` record). No other file switches; every other one of the 520
  `is_global` occurrences across 57 files is still literal.

## 1. Where `is_global`/`gs` actually sits, classified

`rg -c is_global src/` totals 520 hits in 57 files. Breaking that down by
call-site shape:

| Pattern | Hits | What it is |
| --- | --- | --- |
| `call_enter is_global ...` | 90 | CFG-layer call-entry transfer, `CFG_Def.thy` |
| `combine_collect is_global ...` | 88 | CFG-layer return-combine transfer, `CFG_Def.thy` |
| `enter_state is_global ...` | 75 | VIMP-layer store split on procedure entry, `VIMP_Globals.thy` |
| `combine_states is_global ...` | 24 | VIMP-layer store split on return, `VIMP_Globals.thy` |
| `is_global_def` (unfolding) | 23 | Proof-script unfolds of the constant itself |
| bare `is_global x` (guard/simp use) | 72 | Ad hoc case splits inside proofs |
| everything else | ~148 | Locale `assumes` clauses, lemma statement text, comments |

Classifying by what the value is actually for, against the categories the
task asked to weigh:

| Category | Genuinely a shared "manager" concern? | Evidence |
| --- | --- | --- |
| Global/local classification (`gs`) | Yes, but it is already exactly one parameter, threaded correctly. | `combine_states`, `enter_state` (`VIMP_Globals.thy`), `combine_collect`, `call_enter` (`CFG_Def.thy`), and (once the pending edit lands) `cstep` (`Located_Exec.thy`) all take `gs` as their own leading argument. `pstep`/`pcompletes`/`psteps` already do. This is the whole migration; it does not need a record to be "done," it needs the remaining ~470 literal-`is_global` call sites and locale `assumes` clauses switched to accept `gs` instead of hardcoding `is_global`. |
| Context handling | No -- already has its own dedicated abstraction, deliberately separate from `gs`. | `docs/LOCALES.md` documents a context-handling locale family (`context_transfer` in `src/CFG/Collecting/CFG_Collect_Trace.thy` fixes `dg`, `cmp`, `seed_ctx`, `step_ctx`, `comb_ctx`; `dg_ctx_activation`/`routed_context` in `src/Analysis/Generic/Solver/Context/DG/Routed_Context.thy` fix `seed_key`, `enterc`, routing predicates). Context selection is a full interpreted structure with its own soundness obligations -- it is not a scalar flag, and folding it into a `gs`-shaped record would merge two independently-varying axes (which globals exist vs. how contexts are keyed) into one object neither locale actually needs together. |
| Precision configuration (widening, thresholds) | No -- handled by the domain type-class/locale stack, not by the CFG/VIMP layer at all. | `sound_domain = bounded_semilattice_sup_bot + gamma + mono`, `abstract_domain = sound_domain + widening` (Isabelle `class`es, per-type, per `docs/LOCALES.md` header). These live one layer up from where `gs` lives (`Analysis/Generic/Domain`) and are already keyed by the abstract carrier type, not by a runtime record value. |
| Domain-specific settings (Sign/Interval/Mixed knobs) | No. | `src/Analysis/Instances/Sign/Sign_Transfer.thy`, `src/Analysis/Instances/Interval/Interval_Transfer.thy`: each instance's transfer obligations are locale interpretations (`sound_transfer`, `sound_effectful_transfer`) parametrized over that domain's own carrier type; they call `enter_state is_global s` the same way every other consumer does. No instance-specific configuration value exists to bundle. |
| Execution representation (`Exec_St`) | Explicitly out of scope, per the task brief and repo history. | `src/Analysis/Generic/Domain/Exec_St.thy` appears in the `is_global` grep (it interprets `enter_state`/`combine_states` for the executable finite-map state), but the repo's own retirement history (`docs/ROADMAP.md` "Intentionally retired components") treats the classical/executable spine as settled, low-churn architecture; nothing here argues for touching it. |

The upshot: of the four candidate "manager fields" the task asked to weigh,
only one (`gs`) is actually a cross-cutting scalar that flows through many
unrelated proof layers the way Goblint's `man` fields do. The others already
have purpose-built, independently-evolving abstractions. A shared record
would either duplicate those abstractions or, worse, couple them, which is
exactly the "dumping ground" failure mode the task brief warned against.

## 2. Candidate manager record, and why it does not earn its keep

A minimal Goblint-shaped record would look like:

```
record analysis_manager =
  gs :: "vname \<Rightarrow> bool"
```

Fields considered and rejected:

- Context policy fields (`seed_key`, `enterc`, `cmp`, ...): rejected. These
  are already locale `fixes` on `context_transfer`/`routed_context`, not
  runtime values -- a locale fixes a function symbol that later gets
  `interpretation`-instantiated and reasoned about generically; a record field
  is a value threaded at call sites. Moving context policy into a record
  field would mean re-deriving all of `Routed_Context.thy`'s soundness
  obligations against `field_of_record M` instead of a locale-fixed constant,
  losing the ability to state and reuse `route u ctx ... = enterc u ctx ...`
  as a clean equation.
- Precision/widening configuration: rejected. Lives on the domain type class
  (`abstract_domain = sound_domain + widening`), which is per-type, not
  per-value. A record field can't carry a type-class obligation; this would
  have to become a second axis of dependent typing that the record cannot
  express without extending it back into a locale anyway.
- Domain-specific settings: rejected -- no such settings exist today (checked
  `Sign_Transfer.thy`, `Interval_Transfer.thy`, `Mixed_Sign_Interval.thy`;
  each is a locale interpretation over its own carrier, no runtime knob).
- Goblint's effectful fields (`emit`, `spawn`, `split`, `sideg`, `ask`):
  rejected outright -- see section 5. These have no meaning in a pure
  functional soundness proof; a record field can't encode "mutable callback"
  in HOL, and this formalization's side effects are already routed through
  the D/G strategy-tree interface (`docs/DG_COMBINATOR_MIGRATION.md`), not a
  callback record.
- `gs` itself: the one field that survives scrutiny -- and it is already a
  bare parameter with no companion field to justify wrapping it.

A one-field record buys nothing a bare parameter does not already provide, and
costs real friction: every literal instantiation site (`pstep is_global Pi
...`) becomes `pstep (| gs = is_global |) Pi ...`, every locale `assumes`
clause that currently reads `combine_collect is_global dst s t` becomes
`combine_collect (gs M) dst s t`, and pattern-matching a record field inside
an inductive rule body is strictly more characters than matching a bound
variable for zero semantic gain.

## 3. Three options, compared on real signatures

Current (mixed) state, read directly from source:

```
(* src/VIMP/VIMP_Proc.thy -- already migrated *)
inductive pstep :: "(vname \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> (com \<times> store \<times> frame list)
  \<Rightarrow> (com \<times> store \<times> frame list) \<Rightarrow> bool" for gs and \<Pi> where
  Assign: "pstep gs \<Pi> (Assign x a, s, frs) (SKIP, s(x := aval a s), frs)"
  ...

(* src/CFG/CFG_Def.thy -- already migrated *)
definition combine_collect :: "(vname \<Rightarrow> bool) \<Rightarrow> vname option \<Rightarrow> store \<Rightarrow> store \<Rightarrow> store" where
  "combine_collect gs dst s t = combine_assign dst (t ret_var) (combine_states gs s t)"
definition call_enter :: "(vname \<Rightarrow> bool) \<Rightarrow> call_action \<Rightarrow> store \<Rightarrow> store" where
  "call_enter gs ca s = ..."

(* src/CFG/Compiler/Located_Exec.thy -- mid-edit, uncommitted *)
inductive cstep :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> cconf \<Rightarrow> cconf \<Rightarrow> bool" for gs and g where
  Call: "(u, CallEdge dst pars actuals, FunctionEntry q, cont) \<in> calls g \<Longrightarrow>
     cstep gs g (u, s, stk)
       (FunctionEntry q, call_enter gs (CallEdge dst pars actuals) s, (cont, dst, s) # stk)"

(* src/Analysis/Generic/Solver/Context/DG/DG_Soundness.thy -- NOT yet migrated *)
locale sound_dg_spec =
  fixes S :: "('D::bounded_semilattice_sup_bot, 'G::bounded_semilattice_sup_bot) dg_spec"
    and gammaDG :: "'D \<Rightarrow> 'G \<Rightarrow> store set"
  assumes ...
    and combine_sound:
      "\<lbrakk>s \<in> gammaDG dc g; t \<in> gammaDG de g\<rbrakk> \<Longrightarrow>
        combine_collect is_global dst s t \<in> (case dgs_combine S dst dc de g of (g', d') \<Rightarrow> gammaDG d' g')"
```

### Option A -- keep `gs` as its own explicit parameter (continue as-is)

```
inductive cstep :: "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> cconf \<Rightarrow> cconf \<Rightarrow> bool" for gs and g where ...
locale sound_dg_spec =
  fixes S :: "..." and gammaDG :: "..." and gs :: "vname \<Rightarrow> bool"
  assumes combine_sound: "... \<Longrightarrow> combine_collect gs dst s t \<in> ..."
```

- Cost: mechanical -- add one `and gs` binder to each of the locales that
  still hardcode `is_global` inside their `assumes`, and thread `gs` through
  every lemma statement that cites `combine_collect`/`call_enter`/`cstep`
  literally. This is what commits `49c84bc` and `3d3ab7b` already did at the
  VIMP and CFG-definition layers; the pattern is proven to work at this
  project's scale.
- Fits existing precedent exactly: `src/VIMP/VIMP_Notation.thy`'s `imp_prog`
  record already bundles static per-program configuration (`proc_rep`,
  `prog_main`, `declared_global_vars`), but nothing downstream threads the
  record through semantic relations -- `pcompletes`/`pstep` consume the
  record's projection, `declared_global p :: vname => bool`, as a bare
  function, exactly like `gs` today (see
  `src/Examples/CFG/Example_Inc_Proc.thy`). The codebase has already chosen,
  independently, not to thread whole-program records through the operational
  semantics -- a manager record for `gs` would reverse that choice for no new
  reason.
- Sledgehammer/`OF`/`rule` friction: none beyond what already exists. `gs` is
  a first-order argument; `rule cstep.Call[of gs g ...]` and
  `combine_collect_None[of gs]`-style citations work exactly as they do today.

### Option B -- manager record (`M :: analysis_manager`, `pstep M \<Pi> c c'`)

```
record analysis_manager = gs :: "vname \<Rightarrow> bool"
inductive pstep :: "analysis_manager \<Rightarrow> proc_table \<Rightarrow> (com \<times> store \<times> frame list)
  \<Rightarrow> (com \<times> store \<times> frame list) \<Rightarrow> bool" for M and \<Pi> where
  Assign: "pstep M \<Pi> (Assign x a, s, frs) (SKIP, s(x := aval a s), frs)"
  ...
  Call: "... \<Longrightarrow> pstep M \<Pi> (Call dst p actuals, s, frs)
     (SKIP, bind_formals ... (enter_state (gs M) s), Frame s dst # frs)"
```

- Every rule body that touches the classifier gains a `gs M` projection in
  place of a bound `gs` -- pure syntactic overhead for a record with one live
  field.
- `src/VIMP/VIMP_Globals.thy` documents `combine_states`/`enter_state` as
  "self-contained: depends only on the store, not on `com`, small-step, or the
  CFG." Making them consume `analysis_manager` (a type that would need to live
  at or above the CFG layer once it grows any CFG-relevant field) breaks that
  documented independence, or forces `analysis_manager` to be defined so early
  and so thin that it is, again, just `gs` with extra ceremony.
- Every one of the ~470 remaining literal `is_global` call sites becomes
  `(| gs = is_global |)` instead of `is_global` -- strictly more to write, and
  it invites the "dumping ground" pattern CLAUDE.md warns against the moment
  anyone wants to add a second field, since a record with call-site literals
  like `(| gs = is_global |)` reads as an invitation to add sibling fields
  even when (per section 1) those concerns already have better homes.
- Does not reduce the size of the actual migration (still ~470 call sites to
  touch); only changes the shape of what each site is touched into.

### Option C -- locale-based configuration (`locale analysis_environment = fixes M :: analysis_manager`)

```
locale analysis_environment =
  fixes M :: analysis_manager
begin
  abbreviation gs' where "gs' \<equiv> gs M"
  ... pstep, cstep, sound_dg_spec restated inside this locale ...
end
```

- Highest blast radius of the three. `pstep`/`cstep`/`combine_collect`/
  `call_enter` would become locale-qualified constants (e.g.
  `analysis_environment.pstep`), and CLAUDE.md's own audit checklist applies
  directly and unfavorably here:
  - Locale ordering: every existing proof that currently applies
    `pstep.Assign` etc. as a global fact would instead need the
    `analysis_environment` interpretation available first, which the
    project's own "Instantiation gap" guidance flags as easy to get backwards
    (assuming the property before the concrete `gs` is fixed).
  - Instantiation gap: soundness lemmas already proved abstractly (e.g.
    `sound_dg_spec`'s `combine_sound`) would need a matching
    `interpretation analysis_environment` at every one of the ~57 files that
    currently cite `combine_collect`/`call_enter` directly, not just a
    parameter substitution.
  - Shape mismatch: `sound_dg_spec`, `ltr_gamma`, and `routed_context`
    already exist as independent locales with their own `fixes` (`S`,
    `gammaDG`; `g`, `acc`, `enterc`; `seed_key`, ...). Stacking
    `analysis_environment` underneath all three multiplies the
    "interpretation-local premises vs. fully applied global premises"
    mismatch risk documented in `AGENTS.md`/`CLAUDE.md` for each of them,
    since each would need to inherit or align with `analysis_environment.gs`
    on top of its own parameters.
- The project already carries a large, working locale hierarchy
  (`docs/LOCALES.md` lists roughly 15 locales across transfer soundness, RHS
  generation, solver interface, and context/digest reads). That hierarchy is
  justified because each locale abstracts a genuinely reusable proof
  obligation (e.g. "this transfer function is sound"). `gs` is not a proof
  obligation -- it is a data value with no accompanying `assumes`. Locales are
  the wrong tool for a single data value with no laws attached; that is
  precisely what a bare parameter (Option A) is for.

### Verdict

| | Migration cost (~470 remaining sites) | New friction introduced | Fits existing patterns |
| --- | --- | --- | --- |
| A (bare param) | Mechanical, same shape as commits already landed | None | Yes -- matches `imp_prog`/`declared_global` precedent |
| B (record) | Same site count, more syntax per site | Record-field projection noise; invites scope creep | No -- reverses the codebase's own choice not to thread `imp_prog` through semantics |
| C (locale) | Same site count, plus locale interpretation at every citing file | Locale ordering / instantiation gap / shape mismatch, compounded across 3 existing locales | No -- locales are reserved for obligations, not bare data |

## 4. Staged migration plan

Stage 0 and 1 are already-committed history, included for continuity; stages
2+ are the actual proposal.

Stage 0 (done, `49c84bc`): widen `pstep`/`pcompletes`/`psteps`
(`src/VIMP/VIMP_Proc.thy`) to take `gs` explicitly. All call sites instantiate
`gs = is_global`.

Stage 1 (done, `3d3ab7b`): widen `combine_collect`/`call_enter`
(`src/CFG/CFG_Def.thy`) to take `gs`; propagate the parameter through
`valid_ltr`'s rule bodies and every citing file (~30 files). Literal
`is_global` instantiation everywhere.

Stage 2 (in progress, uncommitted): finish widening `cstep`
(`src/CFG/Compiler/Located_Exec.thy` -- the diff already exists on disk).

- Affected files to fix next: `src/CFG/Compiler/Control_Residual.thy`,
  `src/CFG/Compiler/Control_Simulation.thy`, `src/CFG/Compiler/Located_LTR.thy`,
  `src/Examples/CFG/Example_Compile_Baseline.thy`,
  `src/Examples/CFG/Example_Compile_Regression.thy`,
  `src/Examples/CFG/Example_Control_Simulation_Regression.thy`.
- Expected breakage: every `cstep g ...` / `star (cstep g) ...` application
  loses arity match; fix is positional (`cstep is_global g ...`), no semantic
  change expected since these all still target `is_global`.
- Proof impact: should be `simp`/`auto`-absorbable at each site since the
  extra argument is a constant, not a genuinely new degree of freedom, unless
  a lemma pattern-matches on `cstep g` without holes, in which case it needs a
  wildcard or a threaded `gs` var -- expect a handful of one-line fixes, not a
  redesign.
- Rollback point: `git checkout -- src/CFG/Compiler/Located_Exec.thy` restores
  the last-committed state cleanly (confirmed: this is the only dirty file).

Stage 3 (next, not started): widen the locale layer that still hardcodes
`is_global` inside `assumes`/`fixes`-adjacent statements: `sound_dg_spec`
(`src/Analysis/Generic/Solver/Context/DG/DG_Soundness.thy`), `ltr_gamma`
(`src/CFG/Collecting/LTR_Abstract.thy`), `routed_context`
(`src/Analysis/Generic/Solver/Context/DG/Routed_Context.thy`), and their
sibling locales/lemmas across `src/Analysis/Generic/Solver/Context/Activation/`
and `src/Analysis/Generic/Equations/`. This is Option A applied at the locale
layer: add `gs` as a `fixes` (not a new locale, not a record) alongside the
existing parameters of each locale that currently cites
`combine_collect`/`call_enter` literally. Every current interpretation site
instantiates `gs = is_global`, so no proof obligation changes shape -- only
its statement gains a parameter. This is the largest remaining stage by file
count (roughly the ~470 non-Stage-0/1 occurrences) but the lowest-risk kind of
change: adding a `fixes`/argument and re-running `simp`/`auto` at call sites
that already work for the concrete `is_global` instance.

Stage 4 (future, only if a concrete example needs it): pick one soundness
endpoint (`src/Formalization/Pipeline/Source_Activation_Sound.thy` or
`src/Formalization/Pipeline/Run_Analysis_Sound.thy` are the natural targets,
per `docs/GLOSSARY.md`'s "source-facing endpoints") and re-prove it with
`gs = declared_global p` instead of `gs = is_global`, mirroring what
`src/Examples/CFG/Example_Inc_Proc.thy` already did one layer down. This is
the actual point of the migration -- until this stage exists somewhere in the
full pipeline, `gs` is a parameter nothing but the VIMP-level example
exercises differently from a constant. No record or locale restructuring is a
precondition for this stage; Stage 3's plain parameter threading is
sufficient.

No stage in this plan benefits from Option B or C; all four are Option A
scaled up.

## 5. Comparison against Goblint's actual `man` record

Fetched from `https://raw.githubusercontent.com/goblint/analyzer/master/src/framework/analyses.ml`
(current upstream `master`, cross-checked against the cached `/tmp/goblint_base.ml`):

```ocaml
type ('d,'g,'c,'v) man =
  { ask      : 'a. 'a Queries.t -> 'a Queries.result
  ; emit     : Events.t -> unit
  ; node     : MyCFG.node
  ; prev_node: MyCFG.node
  ; control_context : unit -> ControlSpecC.t
  ; context  : unit -> 'c
  ; edge     : MyCFG.edge
  ; local    : 'd
  ; global   : 'v -> 'g
  ; spawn    : ?multiple:bool -> lval option -> varinfo -> exp list -> unit
  ; split    : 'd -> Events.t list -> unit
  ; sideg    : 'v -> 'g -> unit
  }
```

Mapping each field against this formalization:

| `man` field | HOL/formalization analogue | Notes |
| --- | --- | --- |
| `local` | The `D` state explicit arguments already carry (`abs_state`, `store`) | Already a bare positional argument everywhere in this repo; matches Option A style already. |
| `global` (`'v -> 'g`) | The `G`-read half of `dg_spec` (`docs/GLOSSARY.md`: `dg_spec` "transfer, entry, combine, read, and publication interface") | Already modeled as its own locale-fixed function inside `dg_spec`/`sound_dg_spec`, not a manager field. |
| `context`/`control_context` | `context_transfer`/`routed_context` locales (`seed_ctx`, `step_ctx`, `comb_ctx`, `seed_key`) | Already generic, already locale-shaped, deliberately kept separate from `gs` (section 1). |
| `node`/`prev_node`/`edge` | Positional `cfg_node`/`edge_action` arguments already threaded through `cstep`, `edge_step`, `edge_collect` | Already explicit parameters; nothing to migrate. |
| `sideg`, `spawn`, `split`, `emit` | No analogue. | These are mutable, effectful callbacks into Goblint's constraint-solving engine (side-effect a global, spawn a thread analysis, split path state, emit an event). This formalization's side effects are modeled purely, as strategy-tree values consumed by the vendored `TD_side` solver (`docs/DG_COMBINATOR_MIGRATION.md`'s `read_global`/`depend_on`/`answer` combinators), not as callback invocation. A HOL record field of function type could technically hold a "callback," but nothing in the soundness proofs would ever call it effectfully -- it would be dead weight. |
| `ask` | No analogue, and notably not where `gs`-equivalent logic lives in real Goblint either. | `baseUtil.ml`'s real `is_global` is `let is_global (a: Q.ask) (v: varinfo): bool = v.vglob \|\| ThreadEscape.has_escaped a v` -- it takes the query interface, not a static classifier, because in real Goblint globalness can depend on dynamic escape analysis, not just declaration syntax. That is a strictly dynamic, ask-answered predicate, closer in spirit to a full query mechanism than to a record field. This formalization's `gs :: vname => bool` is deliberately the simpler, purely syntactic case (`is_global`) with room to become program-declaration-driven (`declared_global`) -- both are still static, decidable-in-advance classifiers. Modeling `ask`-style dynamism is a strictly larger undertaking than anything this migration currently needs, and nothing in the task background or `docs/ROADMAP.md`/`docs/NEXT_STEPS.md` asks for it. |

The takeaway needs two parts, not one. First: Goblint's `man` record is
partly an artifact of OCaml's module/functor system, which forces every
transfer function in a `Spec` module to receive one uniform record type
regardless of which fields it actually touches -- that part does not transfer
to Isabelle/HOL, which has no such constraint and can give `pstep`/`cstep`/
`combine_collect` exactly the parameters each needs. But `man` is not *only*
that artifact: `node`/`prev_node`/`edge`/`local`/`global`/`context` together
describe a genuine, reusable concept -- the analysis's current execution
context, the "where am I, what do I know here" bundle every transfer function
receives as a unit. That concept has a legitimate future HOL analogue (an
`analysis_env`-shaped record), and section 6 keeps that door open. What does
not transfer, under either framing, is the effectful-callback half
(`sideg`/`spawn`/`split`/`emit`) and `ask`'s dynamic query semantics -- those
are solver-engine plumbing and dynamic escape analysis with no meaning in a
pure functional soundness proof, and no version of a HOL manager record
should try to absorb them.

## 6. Recommendation

This section distinguishes two separate questions that the investigation
brief conflates under one name. "Should `analysis_manager` (a one-field `gs`
wrapper) be the target of the *current* migration?" is settled: no. "Should
this formalization ever converge toward a Goblint-style threaded execution
environment?" is a different, open question that the current evidence does
not settle either way, and should not be closed off by the first answer.

(a) Continue the current `gs` migration exactly as originally planned. The
next step is finishing Stage 2 (commit the in-progress `cstep` widening in
`src/CFG/Compiler/Located_Exec.thy` and fix its six downstream callers), then
Stage 3 (thread `gs` as a `fixes` through `sound_dg_spec`, `ltr_gamma`,
`routed_context`, and their siblings, replacing their literal `is_global`
citations). No pivot to a manager record now.

(b) `analysis_manager` as a one-field `gs` wrapper is over-engineering for
this thesis's actual scope. Per `docs/THESIS_SCOPE_MEMO.md`, the recommended
thesis scope ("Scope A") is already "essentially done -- proof side is polish

- writing," with the supervisor sign-off gate about writing, not new
architecture. Introducing it would touch the same ~470 call sites Stage 3
already needs to touch, add record-projection syntax at every one of them,
and, per section 2, has no second field ready to justify the wrapping. It is
a "missing abstraction" that is, concretely, a single already-generalized
parameter, which is exactly the shape CLAUDE.md tells this project to widen
in place rather than wrap.

The sharpest argument against bundling now is proof ergonomics, not syntax
volume. `combine_states gs s t` lets `simp`/`auto` rewrite `gs` to a concrete
`is_global` (or, at an instantiation boundary, `declared_global p`) directly.
`combine_states (gs env) s t` adds a permanent projection layer: every site
now needs `gs env = is_global` (or the record's `simp` selector lemma) fired
first before the underlying rewrite can apply. At Stage 3's scale -- roughly
470 sites, most closed today by a one-line `simp`/`auto` against a literal
`is_global` -- that projection tax is a real, compounding cost, not a
one-time inconvenience.

(b') That argument caps *when* a manager is justified, but does not cap it
at *never*. `gs` is a single scalar with no fields that travel with it today.
An environment record earns its cost only once several components are
consistently co-threaded together through the same call sites -- the way
`node`/`edge`/`local`/`global`/`context` are in Goblint's `man`, not the way
`gs` is threaded through `combine_states`. Watch for that trigger explicitly,
rather than deciding the question once and shelving it:

- **Phase 1 (current, no record).** Finish the `gs` migration: `is_global`
  becomes a threaded parameter everywhere, `declared_global` instantiation
  works at the example layer, and the locales in Stage 3 quantify over `gs`
  directly. This is Options A applied uniformly, nothing more.
- **Phase 2 (only after Stage 3-4 land, and only if triggered).** Watch for
  parameter clustering: if a locale or top-level relation accumulates three
  or four co-threaded, always-travel-together parameters -- e.g.
  `sound_dg_spec`'s `gs` plus a context policy plus a DG strategy plus a
  trace/query interface, all appearing together at every call site that
  currently just writes `gs` -- that is the concrete signal to introduce a
  bundling record, not a fixed timeline. Absent that clustering, stay on
  Phase 1 shape indefinitely.
- **Phase 3 (only if Phase 2 triggers).** If a record is introduced, bundle
  it only at high-level orchestration interfaces close to
  `run_analysis env program` or a pipeline entry point in
  `src/Formalization/Pipeline/`, where "pass the whole environment" is
  already the natural shape. Leave low-level, single-concern functions like
  `enter_state`/`combine_states`/`combine_collect`/`call_enter` on bare `gs`
  even after such a record exists elsewhere -- they only ever need the
  classifier, and threading the full environment through them would be the
  literal "dumping ground" CLAUDE.md warns against, just moved one layer up.

(c) Smallest concrete next step: save/commit the already-in-progress `cstep`
widening in `src/CFG/Compiler/Located_Exec.thy`, then update its six
downstream callers (`Control_Residual.thy`, `Control_Simulation.thy`,
`Located_LTR.thy`, `Example_Compile_Baseline.thy`,
`Example_Compile_Regression.thy`, `Example_Control_Simulation_Regression.thy`)
to pass `is_global` positionally, and run the batch build to confirm the
Stage 2 boundary is clean before starting Stage 3.

## 7. Planned follow-up, after the current migration: a Goblint-shaped `analysis_env`

Section 6's Phase 1/2/3 sketch answered "when would bundling ever be
justified." This section sharpens that into an actual target shape, so it is
written down once rather than re-derived if the trigger condition is ever
met. It does not change the recommendation in section 6: no record now, the
current `gs` migration continues unmodified. This section is a plan to
consult later, not work to start.

### The real problem a record would solve is not `gs`

`gs` alone never justifies a record (section 2). The actual pressure, if it
ever materializes, is different: as the solver-soundness layer picks up more
independently-varying configuration, positional parameter lists on the
high-level entry points grow long. `cstep gs cfg conf conf'` is fine today.
A hypothetical future `cstep` that also needed a context policy, a `dg_spec`,
a transfer registry, and a widening choice, all as separate positional
arguments, would not be fine — not because five parameters are inherently
bad, but because those five values are always supplied together, by the same
caller, at the same orchestration boundary. That is the actual condition
from section 6(b')'s clustering trigger, made concrete.

Goblint's `man` solves the OCaml-side version of this problem, but not by
accident of the module system alone (contra this document's earlier framing
in section 5, which the session that commissioned this document flagged as
too dismissive): `man` genuinely bundles the analysis's static capabilities
so that every `Spec.transfer`-shaped function receives one thing instead of
independently threading each capability. The part worth carrying into HOL is
that idea, not the record's literal field list or its effectful callbacks.

### Static capabilities vs. dynamic execution state

Goblint's `man` mixes two kinds of field, and only one kind maps to a record
worth introducing here:

- **Static, known before execution starts**: which variables are global
  (`gs`), which domain and its soundness/widening obligations, which context
  policy is in effect, which transfer semantics apply. These are fixed once
  per analysis run and threaded unchanged through every step. This is the
  candidate for a record.
- **Dynamic, changes every step**: the current node, the previous node, the
  active edge, the local abstract state, the current context/activation key.
  These do not belong in the same record as the static capabilities — they
  are the arguments a step relation is defined *over*, not configuration it
  is defined *with*. Mixing the two would recreate the single bloated
  `manager` record section 2 already rejected, just with the dynamic fields
  renamed rather than removed.

A future split, sketched only (field names are illustrative, not a
commitment to specific locale signatures yet):

```isabelle
record analysis_env =
  gs       :: "vname \<Rightarrow> bool"
  dg       :: "('D, 'G) dg_spec"
  ctx_policy :: "..."      (* the seed_key/enterc shape from routed_context *)
  transfer :: "..."        (* the sound_transfer/sound_effectful_transfer shape *)
```

with dynamic execution state staying exactly where it already lives today:
positional arguments to `cstep`/`pstep` (`cfg_node`, `cconf`, `com \<times> store \<times>
frame list`), not a second record. Introducing an `analysis_state` record
for these would be the same over-bundling mistake one layer down and is not
part of this plan.

### Phased path, only if the clustering trigger from section 6(b') fires

**Phase 1 (current, this document's actual recommendation).** Finish the
`gs` migration exactly as section 6(a)/(c) describe: `cstep` widened, its
callers updated, then `sound_dg_spec`/`ltr_gamma`/`routed_context` gain `gs`
as a `fixes`. No record. This phase removes the hidden `is_global`
dependency and proves the soundness stack generic in the classifier — it is
a complete, useful end state on its own, with or without a later Phase 2.

**Phase 2 (only if triggered).** Introduce `analysis_env` holding only
`gs` at first — a record of one field is legitimate *as a named future
extension point*, unlike section 2's rejected `analysis_manager`, provided
it is introduced at the moment a second field is actually ready to join it,
not speculatively. Use it only at orchestration boundaries close to
`run_analysis env program` or a `src/Formalization/Pipeline/` entry point.
Explicitly do not thread it through `enter_state`/`combine_states`/
`combine_collect`/`call_enter` — those keep taking bare `gs`, per section
6(b')'s Phase 3, because threading the full environment into single-concern
functions is the "dumping ground" pattern under a different name.

**Phase 3 (only if Phase 2's env has proven itself and a second field is
ready).** Absorb capabilities that are *already* independent, working
abstractions — `dg_spec` (`DG_Soundness.thy`), the context-policy functions
(`routed_context`/`context_transfer`, `Routed_Context.thy`) — as `analysis_env`
fields, without duplicating the locales that currently fix them. Two ways to
keep the locale layer authoritative rather than redundant:

```isabelle
locale sound_dg_spec =
  fixes env :: analysis_env
  assumes combine_sound: "... \<Longrightarrow> combine_collect (gs env) dst s t \<in> ..."
```

or, if the locale should stay independent of the record's shape,

```isabelle
locale sound_dg_spec =
  fixes S :: "..." and gammaDG :: "..." and gs :: "vname \<Rightarrow> bool"
```

with `analysis_env`'s own fields *instantiated from* the locale's existing
parameters at the interpretation site, not the other way around. Prefer the
second form unless the first demonstrably removes real duplication — the
locale's obligations are the load-bearing artifact; the record is a
convenience for callers that already need several of them together.

**Phase 4 (the point where a record actually pays for itself).** Only once
Phase 3 has landed does migrating transfer-function interfaces from
`transfer :: node \<Rightarrow> D \<Rightarrow> D`-shaped bare parameters to
`transfer :: analysis_env \<Rightarrow> node \<Rightarrow> D \<Rightarrow> D` become worth doing: at that point
every domain instance (`Sign_Transfer.thy`, `Interval_Transfer.thy`, and
siblings) is already passing `gs` and a context policy together at each call
site, and collapsing them into one argument is a real simplification rather
than a projection tax. Before Phase 3 lands, Phase 4 has nothing to collapse
and should not be attempted.

### What this section is not

It is not authorization to start Phase 2. Section 6's recommendation stands:
finish Phase 1 (the plain `gs` migration), and revisit this section only
when a concrete locale or entry point accumulates several always-co-threaded
parameters in practice, not in anticipation.

### Negative criteria: when not to introduce `analysis_env`

Stated positively, section 7 already says "only when several components
consistently co-thread." Stated as an explicit gate, so a future reader (or
agent) skimming this document for license to act cannot mistake "Goblint has
`man`" for a reason on its own:

> Introduce `analysis_env` only when multiple independently useful
> components are consistently threaded together through the same
> high-level interfaces, evidenced by call sites that already pass them
> as a group. Do not introduce it merely to replace a single explicit
> parameter, and do not introduce it in anticipation of components that
> do not exist yet.

Concretely, none of the following justify starting Phase 2 on their own:

- "`gs` is threaded through many files" -- section 1 already established
  this; volume of call sites is not the same as clustering of *distinct*
  parameters at those sites.
- "Goblint has a `man` record" -- section 5's comparison stands: `man` is
  the right idea for capabilities that are actually static and actually
  co-threaded, not a template to copy because the reference implementation
  has one.
- "It would make future extension easier" -- CLAUDE.md's own standard
  applies here directly: don't design for hypothetical future requirements;
  a one-field `record analysis_env = gs :: "vname \<Rightarrow> bool"` is exactly the
  `analysis_manager` section 2 already rejected, wearing a different name.

The trigger is empirical, not aspirational: a Stage 3/4 diff that already
shows two or more parameters appearing together at every citing call site is
sufficient grounds to reopen this document. A clean `gs`-only migration,
however large, is not.

### Reading `is_global` hits during Stage 3: three categories, not one

Stage 3 (threading `gs` as a `fixes` through `sound_dg_spec`, `ltr_gamma`,
`routed_context`, and siblings) will re-run the same kind of grep that
produced section 1's 520-hit count. Not every hit is a Stage 3 target;
sorting them into three categories up front avoids over-scoping the change:

1. **Semantic parameter.** A call site where `is_global` is the literal
   classifier argument to `combine_collect`/`call_enter`/`enter_state`/
   `combine_states`/`cstep`/`pstep`, either directly or inside a locale's
   `assumes`. This is the Stage 3 target: replace the literal with `gs` and
   add `gs` to the enclosing locale's `fixes` (or the enclosing lemma's
   `for`), then instantiate `gs = is_global` at every current caller. Example:
   `combine_collect is_global dst s t` inside `sound_dg_spec`'s
   `combine_sound` assumption becomes `combine_collect gs dst s t` with `gs`
   added to the locale's `fixes`.
2. **Concrete executable program fact.** A call site where `is_global x` (or
   `is_global`) is evaluated against a specific, already-fixed program or
   witness, not passed onward as a classifier -- e.g. an executable example
   computing over the default prefix-based classifier and printing or
   asserting on the result. These do not take `gs`; they are testing what
   `is_global` itself does, not standing in for an arbitrary classifier, and
   converting them would change what they test.
3. **Proof-only unfold or simp helper.** `is_global_def`, or a `simp add:
   is_global_def` / `by (auto simp: is_global_def)` step used to discharge a
   goal for the concrete `is_global` case. These live inside proof bodies
   for facts about the concrete classifier and stay as-is; the migration
   makes them apply after an interpretation-time `gs = is_global` rewrite
   rather than removing them.

Only category 1 is in scope for Stage 3. A `rg -c is_global` count dropping
by less than its full 520 after Stage 3 lands is expected, not a sign the
migration is incomplete -- categories 2 and 3 are meant to stay.

## 8. Stage 3 execution finding: a deeper root, and a record question re-asked and re-closed

This section records what happened the first time Stage 3 was actually
attempted, because both the finding and its resolution are durable: the
finding changes Stage 3's file list, and the resolution is a second,
independent test of section 7's negative criteria under real pressure rather
than in the abstract.

### 8.1 The finding: `sound_dg_spec` cannot be widened in place

Attempting Stage 3 as originally scoped -- add `gs` to `sound_dg_spec`'s
`fixes` and restate `combine_sound`/`enter_sound` generically -- fails at the
proof, not the statement. `combine_collect_sound` and `combine_states_sound`
(`src/Analysis/Generic/Equations/Constraint_System.thy:325,554`) are cited by
`sound_dg_spec`'s assumptions, and their proofs work by unfolding
`combine_abs`:

```isabelle
definition combine_abs :: "'a abs_state \<Rightarrow> 'a abs_state \<Rightarrow> 'a abs_state" ("\<langle>_|_\<rangle>") where
  "combine_abs sc se = (\<lambda>x. if is_global x then se x else sc x)"
```

`combine_abs` is the abstract-domain-side counterpart of the already-generic
`combine_states` -- and unlike `combine_states`, it still hardcodes
`is_global` directly, not as a passed-in classifier. The same is true of
`enter_frame_D` (line 433), `cinit_stores` (line 749), and the
`inl_slot_globals_bot`/`inl_glob_le_glob_env` invariant family (lines
1154-1183). A lemma like `combine_collect_sound` splits the concrete side by
whatever `gs` it is given, but the abstract side it is proved against always
splits by `is_global` -- so the lemma is only true when `gs = is_global`.
Adding `gs` to `sound_dg_spec`'s `fixes` without first fixing this would be
cosmetic: every interpretation would still secretly require `gs = is_global`,
undetectably, since nothing in the locale's type would say so.

The fix is mechanical once identified, not a redesign: `combine_states` and
`enter_state` (`src/VIMP/VIMP_Globals.thy`) already take `gs` explicitly
(Stage 0). `combine_abs`/`enter_frame_D`/`cinit_stores` are the one layer
that was never updated to match. Widening them so both the concrete and
abstract sides split on the *same* `gs` makes `combine_states_sound`'s
existing proof go through unchanged -- `auto` after unfolding both
definitions does not care which predicate `gs` denotes, only that both sides
agree, which they now do by construction. This reclassifies Stage 3 into two
parts:

- **Stage 3a**: widen `combine_abs`, `enter_frame_D`, `cinit_stores`, and the
  `inl_*` invariant predicates in `Constraint_System.thy` to take `gs`. This
  is the actual root; without it, Stage 3b cannot be proved, only stated.
- **Stage 3b**: widen `sound_dg_spec`, `ltr_gamma`, `routed_context`, and
  their siblings, as originally planned -- now provable, because their
  proof obligations bottom out in Stage 3a's generic facts instead of a
  hardcoded `is_global`.

Stage 3a touches `Constraint_System.thy`'s core soundness definitions, which
sit adjacent to `Exec_St` -- the representation problem fenced off earlier in
this migration ("do not touch `Exec_St` yet"). Stage 3a does not touch
`Exec_St.thy` itself or change `Constraint_System`'s architecture; it widens
one classifier parameter through definitions that already existed, the same
arity-only move as every earlier stage. That distinction is what keeps it in
scope despite the adjacency.

### 8.2 The record question, re-asked and re-closed

Finding that `gs` recurs across more functions than expected
(`combine_abs`, `enter_frame_D`, `cinit_stores`, on top of `sound_dg_spec`,
`ltr_gamma`, `routed_context`, `cstep`, `combine_collect`, `call_enter`)
prompted the question again: does this volume mean `gs` has become a "shared
analysis capability" in the Goblint `man` sense, justifying an
`analysis_config`/`analysis_env` record now, introduced small (`gs` alone)
as "a stable extension point" for capabilities that might join it later?

The answer is still no, and the reason is the same reason section 7's
negative criteria already gave: volume is not clustering. Every one of
`combine_abs`, `enter_frame_D`, `cinit_stores`, `sound_dg_spec`, `ltr_gamma`,
and `routed_context` needs exactly one thing from this family --
`gs` -- and nothing else. None of their call sites pass `gs` together with a
second, independently-varying parameter that always travels alongside it;
`enter_frame_D`'s other parameter, `top_val`, is a domain-specific top
element (different for Sign vs. Interval) with no relationship to `gs` at
all, and bundling the two would associate unrelated concerns for no reason.
Finding the *same* single parameter needed in more places is what every
earlier stage of this migration looked like (Stage 0: `combine_states`/
`enter_state`; Stage 1: `combine_collect`/`call_enter`; Stage 2: `cstep`);
none of those prior recurrences were treated as a clustering signal, and this
one is not qualitatively different -- it is the same layer of the same
migration, one level deeper than expected, not a new kind of evidence.

A record introduced now, holding only `gs`, with other fields "added when
they start clustering," is precisely the shape section 2 named and section
7's negative criteria ruled out by name: "do not introduce it merely to
replace a single explicit parameter, and do not introduce it in anticipation
of components that do not exist yet." Depth of recurrence does not change
that test. The trigger stays what section 7 already said it was: a call site
that already needs two or more distinct, independently-sourced parameters
together, evidenced in the diff, not anticipated in the design. Stage 3a/3b
do not produce such a call site -- they produce more places that each need
one classifier. The recommendation from sections 6 and 7 stands unchanged:
bare `gs`, no record, reassessed here under real pressure and confirmed
rather than merely repeated.

## 9. Stage 3a/3b landed: what actually became generic, and a new boundary found

Both stages committed (`refactor(analysis): thread an explicit classifier
through the abstract split layer`; `refactor(analysis): thread an explicit
classifier through sound_dg_spec`), batch build green. This section records
the final shape, since Stage 3b did not land exactly as section 8 planned --
a second boundary surfaced during execution, on the same pattern as section
8's own finding, and is worth keeping on the record for the same reason.

### What is now generic

- `combine_abs`, `combine_collect_abs`, `enter_frame_D`, `enter_D`,
  `cinit_stores`, `inl_slot_globals_bot`, `inr_slot_locals_bot`,
  `inl_glob_le_glob_env` (`Constraint_System.thy`) -- Stage 3a's root
  operators, all take `gs` and their proofs carry through unchanged for
  arbitrary `gs`, exactly as predicted.
- `sound_dg_spec` (`DG_Soundness.thy`) -- `combine_sound`/`enter_sound` and
  every derived fact (`combine_sound_fs`, `enter_sound_fs`,
  `dg_postfix_gamma_call`, `dg_postfix_gamma_combine`) are generic in `gs`.
  Every current interpretation (`sound_dg_spec_indep`, `sound_dg_spec_unit`,
  and every domain's `X_dg_api`) still instantiates `gs = is_global`, per
  the established pattern.
- `dg_ctx_activation` (`DG_Ctx_Activation.thy`) -- passes `gs` straight
  through to `sound_dg_spec`; no obligation of its own references `is_global`,
  so this was a pure arity fix.

### What stays pinned, and why -- a second load-bearing boundary

`ltr_gamma` (`LTR_Abstract.thy`) and `routed_context` (`Routed_Context.thy`)
do **not** become generic, and the reason is structurally the same one
section 8 found for `combine_abs`: a lemma's own proof can force a classifier
to a concrete value even when its *statement* looks like it could be generic.

The attempt: widening `ltr_gamma`'s `CALL`/`COMB` obligations to take `gs`
looked identical in shape to `sound_dg_spec`'s widening -- the same
substitution, `call_enter is_global` to `call_enter gs`. The batch build
caught what a signature-only review would not: `ltr_gamma`'s own internal
lemmas -- `call_closed`, `return_closed`, and everything reachable from them
(`valid_ltr_subset_gamma_ltr`, ultimately `activation_collect_sound` and
`valid_ltr_ctx_sound` in `Activation_Backbone.thy`/`Activation_Local_Sound.thy`)
-- exist specifically to connect the abstract `acc` to `valid_ltr`'s
*concrete* trace semantics (`Call`, `Resume`, the `call`/`ret` constructors in
`CFG_Local_Trace.thy`). `valid_ltr` itself was never widened in this
migration -- deliberately: it sits at the CFG/Collecting layer, one level
below everything Stage 1-3 touched, and its `call`/`ret` rules still
construct their result via literal `call_enter is_global (...)` /
`combine_collect is_global (...)`. Once `ltr_gamma`'s `CALL`/`COMB` read `gs`
instead of `is_global`, `call_closed`'s citation of `CALL` no longer unifies
with its own `shows` clause (which still, necessarily, states a fact about
`valid_ltr`'s literal `is_global`-built `Call` term) -- `gs`, being a
genuinely fixed locale parameter inside `ltr_gamma`'s own `begin...end`
block, cannot be specialized to `is_global` from *inside* that block. The
batch log surfaced this as a flat `Failed to apply initial proof method`,
with no hint that the root cause was a locale-genericity/pinned-dependency
mismatch one layer down -- only re-deriving the dependency chain (`call_closed`
depends on `CALL`, `CALL`'s shape depends on what `valid_ltr`'s `call` rule
literally constructs) explained it.

`routed_context` inherits the identical constraint one hop further out:
its `call_enter_store_agree` obligation is stated directly against
`call_enter_store` (`CFG_Local_Trace.thy`), whose own definition still
reads `call_enter is_global (...)`. Any generic-`gs` version of that
obligation would need `call_enter_store` to also take `gs` -- again, out of
scope, since that is `valid_ltr`'s own file.

The fix that shipped: revert `ltr_gamma` to pinned, and introduce
`sound_dg_spec_ltr` (`DG_LTR_Sound.thy`) -- a locale extending
`sound_dg_spec S gammaDG is_global` with **no new obligations of its own**,
existing solely to give the one bridge theorem that needs both worlds
(`dg_postfix_collect_sound_ltr`, which feeds `sound_dg_spec`'s now-generic
facts into `ltr_collect_semantic_postfix`'s still-pinned premises) a view of
`sound_dg_spec`'s facts already specialized to `is_global`, without touching
`sound_dg_spec`'s own genericity or `ltr_gamma`'s pinned shape. Every
existing `sound_dg_spec ... is_global` sublocale (`sign_dg_api`, `ivl_dg_api`,
`mixed_si_api`) retargets to `sound_dg_spec_ltr` with the same `rewrites`
clauses, so no caller-visible name changed.

### The general lesson, stated once

A locale's *signature* looking genericizable is not sufficient evidence that
it should be. The load-bearing question is always: does anything *inside*
this locale's own proof obligations reach into a sibling definition that is
still concrete? `combine_abs` (section 8) and `ltr_gamma` (this section)
both failed this check on the first attempt, and both failures were
invisible from the signature alone -- only tracing what the locale's own
lemmas actually unfold into (`restrict_local`/`restrict_global` for
`combine_abs`; `valid_ltr`'s `Call`/`Resume` constructors for `ltr_gamma`)
surfaced it. Before widening the next locale in this family, check what its
own internal lemmas cite, not just what its own `assumes` block says.

### What remains, if this migration continues further

`valid_ltr`, `call_enter_store`, and the `Call`/`Resume`/`Root`/`Resume`
inductive-set constructors (`CFG_Local_Trace.thy`) are the one remaining
hardcoded layer in the classifier chain: VIMP semantics (Stage 0), CFG
compiler semantics (Stage 1-2), and the D/G abstract soundness layer
(Stage 3a-3b) are now all generic in `gs`; the activation-local trace
semantics that sits between the CFG layer and the D/G layer is not. Widening
it would let `ltr_gamma`/`routed_context` become genuinely generic too,
closing the boundary this section found. That is a distinct, CFG/Collecting-
layer migration -- comparable in shape to Stage 2 (`cstep`) -- not started
here, and not implied by anything in this document to be either urgent or
in scope for the current work.

## 10. Stage 4 landed: the last hardcoded layer closed

Committed as `refactor(cfg): thread an explicit classifier through valid_ltr
and its cascade`, batch build green across all five sessions. This closes
exactly the boundary section 9 named as remaining.

### What is now generic

- `valid_ltr`, `call_enter_store`, `ltr_F`, `ltr_collect`, `collect_result`,
  `activation_collect` (`CFG_Local_Trace.thy`, `LTR_Collect.thy`) -- the
  inductive trace relation and its projections all take `gs` in place of the
  literal `is_global` inside the `Call`/`Resume`/`Root` constructors and the
  `key`/`sink` projections. Every existing call site now supplies `is_global`
  explicitly at the point where the surrounding context is still pinned
  (`cstep`, `pstep`, or a fixed example CFG), rather than the constant being
  baked into the definition.
- `ltr_gamma` (`LTR_Abstract.thy`) and `routed_context` (`Routed_Context.thy`)
  -- section 9's pinned boundary is gone now that `valid_ltr`/
  `call_enter_store` are generic: `call_closed`/`return_closed` unify against
  a `gs`-generic `Call`/`Resume` term, so the locales' own `CALL`/`COMB`
  obligations no longer need to match a literal `is_global`-built term.
  `valid_ltr_ctx_sound`/`activation_collect_sound`
  (`Activation_Local_Sound.thy`/`Activation_Backbone.thy`) widened to match.
- `ltr_repr`/`located_ltr` (`Located_LTR.thy`) gained `gs` in their own
  definitional signature for the same "extra variables on rhs" reason as
  every other root definition in this migration, but every usage site in
  that file stays pinned to `is_global`: the whole file is the bridge from
  `cstep` execution to trace semantics, and `cstep` itself is still
  hardcoded (Stage 2's unchanged decision). A generic `ltr_repr gs` would be
  well-typed but vacuous here -- nothing in the file has a `gs` to hand it
  other than `is_global`.

### What stays pinned, and why -- unchanged from Stage 2

`cstep`/`pstep` (`Control_Simulation.thy`/`VIMP_Proc.thy`) already take a
generic `(vname => bool)` parameter in their own signature (Stage 2), but
every call site still supplies the literal `is_global`, per Stage 2's
decision, which this migration never revisited. Every file whose obligations
are stated in terms of a `cstep`/`pstep` run -- `Located_LTR.thy`,
`Source_Activation_Sound.thy`, and the
`sound_transfer`/`sound_effectful_transfer` contexts in
`LTR_Analysis_Sound.thy`/`LTR_TD_Side_Eff_Sound.thy`/
`LTR_TD_Side_Eff_Exit.thy` -- therefore still supplies `is_global` as a
literal at its `ltr_collect`/`valid_ltr`/`call_enter_store`/
`activation_collect` call sites, exactly the same two-tier discipline used
throughout Stages 3a-4: generic at the root definition, literal at any
consumer still tied to a pinned sibling.

### Where the classifier chain stands now

Every definition named in this document's section 1 classification now takes
`gs` in its own signature; `cstep`/`pstep` already did (Stage 2). What
remains concrete is call-site instantiation, not definitional shape:
`Located_LTR.thy`'s bridge theorems and every `sound_transfer`/
`sound_effectful_transfer` context still supply the literal `is_global`.
Switching to declaration-driven classification (`declared_global P`) is now
an instantiation change at those call sites, not a semantic rewrite of any
layer in between -- the goal stated at the top of this document.
