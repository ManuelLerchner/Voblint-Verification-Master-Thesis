# Voblint formalization (`src/`)

A machine-checked abstract interpreter for VIMP, sound from the source operational
semantics to the *computed* analysis result:

```text
VIMP source -> CFG -> activation trace -> collecting semantics
            -> D/G equation system -> verified TD side solver
            -> abstract post-solution -> source-level soundness
```

Each arrow is a theorem. The vendored solver is `vendor/td-verification` (session `TD`).
`src/Examples/Capstone/` (session `Voblint_Examples`) is the capstone: it shows the
published theorem is non-vacuous and that the framework's guarantees fail without
its premises.

There is one language. The parser builds surface VIMP (`src_exp`, `src_com`,
`imp_prog`); `elaborate`, `elab_com` and `elab_ptable` turn it into core VIMP
(`exp`, `com`) over variable identities `var_id` and machine-integer kinds
`ikind`, and `pstep` executes core VIMP. A surface program means the core semantics
of its elaboration: elaboration is a definition, not a proved transformation.

## Sessions

One directory is one session — Isabelle rejects two sessions sharing a directory, so
the folder tree and the session graph are the same thing. `ROOTS` lists them all.

| Folder | Session | Role |
| --- | --- | --- |
| [`Program_Model/VIMP/`](Program_Model/VIMP/) | `Voblint_VIMP` | the whole language: machine kinds, surface syntax, elaboration to core VIMP, evaluation `eval`, conversion `kind_conv`, the generic step rules and the canonical `pstep` |
| [`Abstract_Interpreter/Domain/`](Abstract_Interpreter/Domain/) | `Voblint_Domain` | what an abstract value and an abstract state are: sound-domain classes, concretization, the dead-code lift, pointwise states, the integer value lattices |
| [`Abstract_Interpreter/Solver/`](Abstract_Interpreter/Solver/) | `Voblint_Solver` | the strategy-tree equation language of the vendored solver, its monotonicity and post-solution vocabulary. Never sees a CFG. |
| [`Program_Model/CFG/`](Program_Model/CFG/) | `Voblint_CFG` | the graph model, its generic semantics and the canonical instances `cstep`, `valid_activation_trace`, `activation_collect`, `node_collect` — what a soundness claim is stated *about*. Never mentions the compiler. |
| [`Program_Model/Compile/`](Program_Model/Compile/) | `Voblint_Compile` | the compiler (`elab_cfg`), its structural invariants, forward simulation, and the bridge from a source run to a valid activation trace |
| [`Abstract_Interpreter/Framework/`](Abstract_Interpreter/Framework/) | `Voblint_Framework` | the D/G analysis framework: transfer contract, equation generator, cooperation of analyses, collecting soundness for an arbitrary CFG. No domain, no compiler. |
| [`Abstract_Interpreter/Exec/`](Abstract_Interpreter/Exec/) | `Voblint_Exec` | the executable carrier, and transport from the solver's association lists to the function-valued states soundness is stated over |
| [`Analyses/`](Analyses/) | `Voblint_Routing`, `Voblint_Result`, `Voblint_Nonrelational`, `Voblint_Analysis_*` | shared pipeline, the kind-aware non-relational analysis, one session per domain — see below |
| [`Executable_Surface/CLI/`](Executable_Surface/CLI/) | `Voblint_CLI` | the combined state of the analyses, `run_voblint` and its public theorems. Where the domains meet again. |
| [`Examples/`](Examples/) | `Voblint_Examples_CFG`, `Voblint_Examples_CLI`, `Voblint_Examples` | compiler and elaboration regressions, witnesses through `run_voblint`, and the capstone |
| [`Executable_Surface/Codegen/`](Executable_Surface/Codegen/) | `Voblint_Codegen` | the `export_code` boundary into OCaml |

Dependency shape:

```text
VIMP -+-> CFG ----+-> Compile ---------+
      |           |                    v
      |           +-> Framework ---> Exec -> Routing -> Result -> Nonrelational -> Analysis_* -+
      +-> Domain -------^                                                                      |
TD   ---> Solver -------^                                                                      v
                                                                                  CLI -> Codegen
                                                                                   +--> Examples_CLI -> Examples
```

(`CFG` and `Domain` depend on `VIMP`; `Framework` on `CFG`, `Domain` and `Solver`;
`Compile` on `CFG`; `Exec` on `Framework` and `Compile`; `Voblint_Examples_CFG` on
`Compile`.)

The source-level endpoints sit *below* the analysis family, not after it:
`Voblint_Result` holds the domain-free source bridge (`Source_Activation_Sound`)
and the routed endpoints (`gfun_route_result_node_sound`,
`gentry_state_activation_collect_sound_of_terminates` in `DG_Live_Unknowns`) every
pipeline instance reads, so each inherits them from an ancestor heap rather than
re-deriving them.

## The analysis and example families

[`Analyses/Shared/`](Analyses/Shared/) holds what every analysis reuses, as two
sessions chained `Routing -> Result` on top of `Voblint_Exec`: the context policies
and the publication surface with the source-level endpoints.
[`Analyses/Nonrelational/`](Analyses/Nonrelational/) (`Voblint_Nonrelational`) is the
kind-aware non-relational pipeline: abstract states `var_id ⇒ 'a kd` over any
kind-aware integer domain, the transfer (`nonrel_spec`), its executable carrier
(`nonrel_exec_spec`) and the instances `nonrel` and `nonrel_es` of `gdg_analysis`.
It is the parent of [`Sign/`](Analyses/Sign/), [`Interval/`](Analyses/Interval/),
[`Parity/`](Analyses/Parity/), [`Congruence/`](Analyses/Congruence/),
[`Int/`](Analyses/Int/) and [`Analyses/Order/`](Analyses/Order/)
(`Voblint_Analysis_Order`, the relational order domain over variable identities).

Each domain session holds the value-level mathematics (lattice, arithmetic, backward
filtering) and a `<Domain>_Kind` theory that makes it a kind-aware integer domain, so
the non-relational pipeline runs it. Int is the reduced product of Interval and
Congruence at machine kinds (`int_tuple`, `Int_Tuple_Kind`), after Goblint's
`IntDomTuple`.

[`Examples/`](Examples/) holds the domain-independent compiler witnesses, the
witnesses that reach `run_voblint`, and the capstone.

## Where to start

Read a session's own `README.md` first. `src/Executable_Surface/CLI/Run_Voblint.thy`
states the public theorems.

Proof status: `docs/PROOF_OVERVIEW.md`, `docs/PROOF_PHASES.md`.
