# Examples / Sign

Sign-domain witnesses. Each `Example_*` defines its program locally; the
canonical spines additionally prove an end-to-end soundness theorem tying a
concrete run to the abstract result.

| File | Role | What |
| --- | --- | --- |
| `Example_Sign_Domain_Ops.thy` | worked example | the sign lattice and its arithmetic on concrete inputs -- abstraction of an integer, the four operations, the join, printing, expression evaluation, one assignment -- each a `by eval` equation rather than a `value` |
| `Exec_Sign_DG_Run.thy` | required support | end-to-end certified run on the Base-style D/G equation system, registered through `local_state_dg_exec_analysis` as `sign_ex_reg` |
| `Example_Sign_Unit_Assembly.thy` | witness | Sign's instance of the shared unit-context assembly, executed: a callee writes a global, the caller checks its sign, and the assembled report decides the check -- a code-generation defect in the assembly fails here |
| `Example_Sign_DG_Custom_Body.thy` | canonical spine | an analysis-supplied procedure-entry transfer (`dgs_body`) that forgets the callee's formals, carried through the same D/G generator and solver as the stock one; the two solved systems disagree only inside the callee |
| `Example_Sign_DG_Custom_Combine.thy` | canonical spine | an analysis-supplied call-return environment merge that is *not* the stock one, carried through the same D/G generator and solver |
| `Example_Sign_DG_Overlapping_Enter.thy` | canonical spine + witness | one concrete call represented under two contexts at once: `dgs_enter` answers two overlapping (continuation, callee entry) alternatives, and both the solved table and the relational admitted-context relation keep them apart |
| `Example_Sign_Backward_Pollution_Regression.thy` | regression | backward filtering of `Or (And (x=0) (x=1)) (And (y=0) (y=1))`: the raw filter loses `x` and `y` to join-arm pollution, the lifted one canonicalizes each arm to `Bot` first and finds the contradiction, and the executable mirror does too |
| `Example_Sign_Report_Regression.thy` | regression | four whole VIMP programs run end to end through `analyse_sign_report`, each with a `by eval` assertion pinning the verdicts: flow-sensitive globals, a dead branch arm, recursion, and one procedure called from two sites |

`Exec_Sign_DG_Run.thy`'s `gEx`, `dgEx_eqs` and `dgEx_sol` are the
`gs = sign_ex_gs`, `p = sign_ex_prog` instance of the arbitrary-classifier,
arbitrary-program chain `Sign_Entry` publishes, not a separate parallel
definition.

The three `DG_` theories vary one field of the same `dg_spec` each --- `dgs_body`,
`dgs_combine_env`, `dgs_enter` --- against the stock executable Sign
specification, on a program small enough that the field is the only thing that
can explain a difference. `Example_Sign_DG_Custom_Body`'s `bf_program` and
`Example_Sign_DG_Custom_Combine`'s `cj_program` are the same program under two
names, as are `Example_Sign_Unit_Assembly`'s `sign_assembly_demo_prog` and
`Example_Sign_Report_Regression`'s `sign_flow_sensitive_global_prog`; each
theory keeps its own copy so no witness inherits another's imports.

## Vocabulary

| word | meaning |
| --- | --- |
| **storage classifier** | the `gs :: vname => bool` saying which names are global. Every definition here is parametric in one; `sign_ex_gs`, `bf_prog_gs` and `ov_gs` are each *this* program's own classifier, not a fixed choice. |
| **ownership split** | the carrier that keeps a local half and a global half of the abstract state apart, joined back only where the transfer contract says so. `ownership_split_dg_spec_st_for` is the stock executable specification built over it. |
| **routed unit context** | context-insensitivity spelled as the degenerate routing policy: unknowns are keyed by `(node, ())`, so `unit_routed_eqs` is the same routed generator the call-string instances use, at the one-element context type. |
| **custom body / custom combine** | one field of the stock `dg_spec` replaced and nothing else: `dgs_body` (what runs on the `EA_Body` edge leaving a procedure entry) and `dgs_combine_env` (how the caller's and callee's environments merge on return). Each theory's point is that the field is genuinely free and genuinely reached. |
| **overlapping enter** | `dgs_enter` answering a *list* of (continuation, callee entry) alternatives whose entries and continuations both cover the same concrete call, so the route materializes two contexts for one call site. |
| **statement index** | `Statement n` numbering: source order, callee procedures before `main`, one index per command plus one epilogue index per procedure. |

## `CallString/` — context routed by call site

| File | Role | What |
| --- | --- | --- |
| `Example_Sign_DG_CallString_K1.thy` | canonical spine | the `nest` program at `k = 1`, solved by the plain-join solver: Sign is finite, so the computed solution is exact and `g`'s two activations collapse to `STop` |
| `Example_Sign_DG_CallString_K2.thy` | canonical spine | the same at `k = 2`, keeping them apart at `SPos` and `SNeg`. Exactness makes a genuine strict-precision comparison possible here (`sign_k2_strictly_more_precise_than_k1_at_g`) that the Interval pair cannot state |

Sign's two entry-point witnesses -- the smallest certified IP run and the
store-only check trio -- live in `CLI/`, grouped with the other domains' members
of the same trio rather than by what they import.

Role vocabulary: repository `README.md`.
