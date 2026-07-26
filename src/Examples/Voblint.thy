(* SPDX-License-Identifier: MIT *)

section \<open>Voblint: a verified abstract interpreter for IMP2\<close>

theory Voblint
  imports
    "Voblint_IMP2.IMP2_Syntax"
    "Voblint_IMP2.IMP2_Expr"
    "Voblint_IMP2.IMP2_Globals"
    "Voblint_IMP2.IMP2_Proc"
    "Voblint_IMP2.IMP2_Notation"
    "Voblint_CFG.CFG_Def"
    "Voblint_CFG.IMP2_Proc_to_CFG"
    "Voblint_CFG.CFG_Local_Trace"
    "Voblint_CFG.CFG_Prune"
    "Voblint_Analysis.Abstract_Domain"
    "Voblint_Analysis.Constraint_System"
    "Voblint_Analysis.Constraint_System_Sound"
    "Voblint_Analysis.TD_Side_CFG"
    "Voblint_Analysis.TD_Side_Eff_Cone_Lemmas"
    "Voblint_Analysis.Sign_Domain"
    "Voblint_Analysis.Sign_Side_Soundness"
    "Voblint_Analysis.Interval_Domain"
    "Voblint_Analysis.Interval_Side_Soundness"
    "Voblint_Analysis.DG_Framework"
    "Voblint_Analysis.DG_Soundness"
    "Voblint_Analysis.Sign_DG"
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.Mixed_Sign_Interval"
    "Voblint_Analysis.Activation_Backbone"
    "Voblint_Analysis.DG_Ctx_Activation"
    "Voblint_Analysis.Exec_St"
    "Voblint_Analysis.Exec_Bridge"
    "Voblint_Analysis.Exec_DG_Bridge"
    "Voblint_Analysis.Sign_Exec"
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Analysis.Sign_Named_Global_Eff"
    Exec_Sign_Run
    Exec_Sign_DG_Run
    Example_Interval_DG_Flagship
    "Voblint_Formalization.Mixed_Flow_Sound"
    "Voblint_Formalization.Source_Activation_Sound"
    Example_Interval_DG_Ctx_Collect
    Example_Interval_Source_Ctx
    Example_Inc_Proc
    Example_Side_Execute
    Example_Side_Branch_Calls
    Example_Side_Proc_Global
    Example_Interval_Side_Proc_Global
    Example_Mixed_Flow_Sign
    Example_Proc_Call
    Example_Interval_Loop_Coverage
    Example_Guard_Refinement
    Example_Proc_GraphViz
begin

text \<open>
  \<^verbatim>\<open>
____   ____   ___.   .__  .__        __
\   \ /   /___\_ |__ |  | |__| _____/  |_
 \   Y   /  _ \| __ \|  | |  |/    \   __\
  \     (  <_> ) \_\ \  |_|  |   |  \  |
   \___/ \____/|___  /____/__|___|  /__|
                   \/             \/
  \<close>
\<close>

section \<open>Certified pipeline\<close>

text \<open>
  Voblint connects an accepted IMP2 program to the result computed by a verified
  interprocedural analyzer:

  \<^verbatim>\<open>
    source execution
      -> procedure-aware CFG execution
      -> activation-local trace
      -> collecting semantics
      -> D/G equation system
      -> verified side-effecting solver
      -> abstract post-solution
      -> source-level soundness
  \<close>

  Each arrow is justified independently.  Compiler simulation preserves source
  behavior.  Forgetful trace projections introduce no abstract states.  Transfer,
  join, routing, and widening occur only on the abstract side and are justified by
  containment in the corresponding concretization.
\<close>

subsection \<open>Activation-local concrete semantics\<close>

text \<open>
  \<^const>\<open>valid_ltr\<close> represents one procedure activation and its ancestry.
  \<^const>\<open>Root\<close> starts main, \<^const>\<open>Call\<close> records an immediate caller, and
  \<^const>\<open>Resume\<close> continues that caller after its callee reaches the matching
  result node.  Structural caller links distinguish nested and recursive activations
  without placing an unbounded stack in CFG nodes.

  \<^const>\<open>ltr_collect\<close> forgets the activation structure and collects stores by
  node.  \<^const>\<open>ltr_collect_keyed\<close> groups them by an abstract key, while
  \<^const>\<open>activation_collect\<close> uses the structural activation context.  All three
  contain only stores from valid local traces.
\<close>

subsection \<open>Procedure-aware source and CFG\<close>

text \<open>
  Procedures receive fresh local state and inherited globals.  A call frame stores
  the caller state and optional destination.  Explicit return enters unwinding,
  which skips the remaining commands in that activation and resumes the immediate
  caller.  Main has no caller and accepted programs therefore require it to terminate
  by ordinary fall-through.

  CFGs use explicit \<^const>\<open>FunctionEntry\<close> and \<^const>\<open>FunctionResult\<close> nodes.
  The \<^const>\<open>intra\<close> relation carries local transfers and matching returns.  The
  \<^const>\<open>calls\<close> relation carries call-site, callee-entry, and continuation data.
  Compiler certificates expose the node ownership and range separation needed by
  the source/CFG simulation.
\<close>

subsection \<open>Equations, D/G routing, and solver\<close>

text \<open>
  Every node equation joins ordinary predecessor flow, callee-entry flow, and
  caller/callee combination.  Executable equations and their soundness proof use
  the same contribution families.

  The D/G interface separates local flow-sensitive facts from information published
  through global side effects.  Analyses choose the two carriers, routing operations,
  and context keys.  Sign, Interval, and mixed Sign/Interval instances share the
  verified side-effecting top-down solver and the collecting-soundness infrastructure.
\<close>

subsection \<open>Executable witnesses\<close>

text \<open>
  The interval and Sign flagships compile source programs, generate their D/G
  equations, execute the verified solver, and certify the computed post-solutions.
  The \<open>twice\<close> program calls one procedure from two sites; its activation-sensitive
  interval analysis keeps the two call contexts separate.  Recursive examples test
  structural activation nesting independently of that repeated-call witness.

  GraphViz exporters present procedure entries, results, calls, resumes, and computed
  abstract states without changing the certified equation system.
\<close>

text \<open>
  \<^bold>\<open>The D/G execution pipeline (headline).\<close> The flagship threads a single chain,
  every step machine-checked, from source to a soundness theorem over the
  \<^emph>\<open>computed\<close> analysis result:

    \<^item> IMP2 source \<^verbatim>\<open>compile_prog\<close> to a CFG;
    \<^item> the generic D/G generator \<^verbatim>\<open>dg_gen_of\<close> emits the equation system;
    \<^item> the verified solver \<^emph>\<open>computes\<close> a solution (\<^verbatim>\<open>solve_c ... = Some sigma\<close>, \<^verbatim>\<open>by eval\<close>);
    \<^item> the solver's own correctness theorem certifies \<^verbatim>\<open>part_post_solution sigma\<close> --- no re-checking;
    \<^item> the native endpoint \<open>ivl_dg_post_solution_collect_sound\<close> bounds
      \<open>ltr_collect g S v\<close> at every program point.

  \<^bold>\<open>Soundness spine.\<close> The context-sensitive analyses share one native
  interface, the carrier-opaque \<^verbatim>\<open>sound_dg_spec\<close>; Sign, Interval, and
  the mixed flagship are its instances, and context slicing is factored through
  the functional activation spine and its per-context keyed slots. The base
  flow-sensitive spine is the query-cone endpoint
  \<^verbatim>\<open>side_collect_sound_in_eff_cone\<close>, instantiated for Sign and Interval over
  \<^const>\<open>ltr_collect\<close> on the original CFG. Its exit corollary
  \<^verbatim>\<open>side_collect_sound_exit_eff_ltr_cone\<close> uses \<open>q = cfg_exit g\<close>. The cone
  restriction lives in the abstract concretization guard, not in a graph
  transformation.
\<close>

end
