theory Voblint_Codegen
  imports
    "Voblint_CLI.Trace_Run"
begin

section "Code export surface"

text \<open>
  This session owns executable exports; the examples session proves and demonstrates the
  exported definitions without materializing generated code.

  One export block, deliberately. The external OCaml regression driver under
  \<open>codegen/regression/ocaml/\<close> needs a handful of CFG-inspection constants the CLI
  never calls; a second, narrower block would not make any surface narrower, because
  Isabelle emits the reachable transitive closure of whatever is named. Those constants
  are named here instead, so there is one generated artifact for one analysis.

  This is still not the project's public API boundary, but it is not nothing either.
  Three things are decided separately here:

    \<^item> the roots decide what the emitted OCaml \<^emph>\<open>signature\<close> exposes, and how much of it
      is transparent rather than abstract;
    \<^item> their transitive closure decides what the \<^emph>\<open>implementation\<close> contains, which no
      shortening of the root list reduces;
    \<^item> \<open>module_name\<close> decides the \<^emph>\<open>packaging\<close>.

  So trimming a root narrows what a client can name and match on, while leaving the
  emitted code the same size. A supported external surface --- one that could rename a
  constructor, or hide a representation behind an eliminator --- belongs in the
  handwritten OCaml facade \<^verbatim>\<open>cli/voblint.ml\<close> rather than in the shape of this
  list.
\<close>

text \<open>
  The roots below are the \<^emph>\<open>intended callable surface\<close>: what handwritten OCaml under
  \<open>cli/\<close>, \<open>codegen/regression/ocaml/\<close> and \<open>tests/property/\<close> actually calls. Everything else
  in the emitted module is serializer-reachable implementation detail, still present and
  still callable --- the signature narrows with the root list, the code does not. So the
  intent recorded here is not enforced. Handwritten OCaml names the export through the
  facade \<^verbatim>\<open>cli/voblint.ml\<close> (module \<open>Voblint\<close>), which re-exports this module's
  signature unchanged: the root list still decides what the facade can expose, and the
  facade is the one place a later, narrower surface would be stated.

  Analysis entry goes through \<^const>\<open>run_voblint\<close> alone, which checks the
  activation list and well-formedness and runs the requested analyses, update rule and
  context policy. Every combination is answered, so the CLI never decides legality.

  The last group of roots is there for signature visibility rather than for dispatch.
  A constant the serializer does not consider public is emitted but left out of the
  module signature, and a datatype it does not consider public stays abstract, which
  makes it unmatchable. So anything handwritten OCaml names --- even only to take it
  apart --- has to be a root: \<open>Bot\<close>/\<open>Lifted\<close>, which the CLI matches to tell a
  dead point from a live verdict, and \<open>prog_table\<close>/\<open>prog_main\<close>/\<open>prog_procs\<close>, which
  the OCaml program printer reads on a round trip.

  Nothing calls these on the CLI's analysis path, so a reading of the list as "the
  callable surface" alone would drop them, and the resulting break shows up not here but
  in an OCaml consumer, as an unbound value or a match on an abstract type.
\<close>

text \<open>
  \<open>module_name Generated\<close> puts the whole reachable program into one OCaml module rather
  than one module per contributing Isabelle theory. The alternative --- letting the
  serializer split by theory --- does not survive contact with this program: OCaml's
  single-file output emits modules in dependency order and cannot express a cycle, and
  the theories here are mutually dependent at code level (the executable state is
  instantiated at the solver's own widening/narrowing classes, and the CFG-specific
  solver instantiation needs \<open>cfg_node\<close> back). Even a split that Isabelle accepts can
  fail later in \<^verbatim>\<open>ocamlfind ocamlopt\<close>, on a type-class dictionary field that
  module-signature inference does not expose across a boundary the unsplit default never
  had.

  So the generated internals are monolithic, and this says so directly instead of
  arriving there by remapping every contributing theory onto one name by hand. Modularity,
  if wanted, belongs in the handwritten facade over \<open>Generated\<close>,
  \<^verbatim>\<open>cli/voblint.ml\<close>, which today includes it whole.

  Two further modules are emitted regardless: \<open>Bit_Shifts\<close> and \<open>Str_Literal\<close> are HOL's
  own runtime support, injected as literal target code rather than generated from
  constants here.
\<close>

text \<open>
  The list below is grouped by what each name is \<^emph>\<open>for\<close>, because the groups answer
  different questions and only one of them is an operation.

  \<^item> \<^bold>\<open>Run.\<close> \<^const>\<open>run_voblint\<close>, alone. Everything a caller can ask the analyser
    to do goes through it.

  \<^item> \<^bold>\<open>Result.\<close> \<^type>\<open>analysis_answer\<close>'s cases, which a caller must tell apart, the
    projection \<^const>\<open>render_report\<close> that turns an analysed report into displayable
    data, and the readers of that data: contexts, states, routes, checks, globals and
    diagnostics. The records reach OCaml abstract, readable only through their
    selectors, so a field added later cannot break a consumer that matched on field
    order. A caller maps \<^const>\<open>render_report\<close> over the answer with
    \<^const>\<open>map_analysis_answer\<close>, passing the value printer it wants: the CLI composes
    \<^const>\<open>string_of_abstract_value\<close> with its decoding of ASCII symbol tokens.

  \<^item> \<^bold>\<open>Ask.\<close> The values naming a request: which domain, which rule merges
    side-effected globals, which context policy. A caller constructs these, so their
    constructors are public.

  \<^item> \<^bold>\<open>Program.\<close> What the frontend builds an \<^type>\<open>imp_prog\<close> out of: the command
    and expression constructors, the program builder, and the numeral and character
    conversions that bridge OCaml's integers to HOL's.

  \<^item> \<^bold>\<open>Inspect.\<close> Structural readers with no consumer on the CLI's analysis path.
    They exist for the OCaml program printer and the CFG regressions, and are listed
    apart so that reading the surface as ``what the CLI calls'' does not quietly drop
    them.

  \<^item> \<^bold>\<open>Trace.\<close> The solver's events and the readers a run hands the tracer
    (\<^theory>\<open>Voblint_CLI.Trace_Run\<close>). The CLI's trace renderer matches on them, so
    they must be public.
\<close>

export_code

  \<comment> \<open>Run\<close>
  run_voblint

  \<comment> \<open>Result: answers, the report's rendering, contexts, states, routes, checks, globals,
     diagnostics\<close>
  Invalid_Activation Malformed_Program No_Answer Analysed map_analysis_answer
  render_report
  res_cfg res_contexts res_states res_routes res_checks res_globals res_diagnostics
  Context_Unit Context_Entry Context_Call_String
  state_point state_context state_value state_checks state_diagnostics state_steps
  Field_Store Field_Whole
  route_point route_context route_callee route_targets
  check_point check_label check_exp check_verdict
  global_unknown global_state Global_Named Global_Seed
  diagnostic_point diagnostic_occurrence diagnostic_obligation diagnostic_verdict
  arithmetic_operation arithmetic_divisor
  Check_Proved Check_Refuted Check_Unknown
  Bot Lifted
  cfg_entry cfg_node_list

  \<comment> \<open>Ask: configuration of domains, global update rule, context, program globals\<close>
  Analysis_Config
  Program_Globals_Flow_Sensitive Program_Globals_Flow_Insensitive
  Sign_Analysis Interval_Analysis Int_Analysis Refine_Fixpoint Refine_Once Refine_Never
  Parity_Analysis Congruence_Analysis Order_Analysis
  Globals_Join Globals_Per_Origin Globals_Warrow Globals_Warrow_Per_Origin Globals_Bounded_Narrowing
  Ctx_None Ctx_EntryState Ctx_CallString

  \<comment> \<open>Program: what the frontend builds an input out of\<close>
  mk_program proc_decl_ext
  SKIP Assign Seq com.If While Return Check com.Call
  N V Plus Minus Times Div Mod
  exp.Not And Or Less exp.Eq
  Statement FunctionEntry FunctionResult
  int_of_integer nat_of_integer integer_of_int integer_of_nat

  \<comment> \<open>Inspect: for the OCaml program printer and the CFG regressions, not the CLI\<close>
  declared_global_vars
  prog_table prog_main prog_procs
  prog_cfg cfg_intra_list cfg_calls_list prog_stmt_post_order
  EA_Nop EA_Assign EA_Special EA_Assume EA_AssumeNot EA_Body EA_Ret EA_Check
  CallEdge Nondet_Int

  \<comment> \<open>Trace: the events the solver reports and the readers a run hands the tracer\<close>
  Ev_Start Ev_Stop Ev_Query Ev_Query_Wpoint Ev_Iterate_From_Query Ev_Add_Infl Ev_Answer
  Ev_Query_Global Ev_Answer_Global Ev_Iterate Ev_Eq Ev_Rhs Ev_Still_Unstable Ev_Widen Ev_Sol
  Ev_Wpoint_Remove Ev_Wpoint_Clear Ev_Update Ev_Iterate_Changed Ev_Side Ev_Update_Global
    Ev_Destabilize
  Ev_Stable_Remove
  Ev_Route Trace_Printers Trace_Buffer Trace_Global Trace_Seed string_of_abstract_value Inl Inr

  in OCaml module_name Generated file_prefix "Voblint_Generated"

end
