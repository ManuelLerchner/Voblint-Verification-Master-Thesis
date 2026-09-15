theory Voblint_Codegen
  imports
    "Voblint_CLI.State_Report_Call_String"
    "Voblint_CLI.Analysis_Run"
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
  constructor, or hide a representation behind an eliminator --- still belongs in a
  hand-written OCaml facade over this module rather than in the shape of this list.
\<close>

text \<open>
  The roots below are the \<^emph>\<open>intended callable surface\<close>: what handwritten OCaml under
  \<open>cli/\<close>, \<open>codegen/regression/ocaml/\<close> and \<open>tests/property/\<close> actually calls. Everything else
  in the emitted module is serializer-reachable implementation detail, still present and
  still callable --- the signature narrows with the root list, the code does not. So the
  intent recorded here is not enforced: the generated module \<^emph>\<open>is\<close> the API, with no
  handwritten re-export layer in between that could reinterpret a constructor or a
  conversion.

  Analysis entry goes through \<^const>\<open>run_voblint\<close> alone, which consults
  \<^const>\<open>resolve_analysis_config\<close> internally, so the CLI never re-decides legality.
  The typed and config-level dispatchers (\<open>analyse\<close>, \<open>analyse_config\<close>,
  \<open>analyse_with_solver\<close>, ...) are not roots: nothing handwritten calls them.

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
  if wanted, belongs in a handwritten OCaml facade over \<open>Generated\<close> --- a layer this
  project does not currently have.

  Two further modules are emitted regardless: \<open>Bit_Shifts\<close> and \<open>Str_Literal\<close> are HOL's
  own runtime support, injected as literal target code rather than generated from
  constants here.
\<close>

text \<open>
  The list below is grouped by what each name is \<^emph>\<open>for\<close>, because the groups answer
  different questions and only one of them is an operation.

  \<^item> \<^bold>\<open>Run.\<close> \<^const>\<open>run_voblint\<close>, alone. Everything a caller can ask the analyser
    to do goes through it.

  \<^item> \<^bold>\<open>Result.\<close> \<^type>\<open>analysis_answer\<close>'s three cases, which a caller must tell apart,
    and the readers of a successful one: contexts, states, routes, checks, globals and
    diagnostics. The records reach OCaml abstract, readable only through their
    selectors, so a field added later cannot break a consumer that matched on field
    order.

  \<^item> \<^bold>\<open>Ask.\<close> The values naming a request: which domain, which solver discipline,
    which context policy. A caller constructs these, so their constructors are public.

  \<^item> \<^bold>\<open>Program.\<close> What the frontend builds an \<^type>\<open>imp_prog\<close> out of: the command
    and expression constructors, the program builder, and the numeral and character
    conversions that bridge OCaml's integers to HOL's.

  \<^item> \<^bold>\<open>Inspect.\<close> Structural readers with no consumer on the CLI's analysis path.
    They exist for the OCaml program printer and the CFG regressions, and are listed
    apart so that reading the surface as ``what the CLI calls'' does not quietly drop
    them.
\<close>

export_code

  \<comment> \<open>Run\<close>
  run_voblint

  \<comment> \<open>Result: answers, contexts, states, routes, checks, globals, diagnostics\<close>
  Malformed_Program Unsupported_Configuration Analysed
  res_cfg res_contexts res_states res_routes res_checks res_globals res_diagnostics
  Context_Unit Context_Entry Context_Call_String
  state_point state_context state_value state_checks state_diagnostics
  route_point route_context route_callee route_targets
  check_point check_exp check_verdict
  global_var global_val
  diagnostic_point diagnostic_obligation diagnostic_verdict arithmetic_operation
  Check_Proved Check_Refuted Check_Unknown
  Bot Lifted
  cfg_entry cfg_node_list

  \<comment> \<open>Ask: domain, solver, context\<close>
  Sign_Analysis Interval_Analysis Int_Analysis Parity_Analysis Congruence_Analysis
  Solver_Join Solver_PerOrigin Solver_Warrow Solver_WarrowPerOrigin
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

  in OCaml module_name Generated file_prefix "Voblint_CLI"

end


