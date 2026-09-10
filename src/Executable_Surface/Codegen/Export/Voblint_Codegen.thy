theory Voblint_Codegen
  imports
    "Voblint_CLI.State_Report_Call_String"
    "Voblint_CLI.Analysis_Run"
begin

section "Code export surface"

text \<open>
  This session owns executable exports; the examples session proves and demonstrates the
  exported definitions without materializing generated code.

  One export block, deliberately. There used to be a second, narrower one
  (\<open>Voblint_Analyse_OCaml\<close>) whose only consumer was the external OCaml regression driver
  under \<open>codegen/regression/ocaml/\<close>, which needs a handful of CFG-inspection constants
  the CLI itself never calls. Two blocks did not make that surface any narrower: Isabelle
  emits the reachable transitive closure of whatever is named, so both files carried
  essentially the same machinery, differing by exactly those CFG constants and costing
  around 8,400 duplicated generated lines. Naming the constants here instead and pointing
  the driver at this module keeps one generated artifact for one analysis.

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

  Analysis entry goes through \<^const>\<open>analyse_config\<close>/\<^const>\<open>analyse_config_ctx\<close>/
  \<^const>\<open>analyse_config_with_state\<close>, which consult
  \<^const>\<open>resolve_analysis_config\<close> internally, so the CLI never re-decides legality. The
  pre-configuration entry points \<open>analyse_with_state\<close>/\<open>analyse_with_solver\<close> are not
  roots: nothing handwritten calls them, and the configuration path supersedes them.
  \<^const>\<open>analyse\<close> stays, because the external regression oracle calls it directly
  as its domain-dispatch check.

  The last group of roots is there for signature visibility rather than for dispatch.
  A constant the serializer does not consider public is emitted but left out of the
  module signature, and a datatype it does not consider public stays abstract, which
  makes it unmatchable. So anything handwritten OCaml names --- even only to take it
  apart --- has to be a root: \<open>Bot\<close>/\<open>Lifted\<close>, which \<open>cli/main.ml\<close> matches to tell a
  dead point from a live verdict, and \<open>prog_table\<close>/\<open>prog_main\<close>/\<open>prog_procs\<close>, which the
  property-test AST driver passes to \<^const>\<open>pretty_string_of_program\<close> on a round trip.

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

  \<^item> \<^bold>\<open>Ask.\<close> The values naming a request: which domain, which solver discipline,
    which context policy, which drawing. A caller constructs these, so their
    constructors are public.

  \<^item> \<^bold>\<open>Answer.\<close> \<^type>\<open>analysis_answer\<close>'s three cases, which a caller must tell
    apart, and the readers of a successful one. \<^type>\<open>analysis_output\<close> and
    \<^type>\<open>check_row\<close> are deliberately \<^emph>\<open>not\<close> here as constructors: they reach
    OCaml abstract, readable only through their selectors, so a field added later
    cannot break a consumer that matched on field order.

  \<^item> \<^bold>\<open>Graph.\<close> The rendered graph, as data. The prefixes are terse and worth
    spelling out once: \<open>x\<close> is export, and the second letter names the record ---
    \<open>xn_\<close> a node (identifier, label, kind, status, annotation lines), \<open>xe_\<close> an edge
    (source, destination, kind, label), \<open>xc_\<close> a cluster (identifier, label, member
    nodes), \<open>xg_\<close> the graph itself (its clusters, nodes and edges). \<open>XN_\<close>, \<open>XE_\<close>
    and \<open>NS_\<close> are the corresponding tag datatypes: what kind of node, what kind of
    edge, and what a check node's status is. A renderer reading \<^const>\<open>xn_kind\<close>
    and \<^const>\<open>xn_status\<close> together has everything a styling decision needs, which
    is why this stays data here and drawing stays in OCaml.

  \<^item> \<^bold>\<open>Program.\<close> What the frontend builds an \<^type>\<open>imp_prog\<close> out of: the command
    and expression constructors, the program builder, and the numeral and character
    conversions that bridge OCaml's integers to HOL's.

  \<^item> \<^bold>\<open>Inspect.\<close> Structural readers with no consumer on the CLI's analysis path.
    They exist for the property-test AST driver and the CFG regressions, and are
    listed apart so that reading the surface as ``what the CLI calls'' does not
    quietly drop them.
\<close>

export_code

  \<comment> \<open>Run\<close>
  run_voblint

  \<comment> \<open>Ask: domain, solver, context, drawing\<close>
  Sign_Analysis Interval_Analysis Int_Analysis Parity_Analysis Congruence_Analysis
  Solver_Join Solver_PerOrigin Solver_Warrow Solver_WarrowPerOrigin
  Ctx_None Ctx_EntryState Ctx_CallString
  View_Report View_Checks View_States View_Checked_States View_Contexts

  \<comment> \<open>Answer: the three outcomes, then the readers of a successful one\<close>
  Malformed_Program Unsupported_Configuration Analysed
  out_graph out_snapshot out_checks out_globals
  row_point row_condition row_verdict row_state
  Check_Proved Check_Refuted Check_Unknown
  Bot Lifted

  \<comment> \<open>Graph: node, edge, cluster, graph, and their tag datatypes\<close>
  xn_id xn_label xn_kind xn_status xn_lines
  xe_src xe_dst xe_kind xe_label
  xc_id xc_label xc_nodes
  xg_clusters xg_nodes xg_edges
  XN_Entry XN_Exit XN_ProcEntry XN_ProcExit XN_Point XN_Global XN_Source
  XE_Intra XE_Enter XE_Combine XE_CallToReturn XE_GlobalRead XE_GlobalWrite
  NS_Plain NS_Proved NS_Refuted NS_Unknown NS_Unreachable NS_Exit

  \<comment> \<open>Program: what the frontend builds an input out of\<close>
  mk_program proc_decl_ext
  SKIP Assign Seq com.If While Return Check com.Call
  N V Plus Minus Times
  exp.Not And Or Less exp.Eq
  Statement FunctionEntry FunctionResult
  int_of_integer nat_of_integer integer_of_int integer_of_nat integer_of_char

  \<comment> \<open>Inspect: for the property AST driver and the CFG regressions, not the CLI\<close>
  declared_global_vars pretty_string_of_program
  prog_table prog_main prog_procs
  prog_cfg cfg_intra_list cfg_calls_list prog_stmt_post_order
  EA_Nop EA_Assign EA_Special EA_Assume EA_AssumeNot EA_Body EA_Ret EA_Check
  CallEdge Nondet_Int

  in OCaml module_name Generated file_prefix "Voblint_CLI"

end


