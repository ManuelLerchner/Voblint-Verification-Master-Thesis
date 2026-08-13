theory Example_State_Report_GraphViz
  imports
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_Analysis.Sign_Print"
    "Voblint_Analysis.Interval_Print"
    "Voblint_Examples.Example_Analysis_Dispatch"
begin

text \<open>
  \<open>raw_cfg_dot\<close>'s \<open>node_annotation\<close> hook already renders a verdict-only
  \<^const>\<open>classify_checks\<close> report through \<^const>\<open>check_report_node_annotation\<close>.
  This is the same idea over \<open>analyse_with_state\<close>'s richer report: the
  rendered label gains one line per queried variable, printed through the
  same domain print functions (\<open>string_of_sign\<close>, \<open>string_of_ivl\<close>) the
  standalone \<open>Sign_Print\<close>/\<open>Interval_Print\<close> theories already export, so the
  DOT rendering shows a real solved state rather than a hand-built one.
\<close>

fun string_of_abstract_value :: "abstract_value \<Rightarrow> string" where
  "string_of_abstract_value (SignValue s) = string_of_sign s"
| "string_of_abstract_value (IntervalValue i) = string_of_ivl i"

text \<open>
  \<open>is_bottom_abstract_value\<close> tests each domain's own \<^class>\<open>order_bot\<close>
  instance (\<open>x \<le> bot \<longleftrightarrow> x = bot\<close> there) rather than a fresh equality
  check, so it needs no new instance beyond what \<^const>\<open>analyse_with_state\<close>
  already exercises. A pointwise abstract state's concretisation is the
  conjunction of every variable's own concretisation, so one \<^const>\<open>bot\<close>
  component already forces the whole store empty: querying any single
  in-scope variable -- \<^const>\<open>ret_var\<close>, always in scope, is a convenient
  fixed choice -- is enough to test whether a report entry's program point is
  reachable at all, not just whether that one variable happens to be
  unconstrained.
\<close>

text \<open>
  Dispatches to each domain's own \<^const>\<open>is_bot\<close> (\<^class>\<open>sound_domain\<close>,
  \<^theory>\<open>Voblint_Core.Abstract_Domain\<close>) rather than a bespoke test per
  branch: \<open>is_bot\<close> is exact by the class's own \<open>is_bot_correct\<close> axiom for
  every instance, Sign and Interval today and any future domain added to
  \<^type>\<open>abstract_value\<close> without this dispatcher changing at all.
\<close>

fun is_bottom_abstract_value :: "abstract_value \<Rightarrow> bool" where
  "is_bottom_abstract_value (SignValue s) = is_bot s"
| "is_bottom_abstract_value (IntervalValue i) = is_bot i"

text \<open>
  \<open>program_vars\<close> is the union of \<^const>\<open>scope_vnames_list\<close> over every
  procedure in the program (including \<open>main\<close>), a safe program-wide
  superset of any single activation's scope. Querying a variable outside a
  point's own activation through \<^const>\<open>analyse_with_state\<close>'s state
  function is harmless: it returns that name's ordinary default, never a
  false bottom witness. Probing every in-scope variable rather than one
  fixed name (\<^const>\<open>ret_var\<close> alone, tried first) matters because Sign
  and Interval are both non-relational --- \<open>gamma\<close> of a pointwise abstract
  state is the conjunction of every variable's own \<open>gamma\<close>, so it is empty
  \<^bold>\<open>iff\<close> some variable's is, not only when one particular fixed variable's
  is. A single fixed probe is a sound but incomplete reachability test: it
  can miss a program point whose local state has collapsed to bottom
  through a variable other than the one being asked about. Probing every
  in-scope variable closes that gap; for a non-relational domain, no
  variable outside that scope can add a witness \<^const>\<open>scope_vnames_list\<close>
  does not already cover, so the test is exact, not merely broader.
\<close>

definition program_vars :: "imp_prog \<Rightarrow> vname list" where
  "program_vars p =
     remdups (concat (map (scope_vnames_list p) (prog_main_name # prog_procs p)))"

definition state_line :: "(vname \<Rightarrow> abstract_value) \<Rightarrow> vname \<Rightarrow> string" where
  "state_line f x = String.explode x @ ''='' @ string_of_abstract_value (f x)"

definition state_report_node_annotation ::
    "vname list \<Rightarrow> (pp \<times> bexp \<times> check_result \<times> (vname \<Rightarrow> abstract_value)) list
     \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "state_report_node_annotation vars report v =
     (case find (\<lambda>entry. fst entry = v) report of
        None \<Rightarrow> None
      | Some (_, cnd, res, f) \<Rightarrow>
          (case check_result_annotation res cnd of
             Node_Annotation lbl style \<Rightarrow>
               Some (Node_Annotation (join_gv_nl (lbl # map (state_line f) vars)) style)))"

definition state_report_dot ::
    "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> vname list \<Rightarrow> String.literal" where
  "state_report_dot kind p vars =
     raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (state_report_node_annotation vars (analyse_with_state kind p))"

text \<open>
  Reuses \<open>state_wiring_ex_prog\<close>
  (\<^theory>\<open>Voblint_Examples.Example_Analysis_Dispatch\<close>) rather than a fresh
  program: a single exact write with no widening, so \<^const>\<open>analyse\<close>
  itself already classifies the check \<open>Check_Proved\<close> under
  \<open>Interval_Analysis\<close>, and \<open>analyse_with_state\<close> reports the exact
  \<open>[5,5]\<close> interval behind it --- the checked verdict and the rendered
  state agree because both come from the same solved report.
\<close>

text \<open>
  \<open>report_vars\<close> and \<open>bexp_vnames_list\<close> turn \<^const>\<open>bexp_vnames\<close>'s set of
  variable occurrences into a sorted list, the same idiom
  \<^const>\<open>scope_vnames_list\<close> already uses over \<^typ>\<open>vname\<close> via
  \<^const>\<open>sorted_list_of_set\<close>. \<open>state_report_dot_auto\<close> is the CLI-facing
  sibling of \<open>state_report_dot\<close>: instead of a caller-supplied variable
  list, it renders exactly the variables occurring in some check condition
  in the report, solving the program once rather than once per call.
\<close>

definition bexp_vnames_list :: "bexp \<Rightarrow> vname list" where
  "bexp_vnames_list b = sorted_list_of_set (bexp_vnames b)"

definition report_vars ::
    "(pp \<times> bexp \<times> check_result \<times> (vname \<Rightarrow> abstract_value)) list \<Rightarrow> vname list" where
  "report_vars report =
     sorted_list_of_set (\<Union> ((\<lambda>(_, c, _, _). bexp_vnames c) ` set report))"

definition state_report_dot_auto :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "state_report_dot_auto kind p =
     (let report = analyse_with_state kind p
      in raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (state_report_node_annotation (report_vars report) report))"

text \<open>
  The canonical-snapshot sibling of \<open>state_report_dot_auto\<close>: same report,
  same \<open>state_report_node_annotation\<close> hook, but rendered through
  \<^const>\<open>raw_cfg_canonical_text_lit\<close> instead of \<^const>\<open>raw_cfg_dot_lit\<close> ---
  a DOT-free regression representation of the same solved analysis.
\<close>

definition state_report_graph_snapshot_auto :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "state_report_graph_snapshot_auto kind p =
     (let report = analyse_with_state kind p
      in raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (state_report_node_annotation (report_vars report) report))"

definition state_report_demo_dot :: String.literal where
  "state_report_demo_dot =
     state_report_dot Interval_Analysis state_wiring_ex_prog [STR ''x'']"

ML_val \<open>writeln (@{code state_report_demo_dot})\<close>

text \<open>
  A second, self-contained \<open>export_code\<close> surface for the \<open>voblint\<close> CLI: the
  narrower \<open>Voblint_Analyse_OCaml\<close> export
  (\<^theory>\<open>Voblint_Examples.Example_Analysis_Dispatch\<close>) has no reachable
  GraphViz-rendering constant, and that theory precedes this one in the
  import order, so \<open>state_report_dot_auto\<close> cannot be added to its existing
  blocks. This block otherwise mirrors that one's constant list exactly
  (same AST constructors, same numeral/char bridges), plus
  \<open>state_report_dot_auto\<close>, \<open>bexp_vnames_list\<close>, and
  \<open>string_of_abstract_value\<close> for CLI-side rendering.
\<close>

text \<open>
  \<open>state_report_dot_auto\<close> anchors every node label to a report entry
  (\<^const>\<open>state_report_node_annotation\<close> looks a point up in
  \<^const>\<open>analyse_with_state\<close>'s report, which \<^const>\<open>classify_checks_with_state\<close>
  only ever populates at check nodes), so every non-check node renders with no
  state at all. \<open>full_state_dot_auto\<close> instead queries the solved environment
  directly at \<^emph>\<open>every\<close> \<^typ>\<open>pp\<close> via \<^const>\<open>analyse_sign_env_for\<close> /
  \<^const>\<open>analyse_interval_td_at\<close> -- the same per-point lookup
  \<open>analyse_sign_report_for_code\<close>/\<open>interval_td_check_report_code\<close> already use
  to build a check's own state -- so the annotation exists independently of
  whether that point happens to carry a check.
\<close>

fun analyse_env_for :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> abstract_value abs_state" where
  "analyse_env_for Sign_Analysis p v =
     SignValue \<circ> analyse_sign_env_for (declared_global p) p v"
| "analyse_env_for Interval_Analysis p v =
     IntervalValue \<circ>
       case_lifted bot id
         (analyse_interval_td_at (resolved_st_q_is_bot_for (declared_global_vars p))
           (declared_global p) (prog_table p) (prog_procs p)
           prog_main_name (prog_main p) v)"

text \<open>
  Unlike \<^const>\<open>state_report_node_annotation\<close>, every \<^typ>\<open>pp\<close> gets an
  annotation here (never \<open>None\<close>), so \<^const>\<open>raw_cfg_dot\<close>'s own default
  styling never applies; the style string below is that same default
  (\<open>lightgreen\<close>, unfilled by any check verdict) so a full-state rendering
  looks like an ordinary node with extra lines, not a flagged one.
\<close>

definition full_state_node_annotation ::
    "vname list \<Rightarrow> (pp \<Rightarrow> abstract_value abs_state) \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "full_state_node_annotation vars env v =
     Some (Node_Annotation (join_gv_nl (map (state_line (env v)) vars))
             ''shape=box,style=filled,fillcolor=lightgreen'')"

definition full_state_dot_auto :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "full_state_dot_auto kind p =
     raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (full_state_node_annotation (program_vars p) (analyse_env_for kind p))"

text \<open>Canonical-text sibling, the same DOT-free relationship
  \<open>state_report_graph_snapshot_auto\<close> already has to \<open>state_report_dot_auto\<close>.\<close>

definition full_state_graph_snapshot_auto :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "full_state_graph_snapshot_auto kind p =
     raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (full_state_node_annotation (program_vars p) (analyse_env_for kind p))"

text \<open>
  Entry-state siblings of \<open>state_report_dot_auto\<close>/\<open>full_state_dot_auto\<close>
  (\<open>#108\<close>), Interval-only (\<^const>\<open>analyse_ctx\<close> has no Sign entry-state
  branch, so there is no \<open>analysis_kind\<close> parameter here). A \<^typ>\<open>pp\<close> may be
  covered by several entry-state contexts at once; \<open>entry_state_env_at\<close>
  joins every covered context's reading of a variable through \<^typ>\<open>ivl\<close>'s
  own \<^class>\<open>semilattice_sup\<close> (\<^const>\<open>Sup_fin\<close> over \<^const>\<open>Set.filter\<close> on the
  solver's own already-finite solution set, the same non-comprehension
  idiom \<open>entry_state_classify_at\<close> uses and for the same reason -- \<^typ>\<open>ivl
  list\<close> has no \<^class>\<open>enum\<close> instance). An uncovered point falls back to the
  seeded default context, mirroring \<open>entry_state_classify_at\<close>'s own
  uncovered case.
\<close>

definition entry_state_env_at ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> cfg_node \<Rightarrow> abstract_value abs_state" where
  "entry_state_env_at gs is_bot_pred Pi ps mnm main v x =
     (let sol = entry_state_sol gs is_bot_pred Pi ps mnm main;
          sg = entry_state_sg_exec gs is_bot_pred Pi ps mnm main;
          ctxs = snd ` Set.filter (\<lambda>(v', ctx). v' = v) (fst sol)
      in IntervalValue
           (if ctxs = {} then case_lifted bot id (sg (Inl (v, []))) x
            else Sup_fin ((\<lambda>ctx. case_lifted bot id (sg (Inl (v, ctx))) x) ` ctxs)))"

definition entry_state_full_state_dot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_full_state_dot_auto p =
     raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (full_state_node_annotation (program_vars p)
          (entry_state_env_at (declared_global p) (resolved_st_q_is_bot_for (declared_global_vars p))
             (prog_table p) (prog_procs p) prog_main_name (prog_main p)))"

definition entry_state_full_state_graph_snapshot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_full_state_graph_snapshot_auto p =
     raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (full_state_node_annotation (program_vars p)
          (entry_state_env_at (declared_global p) (resolved_st_q_is_bot_for (declared_global_vars p))
             (prog_table p) (prog_procs p) prog_main_name (prog_main p)))"

text \<open>
  \<open>entry_state_report_for_annotation\<close> is \<open>entry_state_check_report_prog\<close>
  (already the context-aggregated verdict, \<^const>\<open>entry_state_classify_at\<close>)
  paired with \<open>entry_state_env_at\<close>'s own, separately joined, per-variable
  state reading, giving \<^const>\<open>state_report_node_annotation\<close> the same
  \<open>(pp \<times> bexp \<times> check_result \<times> (vname \<Rightarrow> abstract_value)) list\<close> shape
  \<open>analyse_with_state\<close>'s report already has.
\<close>

definition entry_state_report_for_annotation ::
    "imp_prog \<Rightarrow> (pp \<times> bexp \<times> check_result \<times> (vname \<Rightarrow> abstract_value)) list" where
  "entry_state_report_for_annotation p =
     map (\<lambda>(v, cnd, res). (v, cnd, res,
            entry_state_env_at (declared_global p) (resolved_st_q_is_bot_for (declared_global_vars p))
              (prog_table p) (prog_procs p) prog_main_name (prog_main p) v))
       (entry_state_check_report_prog prog_main_name p)"

definition entry_state_report_dot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_report_dot_auto p =
     (let report = entry_state_report_for_annotation p
      in raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (state_report_node_annotation (report_vars report) report))"

definition entry_state_report_graph_snapshot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_report_graph_snapshot_auto p =
     (let report = entry_state_report_for_annotation p
      in raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (state_report_node_annotation (report_vars report) report))"

text \<open>
  \<open>program_vars\<close> pulls \<^const>\<open>scope_vnames_list\<close> (hence \<open>VIMP_Notation\<close>,
  already mapped to \<open>Core\<close> below) into the same export as \<open>Complete_Lattices\<close>'s
  \<^class>\<open>complete_lattice\<close> set instance for the first time. Left unmapped,
  OCaml's single-file serializer places \<open>Complete_Lattices\<close> in its own
  module, and the two end up needing each other, which
  \<^theory>\<open>Voblint_Examples.Example_Analysis_Dispatch\<close>'s own header already
  documents as an OCaml module-splitting limit, not fixable by regrouping ---
  only by folding the two together, exactly as done there for \<open>Sign\<close>/\<open>Interval\<close>.
\<close>

code_identifier
  code_module Complete_Lattices \<rightharpoonup> (OCaml) Core

export_code
  analyse Sign_Analysis Interval_Analysis
  analyse_ctx Ctx_None Ctx_EntryState
  analyse_with_state SignValue IntervalValue
  state_report_dot_auto state_report_graph_snapshot_auto
  full_state_dot_auto full_state_graph_snapshot_auto
  entry_state_report_dot_auto entry_state_report_graph_snapshot_auto
  entry_state_full_state_dot_auto entry_state_full_state_graph_snapshot_auto
  bexp_vnames_list string_of_abstract_value
  is_bottom_abstract_value program_vars
  mk_program proc_decl_of declared_global_vars pretty_string_of_program
  SKIP com.Call Random com.If Assign Seq While Restore Unwind Return Check
  N V Plus Minus Times
  Bc bexp.Not And Or Less bexp.Eq
  Check_Proved Check_Refuted Check_Unknown
  int_of_integer nat_of_integer integer_of_int integer_of_nat
  Statement FunctionEntry FunctionResult
  char_of_integer integer_of_char
  string_of_bexp
  in OCaml file_prefix "Voblint_CLI"

end
