theory Example_State_Report_GraphViz
  imports
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_Analysis.Sign_Print"
    "Voblint_Analysis.Interval_Print"
    "Voblint_Examples.Example_Analysis_Dispatch_Regression"
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
  (\<^theory>\<open>Voblint_Examples.Example_Analysis_Dispatch_Regression\<close>) rather than a fresh
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
  The codegen session collects this theory's GraphViz surface with the
  analysis facade from \<^theory>\<open>Voblint_Examples.Analyse_Dispatch\<close>.
  That narrower facade has no reachable GraphViz-rendering constant, and it
  precedes this theory in the import order, so \<open>state_report_dot_auto\<close>
  belongs in the later export declaration. The GraphViz surface uses the
  same AST constructors and numeral/char bridges, plus
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

text \<open>
  Point-free in \<open>v\<close>, mirroring \<^const>\<open>analyse_sign_env_for\<close>/\<^const>\<open>analyse_interval_td_at\<close>'s
  own single-solve-per-report fix one layer down: a plain \<open>fun\<close> pattern-matching on \<open>kind, p, v\<close>
  jointly would rebuild the \<open>analyse_sign_env_for (declared_global p) p\<close>/
  \<open>analyse_interval_td_at ... (prog_main p)\<close> partial application -- and therefore re-solve --
  on every \<open>v\<close>, even though each of those is itself already solved exactly once per partial
  application. Binding \<open>env\<close> here, outside the returned \<open>\<lambda>v\<close>, means a caller that partially
  applies \<open>analyse_env_for kind p\<close> once (every current caller does: \<open>full_state_node_annotation\<close>
  reuses the same closure across every CFG node) solves the selected analysis exactly once,
  regardless of how many nodes it renders.
\<close>

definition analyse_env_for :: "analysis_kind \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> abstract_value abs_state" where
  "analyse_env_for kind p =
     (case kind of
        Sign_Analysis \<Rightarrow>
          (let env = analyse_sign_env_for (declared_global p) p in (\<lambda>v. SignValue \<circ> env v))
      | Interval_Analysis \<Rightarrow>
          (let env = analyse_interval_td_at (resolved_st_q_is_bot_for (declared_global_vars p))
                       (declared_global p) (prog_table p) (prog_procs p)
                       prog_main_name (prog_main p)
           in (\<lambda>v. IntervalValue \<circ> case_lifted bot id (env v))))"

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

text \<open>
  Point-free in \<open>v\<close>/\<open>x\<close> so \<^const>\<open>entry_state_sol\<close> is solved exactly once per partial
  application to \<open>gs is_bot_pred Pi ps mnm main\<close>, not once per \<open>(v, x)\<close> query. Every caller
  already partially applies these six arguments once and reuses the result across every CFG node
  (\<open>full_state_node_annotation\<close>'s \<open>env v\<close>/\<open>env v x\<close>), so this is a pure sharing fix, provably
  the same function as the previous curried-all-the-way-through definition -- no lemma needed, the
  \<open>let\<close>/lambda reordering is extensional equality, not a new fact about the analysis.
\<close>

definition entry_state_env_at ::
    "(vname \<Rightarrow> bool) \<Rightarrow> (ivl exec_dg_st \<Rightarrow> bool) \<Rightarrow> proc_table \<Rightarrow> pname list \<Rightarrow> pname \<Rightarrow> com
       \<Rightarrow> cfg_node \<Rightarrow> abstract_value abs_state" where
  "entry_state_env_at gs is_bot_pred Pi ps mnm main =
     (let sol = entry_state_sol gs is_bot_pred Pi ps mnm main;
          sg = entry_state_sg_exec_from_sol gs sol
      in (\<lambda>v x.
            let ctxs = snd ` Set.filter (\<lambda>(v', ctx). v' = v) (fst sol)
            in IntervalValue
                 (if ctxs = {} then case_lifted bot id (sg (Inl (v, []))) x
                  else Sup_fin ((\<lambda>ctx. case_lifted bot id (sg (Inl (v, ctx))) x) ` ctxs))))"

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
  \<^theory>\<open>Voblint_Examples.Analyse_Dispatch\<close>'s own header already
  documents as an OCaml module-splitting limit, not fixable by regrouping ---
  only by folding the two together, exactly as done there for \<open>Sign\<close>/\<open>Interval\<close>.
\<close>

code_identifier
  code_module Complete_Lattices \<rightharpoonup> (OCaml) Core



end
