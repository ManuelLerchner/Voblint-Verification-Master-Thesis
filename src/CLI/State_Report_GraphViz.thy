theory State_Report_GraphViz
  imports
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_Analysis.Sign_Print"
    "Voblint_Analysis.Interval_Print"
    "Voblint_Analysis.Int_Print"
    Analyse_Dispatch
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
| "string_of_abstract_value (IntDomValue d) = string_of_int_dom d"
| "string_of_abstract_value (ParityValue v) = string_of_parity v"

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
| "is_bottom_abstract_value (IntDomValue d) = is_bot d"
| "is_bottom_abstract_value (ParityValue v) = is_bot v"

text \<open>
  The \<open>top\<close> counterpart, used only to suppress an uninformative return-slot line: a
  \<^const>\<open>top\<close> return value says nothing the reader did not already know, and printing it
  at every node crowds out the variables that do carry information. Each domain's own
  \<^class>\<open>order_top\<close> instance decides, so this dispatches exactly as
  \<^const>\<open>is_bottom_abstract_value\<close> does and needs no new instance either. Purely a
  presentation filter --- nothing downstream reads it, and a suppressed line is not a claim
  that the slot is unset.
\<close>

fun is_top_abstract_value :: "abstract_value \<Rightarrow> bool" where
  "is_top_abstract_value (SignValue s) = (s = top)"
| "is_top_abstract_value (IntervalValue i) = (i = top)"
| "is_top_abstract_value (IntDomValue d) = (d = top)"
| "is_top_abstract_value (ParityValue v) = (v = top)"

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
    "vname list \<Rightarrow> (pp \<times> exp \<times> check_result \<times> (vname \<Rightarrow> abstract_value)) list
     \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "state_report_node_annotation vars report v =
     (case find (\<lambda>entry. fst entry = v) report of
        None \<Rightarrow> None
      | Some (_, cnd, res, f) \<Rightarrow>
          (case check_result_annotation res cnd of
             Node_Annotation lbl style \<Rightarrow>
               Some (Node_Annotation (join_gv_nl (lbl # map (state_line f) vars)) style)))"

text \<open>
  \<open>analyse_with_state\<close>'s report also carries an exact \<open>unreachable\<close> flag
  (\<^theory>\<open>Voblint_Analysis.Sign_Checks\<close>); this GraphViz rendering projects it
  away rather than threading it through \<^const>\<open>state_report_node_annotation\<close>,
  since the rendered label already shows the (necessarily witness-bottom)
  state at an unreachable point instead of suppressing the node the way the
  CLI's text report does.
\<close>

definition state_report_dot ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> vname list \<Rightarrow> String.literal" where
  "state_report_dot kind p vars =
     raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (state_report_node_annotation vars
          (map (\<lambda>(u, c, r, _, s). (u, c, r, s)) (analyse_with_state kind p)))"

text \<open>
  \<open>report_vars\<close> and \<open>exp_vnames_list\<close> turn \<^const>\<open>exp_vnames\<close>'s set of
  variable occurrences into a sorted list, the same idiom
  \<^const>\<open>scope_vnames_list\<close> already uses over \<^typ>\<open>vname\<close> via
  \<^const>\<open>sorted_list_of_set\<close>. \<open>state_report_dot_auto\<close> is the CLI-facing
  sibling of \<open>state_report_dot\<close>: instead of a caller-supplied variable
  list, it renders exactly the variables occurring in some check condition
  in the report, solving the program once rather than once per call.
\<close>

definition exp_vnames_list :: "exp \<Rightarrow> vname list" where
  "exp_vnames_list b = sorted_list_of_set (exp_vnames b)"

definition report_vars :: "('n \<times> exp \<times> 'r) list \<Rightarrow> vname list" where
  "report_vars report =
     sorted_list_of_set (\<Union> ((\<lambda>(_, c, _). exp_vnames c) ` set report))"

definition state_report_dot_auto :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "state_report_dot_auto kind p =
     (let report = map (\<lambda>(u, c, r, _, s). (u, c, r, s)) (analyse_with_state kind p)
      in raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (state_report_node_annotation (report_vars report) report))"

text \<open>
  The canonical-snapshot sibling of \<open>state_report_dot_auto\<close>: same report,
  same \<open>state_report_node_annotation\<close> hook, but rendered through
  \<^const>\<open>raw_cfg_canonical_text_lit\<close> instead of \<^const>\<open>raw_cfg_dot_lit\<close> ---
  a DOT-free regression representation of the same solved analysis.
\<close>

definition state_report_graph_snapshot_auto :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "state_report_graph_snapshot_auto kind p =
     (let report = map (\<lambda>(u, c, r, _, s). (u, c, r, s)) (analyse_with_state kind p)
      in raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (state_report_node_annotation (report_vars report) report))"

text \<open>
  The codegen session collects this theory's GraphViz surface with the
  analysis facade from \<^theory>\<open>Voblint_CLI.Analyse_Dispatch\<close>.
  That narrower facade has no reachable GraphViz-rendering constant, and it
  precedes this theory in the import order, so \<open>state_report_dot_auto\<close>
  belongs in the later export declaration. The GraphViz surface uses the
  same AST constructors and numeral/char bridges, plus
  \<open>state_report_dot_auto\<close>, \<open>exp_vnames_list\<close>, and
  \<open>string_of_abstract_value\<close> for CLI-side rendering.
\<close>

text \<open>
  \<open>state_report_dot_auto\<close> anchors every node label to a report entry
  (\<^const>\<open>state_report_node_annotation\<close> looks a point up in
  \<^const>\<open>analyse_with_state\<close>'s report, which \<^const>\<open>classify_checks_with_state\<close>
  only ever populates at check nodes), so every non-check node renders with no
  state at all. \<open>full_state_dot_auto\<close> (defined below, once
  \<open>point_state_node_annotation\<close> is in scope) instead queries the solved
  \<^type>\<open>analysis_result\<close> table directly at \<^emph>\<open>every\<close> \<^typ>\<open>pp\<close>, so the
  annotation exists independently of whether that point happens to carry a
  check.
\<close>

text \<open>
  Entry-state siblings of \<open>state_report_dot_auto\<close>/\<open>full_state_dot_auto\<close>,
  Interval-only (\<^const>\<open>analyse_ctx\<close> has no Sign entry-state branch, so there
  is no \<open>analysis_domain\<close> parameter here). Both read
  \<^const>\<open>analyse_interval_entry_state_result\<close>, the canonical solved-result
  table, rather than the solver's own solution map. A \<^typ>\<open>pp\<close> may be covered
  by several entry-state contexts at once, and \<^const>\<open>lookup_joined_state\<close> is
  the table's own per-node view: it joins exactly the covered contexts, each
  read at its own key, through \<^typ>\<open>ivl\<close>'s \<^class>\<open>semilattice_sup\<close>.

  That join answers with a \<^typ>\<open>'a point_state\<close>, and both of its cases are
  rendered. A node the solver never covered and a node whose every covered
  context concretizes to nothing are alike \<^const>\<open>Unreachable\<close>: no execution
  arrives, so there is no store to print variable lines for. Printing the
  underlying \<^const>\<open>bot\<close> reading instead would draw an ordinary live node for
  code nothing reaches.
\<close>

definition entry_state_point_env_at ::
    "(ivl list, ivl abs_state) analysis_result
       \<Rightarrow> pp \<Rightarrow> abstract_value abs_state point_state" where
  "entry_state_point_env_at r v =
     map_point_state (\<lambda>st. IntervalValue \<circ> st) (lookup_joined_state r v)"

text \<open>
  The unreachable styling draws from the palette \<^const>\<open>check_result_annotation\<close>
  and \<^const>\<open>analysis_node_attrs\<close> already use: \<open>gray40\<close>, the grey the renderer
  gives its own exit nodes, and deliberately not the \<open>gray70\<close> an undecided
  check carries. ``Nothing reaches this node'' and ``something reaches it and
  the abstraction could not decide'' are different findings and must not
  render alike.
\<close>

definition unreachable_gv_style :: string where
  "unreachable_gv_style = ''shape=box,style=filled,fillcolor=gray40,fontcolor=white''"

definition unreachable_state_annotation :: graphviz_node_annotation where
  "unreachable_state_annotation = Node_Annotation ''unreachable'' unreachable_gv_style"

definition dead_check_annotation :: "exp \<Rightarrow> graphviz_node_annotation" where
  "dead_check_annotation cnd =
     Node_Annotation (''check '' @ string_of_exp 0 cnd @ '' [dead]'') unreachable_gv_style"

text \<open>
  The shared full-state renderer for every \<^typ>\<open>'a point_state\<close>-valued
  monovariant or entry-state env: the same variable lines and the same
  default \<open>lightgreen\<close> styling at a \<^const>\<open>Reachable\<close> node, the shared
  \<^const>\<open>unreachable_state_annotation\<close> where there is no state to print. A
  point never gets its underlying \<^const>\<open>bot\<close> reading rendered as though it
  were an ordinary live state.
\<close>

definition point_state_node_annotation ::
    "vname list \<Rightarrow> (pp \<Rightarrow> abstract_value abs_state point_state)
       \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "point_state_node_annotation vars env v =
     (case env v of
        Unreachable \<Rightarrow> Some unreachable_state_annotation
      | Reachable st \<Rightarrow>
          Some (Node_Annotation (join_gv_nl (map (state_line st) vars))
                  ''shape=box,style=filled,fillcolor=lightgreen''))"

text \<open>
  \<open>analyse_point_env_for\<close> is the monovariant sibling of
  \<^const>\<open>entry_state_point_env_at\<close> below: the same \<^const>\<open>lookup_context\<close>
  reading of a solved \<^type>\<open>analysis_result\<close> table, projected into
  \<^type>\<open>abstract_value\<close> once per domain. Point-free in \<open>v\<close>, the same
  single-solve-per-render discipline \<open>entry_state_point_env_at\<close> gives the
  entry-state renderer: a plain \<open>fun\<close> pattern-matching on \<open>kind, p, v\<close>
  jointly would rebuild \<open>analyse_sign_result p\<close>/\<open>analyse_interval_td_result p\<close>/
  \<open>analyse_int_result p\<close> -- and therefore re-solve -- on every \<open>v\<close>, even
  though each of those is itself already solved exactly once per partial
  application. Binding \<open>r\<close> here, outside the returned \<open>\<lambda>v\<close>, means a caller
  that partially applies \<open>analyse_point_env_for kind p\<close> once (every current
  caller does: \<^const>\<open>point_state_node_annotation\<close> reuses the same closure
  across every CFG node) solves the selected analysis exactly once,
  regardless of how many nodes it renders. A node the solver's key domain
  never covers and a node whose stored state is witness-bottom are alike
  \<^const>\<open>Unreachable\<close> at the \<^const>\<open>lookup_context\<close> boundary, the same
  distinction \<open>entry_state_point_env_at\<close> already reads for the entry-state
  graph -- so this is that same reading applied to the monovariant tables,
  not a second convention.
\<close>

definition analyse_point_env_for ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> abstract_value abs_state point_state" where
  "analyse_point_env_for kind p =
     (case kind of
        Sign_Analysis \<Rightarrow>
          (let r = analyse_sign_result p
           in (\<lambda>v. map_point_state (\<lambda>st. SignValue \<circ> st) (lookup_context r v ())))
      | Interval_Analysis \<Rightarrow>
          (let r = analyse_interval_td_result p
           in (\<lambda>v. map_point_state (\<lambda>st. IntervalValue \<circ> st) (lookup_context r v ())))
      | Int_Analysis \<Rightarrow>
          (let r = analyse_int_result p
           in (\<lambda>v. map_point_state (\<lambda>st. IntDomValue \<circ> st) (lookup_context r v ())))
      | Parity_Analysis \<Rightarrow>
          (let r = analyse_parity_result p
           in (\<lambda>v. map_point_state (\<lambda>st. ParityValue \<circ> st) (lookup_context r v ()))))"

definition full_state_dot_auto :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "full_state_dot_auto kind p =
     raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (point_state_node_annotation (program_vars p) (analyse_point_env_for kind p))"

text \<open>Canonical-text sibling, the same DOT-free relationship
  \<open>state_report_graph_snapshot_auto\<close> already has to \<open>state_report_dot_auto\<close>.\<close>

definition full_state_graph_snapshot_auto :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "full_state_graph_snapshot_auto kind p =
     raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (point_state_node_annotation (program_vars p) (analyse_point_env_for kind p))"

text \<open>
  One render is one solve. The \<open>[code]\<close> equations bind the result table once,
  outside the per-node annotation closure, so the whole graph is annotated
  from a single \<^const>\<open>entry_state_sol_prog\<close> run no matter how many nodes it
  has; the defining equations stay in the shape that reads as the intended
  meaning.
\<close>

definition entry_state_full_state_dot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_full_state_dot_auto p =
     raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (point_state_node_annotation (program_vars p)
          (entry_state_point_env_at (analyse_interval_entry_state_result p)))"

declare entry_state_full_state_dot_auto_def [code del]

lemma entry_state_full_state_dot_auto_code [code]:
  "entry_state_full_state_dot_auto p =
     (let r = analyse_interval_entry_state_result p
      in raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (point_state_node_annotation (program_vars p) (entry_state_point_env_at r)))"
  unfolding entry_state_full_state_dot_auto_def Let_def by (rule refl)

definition entry_state_full_state_graph_snapshot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_full_state_graph_snapshot_auto p =
     raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
       (point_state_node_annotation (program_vars p)
          (entry_state_point_env_at (analyse_interval_entry_state_result p)))"

declare entry_state_full_state_graph_snapshot_auto_def [code del]

lemma entry_state_full_state_graph_snapshot_auto_code [code]:
  "entry_state_full_state_graph_snapshot_auto p =
     (let r = analyse_interval_entry_state_result p
      in raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (point_state_node_annotation (program_vars p) (entry_state_point_env_at r)))"
  unfolding entry_state_full_state_graph_snapshot_auto_def Let_def by (rule refl)

text \<open>
  \<open>entry_state_report_for_annotation\<close> pairs
  \<^const>\<open>entry_state_verdict_report_prog\<close>'s source-level verdicts with the same
  table's per-node joined state. The verdict column is
  \<^typ>\<open>contextual_verdict\<close>, not \<^typ>\<open>check_result\<close>: a check every covering
  context finds unreachable stays \<^const>\<open>Dead\<close> all the way into the annotation,
  which has a case for it, so nothing is collapsed into \<^const>\<open>Check_Unknown\<close>
  on the way to the graph.
\<close>

definition entry_state_report_for_annotation ::
    "imp_prog
       \<Rightarrow> (pp \<times> exp \<times> contextual_verdict \<times> abstract_value abs_state point_state) list" where
  "entry_state_report_for_annotation p =
     map (\<lambda>(v, cnd, verdict).
            (v, cnd, verdict,
             entry_state_point_env_at (analyse_interval_entry_state_result p) v))
       (entry_state_verdict_report_prog prog_main_name p)"

declare entry_state_report_for_annotation_def [code del]

text \<open>Both columns come off one table. The defining equation names
  \<^const>\<open>entry_state_verdict_report_prog\<close>, which builds its own;
  \<open>entry_state_verdict_report_prog_eq\<close> re-reads that report as
  \<^const>\<open>classify_checks_verdicts\<close> over an already-bound table, which is what
  lets verdicts and states share the single solve.\<close>

lemma entry_state_report_for_annotation_code [code]:
  "entry_state_report_for_annotation p =
     (let r = analyse_interval_entry_state_result p
      in map (\<lambda>(v, cnd, verdict). (v, cnd, verdict, entry_state_point_env_at r v))
           (classify_checks_verdicts (prog_cfg prog_main_name p) r interval_classify_check))"
  unfolding entry_state_report_for_annotation_def Let_def
    entry_state_verdict_report_prog_eq analyse_interval_entry_state_result_def
  by (rule refl)

text \<open>
  The \<^typ>\<open>contextual_verdict\<close> sibling of \<^const>\<open>state_report_node_annotation\<close>.
  A decided check at a reachable node renders exactly as before, through
  \<^const>\<open>check_result_annotation\<close> plus the state lines. The remaining case is
  the dead check, and it is one case, not two: a verdict is \<^const>\<open>Dead\<close>
  exactly when every context covered at the node is \<^const>\<open>Unreachable\<close>, which
  is also exactly when the joined state is, so the two columns cannot
  disagree.
\<close>

definition verdict_state_report_node_annotation ::
    "vname list
       \<Rightarrow> (pp \<times> exp \<times> contextual_verdict \<times> abstract_value abs_state point_state) list
       \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "verdict_state_report_node_annotation vars report v =
     (case find (\<lambda>entry. fst entry = v) report of
        None \<Rightarrow> None
      | Some (_, cnd, verdict, st) \<Rightarrow>
          Some (case (verdict, st) of
                  (Decided res, Reachable f) \<Rightarrow>
                    (case check_result_annotation res cnd of
                       Node_Annotation lbl style \<Rightarrow>
                         Node_Annotation (join_gv_nl (lbl # map (state_line f) vars)) style)
                | _ \<Rightarrow> dead_check_annotation cnd))"

definition entry_state_report_dot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_report_dot_auto p =
     (let report = entry_state_report_for_annotation p
      in raw_cfg_dot_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (verdict_state_report_node_annotation (report_vars report) report))"

definition entry_state_report_graph_snapshot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_report_graph_snapshot_auto p =
     (let report = entry_state_report_for_annotation p
      in raw_cfg_canonical_text_lit (prog_table p) (prog_procs p) prog_main_name (prog_main p)
           (verdict_state_report_node_annotation (report_vars report) report))"

text \<open>
  \<open>program_vars\<close> pulls \<^const>\<open>scope_vnames_list\<close> (hence \<open>VIMP_Notation\<close>,
  already mapped to \<open>Core\<close> below) into the same export as \<open>Complete_Lattices\<close>'s
  \<^class>\<open>complete_lattice\<close> set instance for the first time. Left unmapped,
  OCaml's single-file serializer places \<open>Complete_Lattices\<close> in its own
  module, and the two end up needing each other, which
  \<^theory>\<open>Voblint_CLI.Analyse_Dispatch\<close>'s own header already
  documents as an OCaml module-splitting limit, not fixable by regrouping ---
  only by folding the two together, exactly as done there for \<open>Sign\<close>/\<open>Interval\<close>.
\<close>

section \<open>The context-expanded entry-state graph\<close>

text \<open>
  Everything above renders one visual node per \<^typ>\<open>pp\<close> and shows
  \<^const>\<open>lookup_joined_state\<close> there. That join is lossy in exactly the way the
  entry-state analysis is precise: three activations of one callee collapse
  into one box, and a point dead in one activation and live in another reads
  as live.

  The expanded rendering draws one node per covered \<^term>\<open>(v, ctx)\<close> instead
  and annotates each through \<^const>\<open>lookup_context\<close>, so no join takes place at
  all. The generic contextual builder already carries every part of this:
  the node set is \<^const>\<open>contextual_result_domain\<close> over the same table, the
  routing hook is \<^const>\<open>entry_state_callee_ctx\<close>, and intra, enter, combine and
  call-to-return edges come from \<^const>\<open>build_analysis_graph\<close> unchanged.
\<close>

text \<open>
  The state source is \<^const>\<open>lookup_context\<close> at the node's own key, so the
  solution the builder is handed is already the result table, not the
  solver's map. \<^const>\<open>Inr\<close> is answered \<^const>\<open>Unreachable\<close>: the entry-state
  system carries every program variable in the local unknown, so its
  solver-global slots hold no program state to draw, and
  \<^const>\<open>contextual_result_domain\<close> contributes no \<^const>\<open>GlobalNode\<close> keys either.
\<close>

definition entry_state_ctx_sol ::
    "(ivl list, ivl abs_state) analysis_result
       \<Rightarrow> pp \<times> ivl list + gk \<Rightarrow> ivl abs_state point_state" where
  "entry_state_ctx_sol r k =
     (case k of Inl (v, ctx) \<Rightarrow> lookup_context r v ctx | Inr _ \<Rightarrow> Unreachable)"

text \<open>
  The routing hook ignores its call site and its caller context, matching
  \<^const>\<open>entry_state_route_gen\<close>, and takes the caller's own reachability case
  split before routing: an \<^const>\<open>Unreachable\<close> caller answers \<^const>\<open>None\<close>
  directly, so \<^const>\<open>analysis_enter_edges\<close> and \<^const>\<open>analysis_combine_edges\<close>
  draw no edge at all, and \<^const>\<open>entry_state_callee_ctx\<close> is never applied to a
  state that represents nothing. This is a structural absence, not a
  disguised sentinel context: an empty formal list is a legitimate context in
  its own right (a zero-formal callee's own entry is genuinely keyed at
  \<open>[]\<close>), so \<^const>\<open>None\<close> is the only value that can mean "no route" without
  risking collision with a real one.
\<close>

definition entry_state_ctx_route ::
    "imp_prog \<Rightarrow> pp \<Rightarrow> ivl list \<Rightarrow> call_action \<Rightarrow> ivl abs_state point_state \<Rightarrow> ivl list option" where
  "entry_state_ctx_route p u ctx ca d =
     (case d of Unreachable \<Rightarrow> None
      | Reachable st \<Rightarrow> entry_state_callee_ctx (declared_global p) ca st)"

definition entry_state_ctx_graph_config ::
    "imp_prog \<Rightarrow> (ivl list, gk, ivl abs_state point_state, ivl abs_state point_state)
       analysis_graph_config" where
  "entry_state_ctx_graph_config p =
    \<lparr> local_of = id,
      route = entry_state_ctx_route p,
      context_key = String.implode o (\<lambda>ctx. concat (map (\<lambda>x. string_of_ivl x @ '' '') ctx)),
      show_context = (\<lambda>ctx. concat (map (\<lambda>x. string_of_ivl x @ '' '') ctx)),
      locals_for_pp = (\<lambda>v.
        let sc = compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p)
                   prog_main_name (prog_main p) (prog_cfg prog_main_name p) v
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>v.
        scope_return_slot (compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p)
          prog_main_name (prog_main p) (prog_cfg prog_main_name p) v)),
      globals_to_show = [],
      show_local = (\<lambda>v ctx vars d.
        case d of Unreachable \<Rightarrow> [''unreachable'']
        | Reachable st \<Rightarrow> map (\<lambda>x. String.explode x @ ''='' @ string_of_ivl (st x)) vars),
      format_return = (\<lambda>v ctx ret d.
        case d of Unreachable \<Rightarrow> []
        | Reachable st \<Rightarrow>
            if st ret = ivl_top then [] else [''ret='' @ string_of_ivl (st ret)]),
      show_global = (\<lambda>k vars s. []),
      show_global_key = (\<lambda>k. ''Global''),
      is_shared_global = (\<lambda>k. False),
      show_internal_globals = False,
      owner_of = String.explode o
        compiled_owner_of (prog_table p) (prog_procs p) prog_main_name (prog_main p),
      cluster_label = (\<lambda>owner ctx.
        if ctx = [] then owner @ '' / root context''
        else owner @ '' / context='' @ concat (map (\<lambda>x. string_of_ivl x @ '' '') ctx)),
      source_text = Some (pretty_string_of_program (prog_table p) (prog_procs p) (prog_main p) []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

subsection \<open>Per-context check verdicts\<close>

text \<open>
  A check's verdict is per activation, so the annotation hook takes the
  context along with the point. Nothing classifies a second time:
  \<^const>\<open>classify_point\<close> against \<^const>\<open>lookup_context\<close> at that key is exactly the
  element \<^const>\<open>classify_checks_ctx\<close> would put in its own observation set for
  the same key, at the same \<^const>\<open>interval_classify_check\<close>, over the same
  table. Consulting the table directly keeps the annotation a lookup rather
  than a scan of a report built beside it.
\<close>

definition check_cond_at :: "cfg \<Rightarrow> pp \<Rightarrow> exp option" where
  "check_cond_at g v =
     map_option (\<lambda>(u, a, w). ea_check_cond a)
       (find (\<lambda>(u, a, w). u = v \<and> is_EA_Check a) (cfg_intra_list g))"

definition entry_state_ctx_check_annotation ::
    "cfg \<Rightarrow> (ivl list, ivl abs_state) analysis_result \<Rightarrow> pp \<Rightarrow> ivl list
       \<Rightarrow> graphviz_node_annotation option" where
  "entry_state_ctx_check_annotation g r v ctx =
     (case check_cond_at g v of
        None \<Rightarrow> None
      | Some cnd \<Rightarrow>
          Some (case classify_point interval_classify_check cnd (lookup_context r v ctx) of
                  Dead \<Rightarrow> dead_check_annotation cnd
                | Decided res \<Rightarrow> check_result_annotation res cnd))"

text \<open>
  One solve feeds the node set, every node's state, and every check verdict:
  \<open>r\<close> is bound once and reaches all three. The defining equation names
  \<^const>\<open>analyse_interval_entry_state_result\<close> repeatedly because that reads as
  the intended meaning; the \<open>[code]\<close> equation binds it, the same fix
  \<open>entry_state_full_state_dot_auto_code\<close> already applies one section up.
\<close>

definition entry_state_ctx_annotated_config ::
    "imp_prog \<Rightarrow> (ivl list, gk, ivl abs_state point_state, ivl abs_state point_state)
       analysis_graph_config" where
  "entry_state_ctx_annotated_config p =
     entry_state_ctx_graph_config p
       \<lparr> node_annotation :=
           entry_state_ctx_check_annotation (prog_cfg prog_main_name p)
             (analyse_interval_entry_state_result p) \<rparr>"

definition entry_state_ctx_graph :: "imp_prog \<Rightarrow> (ivl list, gk) analysis_graph" where
  "entry_state_ctx_graph p =
     build_analysis_graph (entry_state_ctx_annotated_config p) (prog_cfg prog_main_name p)
       (contextual_result_domain (entry_state_ctx_graph_config p) (prog_cfg prog_main_name p)
          (analyse_interval_entry_state_result p))
       (entry_state_ctx_sol (analyse_interval_entry_state_result p))"

declare entry_state_ctx_graph_def [code del]

lemma entry_state_ctx_graph_code [code]:
  "entry_state_ctx_graph p =
     (let r = analyse_interval_entry_state_result p;
          g = prog_cfg prog_main_name p;
          base = entry_state_ctx_graph_config p
      in build_analysis_graph (base \<lparr> node_annotation := entry_state_ctx_check_annotation g r \<rparr>)
           g (contextual_result_domain base g r) (entry_state_ctx_sol r))"
  unfolding entry_state_ctx_graph_def entry_state_ctx_annotated_config_def Let_def
  by (rule refl)

definition entry_state_ctx_dot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_ctx_dot_auto p =
     String.implode
       (analysis_graph_to_dot (entry_state_ctx_annotated_config p) (prog_cfg prog_main_name p)
          (entry_state_ctx_sol (analyse_interval_entry_state_result p))
          (entry_state_ctx_graph p))"

declare entry_state_ctx_dot_auto_def [code del]

text \<open>
  The graph is inlined here rather than left as a call to
  \<^const>\<open>entry_state_ctx_graph\<close>: that constant binds a solve of its own, so
  naming it under an already-bound \<open>r\<close> would solve the program twice, once for
  the rendering's own annotations and once inside the graph it renders.
\<close>

lemma entry_state_ctx_dot_auto_code [code]:
  "entry_state_ctx_dot_auto p =
     (let r = analyse_interval_entry_state_result p;
          g = prog_cfg prog_main_name p;
          base = entry_state_ctx_graph_config p;
          cfg = base \<lparr> node_annotation := entry_state_ctx_check_annotation g r \<rparr>;
          sol = entry_state_ctx_sol r
      in String.implode
           (analysis_graph_to_dot cfg g sol
              (build_analysis_graph cfg g (contextual_result_domain base g r) sol)))"
  unfolding entry_state_ctx_dot_auto_def entry_state_ctx_graph_def
            entry_state_ctx_annotated_config_def Let_def
  by (rule refl)

definition entry_state_ctx_graph_snapshot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_ctx_graph_snapshot_auto p =
     String.implode
       (analysis_graph_to_canonical_text (entry_state_ctx_annotated_config p) (prog_cfg prog_main_name p)
          (entry_state_ctx_sol (analyse_interval_entry_state_result p))
          (entry_state_ctx_graph p))"

declare entry_state_ctx_graph_snapshot_auto_def [code del]

lemma entry_state_ctx_graph_snapshot_auto_code [code]:
  "entry_state_ctx_graph_snapshot_auto p =
     (let r = analyse_interval_entry_state_result p;
          g = prog_cfg prog_main_name p;
          base = entry_state_ctx_graph_config p;
          cfg = base \<lparr> node_annotation := entry_state_ctx_check_annotation g r \<rparr>;
          sol = entry_state_ctx_sol r
      in String.implode
           (analysis_graph_to_canonical_text cfg g sol
              (build_analysis_graph cfg g (contextual_result_domain base g r) sol)))"
  unfolding entry_state_ctx_graph_snapshot_auto_def entry_state_ctx_graph_def
            entry_state_ctx_annotated_config_def Let_def
  by (rule refl)

section \<open>The context-expanded call-string graph\<close>

text \<open>
  The call-string counterpart of the entry-state section above, and the point at which the
  contextual renderer stops being per-domain. An entry-state context is the analysed
  domain's own value list (\<^typ>\<open>ivl list\<close>), so its graph configuration can only ever be
  written for one domain at a time. A call-string context is a \<^typ>\<open>cfg_node list\<close>
  (\<^theory>\<open>Voblint_Core.Call_String_Context\<close>) --- pure call history, no domain content ---
  and every rendered state here is projected into \<^typ>\<open>abstract_value\<close> exactly as
  \<^const>\<open>analyse_point_env_for\<close> already projects the monovariant tables. Both axes of
  domain-dependence are therefore removed, and Sign, Interval and Int share \<^emph>\<open>one\<close>
  configuration, one solution reader, and one annotation hook, selected by an ordinary
  \<^typ>\<open>analysis_domain\<close> argument rather than by three parallel renderers.
\<close>

text \<open>
  The solution reader: \<^const>\<open>lookup_context\<close> at the node's own \<^term>\<open>(v, ctx)\<close> key over
  that domain's own call-string result table, projected once into \<^typ>\<open>abstract_value\<close>.
  \<open>r\<close> is bound outside the returned \<open>\<lambda>\<close> for the same single-solve reason
  \<^const>\<open>analyse_point_env_for\<close> documents: a caller that partially applies this once
  solves the program once, however many nodes it then renders. \<^const>\<open>Inr\<close> is
  \<^const>\<open>Unreachable\<close> --- the routed call-string system carries every program variable in
  the local unknown, so its solver-global slots hold no program state to draw.
\<close>

definition cs_ctx_sol_for ::
    "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> pp \<times> call_string + call_string_gk \<Rightarrow> abstract_value abs_state point_state" where
  "cs_ctx_sol_for kind k p =
     (case kind of
        Sign_Analysis \<Rightarrow>
          (let r = analyse_sign_call_string_result k p
           in (\<lambda>x. case x of Inl (v, ctx) \<Rightarrow>
                     map_point_state (\<lambda>st. SignValue \<circ> st) (lookup_context r v ctx)
                   | Inr _ \<Rightarrow> Unreachable))
      | Interval_Analysis \<Rightarrow>
          (let r = analyse_interval_call_string_result k p
           in (\<lambda>x. case x of Inl (v, ctx) \<Rightarrow>
                     map_point_state (\<lambda>st. IntervalValue \<circ> st) (lookup_context r v ctx)
                   | Inr _ \<Rightarrow> Unreachable))
      | Int_Analysis \<Rightarrow>
          (let r = analyse_int_call_string_result k p
           in (\<lambda>x. case x of Inl (v, ctx) \<Rightarrow>
                     map_point_state (\<lambda>st. IntDomValue \<circ> st) (lookup_context r v ctx)
                   | Inr _ \<Rightarrow> Unreachable))
      | Parity_Analysis \<Rightarrow> (\<lambda>_. Unreachable))"

text \<open>
  The covered \<^term>\<open>(v, ctx)\<close> pairs, again read off whichever domain's table was selected.
  Coverage is the result's own extensional key set throughout ---
  \<^const>\<open>contextual_result_domain\<close> asks \<^const>\<open>contexts_at\<close>, never a traversal --- so a
  context the solver did not cover contributes no node, exactly as in the entry-state graph.
\<close>

definition cs_ctx_domain_for ::
    "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> (call_string, call_string_gk, abstract_value abs_state point_state,
            abstract_value abs_state point_state) analysis_graph_config
       \<Rightarrow> ((pp \<times> call_string) + call_string_gk) list" where
  "cs_ctx_domain_for kind k p base =
     (case kind of
        Sign_Analysis \<Rightarrow>
          contextual_result_domain base (prog_cfg prog_main_name p)
            (analyse_sign_call_string_result k p)
      | Interval_Analysis \<Rightarrow>
          contextual_result_domain base (prog_cfg prog_main_name p)
            (analyse_interval_call_string_result k p)
      | Int_Analysis \<Rightarrow>
          contextual_result_domain base (prog_cfg prog_main_name p)
            (analyse_int_call_string_result k p)
      | Parity_Analysis \<Rightarrow> [])"

text \<open>
  Per-context check verdicts. The classification stays each domain's own
  (\<^const>\<open>sign_classify_check\<close>, \<^const>\<open>interval_classify_check\<close>,
  \<^const>\<open>int_classify_check\<close> read their own \<open>abs_state\<close>, not the projected
  \<^typ>\<open>abstract_value\<close> one the renderer draws), so this hook dispatches while the graph
  structure above does not: nothing classifies a second time, and each branch is exactly the
  observation \<^const>\<open>classify_checks_ctx\<close> would record for the same key.
\<close>

definition cs_ctx_check_annotation ::
    "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog \<Rightarrow> cfg \<Rightarrow> pp \<Rightarrow> call_string
       \<Rightarrow> graphviz_node_annotation option" where
  "cs_ctx_check_annotation kind k p g v ctx =
     (case check_cond_at g v of
        None \<Rightarrow> None
      | Some cnd \<Rightarrow>
          Some (case (case kind of
                        Sign_Analysis \<Rightarrow>
                          classify_point sign_classify_check cnd
                            (lookup_context (analyse_sign_call_string_result k p) v ctx)
                      | Interval_Analysis \<Rightarrow>
                          classify_point interval_classify_check cnd
                            (lookup_context (analyse_interval_call_string_result k p) v ctx)
                      | Int_Analysis \<Rightarrow>
                          classify_point int_classify_check cnd
                            (lookup_context (analyse_int_call_string_result k p) v ctx)
                      | Parity_Analysis \<Rightarrow> Dead) of
                  Dead \<Rightarrow> dead_check_annotation cnd
                | Decided res \<Rightarrow> check_result_annotation res cnd))"

text \<open>
  The configuration itself: every context-specific field comes from
  \<^theory>\<open>Voblint_Analysis.Analysis_GraphViz\<close>'s own call-string presentation constants
  (\<^const>\<open>cs_graph_route\<close>, \<^const>\<open>cs_context_key\<close>, \<^const>\<open>cs_show_context\<close>,
  \<^const>\<open>cs_cluster_label\<close>), and every state-rendering field is the \<^typ>\<open>abstract_value\<close>
  reading shared with \<^const>\<open>point_state_node_annotation\<close>. Nothing here mentions a domain,
  so adding call-string rendering for a fourth domain would extend the two dispatch
  constants above and leave this configuration untouched.
\<close>

definition cs_ctx_graph_config ::
    "imp_prog \<Rightarrow> nat \<Rightarrow> (call_string, call_string_gk, abstract_value abs_state point_state,
        abstract_value abs_state point_state) analysis_graph_config" where
  "cs_ctx_graph_config p k =
    \<lparr> local_of = id,
      route = (\<lambda>u ctx ca d. cs_graph_route k u ctx ca d),
      context_key = cs_context_key,
      show_context = cs_show_context,
      locals_for_pp = (\<lambda>v.
        let sc = compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p)
                   prog_main_name (prog_main p) (prog_cfg prog_main_name p) v
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>v.
        scope_return_slot (compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p)
          prog_main_name (prog_main p) (prog_cfg prog_main_name p) v)),
      globals_to_show = [],
      show_local = (\<lambda>v ctx vars d.
        case d of Unreachable \<Rightarrow> [''unreachable'']
        | Reachable st \<Rightarrow> map (\<lambda>x. String.explode x @ ''='' @ string_of_abstract_value (st x)) vars),
      format_return = (\<lambda>v ctx ret d.
        case d of Unreachable \<Rightarrow> []
        | Reachable st \<Rightarrow>
            if is_top_abstract_value (st ret) then []
            else [''ret='' @ string_of_abstract_value (st ret)]),
      show_global = (\<lambda>x vars s. []),
      show_global_key = (\<lambda>x. ''Global''),
      is_shared_global = (\<lambda>x. False),
      show_internal_globals = False,
      owner_of = String.explode o
        compiled_owner_of (prog_table p) (prog_procs p) prog_main_name (prog_main p),
      cluster_label = cs_cluster_label,
      source_text = Some (pretty_string_of_program (prog_table p) (prog_procs p) (prog_main p) []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

definition cs_ctx_annotated_config ::
    "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> (call_string, call_string_gk, abstract_value abs_state point_state,
            abstract_value abs_state point_state) analysis_graph_config" where
  "cs_ctx_annotated_config kind k p =
     cs_ctx_graph_config p k
       \<lparr> node_annotation :=
           cs_ctx_check_annotation kind k p (prog_cfg prog_main_name p) \<rparr>"

definition cs_ctx_dot_auto :: "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "cs_ctx_dot_auto kind k p =
     (let g = prog_cfg prog_main_name p;
          base = cs_ctx_graph_config p k;
          cfg = cs_ctx_annotated_config kind k p;
          sol = cs_ctx_sol_for kind k p
      in String.implode
           (analysis_graph_to_dot cfg g sol
              (build_analysis_graph cfg g (cs_ctx_domain_for kind k p base) sol)))"

definition cs_ctx_graph_snapshot_auto :: "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "cs_ctx_graph_snapshot_auto kind k p =
     (let g = prog_cfg prog_main_name p;
          base = cs_ctx_graph_config p k;
          cfg = cs_ctx_annotated_config kind k p;
          sol = cs_ctx_sol_for kind k p
      in String.implode
           (analysis_graph_to_canonical_text cfg g sol
              (build_analysis_graph cfg g (cs_ctx_domain_for kind k p base) sol)))"

code_identifier
  code_module Complete_Lattices \<rightharpoonup> (OCaml) Core



end
