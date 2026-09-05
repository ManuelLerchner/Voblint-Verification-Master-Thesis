theory State_Report_GraphViz
  imports
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_Analysis.Int_Domain"
    Analyse_Dispatch
begin

text \<open>
  \<open>raw_cfg_dot\<close>'s \<open>node_annotation\<close> hook already renders a verdict-only
  \<^const>\<open>classify_checks\<close> report through \<^const>\<open>check_report_node_annotation\<close>.
  This is the same idea over \<open>analyse_with_state\<close>'s richer report: the
  rendered label gains one line per queried variable, printed through the
  same \<^const>\<open>to_string\<close> every \<^class>\<open>executable_domain\<close> instance already
  carries, so the DOT rendering shows a real solved state rather than a
  hand-built one.
\<close>

fun string_of_abstract_value :: "abstract_value \<Rightarrow> string" where
  "string_of_abstract_value (SignValue s) = to_string s"
| "string_of_abstract_value (IntervalValue i) = to_string i"
| "string_of_abstract_value (IntDomValue d) = to_string d"
| "string_of_abstract_value (ParityValue v) = to_string v"

text \<open>
  Used only to suppress an uninformative return-slot line: a \<^const>\<open>top\<close>
  return value says nothing the reader did not already know, and printing it at
  every node crowds out the variables that do carry information. Each domain's
  own \<^class>\<open>order_top\<close> instance decides, so no new instance is needed for a
  domain added to \<^type>\<open>abstract_value\<close>. Purely a presentation filter ---
  nothing downstream reads it, and a suppressed line is not a claim that the
  slot is unset.

  Reachability is not read here: \<^const>\<open>analyse_with_state\<close> carries its own
  unreachability flag, and the renderer reads that flag rather than probing a
  variable's value for \<^const>\<open>bot\<close>.
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

text \<open>
  Every renderer below needs the same thing from a solved table: the state at a point, as
  the uniform \<^typ>\<open>abstract_value\<close> view rather than the domain's own carrier. Stating that
  projection once means a dispatcher names a table and an injector and nothing else --- the
  \<^const>\<open>map_lift\<close>/\<^const>\<open>lookup_context\<close> pairing is not restated per domain, per
  solver, and per context mode.

  What cannot be factored out is the dispatch itself. \<^typ>\<open>analysis_domain\<close> is a runtime
  value, while the type of a solved table is static and different for each domain, so
  something has to enumerate the domains to get from one to the other. \<^typ>\<open>abstract_value\<close>
  is precisely the type that ends that enumeration: past this projection every renderer is
  domain-agnostic. The enumerations that remain are the boundary, not repetition.
\<close>

definition project_env ::
    "('a \<Rightarrow> abstract_value) \<Rightarrow> (unit, 'a abs_state) analysis_result
       \<Rightarrow> pp \<Rightarrow> abstract_value abs_state lifted" where
  "project_env into r v = map_lift (\<lambda>st. into \<circ> st) (lookup_context r v ())"

text \<open>
  The context-sensitive counterpart: \<^const>\<open>lookup_joined_state\<close> joins the contexts covering
  a point before projecting, so the reader is a per-node view with no context type left in
  it. Same projection, different reading of the table.
\<close>

definition project_joined_env ::
    "('a::semilattice_sup \<Rightarrow> abstract_value) \<Rightarrow> ('ctx, 'a abs_state) analysis_result
       \<Rightarrow> pp \<Rightarrow> abstract_value abs_state lifted" where
  "project_joined_env into r v =
     map_lift (\<lambda>st. into \<circ> st) (lookup_joined_state r v)"

definition program_vars :: "imp_prog \<Rightarrow> vname list" where
  "program_vars p =
     remdups (concat (map (scope_vnames_list p) (prog_main_name # prog_procs p)))"

definition state_line :: "(vname \<Rightarrow> abstract_value) \<Rightarrow> vname \<Rightarrow> string" where
  "state_line f x = String.explode x @ ''='' @ string_of_abstract_value (f x)"

text \<open>One point's state as the lines a document shows, unreachability included ---
  the same rendering a node label carries, so a state reads the same wherever it
  appears.\<close>

definition point_lines ::
    "vname list \<Rightarrow> abstract_value abs_state lifted \<Rightarrow> String.literal list" where
  "point_lines vars st =
     (case st of
        Bot \<Rightarrow> [STR ''unreachable'']
      | Lifted s \<Rightarrow> map (\<lambda>x. String.implode (state_line s x)) vars)"

definition state_report_node_annotation ::
    "vname list \<Rightarrow> (pp \<times> exp \<times> check_result \<times> (vname \<Rightarrow> abstract_value)) list
     \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "state_report_node_annotation vars report v =
     (case find (\<lambda>entry. fst entry = v) report of
        None \<Rightarrow> None
      | Some (_, cnd, res, f) \<Rightarrow>
          (case check_result_annotation res cnd of
             Node_Annotation lbl status \<Rightarrow>
               Some (Node_Annotation (join_gv_nl (lbl # map (state_line f) vars)) status)))"

text \<open>
  \<open>analyse_with_state\<close>'s report also carries an exact \<open>unreachable\<close> flag
  (\<^theory>\<open>Voblint_Analysis.Sign_Checks\<close>); this GraphViz rendering projects it
  away rather than threading it through \<^const>\<open>state_report_node_annotation\<close>,
  since the rendered label already shows the (necessarily witness-bottom)
  state at an unreachable point instead of suppressing the node the way the
  CLI's text report does.
\<close>

text \<open>
  \<open>report_vars\<close> and \<open>exp_vnames_list\<close> turn \<^const>\<open>exp_vnames\<close>'s set of
  variable occurrences into a sorted list, the same idiom
  \<^const>\<open>scope_vnames_list\<close> already uses over \<^typ>\<open>vname\<close> via
  \<^const>\<open>sorted_list_of_set\<close>. The CLI-facing renderers below take no
  caller-supplied variable list: each renders exactly the variables occurring
  in some check condition in the report, solving the program once rather than
  once per call.
\<close>

definition exp_vnames_list :: "exp \<Rightarrow> vname list" where
  "exp_vnames_list b = sorted_list_of_set (exp_vnames b)"

definition report_vars :: "('n \<times> exp \<times> 'r) list \<Rightarrow> vname list" where
  "report_vars report =
     sorted_list_of_set (\<Union> ((\<lambda>(_, c, _). exp_vnames c) ` set report))"

text \<open>
  Renders the check report through \<^const>\<open>raw_cfg_canonical_text_lit\<close>: a
  DOT-free, diff-stable representation of the solved analysis, which is what
  the regression fixtures compare against.
\<close>

definition state_report_graph_snapshot_auto :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "state_report_graph_snapshot_auto kind p =
     (let report = map (\<lambda>(u, c, r, _, s). (u, c, r, s)) (analyse_with_state_default kind p)
      in raw_cfg_canonical_text_lit (prog_table p) (prog_procs p)
           (state_report_node_annotation (report_vars report) report))"

text \<open>
  The codegen session collects this theory's rendering surface with the
  analysis facade from \<^theory>\<open>Voblint_CLI.Analyse_Dispatch\<close>. That narrower
  facade has no reachable rendering constant, and it precedes this theory in
  the import order, so the renderers belong in the later export declaration.
  The rendering surface uses the same AST constructors and numeral/char
  bridges, plus \<open>exp_vnames_list\<close> and \<open>string_of_abstract_value\<close> for CLI-side
  rendering.
\<close>

text \<open>
  \<^const>\<open>state_report_graph_snapshot_auto\<close> anchors every node label to a
  report entry (\<^const>\<open>state_report_node_annotation\<close> looks a point up in
  \<^const>\<open>analyse_with_state\<close>'s report, which \<^const>\<open>classify_checks_with_state\<close>
  only ever populates at check nodes), so every non-check node renders with no
  state at all. \<open>full_state_graph_snapshot_auto\<close> (defined below, once
  \<open>point_node_annotation\<close> is in scope) instead queries the solved
  \<^type>\<open>analysis_result\<close> table directly at \<^emph>\<open>every\<close> \<^typ>\<open>pp\<close>, so the
  annotation exists independently of whether that point happens to carry a
  check.
\<close>

text \<open>
  Entry-state siblings of \<open>state_report_graph_snapshot_auto\<close> /
  \<open>full_state_graph_snapshot_auto\<close>, Interval-only (so there is no
  \<open>analysis_domain\<close> parameter here). Both read
  \<^const>\<open>analyse_interval_entry_state_result\<close>, the canonical solved-result
  table, rather than the solver's own solution map. A \<^typ>\<open>pp\<close> may be covered
  by several entry-state contexts at once, and \<^const>\<open>lookup_joined_state\<close> is
  the table's own per-node view: it joins exactly the covered contexts, each
  read at its own key, through \<^typ>\<open>ivl\<close>'s \<^class>\<open>semilattice_sup\<close>.

  That join answers with a \<^typ>\<open>'a lifted\<close>, and both of its cases are
  rendered. A node the solver never covered and a node whose every covered
  context concretizes to nothing are alike \<^const>\<open>Bot\<close>: no execution
  arrives, so there is no store to print variable lines for. Printing the
  underlying \<^const>\<open>bot\<close> reading instead would draw an ordinary live node for
  code nothing reaches.
\<close>

definition entry_state_point_env_at ::
    "(ivl list, ivl abs_state) analysis_result
       \<Rightarrow> pp \<Rightarrow> abstract_value abs_state lifted" where
  "entry_state_point_env_at r v =
     map_lift (\<lambda>st. IntervalValue \<circ> st) (lookup_joined_state r v)"

text \<open>
  The domain-dispatching sibling, and the reason the collapsed entry-state renderings can
  be shared at all: \<^const>\<open>lookup_joined_state\<close> joins a point's covered contexts away, so
  what reaches the renderer is an ordinary per-node \<^typ>\<open>'a abs_state lifted\<close> with no
  context type left in it. Projecting that into \<^typ>\<open>abstract_value\<close> --- exactly as
  \<open>analyse_point_env_for\<close> already does for the monovariant tables --- removes the
  last domain-dependence, so Sign, Interval and Int share one renderer here.

  \<open>r\<close> is bound outside the returned \<open>\<lambda>\<close> for the usual single-solve reason: a caller that
  partially applies this once solves the program once, however many nodes it renders.
  \<^const>\<open>Parity_Analysis\<close> has no entry-state instance, so it answers
  \<^const>\<open>Bot\<close> --- unreachable in practice, since \<^const>\<open>resolve_analysis_config\<close>
  rejects that combination before any renderer is called.
\<close>

definition entry_state_point_env_for ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> abstract_value abs_state lifted" where
  "entry_state_point_env_for kind p =
     (case kind of
        Sign_Analysis \<Rightarrow>
          project_joined_env SignValue (analyse_sign_entry_state_result p)
      | Interval_Analysis \<Rightarrow>
          project_joined_env IntervalValue (analyse_interval_entry_state_result p)
      | Int_Analysis \<Rightarrow>
          project_joined_env IntDomValue (analyse_int_entry_state_result_warrow p)
      | Parity_Analysis \<Rightarrow> (\<lambda>_. Bot))"

text \<open>
  \<^const>\<open>NS_Unreachable\<close> is a distinct status, not a shade of the undecided one:
  ``nothing reaches this node'' and ``something reaches it and the abstraction could not
  decide'' are different findings, and \<^const>\<open>gv_style_of_status\<close> keeps them apart in
  every renderer at once.
\<close>

definition unreachable_state_annotation :: graphviz_node_annotation where
  "unreachable_state_annotation = Node_Annotation ''unreachable'' NS_Unreachable"

definition dead_check_annotation :: "exp \<Rightarrow> graphviz_node_annotation" where
  "dead_check_annotation cnd =
     Node_Annotation (''check '' @ string_of_exp 0 cnd @ '' [dead]'') NS_Unreachable"

text \<open>
  The shared full-state renderer for every \<^typ>\<open>'a lifted\<close>-valued
  monovariant or entry-state env: the same variable lines and the same
  default \<open>lightgreen\<close> styling at a \<^const>\<open>Lifted\<close> node, the shared
  \<^const>\<open>unreachable_state_annotation\<close> where there is no state to print. A
  point never gets its underlying \<^const>\<open>bot\<close> reading rendered as though it
  were an ordinary live state.
\<close>

definition point_node_annotation ::
    "vname list \<Rightarrow> (pp \<Rightarrow> abstract_value abs_state lifted)
       \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "point_node_annotation vars env v =
     (case env v of
        Bot \<Rightarrow> Some unreachable_state_annotation
      | Lifted st \<Rightarrow>
          Some (Node_Annotation (join_gv_nl (map (state_line st) vars)) NS_Plain))"

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
  caller does: \<^const>\<open>point_node_annotation\<close> reuses the same closure
  across every CFG node) solves the selected analysis exactly once,
  regardless of how many nodes it renders. A node the solver's key domain
  never covers and a node whose stored state is witness-bottom are alike
  \<^const>\<open>Bot\<close> at the \<^const>\<open>lookup_context\<close> boundary, the same
  distinction \<open>entry_state_point_env_at\<close> already reads for the entry-state
  graph -- so this is that same reading applied to the monovariant tables,
  not a second convention.
\<close>

definition analyse_point_env_for ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> pp \<Rightarrow> abstract_value abs_state lifted" where
  "analyse_point_env_for kind p =
     (case kind of
        Sign_Analysis \<Rightarrow> project_env SignValue (analyse_sign_result p)
      | Interval_Analysis \<Rightarrow> project_env IntervalValue (analyse_interval_td_result p)
      | Int_Analysis \<Rightarrow> project_env IntDomValue (analyse_int_result p)
      | Parity_Analysis \<Rightarrow> project_env ParityValue (analyse_parity_result p))"

text \<open>The whole-table counterpart of \<open>state_report_graph_snapshot_auto\<close>:
  the same DOT-free canonical text, over every point rather than check nodes
  only.\<close>

definition full_state_graph_snapshot_auto :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "full_state_graph_snapshot_auto kind p =
     raw_cfg_canonical_text_lit (prog_table p) (prog_procs p)
       (point_node_annotation (program_vars p) (analyse_point_env_for kind p))"

text \<open>
  The structured-export siblings. Same report, same annotation hook, same single solve per
  render as their DOT and snapshot counterparts above --- only the view of the built graph
  differs. These are what the CLI's own renderers consume: everything a DOT or HTML
  rendering needs is in the returned \<^typ>\<open>export_graph\<close>, so no renderer outside this
  session re-derives the graph or parses text back into one.
\<close>

definition state_report_export_auto :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> export_graph" where
  "state_report_export_auto kind p =
     (let report = map (\<lambda>(u, c, r, _, s). (u, c, r, s)) (analyse_with_state_default kind p)
      in raw_cfg_export (prog_table p) (prog_procs p)
           (state_report_node_annotation (report_vars report) report))"

definition full_state_export_auto :: "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> export_graph" where
  "full_state_export_auto kind p =
     raw_cfg_export (prog_table p) (prog_procs p)
       (point_node_annotation (program_vars p) (analyse_point_env_for kind p))"

text \<open>
  Neither existing annotation carries what a report browser needs at once.
  \<^const>\<open>point_node_annotation\<close> has a state at every point but no verdicts;
  \<^const>\<open>state_report_node_annotation\<close> has verdicts but only at check nodes, and nothing
  anywhere else. This one is their join: the state everywhere, and at a point that carries
  a check, that check's \<^typ>\<open>node_status\<close> in place of \<^const>\<open>NS_Plain\<close>, so a refuted check
  is visible in the graph without opening the node.

  Unreachability wins over a verdict, and deliberately: a check whose point nothing
  reaches has no finding to report, which is the same convention the CLI's text report
  follows when it suppresses those rows entirely.
\<close>

definition full_state_checked_node_annotation ::
    "vname list \<Rightarrow> (pp \<Rightarrow> abstract_value abs_state lifted)
       \<Rightarrow> (pp \<times> exp \<times> check_result) list \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "full_state_checked_node_annotation vars env verdicts v =
     (case env v of
        Bot \<Rightarrow> Some unreachable_state_annotation
      | Lifted st \<Rightarrow>
          (let lines = map (state_line st) vars
           in case find (\<lambda>entry. fst entry = v) verdicts of
                None \<Rightarrow> Some (Node_Annotation (join_gv_nl lines) NS_Plain)
              | Some (_, cnd, res) \<Rightarrow>
                  (case check_result_annotation res cnd of
                     Node_Annotation lbl status \<Rightarrow>
                       Some (Node_Annotation (join_gv_nl (lbl # lines)) status))))"

text \<open>
  One solve behind both views. A report browser needs a state at every point
  and a verdict at every check, and those are two readings of one solved
  table rather than two analyses: the state column and the verdict column
  can only disagree if they came from different solves.

  Taking the table as an argument is what makes that sharing survive code
  generation. A body naming \<^const>\<open>analyse_sign_result\<close> once for the states
  and once for the verdicts is two calls in the generated OCaml, hence two
  solves of the same equation system; one argument used twice is one call.

  \<open>bot_state\<close> is a parameter for the reason \<^locale>\<open>analysis_surface\<close> already
  takes it as one: at an abstract state --- a function type --- the class
  operation's code equation demands an executable \<^class>\<open>bot\<close> arity that a
  definition polymorphic in \<open>'a\<close> cannot supply.
\<close>

definition checked_payload_of ::
    "('a \<Rightarrow> abstract_value) \<Rightarrow> (exp \<Rightarrow> 'a abs_state \<Rightarrow> check_result) \<Rightarrow> 'a abs_state
       \<Rightarrow> (unit, 'a abs_state) analysis_result
       \<Rightarrow> (String.literal \<times> 'a abs_state lifted) list \<Rightarrow> imp_prog
       \<Rightarrow> export_graph \<times> (pp \<times> exp \<times> check_result \<times> bool \<times> abstract_value abs_state) list
            \<times> (String.literal \<times> String.literal list) list"
where
  "checked_payload_of into classify bot_state r globals p =
     (let full = classify_checks_with_state (prog_cfg p)
                   (\<lambda>v. case lookup_context r v () of
                          Bot \<Rightarrow> (True, bot_state)
                        | Lifted st \<Rightarrow> (False, st))
                   (\<lambda>c (_, s). classify c s)
      in (raw_cfg_export (prog_table p) (prog_procs p)
            (full_state_checked_node_annotation (program_vars p) (project_env into r)
               (map (\<lambda>(u, c, res, _, _). (u, c, res)) full)),
          map (\<lambda>(u, c, res, unr, st). (u, c, res, unr, into \<circ> st)) full,
          map (\<lambda>(k, st).
                 (k, point_lines (program_vars p)
                       (map_lift (\<lambda>s. into \<circ> s) st)))
              globals))"

text \<open>
  Dropping the two published columns leaves the plain check report. The
  state-carrying traversal reads \<^const>\<open>Bot\<close> into a flag beside the state
  and classifies from the state alone, so a verdict never depends on the extra
  column --- which is what lets a payload's verdicts be compared against the
  verdict-only dispatchers below rather than trusted to agree.
\<close>

lemma map_classify_checks_with_state_flagged:
  "map ((\<lambda>(u, c, res, _, _). (u, c, res)) \<circ> (\<lambda>(u, c, res, unr, st). (u, c, res, unr, h st)))
     (classify_checks_with_state g
        (\<lambda>v. case q v of Bot \<Rightarrow> (True, b) | Lifted st \<Rightarrow> (False, st))
        (\<lambda>c (_, s). classify c s))
   = classify_checks g (\<lambda>v. case q v of Bot \<Rightarrow> b | Lifted st \<Rightarrow> st) classify"
  by (simp add: classify_checks_with_state_def classify_checks_def comp_def case_prod_beta
      split: lifted.split)

text \<open>
  Each branch reads its domain's \<open>ctx_solved_for\<close> pair rather than the result table
  alone, so the states, the verdicts and the global unknowns all come from the one
  solve that pair performed.
\<close>

definition full_state_checked_payload_auto ::
    "analysis_domain \<Rightarrow> imp_prog
       \<Rightarrow> export_graph \<times> (pp \<times> exp \<times> check_result \<times> bool \<times> abstract_value abs_state) list
            \<times> (String.literal \<times> String.literal list) list"
where
  "full_state_checked_payload_auto kind p =
     (case kind of
        Sign_Analysis \<Rightarrow>
          (case analyse_sign_ctx_solved_for (declared_global p) p of
             (r, gvs) \<Rightarrow> checked_payload_of SignValue sign_classify_check bot r gvs p)
      | Interval_Analysis \<Rightarrow>
          (case analyse_interval_ctx_solved_warrow_for (declared_global p) p of
             (r, gvs) \<Rightarrow>
               checked_payload_of IntervalValue interval_classify_check bot r gvs p)
      | Int_Analysis \<Rightarrow>
          (case analyse_int_ctx_solved_warrow_for Refine_Fixpoint (declared_global p) p of
             (r, gvs) \<Rightarrow> checked_payload_of IntDomValue int_classify_check bot r gvs p)
      | Parity_Analysis \<Rightarrow>
          (case analyse_parity_ctx_solved_for (declared_global p) p of
             (r, gvs) \<Rightarrow> checked_payload_of ParityValue parity_classify_check bot r gvs p))"

text \<open>
  The report half is exactly \<^const>\<open>analyse_with_state\<close>'s answer, so sharing one
  solve with the graph changes what the browser is shown from, not what it shows:
  a reader's verdicts stay the CLI's verdicts, and no second classification
  convention enters through the rendering path.
\<close>

lemma snd_full_state_checked_payload_auto [simp]:
  "fst (snd (full_state_checked_payload_auto kind p)) = analyse_with_state_default kind p"
  by (cases kind)
     (simp_all add: full_state_checked_payload_auto_def checked_payload_of_def Let_def
        fst_analyse_sign_ctx_solved_for fst_analyse_parity_ctx_solved_for
        fst_analyse_interval_ctx_solved_warrow_for fst_analyse_int_ctx_solved_warrow_for
        case_prod_beta analyse_sign_result_for_def analyse_interval_td_result_for_def
        analyse_int_result_for_def analyse_parity_result_for_def
        analyse_sign_report_with_state_def analyse_sign_report_for_with_state_def
        analyse_sign_result_def
        analyse_interval_td_report_with_state_def analyse_interval_td_report_for_with_state_def
        analyse_interval_td_result_def
        analyse_int_report_with_state_def analyse_int_report_for_with_state_def
        analyse_int_result_def
        analyse_parity_report_with_state_def analyse_parity_report_for_with_state_def
        analyse_parity_result_def analyse_with_state_default.simps tag_states_def)

text \<open>
  One render is one solve. The \<open>[code]\<close> equations bind the result table once,
  outside the per-node annotation closure, so the whole graph is annotated
  from a single \<^const>\<open>entry_state_sol_prog\<close> run no matter how many nodes it
  has; the defining equations stay in the shape that reads as the intended
  meaning.
\<close>

definition entry_state_full_state_graph_snapshot_auto ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "entry_state_full_state_graph_snapshot_auto kind p =
     raw_cfg_canonical_text_lit (prog_table p) (prog_procs p)
       (point_node_annotation (program_vars p) (entry_state_point_env_for kind p))"

text \<open>
  \<open>entry_state_report_for_annotation\<close> pairs each domain's own source-level verdicts with
  the same table's per-node joined state. The verdict column is
  \<^typ>\<open>contextual_verdict\<close>, not \<^typ>\<open>check_result\<close>: a check every covering
  context finds unreachable stays \<^const>\<open>Dead\<close> all the way into the annotation,
  which has a case for it, so nothing is collapsed into \<^const>\<open>Check_Unknown\<close>
  on the way to the graph.
\<close>

text \<open>
  The verdict column, dispatched per domain: each domain's own entry-state contextual
  report, all three of which already share the \<^typ>\<open>contextual_verdict\<close> shape.
  \<^const>\<open>Parity_Analysis\<close> has no entry-state instance and answers the empty report;
  \<^const>\<open>resolve_analysis_config\<close> rejects that combination before any renderer runs.
\<close>

definition entry_state_verdicts_for ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "entry_state_verdicts_for kind p =
     (case kind of
        Sign_Analysis \<Rightarrow> analyse_sign_entry_state_report p
      | Interval_Analysis \<Rightarrow> analyse_interval_entry_state p
      | Int_Analysis \<Rightarrow> analyse_int_entry_state_report_warrow p
      | Parity_Analysis \<Rightarrow> [])"

subsection \<open>Global unknowns of a context-sensitive solve\<close>

text \<open>
  A seed's payload is readable off the local table, so this needs no second solve:
  \<open>routed_entry_seed_tree\<close> answers a callee entry's local from
  \<^term>\<open>locals (sigma (Inr (seed_key v ctx)))\<close>, which makes
  \<^term>\<open>lookup_context r (FunctionEntry f) ctx\<close> that seed rather than a summary of it.

  Contexts come from the table's own covered set, ordered by the same key the
  expanded graph clusters by --- \<^const>\<open>ordered_by_key\<close> needs an order on that key,
  not on the context type, which is what makes an \<^typ>\<open>ivl list\<close> enumerable at all.

  The shared slot is absent here, unlike the context-insensitive pane. Its value
  lives in \<^term>\<open>globs (sigma (Inr gk0))\<close> and no local table carries it, so listing
  it would mean inventing one; a route that publishes it needs the solve itself.
\<close>

definition ctx_key_of :: "('a \<Rightarrow> abstract_value) \<Rightarrow> 'a list \<Rightarrow> String.literal" where
  "ctx_key_of into ctx =
     String.implode (concat (map (\<lambda>x. string_of_abstract_value (into x) @ '' '') ctx))"

text \<open>The key orders the rows; this names them. \<^const>\<open>prog_main_name\<close>'s context is
  empty --- nothing calls it, so nothing seeds it --- and the expanded graph already
  calls that the root context, so a reader meets one spelling in both places.\<close>

definition ctx_show_of :: "('a \<Rightarrow> abstract_value) \<Rightarrow> 'a list \<Rightarrow> string" where
  "ctx_show_of into ctx =
     (case ctx of
        [] \<Rightarrow> ''root context''
      | x # xs \<Rightarrow>
          string_of_abstract_value (into x)
            @ concat (map (\<lambda>y. '', '' @ string_of_abstract_value (into y)) xs))"

definition ctx_seed_globals ::
    "('a::semilattice_sup \<Rightarrow> abstract_value) \<Rightarrow> ('c \<Rightarrow> String.literal) \<Rightarrow> ('c \<Rightarrow> string)
       \<Rightarrow> ('c, 'a abs_state) analysis_result \<Rightarrow> imp_prog
       \<Rightarrow> (String.literal \<times> String.literal list) list" where
  "ctx_seed_globals into ckey show_ctx r p =
     concat
       (map (\<lambda>f.
               map (\<lambda>c.
                      (STR ''enter '' + f + STR '' @ '' + String.implode (show_ctx c),
                       point_lines (program_vars p)
                         (map_lift (\<lambda>st. into \<circ> st)
                           (lookup_context r (FunctionEntry f) c))))
                   (ordered_by_key ckey (contexts_at r (FunctionEntry f))))
            (prog_main_name # prog_procs p))"

text \<open>A context-insensitive route has one context per entry, so its rows differ only
  by procedure and the context adds nothing to read.\<close>

definition unit_seed_globals ::
    "('a::semilattice_sup \<Rightarrow> abstract_value) \<Rightarrow> (unit, 'a abs_state) analysis_result
       \<Rightarrow> imp_prog \<Rightarrow> (String.literal \<times> String.literal list) list" where
  "unit_seed_globals into =
     ctx_seed_globals into (\<lambda>_. STR '''') (\<lambda>_. ''root context'')"

definition entry_state_globals_for ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> (String.literal \<times> String.literal list) list" where
  "entry_state_globals_for kind p =
     (case kind of
        Sign_Analysis \<Rightarrow>
          ctx_seed_globals SignValue (ctx_key_of SignValue) (ctx_show_of SignValue)
            (analyse_sign_entry_state_result p) p
      | Interval_Analysis \<Rightarrow>
          ctx_seed_globals IntervalValue (ctx_key_of IntervalValue)
            (ctx_show_of IntervalValue) (analyse_interval_entry_state_result p) p
      | Int_Analysis \<Rightarrow>
          ctx_seed_globals IntDomValue (ctx_key_of IntDomValue) (ctx_show_of IntDomValue)
            (analyse_int_entry_state_result_warrow p) p
      | Parity_Analysis \<Rightarrow> [])"

text \<open>
  The same reading for a route that solved at one context. An explicit solver choice
  and the call-string renderer both have a solved table and no combined producer, and a
  seed is in that table either way, so neither needs to solve again to publish one.
\<close>

definition solver_globals_for ::
    "analysis_domain \<Rightarrow> solver_choice \<Rightarrow> imp_prog
       \<Rightarrow> (String.literal \<times> String.literal list) list" where
  "solver_globals_for kind sc p =
     (case (kind, sc) of
        (Sign_Analysis, Solver_Join) \<Rightarrow> unit_seed_globals SignValue (analyse_sign_result p) p
      | (Sign_Analysis, Solver_PerOrigin) \<Rightarrow>
          unit_seed_globals SignValue (analyse_sign_result_per_origin p) p
      | (Sign_Analysis, _) \<Rightarrow> []
      | (Interval_Analysis, Solver_Join) \<Rightarrow>
          unit_seed_globals IntervalValue (analyse_interval_join_result p) p
      | (Interval_Analysis, Solver_PerOrigin) \<Rightarrow>
          unit_seed_globals IntervalValue (analyse_interval_per_origin_result p) p
      | (Interval_Analysis, Solver_Warrow) \<Rightarrow>
          unit_seed_globals IntervalValue (analyse_interval_td_result p) p
      | (Interval_Analysis, Solver_WarrowPerOrigin) \<Rightarrow>
          unit_seed_globals IntervalValue (analyse_interval_wpo_result p) p
      | (Int_Analysis, Solver_Join) \<Rightarrow>
          unit_seed_globals IntDomValue (analyse_int_join_result p) p
      | (Int_Analysis, Solver_PerOrigin) \<Rightarrow>
          unit_seed_globals IntDomValue (analyse_int_per_origin_result p) p
      | (Int_Analysis, Solver_Warrow) \<Rightarrow>
          unit_seed_globals IntDomValue (analyse_int_result p) p
      | (Int_Analysis, Solver_WarrowPerOrigin) \<Rightarrow>
          unit_seed_globals IntDomValue (analyse_int_wpo_result p) p
      | (Parity_Analysis, Solver_Join) \<Rightarrow>
          unit_seed_globals ParityValue (analyse_parity_result p) p
      | (Parity_Analysis, Solver_PerOrigin) \<Rightarrow>
          unit_seed_globals ParityValue (analyse_parity_result_per_origin p) p
      | (Parity_Analysis, _) \<Rightarrow> [])"

text \<open>
  The call-string reading, keyed and named by the same \<^const>\<open>cs_context_key\<close> and
  \<^const>\<open>cs_show_context\<close> the call-string graph clusters by, so one context has one
  spelling wherever it appears. Parity has no call-string table to read.
\<close>

definition cs_globals_for ::
    "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> (String.literal \<times> String.literal list) list" where
  "cs_globals_for kind k p =
     (case kind of
        Sign_Analysis \<Rightarrow>
          ctx_seed_globals SignValue cs_context_key cs_show_context
            (analyse_sign_call_string_result k p) p
      | Interval_Analysis \<Rightarrow>
          ctx_seed_globals IntervalValue cs_context_key cs_show_context
            (analyse_interval_call_string_result k p) p
      | Int_Analysis \<Rightarrow>
          ctx_seed_globals IntDomValue cs_context_key cs_show_context
            (analyse_int_call_string_result k p) p
      | Parity_Analysis \<Rightarrow> [])"

definition entry_state_report_for_annotation ::
    "analysis_domain \<Rightarrow> imp_prog
       \<Rightarrow> (pp \<times> exp \<times> contextual_verdict \<times> abstract_value abs_state lifted) list" where
  "entry_state_report_for_annotation kind p =
     (let env = entry_state_point_env_for kind p
      in map (\<lambda>(v, cnd, verdict). (v, cnd, verdict, env v))
           (entry_state_verdicts_for kind p))"

text \<open>
  The \<^typ>\<open>contextual_verdict\<close> sibling of \<^const>\<open>state_report_node_annotation\<close>.
  A decided check at a reachable node renders exactly as before, through
  \<^const>\<open>check_result_annotation\<close> plus the state lines. The remaining case is
  the dead check, and it is one case, not two: a verdict is \<^const>\<open>Dead\<close>
  exactly when every context covered at the node is \<^const>\<open>Bot\<close>, which
  is also exactly when the joined state is, so the two columns cannot
  disagree.
\<close>

definition verdict_state_report_node_annotation ::
    "vname list
       \<Rightarrow> (pp \<times> exp \<times> contextual_verdict \<times> abstract_value abs_state lifted) list
       \<Rightarrow> pp \<Rightarrow> graphviz_node_annotation option" where
  "verdict_state_report_node_annotation vars report v =
     (case find (\<lambda>entry. fst entry = v) report of
        None \<Rightarrow> None
      | Some (_, cnd, verdict, st) \<Rightarrow>
          Some (case (verdict, st) of
                  (Decided res, Lifted f) \<Rightarrow>
                    (case check_result_annotation res cnd of
                       Node_Annotation lbl status \<Rightarrow>
                         Node_Annotation (join_gv_nl (lbl # map (state_line f) vars)) status)
                | _ \<Rightarrow> dead_check_annotation cnd))"

definition entry_state_report_graph_snapshot_auto ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "entry_state_report_graph_snapshot_auto kind p =
     (let report = entry_state_report_for_annotation kind p
      in raw_cfg_canonical_text_lit (prog_table p) (prog_procs p)
           (verdict_state_report_node_annotation (report_vars report) report))"

definition entry_state_report_export_auto ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> export_graph" where
  "entry_state_report_export_auto kind p =
     (let report = entry_state_report_for_annotation kind p
      in raw_cfg_export (prog_table p) (prog_procs p)
           (verdict_state_report_node_annotation (report_vars report) report))"

definition entry_state_full_state_export_auto ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> export_graph" where
  "entry_state_full_state_export_auto kind p =
     raw_cfg_export (prog_table p) (prog_procs p)
       (point_node_annotation (program_vars p) (entry_state_point_env_for kind p))"

text \<open>
  The entry-state counterpart of \<^const>\<open>full_state_checked_payload_auto\<close>. Without it a
  context-sensitive report shows every state and no verdict, which is the one column a
  reader opens a check node for.

  \<^const>\<open>full_state_checked_node_annotation\<close> is reused unchanged by dropping the
  \<^const>\<open>Dead\<close> verdicts on the way in: a dead check's point is \<^const>\<open>Bot\<close> in the
  joined state as well, so the annotation reaches the same conclusion from the env alone.
  The two columns cannot disagree --- a verdict is \<^const>\<open>Dead\<close> exactly when every context
  covered at the node is unreachable, which is exactly when the join is.
\<close>

definition entry_state_checked_verdicts ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> (pp \<times> exp \<times> check_result) list" where
  "entry_state_checked_verdicts kind p =
     List.map_filter
       (\<lambda>(v, cnd, verdict).
          case verdict of Decided res \<Rightarrow> Some (v, cnd, res) | Dead \<Rightarrow> None)
       (entry_state_verdicts_for kind p)"

definition entry_state_full_state_checked_export_auto ::
    "analysis_domain \<Rightarrow> imp_prog \<Rightarrow> export_graph" where
  "entry_state_full_state_checked_export_auto kind p =
     raw_cfg_export (prog_table p) (prog_procs p)
       (full_state_checked_node_annotation (program_vars p)
          (entry_state_point_env_for kind p) (entry_state_checked_verdicts kind p))"

subsection \<open>Reporting an explicitly chosen solver\<close>

text \<open>
  \<^const>\<open>analyse_with_solver\<close> answers a \<^typ>\<open>check_report_entry list\<close>: it projects verdicts
  out of the solved table and drops the states. That is all a textual check report needs, and
  it is why a report browser had nothing to show for an explicit \<^typ>\<open>solver_choice\<close>.

  The states were never missing, only unpublished --- every one of those branches reads a
  solved \<^type>\<open>analysis_result\<close> of its own. What a reader sees is therefore what the verdicts
  were drawn from: \<^const>\<open>checked_payload_of\<close> reads the states and the verdicts off the one
  table the requested discipline solved, rather than resolving under a second rule.

  The \<^const>\<open>None\<close> cases are exactly \<^const>\<open>analyse_with_solver\<close>'s: a domain with no widen
  instance has no warrowing table to read, and \<^const>\<open>valid_analysis_config\<close> rejects those
  combinations before a renderer runs.

  Each \<^const>\<open>Some\<close> branch names the table of the corresponding
  \<^locale>\<open>analysis_surface\<close> interpretation, which is the same pairing of table with
  classifier that the domain's own check report goes through.
\<close>

definition solver_checked_payload_auto ::
    "analysis_domain \<Rightarrow> solver_choice \<Rightarrow> imp_prog
       \<Rightarrow> (export_graph \<times> (pp \<times> exp \<times> check_result \<times> bool \<times> abstract_value abs_state) list
            \<times> (String.literal \<times> String.literal list) list)
          option"
where
  "solver_checked_payload_auto kind sc p =
     (case (kind, sc) of
        (Sign_Analysis, Solver_Join) \<Rightarrow>
          Some (checked_payload_of SignValue sign_classify_check bot
                  (analyse_sign_result p) [] p)
      | (Sign_Analysis, Solver_PerOrigin) \<Rightarrow>
          Some (checked_payload_of SignValue sign_classify_check bot
                  (analyse_sign_result_per_origin p) [] p)
      | (Sign_Analysis, _) \<Rightarrow> None
      | (Interval_Analysis, Solver_Join) \<Rightarrow>
          Some (checked_payload_of IntervalValue interval_classify_check bot
                  (analyse_interval_join_result p) [] p)
      | (Interval_Analysis, Solver_PerOrigin) \<Rightarrow>
          Some (checked_payload_of IntervalValue interval_classify_check bot
                  (analyse_interval_per_origin_result p) [] p)
      | (Interval_Analysis, Solver_Warrow) \<Rightarrow>
          Some (checked_payload_of IntervalValue interval_classify_check bot
                  (analyse_interval_td_result p) [] p)
      | (Interval_Analysis, Solver_WarrowPerOrigin) \<Rightarrow>
          Some (checked_payload_of IntervalValue interval_classify_check bot
                  (analyse_interval_wpo_result p) [] p)
      | (Int_Analysis, Solver_Join) \<Rightarrow>
          Some (checked_payload_of IntDomValue int_classify_check bot
                  (analyse_int_join_result p) [] p)
      | (Int_Analysis, Solver_PerOrigin) \<Rightarrow>
          Some (checked_payload_of IntDomValue int_classify_check bot
                  (analyse_int_per_origin_result p) [] p)
      | (Int_Analysis, Solver_Warrow) \<Rightarrow>
          Some (checked_payload_of IntDomValue int_classify_check bot
                  (analyse_int_result p) [] p)
      | (Int_Analysis, Solver_WarrowPerOrigin) \<Rightarrow>
          Some (checked_payload_of IntDomValue int_classify_check bot
                  (analyse_int_wpo_result p) [] p)
      | (Parity_Analysis, Solver_Join) \<Rightarrow>
          Some (checked_payload_of ParityValue parity_classify_check bot
                  (analyse_parity_result p) [] p)
      | (Parity_Analysis, Solver_PerOrigin) \<Rightarrow>
          Some (checked_payload_of ParityValue parity_classify_check bot
                  (analyse_parity_result_per_origin p) [] p)
      | (Parity_Analysis, _) \<Rightarrow> None)"

text \<open>
  Every branch's verdict column is the one \<^const>\<open>analyse_with_solver\<close> already
  answers with, and the \<^const>\<open>None\<close> branches coincide. Fourteen tables are named
  here by hand, so the risk this rules out is concrete: a branch reading a
  neighbouring discipline's table would still typecheck, still render, and
  disagree with the text report only where the two disciplines happen to differ.
\<close>

lemma solver_checked_payload_verdicts:
  "map_option (map (\<lambda>(u, c, res, _, _). (u, c, res)) \<circ> fst \<circ> snd)
     (solver_checked_payload_auto kind sc p)
   = analyse_with_solver kind sc p"
  by (cases kind; cases sc)
     (simp_all add: solver_checked_payload_auto_def checked_payload_of_def Let_def
        map_classify_checks_with_state_flagged surface_unfold
        analyse_sign_report_def analyse_sign_report_for_def
        analyse_sign_report_per_origin_def
        analyse_sign_result_def analyse_sign_result_per_origin_def
        analyse_interval_report_def analyse_interval_report_for_def
        analyse_interval_report_per_origin_def analyse_interval_report_per_origin_for_def
        analyse_interval_td_report_def analyse_interval_td_report_for_def
        analyse_interval_report_wpo_def analyse_interval_report_wpo_for_def
        analyse_interval_join_result_def analyse_interval_per_origin_result_def
        analyse_interval_td_result_def analyse_interval_wpo_result_def
        analyse_int_report_join_def analyse_int_report_join_for_def
        analyse_int_report_per_origin_def analyse_int_report_per_origin_for_def
        analyse_int_report_def analyse_int_report_for_def
        analyse_int_report_wpo_def analyse_int_report_wpo_for_def
        analyse_int_join_result_def analyse_int_per_origin_result_def
        analyse_int_result_def analyse_int_result_for_def analyse_int_wpo_result_def
        analyse_parity_report_def analyse_parity_report_for_def
        analyse_parity_report_per_origin_def analyse_parity_report_per_origin_for_def
        analyse_parity_result_def analyse_parity_result_per_origin_def)

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
  solver's map. \<^const>\<open>Inr\<close> is answered \<^const>\<open>Bot\<close>: the entry-state
  system carries every program variable in the local unknown, so its
  solver-global slots hold no program state to draw, and
  \<^const>\<open>contextual_result_domain\<close> contributes no \<^const>\<open>GlobalNode\<close> keys either.
\<close>

definition entry_state_ctx_sol ::
    "(ivl list, ivl abs_state) analysis_result
       \<Rightarrow> pp \<times> ivl list + (unit, ivl list) routed_gk \<Rightarrow> ivl abs_state lifted" where
  "entry_state_ctx_sol r k =
     (case k of Inl (v, ctx) \<Rightarrow> lookup_context r v ctx | Inr _ \<Rightarrow> Bot)"

text \<open>
  The routing hook ignores its call site and its caller context, matching
  \<^const>\<open>entry_state_route_gen\<close>, and takes the caller's own reachability case
  split before routing: an \<^const>\<open>Bot\<close> caller answers \<^const>\<open>None\<close>
  directly, so \<^const>\<open>analysis_enter_edges\<close> and \<^const>\<open>analysis_combine_edges\<close>
  draw no edge at all, and \<^const>\<open>entry_state_callee_ctx\<close> is never applied to a
  state that represents nothing. This is a structural absence, not a
  disguised sentinel context: an empty formal list is a legitimate context in
  its own right (a zero-formal callee's own entry is genuinely keyed at
  \<open>[]\<close>), so \<^const>\<open>None\<close> is the only value that can mean "no route" without
  risking collision with a real one.
\<close>

definition entry_state_ctx_route ::
    "imp_prog \<Rightarrow> pp \<Rightarrow> ivl list \<Rightarrow> call_action \<Rightarrow> ivl abs_state lifted \<Rightarrow> ivl list option" where
  "entry_state_ctx_route p u ctx ca d =
     (case d of Bot \<Rightarrow> None
      | Lifted st \<Rightarrow> entry_state_callee_ctx (declared_global p) ca st)"

definition entry_state_ctx_graph_config ::
    "imp_prog \<Rightarrow> (ivl list, (unit, ivl list) routed_gk, ivl abs_state lifted, ivl abs_state lifted)
       analysis_graph_config" where
  "entry_state_ctx_graph_config p =
    \<lparr> local_of = id,
      route = entry_state_ctx_route p,
      context_key = String.implode o (\<lambda>ctx. concat (map (\<lambda>x. string_of_ivl x @ '' '') ctx)),
      show_context = (\<lambda>ctx. concat (map (\<lambda>x. string_of_ivl x @ '' '') ctx)),
      locals_for_pp = (\<lambda>v.
        let sc = compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p) (prog_cfg p) v
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>v.
        scope_return_slot (compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p) (prog_cfg p) v)),
      globals_to_show = [],
      show_local = (\<lambda>v ctx vars d.
        case d of Bot \<Rightarrow> [''unreachable'']
        | Lifted st \<Rightarrow> map (\<lambda>x. String.explode x @ ''='' @ string_of_ivl (st x)) vars),
      format_return = (\<lambda>v ctx ret d.
        case d of Bot \<Rightarrow> []
        | Lifted st \<Rightarrow>
            if st ret = ivl_top then [] else [''ret='' @ string_of_ivl (st ret)]),
      show_global = (\<lambda>k vars s. []),
      show_global_key = (\<lambda>k. ''Global''),
      is_shared_global = (\<lambda>k. False),
      show_internal_globals = False,
      owner_of = String.explode o
        compiled_owner_of (prog_table p) (prog_procs p),
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
  the intended meaning; the \<open>[code]\<close> equation binds it once so the generated
  code solves once, the same shape the entry-state renderers one section up
  already use.
\<close>

definition entry_state_ctx_annotated_config ::
    "imp_prog \<Rightarrow> (ivl list, (unit, ivl list) routed_gk, ivl abs_state lifted, ivl abs_state lifted)
       analysis_graph_config" where
  "entry_state_ctx_annotated_config p =
     entry_state_ctx_graph_config p
       \<lparr> node_annotation :=
           entry_state_ctx_check_annotation (prog_cfg p)
             (analyse_interval_entry_state_result p) \<rparr>"

definition entry_state_ctx_graph :: "imp_prog \<Rightarrow> (ivl list, (unit, ivl list) routed_gk) analysis_graph" where
  "entry_state_ctx_graph p =
     build_analysis_graph (entry_state_ctx_annotated_config p) (prog_cfg p)
       (contextual_result_domain (entry_state_ctx_graph_config p) (prog_cfg p)
          (analyse_interval_entry_state_result p))
       (entry_state_ctx_sol (analyse_interval_entry_state_result p))"

text \<open>The rendered graph is well-formed for every program: it is built over a compiled
  CFG, whose call sites are unique and whose edge relations are finite, which is all
  \<open>build_analysis_graph_wf\<close> asks for.\<close>

lemma entry_state_ctx_graph_wf: "analysis_graph_wf (entry_state_ctx_graph p)"
  unfolding entry_state_ctx_graph_def prog_cfg_def
  by (rule build_analysis_graph_wf
        [OF calls_source_unique_compile_prog compile_prog_finite[THEN conjunct2]])

declare entry_state_ctx_graph_def [code del]

lemma entry_state_ctx_graph_code [code]:
  "entry_state_ctx_graph p =
     (let r = analyse_interval_entry_state_result p;
          g = prog_cfg p;
          base = entry_state_ctx_graph_config p
      in build_analysis_graph (base \<lparr> node_annotation := entry_state_ctx_check_annotation g r \<rparr>)
           g (contextual_result_domain base g r) (entry_state_ctx_sol r))"
  unfolding entry_state_ctx_graph_def entry_state_ctx_annotated_config_def Let_def
  by (rule refl)

text \<open>
  The graph is inlined in each \<open>[code]\<close> equation below rather than left as a call to
  \<^const>\<open>entry_state_ctx_graph\<close>: that constant binds a solve of its own, so naming it
  under an already-bound \<open>r\<close> would solve the program twice, once for the rendering's own
  annotations and once inside the graph it renders.
\<close>

definition entry_state_ctx_graph_snapshot_auto :: "imp_prog \<Rightarrow> String.literal" where
  "entry_state_ctx_graph_snapshot_auto p =
     String.implode
       (analysis_graph_to_canonical_text (entry_state_ctx_annotated_config p) (prog_cfg p)
          (entry_state_ctx_sol (analyse_interval_entry_state_result p))
          (entry_state_ctx_graph p))"

declare entry_state_ctx_graph_snapshot_auto_def [code del]

lemma entry_state_ctx_graph_snapshot_auto_code [code]:
  "entry_state_ctx_graph_snapshot_auto p =
     (let r = analyse_interval_entry_state_result p;
          g = prog_cfg p;
          base = entry_state_ctx_graph_config p;
          cfg = base \<lparr> node_annotation := entry_state_ctx_check_annotation g r \<rparr>;
          sol = entry_state_ctx_sol r
      in String.implode
           (analysis_graph_to_canonical_text cfg g sol
              (build_analysis_graph cfg g (contextual_result_domain base g r) sol)))"
  unfolding entry_state_ctx_graph_snapshot_auto_def entry_state_ctx_graph_def
            entry_state_ctx_annotated_config_def Let_def
  by (rule refl)

definition entry_state_ctx_export_auto :: "imp_prog \<Rightarrow> export_graph" where
  "entry_state_ctx_export_auto p =
     analysis_graph_to_export (entry_state_ctx_annotated_config p) (prog_cfg p)
       (entry_state_ctx_sol (analyse_interval_entry_state_result p))
       (entry_state_ctx_graph p)"

declare entry_state_ctx_export_auto_def [code del]

lemma entry_state_ctx_export_auto_code [code]:
  "entry_state_ctx_export_auto p =
     (let r = analyse_interval_entry_state_result p;
          g = prog_cfg p;
          base = entry_state_ctx_graph_config p;
          cfg = base \<lparr> node_annotation := entry_state_ctx_check_annotation g r \<rparr>;
          sol = entry_state_ctx_sol r
      in analysis_graph_to_export cfg g sol
           (build_analysis_graph cfg g (contextual_result_domain base g r) sol))"
  unfolding entry_state_ctx_export_auto_def entry_state_ctx_graph_def
            entry_state_ctx_annotated_config_def Let_def
  by (rule refl)

section \<open>The context-expanded call-string graph\<close>

text \<open>
  The call-string counterpart of the entry-state section above, and the point at which the
  contextual renderer stops being per-domain. An entry-state context is the analysed
  domain's own value list (\<^typ>\<open>ivl list\<close>), so its graph configuration can only ever be
  written for one domain at a time. A call-string context is a \<^typ>\<open>cfg_node list\<close>
  (\<^theory>\<open>Voblint_Framework.Call_String_Context\<close>) --- pure call history, no domain content ---
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
  \<^const>\<open>Bot\<close> --- the routed call-string system carries every program variable in
  the local unknown, so its solver-global slots hold no program state to draw.
\<close>

definition cs_ctx_sol_for ::
    "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> pp \<times> call_string + call_string_gk \<Rightarrow> abstract_value abs_state lifted" where
  "cs_ctx_sol_for kind k p =
     (case kind of
        Sign_Analysis \<Rightarrow>
          (let r = analyse_sign_call_string_result k p
           in (\<lambda>x. case x of Inl (v, ctx) \<Rightarrow>
                     map_lift (\<lambda>st. SignValue \<circ> st) (lookup_context r v ctx)
                   | Inr _ \<Rightarrow> Bot))
      | Interval_Analysis \<Rightarrow>
          (let r = analyse_interval_call_string_result k p
           in (\<lambda>x. case x of Inl (v, ctx) \<Rightarrow>
                     map_lift (\<lambda>st. IntervalValue \<circ> st) (lookup_context r v ctx)
                   | Inr _ \<Rightarrow> Bot))
      | Int_Analysis \<Rightarrow>
          (let r = analyse_int_call_string_result k p
           in (\<lambda>x. case x of Inl (v, ctx) \<Rightarrow>
                     map_lift (\<lambda>st. IntDomValue \<circ> st) (lookup_context r v ctx)
                   | Inr _ \<Rightarrow> Bot))
      | Parity_Analysis \<Rightarrow> (\<lambda>_. Bot))"

text \<open>
  The covered \<^term>\<open>(v, ctx)\<close> pairs, again read off whichever domain's table was selected.
  Coverage is the result's own extensional key set throughout ---
  \<^const>\<open>contextual_result_domain\<close> asks \<^const>\<open>contexts_at\<close>, never a traversal --- so a
  context the solver did not cover contributes no node, exactly as in the entry-state graph.
\<close>

definition cs_ctx_domain_for ::
    "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> (call_string, call_string_gk, abstract_value abs_state lifted,
            abstract_value abs_state lifted) analysis_graph_config
       \<Rightarrow> ((pp \<times> call_string) + call_string_gk) list" where
  "cs_ctx_domain_for kind k p base =
     (case kind of
        Sign_Analysis \<Rightarrow>
          contextual_result_domain base (prog_cfg p)
            (analyse_sign_call_string_result k p)
      | Interval_Analysis \<Rightarrow>
          contextual_result_domain base (prog_cfg p)
            (analyse_interval_call_string_result k p)
      | Int_Analysis \<Rightarrow>
          contextual_result_domain base (prog_cfg p)
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
  reading shared with \<^const>\<open>point_node_annotation\<close>. Nothing here mentions a domain,
  so adding call-string rendering for a fourth domain would extend the two dispatch
  constants above and leave this configuration untouched.
\<close>

definition cs_ctx_graph_config ::
    "imp_prog \<Rightarrow> nat \<Rightarrow> (call_string, call_string_gk, abstract_value abs_state lifted,
        abstract_value abs_state lifted) analysis_graph_config" where
  "cs_ctx_graph_config p k =
    \<lparr> local_of = id,
      route = (\<lambda>u ctx ca d. cs_graph_route k u ctx ca d),
      context_key = cs_context_key,
      show_context = cs_show_context,
      locals_for_pp = (\<lambda>v.
        let sc = compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p) (prog_cfg p) v
        in scope_formals sc @ scope_locals sc),
      return_slot_for_pp = (\<lambda>v.
        scope_return_slot (compiled_procedure_scope (declared_global p) (prog_table p) (prog_procs p) (prog_cfg p) v)),
      globals_to_show = [],
      show_local = (\<lambda>v ctx vars d.
        case d of Bot \<Rightarrow> [''unreachable'']
        | Lifted st \<Rightarrow> map (\<lambda>x. String.explode x @ ''='' @ string_of_abstract_value (st x)) vars),
      format_return = (\<lambda>v ctx ret d.
        case d of Bot \<Rightarrow> []
        | Lifted st \<Rightarrow>
            if is_top_abstract_value (st ret) then []
            else [''ret='' @ string_of_abstract_value (st ret)]),
      show_global = (\<lambda>x vars s. []),
      show_global_key = (\<lambda>x. ''Global''),
      is_shared_global = (\<lambda>x. False),
      show_internal_globals = False,
      owner_of = String.explode o
        compiled_owner_of (prog_table p) (prog_procs p),
      cluster_label = cs_cluster_label,
      source_text = Some (pretty_string_of_program (prog_table p) (prog_procs p) (prog_main p) []),
      node_annotation = (\<lambda>_ _. None)
    \<rparr>"

definition cs_ctx_annotated_config ::
    "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog
       \<Rightarrow> (call_string, call_string_gk, abstract_value abs_state lifted,
            abstract_value abs_state lifted) analysis_graph_config" where
  "cs_ctx_annotated_config kind k p =
     cs_ctx_graph_config p k
       \<lparr> node_annotation :=
           cs_ctx_check_annotation kind k p (prog_cfg p) \<rparr>"

definition cs_ctx_export_auto :: "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog \<Rightarrow> export_graph" where
  "cs_ctx_export_auto kind k p =
     (let g = prog_cfg p;
          base = cs_ctx_graph_config p k;
          cfg = cs_ctx_annotated_config kind k p;
          sol = cs_ctx_sol_for kind k p
      in analysis_graph_to_export cfg g sol
           (build_analysis_graph cfg g (cs_ctx_domain_for kind k p base) sol))"

definition cs_ctx_graph_snapshot_auto :: "analysis_domain \<Rightarrow> nat \<Rightarrow> imp_prog \<Rightarrow> String.literal" where
  "cs_ctx_graph_snapshot_auto kind k p =
     (let g = prog_cfg p;
          base = cs_ctx_graph_config p k;
          cfg = cs_ctx_annotated_config kind k p;
          sol = cs_ctx_sol_for kind k p
      in String.implode
           (analysis_graph_to_canonical_text cfg g sol
              (build_analysis_graph cfg g (cs_ctx_domain_for kind k p base) sol)))"

code_identifier
  code_module Complete_Lattices \<rightharpoonup> (OCaml) Core



end
