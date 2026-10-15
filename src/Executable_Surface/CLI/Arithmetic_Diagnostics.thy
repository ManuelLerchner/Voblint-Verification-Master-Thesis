theory Arithmetic_Diagnostics
  imports "Voblint_Framework.Contextual_Check_Report"
begin

section \<open>Arithmetic obligations\<close>

text \<open>Diagnostics inspect all expression operands, matching VIMP's total,
  pure expression model. They neither change execution nor assume short-circuit
  evaluation for logical operators. Lists retain repeated syntactically equal occurrences.\<close>

text \<open>
  An obligation names an operation, the hazard it may run into and the operand the
  hazard concerns. A division or remainder must not divide by zero; its operand is the
  divisor. A signed arithmetic operation must compute a result its kind represents,
  as C requires (ISO/IEC 9899 6.5p5); its operand is the operation itself. A conversion
  must convert a value the target kind represents, the categories Goblint separates as
  arithmetic and cast overflow (\<^verbatim>\<open>Checks.Category\<close> at \<open>0dc12d355\<close>); its operand is
  the converted expression. Which hazards a language raises, and when one is safe, is
  the language's; the report treats them alike.
\<close>

datatype arithmetic_hazard = Division_By_Zero | Signed_Overflow | Conversion_Overflow

datatype 'e arithmetic_obligation = Arithmetic_Obligation
  (arithmetic_hazard: arithmetic_hazard)
  (arithmetic_operation: 'e)
  (arithmetic_operand: 'e)

section \<open>Sites and their solved classifications\<close>

text \<open>
  \<open>arithmetic_expression_sites\<close> collects the expressions each CFG edge and call
  evaluates; \<open>obligation_sites\<close> turns them into the obligations the solved table then
  classifies, given how an expression of the language yields them.
\<close>

text \<open>Only suppress a negative guard edge when the same point has a matching
  positive guard edge. All other expression-bearing edges remain in the report.\<close>

definition arithmetic_expression_sites ::
    "('v::linorder, 'e::linorder) gcfg \<Rightarrow> (pp \<times> 'e list) list" where
  "arithmetic_expression_sites g =
     (let edges = cfg_intra_list g
      in map (\<lambda>(u, a, v). (u, edge_expressions a))
           (filter (\<lambda>(u, a, v). case a of EA_AssumeNot e \<Rightarrow>
             \<not> list_ex (\<lambda>(u', a', v'). u = u' \<and> a' = EA_Assume e) edges
             | _ \<Rightarrow> True) edges)) @
       map (\<lambda>(u, ca, ce, k). (u, ce_args ca)) (cfg_calls_list g)"

definition obligation_sites ::
    "('e \<Rightarrow> 'e arithmetic_obligation list) \<Rightarrow> ('v::linorder, 'e::linorder) gcfg
       \<Rightarrow> (pp \<times> 'e arithmetic_obligation list) list" where
  "obligation_sites obls g =
     map (\<lambda>(v, es). (v, concat (map obls es))) (arithmetic_expression_sites g)"

text \<open>A diagnostic names an obligation of a site list, read through a classifier of
  obligations. The site list and the classifier depend on the expression language and
  the analysis; the classification does not.\<close>

datatype 'e arithmetic_diagnostic = Arithmetic_Diagnostic
  (diagnostic_point: pp)
  (diagnostic_occurrence: nat)
  (diagnostic_obligation: "'e arithmetic_obligation")
  (diagnostic_verdict: check_result)

fun arithmetic_diagnostic_of ::
    "pp \<Rightarrow> nat \<Rightarrow> 'e arithmetic_obligation \<Rightarrow> contextual_verdict
       \<Rightarrow> 'e arithmetic_diagnostic list" where
  "arithmetic_diagnostic_of v i obligation (Lifted Check_Refuted) =
     [Arithmetic_Diagnostic v i obligation Check_Refuted]"
| "arithmetic_diagnostic_of v i obligation (Lifted Check_Unknown) =
     [Arithmetic_Diagnostic v i obligation Check_Unknown]"
| "arithmetic_diagnostic_of v i obligation _ = []"

definition arithmetic_diagnostics ::
    "(pp \<times> 'e arithmetic_obligation list) list \<Rightarrow> ('ctx, 'a) solved_table
       \<Rightarrow> ('e arithmetic_obligation \<Rightarrow> 'a \<Rightarrow> check_result)
       \<Rightarrow> 'e arithmetic_diagnostic list" where
  "arithmetic_diagnostics sites r classify =
     concat (map (\<lambda>(v, obligations).
       concat (map (\<lambda>(i, obligation).
         arithmetic_diagnostic_of v i obligation (point_verdict r classify v obligation))
         (zip [0..<length obligations] obligations))) sites)"

lemma arithmetic_expression_sites_intra:
  assumes "finite (intra g)" and "(v, a, w) \<in> intra g"
  shows "(v, edge_expressions a) \<in> set (arithmetic_expression_sites g)"
proof -
  let ?edges = "cfg_intra_list g"
  have mem: "(v, a, w) \<in> set ?edges" using assms by simp
  have kept: "\<And>b t. (v, b, t) \<in> set ?edges \<Longrightarrow>
      (case b of EA_AssumeNot e \<Rightarrow>
        \<not> list_ex (\<lambda>(u', a', v'). v = u' \<and> a' = EA_Assume e) ?edges
        | _ \<Rightarrow> True) \<Longrightarrow>
      (v, edge_expressions b) \<in> set (arithmetic_expression_sites g)"
    unfolding arithmetic_expression_sites_def
    by (force simp: Let_def image_iff)
  show ?thesis
  proof (cases "\<exists>e. a = EA_AssumeNot e")
    case False
    with mem show ?thesis by (intro kept[of a w]) (auto split: gedge_action.splits)
  next
    case True
    then obtain e where a: "a = EA_AssumeNot e" by blast
    show ?thesis
    proof (cases "list_ex (\<lambda>(u', a', v'). v = u' \<and> a' = EA_Assume e) ?edges")
      case False
      from kept[OF mem] False a show ?thesis by simp
    next
      case True
      then obtain t where pos: "(v, EA_Assume e, t) \<in> set ?edges"
        by (auto simp: list_ex_iff)
      from kept[OF pos] a show ?thesis by simp
    qed
  qed
qed

lemma arithmetic_expression_sites_call:
  assumes "finite (calls g)" and "(v, ca, ce, k) \<in> calls g"
  shows "(v, ce_args ca) \<in> set (arithmetic_expression_sites g)"
  using assms unfolding arithmetic_expression_sites_def
  by (force simp: image_iff)

lemma arithmetic_diagnostics_absent:
  assumes site: "(v, obligations) \<in> set sites"
    and ob: "obligation \<in> set obligations"
    and absent: "\<forall>d \<in> set (arithmetic_diagnostics sites r classify). diagnostic_point d \<noteq> v"
  shows "point_verdict r classify v obligation = Bot \<or>
    point_verdict r classify v obligation = Lifted Check_Proved"
proof -
  have "obligation \<in> set (map snd (zip [0..<length obligations] obligations))"
    using ob by simp
  then obtain pair where pair: "pair \<in> set (zip [0..<length obligations] obligations)"
    and snd: "snd pair = obligation"
    unfolding set_map by blast
  have indexed: "(fst pair, obligation) \<in> set (zip [0..<length obligations] obligations)"
    using pair snd by (cases pair) auto
  define i where "i = fst pair"
  have indexed: "(i, obligation) \<in> set (zip [0..<length obligations] obligations)"
    using indexed unfolding i_def .
  let ?verdict = "point_verdict r classify v obligation"
  have included: "set (arithmetic_diagnostic_of v i obligation ?verdict)
      \<subseteq> set (arithmetic_diagnostics sites r classify)"
    using site indexed
    unfolding arithmetic_diagnostics_def
    by (force simp only: set_concat set_map image_iff case_prod_beta)
  have point: "\<And>d. d \<in> set (arithmetic_diagnostic_of v i obligation ?verdict) \<Longrightarrow>
      diagnostic_point d = v"
  proof -
    fix d
    assume d: "d \<in> set (arithmetic_diagnostic_of v i obligation ?verdict)"
    show "diagnostic_point d = v"
    proof (cases ?verdict)
      case Bot
      with d show ?thesis by simp
    next
      case (Lifted verdict)
      with d show ?thesis by (cases verdict) auto
    qed
  qed
  have empty: "arithmetic_diagnostic_of v i obligation ?verdict = []"
    using included point absent
    by (meson empty_subsetI set_empty2 subset_antisym subset_iff)
  show ?thesis
  proof (cases ?verdict)
    case Bot
    then show ?thesis by simp
  next
    case (Lifted verdict)
    with empty show ?thesis by (cases verdict) auto
  qed
qed

text \<open>An error names a point whose obligation the solved table refutes.\<close>

lemma arithmetic_diagnostic_of_refuted:
  assumes "d \<in> set (arithmetic_diagnostic_of v i obligation verdict)"
    and "diagnostic_verdict d = Check_Refuted"
  shows "verdict = Lifted Check_Refuted \<and> diagnostic_point d = v
    \<and> diagnostic_obligation d = obligation"
  using assms by (cases "(v, i, obligation, verdict)" rule: arithmetic_diagnostic_of.cases) auto

lemma arithmetic_diagnostics_refuted:
  assumes "d \<in> set (arithmetic_diagnostics sites r classify)"
    and "diagnostic_verdict d = Check_Refuted"
  shows "point_verdict r classify (diagnostic_point d) (diagnostic_obligation d)
      = Lifted Check_Refuted"
  using assms unfolding arithmetic_diagnostics_def
  by (auto dest!: arithmetic_diagnostic_of_refuted)

end
