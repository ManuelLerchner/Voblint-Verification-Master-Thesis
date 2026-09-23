theory Arithmetic_Diagnostics
  imports "Voblint_Framework.Contextual_Check_Report"
    "Voblint_Framework.Abstract_Checks"
begin

section \<open>Division and remainder occurrences\<close>

text \<open>Diagnostics inspect all expression operands, matching VIMP's total,
  pure expression model. They neither change execution nor assume short-circuit
  evaluation for logical operators. Lists retain repeated syntactically equal occurrences.\<close>

datatype arithmetic_obligation = Arithmetic_Obligation
  (arithmetic_operation: exp)
  (arithmetic_divisor: exp)

fun arithmetic_obligations :: "exp \<Rightarrow> arithmetic_obligation list" where
  "arithmetic_obligations (N n) = []"
| "arithmetic_obligations (V x) = []"
| "arithmetic_obligations (Not a) = arithmetic_obligations a"
| "arithmetic_obligations (And a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (Or a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (Div a b) =
     arithmetic_obligations a @ arithmetic_obligations b @
       [Arithmetic_Obligation (Div a b) b]"
| "arithmetic_obligations (Mod a b) =
     arithmetic_obligations a @ arithmetic_obligations b @
       [Arithmetic_Obligation (Mod a b) b]"
| "arithmetic_obligations (Plus a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (Minus a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (Times a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (Less a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (LessEq a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (Greater a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (GreaterEq a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (Eq a b) =
     arithmetic_obligations a @ arithmetic_obligations b"
| "arithmetic_obligations (NotEq a b) =
     arithmetic_obligations a @ arithmetic_obligations b"

text \<open>The set specification ignores occurrence numbering and names every denominator
  appearing anywhere in an expression. The extraction theorem connects it to the
  occurrence-preserving list consumed by the report.\<close>

fun expression_divisors :: "exp \<Rightarrow> exp set" where
  "expression_divisors (N n) = {}"
| "expression_divisors (V x) = {}"
| "expression_divisors (Not a) = expression_divisors a"
| "expression_divisors (And a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (Or a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (Div a b) =
     insert b (expression_divisors a \<union> expression_divisors b)"
| "expression_divisors (Mod a b) =
     insert b (expression_divisors a \<union> expression_divisors b)"
| "expression_divisors (Plus a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (Minus a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (Times a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (Less a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (LessEq a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (Greater a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (GreaterEq a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (Eq a b) =
     expression_divisors a \<union> expression_divisors b"
| "expression_divisors (NotEq a b) =
     expression_divisors a \<union> expression_divisors b"

lemma arithmetic_obligations_divisors:
  "arithmetic_divisor ` set (arithmetic_obligations e) = expression_divisors e"
  by (induction e) auto

definition arithmetic_condition :: "arithmetic_obligation \<Rightarrow> exp" where
  "arithmetic_condition obligation = NotEq (arithmetic_divisor obligation) (N 0)"

lemma arithmetic_condition_safe:
  "truthy (\<lbrakk>arithmetic_condition obligation\<rbrakk>\<^sub>e s) \<longleftrightarrow>
    \<lbrakk>arithmetic_divisor obligation\<rbrakk>\<^sub>e s \<noteq> 0"
  by (auto simp: arithmetic_condition_def split: if_splits)

context abstract_check_domain
begin

lemma arithmetic_classify_safe:
  assumes "classify_check (arithmetic_condition obligation) d = Check_Proved"
    and "s \<in> gamma_state d"
  shows "\<lbrakk>arithmetic_divisor obligation\<rbrakk>\<^sub>e s \<noteq> 0"
  using classify_check_proved[OF assms]
  by (auto simp: arithmetic_condition_def split: if_splits)

lemma arithmetic_classify_zero:
  assumes "classify_check (arithmetic_condition obligation) d = Check_Refuted"
    and "s \<in> gamma_state d"
  shows "\<lbrakk>arithmetic_divisor obligation\<rbrakk>\<^sub>e s = 0"
  using classify_check_refuted[OF assms]
  by (auto simp: arithmetic_condition_def split: if_splits)

end

section \<open>Sites and their solved classifications\<close>

fun arithmetic_edge_expressions :: "edge_action \<Rightarrow> exp list" where
  "arithmetic_edge_expressions (EA_Assign x e) = [e]"
| "arithmetic_edge_expressions (EA_Assume e) = [e]"
| "arithmetic_edge_expressions (EA_AssumeNot e) = [e]"
| "arithmetic_edge_expressions (EA_Check e) = [e]"
| "arithmetic_edge_expressions (EA_Ret (Some e) p) = [e]"
| "arithmetic_edge_expressions (EA_Special (Min a b) x) = [a, b]"
| "arithmetic_edge_expressions (EA_Special (Max a b) x) = [a, b]"
| "arithmetic_edge_expressions _ = []"

text \<open>Only suppress a negative guard edge when the same point has a matching
  positive guard edge. All other expression-bearing edges remain in the report.\<close>

definition arithmetic_expression_sites :: "cfg \<Rightarrow> (pp \<times> exp list) list" where
  "arithmetic_expression_sites g =
     (let edges = cfg_intra_list g
      in map (\<lambda>(u, a, v). (u, arithmetic_edge_expressions a))
           (filter (\<lambda>(u, a, v). case a of EA_AssumeNot e \<Rightarrow>
             \<not> list_ex (\<lambda>(u', a', v'). u = u' \<and> a' = EA_Assume e) edges
             | _ \<Rightarrow> True) edges)) @
       map (\<lambda>(u, ca, ce, k). (u, ce_args ca)) (cfg_calls_list g)"

definition arithmetic_sites :: "cfg \<Rightarrow> (pp \<times> arithmetic_obligation list) list" where
  "arithmetic_sites g =
     map (\<lambda>(v, es). (v, concat (map arithmetic_obligations es)))
       (arithmetic_expression_sites g)"

datatype arithmetic_diagnostic = Arithmetic_Diagnostic
  (diagnostic_point: pp)
  (diagnostic_occurrence: nat)
  (diagnostic_obligation: arithmetic_obligation)
  (diagnostic_verdict: check_result)

definition arithmetic_site_verdict ::
    "('ctx, 'a) analysis_result \<Rightarrow> (exp \<Rightarrow> 'a \<Rightarrow> check_result)
       \<Rightarrow> pp \<Rightarrow> arithmetic_obligation \<Rightarrow> contextual_verdict" where
  "arithmetic_site_verdict r classify v obligation =
     aggregate_verdicts
       (image (\<lambda>ctx. classify_point classify (arithmetic_condition obligation)
         (lookup_context r v ctx)) (contexts_at r v))"

fun arithmetic_diagnostic_of ::
    "pp \<Rightarrow> nat \<Rightarrow> arithmetic_obligation \<Rightarrow> contextual_verdict
       \<Rightarrow> arithmetic_diagnostic list" where
  "arithmetic_diagnostic_of v i obligation (Lifted Check_Refuted) =
     [Arithmetic_Diagnostic v i obligation Check_Refuted]"
| "arithmetic_diagnostic_of v i obligation (Lifted Check_Unknown) =
     [Arithmetic_Diagnostic v i obligation Check_Unknown]"
| "arithmetic_diagnostic_of v i obligation _ = []"

definition arithmetic_diagnostics ::
    "cfg \<Rightarrow> ('ctx, 'a) analysis_result \<Rightarrow> (exp \<Rightarrow> 'a \<Rightarrow> check_result)
       \<Rightarrow> arithmetic_diagnostic list" where
  "arithmetic_diagnostics g r classify =
     concat (map (\<lambda>(v, obligations).
       concat (map (\<lambda>(i, obligation).
         arithmetic_diagnostic_of v i obligation
           (arithmetic_site_verdict r classify v obligation))
         (zip [0..<length obligations] obligations))) (arithmetic_sites g))"

lemma arithmetic_expression_sites_intra:
  assumes "finite (intra g)" and "(v, a, w) \<in> intra g"
  shows "(v, arithmetic_edge_expressions a) \<in> set (arithmetic_expression_sites g)"
proof -
  let ?edges = "cfg_intra_list g"
  have mem: "(v, a, w) \<in> set ?edges" using assms by simp
  have kept: "\<And>b t. (v, b, t) \<in> set ?edges \<Longrightarrow>
      (case b of EA_AssumeNot e \<Rightarrow>
        \<not> list_ex (\<lambda>(u', a', v'). v = u' \<and> a' = EA_Assume e) ?edges
        | _ \<Rightarrow> True) \<Longrightarrow>
      (v, arithmetic_edge_expressions b) \<in> set (arithmetic_expression_sites g)"
    unfolding arithmetic_expression_sites_def
    by (force simp: Let_def image_iff)
  show ?thesis
  proof (cases "\<exists>e. a = EA_AssumeNot e")
    case False
    with mem show ?thesis by (intro kept[of a w]) (auto split: edge_action.splits)
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

lemma arithmetic_sites_divisor:
  assumes "(v, es) \<in> set (arithmetic_expression_sites g)"
    and "e \<in> set es" and "divisor \<in> expression_divisors e"
  obtains obligations obligation where "(v, obligations) \<in> set (arithmetic_sites g)"
    and "obligation \<in> set obligations" and "arithmetic_divisor obligation = divisor"
proof -
  from assms(3) obtain obligation where
    ob: "obligation \<in> set (arithmetic_obligations e)"
      "arithmetic_divisor obligation = divisor"
    using arithmetic_obligations_divisors[of e] by force
  have site: "(v, concat (map arithmetic_obligations es)) \<in> set (arithmetic_sites g)"
    using assms(1) by (auto simp: arithmetic_sites_def)
  have "obligation \<in> set (concat (map arithmetic_obligations es))"
    using ob assms(2) by auto
  from that[OF site this ob(2)] show thesis .
qed

lemma arithmetic_diagnostics_absent:
  assumes site: "(v, obligations) \<in> set (arithmetic_sites g)"
    and ob: "obligation \<in> set obligations"
    and absent: "\<forall>d \<in> set (arithmetic_diagnostics g r classify). diagnostic_point d \<noteq> v"
  shows "arithmetic_site_verdict r classify v obligation = Bot \<or>
    arithmetic_site_verdict r classify v obligation = Lifted Check_Proved"
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
  let ?verdict = "arithmetic_site_verdict r classify v obligation"
  have included: "set (arithmetic_diagnostic_of v i obligation ?verdict)
      \<subseteq> set (arithmetic_diagnostics g r classify)"
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
  proof (cases "arithmetic_site_verdict r classify v obligation")
    case Bot
    then show ?thesis by simp
  next
    case (Lifted verdict)
    with empty show ?thesis by (cases verdict) auto
  qed
qed

lemma arithmetic_site_verdict_classify:
  assumes agg: "arithmetic_site_verdict r classify v obligation = Lifted verdict"
    and known: "verdict \<noteq> Check_Unknown"
    and look: "lookup_context r v ctx = Lifted st"
  shows "classify (arithmetic_condition obligation) st = verdict"
proof -
  have ctx: "ctx \<in> contexts_at r v"
    using look unfolding lookup_context_def by (auto split: if_splits)
  have member: "classify_point classify (arithmetic_condition obligation) (lookup_context r v ctx)
      \<in> image (\<lambda>c. classify_point classify (arithmetic_condition obligation)
        (lookup_context r v c)) (contexts_at r v)"
    using ctx by blast
  from aggregate_verdicts_decided_dest[OF agg[unfolded arithmetic_site_verdict_def] known]
    member look show ?thesis by auto
qed

lemma arithmetic_site_verdict_not_bot:
  assumes fin: "finite (contexts_at r v)"
    and look: "lookup_context r v ctx = Lifted st"
  shows "arithmetic_site_verdict r classify v obligation \<noteq> Bot"
proof -
  have ctx: "ctx \<in> contexts_at r v"
    using look unfolding lookup_context_def by (auto split: if_splits)
  let ?vs = "image (\<lambda>c. classify_point classify (arithmetic_condition obligation)
    (lookup_context r v c)) (contexts_at r v)"
  have finite_vs: "finite ?vs" using fin by simp
  show ?thesis
  proof
    assume bottom: "arithmetic_site_verdict r classify v obligation = Bot"
    have all_bot: "\<forall>x \<in> ?vs. x = Bot"
      by (rule aggregate_verdicts_eq_Dead_iff[OF finite_vs, THEN iffD1])
         (use bottom in \<open>simp only: arithmetic_site_verdict_def\<close>)
    have member: "classify_point classify (arithmetic_condition obligation)
      (lookup_context r v ctx) \<in> ?vs"
      by (rule imageI[OF ctx])
    have "classify_point classify (arithmetic_condition obligation)
      (lookup_context r v ctx) = Bot"
      by (rule bspec[OF all_bot member])
    with look show False by simp
  qed
qed

end
