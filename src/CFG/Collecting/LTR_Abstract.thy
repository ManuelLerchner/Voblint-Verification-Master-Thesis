theory LTR_Abstract
  imports LTR_Collect
begin

section \<open>What an analysis must satisfy to be sound\<close>

text \<open>
  An analysis claims: "at node \<open>v\<close>, in context \<open>c\<close>, only these stores can occur".  This
  theory says what such a claim must satisfy to be believed, and proves that satisfying it
  is enough --- every valid trace's final store really does lie in the set claimed for its
  own node and every context it carries.  No domain, solver or dependency graph appears
  here; they instantiate this.

  The claim is a function \<open>cover\<close> from a node and a context to a set of stores, and there
  are five obligations on it: the seed stores are covered at the entry (\<open>INIT\<close>), each intra
  edge keeps them covered (\<open>INTRA\<close>), a call covers the entered store at the callee in every
  context the policy admits (\<open>CALL\<close>), a return covers the combined store back at the caller
  (\<open>RETURN\<close>), and every covered call admits at least one context (\<open>TOTAL\<close>).

  \<open>RETURN\<close> is the load-bearing one.  The callee is read at a context admitted for the
  transition from the caller's own carried context, so a return may only compose a callee
  whose context came from the caller it is resuming --- not any context that happens to
  cover that callee's entry.  This correlation is not an extra parameter to assume:
  \<open>trace_context_caller_entry\<close> makes it a theorem about \<^const>\<open>valid_ltr\<close>.

  \<open>TOTAL\<close> is what makes the buckets meaningful rather than merely safe.  A resumed caller
  may carry a context under which its callee was never assigned one; the callee's exit
  store would then be bounded by no bucket, and the combined store by nothing.  With it,
  every valid trace carries some context, so the context-insensitive collection is exactly
  the union of the buckets.

  A context is not claimed to identify an activation: two activations may carry the same
  context, and one activation may carry several.  The theorem is that each trace lands in
  every slot it carries.
\<close>

subsection \<open>The abstract interface\<close>

text \<open>\<open>cover\<close> is the claim itself, \<open>R\<close> the context policy it is indexed by, and
  \<open>startcontext\<close> the context the seed stores arrive under.  An analysis interprets this once,
  with its own solved table in place of \<open>cover\<close>; nothing below asks how that table was
  computed.\<close>
locale ltr_coverage =
  fixes g :: cfg and S :: "store set"
    and cover :: "cfg_node \<Rightarrow> 'c \<Rightarrow> store set"
    and R :: "'c call_context_rel"
    and startcontext :: 'c
    and gs :: "vname \<Rightarrow> bool"
  assumes INIT[intro]: "\<And>s. s \<in> S \<Longrightarrow> s \<in> cover (cfg_entry g) startcontext"
    and INTRA[intro]: "\<And>u a v c s s'. (u, a, v) \<in> intra g
        \<Longrightarrow> s \<in> cover u c \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> s' \<in> cover v c"
    and CALL[intro]: "\<And>u dst pars args p cont c c' s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover u c
        \<Longrightarrow> R u c (call_info_of (CallEdge dst pars args) p) s
              (call_enter gs (CallEdge dst pars args) s) c'
        \<Longrightarrow> call_enter gs (CallEdge dst pars args) s \<in> cover (FunctionEntry p) c'"
    and RETURN[intro]: "\<And>cl dst pars args p cont c1 c' p' s t es.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> cover cl c1
        \<Longrightarrow> admits_call_context gs g R cl c1 p' s es c'
        \<Longrightarrow> t \<in> cover (FunctionResult p) c'
        \<Longrightarrow> combine_collect gs dst s t \<in> cover cont c1"
    and TOTAL: "call_context_total_on cover R gs g"
begin

text \<open>\<open>trace_covered u\<close>: \<open>u\<close> carries some context, and its sink store is admitted at its
  own node under every context it carries.\<close>
definition trace_covered :: "ltr \<Rightarrow> bool" where
  "trace_covered u \<longleftrightarrow>
     (\<exists>c. trace_context gs R startcontext g u c)
     \<and> (\<forall>c. trace_context gs R startcontext g u c \<longrightarrow> sink_store u \<in> cover (sink_node u) c)"

lemma trace_coveredI:
  assumes "trace_context gs R startcontext g u c0"
    and "\<And>c. trace_context gs R startcontext g u c \<Longrightarrow> sink_store u \<in> cover (sink_node u) c"
  shows "trace_covered u"
  using assms unfolding trace_covered_def by blast

lemma trace_covered_someE:
  assumes "trace_covered u"
  obtains c where "trace_context gs R startcontext g u c" "sink_store u \<in> cover (sink_node u) c"
  using assms unfolding trace_covered_def by blast

lemma trace_coveredD:
  "trace_covered u \<Longrightarrow> trace_context gs R startcontext g u c
   \<Longrightarrow> sink_store u \<in> cover (sink_node u) c"
  unfolding trace_covered_def by blast

subsection \<open>Closure under the four constructor clauses\<close>

text \<open>\<open>init_covered\<close>: the main activation's seed store is admitted at \<open>startcontext\<close>, the
  one context every \<^const>\<open>Root\<close> carries.\<close>
lemma init_covered: "s \<in> S \<Longrightarrow> trace_covered (Root [(cfg_entry g, s)])"
  by (auto simp: trace_covered_def)

text \<open>\<open>intra_covered\<close>: an intra edge preserves the carried contexts (\<open>trace_context_extend\<close>)
  and covers the concrete step through \<open>INTRA\<close> at each of them.\<close>
lemma intra_covered:
  assumes e: "(sink_node t, a, v) \<in> intra g"
    and st: "s' \<in> edge_step a (sink_store t)" and pne: "path t \<noteq> []" and iht: "trace_covered t"
  shows "trace_covered (extend t (v, s'))"
  using iht unfolding trace_covered_def
  by (auto simp: trace_context_extend[OF pne] intro: INTRA[OF e _ st])

text \<open>\<open>call_covered\<close>: \<open>TOTAL\<close> gives the new activation some context, from a context its
  caller carries; \<open>CALL\<close> covers the entered store at every context it carries, each of
  which names its own edge out of the call site.\<close>
lemma call_covered:
  assumes e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ihc: "trace_covered caller"
  shows "trace_covered (Call caller
           [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
proof -
  let ?es = "call_enter gs (CallEdge dst pars args) (sink_store caller)"
  from ihc obtain c where c: "trace_context gs R startcontext g caller c"
    and cov: "sink_store caller \<in> cover (sink_node caller) c"
    by (rule trace_covered_someE)
  obtain c' where
    adm: "admits_call_context gs g R (sink_node caller) c p (sink_store caller) ?es c'"
    by (rule call_context_total_onE[OF TOTAL e cov])
  have some: "trace_context gs R startcontext g (Call caller [(FunctionEntry p, ?es)]) c'"
    using c adm by (rule trace_context.Call)
  show ?thesis
  proof (rule trace_coveredI[OF some])
    fix c' assume "trace_context gs R startcontext g (Call caller [(FunctionEntry p, ?es)]) c'"
    then obtain c0 where c0: "trace_context gs R startcontext g caller c0"
      and adm0: "admits_call_context gs g R (sink_node caller) c0 p (sink_store caller) ?es c'"
      by (auto simp: trace_context_Call_iff)
    from adm0 obtain dst' pars' args' cont'
      where e': "(sink_node caller, CallEdge dst' pars' args', FunctionEntry p, cont') \<in> calls g"
        and es: "?es = call_enter gs (CallEdge dst' pars' args') (sink_store caller)"
        and Rc: "R (sink_node caller) c0 (call_info_of (CallEdge dst' pars' args') p)
                   (sink_store caller) ?es c'"
      by (rule admits_call_contextE)
    have "sink_store caller \<in> cover (sink_node caller) c0"
      using ihc c0 by (rule trace_coveredD)
    from CALL[OF e' this Rc[unfolded es]] es
    show "sink_store (Call caller [(FunctionEntry p, ?es)])
            \<in> cover (sink_node (Call caller [(FunctionEntry p, ?es)])) c'" by simp
  qed
qed

text \<open>\<open>return_covered\<close>: the matched return.  For each context \<open>c\<close> the resumed caller carries,
  \<open>TOTAL\<close> re-enters the callee at a context \<open>c'\<close> admitted from \<open>c\<close> along the callee's own
  entry edge (\<open>trace_context_caller_entry\<close>, both directions), the callee's hypothesis
  bounds its exit at \<open>c'\<close>, and \<open>RETURN\<close> composes the two at \<open>c\<close> --- never at a context
  rediscovered independently.\<close>
lemma return_covered:
  assumes callee_val: "callee \<in> valid_ltr gs g S"
    and cof: "caller_of callee = Some caller"
    and res: "sink_node callee = FunctionResult p"
    and comb: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
    and ih_caller: "trace_covered caller"
    and ih_callee: "trace_covered callee"
  shows "trace_covered (Resume caller callee (path caller
               @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
proof -
  let ?u = "Resume caller callee (path caller
    @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))])"
  have sn: "sink_node ?u = cont"
    and ss: "sink_store ?u = combine_collect gs dst (sink_store caller) (sink_store callee)"
    by (simp_all add: sink_node_def sink_store_def)
  from ih_caller obtain c1 where c1: "trace_context gs R startcontext g caller c1"
    by (rule trace_covered_someE)
  have some: "trace_context gs R startcontext g ?u c1" using c1 by simp
  from ih_callee obtain ce where ce: "trace_context gs R startcontext g callee ce"
    by (rule trace_covered_someE)
  obtain c0 p' where hd: "hd (path callee) = (FunctionEntry p', entry_store callee)"
    and adm: "admits_call_context gs g R (sink_node caller) c0 p' (sink_store caller)
                (entry_store callee) ce"
    by (rule trace_context_caller_entryE[OF callee_val cof ce])
  from adm obtain dst' pars' args' cont'
    where e': "(sink_node caller, CallEdge dst' pars' args', FunctionEntry p', cont') \<in> calls g"
      and es: "entry_store callee = call_enter gs (CallEdge dst' pars' args') (sink_store caller)"
    by (rule admits_call_contextE)
  show ?thesis
  proof (rule trace_coveredI[OF some])
    fix c assume "trace_context gs R startcontext g ?u c"
    then have cc: "trace_context gs R startcontext g caller c" by simp
    have s_cov: "sink_store caller \<in> cover (sink_node caller) c"
      using ih_caller cc by (rule trace_coveredD)
    obtain c' where adm': "admits_call_context gs g R (sink_node caller) c p' (sink_store caller)
                             (call_enter gs (CallEdge dst' pars' args') (sink_store caller)) c'"
      by (rule call_context_total_onE[OF TOTAL e' s_cov])
    have tc': "trace_context gs R startcontext g callee c'"
      by (rule trace_context_caller_entryI[OF callee_val cof hd cc adm'[folded es]])
    have t_cov: "sink_store callee \<in> cover (FunctionResult p) c'"
      using trace_coveredD[OF ih_callee tc'] res by simp
    have "combine_collect gs dst (sink_store caller) (sink_store callee) \<in> cover cont c"
      by (rule RETURN[OF comb s_cov adm'[folded es] t_cov])
    then show "sink_store ?u \<in> cover (sink_node ?u) c" by (simp add: sn ss)
  qed
qed

subsection \<open>The generic soundness theorem\<close>

text \<open>The bound holds along the whole caller chain, by \<^const>\<open>valid_ltr\<close> rule induction
  feeding the four closure lemmas.  The chain, not a per-node statement, is what the
  \<open>RETURN\<close> case needs: it recovers its caller structurally, and the caller lies in the
  callee's chain.\<close>
lemma caller_chain_covered:
  "t \<in> valid_ltr gs g S \<Longrightarrow> \<forall>u \<in> callers t. trace_covered u"
proof (rule caller_chain_closure)
  fix s assume "s \<in> S"
  then show "trace_covered (Root [(cfg_entry g, s)])" by (rule init_covered)
next
  fix t a v s' assume ht: "t \<in> valid_ltr gs g S" and ch: "\<forall>u \<in> callers t. trace_covered u"
    and e: "(sink_node t, a, v) \<in> intra g" and st: "s' \<in> edge_step a (sink_store t)"
  have pt: "path t \<noteq> []" using ht valid_ltr_path_nonempty by blast
  have iht: "trace_covered t" using ch callers_refl by blast
  show "trace_covered (extend t (v, s'))" by (rule intra_covered[OF e st pt iht])
next
  fix caller dst pars args p cont
  assume ch: "\<forall>u \<in> callers caller. trace_covered u"
    and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  have ihc: "trace_covered caller" using ch callers_refl by blast
  show "trace_covered (Call caller
          [(FunctionEntry p, call_enter gs (CallEdge dst pars args) (sink_store caller))])"
    by (rule call_covered[OF e ihc])
next
  fix callee caller p dst pars args cont
  assume cv: "callee \<in> valid_ltr gs g S" and ch: "\<forall>u \<in> callers callee. trace_covered u"
    and cof: "caller_of callee = Some caller" and res: "sink_node callee = FunctionResult p"
    and e: "(sink_node caller, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g"
  have ih_caller: "trace_covered caller" using ch cof callers_caller_subset callers_refl by blast
  have ih_callee: "trace_covered callee" using ch callers_refl by blast
  show "trace_covered (Resume caller callee (path caller
             @ [(cont, combine_collect gs dst (sink_store caller) (sink_store callee))]))"
    by (rule return_covered[OF cv cof res e ih_caller ih_callee])
qed

text \<open>Every valid trace carries a context, and its sink lies in every slot it carries:
  \<^const>\<open>valid_ltr\<close> is soundly over-approximated by \<open>trace_covered\<close>.\<close>
theorem valid_ltr_covered: "t \<in> valid_ltr gs g S \<Longrightarrow> trace_covered t"
proof -
  assume "t \<in> valid_ltr gs g S"
  then have "\<forall>u \<in> callers t. trace_covered u" by (rule caller_chain_covered)
  then show "trace_covered t" using callers_refl by blast
qed

theorem valid_ltr_has_context:
  assumes "t \<in> valid_ltr gs g S"
  obtains c where "trace_context gs R startcontext g t c"
  using valid_ltr_covered[OF assms] by (rule trace_covered_someE)

theorem valid_ltr_covered_at:
  "t \<in> valid_ltr gs g S \<Longrightarrow> trace_context gs R startcontext g t c
   \<Longrightarrow> sink_store t \<in> cover (sink_node t) c"
  using valid_ltr_covered by (rule trace_coveredD)

text \<open>Bridge (2) of \<^theory>\<open>Voblint_CFG.LTR_Collect\<close>, earned: under \<open>TOTAL\<close> the
  context-insensitive collection is the union of the buckets.\<close>
theorem ltr_collect_eq_Union_activation_collect:
  "ltr_collect gs g S v = (\<Union>c. activation_collect gs R startcontext g S v c)"
proof
  show "ltr_collect gs g S v \<subseteq> (\<Union>c. activation_collect gs R startcontext g S v c)"
  proof
    fix x assume "x \<in> ltr_collect gs g S v"
    then obtain t where t: "t \<in> valid_ltr gs g S" "sink_node t = v" "sink_store t = x"
      by (rule ltr_collect_E)
    from valid_ltr_has_context[OF t(1)] obtain c where "trace_context gs R startcontext g t c" .
    with t show "x \<in> (\<Union>c. activation_collect gs R startcontext g S v c)" by blast
  qed
next
  show "(\<Union>c. activation_collect gs R startcontext g S v c) \<subseteq> ltr_collect gs g S v"
    by (rule Union_activation_collect_le_ltr_collect)
qed

end

subsection \<open>Non-vacuity\<close>

text \<open>The interface is satisfiable for every graph, seed set, and start context: choosing
  the top cover \<open>cover = (\<lambda>_ _. UNIV)\<close> together with any total functional context policy
  discharges all five obligations, \<open>TOTAL\<close> included, since a functional policy is total
  (\<open>call_context_total_on_of_fun\<close>). It is not satisfiable at an arbitrary \<open>R\<close>: taking
  \<open>R = (\<lambda>_ _ _ _ _ _. False)\<close> fails \<open>TOTAL\<close> for any graph with a reachable call, however
  wide \<open>cover\<close> is chosen --- \<open>TOTAL\<close> genuinely constrains the context policy, not merely
  the cover.\<close>

lemma ltr_coverage_exists:
  "ltr_coverage g S (\<lambda>_ _. UNIV) (call_context_rel_of_fun (\<lambda>_ _ _. ())) () gs"
  by unfold_locales auto

subsection \<open>Monovariant semantic post-fixpoint\<close>

text \<open>
  Set-valued entry, edge, call, and combine closure of a candidate node map \<open>B\<close> bounds the
  stack-faithful \<^const>\<open>ltr_collect\<close> at every node.  The proof interprets
  \<^locale>\<open>ltr_coverage\<close> at \<open>cover v _ = B v\<close> with the trivial one-point context, whose policy
  is total outright; its combine obligation follows one caller and one callee exit.
\<close>
lemma ltr_collect_semantic_postfix:
  fixes g :: cfg and B :: "cfg_node \<Rightarrow> store set" and S0 :: "store set" and v :: cfg_node
    and gs :: "vname \<Rightarrow> bool"
  assumes entry: "S0 \<subseteq> B (cfg_entry g)"
    and edge: "\<And>u a w s s'. (u, a, w) \<in> intra g \<Longrightarrow> s \<in> B u \<Longrightarrow> s' \<in> edge_step a s \<Longrightarrow> s' \<in> B w"
    and call: "\<And>u dst pars args p cont s.
        (u, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> B u \<Longrightarrow> call_enter gs (CallEdge dst pars args) s \<in> B (FunctionEntry p)"
    and combine: "\<And>cl dst pars args p cont s t.
        (cl, CallEdge dst pars args, FunctionEntry p, cont) \<in> calls g
        \<Longrightarrow> s \<in> B cl \<Longrightarrow> t \<in> B (FunctionResult p) \<Longrightarrow> combine_collect gs dst s t \<in> B cont"
  shows "ltr_collect gs g S0 v \<subseteq> B v"
proof -
  interpret G: ltr_coverage g S0 "\<lambda>v _. B v" "call_context_rel_of_fun (\<lambda>_ _ _. ())" "()" gs
  proof (standard, goal_cases INIT INTRA CALL RETURN TOTAL)
    case (INIT s) then show ?case using entry by auto
  next
    case (INTRA u a w c s s') then show ?case using edge by simp
  next
    case (CALL u dst pars args p cont c c' s) then show ?case using call by simp
  next
    case (RETURN cl dst pars args p cont c1 c' p' s t es) then show ?case using combine by simp
  next
    case TOTAL then show ?case by simp
  qed
  show ?thesis
  proof (rule subsetI)
    fix x assume "x \<in> ltr_collect gs g S0 v"
    then obtain u where u: "u \<in> valid_ltr gs g S0" "sink_node u = v" "sink_store u = x"
      by (rule ltr_collect_E)
    from G.valid_ltr_has_context[OF u(1)] obtain c
      where c: "trace_context gs (call_context_rel_of_fun (\<lambda>_ _ _. ())) () g u c" .
    have "sink_store u \<in> B (sink_node u)" using G.valid_ltr_covered_at[OF u(1) c] by simp
    then show "x \<in> B v" using u(2,3) by simp
  qed
qed


end
