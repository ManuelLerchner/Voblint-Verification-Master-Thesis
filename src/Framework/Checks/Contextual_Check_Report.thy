theory Contextual_Check_Report
  imports Check_Report Analysis_Result
begin

section \<open>Contextual check verdicts over a solved result table\<close>

text \<open>
  \<^const>\<open>classify_checks\<close> reads exactly one abstract state per checked node.
  A context-sensitive result has one state per \<open>(node, context)\<close> pair
  instead, and some of those pairs represent no concrete execution at all: a
  branch that is dead inside one activation, or an activation a node is never
  reached under. Classifying such a point against its stored state answers
  vacuously: a classifier's soundness obligation only constrains the stores
  its state represents, so on a state representing none, either definite
  answer satisfies that obligation vacuously --- a verdict read there is
  evidence of nothing, and reporting it as \<^const>\<open>Check_Proved\<close> would
  fabricate a proof about executions that do not exist.

  \<open>contextual_verdict\<close> keeps that case outside \<^typ>\<open>check_result\<close> rather
  than folding it into one of its three values. \<open>Dead\<close> means ``no concrete
  execution is represented here''; it is neither \<^const>\<open>Check_Unknown\<close>, which
  does assert that something reaches this point and the abstraction failed to
  decide it, nor \<^const>\<open>Check_Proved\<close>.
\<close>

text \<open>
  \<open>contextual_verdict\<close> is literally \<^typ>\<open>check_result lifted\<close>
  (\<^theory>\<open>Voblint_Domain.Reachability_Lift\<close>): \<open>Dead\<close> is \<^const>\<open>Bot\<close>, \<open>Decided\<close>
  is \<^const>\<open>Lifted\<close>, and the order/bottom/join this section used to
  instantiate by hand agree with \<^typ>\<open>'a lifted\<close>'s own generic instance at
  \<^typ>\<open>check_result\<close> (itself \<^class>\<open>semilattice_sup\<close>, from
  \<^theory>\<open>Voblint_Framework.Check_Result\<close>) constructor for constructor: \<open>Dead \<le> _\<close>
  always, a \<open>Decided\<close> never sits below \<open>Dead\<close>, and two \<open>Decided\<close> verdicts
  compare and join through \<^typ>\<open>check_result\<close>'s own flat order. Reusing it
  here keeps one lattice construction for "structurally absent vs. present
  with a payload" instead of two.
\<close>

type_synonym contextual_verdict = "check_result lifted"

abbreviation Dead :: contextual_verdict where
  "Dead \<equiv> Bot"

abbreviation Decided :: "check_result \<Rightarrow> contextual_verdict" where
  "Decided r \<equiv> Lifted r"


subsection \<open>Classifying one contextual point\<close>

text \<open>
  The reachability decision is not remade here: it was already made when the
  raw solved local unknown crossed the result boundary, one layer before
  \<open>normalize_point\<close>'s own structural relabeling. A witness-bottom
  \<^const>\<open>Lifted\<close> payload is collapsed to \<^const>\<open>Bot\<close> by
  \<^const>\<open>canonicalize_lift\<close>, so by the time a value reaches
  \<open>normalize_point\<close> --- as every public result adapter's raw value
  does --- \<^const>\<open>Bot\<close> and \<^const>\<open>Lifted\<close> already agree with concrete
  emptiness and non-emptiness respectively, and \<^const>\<open>Bot\<close> at the
  \<open>lifted\<close> level means exactly that. \<open>classify_point\<close> only refuses to
  classify against a state that represents nothing: a covered-but-dead
  activation, whose raw stored state a solver run could otherwise leave as
  a witness-bottom \<^const>\<open>Lifted\<close>, reaches \<open>classify_point\<close> as
  \<^const>\<open>Bot\<close> rather than fabricating a vacuous
  \<^const>\<open>Check_Proved\<close> off an empty state.
\<close>

fun classify_point ::
  "(exp \<Rightarrow> 'a \<Rightarrow> check_result) \<Rightarrow> exp \<Rightarrow> 'a lifted \<Rightarrow> contextual_verdict"
where
  "classify_point classify c Bot = Dead"
| "classify_point classify c (Lifted st) = Decided (classify c st)"

subsection \<open>Aggregating the contexts observed at one check\<close>

text \<open>
  Folding \<^const>\<open>sup\<close> from \<open>Dead\<close> over a finite set of observations, exactly
  as \<open>join_states_over\<close> folds the state join from \<^const>\<open>Bot\<close>. The
  fold's unit is the empty-set answer, so a check with no covered context
  needs no separate guard. The \<open>[code]\<close> equation is the usual
  \<open>comp_fun_idem\<close> transfer to a list fold: over an unordered set the value is
  well defined only because \<^const>\<open>sup\<close> is commutative, associative, and
  idempotent.
\<close>

definition aggregate_verdicts :: "contextual_verdict set \<Rightarrow> contextual_verdict" where
  "aggregate_verdicts vs = Finite_Set.fold sup Dead vs"

declare aggregate_verdicts_def [code del]

lemma aggregate_verdicts_code [code]:
  "aggregate_verdicts (set vs) = List.fold sup vs Dead"
proof -
  interpret ci: comp_fun_idem "sup :: contextual_verdict \<Rightarrow> _"
    by (rule comp_fun_idem_sup)
  show ?thesis unfolding aggregate_verdicts_def by (rule ci.fold_set_fold)
qed

lemma aggregate_verdicts_empty [simp]: "aggregate_verdicts {} = Dead"
  unfolding aggregate_verdicts_def by simp

lemma aggregate_verdicts_insert [simp]:
  "finite vs \<Longrightarrow> aggregate_verdicts (insert v vs) = v \<squnion> aggregate_verdicts vs"
proof -
  assume "finite vs"
  interpret ci: comp_fun_idem "sup :: contextual_verdict \<Rightarrow> _"
    by (rule comp_fun_idem_sup)
  show ?thesis
    unfolding aggregate_verdicts_def using \<open>finite vs\<close> by simp
qed

text \<open>A check is dead exactly when every context observed at it is dead ---
  vacuously so when none is observed. Stated over the observations themselves
  rather than over the aggregate, and then shown to agree with it, so the two
  readings cannot drift.\<close>

lemma sup_contextual_verdict_eq_Dead_iff [simp]:
  "(x \<squnion> y = Dead) \<longleftrightarrow> x = Dead \<and> y = Dead"
  by (cases x; cases y) simp_all

definition check_dead :: "('ctx \<times> contextual_verdict) set \<Rightarrow> bool" where
  "check_dead vs = (\<forall>(c, v) \<in> vs. v = Dead)"

lemma check_dead_empty [simp]: "check_dead {}"
  unfolding check_dead_def by simp

text \<open>The opposite direction, for a report that has only one observation per
  check and therefore no dead case to distinguish: every entry is
  \<open>Decided\<close>. Deadness is not asserted either way --- such a report simply does
  not carry the channel that would express it.\<close>

definition decided_report ::
  "check_report_entry list \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "decided_report = map (\<lambda>(u, cnd, r). (u, cnd, Decided r))"

lemma length_decided_report [simp]: "length (decided_report rs) = length rs"
  unfolding decided_report_def by simp

subsection \<open>Whole-program contextual check report\<close>

text \<open>
  The context-sensitive sibling of \<^const>\<open>classify_checks\<close>: the same
  \<^const>\<open>EA_Check\<close> traversal in the same \<^const>\<open>cfg_intra_list\<close> order, but
  reading a \<^typ>\<open>('ctx, 'a) analysis_result\<close> instead of a single
  \<^typ>\<open>pp \<Rightarrow> 's\<close> environment, and retaining one verdict per context covered
  at the checked node rather than collapsing them at construction time.
  \<open>classify_checks_ctx_positions\<close> below is the load-bearing consequence: the
  node and condition columns coincide with \<^const>\<open>classify_checks\<close>'s, so a
  positional consumer pairing this report with the source's own check list
  stays aligned.

  The per-check observations are a set, not a list. \<^typ>\<open>'ctx\<close> carries no
  ordering constraint --- \<^const>\<open>contexts_at\<close> is a set for precisely that
  reason, and real context types such as interval vectors have no total
  order --- so no canonical list exists to produce. Nothing downstream needs
  one: \<^const>\<open>aggregate_verdicts\<close> is order-independent by construction.
\<close>

definition classify_checks_ctx ::
    "cfg \<Rightarrow> ('ctx, 'a) analysis_result \<Rightarrow> (exp \<Rightarrow> 'a \<Rightarrow> check_result)
       \<Rightarrow> (pp \<times> exp \<times> ('ctx \<times> contextual_verdict) set) list" where
  "classify_checks_ctx g r classify =
     map (\<lambda>(u, a, v). (u, ea_check_cond a,
            (\<lambda>ctx. (ctx, classify_point classify (ea_check_cond a) (lookup_context r u ctx)))
              ` contexts_at r u))
       (filter (\<lambda>(u, a, v). is_EA_Check a) (cfg_intra_list g))"

definition classify_checks_verdicts ::
    "cfg \<Rightarrow> ('ctx, 'a) analysis_result \<Rightarrow> (exp \<Rightarrow> 'a \<Rightarrow> check_result)
       \<Rightarrow> (pp \<times> exp \<times> contextual_verdict) list" where
  "classify_checks_verdicts g r classify =
     map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs))) (classify_checks_ctx g r classify)"

lemma classify_checks_verdicts_proj [simp]:
  "map (\<lambda>(u, c, vs). (u, c, aggregate_verdicts (snd ` vs))) (classify_checks_ctx g r classify)
     = classify_checks_verdicts g r classify"
  unfolding classify_checks_verdicts_def by (rule refl)

lemma classify_checks_ctx_positions:
  "map (\<lambda>(u, c, vs). (u, c)) (classify_checks_ctx g r classify)
     = map (\<lambda>(u, c, res). (u, c)) (classify_checks g env classify')"
  unfolding classify_checks_ctx_def classify_checks_def
  by (simp add: comp_def case_prod_beta)

text \<open>Membership unfolds to an \<^const>\<open>EA_Check\<close> edge at the entry's own source
  node, with that node's whole context fan-out attached --- the same shape
  \<open>classify_checks_mem_iff\<close> gives the context-insensitive report.\<close>

lemma classify_checks_ctx_mem_iff:
  assumes "finite (intra g)"
  shows "(v, c, vs) \<in> set (classify_checks_ctx g r classify)
     \<longleftrightarrow> (\<exists>tgt. (v, EA_Check c, tgt) \<in> intra g)
         \<and> vs = (\<lambda>ctx. (ctx, classify_point classify c (lookup_context r v ctx))) ` contexts_at r v"
  unfolding classify_checks_ctx_def set_map set_filter
  using set_cfg_intra_list[OF assms]
  by (auto simp: image_iff split: edge_action.splits)

subsection \<open>Contextual proved/refuted soundness\<close>

text \<open>
  The \<open>Decided Check_Proved\<close>/\<open>Decided Check_Refuted\<close> analogues of
  \<open>classify_checks_proved_sound\<close>/\<open>classify_checks_refuted_sound\<close>: an
  aggregated verdict of \<^term>\<open>Decided Check_Proved\<close> forces every observation
  folded into it to be \<^const>\<open>Dead\<close> or \<^term>\<open>Decided Check_Proved\<close> --- never
  a disagreeing \<^term>\<open>Decided Check_Refuted\<close> or \<^term>\<open>Decided Check_Unknown\<close>,
  since either would collapse the join to \<^term>\<open>Decided Check_Unknown\<close>
  instead. \<open>Dead\<close> observations contribute nothing and are filtered out at the
  call site, not here.
\<close>

text \<open>
  The order-theoretic route: every member of a finite set sits below the
  set's own fold-join (\<open>aggregate_verdicts_member_le\<close>), a decided,
  non-\<open>Check_Unknown\<close> aggregate already forces the set finite
  (\<open>aggregate_verdicts_decided_finite\<close>, since an infinite carrier folds to the
  identity \<open>Dead\<close>), and sitting below such a verdict has only two shapes
  (\<open>contextual_verdict_le_Decided_iff\<close>). Composing the three gives
  \<open>aggregate_verdicts_decided_dest\<close> directly, with no case-bash over the fold
  step: disagreement, from either side, could only have collapsed the join to
  \<^term>\<open>Decided Check_Unknown\<close> instead.
\<close>

lemma aggregate_verdicts_member_le:
  assumes "finite vs" and "v \<in> vs"
  shows "v \<le> aggregate_verdicts vs"
  using assms
  by (induction vs rule: finite_induct) (auto intro: order_trans sup_ge2)

lemma contextual_verdict_le_Decided_iff [simp]:
  assumes "r \<noteq> Check_Unknown"
  shows "v \<le> Decided r \<longleftrightarrow> v = Dead \<or> v = Decided r"
  using assms by (cases v; cases r) (simp_all add: less_eq_check_result_def)

lemma aggregate_verdicts_decided_finite:
  "aggregate_verdicts vs = Decided r \<Longrightarrow> finite vs"
  by (rule ccontr) (simp add: aggregate_verdicts_def)

lemma aggregate_verdicts_decided_dest:
  assumes agg: "aggregate_verdicts vs = Decided r" and known: "r \<noteq> Check_Unknown"
  shows "\<forall>v \<in> vs. v = Dead \<or> v = Decided r"
proof
  fix v
  assume "v \<in> vs"
  have "v \<le> aggregate_verdicts vs"
    using aggregate_verdicts_member_le[OF aggregate_verdicts_decided_finite[OF agg] \<open>v \<in> vs\<close>] .
  with agg known show "v = Dead \<or> v = Decided r" by simp
qed


text \<open>
  The context-indexed report analogue of \<open>classify_checks_proved_sound\<close>/
  \<open>classify_checks_refuted_sound\<close>, stated once for any decided,
  non-\<open>Check_Unknown\<close> aggregate: it forces the classifier's own reading at
  every \<^const>\<open>Lifted\<close> context to agree. The image set being folded is
  shown finite from the aggregate equation itself (\<open>Finite_Set.fold_infinite\<close>:
  an infinite carrier folds to the identity \<open>Dead\<close>, which a decided,
  non-\<open>Check_Unknown\<close> result already rules out), so no separate finiteness
  assumption on the covered contexts is needed.
  \<open>classify_checks_ctx_proved_sound\<close>/\<open>classify_checks_ctx_refuted_sound\<close> below
  are its two instances, kept under their own names for \<open>DG_Analysis_Adapter\<close>.
\<close>

lemma classify_checks_verdicts_mem_iff:
  assumes "finite (intra g)"
  shows "(v, c, vr) \<in> set (classify_checks_verdicts g ar classify)
     \<longleftrightarrow> (\<exists>tgt. (v, EA_Check c, tgt) \<in> intra g)
         \<and> vr = aggregate_verdicts
                  ((\<lambda>ctx. classify_point classify c (lookup_context ar v ctx)) ` contexts_at ar v)"
proof -
  have "(v, c, vr) \<in> set (classify_checks_verdicts g ar classify)
      \<longleftrightarrow> (\<exists>vs. (v, c, vs) \<in> set (classify_checks_ctx g ar classify) \<and> vr = aggregate_verdicts (snd ` vs))"
    unfolding classify_checks_verdicts_def set_map by (force simp: image_iff)
  also have "... \<longleftrightarrow> (\<exists>tgt. (v, EA_Check c, tgt) \<in> intra g)
         \<and> vr = aggregate_verdicts
                  ((\<lambda>ctx. classify_point classify c (lookup_context ar v ctx)) ` contexts_at ar v)"
  proof
    assume "\<exists>vs. (v, c, vs) \<in> set (classify_checks_ctx g ar classify) \<and> vr = aggregate_verdicts (snd ` vs)"
    then obtain vs where mem_vs: "(v, c, vs) \<in> set (classify_checks_ctx g ar classify)"
      and vr_eq: "vr = aggregate_verdicts (snd ` vs)" by blast
    from mem_vs classify_checks_ctx_mem_iff[OF assms] obtain tgt
      where tgt: "(v, EA_Check c, tgt) \<in> intra g"
        and vs_eq: "vs = (\<lambda>ctx. (ctx, classify_point classify c (lookup_context ar v ctx))) ` contexts_at ar v"
      by (metis (mono_tags, lifting))
    from vr_eq vs_eq have "vr = aggregate_verdicts
        ((\<lambda>ctx. classify_point classify c (lookup_context ar v ctx)) ` contexts_at ar v)"
      by (simp add: image_comp comp_def)
    with tgt show "(\<exists>tgt. (v, EA_Check c, tgt) \<in> intra g)
         \<and> vr = aggregate_verdicts
                  ((\<lambda>ctx. classify_point classify c (lookup_context ar v ctx)) ` contexts_at ar v)"
      by blast
  next
    assume "(\<exists>tgt. (v, EA_Check c, tgt) \<in> intra g)
         \<and> vr = aggregate_verdicts
                  ((\<lambda>ctx. classify_point classify c (lookup_context ar v ctx)) ` contexts_at ar v)"
    then obtain tgt where tgt: "(v, EA_Check c, tgt) \<in> intra g"
      and vr_eq: "vr = aggregate_verdicts
          ((\<lambda>ctx. classify_point classify c (lookup_context ar v ctx)) ` contexts_at ar v)"
      by blast
    let ?vs = "(\<lambda>ctx. (ctx, classify_point classify c (lookup_context ar v ctx))) ` contexts_at ar v"
    have mem_vs: "(v, c, ?vs) \<in> set (classify_checks_ctx g ar classify)"
      using classify_checks_ctx_mem_iff[OF assms] tgt by blast
    have "vr = aggregate_verdicts (snd ` ?vs)"
      using vr_eq by (simp add: image_comp comp_def)
    with mem_vs show "\<exists>vs. (v, c, vs) \<in> set (classify_checks_ctx g ar classify) \<and> vr = aggregate_verdicts (snd ` vs)"
      by blast
  qed
  finally show ?thesis .
qed

theorem classify_checks_ctx_decided_sound:
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Decided r) \<in> set (classify_checks_verdicts g ar classify)"
    and reach: "lookup_context ar v ctx = Lifted st"
    and known: "r \<noteq> Check_Unknown"
  shows "classify c st = r"
proof -
  have agg: "aggregate_verdicts ((\<lambda>c'. classify_point classify c (lookup_context ar v c')) ` contexts_at ar v)
               = Decided r"
    using classify_checks_verdicts_mem_iff[OF fin, of v c "Decided r" ar classify] mem by metis
  have covctx: "ctx \<in> contexts_at ar v" using reach by (rule lookup_context_LiftedD)
  have mem_img: "classify_point classify c (lookup_context ar v ctx)
          \<in> (\<lambda>c'. classify_point classify c (lookup_context ar v c')) ` contexts_at ar v"
    using covctx by blast
  have "classify_point classify c (lookup_context ar v ctx) = Dead
          \<or> classify_point classify c (lookup_context ar v ctx) = Decided r"
    using aggregate_verdicts_decided_dest[OF agg known] mem_img by blast
  with reach show ?thesis by simp
qed

theorem classify_checks_ctx_proved_sound:
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Decided Check_Proved) \<in> set (classify_checks_verdicts g r classify)"
    and reach: "lookup_context r v ctx = Lifted st"
  shows "classify c st = Check_Proved"
  using classify_checks_ctx_decided_sound[OF fin mem reach] by simp

theorem classify_checks_ctx_refuted_sound:
  assumes fin: "finite (intra g)"
    and mem: "(v, c, Decided Check_Refuted) \<in> set (classify_checks_verdicts g r classify)"
    and reach: "lookup_context r v ctx = Lifted st"
  shows "classify c st = Check_Refuted"
  using classify_checks_ctx_decided_sound[OF fin mem reach] by simp

end
