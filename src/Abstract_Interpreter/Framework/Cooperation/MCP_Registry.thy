theory MCP_Registry
  imports MCP_Spec Check_Answer
begin

section \<open>Registered analyses, run as one\<close>

text \<open>
  A registry assigns each analysis one field of a combined state: the component that
  runs on it, whether the field is live, what a solved field publishes, what a
  published value describes, whether it is empty, and how it answers a query. The
  registry runs any distinct, nonempty list of its analyses as one component
  (\<^const>\<open>mcp_combine\<close>), decides checks from the meet of their answers, and is
  sound whenever each field is. Nothing here depends on the language: the language
  enters through its evaluator \<open>ev\<close>, its return slot \<open>rv\<close>, the conversion and the
  global predicate of each program, and \<open>tx\<close>, the expression that asks for a
  check's truth value.
\<close>

locale mcp_registry =
  fixes ev :: "'e \<Rightarrow> ('vr \<Rightarrow> int) \<Rightarrow> int" and rv :: 'vr
    and pconv :: "'p \<Rightarrow> 'vr option \<Rightarrow> int \<Rightarrow> int" and pglob :: "'p \<Rightarrow> 'vr \<Rightarrow> bool"
    and tx :: "'e \<Rightarrow> 'e"
    and field :: "('vr \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> 'a \<Rightarrow> ('vr, 'e, 's::{semilattice_sup, order_bot} lifted) glocal_spec"
    and live :: "'a \<Rightarrow> 's \<Rightarrow> bool"
    and rd :: "('vr \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> 'v::bot"
    and val_gamma :: "'a \<Rightarrow> 'v \<Rightarrow> ('vr \<Rightarrow> int) set"
    and val_empty :: "'a \<Rightarrow> 'v \<Rightarrow> bool"
    and field_empty :: "'p \<Rightarrow> 'a \<Rightarrow> 's \<Rightarrow> bool"
    and answer :: "'a \<Rightarrow> 'v \<Rightarrow> 'e gchannel \<Rightarrow> 'e gquery \<Rightarrow> answer"
  assumes truth: "ev (tx c) s = (if truthy (ev c s) then 1 else 0)"
    and field_sound: "mcp_sem.gsound_local_spec ev rv (pconv p) (pglob p)
         (\<lambda>x. gamma_lift (val_gamma a) (map_lift (rd (pglob p)) x)) (field (pglob p) p a)"
    and field_frame: "a \<noteq> b \<Longrightarrow>
         mcp_frame (field \<G> p a) (\<lambda>x. gamma_lift (val_gamma b) (map_lift (rd \<G>) x))"
    and single_entry_field: "single_entry (field \<G> p a)"
    and dead: "\<not> live a r \<Longrightarrow> val_gamma a (rd \<G> r) = {}"
    and field_empty_rd: "field_empty p a r = val_empty a (rd (pglob p) r)"
    and val_empty_gamma: "val_empty a v \<Longrightarrow> val_gamma a v = {}"
    and val_gamma_bot: "val_gamma a \<bottom> = {}"
    and answer_sound: "s \<in> val_gamma a v \<Longrightarrow> geval_query.channel_holds ev ch s
         \<Longrightarrow> geval_holds ev q (answer a v ch q) s"
begin

abbreviation part_gamma :: "('vr \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 's lifted \<Rightarrow> ('vr \<Rightarrow> int) set" where
  "part_gamma \<G> a x \<equiv> gamma_lift (val_gamma a) (map_lift (rd \<G>) x)"

definition act_gamma :: "'a list \<Rightarrow> 'v \<Rightarrow> ('vr \<Rightarrow> int) set" where
  "act_gamma as v = (\<Inter>a \<in> set as. val_gamma a v)"

subsection \<open>Each analysis answers what it knows\<close>

text \<open>
  A field answers a query as its published value does, so an analysis written
  without a query handler becomes a provider on the combined state
  (\<^const>\<open>with_qry\<close>), as every Goblint analysis answers \<open>EvalInt\<close> from its domain.
  An answer may itself ask the channel, as Goblint's \<^verbatim>\<open>base\<close> asks about the operands
  of the expression it is asked about.
\<close>

definition part_answer ::
    "('vr \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'e gchannel \<Rightarrow> 's lifted \<Rightarrow> 'e gquery \<Rightarrow> answer" where
  "part_answer \<G> a ch x q = (case x of Bot \<Rightarrow> \<top> | Lifted r \<Rightarrow> answer a (rd \<G> r) ch q)"

lemma part_answer_sound:
  "s \<in> part_gamma \<G> a x \<Longrightarrow> geval_query.channel_holds ev ch s
     \<Longrightarrow> geval_holds ev q (part_answer \<G> a ch x q) s"
  by (cases x) (auto simp: part_answer_def intro: answer_sound)

definition mcp_field :: "('vr \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> 'a \<Rightarrow> ('vr, 'e, 's lifted) glocal_spec" where
  "mcp_field \<G> p a = with_qry (part_answer \<G> a) (field \<G> p a)"

lemma mcp_field_sound:
  "mcp_sem.gsound_local_spec ev rv (pconv p) (pglob p) (part_gamma (pglob p) a)
     (mcp_field (pglob p) p a)"
  unfolding mcp_field_def
  by (rule mcp_sem.with_qry_sound[OF field_sound]) (rule part_answer_sound)

lemma mcp_field_frame: "a \<noteq> b \<Longrightarrow> mcp_frame (mcp_field \<G> p a) (part_gamma \<G> b)"
  unfolding mcp_field_def by (rule with_qry_frame[OF field_frame])

subsection \<open>The active analyses, run as one\<close>

text \<open>
  The combined state is unreachable as soon as one active analysis says its field
  is, as Goblint's \<open>MCP\<close> raises \<open>Deadcode\<close> when one component does. The
  normalization changes no concretization: a field that describes nothing empties
  the intersection already.
\<close>

definition mcp_norm :: "'a list \<Rightarrow> 's lifted \<Rightarrow> 's lifted" where
  "mcp_norm as x =
     (case x of Bot \<Rightarrow> Bot | Lifted r \<Rightarrow> if list_all (\<lambda>a. live a r) as then x else Bot)"

lemma mcp_gamma_norm:
  "mcp_gamma (map (part_gamma \<G>) as) (mcp_norm as x) = mcp_gamma (map (part_gamma \<G>) as) x"
  by (cases x) (auto simp: mcp_norm_def mcp_gamma_def list_all_iff dest: dead)

definition mcp_comp :: "'a list \<Rightarrow> ('vr \<Rightarrow> bool) \<Rightarrow> 'p \<Rightarrow> ('vr, 'e, 's lifted) glocal_spec" where
  "mcp_comp as \<G> p = map_local_spec (mcp_norm as) (mcp_combine (map (mcp_field \<G> p) as))"

theorem mcp_comp_sound:
  assumes "distinct as" and "as \<noteq> []"
  shows "mcp_sem.gsound_local_spec ev rv (pconv p) (pglob p)
           (mcp_gamma (map (part_gamma (pglob p)) as)) (mcp_comp as (pglob p) p)"
proof -
  interpret S: mcp_sem ev rv "pconv p" "pglob p" .
  let ?gcs = "map (\<lambda>a. (part_gamma (pglob p) a, mcp_field (pglob p) p a)) as"
  have "S.gsound_local_spec (mcp_gamma (map fst ?gcs)) (mcp_combine (map snd ?gcs))"
    by (rule S.mcp_combine_sound)
       (auto simp: mcp_field_sound assms intro!: mcp_independent_map mcp_field_frame)
  then show ?thesis
    unfolding mcp_comp_def
    by (intro S.map_local_spec_sound) (simp_all add: comp_def mcp_gamma_norm)
qed

lemma single_entry_mcp_comp: "as \<noteq> [] \<Longrightarrow> single_entry (mcp_comp as \<G> p)"
  unfolding mcp_comp_def mcp_field_def
  by (intro single_entry_map_local_spec single_entry_mcp_combine)
     (auto simp: single_entry_field single_entry_with_qry)

subsection \<open>What the combined state publishes\<close>

lemma mcp_gamma_rd:
  "mcp_gamma (map (part_gamma \<G>) as) x = gamma_lift (act_gamma as) (map_lift (rd \<G>) x)"
  if "as \<noteq> []"
  using that by (cases x) (auto simp: mcp_gamma_def act_gamma_def)

lemma act_gamma_bot: "as \<noteq> [] \<Longrightarrow> act_gamma as \<bottom> = {}"
  by (auto simp: act_gamma_def val_gamma_bot)

definition mcp_emp :: "'a list \<Rightarrow> 'p \<Rightarrow> 's \<Rightarrow> bool" where
  "mcp_emp as p r = list_ex (\<lambda>a. field_empty p a r) as"

definition mcp_empty_v :: "'a list \<Rightarrow> 'v \<Rightarrow> bool" where
  "mcp_empty_v as v = list_ex (\<lambda>a. val_empty a v) as"

lemma mcp_emp_rd: "mcp_emp as p r = mcp_empty_v as (rd (pglob p) r)"
  by (simp add: mcp_emp_def mcp_empty_v_def field_empty_rd)

lemma mcp_empty_v_gamma: "mcp_empty_v as v \<Longrightarrow> act_gamma as v = {}"
  by (auto simp: mcp_empty_v_def act_gamma_def list_ex_iff dest: val_empty_gamma)

lemma sound_emptiness_mcp: "sound_emptiness (mcp_empty_v as) (act_gamma as)"
  by (rule sound_emptinessI) (rule mcp_empty_v_gamma)

subsection \<open>Deciding a check from every active analysis\<close>

text \<open>
  The combined answer meets the active analyses' answers, as \<open>MCP.query'\<close> does,
  and a check is decided from it as Goblint's \<open>assert\<close> reads \<open>eval_bool\<close>. The
  question goes through the channel the combined answer closes over itself
  (\<^const>\<open>ask_rec\<close>), so an answer that asks about a subexpression reaches every
  active analysis, and a query cycle answers \<open>\<top>\<close>.
\<close>

definition mcp_answer :: "'a list \<Rightarrow> 'e gchannel \<Rightarrow> 'v \<Rightarrow> 'e gquery \<Rightarrow> answer" where
  "mcp_answer as ch v q = fold (\<lambda>a r. r \<sqinter> answer a v ch q) as \<top>"

lemma mcp_answer_fold_sound:
  "\<forall>a \<in> set as. s \<in> val_gamma a v \<Longrightarrow> geval_query.channel_holds ev ch s
   \<Longrightarrow> geval_holds ev q r s \<Longrightarrow> geval_holds ev q (fold (\<lambda>a r. r \<sqinter> answer a v ch q) as r) s"
  by (induction as arbitrary: r) (auto intro: geval_query.inf_sound answer_sound)

lemma mcp_answer_sound:
  "s \<in> act_gamma as v \<Longrightarrow> geval_query.channel_holds ev ch s
     \<Longrightarrow> geval_holds ev q (mcp_answer as ch v q) s"
  unfolding mcp_answer_def act_gamma_def by (rule mcp_answer_fold_sound) auto

definition mcp_ask :: "'a list \<Rightarrow> 'v \<Rightarrow> 'e gchannel" where
  "mcp_ask as v = ask_rec (mcp_answer as) query_depth {} v"

lemma mcp_ask_sound:
  assumes s: "s \<in> act_gamma as v"
  shows "geval_query.channel_holds ev (mcp_ask as v) s"
proof -
  interpret S: mcp_sem ev rv "\<lambda>_ n. n" "\<lambda>_. True" .
  show ?thesis
    unfolding mcp_ask_def by (rule S.ask_rec_sound) (rule mcp_answer_sound[OF s])
qed

definition mcp_classify :: "'a list \<Rightarrow> 'e \<Rightarrow> 'v \<Rightarrow> check_result" where
  "mcp_classify as = answer_check tx (mcp_ask as)"

lemma mcp_classify_sound:
  assumes s: "s \<in> act_gamma as v"
  shows mcp_classify_proved: "mcp_classify as c v = Check_Proved \<Longrightarrow> truthy (ev c s)"
    and mcp_classify_refuted: "mcp_classify as c v = Check_Refuted \<Longrightarrow> \<not> truthy (ev c s)"
  using answer_check_gsound[where ev = ev and tx = tx and q = "mcp_ask as" and c = c and v = v,
      OF truth geval_query.channel_holdsD[OF mcp_ask_sound[OF s]]]
  by (simp_all add: mcp_classify_def)

end

end
