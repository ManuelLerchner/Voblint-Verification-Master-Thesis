theory Example_Entry_Store_Context_Precision
  imports
    "Voblint_Analysis.TD_Side_Eff_Ctx_Sound"
    "Voblint_Analysis.Sign_Domain"
    "Voblint_Analysis.Analysis_GraphViz"
    "Voblint_IMP2.IMP2_Notation"
begin

section \<open>Compiled entry-store witness\<close>

text \<open>
  The program has one call at the compiled CFG entry.  The initial set contains
  the two concrete caller stores that a two-call program would pass to the
  procedure entry: one with \<open>Gx = 0\<close>, one with \<open>Gx = 1\<close>.  The context
  split is therefore exactly the entry-store split used by
  @{thm [source] semantic_entry_store_ctx_analysis_sound}.
\<close>

definition entry_ctx_program :: imp_prog where
  "entry_ctx_program = \<lbrakk>
     int Gx, G;
     void f() { G := Gx }
     void main() { f() }
   \<rbrakk>"

definition entry_ctx_g :: cfg where
  "entry_ctx_g = compile_prog (prog_table entry_ctx_program)
                   (prog_procs entry_ctx_program) (prog_main entry_ctx_program)"

lemma entry_ctx_program_parts:
  shows "prog_procs entry_ctx_program = [''f'']"
    and "prog_main entry_ctx_program = Call ''f''"
  by (simp_all add: entry_ctx_program_def)

lemma entry_ctx_g_full:
  "entry_ctx_g = mk_cfg 2 3
     {(0, EA_Assign ''G'' (V ''Gx''), 1),
      (2, EA_Enter, 0)}
     {(2, 1, 3)}"
  by (simp add: entry_ctx_g_def entry_ctx_program_def compile_eval_simps Let_def; blast)

lemma entry_ctx_g_structure:
  shows "cfg_entry entry_ctx_g = 2"
    and "cfg_exit entry_ctx_g = 3"
    and "edges entry_ctx_g =
       {(0, EA_Assign ''G'' (V ''Gx''), 1),
        (2, EA_Enter, 0)}"
    and "combines entry_ctx_g = {(2, 1, 3)}"
  by (simp_all add: entry_ctx_g_full)

section \<open>Entry stores\<close>

definition s0 :: store where
  "s0 = (\<lambda>_. 0)"

definition s1 :: store where
  "s1 = (\<lambda>_. 0)(''Gx'' := 1)"

definition S01 :: "store set" where
  "S01 = {s0, s1}"

definition ent0 :: store where
  "ent0 = enter_state s0"

definition ent1 :: store where
  "ent1 = enter_state s1"

definition body0 :: store where
  "body0 = ent0(''G'' := 0)"

definition body1 :: store where
  "body1 = ent1(''G'' := 1)"

lemma global_names[simp]:
  "is_global ''G''" "is_global ''Gx''"
  by (simp_all add: is_global_def)

lemma entry_stores[simp]:
  "ent0 = s0" "ent1 = s1"
  by (simp_all add: ent0_def ent1_def s0_def s1_def enter_state_def is_global_def fun_eq_iff)

lemma body_values[simp]:
  "body0 ''G'' = 0" "body1 ''G'' = 1"
  "body0 ''Gx'' = 0" "body1 ''Gx'' = 1"
  by (simp_all add: body0_def body1_def s0_def s1_def)

lemma body_distinct[simp]: "body0 \<noteq> body1"
proof
  assume "body0 = body1"
  then have "body0 ''G'' = body1 ''G''" by simp
  then show False by simp
qed

lemma entry_store_distinct[simp]: "ent0 \<noteq> ent1"
proof
  assume "ent0 = ent1"
  then have "ent0 ''Gx'' = ent1 ''Gx''" by simp
  then show False by (simp add: s0_def s1_def)
qed

section \<open>Callee traces\<close>

definition rho0 :: trace where
  "rho0 = [ent0, body0]"

definition rho1 :: trace where
  "rho1 = [ent1, body1]"

lemma ent0_proc_entry:
  "trace_witness entry_ctx_g S01 0 [ent0]"
proof (rule trace_witness.proc_entry)
  show "(cfg_entry entry_ctx_g, EA_Enter, 0) \<in> edges entry_ctx_g"
    by (simp add: entry_ctx_g_structure)
  show "ent0 \<in> enter_state ` S01"
    using S01_def ent0_def by auto
qed

lemma ent1_proc_entry:
  "trace_witness entry_ctx_g S01 0 [ent1]"
proof (rule trace_witness.proc_entry)
  show "(cfg_entry entry_ctx_g, EA_Enter, 0) \<in> edges entry_ctx_g"
    by (simp add: entry_ctx_g_structure)
  show "ent1 \<in> enter_state ` S01"
    using S01_def ent1_def by auto
qed

lemma rho0_witness:
  "trace_witness entry_ctx_g S01 1 rho0"
proof -
  have step: "edge_step (EA_Assign ''G'' (V ''Gx'')) ent0 = Some body0"
    by (simp add: body0_def s0_def)
  have "trace_witness entry_ctx_g S01 1 ([ent0] @ [body0])"
    by (rule trace_witness.edge[where u = 0 and a = "EA_Assign ''G'' (V ''Gx'')"])
      (use ent0_proc_entry step in \<open>auto simp: entry_ctx_g_structure\<close>)
  then show ?thesis by (simp add: rho0_def)
qed

lemma rho1_witness:
  "trace_witness entry_ctx_g S01 1 rho1"
proof -
  have step: "edge_step (EA_Assign ''G'' (V ''Gx'')) ent1 = Some body1"
    by (simp add: body1_def s1_def)
  have "trace_witness entry_ctx_g S01 1 ([ent1] @ [body1])"
    by (rule trace_witness.edge[where u = 0 and a = "EA_Assign ''G'' (V ''Gx'')"])
      (use ent1_proc_entry step in \<open>auto simp: entry_ctx_g_structure\<close>)
  then show ?thesis by (simp add: rho1_def)
qed

lemma rho_in_plain:
  "rho0 \<in> cfg_collect_trace entry_ctx_g S01 1"
  "rho1 \<in> cfg_collect_trace entry_ctx_g S01 1"
  using rho0_witness rho1_witness unfolding cfg_collect_trace_def by auto

definition env_ctx0 :: "vname \<Rightarrow> sign" where
  "env_ctx0 = (\<lambda>x. if x = ''G'' then SZero else STop)"

definition env_ctx1 :: "vname \<Rightarrow> sign" where
  "env_ctx1 = (\<lambda>x. if x = ''G'' then SPos else STop)"

lemma node2_shape:
  assumes "trace_witness entry_ctx_g S01 2 tr"
  shows "tr = [ent0] \<or> tr = [ent1]"
  using assms
proof (cases rule: trace_witness.cases)
  case (entry s)
  then show ?thesis by (auto simp: entry_ctx_g_structure S01_def)
next
  case (proc_entry s)
  then show ?thesis by (auto simp: entry_ctx_g_structure)
next
  case (edge u a tr' s')
  then show ?thesis by (auto simp: entry_ctx_g_structure)
next
  case (combine c ex tau rho)
  then show ?thesis by (auto simp: entry_ctx_g_structure)
qed

lemma node0_shape:
  assumes "trace_witness entry_ctx_g S01 0 tr"
  shows "(hd tr = ent0 \<and> last tr = ent0) \<or> (hd tr = ent1 \<and> last tr = ent1)"
  using assms
proof (cases rule: trace_witness.cases)
  case (entry s)
  then show ?thesis by (auto simp: entry_ctx_g_structure)
next
  case (proc_entry s)
  then show ?thesis
    by (auto simp: entry_ctx_g_structure S01_def image_iff ent0_def ent1_def
        enter_state_def is_global_def fun_eq_iff s0_def s1_def)
next
  case (edge u a tr' s')
  then have u: "u = 2" and a: "a = EA_Enter"
    and step: "s' = enter_state (last tr')" and tr: "tr = tr' @ [s']"
    by (auto simp: entry_ctx_g_structure)
  have prev: "trace_witness entry_ctx_g S01 2 tr'"
    using edge(3) u by simp
  have tr'_shape: "tr' = [ent0] \<or> tr' = [ent1]"
    by (rule node2_shape[OF prev])
  show ?thesis
    using tr'_shape a step tr
    by (auto simp: enter_state_def is_global_def fun_eq_iff s0_def s1_def)
next
  case (combine c ex tau rho)
  then show ?thesis by (auto simp: entry_ctx_g_structure)
qed

lemma node1_shape:
  assumes "trace_witness entry_ctx_g S01 1 tr"
  shows "(hd tr = ent0 \<and> last tr = body0) \<or> (hd tr = ent1 \<and> last tr = body1)"
  using assms
proof (cases rule: trace_witness.cases)
  case (entry s)
  then show ?thesis by (auto simp: entry_ctx_g_structure)
next
  case (proc_entry s)
  then show ?thesis by (auto simp: entry_ctx_g_structure)
next
  case (edge u a tr' s')
  then have prev: "trace_witness entry_ctx_g S01 0 tr'"
    and tr: "tr = tr' @ [s']"
    and step: "edge_step (EA_Assign ''G'' (V ''Gx'')) (last tr') = Some s'"
    by (auto simp: entry_ctx_g_structure)
  have prev_shape: "(hd tr' = ent0 \<and> last tr' = ent0) \<or> (hd tr' = ent1 \<and> last tr' = ent1)"
    by (rule node0_shape[OF prev])
  have ne: "tr' \<noteq> []" by (rule trace_witness_nonempty[OF prev])
  show ?thesis
    using prev_shape step ne tr by (auto simp: body0_def body1_def s0_def s1_def)
next
  case (combine c ex tau rho)
  then show ?thesis by (auto simp: entry_ctx_g_structure)
qed

lemma ctx0_sound:
  "cfg_collect_ctx entry_store_dg (\<subseteq>) entry_ctx_g S01 1 {ent0} \<subseteq> \<lbrakk>env_ctx0\<rbrakk>"
  unfolding cfg_collect_ctx_def alpha_ctx_def reaching_compat_def cfg_collect_trace_def
proof (rule subsetI)
  fix s
  assume "s \<in> {last tr |tr. tr \<in> Collect (trace_witness entry_ctx_g S01 1)
      \<and> entry_store_dg tr \<subseteq> {ent0}}"
  then obtain tr where tr: "trace_witness entry_ctx_g S01 1 tr"
    and ctx: "entry_store_dg tr \<subseteq> {ent0}"
    and s: "s = last tr"
    by blast
  have ne: "tr \<noteq> []" by (rule trace_witness_nonempty[OF tr])
  from ctx ne have hd: "hd tr = ent0" by (simp add: entry_store_dg_def)
  have shape: "(hd tr = ent0 \<and> last tr = body0) \<or> (hd tr = ent1 \<and> last tr = body1)"
    by (rule node1_shape[OF tr])
  have not1: "hd tr \<noteq> ent1"
    using hd entry_store_distinct by auto
  have last0: "last tr = body0"
    using shape not1 by auto
  show "s \<in> \<lbrakk>env_ctx0\<rbrakk>"
    using s last0 by (auto simp: gamma_state_def env_ctx0_def)
qed

lemma ctx1_sound:
  "cfg_collect_ctx entry_store_dg (\<subseteq>) entry_ctx_g S01 1 {ent1} \<subseteq> \<lbrakk>env_ctx1\<rbrakk>"
  unfolding cfg_collect_ctx_def alpha_ctx_def reaching_compat_def cfg_collect_trace_def
proof (rule subsetI)
  fix s
  assume "s \<in> {last tr |tr. tr \<in> Collect (trace_witness entry_ctx_g S01 1)
      \<and> entry_store_dg tr \<subseteq> {ent1}}"
  then obtain tr where tr: "trace_witness entry_ctx_g S01 1 tr"
    and ctx: "entry_store_dg tr \<subseteq> {ent1}"
    and s: "s = last tr"
    by blast
  have ne: "tr \<noteq> []" by (rule trace_witness_nonempty[OF tr])
  from ctx ne have hd: "hd tr = ent1" by (simp add: entry_store_dg_def)
  have shape: "(hd tr = ent0 \<and> last tr = body0) \<or> (hd tr = ent1 \<and> last tr = body1)"
    by (rule node1_shape[OF tr])
  have not0: "hd tr \<noteq> ent0"
    using hd entry_store_distinct by auto
  have last1: "last tr = body1"
    using shape not0 by auto
  show "s \<in> \<lbrakk>env_ctx1\<rbrakk>"
    using s last1 by (auto simp: gamma_state_def env_ctx1_def)
qed



section \<open>Strict precision against monovariant reads\<close>

lemma sign_zero_pos_not_singleton:
  assumes zero: "0 \<in> gamma_sign sv"
  assumes one: "1 \<in> gamma_sign sv"
  shows "gamma_sign SZero \<subset> gamma_sign sv"
    and "gamma_sign SPos \<subset> gamma_sign sv"
proof -
  have "sv = SNonNeg \<or> sv = STop"
    using zero one by (cases sv) auto
  then show "gamma_sign SZero \<subset> gamma_sign sv"
    and "gamma_sign SPos \<subset> gamma_sign sv"
    apply (metis empty_subsetI gamma_sign.simps(4) insert_subset one psubsetI singletonD zero
        zero_neq_one)
    using \<open>sv = SNonNeg \<or> sv = STop\<close> meet_sign_sound by auto
qed

 
lemma flat_g_strictly_coarser:
  assumes flat: "alpha_last (cfg_collect_trace entry_ctx_g S01 1) \<subseteq> \<lbrakk>envf\<rbrakk>"
  shows "gamma_sign SZero \<subset> gamma_sign (envf ''G'')"
    and "gamma_sign SPos \<subset> gamma_sign (envf ''G'')"
proof -
  have b0: "body0 \<in> \<lbrakk>envf\<rbrakk>"
    using flat rho_in_plain(1) unfolding alpha_last_def by (auto simp: rho0_def)
  have b1: "body1 \<in> \<lbrakk>envf\<rbrakk>"
    using flat rho_in_plain(2) unfolding alpha_last_def by (auto simp: rho1_def)
  have zero: "0 \<in> gamma_sign (envf ''G'')"
  proof -
    have all: "\<forall>x. body0 x \<in> gamma_sign (envf x)"
      using b0 by (simp add: gamma_state_def)
    then have "body0 ''G'' \<in> gamma_sign (envf ''G'')"
      by blast
    then show ?thesis by simp
  qed
  have one: "1 \<in> gamma_sign (envf ''G'')"
  proof -
    have all: "\<forall>x. body1 x \<in> gamma_sign (envf x)"
      using b1 by (simp add: gamma_state_def)
    then have "body1 ''G'' \<in> gamma_sign (envf ''G'')"
      by blast
    then show ?thesis by simp
  qed

  show "gamma_sign SZero \<subset> gamma_sign (envf ''G'')"
    by (rule sign_zero_pos_not_singleton(1)[OF zero one])
  show "gamma_sign SPos \<subset> gamma_sign (envf ''G'')"
    by (rule sign_zero_pos_not_singleton(2)[OF zero one])
qed


theorem entry_store_context_precision_witness:
  assumes flat: "alpha_last (cfg_collect_trace entry_ctx_g S01 1) \<subseteq> \<lbrakk>envf\<rbrakk>"
  shows "cfg_collect_ctx entry_store_dg (\<subseteq>) entry_ctx_g S01 1 {ent0} \<subseteq> \<lbrakk>env_ctx0\<rbrakk>
       \<and> cfg_collect_ctx entry_store_dg (\<subseteq>) entry_ctx_g S01 1 {ent1} \<subseteq> \<lbrakk>env_ctx1\<rbrakk>
       \<and> gamma_sign (env_ctx0 ''G'') \<subset> gamma_sign (envf ''G'')
       \<and> gamma_sign (env_ctx1 ''G'') \<subset> gamma_sign (envf ''G'')"
  using ctx0_sound ctx1_sound flat_g_strictly_coarser[OF flat]
  by (simp add: env_ctx0_def env_ctx1_def)

text \<open>
  This example demonstrates the precision benefit of semantic entry-store
  contexts. A context-insensitive (monovariant) analysis must merge both
  procedure entries and therefore infers a single abstract value for \<open>G\<close> that
  covers both executions. In contrast, the semantic context analysis partitions
  the execution by entry context, proving \<open>G = 0\<close> in the context \<open>{ent0}\<close> and
  \<open>G = 1\<close> in the context \<open>{ent1}\<close>. Consequently,
  @{thm [source] entry_store_context_precision_witness} establishes a strict
  precision improvement over the corresponding monovariant analysis.
\<close>

section \<open>Debug GraphViz rendering for entry-store contexts\<close>

text \<open>
  The generic context debug renderer from @{theory Voblint_Analysis.Analysis_GraphViz}
  receives the CFG, context-label lines, and a separate per-context globals box.
\<close>

definition entry_ctx_debug_dot :: string where
  "entry_ctx_debug_dot =
     ctx_debug_graphviz_same_ctx_cfg_show_globals_default
       (\<lambda>s. [''context Gx='' @ show_val s])
       (\<lambda>s. [''Gx='' @ show_val s, ''G='' @ show_val s])
       [SZero, SPos] entry_ctx_g"

definition entry_ctx_debug_dot_lit :: String.literal where
  "entry_ctx_debug_dot_lit = String.implode entry_ctx_debug_dot"

ML_val \<open>
  writeln (@{code entry_ctx_debug_dot_lit})
\<close>

end
