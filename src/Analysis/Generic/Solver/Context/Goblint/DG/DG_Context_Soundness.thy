theory DG_Context_Soundness
  imports DG_Soundness
begin

section \<open>Context-keyed DG soundness (feasibility slice)\<close>

text \<open>
  \<open>DG_Soundness\<close> fixes the context to \<^typ>\<open>unit\<close>: the accessors \<open>dg_D\<close> / \<open>dg_G\<close> read the
  single slots \<open>Inl (v, ())\<close> / \<open>Inr ()\<close>, and \<open>dg_postfix_collect_sound\<close> is stated over
  them.  This theory shows the collecting-soundness argument is in fact
  \<^emph>\<open>context-agnostic\<close>: it depends on the solution only through a per-point answer reader
  \<open>dD :: pp \<Rightarrow> 'D\<close> and a global reader \<open>dG :: 'G\<close>, never on how those are extracted from
  \<open>sigma\<close>.

  The reader lemma below is exactly \<open>dg_postfix_collect_sound\<close> with the two accessors
  abstracted.  Instantiating \<open>dD\<close>/\<open>dG\<close> at context-keyed slots (\<open>Inl (v, ctx)\<close> /
  \<open>Inr ctx\<close>) yields per-context soundness for free --- one theorem per reachable
  context, with no new locale assumption.  This is the \<^emph>\<open>own-slot\<close> (diagonal,
  \<open>gcmp = (=)\<close>) read the maintained keyed examples use.  Cross-context edges (an
  \<^const>\<open>EA_Enter\<close> that selects the callee context from the caller state, or a combine
  that reads a different context's global) are \<^emph>\<open>not\<close> covered here and remain the
  route / \<open>side_env_cmp\<close> work catalogued in the feasibility report.
\<close>

context sound_dg_spec
begin

subsection \<open>Context-agnostic collecting soundness\<close>

text \<open>
  The body of \<open>dg_postfix_collect_sound\<close>, with the solution reader made explicit.
  \<open>dD v\<close> is the answer read at point \<open>v\<close>; \<open>dG\<close> is the global read shared along the
  covered region.  No finiteness hypothesis is needed: the bound is a post-fixpoint
  closure over \<open>cfg_collect_semantic_postfix\<close>.
\<close>

lemma collect_sound_reader:
  fixes dD :: "pp \<Rightarrow> 'D" and dG :: "'G"
  assumes entryD: "s0d \<le> dD (cfg_entry g)"
    and entryG: "s0g \<le> dG"
    and edgeD: "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow>
        snd (dg_spec_step S a (dD u) dG) \<le> dD v"
    and edgeG: "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow>
        fst (dg_spec_step S a (dD u) dG) \<le> dG"
    and combD: "\<And>cc ex v dst. (cc, ex, v, dst) \<in> combines g \<Longrightarrow>
        snd (dgs_combine S dst (dD cc) (dD ex) dG) \<le> dD v"
    and combG: "\<And>cc ex v dst. (cc, ex, v, dst) \<in> combines g \<Longrightarrow>
        fst (dgs_combine S dst (dD cc) (dD ex) dG) \<le> dG"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "cfg_collect g S0 v \<subseteq> gammaDG (dD v) dG"
proof (rule cfg_collect_semantic_postfix)
  show "S0 \<subseteq> gammaDG (dD (cfg_entry g)) dG"
  proof -
    have "gammaDG s0d s0g \<subseteq> gammaDG (dD (cfg_entry g)) dG"
      by (rule gammaDG_mono[OF entryD entryG])
    then show ?thesis using sound0 by blast
  qed
next
  fix u a w s
  assume edge: "(u, a, w) \<in> edges g"
    and sin: "s \<in> edge_collect a (gammaDG (dD u) dG)"
  obtain g' d' where step:
      "dg_spec_step S a (dD u) dG = (g', d')"
    by (cases "dg_spec_step S a (dD u) dG") blast
  have "s \<in> (case dg_spec_step S a (dD u) dG of (g', d') \<Rightarrow> gammaDG d' g')"
    by (rule step_sound[THEN subsetD, OF sin])
  then have out: "s \<in> gammaDG d' g'" using step by simp
  have "d' \<le> dD w" and "g' \<le> dG"
    using edgeD[OF edge] edgeG[OF edge] step by simp_all
  then have "gammaDG d' g' \<subseteq> gammaDG (dD w) dG"
    by (rule gammaDG_mono)
  then show "s \<in> gammaDG (dD w) dG" using out by blast
next
  fix cc ex w dst s t
  assume comb: "(cc, ex, w, dst) \<in> combines g"
    and sin: "s \<in> gammaDG (dD cc) dG"
    and tin: "t \<in> gammaDG (dD ex) dG"
  obtain g' d' where cmb:
      "dgs_combine S dst (dD cc) (dD ex) dG = (g', d')"
    by (cases "dgs_combine S dst (dD cc) (dD ex) dG") blast
  have "combine_collect dst s t \<in>
      (case dgs_combine S dst (dD cc) (dD ex) dG of (g', d') \<Rightarrow> gammaDG d' g')"
    by (rule combine_sound[OF sin tin])
  then have out: "combine_collect dst s t \<in> gammaDG d' g'" using cmb by simp
  have "d' \<le> dD w" and "g' \<le> dG"
    using combD[OF comb] combG[OF comb] cmb by simp_all
  then have "gammaDG d' g' \<subseteq> gammaDG (dD w) dG"
    by (rule gammaDG_mono)
  then show "combine_collect dst s t \<in> gammaDG (dD w) dG" using out by blast
qed

subsection \<open>Context-keyed accessors and per-context soundness\<close>

text \<open>
  Keyed slots: a solution ranges over \<^typ>\<open>pp \<times> 'c + 'c\<close> unknowns.  Point \<open>v\<close> under
  context \<open>ctx\<close> answers in \<open>Inl (v, ctx)\<close>; context \<open>ctx\<close>'s own global lives in
  \<open>Inr ctx\<close> (the \<open>gkey = id\<close>, \<open>gcmp = (=)\<close> diagonal).  These generalise the \<^typ>\<open>unit\<close>
  accessors of \<open>DG_Soundness\<close>, which are the \<open>ctx = ()\<close> case.
\<close>

definition dg_D_c ::
  "(pp \<times> 'c + 'c \<Rightarrow> ('D, 'G) dg_state) \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> 'D"
where
  "dg_D_c sigma ctx v = locals (sigma (Inl (v, ctx)))"

definition dg_G_c ::
  "(pp \<times> 'c + 'c \<Rightarrow> ('D, 'G) dg_state) \<Rightarrow> 'c \<Rightarrow> 'G"
where
  "dg_G_c sigma ctx = globs (sigma (Inr ctx))"

definition dg_gamma_c ::
  "(pp \<times> 'c + 'c \<Rightarrow> ('D, 'G) dg_state) \<Rightarrow> 'c \<Rightarrow> pp \<Rightarrow> store set"
where
  "dg_gamma_c sigma ctx v = gammaDG (dg_D_c sigma ctx v) (dg_G_c sigma ctx)"

text \<open>
  A within-context post-fixpoint at context \<open>ctx\<close>: every edge and same-context combine
  is closed at \<open>ctx\<close>'s slots.  The absence of an \<^const>\<open>EA_Enter\<close> that changes context
  is what keeps the global read a single slot; that is the boundary of this slice.
\<close>

definition dg_postfix_c ::
  "cfg \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> 'G \<Rightarrow> (pp \<times> 'c + 'c \<Rightarrow> ('D, 'G) dg_state) \<Rightarrow> bool"
where
  "dg_postfix_c g ctx s0d s0g sigma \<longleftrightarrow>
     s0d \<le> dg_D_c sigma ctx (cfg_entry g) \<and>
     s0g \<le> dg_G_c sigma ctx \<and>
     (\<forall>u a v. (u, a, v) \<in> edges g \<longrightarrow>
        snd (dg_spec_step S a (dg_D_c sigma ctx u) (dg_G_c sigma ctx))
          \<le> dg_D_c sigma ctx v) \<and>
     (\<forall>u a v. (u, a, v) \<in> edges g \<longrightarrow>
        fst (dg_spec_step S a (dg_D_c sigma ctx u) (dg_G_c sigma ctx))
          \<le> dg_G_c sigma ctx) \<and>
     (\<forall>cc ex v dst. (cc, ex, v, dst) \<in> combines g \<longrightarrow>
        snd (dgs_combine S dst (dg_D_c sigma ctx cc) (dg_D_c sigma ctx ex)
              (dg_G_c sigma ctx)) \<le> dg_D_c sigma ctx v) \<and>
     (\<forall>cc ex v dst. (cc, ex, v, dst) \<in> combines g \<longrightarrow>
        fst (dgs_combine S dst (dg_D_c sigma ctx cc) (dg_D_c sigma ctx ex)
              (dg_G_c sigma ctx)) \<le> dg_G_c sigma ctx)"

theorem dg_postfix_c_collect_sound:
  assumes pf: "dg_postfix_c g ctx s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "cfg_collect g S0 v \<subseteq> dg_gamma_c sigma ctx v"
proof -
  from pf have
      e1: "s0d \<le> dg_D_c sigma ctx (cfg_entry g)"
    and e2: "s0g \<le> dg_G_c sigma ctx"
    and e3: "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow>
        snd (dg_spec_step S a (dg_D_c sigma ctx u) (dg_G_c sigma ctx)) \<le> dg_D_c sigma ctx v"
    and e4: "\<And>u a v. (u, a, v) \<in> edges g \<Longrightarrow>
        fst (dg_spec_step S a (dg_D_c sigma ctx u) (dg_G_c sigma ctx)) \<le> dg_G_c sigma ctx"
    and e5: "\<And>cc ex v dst. (cc, ex, v, dst) \<in> combines g \<Longrightarrow>
        snd (dgs_combine S dst (dg_D_c sigma ctx cc) (dg_D_c sigma ctx ex) (dg_G_c sigma ctx))
          \<le> dg_D_c sigma ctx v"
    and e6: "\<And>cc ex v dst. (cc, ex, v, dst) \<in> combines g \<Longrightarrow>
        fst (dgs_combine S dst (dg_D_c sigma ctx cc) (dg_D_c sigma ctx ex) (dg_G_c sigma ctx))
          \<le> dg_G_c sigma ctx"
    unfolding dg_postfix_c_def by blast+
  show ?thesis
    unfolding dg_gamma_c_def
    by (rule collect_sound_reader
          [where dD = "dg_D_c sigma ctx" and dG = "dg_G_c sigma ctx",
           OF e1 e2 e3 e4 e5 e6 sound0])
qed

text \<open>
  The \<^typ>\<open>unit\<close> theorem of \<open>DG_Soundness\<close> is the \<open>ctx = ()\<close> instance: keyed accessors
  at \<open>()\<close> are the original accessors, and \<open>dg_postfix_c\<close> at \<open>()\<close> is \<open>dg_postfix\<close>.
\<close>

lemma dg_D_c_unit: "dg_D_c sigma () v = dg_D sigma v"
  by (simp add: dg_D_c_def dg_D_def)

lemma dg_G_c_unit: "dg_G_c sigma () = dg_G sigma"
  by (simp add: dg_G_c_def dg_G_def)

lemma dg_postfix_c_unit: "dg_postfix_c g () = dg_postfix g"
  by (simp add: fun_eq_iff dg_postfix_c_def dg_postfix_def dg_D_c_unit dg_G_c_unit)

end

end
