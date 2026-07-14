theory Ctx_Collect_Backbone
  imports "Voblint_CFG.CFG_Collect_Trace"
begin

section \<open>Context-sliced collecting soundness over an opaque meaning\<close>

text \<open>
  The single canonical trace backbone for context-sensitive collecting soundness.
  Every context spine --- the homogeneous keyed read (\<open>side_env_cmp\<close>), the
  seeded-clean local read (R_read), the two-gamma DG endpoint --- runs the \<^emph>\<open>same\<close>
  trace induction over \<^const>\<open>cfg_collect_ctx\<close>.  That induction never inspects the
  abstract-state structure of a read: it uses only the \<^emph>\<open>meaning set\<close> at each
  (point, context) pair, and a routing read the context selector \<open>rt\<close> consumes.

  Abstracting the meaning to \<open>M :: pp \<times> 'c \<Rightarrow> store set\<close> and the routing read to
  \<open>rd :: pp \<times> 'c \<Rightarrow> 'r\<close> makes the backbone carrier-agnostic: each spine is an
  instance, differing only in how \<open>M\<close> reads a solution (single homogeneous
  concretization \<open>[[renv sigma (v, ctx)]]\<close>, or the DG \<open>gammaDG (dD v) dG\<close>).  Both the
  homogeneous \<open>post_fixpoint_sound_at_ctx_semantic_generic\<close> and the DG
  \<open>sound_dg_spec.dg_collect_ctx_sound\<close> are corollaries.
\<close>

subsection \<open>Trace backbone\<close>

theorem trace_ctx_sound_meaning:
  fixes M :: "pp \<times> 'c \<Rightarrow> store set"
    and rd :: "pp \<times> 'c \<Rightarrow> 'r"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'r \<Rightarrow> 'c"
    and entdg :: "store \<Rightarrow> 'c"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and S :: "store set" and g :: cfg
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> M (cfg_entry g, ctx)"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> M (v, ctx)"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> M (u, ctx) \<Longrightarrow> s' \<in> M (v, ctx)"
    and COMB: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> M (cl, ctx)
        \<Longrightarrow> last rho \<in> M (ex, rt cl ctx (rd (cl, ctx)))
        \<Longrightarrow> <last tau|last rho> \<in> M (v, ctx)"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> M (cl, ctx)
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (rd (cl, ctx)))"
    and wit: "trace_witness g S v tr"
    and compat: "cmp (dg tr) ctx"
  shows "last tr \<in> M (v, ctx)"
proof -
  from wit have "cmp (dg tr) ctx \<Longrightarrow> last tr \<in> M (v, ctx)"
  proof (induction arbitrary: ctx rule: trace_witness.induct)
    case (entry v s)
    have "s \<in> M (cfg_entry g, ctx)"
      using ENTRY entry.hyps entry.prems by blast
    thus ?case using entry.hyps by simp
  next
    case (proc_entry v s)
    have "s \<in> M (v, ctx)"
      using PROC_ENTRY proc_entry.hyps proc_entry.prems by blast
    thus ?case by simp
  next
    case (edge u a v tr s')
    have tr_ne: "tr \<noteq> []" using edge.hyps(2) by (rule trace_witness_nonempty)
    have ctr: "cmp (dg tr) ctx"
      by (rule DG_INTRA[OF tr_ne edge.prems])
    have lt: "last tr \<in> M (u, ctx)" using edge.IH[OF ctr] .
    have "s' \<in> M (v, ctx)" using EDGE edge.hyps lt by blast
    thus ?case by simp
  next
    case (combine cl ex v tau rho)
    have tau_ne: "tau \<noteq> []" using combine.hyps(2) by (rule trace_witness_nonempty)
    have rho_ne: "rho \<noteq> []" using combine.hyps(3) by (rule trace_witness_nonempty)
    have ctau: "cmp (dg tau) ctx"
      using combine.prems DG_RETURN[OF tau_ne, of rho] by simp
    have caller_sound: "last tau \<in> M (cl, ctx)"
      using combine.IH(1)[OF ctau] .
    have crho: "cmp (dg rho) (rt cl ctx (rd (cl, ctx)))"
    proof -
      have "dg rho = entdg (last tau)" using DG_CALLEE[OF rho_ne combine.hyps(4)] .
      thus ?thesis using ENTER_MONO[OF caller_sound] by simp
    qed
    have callee_sound: "last rho \<in> M (ex, rt cl ctx (rd (cl, ctx)))"
      using combine.IH(2)[OF crho] .
    have "<last tau|last rho> \<in> M (v, ctx)"
      using COMB[OF combine.hyps(1) caller_sound callee_sound] .
    thus ?case
      by (metis last_appendR snoc_eq_iff_butlast)
  qed
  thus ?thesis using compat by blast
qed

subsection \<open>Collecting form\<close>

text \<open>
  Wrapping the trace backbone through \<^const>\<open>cfg_collect_ctx\<close> once, for every spine.
\<close>

theorem collect_ctx_sound_meaning:
  fixes M :: "pp \<times> 'c \<Rightarrow> store set"
    and rd :: "pp \<times> 'c \<Rightarrow> 'r"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'r \<Rightarrow> 'c"
    and entdg :: "store \<Rightarrow> 'c"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and S :: "store set" and g :: cfg
  assumes ENTRY: "\<And>ctx s. s \<in> S \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> M (cfg_entry g, ctx)"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> M (v, ctx)"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> M (u, ctx) \<Longrightarrow> s' \<in> M (v, ctx)"
    and COMB: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> M (cl, ctx)
        \<Longrightarrow> last rho \<in> M (ex, rt cl ctx (rd (cl, ctx)))
        \<Longrightarrow> <last tau|last rho> \<in> M (v, ctx)"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> M (cl, ctx)
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (rd (cl, ctx)))"
  shows "cfg_collect_ctx dg cmp g S v ctx \<subseteq> M (v, ctx)"
proof -
  have trace_sound:
    "\<And>tr. trace_witness g S v tr \<Longrightarrow> cmp (dg tr) ctx \<Longrightarrow> last tr \<in> M (v, ctx)"
  proof -
    fix tr assume w: "trace_witness g S v tr" and c: "cmp (dg tr) ctx"
    show "last tr \<in> M (v, ctx)"
      by (rule trace_ctx_sound_meaning
            [where M = M and rd = rd and rt = rt and entdg = entdg
               and dg = dg and cmp = cmp and S = S and g = g,
             OF ENTRY PROC_ENTRY EDGE COMB DG_INTRA DG_RETURN DG_CALLEE ENTER_MONO w c])
  qed
  show ?thesis
    unfolding cfg_collect_ctx_def alpha_ctx_def cfg_collect_trace_def
    using trace_sound by auto
qed

end
