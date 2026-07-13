theory DG_Route_Soundness
  imports DG_Context_Soundness
begin

section \<open>Context-sliced collecting soundness, carrier-agnostic\<close>

text \<open>
  The homogeneous context spine proves \<open>cfg_collect_ctx dg cmp g S v ctx\<close> sound for
  the keyed read \<^const>\<open>side_env_cmp\<close> by interpreting \<^locale>\<open>context_analysis_soundness\<close>
  and running a trace induction (\<open>post_fixpoint_sound_at_ctx_semantic_generic\<close>).  That
  induction never inspects the abstract-state structure of a read: it uses only the
  \<^emph>\<open>meaning set\<close> \<open>[[renv sigma (v, ctx)]]\<close> at each (point, context) pair.  So it factors
  through an opaque meaning \<open>M :: pp \<times> 'c \<Rightarrow> store set\<close>, with the routing read \<open>rd\<close>
  supplying only the value the context selector \<open>rt\<close> consumes.

  This is the shared backbone of both spines: the homogeneous instance takes
  \<open>M (v, ctx) = [[side_env_cmp gcmp sigma (v, ctx)]]\<close>, the DG instance takes
  \<open>M (v, ctx) = gammaDG (dg_D_c sigma ctx v) (dg_G_c sigma ctx)\<close> --- the two-gamma
  meaning of the context-keyed slots.  Restating the collecting theorem over \<open>M\<close> once
  turns the DG port into an instantiation rather than a re-proof.
\<close>

subsection \<open>Trace backbone over an opaque meaning\<close>

text \<open>
  The read-agnostic trace induction with the meaning abstracted to \<open>M\<close>.  Mirrors
  \<open>post_fixpoint_sound_at_ctx_semantic_generic\<close> line for line, replacing every
  \<open>[[renv sigma (p, c)]]\<close> by \<open>M (p, c)\<close> and every routing read \<open>rread sigma (cl, ctx)\<close>
  by \<open>rd (cl, ctx)\<close>.
\<close>

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

subsection \<open>Context-sliced collecting soundness over an opaque meaning\<close>

text \<open>
  Wrapping the trace backbone through \<^const>\<open>cfg_collect_ctx\<close> once.  This is the
  carrier-agnostic form of \<open>context_analysis_soundness.collect_sound\<close>.
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

section \<open>DG instantiation: context-keyed collecting soundness\<close>

text \<open>
  The DG endpoint replacing \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close>: the
  opaque meaning is the two-gamma reading of the context-keyed slots
  (\<open>dg_gamma_c\<close>), and the routing read is the local slot's Answer
  (\<open>dg_D_c\<close>).  The eight obligations keep the shape of the homogeneous theorem
  but read through \<open>gammaDG\<close>.  As on the homogeneous spine the intra
  \<open>EDGE\<close> / seed \<open>ENTRY\<close> and the switching \<open>COMB\<close> stay premises, discharged per
  analysis instance (the concrete witness supplies them from \<open>step_sound\<close> /
  \<open>combine_sound\<close> / a post-solution).
\<close>

context sound_dg_spec
begin

theorem dg_collect_ctx_sound:
  fixes sigma :: "pp \<times> 'c + 'c \<Rightarrow> ('D, 'G) dg_state"
    and dg :: "store list \<Rightarrow> 'c" and cmp :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
    and rt :: "pp \<Rightarrow> 'c \<Rightarrow> 'D \<Rightarrow> 'c" and entdg :: "store \<Rightarrow> 'c"
  assumes ENTRY: "\<And>ctx s. s \<in> S0 \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> dg_gamma_c sigma ctx (cfg_entry g)"
    and PROC_ENTRY: "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S0
        \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> dg_gamma_c sigma ctx v"
    and EDGE: "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
        \<Longrightarrow> last tr \<in> dg_gamma_c sigma ctx u \<Longrightarrow> s' \<in> dg_gamma_c sigma ctx v"
    and COMB: "\<And>ctx cl ex v tau rho. (cl, ex, v) \<in> combines g
        \<Longrightarrow> last tau \<in> dg_gamma_c sigma ctx cl
        \<Longrightarrow> last rho \<in> dg_gamma_c sigma (rt cl ctx (dg_D_c sigma ctx cl)) ex
        \<Longrightarrow> <last tau|last rho> \<in> dg_gamma_c sigma ctx v"
    and DG_INTRA: "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
    and DG_RETURN: "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
    and DG_CALLEE: "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
    and ENTER_MONO: "\<And>ctx cl s. s \<in> dg_gamma_c sigma ctx cl
        \<Longrightarrow> cmp (entdg s) (rt cl ctx (dg_D_c sigma ctx cl))"
  shows "cfg_collect_ctx dg cmp g S0 v ctx \<subseteq> dg_gamma_c sigma ctx v"
proof -
  have "cfg_collect_ctx dg cmp g S0 v ctx
          \<subseteq> (\<lambda>(p, c). dg_gamma_c sigma c p) (v, ctx)"
  proof (rule collect_ctx_sound_meaning
      [where M = "\<lambda>(p, c). dg_gamma_c sigma c p"
         and rd = "\<lambda>(p, c). dg_D_c sigma c p"
         and rt = rt and entdg = entdg and dg = dg and cmp = cmp and S = S0 and g = g])
    show "\<And>ctx s. s \<in> S0 \<Longrightarrow> cmp (dg [s]) ctx
            \<Longrightarrow> s \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (cfg_entry g, ctx)"
      using ENTRY by simp
  next
    show "\<And>ctx v s. (cfg_entry g, EA_Enter, v) \<in> edges g \<Longrightarrow> s \<in> enter_state ` S0
            \<Longrightarrow> cmp (dg [s]) ctx \<Longrightarrow> s \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (v, ctx)"
      using PROC_ENTRY by simp
  next
    show "\<And>ctx u a v tr s'. (u, a, v) \<in> edges g \<Longrightarrow> edge_step a (last tr) = Some s'
            \<Longrightarrow> last tr \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (u, ctx)
            \<Longrightarrow> s' \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (v, ctx)"
      using EDGE by simp
  next
    fix ctx cl ex v' tau rho
    assume comb: "(cl, ex, v') \<in> combines g"
      and cr: "last tau \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (cl, ctx)"
      and ce: "last rho \<in> (\<lambda>(p, c). dg_gamma_c sigma c p)
                  (ex, rt cl ctx ((\<lambda>(p, c). dg_D_c sigma c p) (cl, ctx)))"
    show "<last tau|last rho> \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (v', ctx)"
      using COMB[OF comb] cr ce by simp
  next
    show "\<And>tr s' ctx. tr \<noteq> [] \<Longrightarrow> cmp (dg (tr @ [s'])) ctx \<Longrightarrow> cmp (dg tr) ctx"
      using DG_INTRA by blast
  next
    show "\<And>tau rho. tau \<noteq> [] \<Longrightarrow> dg (tau @ tl rho @ [<last tau|last rho>]) = dg tau"
      using DG_RETURN by blast
  next
    show "\<And>tau rho. rho \<noteq> [] \<Longrightarrow> hd rho = enter_state (last tau) \<Longrightarrow> dg rho = entdg (last tau)"
      using DG_CALLEE by blast
  next
    fix ctx cl s
    assume "s \<in> (\<lambda>(p, c). dg_gamma_c sigma c p) (cl, ctx)"
    thus "cmp (entdg s) (rt cl ctx ((\<lambda>(p, c). dg_D_c sigma c p) (cl, ctx)))"
      using ENTER_MONO by simp
  qed
  thus ?thesis by simp
qed

end

end
