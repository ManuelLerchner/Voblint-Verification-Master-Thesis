theory DG_LTR_Sound
  imports DG_Soundness "Voblint_CFG.LTR_Abstract"
begin

section \<open>Trace-native D/G collecting soundness\<close>

text \<open>
  The D/G post-solution endpoint restated over the stack-faithful local-trace collecting
  \<open>ltr_collect\<close> instead of the broad \<open>cfg_collect\<close>.  It reuses the analysis-specific closure
  obligations \<open>dg_postfix_gamma_entry\<close> / \<open>dg_postfix_gamma_edge\<close> / \<open>dg_postfix_gamma_combine\<close>
  verbatim --- the only change is the final semantic step, \<open>ltr_collect_semantic_postfix\<close> in place
  of \<open>cfg_collect_semantic_postfix\<close>.  Soundness therefore rides on \<open>valid_ltr\<close>'s matched return
  rule (inside \<open>ltr_gamma\<close>), NOT on \<open>ltr_collect_le_cfg_collect\<close>: each return recovers its own
  caller rather than pairing every reachable caller with every callee exit.  The single-caller
  \<open>COMB\<close> obligation reads exactly one combine triple's caller and callee-exit slots, so no second
  caller/callee matching argument is introduced.  The \<open>cfg_collect\<close> endpoints in
  \<^theory>\<open>Voblint_Analysis.DG_Soundness\<close> remain available as compatibility results.

  Kept in a separate leaf so that importing the trace stack (which brings \<open>ltr.Call\<close> into scope,
  shadowing the bare \<open>Call\<close> constructor) does not touch the wide D/G consumer theories.
\<close>

context sound_dg_spec
begin

theorem dg_postfix_collect_sound_ltr:
  assumes pf: "dg_postfix g s0d s0g sigma"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect g S0 v \<subseteq> dg_gamma sigma v"
proof (rule ltr_collect_semantic_postfix)
  show "S0 \<subseteq> dg_gamma sigma (cfg_entry g)"
    by (rule dg_postfix_gamma_entry[OF pf sound0])
next
  fix u a w s
  assume "(u, a, w) \<in> edges g" and "s \<in> edge_collect a (dg_gamma sigma u)"
  then show "s \<in> dg_gamma sigma w" by (rule dg_postfix_gamma_edge[OF pf])
next
  fix cc ex w dst s t
  assume "(cc, ex, w, dst) \<in> combines g" and "s \<in> dg_gamma sigma cc"
    and "t \<in> dg_gamma sigma ex"
  then show "combine_collect dst s t \<in> dg_gamma sigma w"
    by (rule dg_postfix_gamma_combine[OF pf])
qed

corollary dg_post_solution_collect_sound_ltr:
  assumes pp:
      "part_post_solution (dg_gen g bot0 s0d s0g) x sigma vars"
    and cover_entry: "(cfg_entry g, ()) \<in> vars"
    and cover_edge:
      "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ()) \<in> vars"
    and cover_combine:
      "\<And>cc ex w dst. (cc, ex, w, dst) \<in> combines g \<Longrightarrow> (w, ()) \<in> vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and sound0: "S0 \<subseteq> gammaDG s0d s0g"
  shows "ltr_collect g S0 v \<subseteq> dg_gamma sigma v"
proof -
  have pf: "dg_postfix g s0d s0g sigma"
    by (rule dg_post_solution_postfix
          [OF pp cover_entry cover_edge cover_combine finE finC])
  show ?thesis by (rule dg_postfix_collect_sound_ltr[OF pf sound0])
qed

end

end
