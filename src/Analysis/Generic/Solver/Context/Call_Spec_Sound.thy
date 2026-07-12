theory Call_Spec_Sound
  imports Call_Spec_Generator
begin

section \<open>Stage 0.5: collecting soundness from a \<open>spec_generator\<close> post-fixpoint\<close>

text \<open>
  The Stage-0.5 endpoint: an analysis that interprets \<^locale>\<open>goblint_analysis_spec\<close>,
  supplies transfer soundness, and exhibits a post-fixpoint of its configured generator
  \<^const>\<open>goblint_analysis_spec.spec_generator\<close> obtains collecting-semantics soundness
  \<^emph>\<open>without\<close> restating the six candidate-solution premises of
  \<open>context_collecting_sound\<close> (\<open>ENTRY\<close> / \<open>PROC_ENTRY\<close> / \<open>EDGE\<close> / \<open>LOCAL_POST\<close> /
  \<open>CMP_SOUND\<close> / \<open>ENTER_MONO\<close>).

  How each premise is discharged from the post-fixpoint (all reused, none reproved):
  \<^item> \<open>ENTRY\<close> --- \<open>s0_le_side_env_cmp_entry\<close> inside \<open>side_cfg_T_eff_cmp_collect_sound_gen\<close>;
  \<^item> \<open>PROC_ENTRY\<close> --- \<open>side_cfg_T_eff_cmp_enter_le\<close> (needs the framed transfer contract);
  \<^item> \<open>EDGE\<close> --- \<open>side_cfg_T_eff_cmp_edge_le\<close>;
  \<^item> \<open>LOCAL_POST\<close> / \<open>CMP_SOUND\<close> --- the combine branch, via the spec's own
    \<open>spec_cmb_realizes_combine\<close> (\<^const>\<open>switching_combine_sound\<close>);
  \<^item> \<open>ENTER_MONO\<close> --- not needed on this route: the generator theorem bounds the \<^emph>\<open>flat\<close>
    collecting set \<^const>\<open>cfg_collect\<close>, and every digest slice is below the flat set
    (\<open>cfg_collect_ctx_le\<close>).

  Honest scope: this route certifies the context-sliced bound through the flat
  collapse --- each keyed slot at \<open>ctx\<close> covers \<^emph>\<open>all\<close> flows, which is sound but does not
  exploit digest slicing for precision.  A digest-precise candidate solution (keyed
  slots covering only their compatible traces) still needs the six-premise route
  \<open>context_collecting_sound\<close>; its \<open>ENTER_MONO\<close> is provably not always dischargeable
  (see the shared-context sign case in \<open>Example_Finite_Sign_Context_Analysis\<close>), so a
  premise-free theorem covering that route cannot exist.

  Two hypotheses configure the route rather than the candidate solution:
  \<^item> \<open>seed_const\<close>: the spec's \<open>entry_seed\<close> is context-independent, collapsing
    \<^const>\<open>side_cfg_T_eff_cmp_seed\<close> to the fixed-frame generator
    (\<open>side_cfg_T_eff_cmp_seed_const\<close>).  Context-dependent seeds are the
    activation-witness spine (\<open>Seeded_Clean_Ctx_Collect\<close>), not Stage 0.5.
  \<^item> \<open>single\<close>: at the read context the routing is exactly-one-slot.  Stage 0's
    \<open>reads_own_slot\<close> is deliberately weaker (at-least-own-slot); the flat collapse
    additionally needs that no \<^emph>\<open>other\<close> slot is read.

  The remaining premises (\<open>inr\<close>/\<open>inl\<close> slot invariants, start cover \<open>S_sound\<close>,
  finiteness, variable covers) are the standard well-formedness side conditions every
  existing generator endpoint takes.
\<close>

context goblint_analysis_spec
begin

theorem spec_post_fixpoint_flat_sound:
  fixes sigma :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes seed_const: "entry_seed = (\<lambda>_. fr)"
    and stf: "sound_effectful_transfer_framed etf fr"
    and single: "{k. gcmp ctx k} = {gkey ctx}"
    and inr: "inr_slot_locals_bot_ctx sigma"
    and inl: "inl_slot_globals_bot_ctx sigma"
    and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
    and pp: "part_post_solution (spec_generator g etf bot0 s0) x sigma vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ctx) \<in> vars"
    and cover_comb: "\<And>cc ex ret. (cc, ex, ret) \<in> combines g \<Longrightarrow> (ret, ctx) \<in> vars"
    and cover_entry: "(cfg_entry g, ctx) \<in> vars"
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env_cmp gcmp sigma (v0, ctx)\<rbrakk>"
proof -
  have gen_eq: "spec_generator g etf bot0 s0
                  = side_cfg_T_eff_cmp gkey (spec_cmb etf) g etf fr bot0 s0"
    unfolding spec_generator_def
    unfolding seed_const
    by (rule side_cfg_T_eff_cmp_seed_const)
  have comb: "switching_combine_sound gkey (spec_cmb etf) g etf fr bot0 s0"
    by (rule spec_cmb_realizes_combine[OF finC])
  show ?thesis
    by (rule side_cfg_T_eff_cmp_collect_sound_gen
          [where gcmp = gcmp, OF stf comb single inr inl S_sound
              pp[unfolded gen_eq] finE finC cover_edge cover_comb cover_entry])
qed

end

text \<open>
  The canonical Stage-0.5 entry point, stated in \<^locale>\<open>context_collecting_soundness\<close>
  so its conclusion is literally the conclusion of \<open>context_collecting_sound\<close>: the
  digest slice at \<open>(v0, ctx)\<close> is below the flat set (\<open>cfg_collect_ctx_le\<close>), which the
  flat theorem bounds by the keyed read.
\<close>

context context_collecting_soundness
begin

theorem spec_post_fixpoint_collecting_sound:
  fixes sigma :: "pp \<times> 'c + 'g \<Rightarrow> 'a abs_state"
    and etf :: "(unit, 'a) effectful_domain_transfer"
  assumes seed_const: "entry_seed = (\<lambda>_. fr)"
    and stf: "sound_effectful_transfer_framed etf fr"
    and single: "{k. gcmp ctx k} = {gkey ctx}"
    and inr: "inr_slot_locals_bot_ctx sigma"
    and inl: "inl_slot_globals_bot_ctx sigma"
    and S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
    and pp: "part_post_solution (spec_generator g etf bot0 s0) x sigma vars"
    and finE: "finite (edges g)"
    and finC: "finite (combines g)"
    and cover_edge: "\<And>u a w. (u, a, w) \<in> edges g \<Longrightarrow> (w, ctx) \<in> vars"
    and cover_comb: "\<And>cc ex ret. (cc, ex, ret) \<in> combines g \<Longrightarrow> (ret, ctx) \<in> vars"
    and cover_entry: "(cfg_entry g, ctx) \<in> vars"
  shows "cfg_collect_ctx dg cmp g S v0 ctx \<le> \<lbrakk>side_env_cmp gcmp sigma (v0, ctx)\<rbrakk>"
proof -
  have flat: "cfg_collect g S v0 \<le> \<lbrakk>side_env_cmp gcmp sigma (v0, ctx)\<rbrakk>"
    by (rule spec_post_fixpoint_flat_sound
          [OF seed_const stf single inr inl S_sound pp finE finC
              cover_edge cover_comb cover_entry])
  have slice: "cfg_collect_ctx dg cmp g S v0 ctx \<subseteq> cfg_collect g S v0"
    by (rule cfg_collect_ctx_le)
  from slice flat show ?thesis by (rule order_trans)
qed

end

end
