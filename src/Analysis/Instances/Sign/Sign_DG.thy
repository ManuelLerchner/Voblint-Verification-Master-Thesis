theory Sign_DG
  imports
    "Voblint_Core.DG_LTR_Sound"
    Sign_Transfer
begin

section \<open>Sign on the heterogeneous DG spine\<close>

text \<open>Sign is the diagonal D/G instance: answers and side effects use the same
  abstract-state domain. The entry transfer therefore combines the caller answer and
  global side effect before binding parameters. All generator and collecting results
  follow from the generic locale; only transfer soundness is domain-specific.\<close>

context
  fixes gs :: "vname \<Rightarrow> bool"
begin

interpretation sign_dg: sound_dg_spec "unit_dg_spec_for gs (sign_tf_for gs)" gamma_unit gs
  by (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for])

text \<open>Sign under a conjunctive placement: every location keeps a precise
  per-activation local view (\<open>sign_keep_all\<close> holds everywhere), while every
  declared global also publishes a joined summary for other activations
  (\<open>publish_side = gs\<close>). \<open>gs\<close> here only decides publication, never whether a
  location is also kept -- unlike \<open>unit_dg_spec_for\<close>'s exclusive \<open>gs\<close>/\<open>\<not> gs\<close>
  split, this is the two-copies shape Goblint-style privatization needs, and
  it is sound by the same generic covering argument, no separate proof.\<close>
definition sign_keep_all :: "vname \<Rightarrow> bool" where
  "sign_keep_all x = True"

lemma sign_keep_all_cover: "\<forall>x. gs x \<or> sign_keep_all x"
  unfolding sign_keep_all_def by simp

interpretation sign_dg_privatized:
  sound_dg_spec "unit_dg_spec_placed gs sign_keep_all gs (sign_tf_for gs)" gamma_unit gs
  by (rule sound_dg_spec_unit_placed[OF sign_is_sound_transfer_for sign_keep_all_cover])

text \<open>Validation: an assignment to a declared global under this policy lands
  in both projections of the same step -- the local (kept) slot always gets
  the fresh value (\<open>sign_keep_all\<close> holds everywhere), and the side
  (published) slot gets it too whenever the assigned location is a declared
  global. This is the retain-and-publish shape the exclusive classic split
  cannot express: there, a global's fresh value is dropped from the local
  slot at the same step it gets published. No claim is made about what a
  later read sees -- reads still join the local slot with the full published
  side value regardless of placement.\<close>

lemma sign_dg_privatized_assign_local:
  "snd (dgs_assign (unit_dg_spec_placed gs sign_keep_all gs (sign_tf_for gs)) x a d g)
     = assign_sign x a (d \<squnion> g)"
  unfolding unit_dg_spec_placed_def unit_step_placed_def sign_tf_for_def
  by (simp add: sign_keep_all_def project_component_def Let_def)

lemma sign_dg_privatized_assign_published_at:
  assumes "gs y"
  shows "fst (dgs_assign (unit_dg_spec_placed gs sign_keep_all gs (sign_tf_for gs)) x a d g) y
     = assign_sign x a (d \<squnion> g) y"
  unfolding unit_dg_spec_placed_def unit_step_placed_def sign_tf_for_def
  by (simp add: sign_keep_all_def project_component_def Let_def assms)

text \<open>Concrete witness: \<open>g := 5\<close> from the empty state is retained locally
  and published, both at exactly \<open>SPos\<close>.\<close>
corollary sign_dg_privatized_assign_g_five:
  assumes gs_g: "gs (STR ''g'')"
  shows
    "snd (dgs_assign (unit_dg_spec_placed gs sign_keep_all gs (sign_tf_for gs))
            (STR ''g'') (N 5) bot bot) (STR ''g'') = SPos"
    "fst (dgs_assign (unit_dg_spec_placed gs sign_keep_all gs (sign_tf_for gs))
            (STR ''g'') (N 5) bot bot) (STR ''g'') = SPos"
  using sign_dg_privatized_assign_local[where x = "(STR ''g'')" and a = "N 5"
      and d = "bot::sign abs_state" and g = "bot::sign abs_state"]
    sign_dg_privatized_assign_published_at[where y = "(STR ''g'')" and x = "(STR ''g'')" and a = "N 5"
      and d = "bot::sign abs_state" and g = "bot::sign abs_state", OF gs_g]
  by (simp_all add: bot_fun_def assign_sign_def)

end

subsection \<open>Native endpoint\<close>

text \<open>
  The joint concretization at a program point and the configured equation system,
  named natively so consumers do not reach through the locale prefix.
\<close>

definition sign_dg_gamma ::
  "(pp \<times> unit + unit \<Rightarrow> (sign abs_state, sign abs_state) dg_state)
   \<Rightarrow> pp \<Rightarrow> store set"
where
  "sign_dg_gamma \<equiv> sound_dg_spec.dg_gamma gamma_unit"

definition sign_dg_generator ::
  "(vname \<Rightarrow> bool) \<Rightarrow> cfg \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state \<Rightarrow> sign abs_state
   \<Rightarrow> (pp \<times> unit, unit, (sign abs_state, sign abs_state) dg_state) eqsT"
where
  "sign_dg_generator gs \<equiv> sound_dg_spec.dg_gen (unit_dg_spec_for gs (sign_tf_for gs))"

text \<open>
  Public DG API for the Sign domain, generic in the classifier \<open>gs\<close>.  The
  sublocale interpretation rewrites facts inherited from @{locale sound_dg_spec}
  into this native vocabulary, so the exported theorem below cites the generic
  collecting-soundness fact directly with no manual unfold/fold bridging.
\<close>
locale sign_dg_api =
  fixes gs :: "vname \<Rightarrow> bool"

sublocale sign_dg_api \<subseteq> sound_dg_spec_ltr_for "unit_dg_spec_for gs (sign_tf_for gs)" gamma_unit gs
  rewrites "sound_dg_spec.dg_gamma gamma_unit = sign_dg_gamma"
       and "sound_dg_spec.dg_gen (unit_dg_spec_for gs (sign_tf_for gs)) = sign_dg_generator gs"
  apply (unfold sound_dg_spec_ltr_for_def)
   apply (rule sound_dg_spec_unit_for[OF sign_is_sound_transfer_for])
  apply (simp add: sign_dg_gamma_def)
  apply (simp add: sign_dg_generator_def)
  done

context sign_dg_api
begin

text \<open>
  Trace-native collecting soundness from a post-solution of the configured generator.
\<close>

theorem sign_dg_post_solution_collect_sound:
  assumes pp: "part_post_solution (sign_dg_generator gs g bot0 s0d s0g) x sigma vars"
    and cover: "vars_cover g vars"
    and finI: "finite (intra g)"
    and finC: "finite (calls g)"
    and sound0: "S0 \<subseteq> \<lbrakk>s0d \<squnion> s0g\<rbrakk>"
  shows "ltr_collect gs g S0 v \<subseteq> sign_dg_gamma sigma v"
  by (rule dg_post_solution_collect_sound_ltr_for
        [OF pp cover finI finC sound0[folded gamma_unit_def]])

end

end
