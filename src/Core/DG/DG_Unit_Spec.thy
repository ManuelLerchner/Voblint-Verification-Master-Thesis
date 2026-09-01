theory DG_Unit_Spec
  imports DG_Spec_Sound
begin

section \<open>An analysis that genuinely uses the global channel\<close>

text \<open>
  Every other specification in this session is local-only: it answers from
  the local value and never touches \<open>man_global\<close> or \<open>man_sideg\<close>. This one
  does the opposite, and is the reason those capabilities exist.

  It chooses \<open>D = G = 'a abs_state\<close>, splitting each state by variable
  ownership: the global names live on the shared channel, the rest on the
  program point's own unknown. A transfer therefore reads the shared fact,
  rejoins it with the local half to recover the whole state, runs the
  ordinary transfer on that, and splits the result back -- publishing the
  global half with \<open>man_sideg\<close> and answering with the local half.

  \<open>unit_transfer\<close> is that shape, and it is written in the manager language
  directly: there is no \<open>'dl \<Rightarrow> 'dg \<Rightarrow> 'dg \<times> 'dl\<close> anywhere. Its compiled
  tree reads the source, queries the global key, publishes a \<open>Side\<close>, and
  answers -- which is what makes it the first specification whose equations
  carry a genuine \<open>QueryG\<close> and \<open>Side\<close>.
\<close>

subsection \<open>The ownership-splitting transfer\<close>

text \<open>
  The pattern is stated once, over any carrier that can merge a local and a
  global half and project each back out. Which carrier is a separate question
  from what the transfer does: the same three operations exist on
  function-valued states and on the solver's association lists, so the
  executable mirror is this definition at other arguments rather than a
  second development.
\<close>

definition unit_transfer_gen ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd)
   \<Rightarrow> ('x,'k,'d::bounded_semilattice_sup_bot,'d) man_transfer"
where
  "unit_transfer_gen cmb rg rl f m =
     do {
       g \<leftarrow> man_global m;
       let res = f (cmb (man_local m) g);
       _ \<leftarrow> man_sideg m (rg res);
       sp_return (rl res)
     }"

text \<open>
  A return combine is the same pattern whose whole-state function additionally
  depends on the callee's exit value. The pure-pair encoding had to split this
  into an environment stage and an assignment stage; in the manager language
  the callee exit is just an extra argument, so one definition covers both.
\<close>

definition unit_combine_transfer_gen ::
  "('d \<Rightarrow> 'd \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd) \<Rightarrow> ('d \<Rightarrow> 'd \<Rightarrow> 'd)
   \<Rightarrow> ('x,'k,'d::bounded_semilattice_sup_bot,'d) man_combine_transfer"
where
  "unit_combine_transfer_gen cmb rg rl asn m de = unit_transfer_gen cmb rg rl (asn de) m"

subsection \<open>What the compiled tree reads and publishes\<close>

text \<open>
  Soundness judges a transfer by these two observations, so they are proved
  once here, on the pattern, rather than per carrier: the answer is the local
  projection of the merged whole state, and the contribution at the routed key
  is its global projection.
\<close>

lemma traverse_unit_transfer_gen [simp]:
  "locals (traverse_rhs (transfer_tree (unit_transfer_gen cmb rg rl f) src gk) \<tau>)
     = rl (f (cmb (locals (\<tau> src)) (globs (\<tau> (Inr gk)))))"
  by (cases src)
     (simp_all add: transfer_tree_def dg_edge_tree_man_def unit_transfer_gen_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc
        Let_def)

lemma sides_unit_transfer_gen [simp]:
  "globs (sides_of_rhs (transfer_tree (unit_transfer_gen cmb rg rl f) src gk) \<tau> (Inr gk))
     = rg (f (cmb (locals (\<tau> src)) (globs (\<tau> (Inr gk)))))"
  by (cases src)
     (simp_all add: transfer_tree_def dg_edge_tree_man_def unit_transfer_gen_def
        mk_dg_man_def dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc
        Let_def)

lemma traverse_unit_combine_transfer_gen [simp]:
  "locals (traverse_rhs
             (combine_transfer_tree (unit_combine_transfer_gen cmb rg rl asn)
                src_cc src_ex gk) \<tau>)
     = rl (asn (locals (\<tau> src_ex)) (cmb (locals (\<tau> src_cc)) (globs (\<tau> (Inr gk)))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def
        unit_combine_transfer_gen_def unit_transfer_gen_def mk_dg_man_def
        dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc Let_def)

lemma sides_unit_combine_transfer_gen [simp]:
  "globs (sides_of_rhs
            (combine_transfer_tree (unit_combine_transfer_gen cmb rg rl asn)
               src_cc src_ex gk) \<tau> (Inr gk))
     = rg (asn (locals (\<tau> src_ex)) (cmb (locals (\<tau> src_cc)) (globs (\<tau> (Inr gk)))))"
  by (cases src_cc; cases src_ex)
     (simp_all add: combine_transfer_tree_def dg_combine_tree_man_def
        unit_combine_transfer_gen_def unit_transfer_gen_def mk_dg_man_def
        dg_read_at_def dg_read_global_def dg_sideg_def sp_bind_assoc Let_def)

definition unit_transfer ::
  "(vname \<Rightarrow> bool) \<Rightarrow> ('a::bounded_semilattice_sup_bot abs_state \<Rightarrow> 'a abs_state)
   \<Rightarrow> ('x,'k,'a abs_state,'a abs_state) man_transfer"
where
  "unit_transfer gs =
     unit_transfer_gen (combine_env gs) (restrict_global_for gs) (restrict_local_for gs)"

lemma unit_transfer_unfold:
  "unit_transfer gs f m =
     do {
       g \<leftarrow> man_global m;
       let res = f (combine_env gs (man_local m) g);
       _ \<leftarrow> man_sideg m (restrict_global_for gs res);
       sp_return (restrict_local_for gs res)
     }"
  unfolding unit_transfer_def unit_transfer_gen_def by (rule refl)

text \<open>
  The return combine is the same shape with one extra read: the return slot
  is a local name owned by the callee's exit state \<open>de\<close>, while every global
  name is owned by the freshly queried shared fact, not by \<open>de\<close>'s own
  locally-restricted copy of it. \<^const>\<open>combine_env\<close> supplies the ownership
  routing for the non-return names; \<open>de ret_var\<close> is read directly.
\<close>

definition unit_combine_transfer ::
  "(vname \<Rightarrow> bool) \<Rightarrow> call_info
   \<Rightarrow> ('x,'k,'a::bounded_semilattice_sup_bot abs_state,'a abs_state) man_combine_transfer"
where
  "unit_combine_transfer gs ci =
     unit_combine_transfer_gen (combine_env gs) (restrict_global_for gs) (restrict_local_for gs)
       (\<lambda>de. combine_assign (ci_dst ci) (de ret_var))"

lemma unit_combine_transfer_unfold:
  "unit_combine_transfer gs ci m de =
     do {
       g \<leftarrow> man_global m;
       let res = combine_assign (ci_dst ci) (de ret_var)
                   (combine_env gs (man_local m) g);
       _ \<leftarrow> man_sideg m (restrict_global_for gs res);
       sp_return (restrict_local_for gs res)
     }"
  unfolding unit_combine_transfer_def unit_combine_transfer_gen_def unit_transfer_gen_def
  by (rule refl)

subsection \<open>The complete unit specification\<close>

text \<open>
  Built the same way any other analysis is: start from
  \<^const>\<open>default_local_dg_spec\<close> and override the fields this analysis
  implements. \<open>caller_cont\<close> and \<open>combine_env\<close> stay at their identity
  defaults -- the ownership split happens inside \<open>combine_assign\<close>, which
  needs the callee exit and the shared fact together.
\<close>

definition unit_dg_spec_for ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a::sound_domain domain_transfer
   \<Rightarrow> ('x,'k,'a abs_state,'a abs_state) dg_spec"
where
  "unit_dg_spec_for gs tf = default_local_dg_spec\<lparr>
     dgs_skip := unit_transfer gs (apply_tf tf EA_Nop),
     dgs_assign := (\<lambda>x e. unit_transfer gs (apply_tf tf (EA_Assign x e))),
     dgs_special := (\<lambda>sc x. unit_transfer gs (apply_tf tf (EA_Special sc x))),
     dgs_branch := (\<lambda>b pol. unit_transfer gs (branch\<^sup># tf b pol)),
     dgs_body := (\<lambda>p. unit_transfer gs (body\<^sup># tf p)),
     dgs_return := (\<lambda>e p. unit_transfer gs (return\<^sup># tf e p)),
     dgs_enter := (\<lambda>ci. unit_transfer gs (snd o enter\<^sup># tf ci)),
     dgs_event := (\<lambda>ev. unit_transfer gs (event\<^sup># tf ev)),
     dgs_combine_assign := unit_combine_transfer gs \<rparr>"

lemma dg_spec_step_unit_for:
  "dg_spec_step (unit_dg_spec_for gs tf) a = unit_transfer gs (apply_tf tf a)"
  unfolding unit_dg_spec_for_def
  by (cases a) simp_all

lemma dgs_enter_unit_dg_spec_for:
  "dgs_enter (unit_dg_spec_for gs tf) ci = unit_transfer gs (snd o enter\<^sup># tf ci)"
  unfolding unit_dg_spec_for_def by simp

text \<open>The composed return pipeline: \<open>caller_cont\<close> and \<open>combine_env\<close> are
  identities, so the whole combine is \<^const>\<open>unit_combine_transfer\<close> on the raw
  call-site value.\<close>

lemma dg_spec_combine_transfer_unit_dg_spec_for:
  "dg_spec_combine_transfer (unit_dg_spec_for gs tf) ci m de
     = unit_combine_transfer gs ci m de"
  unfolding dg_spec_combine_transfer_def dgs_combine_def unit_dg_spec_for_def
  by (simp add: local_transfer_def local_combine_transfer_def man_with_local_def)

section \<open>What a split point means\<close>

text \<open>
  A point's two halves are read back by routing each name to the component that
  owns it, never by joining them: an untouched name keeps whatever precision its
  owning half has, instead of being coarsened by the other half's unrelated
  default. That routing is exactly the merge the transfers above perform, which
  is why this is the concretization they are sound for.
\<close>

definition gamma_unit ::
  "(vname \<Rightarrow> bool) \<Rightarrow> 'a::sound_domain abs_state \<Rightarrow> 'a abs_state \<Rightarrow> store set"
where
  "gamma_unit gs d g = \<lbrakk>combine_env gs d g\<rbrakk>"

lemma gamma_unit_eq: "gamma_unit gs d g = \<lbrakk>combine_env gs d g\<rbrakk>"
  unfolding gamma_unit_def ..

lemma gamma_unitD [dest]: "s \<in> gamma_unit gs d g \<Longrightarrow> s \<in> \<lbrakk>combine_env gs d g\<rbrakk>"
  unfolding gamma_unit_def by simp

lemma gamma_unit_mono:
  assumes "d \<le> d'" and "g \<le> g'"
  shows "gamma_unit gs d g \<subseteq> gamma_unit gs d' g'"
  unfolding gamma_unit_def
  by (rule gamma_state_mono) (use assms in \<open>auto simp: combine_env_def le_fun_def\<close>)

text \<open>
  A return merges two concrete stores by the same ownership routing the
  abstract merge uses, so the merged store is still described by the caller's
  own merged state: its locals come from the caller side, and its globals from
  a state whose global half is the same \<open>g\<close>.
\<close>

lemma gamma_unit_combine_env:
  assumes cc: "s \<in> \<lbrakk>combine_env gs dc g\<rbrakk>"
    and ex: "t \<in> \<lbrakk>combine_env gs de g\<rbrakk>"
  shows "combine_env gs s t \<in> \<lbrakk>combine_env gs dc g\<rbrakk>"
proof (rule gamma_stateI)
  fix x
  show "combine_env gs s t x \<in> gamma (combine_env gs dc g x)"
  proof (cases "gs x")
    case True
    have "t x \<in> gamma (combine_env gs de g x)" using ex by (simp add: gamma_state_def)
    then show ?thesis using True by (simp add: combine_env_def)
  next
    case False
    have "s x \<in> gamma (combine_env gs dc g x)" using cc by (simp add: gamma_state_def)
    then show ?thesis using False by (simp add: combine_env_def)
  qed
qed

text \<open>
  The return value is the one name read off the callee's local half rather than
  through the merge, so it needs \<^const>\<open>reserved_ret_var\<close>: only because no
  program declares \<^const>\<open>ret_var\<close> global does that half agree with the merged
  state there.
\<close>

lemma gamma_unit_combine_assign:
  assumes reserved: "reserved_ret_var gs"
    and cc: "s \<in> \<lbrakk>combine_env gs dc g\<rbrakk>"
    and ex: "t \<in> \<lbrakk>combine_env gs de g\<rbrakk>"
  shows "combine_assign dst (t ret_var) (combine_env gs s t)
           \<in> \<lbrakk>combine_assign dst (de ret_var) (combine_env gs dc g)\<rbrakk>"
proof (cases dst)
  case None
  then show ?thesis using gamma_unit_combine_env[OF cc ex] by simp
next
  case (Some x)
  have ret: "t ret_var \<in> gamma (de ret_var)"
  proof -
    have "t ret_var \<in> gamma (combine_env gs de g ret_var)"
      using ex by (simp add: gamma_state_def)
    then show ?thesis
      using reserved by (simp add: combine_env_def reserved_ret_var_def)
  qed
  show ?thesis
    unfolding Some
    using gamma_unit_combine_env[OF cc ex] ret
    by (auto simp: gamma_state_def)
qed

section \<open>Soundness of the ownership-splitting analysis\<close>

text \<open>
  The whole-state transfer's own soundness is the only mathematics here. Each
  obligation reduces by the two observation lemmas to a statement about the
  merged state, where \<open>combine_env_restrict_id\<close> rebuilds exactly what the
  transfer was applied to -- so what is left is the transfer contract itself,
  cited from the interpreted locale.
\<close>

theorem sound_dg_spec_unit_for:
  assumes tf_sound: "sound_transfer_for gs tf"
    and reserved: "reserved_ret_var gs"
  shows "sound_dg_spec (unit_dg_spec_for gs tf) (gamma_unit gs) gs"
proof -
  interpret tfs: sound_transfer_for gs tf by (rule tf_sound)
  show ?thesis
  proof (unfold_locales, goal_cases)
    case (1 d d' g g')
    then show ?case by (rule gamma_unit_mono)
  next
    case (2 a \<tau> src gk)
    show ?case
      unfolding dg_spec_edge_tree_def dg_spec_step_unit_for unit_transfer_def
        gamma_unit_def
      by (simp add: tfs.edge_collect_apply_tf_sound_for)
  next
    case (3 s \<tau> src gk ci)
    then show ?case
      unfolding dgs_enter_unit_dg_spec_for unit_transfer_def gamma_unit_def
      by (simp add: call_enter_def tfs.tf_sound_enter_entry_for)
  next
    case (4 s \<tau> src_cc gk t src_ex ci)
    then show ?case
      unfolding dg_spec_combine_tree_def dg_spec_combine_transfer_unit_dg_spec_for
        unit_combine_transfer_def gamma_unit_def combine_collect_def
      by (simp add: gamma_unit_combine_assign[OF reserved])
  qed
qed

end
