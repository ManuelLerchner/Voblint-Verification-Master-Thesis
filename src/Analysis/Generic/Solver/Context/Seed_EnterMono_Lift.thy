theory Seed_EnterMono_Lift
  imports Clean_RRead_Sound
begin

section \<open>Point-digest routing: the domain-generic ENTER_MONO capability\<close>

text \<open>
  The last obligation of the seeded-clean kernel \<open>clean_ctx_collect_rread\<close>
  (\<^theory>\<open>Voblint_Analysis.Clean_RRead_Sound\<close>) is \<open>ENTER_MONO\<close> --- the value-digest
  routing (Goblint \<open>Spec.context\<close>):

    \<open>s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk> \<Longrightarrow> cmp (entdg s) (rt cl ctx (sg (Inl (cl, ctx))))\<close>

  For a value-keyed digest that reads a projected variable and abstracts it by a
  point map \<open>decode\<close> (with \<open>cmp = (=)\<close> and the routed context being the slot value
  itself), the obligation at a routing slot \<open>L = sg (Inl (cl, ctx))\<close> is the
  pointwise equation \<open>decode (s proj_var) = L proj_var\<close>.

  \<open>point_digest\<close> is the capability that makes this hold: a domain supplies its
  point abstraction \<open>decode :: int \<Rightarrow> 'a\<close> and a point predicate \<open>is_point\<close>, and
  proves the single \<^emph>\<open>gamma-exactness\<close> assumption \<open>point_exact\<close> --- on a point slot
  \<open>decode\<close> is constant over the slot's concretisation and returns it.  The locale
  then derives \<open>enter_mono_point\<close> for every domain that interprets it.

  This bundles exactly one assumption (\<open>point_exact\<close>, a precision fact soundness
  never gives) and re-exports one inherited lemma to plural domain instances (Sign,
  Interval) --- the same shape as \<open>sound_transfer\<close> / \<open>value_digest_reader\<close>.
  The premise \<open>is_point (L proj_var)\<close> quantifies only the value gamma of the
  projected variable; it never mentions the entering store \<open>s\<close> or the routing
  plumbing, so it is strictly weaker than and not circular with the ENTER_MONO
  conclusion.
\<close>

locale point_digest =
  fixes decode :: "Int.int \<Rightarrow> 'a::sound_domain"
    and is_point :: "'a \<Rightarrow> bool"
  assumes point_exact: "\<And>a v. is_point a \<Longrightarrow> v \<in> gamma a \<Longrightarrow> decode v = a"
begin

text \<open>
  ENTER_MONO at a point routing slot: every concrete store admitted by the slot
  projects, under \<open>decode\<close>, to the slot's own value.  The proof is the projection
  \<open>s \<in> \<lbrakk>L\<rbrakk> \<Longrightarrow> s proj_var \<in> gamma (L proj_var)\<close> followed by \<open>point_exact\<close>.
\<close>

lemma enter_mono_point:
  fixes sg :: "(pp \<times> 'c) + 'g \<Rightarrow> 'a abs_state"
  assumes pt: "is_point (sg (Inl (cl, ctx)) proj_var)"
    and s: "s \<in> \<lbrakk>sg (Inl (cl, ctx))\<rbrakk>"
  shows "decode (s proj_var) = sg (Inl (cl, ctx)) proj_var"
proof -
  have "s proj_var \<in> gamma (sg (Inl (cl, ctx)) proj_var)"
    using s unfolding gamma_state_def by simp
  thus ?thesis by (rule point_exact[OF pt])
qed

end

end
