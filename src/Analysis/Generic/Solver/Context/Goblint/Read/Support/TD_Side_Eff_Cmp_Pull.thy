theory TD_Side_Eff_Cmp_Pull
  imports TD_Side_Eff_Ctx_Shared TD_Side_Eff_Sound TD_Side_Eff_Cmp_Sound
begin

section \<open>Keyed-global pullback: collecting soundness for the cmp-filtered read\<close>

text \<open>
  The reusable heart of a keyed-global (\<open>cmp\<close>-filtered) context generator.  The
  unit-context spine reduces context soundness to the monovariant
  \<open>post_fixpoint_sound_at_eff\<close> through the pullback \<^const>\<open>pull_ctx\<close>.

  Keyed globals read \<^emph>\<open>several\<close> slots per context (\<^const>\<open>glob_env_cmp\<close> joins the
  \<open>cmp\<close>-compatible \<^term>\<open>Inr k\<close>), so the read is context-dependent.  The intra
  transfer \<^const>\<open>apply_etf\<close> still queries and side-effects the \<^typ>\<open>'g\<close>-keyed
  slots, so the pullback keeps the key type \<^typ>\<open>'g\<close> but \<^emph>\<open>masks\<close> the incompatible
  slots to \<^term>\<open>bot\<close>: \<open>pull_cmp\<close> maps \<open>Inl u \<mapsto> sigma (Inl (u, ctx))\<close> and
  \<open>Inr k \<mapsto> (if cmp then sigma (Inr k) else bot)\<close>.  The join-all monovariant read
  over the masked environment is then exactly the filtered read
  (\<open>glob_env_pull_cmp\<close>), so \<^const>\<open>side_env\<close> at the pullback reproduces
  \<^const>\<open>side_env_cmp\<close> (\<open>side_env_cmp_pull\<close>) and the whole monovariant intra
  machinery applies at the keyed read unchanged.
\<close>

subsection \<open>The context-parametrised keyed pullback\<close>

definition pull_cmp ::
  "('c \<Rightarrow> 'g \<Rightarrow> bool) \<Rightarrow> 'c
   \<Rightarrow> (pp \<times> 'c + 'g::finite \<Rightarrow> 'a::bounded_semilattice_sup_bot abs_state)
   \<Rightarrow> (pp + 'g \<Rightarrow> 'a abs_state)"
where
  "pull_cmp gcmp ctx sigma =
     (\<lambda>n. case n of Inl u \<Rightarrow> sigma (Inl (u, ctx))
                  | Inr k \<Rightarrow> (if gcmp ctx k then sigma (Inr k) else bot))"

lemma pull_cmp_Inl: "pull_cmp gcmp ctx sigma (Inl u) = sigma (Inl (u, ctx))"
  by (simp add: pull_cmp_def)

lemma pull_cmp_Inr:
  "pull_cmp gcmp ctx sigma (Inr k) = (if gcmp ctx k then sigma (Inr k) else bot)"
  by (simp add: pull_cmp_def)

text \<open>
  The masked join-all read at the pullback is the \<open>cmp\<close>-filtered read: incompatible
  slots contribute \<^term>\<open>bot\<close>, compatible ones their own value, so the two joins
  agree.  Keyed analogue of the unit-context pullback law.
\<close>

lemma glob_env_pull_cmp:
  "glob_env (pull_cmp gcmp ctx sigma) = glob_env_cmp gcmp ctx sigma"
proof (rule order_antisym)
  show "glob_env (pull_cmp gcmp ctx sigma) \<le> glob_env_cmp gcmp ctx sigma"
    unfolding glob_env_def
  proof (rule abs_join_set_le)
    show "finite ((\<lambda>g. pull_cmp gcmp ctx sigma (Inr g)) ` UNIV)" by simp
  next
    fix a assume "a \<in> (\<lambda>g. pull_cmp gcmp ctx sigma (Inr g)) ` UNIV"
    then obtain k where a: "a = pull_cmp gcmp ctx sigma (Inr k)" by auto
    show "a \<le> glob_env_cmp gcmp ctx sigma"
    proof (cases "gcmp ctx k")
      case True
      hence "a = sigma (Inr k)" using a by (simp add: pull_cmp_Inr)
      thus ?thesis using glob_env_cmp_upper[of gcmp ctx k sigma] True by simp
    next
      case False
      hence "a = bot" using a by (simp add: pull_cmp_Inr)
      thus ?thesis by simp
    qed
  qed
next
  show "glob_env_cmp gcmp ctx sigma \<le> glob_env (pull_cmp gcmp ctx sigma)"
  proof (rule glob_env_cmp_le)
    fix k assume k: "gcmp ctx k"
    have "sigma (Inr k) = pull_cmp gcmp ctx sigma (Inr k)"
      using k by (simp add: pull_cmp_Inr)
    also have "... \<le> glob_env (pull_cmp gcmp ctx sigma)" by (rule glob_env_upper)
    finally show "sigma (Inr k) \<le> glob_env (pull_cmp gcmp ctx sigma)" .
  qed
qed

lemma side_env_cmp_pull:
  "side_env_cmp gcmp sigma (v, ctx) = side_env (pull_cmp gcmp ctx sigma) v"
  by (simp add: side_env_def side_env_cmp_def pull_cmp_Inl glob_env_pull_cmp)

subsection \<open>The local-bot invariant transports through the mask\<close>

text \<open>
  Every keyed slot is locals-bot (\<^const>\<open>inr_slot_locals_bot_ctx\<close>) and the mask only
  ever replaces a slot by \<^term>\<open>bot\<close>, so the masked environment is locals-bot too.
\<close>

lemma inr_slot_locals_bot_pull_cmp:
  assumes "inr_slot_locals_bot_ctx sigma"
  shows "inr_slot_locals_bot (pull_cmp gcmp ctx sigma)"
  using assms
  unfolding inr_slot_locals_bot_ctx_def inr_slot_locals_bot_def pull_cmp_def
  by (auto split: sum.split)

subsection \<open>Keyed collecting soundness via the pullback\<close>

text \<open>
  The keyed analogue of \<open>post_fixpoint_sound_at_ctx_pull\<close>: given the monovariant
  per-edge / per-combine / entry post-fixpoint bounds phrased against the keyed
  read \<open>side_env_cmp gcmp sigma (v, ctx)\<close> at the pulled-back environment
  \<^term>\<open>pull_cmp gcmp ctx sigma\<close>, the filtered read over-approximates the IP
  collecting semantics at \<^term>\<open>(v0, ctx)\<close>.  The proof is the unit-context one with
  \<^const>\<open>pull_cmp\<close> for \<^const>\<open>pull_ctx\<close>: \<open>side_env_cmp_pull\<close> rewrites every bound into
  monovariant \<^const>\<open>side_env\<close> shape and \<open>post_fixpoint_sound_at_eff\<close> closes it.
\<close>

context sound_effectful_transfer
begin

theorem post_fixpoint_sound_at_cmp_pull:
  fixes g :: cfg
    and sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a abs_state"
    and s0 :: "'a abs_state" and S :: "store set" and v0 :: pp
    and ctx :: 'c and gcmp :: "'c \<Rightarrow> 'g \<Rightarrow> bool"
  assumes inr: "inr_slot_locals_bot_ctx sigma"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes step_le:
    "\<And>u a w. (u, a, w) \<in> edges g
       \<Longrightarrow> etf_full (apply_etf etf a u) (pull_cmp gcmp ctx sigma)
             \<le> side_env_cmp gcmp sigma (w, ctx)"
  assumes combine_le:
    "\<And>c ex ret. (c, ex, ret) \<in> combines g \<Longrightarrow>
       etf_full (etf_combine etf c ex) (pull_cmp gcmp ctx sigma)
         \<le> side_env_cmp gcmp sigma (ret, ctx)"
  assumes entry_le: "s0 \<le> side_env_cmp gcmp sigma (cfg_entry g, ctx)"
  shows "cfg_collect g S v0 \<le> \<lbrakk>side_env_cmp gcmp sigma (v0, ctx)\<rbrakk>"
proof -
  have main: "cfg_collect g S v0 \<le> \<lbrakk>side_env (pull_cmp gcmp ctx sigma) v0\<rbrakk>"
  proof (rule post_fixpoint_sound_at_eff
           [OF inr_slot_locals_bot_pull_cmp[OF inr] S_sound])
    fix u a w assume e: "(u, a, w) \<in> edges g"
    show "etf_full (apply_etf etf a u) (pull_cmp gcmp ctx sigma)
            \<le> side_env (pull_cmp gcmp ctx sigma) w"
      using step_le[OF e] by (simp add: side_env_cmp_pull)
  next
    fix c ex ret assume cm: "(c, ex, ret) \<in> combines g"
    show "etf_full (etf_combine etf c ex) (pull_cmp gcmp ctx sigma)
            \<le> side_env (pull_cmp gcmp ctx sigma) ret"
      using combine_le[OF cm] by (simp add: side_env_cmp_pull)
  next
    show "s0 \<le> side_env (pull_cmp gcmp ctx sigma) (cfg_entry g)"
      using entry_le by (simp add: side_env_cmp_pull)
  qed
  show ?thesis using main by (simp add: side_env_cmp_pull)
qed

subsection \<open>Per-edge trace soundness at the keyed read\<close>

text \<open>
  The per-edge fact of \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close>'s \<open>EDGE\<close>
  premise, discharged from the keyed pullback bound.  Keyed analogue of
  \<open>entry_store_edge_sound_ctx\<close>: a concrete step through edge \<open>(u, a, v)\<close> that starts
  inside the filtered read at \<open>u\<close> lands inside the filtered read at \<open>v\<close>, whenever
  the pullback bound for that edge holds.  Lets a generator that supplies the
  \<^const>\<open>pull_cmp\<close> bounds discharge \<open>_cmp_final\<close>'s \<open>EDGE\<close> directly.
\<close>

lemma cmp_edge_sound:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a abs_state"
  assumes inr: "inr_slot_locals_bot_ctx sigma"
  assumes bound:
    "etf_full (apply_etf etf a u) (pull_cmp gcmp ctx sigma)
       \<le> side_env_cmp gcmp sigma (v, ctx)"
  assumes step: "edge_step a s = Some s'"
  assumes src: "s \<in> \<lbrakk>side_env_cmp gcmp sigma (u, ctx)\<rbrakk>"
  shows "s' \<in> \<lbrakk>side_env_cmp gcmp sigma (v, ctx)\<rbrakk>"
proof -
  have src_pull: "s \<in> \<lbrakk>side_env (pull_cmp gcmp ctx sigma) u\<rbrakk>"
    using src by (simp add: side_env_cmp_pull)
  have step_mem: "s' \<in> edge_collect a {s}"
    using step by (simp add: edge_collect_single)
  have step_full:
    "s' \<in> \<lbrakk>etf_collecting_full (apply_etf etf a u) (pull_cmp gcmp ctx sigma)\<rbrakk>"
  proof -
    have "edge_collect a {s} \<subseteq> edge_collect a \<lbrakk>side_env (pull_cmp gcmp ctx sigma) u\<rbrakk>"
      using src_pull
        edge_collect_mono[of "{s}" "\<lbrakk>side_env (pull_cmp gcmp ctx sigma) u\<rbrakk>" a] by auto
    thus ?thesis
      using step_mem edge_collect_etf_sound[OF inr_slot_locals_bot_pull_cmp[OF inr]]
      by blast
  qed
  have collect_le_pull:
    "etf_collecting_full (apply_etf etf a u) (pull_cmp gcmp ctx sigma)
       \<le> side_env (pull_cmp gcmp ctx sigma) v"
    by (rule etf_collecting_full_le_side_env[OF bound[unfolded side_env_cmp_pull]])
  have collect_le:
    "etf_collecting_full (apply_etf etf a u) (pull_cmp gcmp ctx sigma)
       \<le> side_env_cmp gcmp sigma (v, ctx)"
    using collect_le_pull by (simp add: side_env_cmp_pull)
  show ?thesis using gamma_state_mono[OF collect_le] step_full by blast
qed

text \<open>
  The \<open>ENTRY\<close> premise of \<open>_cmp_final\<close> from the entry bound: an initial store that is
  covered by the seed \<open>s0\<close> is covered by the filtered read at the entry.  The
  context-compatibility hypothesis \<open>cmp (dg [s]) ctx\<close> plays no role here --- it is
  consumed downstream by the trace induction, not by the entry containment.
\<close>

lemma cmp_entry_sound:
  fixes sigma :: "pp \<times> 'c + 'g::finite \<Rightarrow> 'a abs_state"
  assumes S_sound: "S \<le> \<lbrakk>s0\<rbrakk>"
  assumes entry_le: "s0 \<le> side_env_cmp gcmp sigma (cfg_entry g, ctx)"
  assumes s: "s \<in> S"
  shows "s \<in> \<lbrakk>side_env_cmp gcmp sigma (cfg_entry g, ctx)\<rbrakk>"
  using S_sound entry_le s gamma_state_mono by blast

end

end
