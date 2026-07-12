theory Exec_Sign_Cmp_Keyed_Run
  imports Voblint_Analysis.TD_Side_Eff_Cmp_Sound Voblint_Analysis.Sign_Domain
begin

section \<open>Keyed-global context precision: sound concrete witness (sign)\<close>

text \<open>
  The sound counterpart to \<open>Exec_Sign_Ctx_Seeded_Run\<close>.  Where the seeded demo keys
  on caller locals (erased by \<^const>\<open>enter_state\<close>, hence unsound), this witness keys
  the globals themselves: a two-call program whose call contexts differ only by a
  preserved global input, analysed with per-context global slots \<^term>\<open>Inr False\<close> /
  \<^term>\<open>Inr True\<close>.  The context is derived from the global that survives entry, so
  the split over-approximates the concrete semantics.

  The exhibited environment \<open>kw_sig\<close> is a keyed post-solution: the callee's global
  effect under context \<open>ctx\<close> is routed to slot \<^term>\<open>Inr ctx\<close>, and the \<open>cmp\<close>-filtered
  read (\<^const>\<open>glob_env_cmp\<close>, \<open>cmp = (=)\<close>) at a context recovers only that context's
  slot.  The two read-side combine obligations of
  \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close> --- \<open>LOCAL_POST\<close> (caller local flows
  to the return) and \<open>CMP_SOUND\<close> (Goblint read compatibility) --- are discharged in
  the theorem's exact premise shape, and their combine bound \<open>combine_read_cmp_le\<close> and
  soundness follow through \<^const>\<open>combine_read_cmp\<close> / \<open>combine_case_cmp_sound\<close>.
\<close>

subsection \<open>The program and its keyed solution\<close>

text \<open>
  Program points: caller call \<^term>\<open>0::pp\<close>, callee exit \<^term>\<open>1::pp\<close>, return
  \<^term>\<open>2::pp\<close>.  Context \<^typ>\<open>bool\<close>: \<^term>\<open>False\<close> is the call under global input
  \<open>G = 0\<close> (\<^const>\<open>SZero\<close>), \<^term>\<open>True\<close> the call under \<open>G = 1\<close> (\<^const>\<open>SPos\<close>).
\<close>

definition kw_gin :: "bool \<Rightarrow> sign" where
  "kw_gin ctx = (if ctx then SPos else SZero)"

text \<open>Per-context global slot: the callee's global effect for context \<open>ctx\<close>.\<close>
definition kw_slot :: "bool \<Rightarrow> sign abs_state" where
  "kw_slot ctx = (\<lambda>n. if n = ''G'' then kw_gin ctx else SBot)"

text \<open>
  Local unknown at a program point: globals sit in the slots (\<^const>\<open>SBot\<close> here),
  the caller local \<open>x\<close> flows \<^const>\<open>SPos\<close> at the call to \<^const>\<open>STop\<close> at the return.
\<close>
definition kw_loc :: "pp \<Rightarrow> sign abs_state" where
  "kw_loc p = (\<lambda>n. if is_global n then SBot
                   else if n = ''x'' then (if p = 0 then SPos else if p = 2 then STop else SBot)
                   else SBot)"

text \<open>
  The retain-discipline local slot: the flow-sensitive global \<^term>\<open>kw_gin ctx\<close> is
  kept in the per-context local unknown rather than erased to \<^const>\<open>SBot\<close>.  Context
  selection reading the local slot (\<^const>\<open>route_read_cmp\<close>) therefore recovers the
  precise context; under the publish discipline the local \<open>G\<close> is \<^const>\<open>SBot\<close> and the
  read collapses.
\<close>
definition kw_locg :: "pp \<Rightarrow> bool \<Rightarrow> sign abs_state" where
  "kw_locg p ctx = (\<lambda>n. if n = ''G'' then kw_gin ctx else kw_loc p n)"

definition kw_sig :: "pp \<times> bool + bool \<Rightarrow> sign abs_state" where
  "kw_sig u = (case u of Inl (p, ctx) \<Rightarrow> kw_locg p ctx | Inr ctx \<Rightarrow> kw_slot ctx)"

text \<open>Goblint context computation: derive the context from the surviving global \<open>G\<close>.\<close>
definition kw_ec :: "bool \<Rightarrow> sign abs_state \<Rightarrow> bool" where
  "kw_ec ctx s = (s ''G'' = SPos)"

subsection \<open>Filtered read collapses to the context's slot\<close>

lemma glob_read: "glob_env_cmp (=) ctx kw_sig = kw_slot ctx"
proof -
  have "{k. (=) ctx k} = {ctx}" by auto
  hence "glob_env_cmp (=) ctx kw_sig = kw_sig (Inr ctx)" by (rule glob_env_cmp_singleton)
  thus ?thesis by (simp add: kw_sig_def)
qed

lemma senv: "side_env_cmp (=) kw_sig (p, ctx) = kw_loc p \<squnion> kw_slot ctx"
proof -
  have "kw_locg p ctx \<squnion> kw_slot ctx = kw_loc p \<squnion> kw_slot ctx"
    by (auto simp: kw_locg_def kw_slot_def kw_loc_def kw_gin_def sup_fun_def
             sup_sign_def is_global_def fun_eq_iff split: if_splits)
  thus ?thesis by (simp add: side_env_cmp_def kw_sig_def glob_read)
qed

subsection \<open>The two read-side combine obligations\<close>

text \<open>\<open>LOCAL_POST\<close>: the caller local flows to the return local (here \<open>x\<close>: \<open>SPos \<le> STop\<close>).\<close>
lemma local_post:
  "\<not> is_global x \<Longrightarrow> kw_sig (Inl (0, ctx)) x \<le> kw_sig (Inl (2, ctx)) x"
  by (auto simp: kw_sig_def kw_locg_def kw_loc_def less_eq_sign_def is_global_def)

text \<open>
  The derived callee context equals the syntactic context: under retain the local
  slot read by \<^const>\<open>route_read_cmp\<close> carries \<open>G\<close>, so the context survives to it.
\<close>
lemma derived_ctx: "kw_ec ctx (route_read_cmp kw_sig (0, ctx)) = ctx"
  by (cases ctx)
     (simp_all add: kw_ec_def route_read_cmp_def kw_sig_def kw_locg_def kw_gin_def)

text \<open>
  \<open>CMP_SOUND\<close>: at a global variable the callee-exit read under the context derived
  from the local slot is covered by the filtered read at the return context --- both
  are the slot \<^term>\<open>Inr ctx\<close>.
\<close>
lemma cmp_sound:
  "is_global x \<Longrightarrow>
     side_env_cmp (=) kw_sig (1, kw_ec ctx (route_read_cmp kw_sig (0, ctx))) x
       \<le> side_env_cmp (=) kw_sig (2, ctx) x"
  using derived_ctx kw_loc_def senv by force

subsection \<open>Combine bound and soundness\<close>

lemma comb_bound:
  "combine_read_cmp (=) kw_sig (\<lambda>cc. kw_ec) 0 1 ctx \<le> side_env_cmp (=) kw_sig (2, ctx)"
  by (meson cmp_sound combine_read_cmp_le local_post)

lemma comb_sound:
  assumes s: "s \<in> \<lbrakk>side_env_cmp (=) kw_sig (0, ctx)\<rbrakk>"
    and t: "t \<in> \<lbrakk>side_env_cmp (=) kw_sig (1, kw_ec ctx (route_read_cmp kw_sig (0, ctx)))\<rbrakk>"
  shows "<s|t> \<in> \<lbrakk>side_env_cmp (=) kw_sig (2, ctx)\<rbrakk>"
proof -
  have "<last [s] | last [t]> \<in> \<lbrakk>side_env_cmp (=) kw_sig (2, ctx)\<rbrakk>"
    by (rule combine_case_cmp_sound[OF _ _ comb_bound]) (use s t in simp_all)
  thus ?thesis by simp
qed

subsection \<open>Wiring: the obligations in the theorem's premise shape\<close>

text \<open>
  The combine set of the witness program.  With \<^term>\<open>combines g = kw_combines\<close> the
  two lemmas below are literally the \<open>LOCAL_POST\<close> and \<open>CMP_SOUND\<close> premises of
  \<open>side_cfg_T_eff_cmp_collect_ctx_sound_semantic\<close> instantiated at \<open>kw_sig\<close>,
  \<open>gcmp = (=)\<close>, \<open>kw_ec\<close>.
\<close>
definition kw_combines :: "(pp \<times> pp \<times> pp) set" where
  "kw_combines = {(0, 1, 2)}"

lemma LOCAL_POST_inst:
  "(cl, ex, v) \<in> kw_combines \<Longrightarrow> \<not> is_global x
     \<Longrightarrow> kw_sig (Inl (cl, ctx)) x \<le> kw_sig (Inl (v, ctx)) x"
  using local_post by (auto simp: kw_combines_def)

lemma CMP_SOUND_inst:
  "(cl, ex, v) \<in> kw_combines \<Longrightarrow> is_global x
     \<Longrightarrow> side_env_cmp (=) kw_sig (ex, (\<lambda>cc. kw_ec) cl ctx (route_read_cmp kw_sig (cl, ctx))) x
           \<le> side_env_cmp (=) kw_sig (v, ctx) x"
  using cmp_sound by (auto simp: kw_combines_def)

subsection \<open>The precision payoff, machine-checked\<close>

text \<open>
  The keyed reads separate the two contexts; the join of the two slots (the
  monovariant, context-blind read) merges them to \<^const>\<open>SNonNeg\<close> --- the precision
  the keying recovers.  The filtered read is executable via \<open>glob_env_cmp_code\<close>.
\<close>

lemma read_False: "glob_env_cmp (=) False kw_sig ''G'' = SZero"
  by (simp add: glob_read kw_slot_def kw_gin_def)

lemma read_True: "glob_env_cmp (=) True kw_sig ''G'' = SPos"
  by (simp add: glob_read kw_slot_def kw_gin_def)

lemma read_False_exec: "glob_env_cmp (=) False kw_sig ''G'' = SZero"
  by eval

lemma merge_join_all: "(kw_slot False \<squnion> kw_slot True) ''G'' = SNonNeg"
  by eval

lemma contexts_separated:
  "glob_env_cmp (=) False kw_sig \<noteq> glob_env_cmp (=) True kw_sig"
proof
  assume "glob_env_cmp (=) False kw_sig = glob_env_cmp (=) True kw_sig"
  hence "glob_env_cmp (=) False kw_sig ''G'' = glob_env_cmp (=) True kw_sig ''G''" by simp
  thus False using read_False read_True by simp
qed

subsection \<open>Routing precision: the routing read sees the retained global, publish erases it\<close>

text \<open>
  The publish sibling of \<^const>\<open>kw_sig\<close>: identical global slots, but the local unknown
  keeps the publish \<^const>\<open>kw_loc\<close> (globals erased to \<^const>\<open>SBot\<close>) instead of the retain
  \<^const>\<open>kw_locg\<close>.
\<close>

definition kw_sig_pub :: "pp \<times> bool + bool \<Rightarrow> sign abs_state" where
  "kw_sig_pub u = (case u of Inl (p, ctx) \<Rightarrow> kw_loc p | Inr ctx \<Rightarrow> kw_slot ctx)"

text \<open>
  The routing-precision payoff, machine-checked.  \<^const>\<open>route_read_cmp\<close> is the routing
  read (\<open>sigma (Inl vk)\<close>): the local slot alone, without the join-all globals of the
  observation read \<^const>\<open>side_env_cmp\<close>.  Under the retain discipline the local slot
  carries the flow-sensitive global \<open>G\<close>, so the routing read recovers the precise
  per-context value; under publish the local \<open>G\<close> is \<^const>\<open>SBot\<close> and the routing read
  collapses.
\<close>

text \<open>After retain: the routing read observes the precise per-context global.\<close>
lemma route_read_retain_G:
  "route_read_cmp kw_sig (p, ctx) ''G'' = (if ctx then SPos else SZero)"
  by (simp add: route_read_cmp_def kw_sig_def kw_locg_def kw_gin_def)

text \<open>Before retain: the routing read sees the erased local global.\<close>
lemma route_read_publish_G:
  "route_read_cmp kw_sig_pub (p, ctx) ''G'' = SBot"
  by (simp add: route_read_cmp_def kw_sig_pub_def kw_loc_def is_global_def)

text \<open>
  Why routing precision improves.  The context selector \<^const>\<open>kw_ec\<close> reads \<open>G\<close> from the
  routing read.  Under retain it recovers the syntactic context; under publish it reads
  \<^const>\<open>SBot\<close> for both contexts, so both call sites route to the same \<^term>\<open>False\<close> ---
  the routing channel carries no context, and precision is lost precisely here.
\<close>
lemma route_ctx_retain_recovers:
  "kw_ec ctx (route_read_cmp kw_sig (p, ctx)) = ctx"
  by (cases ctx) (simp_all add: kw_ec_def route_read_retain_G)

lemma route_ctx_publish_collapses:
  "kw_ec ctx (route_read_cmp kw_sig_pub (p, ctx)) = False"
  by (simp add: kw_ec_def route_read_publish_G)

lemma route_publish_contexts_indistinguishable:
  "kw_ec False (route_read_cmp kw_sig_pub (p, False))
     = kw_ec True (route_read_cmp kw_sig_pub (p, True))"
  by (simp add: route_ctx_publish_collapses)

end

