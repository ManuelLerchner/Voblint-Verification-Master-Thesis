theory Exec_Sign_Cmp_Keyed_DG_Run
  imports
    "Voblint_Analysis.Sign_DG"
    "Voblint_Analysis.DG_Route_Soundness"
begin

section \<open>Keyed-global context precision on the DG spine (sign)\<close>

text \<open>
  The DG keyed witness for the two-call, two-context program.  It is a \<^emph>\<open>DG\<close> solution
  \<^term>\<open>kw_dg :: pp \<times> bool + bool \<Rightarrow> (sign abs_state, sign abs_state) dg_state\<close>, and the
  reader is \<^const>\<open>sound_dg_spec.dg_gamma_c\<close> --- the two-gamma meaning of the keyed
  slots.  The meaning set is provably \<^emph>\<open>identical\<close> to the keyed read shape
  (\<open>dg_meaning\<close>: it equals \<open>[[kw_loc p \<squnion> kw_slot ctx]]\<close>), so the witness
  preserves theorem strength and executable precision while dropping the
  homogeneous context-soundness stack: this theory imports only the DG endpoint.

  The load-bearing obligation --- the switching combine of
  \<open>sound_dg_spec.dg_collect_ctx_sound\<close> --- is discharged through the DG locale's
  own \<open>combine_sound\<close>, with no \<^const>\<open>combine_read_cmp\<close> plumbing.  The routing read
  \<open>dg_route sigma (p, ctx)\<close> is the local slot's Answer \<^const>\<open>sound_dg_spec.dg_D_c\<close>.
\<close>

subsection \<open>The program and its keyed DG solution\<close>

text \<open>Program points: caller call \<open>0\<close>, callee exit \<open>1\<close>, return \<open>2\<close>; context
  \<^typ>\<open>bool\<close> from the surviving global input.\<close>

definition kw_gin :: "bool \<Rightarrow> sign" where
  "kw_gin ctx = (if ctx then SPos else SZero)"

definition kw_slot :: "bool \<Rightarrow> sign abs_state" where
  "kw_slot ctx = (\<lambda>n. if n = ''G'' then kw_gin ctx else SBot)"

definition kw_loc :: "pp \<Rightarrow> sign abs_state" where
  "kw_loc p = (\<lambda>n. if is_global n then SBot
                   else if n = ''x'' then (if p = 0 then SPos else if p = 2 then STop else SBot)
                   else SBot)"

definition kw_locg :: "pp \<Rightarrow> bool \<Rightarrow> sign abs_state" where
  "kw_locg p ctx = (\<lambda>n. if n = ''G'' then kw_gin ctx else kw_loc p n)"

text \<open>Goblint context computation: derive the context from the surviving global \<open>G\<close>.\<close>
definition kw_ec :: "bool \<Rightarrow> sign abs_state \<Rightarrow> bool" where
  "kw_ec ctx s = (s ''G'' = SPos)"

text \<open>
  The DG solution: a local unknown \<open>Inl (p, ctx)\<close> carries the retain-discipline Answer
  \<^term>\<open>kw_locg p ctx\<close> in its \<^const>\<open>locals\<close>; a global unknown \<open>Inr ctx\<close> carries the
  per-context global slot \<^term>\<open>kw_slot ctx\<close> in its \<^const>\<open>globs\<close>.
\<close>
definition kw_dg :: "pp \<times> bool + bool \<Rightarrow> (sign abs_state, sign abs_state) dg_state" where
  "kw_dg u = (case u of Inl (p, ctx) \<Rightarrow> DG (kw_locg p ctx) bot | Inr ctx \<Rightarrow> DG bot (kw_slot ctx))"

subsection \<open>Keyed accessors and the meaning equality\<close>

lemma dg_D_val: "sign_dg.dg_D_c kw_dg ctx p = kw_locg p ctx"
  by (simp add: sign_dg.dg_D_c_def kw_dg_def)

lemma dg_G_val: "sign_dg.dg_G_c kw_dg ctx = kw_slot ctx"
  by (simp add: sign_dg.dg_G_c_def kw_dg_def)

text \<open>The retain local and the publish local agree once the context global is joined in.\<close>
lemma locg_slot_eq: "kw_locg p ctx \<squnion> kw_slot ctx = kw_loc p \<squnion> kw_slot ctx"
  by (auto simp: kw_locg_def kw_slot_def kw_loc_def kw_gin_def sup_fun_def
           sup_sign_def is_global_def fun_eq_iff split: if_splits)

text \<open>
  The DG meaning at a (point, context) equals the homogeneous keyed read meaning
  \<open>[[side_env_cmp (=) kw_sig (p, ctx)]] = [[kw_loc p \<squnion> kw_slot ctx]]\<close>: same store set,
  so soundness carries the same strength.
\<close>
lemma dg_meaning: "sign_dg.dg_gamma_c kw_dg ctx p = \<lbrakk>kw_loc p \<squnion> kw_slot ctx\<rbrakk>"
  by (simp add: sign_dg.dg_gamma_c_def dg_D_val dg_G_val gamma_unit_def locg_slot_eq)

subsection \<open>The switching combine, discharged on the DG spine\<close>

text \<open>The context selector recovers the syntactic context from the retained local \<open>G\<close>.\<close>
lemma derived_ctx: "kw_ec ctx (sign_dg.dg_D_c kw_dg ctx 0) = ctx"
  by (cases ctx) (simp_all add: kw_ec_def dg_D_val kw_locg_def kw_gin_def)

definition kw_res :: "bool \<Rightarrow> sign abs_state" where
  "kw_res ctx = restrict_local (kw_locg 0 ctx \<squnion> kw_slot ctx)
                  \<squnion> restrict_global (kw_locg 1 ctx \<squnion> kw_slot ctx)"

lemma unit_comb_eval:
  "dgs_combine (unit_dg_spec sign_tf) (kw_locg 0 ctx) (kw_locg 1 ctx) (kw_slot ctx)
     = (restrict_global (kw_res ctx), restrict_local (kw_res ctx))"
  by (simp add: unit_dg_spec_def unit_combine_step_def kw_res_def Let_def)

lemma gamma_unit_restrict: "gamma_unit (restrict_local r) (restrict_global r) = \<lbrakk>r\<rbrakk>"
  by (simp add: gamma_unit_def restrict_local_global_join)

text \<open>
  The reassembly bound: the caller local flows to the return local and the callee-exit
  global is covered by the return context's slot --- the \<open>LOCAL_POST\<close> + \<open>CMP_SOUND\<close>
  content, here a single pointwise order fact.
\<close>
lemma kw_res_le: "kw_res ctx \<le> kw_locg 2 ctx \<squnion> kw_slot ctx"
  by (auto simp: le_fun_def kw_res_def restrict_local_def restrict_global_def
                 kw_locg_def kw_loc_def kw_slot_def kw_gin_def sup_fun_def sup_sign_def
                 bot_sign_def is_global_def less_eq_sign_def split: if_splits)

text \<open>
  The DG switching combine: caller at \<open>ctx\<close>, callee at the derived context (here again
  \<open>ctx\<close>), reassembled into the return read at \<open>ctx\<close>.  Discharged through the DG locale's
  own \<open>combine_sound\<close>.
\<close>
lemma dg_combine_obligation:
  assumes s: "s \<in> sign_dg.dg_gamma_c kw_dg ctx 0"
    and t: "t \<in> sign_dg.dg_gamma_c kw_dg ctx 1"
  shows "<s|t> \<in> sign_dg.dg_gamma_c kw_dg ctx 2"
proof -
  have s': "s \<in> gamma_unit (kw_locg 0 ctx) (kw_slot ctx)"
    using s by (simp add: sign_dg.dg_gamma_c_def dg_D_val dg_G_val)
  have t': "t \<in> gamma_unit (kw_locg 1 ctx) (kw_slot ctx)"
    using t by (simp add: sign_dg.dg_gamma_c_def dg_D_val dg_G_val)
  have "<s|t> \<in> gamma_unit (restrict_local (kw_res ctx)) (restrict_global (kw_res ctx))"
    using sign_dg.combine_sound[OF s' t'] unit_comb_eval by auto
  then have "<s|t> \<in> \<lbrakk>kw_res ctx\<rbrakk>" by (simp add: gamma_unit_restrict)
  then have "<s|t> \<in> \<lbrakk>kw_locg 2 ctx \<squnion> kw_slot ctx\<rbrakk>"
    using gamma_state_mono[OF kw_res_le] by blast
  then show ?thesis
    by (simp add: sign_dg.dg_gamma_c_def dg_D_val dg_G_val gamma_unit_def)
qed

text \<open>
  The switching-combine premise of \<open>sound_dg_spec.dg_collect_ctx_sound\<close> in its exact
  shape, at this witness (route \<open>rt = (\<lambda>cc. kw_ec)\<close>, combine set \<open>{(0, 1, 2)}\<close>).  The
  derived callee context collapses to the caller context, so it reduces to
  \<open>dg_combine_obligation\<close>.
\<close>
lemma dg_COMB_premise:
  assumes comb: "(cl, ex, v) \<in> {(0::pp, 1::pp, 2::pp)}"
    and caller: "last tau \<in> sign_dg.dg_gamma_c kw_dg ctx cl"
    and callee: "last rho \<in> sign_dg.dg_gamma_c kw_dg
                    ((\<lambda>cc. kw_ec) cl ctx (sign_dg.dg_D_c kw_dg ctx cl)) ex"
  shows "<last tau|last rho> \<in> sign_dg.dg_gamma_c kw_dg ctx v"
proof -
  from comb have e: "cl = 0" "ex = 1" "v = 2" by auto
  have "last rho \<in> sign_dg.dg_gamma_c kw_dg ctx 1"
    using callee e derived_ctx by simp
  thus ?thesis using caller e dg_combine_obligation by simp
qed

subsection \<open>The precision payoff, machine-checked\<close>

text \<open>
  The keyed reads separate the two contexts; the context-blind join merges them to
  \<^const>\<open>SNonNeg\<close>.  The precision witness is executable through the underlying slots.
\<close>

lemma read_False: "sign_dg.dg_G_c kw_dg False ''G'' = SZero"
  by (simp add: dg_G_val kw_slot_def kw_gin_def)

lemma read_True: "sign_dg.dg_G_c kw_dg True ''G'' = SPos"
  by (simp add: dg_G_val kw_slot_def kw_gin_def)

lemma merge_join_all: "(kw_slot False \<squnion> kw_slot True) ''G'' = SNonNeg"
  by eval

lemma contexts_separated: "sign_dg.dg_G_c kw_dg False \<noteq> sign_dg.dg_G_c kw_dg True"
proof
  assume "sign_dg.dg_G_c kw_dg False = sign_dg.dg_G_c kw_dg True"
  hence "sign_dg.dg_G_c kw_dg False ''G'' = sign_dg.dg_G_c kw_dg True ''G''" by simp
  thus False using read_False read_True by simp
qed

subsection \<open>Routing precision: the routing read sees the retained global\<close>

text \<open>The publish sibling: identical global slots, but the local answer erases \<open>G\<close>.\<close>
definition kw_dg_pub :: "pp \<times> bool + bool \<Rightarrow> (sign abs_state, sign abs_state) dg_state" where
  "kw_dg_pub u = (case u of Inl (p, ctx) \<Rightarrow> DG (kw_loc p) bot | Inr ctx \<Rightarrow> DG bot (kw_slot ctx))"

lemma route_read_retain_G:
  "sign_dg.dg_D_c kw_dg ctx p ''G'' = (if ctx then SPos else SZero)"
  by (simp add: dg_D_val kw_locg_def kw_gin_def)

lemma route_read_publish_G:
  "sign_dg.dg_D_c kw_dg_pub ctx p ''G'' = SBot"
  by (simp add: sign_dg.dg_D_c_def kw_dg_pub_def kw_loc_def is_global_def)

lemma route_ctx_retain_recovers:
  "kw_ec ctx (sign_dg.dg_D_c kw_dg ctx p) = ctx"
  by (cases ctx) (simp_all add: kw_ec_def route_read_retain_G)

lemma route_ctx_publish_collapses:
  "kw_ec ctx (sign_dg.dg_D_c kw_dg_pub ctx p) = False"
  by (simp add: kw_ec_def route_read_publish_G)

lemma route_publish_contexts_indistinguishable:
  "kw_ec False (sign_dg.dg_D_c kw_dg_pub False p)
     = kw_ec True (sign_dg.dg_D_c kw_dg_pub True p)"
  by (simp add: route_ctx_publish_collapses)

end
