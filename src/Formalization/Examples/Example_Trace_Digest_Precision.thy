theory Example_Trace_Digest_Precision
  imports Trace_IP_Analysis_Sound "Goblint_Analysis.Sign_Domain"
begin

(*
  M4 precision witness -- digest-indexed globals are STRICTLY more precise than
  the flow-insensitive (flat) read, soundly.

  Setting: an edge-less, combine-less CFG whose entry set has two stores --
  sp (x = 1) and sn (x = -1).  Reading x flow-insensitively must join both, and
  in the sign domain the only abstract value whose concretization contains both
  1 and -1 is STop -- so ANY sound flat env reads x as the whole of ZZ
  (flat_forces_top).

  A digest-indexed env keyed by "the value of x at the end of the trace" keeps
  the two histories apart: the reader holding digest 1 sees only sp, so x reads
  as SPos = {n. n > 0}, which is a STRICT subset of ZZ -- and this digest-indexed
  env is globally sound (digest_env_sound_concrete, the unfolded
  Trace_IP_Analysis_Sound.digest_env_sound with gamma_state = sign_domain.gamma_state).
  digest_beats_flat bundles both: sound AND strictly tighter.

  This is the precision payoff the trace pivot was built for: history-indexed
  globals proved both sound (M4 core + flat_env_is_digest_sound) and strictly
  more precise than the flat read on a concrete program.
*)

(* -- the two entry stores and the trivial CFG ----------------------------- *)

definition sp :: store where "sp = (\<lambda>_. 0)(''x'' := 1)"
definition sn :: store where "sn = (\<lambda>_. 0)(''x'' := - 1)"
definition gcfg :: cfg where "gcfg = mk_cfg 0 0 {}"
definition S0 :: "store set" where "S0 = {sp, sn}"

lemma gcfg_edges[simp]: "edges gcfg = {}" by (simp add: gcfg_def)
lemma gcfg_combines[simp]: "combines gcfg = {}" by (simp add: gcfg_def)
lemma gcfg_entry[simp]: "cfg_entry gcfg = 0" by (simp add: gcfg_def)

(* -- the reaching trace set is exactly the two singletons ----------------- *)

lemma gcfg_witness_inv:
  "ip_trace_witness gcfg S0 v tr \<Longrightarrow> v = 0 \<and> (\<exists>s\<in>S0. tr = [s])"
  by (induction rule: ip_trace_witness.induct) auto

lemma reaching_gcfg: "cfg_collect_trace_ip gcfg S0 0 = {[sp], [sn]}"
proof
  show "cfg_collect_trace_ip gcfg S0 0 \<subseteq> {[sp], [sn]}"
    using gcfg_witness_inv unfolding cfg_collect_trace_ip_def S0_def by auto
next
  show "{[sp], [sn]} \<subseteq> cfg_collect_trace_ip gcfg S0 0"
  proof -
    have "[sp] \<in> cfg_collect_trace_ip gcfg S0 0"
      using cfg_collect_trace_ip_entry[of sp S0 gcfg] by (simp add: S0_def)
    moreover have "[sn] \<in> cfg_collect_trace_ip gcfg S0 0"
      using cfg_collect_trace_ip_entry[of sn S0 gcfg] by (simp add: S0_def)
    ultimately show ?thesis by simp
  qed
qed

lemma reaching_gcfg_other: "v \<noteq> 0 \<Longrightarrow> cfg_collect_trace_ip gcfg S0 v = {}"
  using gcfg_witness_inv unfolding cfg_collect_trace_ip_def by auto

lemma alpha_last_empty[simp]: "alpha_last {} = {}" unfolding alpha_last_def by simp
lemma alpha_last_single: "alpha_last {t} = {last t}" unfolding alpha_last_def by auto
lemma alpha_last_reaching: "alpha_last (cfg_collect_trace_ip gcfg S0 0) = {sp, sn}"
  unfolding alpha_last_def reaching_gcfg by force

(* -- sign coarseness: only STop concretizes both a positive and a negative -- *)

lemma sign_pos_neg_top: "(1::int) \<in> gamma_sign sv \<Longrightarrow> (-1::int) \<in> gamma_sign sv \<Longrightarrow> sv = STop"
  by (cases sv) auto

(* -- ANY sound flat env reads x as the whole of ZZ ------------------------ *)

lemma flat_forces_top:
  assumes "alpha_last (cfg_collect_trace_ip gcfg S0 0) \<le> sign_domain.gamma_state envf"
  shows "gamma_sign (envf ''x'') = UNIV"
proof -
  from assms have sp_in: "sp \<in> sign_domain.gamma_state envf"
    and sn_in: "sn \<in> sign_domain.gamma_state envf"
    using alpha_last_reaching by auto
  from sp_in have "\<forall>y. sp y \<in> gamma_sign (envf y)"
    by (simp add: sign_domain.gamma_state_def)
  from this[rule_format, of "''x''"] have p1: "(1::int) \<in> gamma_sign (envf ''x'')"
    by (simp add: sp_def)
  from sn_in have "\<forall>y. sn y \<in> gamma_sign (envf y)"
    by (simp add: sign_domain.gamma_state_def)
  from this[rule_format, of "''x''"] have p2: "(-1::int) \<in> gamma_sign (envf ''x'')"
    by (simp add: sn_def)
  from p1 p2 have "envf ''x'' = STop" by (rule sign_pos_neg_top)
  thus ?thesis by simp
qed

theorem digest_strictly_more_precise:
  assumes flat: "alpha_last (cfg_collect_trace_ip gcfg S0 0) \<le> sign_domain.gamma_state envf"
  shows "gamma_sign SPos \<subset> gamma_sign (envf ''x'')"
proof -
  have top: "gamma_sign (envf ''x'') = UNIV" by (rule flat_forces_top[OF flat])
  have "gamma_sign SPos \<noteq> UNIV" by auto
  thus ?thesis using top by auto
qed

(* -- the digest-indexed env: key on the value of x at the end of the trace -- *)

definition dgx :: "trace \<Rightarrow> int" where "dgx tr = (last tr) ''x''"

definition envd :: "pp \<Rightarrow> int \<Rightarrow> (vname \<Rightarrow> sign)" where
  "envd v d = (if v = 0 \<and> d = 1 then (\<lambda>_. SZero)(''x'' := SPos)
               else if v = 0 \<and> d = (- 1) then (\<lambda>_. SZero)(''x'' := SNeg)
               else (\<lambda>_. STop))"

lemma dgx_sp[simp]: "dgx [sp] = 1" by (simp add: dgx_def sp_def)
lemma dgx_sn[simp]: "dgx [sn] = - 1" by (simp add: dgx_def sn_def)
lemma envd_0_1_x[simp]: "envd 0 1 ''x'' = SPos" by (simp add: envd_def)

lemma sp_in_envd: "sp \<in> sign_domain.gamma_state (envd 0 1)"
  unfolding sign_domain.gamma_state_def envd_def sp_def by auto
lemma sn_in_envd: "sn \<in> sign_domain.gamma_state (envd 0 (- 1))"
  unfolding sign_domain.gamma_state_def envd_def sn_def by auto

lemma reaching_compat_0_1: "reaching_compat dgx (=) 1 gcfg S0 0 = {[sp]}"
  unfolding reaching_compat_def reaching_gcfg by auto
lemma reaching_compat_0_m1: "reaching_compat dgx (=) (- 1) gcfg S0 0 = {[sn]}"
  unfolding reaching_compat_def reaching_gcfg by auto
lemma reaching_compat_0_other:
  "d \<noteq> 1 \<Longrightarrow> d \<noteq> - 1 \<Longrightarrow> reaching_compat dgx (=) d gcfg S0 0 = {}"
  unfolding reaching_compat_def reaching_gcfg by auto

(* -- the digest-indexed env is GLOBALLY sound (= digest_env_sound unfolded) -- *)

lemma digest_env_sound_concrete:
  "\<forall>d v. alpha_last (reaching_compat dgx (=) d gcfg S0 v) \<le> sign_domain.gamma_state (envd v d)"
proof (intro allI)
  fix d :: int and v :: pp
  show "alpha_last (reaching_compat dgx (=) d gcfg S0 v) \<le> sign_domain.gamma_state (envd v d)"
  proof (cases "v = 0")
    case False
    then have "cfg_collect_trace_ip gcfg S0 v = {}" by (rule reaching_gcfg_other)
    then have "reaching_compat dgx (=) d gcfg S0 v = {}"
      unfolding reaching_compat_def by simp
    then show ?thesis by simp
  next
    case True
    consider (pos) "d = 1" | (neg) "d = - 1" | (oth) "d \<noteq> 1 \<and> d \<noteq> - 1" by auto
    then show ?thesis
    proof cases
      case pos
      have "alpha_last (reaching_compat dgx (=) d gcfg S0 v) = {sp}"
        using True pos by (simp add: reaching_compat_0_1 alpha_last_single)
      then show ?thesis using True pos sp_in_envd by simp
    next
      case neg
      have "alpha_last (reaching_compat dgx (=) d gcfg S0 v) = {sn}"
        using True neg by (simp add: reaching_compat_0_m1 alpha_last_single)
      then show ?thesis using True neg sn_in_envd by simp
    next
      case oth
      then have "reaching_compat dgx (=) d gcfg S0 v = {}"
        using True by (simp add: reaching_compat_0_other)
      then show ?thesis by simp
    qed
  qed
qed

lemma digest_read_pos: "(last [sp]) ''x'' \<in> gamma_sign (envd 0 1 ''x'')"
  by (simp add: sp_def)

(* -- capstone: sound AND strictly more precise than every sound flat env --- *)

theorem digest_beats_flat:
  assumes flat: "alpha_last (cfg_collect_trace_ip gcfg S0 0) \<le> sign_domain.gamma_state envf"
  shows "gamma_sign (envd 0 1 ''x'') \<subset> gamma_sign (envf ''x'')
       \<and> (\<forall>d v. alpha_last (reaching_compat dgx (=) d gcfg S0 v) \<le> sign_domain.gamma_state (envd v d))"
proof
  show "gamma_sign (envd 0 1 ''x'') \<subset> gamma_sign (envf ''x'')"
    using digest_strictly_more_precise[OF flat] by simp
next
  show "\<forall>d v. alpha_last (reaching_compat dgx (=) d gcfg S0 v) \<le> sign_domain.gamma_state (envd v d)"
    by (rule digest_env_sound_concrete)
qed

end
