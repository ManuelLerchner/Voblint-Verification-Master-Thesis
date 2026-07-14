theory Exec_Ivl_Cmp_Keyed_DG_Run
  imports
    "Voblint_Analysis.Interval_DG"
    "Voblint_Analysis.DG_Route_Soundness"
begin

section \<open>Keyed-global context precision on the DG spine (interval)\<close>

text \<open>
  DG-native interval sibling of the keyed sign witness.  The same two-context
  shape is now read through the DG interpretation of Interval, so the example
  no longer depends on the homogeneous context tower.
\<close>

subsection \<open>The DG solution\<close>

definition ikw_gin :: "bool \<Rightarrow> ivl" where
  "ikw_gin ctx = (if ctx then Ivl (Fin 0) (Fin 0) else Ivl (Fin 1) (Fin 1))"

definition ikw_slot :: "bool \<Rightarrow> ivl abs_state" where
  "ikw_slot ctx = (\<lambda>n. if n = ''G'' then ikw_gin ctx else bot)"

definition ikw_loc :: "pp \<Rightarrow> ivl abs_state" where
  "ikw_loc p = (\<lambda>n. if is_global n then bot
                   else if n = ''x'' then (if p = 0 then Ivl (Fin 0) (Fin 0)
                                             else if p = 2 then Ivl (Fin 2) (Fin 2)
                                             else bot)
                   else bot)"

definition ikw_locg :: "pp \<Rightarrow> bool \<Rightarrow> ivl abs_state" where
  "ikw_locg p ctx = ikw_loc p \<squnion> ikw_slot ctx"

definition ikw_dg :: "pp \<times> bool + bool \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state" where
  "ikw_dg u = (case u of Inl (p, ctx) \<Rightarrow> DG (ikw_locg p ctx) bot | Inr ctx \<Rightarrow> DG bot (ikw_slot ctx))"

subsection \<open>Keyed accessors and meaning equality\<close>

lemma dg_D_val: "ivl_dg.dg_D_c ikw_dg ctx p = ikw_locg p ctx"
  by (simp add: ivl_dg.dg_D_c_def ikw_dg_def)

lemma dg_G_val: "ivl_dg.dg_G_c ikw_dg ctx = ikw_slot ctx"
  by (simp add: ivl_dg.dg_G_c_def ikw_dg_def)

lemma locg_slot_eq: "ikw_locg p ctx = ikw_loc p \<squnion> ikw_slot ctx"
  by (simp add: ikw_locg_def)

lemma dg_meaning: "ivl_dg.dg_gamma_c ikw_dg ctx p = \<lbrakk>ikw_loc p \<squnion> ikw_slot ctx\<rbrakk>"
  by (simp add: ivl_dg.dg_gamma_c_def dg_D_val dg_G_val gamma_unit_def locg_slot_eq)

subsection \<open>Keyed separation\<close>

lemma contexts_separated:
  "ivl_dg.dg_G_c ikw_dg False \<noteq> ivl_dg.dg_G_c ikw_dg True"
proof
  assume eq: "ivl_dg.dg_G_c ikw_dg False = ivl_dg.dg_G_c ikw_dg True"
  then have "ivl_dg.dg_G_c ikw_dg False ''G'' = ivl_dg.dg_G_c ikw_dg True ''G''"
    by simp
  thus False
    by (simp add: dg_G_val ikw_slot_def ikw_gin_def)
qed

end
