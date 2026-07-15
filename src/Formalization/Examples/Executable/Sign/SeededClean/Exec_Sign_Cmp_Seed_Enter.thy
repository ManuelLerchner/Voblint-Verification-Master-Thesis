theory Exec_Sign_Cmp_Seed_Enter
  imports
    "Voblint_Analysis.Sign_Exec_Sound"
    "Voblint_Analysis.Sign_DG"
    Twfr_Reach_Read
begin

section \<open>Native DG seeded entry for the sign example\<close>

text \<open>
  This is the DG-native version of the seeded-enter probe.  It keeps the concrete
  program and the twfr witness, but the analysis witness is now a direct
  \<open>dg_state\<close> solution with separate local and global carriers.

  The point of the probe is architectural: the executable example uses the
  native DG seeded-clean witness directly.
\<close>

subsection \<open>The program\<close>

definition seed_prog :: imp_prog where
  "seed_prog = \<lbrakk>
     int G;

     void f() {
       G := G + 1
     }
     void main() {
       G := 0;
       f();
       G := 1;
       f()
     }
   \<rbrakk>"

definition seed_cfg :: cfg where
  "seed_cfg = compile_prog (prog_table seed_prog) (prog_procs seed_prog) (prog_main seed_prog)"

subsection \<open>A concrete DG witness\<close>

definition seed_ctx_zero :: "bool" where
  "seed_ctx_zero = False"

definition seed_ctx_pos :: "bool" where
  "seed_ctx_pos = True"

definition seed_gin :: "bool \<Rightarrow> sign" where
  "seed_gin ctx = (if ctx then SPos else SZero)"

definition seed_slot :: "bool \<Rightarrow> sign abs_state" where
  "seed_slot ctx = (\<lambda>n. if n = ''H'' then (if ctx then SPos else SZero) else SBot)"

definition seed_loc :: "pp \<Rightarrow> sign abs_state" where
  "seed_loc p = (\<lambda>n. if n = ''G'' then (if p = 0 then SZero
                                      else if p = 1 then SPos
                                      else SNonNeg)
                   else if is_global n then SBot
                   else SBot)"

definition seed_locg :: "pp \<Rightarrow> bool \<Rightarrow> sign abs_state" where
  "seed_locg p ctx = seed_loc p \<squnion> seed_slot ctx"

definition seed_ec :: "bool \<Rightarrow> sign abs_state \<Rightarrow> bool" where
  "seed_ec ctx s = ctx"

definition seed_dg ::
  "pp \<times> bool + bool \<Rightarrow> (sign abs_state, sign abs_state) dg_state"
where
  "seed_dg u = (case u of
      Inl (p, ctx) \<Rightarrow> DG (seed_locg p ctx) (seed_slot ctx)
    | Inr ctx \<Rightarrow> DG bot (seed_slot ctx))"

subsection \<open>Accessors and meaning\<close>

lemma dg_D_val: "sign_dg.dg_D_c seed_dg ctx p = seed_locg p ctx"
  by (simp add: sign_dg.dg_D_c_def seed_dg_def)

lemma dg_G_val: "sign_dg.dg_G_c seed_dg ctx = seed_slot ctx"
  by (simp add: sign_dg.dg_G_c_def seed_dg_def)

lemma locg_slot_eq: "seed_locg p ctx \<squnion> seed_slot ctx = seed_loc p \<squnion> seed_slot ctx"
  by (simp add: seed_locg_def seed_slot_def seed_loc_def fun_eq_iff)

lemma dg_meaning: "sign_dg.dg_gamma_c seed_dg ctx p = \<lbrakk>seed_loc p \<squnion> seed_slot ctx\<rbrakk>"
  by (simp add: sign_dg.dg_gamma_c_def dg_D_val dg_G_val gamma_unit_def locg_slot_eq)

lemma derived_ctx: "seed_ec ctx (sign_dg.dg_D_c seed_dg ctx 0) = ctx"
  by (simp add: seed_ec_def dg_D_val seed_locg_def seed_gin_def)

lemma contexts_separated:
  "sign_dg.dg_G_c seed_dg seed_ctx_zero \<noteq> sign_dg.dg_G_c seed_dg seed_ctx_pos"
proof
  assume eq: "sign_dg.dg_G_c seed_dg seed_ctx_zero = sign_dg.dg_G_c seed_dg seed_ctx_pos"
  then have "sign_dg.dg_G_c seed_dg seed_ctx_zero ''H'' = sign_dg.dg_G_c seed_dg seed_ctx_pos ''H''"
    by simp
  thus False
    by (simp add: dg_G_val seed_slot_def seed_ctx_zero_def seed_ctx_pos_def)
qed

subsection \<open>Concrete execution\<close>

lemma seed_e_0_1:
  "(0, EA_Assign ''G'' (Plus (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 1)), 1) \<in> edges seed_cfg"
  unfolding seed_cfg_def seed_prog_def by eval

lemma seed_wit:
  "twfr enterc combc seed_cfg 0 (seed_locg 0 seed_ctx_zero) 1
     (seed_locg 0 seed_ctx_zero) [gk 0, gk 1]"
proof -
  have w0: "twfr enterc combc seed_cfg 0 (seed_locg 0 seed_ctx_zero) 0
              (seed_locg 0 seed_ctx_zero) [gk 0]"
    by (rule twfr.start)
  have no_enter: "\<not> is_enter_action (EA_Assign ''G'' (Plus (IMP2_Syntax.V ''G'') (IMP2_Syntax.N 1)))"
    by (simp add: is_enter_action_def)
  show ?thesis using twfr.intra[OF seed_e_0_1 no_enter w0] by (simp add: step_assign_incr)
qed

theorem seed_wit_sound:
  "\<exists>tr. twfr enterc combc seed_cfg 0 (seed_locg 0 seed_ctx_zero) 1
          (seed_locg 0 seed_ctx_zero) tr \<and> tr \<noteq> []
     \<and> last tr ''G'' \<in> gamma_sign (seed_locg 1 seed_ctx_zero ''G'')"
proof -
  have slot: "seed_locg 1 seed_ctx_zero ''G'' = SPos"
    by (simp add: seed_locg_def seed_loc_def seed_slot_def seed_ctx_zero_def seed_gin_def sup_sign_def)
  have rd0: "(1::Int.int) \<in> gamma_sign SPos"
    by simp
  have rd: "last [gk 0, gk 1] ''G'' \<in> gamma_sign (seed_locg 1 seed_ctx_zero ''G'')"
    using slot rd0 by simp
  show ?thesis by (rule twfr_reach_read[OF seed_wit rd])
qed


text \<open>
  The probe demonstrates the native DG carrier directly: local and global values
  are separate \<open>dg_state\<close> components, context selection uses the local slot, and
  the concrete twfr execution is checked against the DG concretization.
\<close>

end
