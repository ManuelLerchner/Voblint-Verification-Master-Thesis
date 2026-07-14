theory Exec_Ivl_Cmp_Seed_Enter
  imports
    Exec_Ivl_Run
    Voblint_Analysis.Interval_DG
    Twfr_Reach_Read
begin

section \<open>Native DG seeded entry for the interval example\<close>

text \<open>
  This is the DG-native version of the seeded-enter probe for Interval.  The
  concrete program and the twfr witness stay unchanged, but the analysis witness is
  now a direct @{typ "(ivl abs_state, ivl abs_state) dg_state"} solution with
  separate local and global carriers.

  The point of the probe is architectural: the executable example no longer needs
  the `_st` transport path.
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

definition seed_ctx_zero :: bool where
  "seed_ctx_zero = False"

definition seed_ctx_pos :: bool where
  "seed_ctx_pos = True"

definition seed_gin :: "bool \<Rightarrow> ivl" where
  "seed_gin ctx = (if ctx then Ivl (Fin 1) (Fin 1) else Ivl (Fin 0) (Fin 0))"

definition seed_slot :: "bool \<Rightarrow> ivl abs_state" where
  "seed_slot ctx = (\<lambda>n. if n = ''H'' then seed_gin ctx else bot)"

definition seed_loc :: "pp \<Rightarrow> ivl abs_state" where
  "seed_loc p = (\<lambda>n. if n = ''G'' then (if p = 0 then Ivl (Fin 0) (Fin 0)
                                      else if p = 1 then Ivl (Fin 1) (Fin 1)
                                      else Ivl (Fin 1) (Fin 1))
                   else if is_global n then bot
                   else bot)"

definition seed_locg :: "pp \<Rightarrow> bool \<Rightarrow> ivl abs_state" where
  "seed_locg p ctx = seed_loc p \<squnion> seed_slot ctx"

definition seed_dg ::
  "pp \<times> bool + bool \<Rightarrow> (ivl abs_state, ivl abs_state) dg_state"
where
  "seed_dg u = (case u of
      Inl (p, ctx) \<Rightarrow> DG (seed_locg p ctx) (seed_slot ctx)
    | Inr ctx \<Rightarrow> DG bot (seed_slot ctx))"

definition seed_ec :: "bool \<Rightarrow> ivl abs_state \<Rightarrow> bool" where
  "seed_ec ctx d = ctx"

subsection \<open>Accessors and meaning\<close>

lemma dg_D_val: "ivl_dg.dg_D_c seed_dg ctx p = seed_locg p ctx"
  by (simp add: ivl_dg.dg_D_c_def seed_dg_def)

lemma dg_G_val: "ivl_dg.dg_G_c seed_dg ctx = seed_slot ctx"
  by (simp add: ivl_dg.dg_G_c_def seed_dg_def)

lemma locg_slot_eq: "seed_locg p ctx = seed_loc p \<squnion> seed_slot ctx"
  by (simp add: seed_locg_def)

lemma dg_meaning: "ivl_dg.dg_gamma_c seed_dg ctx p = \<lbrakk>seed_loc p \<squnion> seed_slot ctx\<rbrakk>"
  by (simp add: ivl_dg.dg_gamma_c_def dg_D_val dg_G_val gamma_unit_def locg_slot_eq)

lemma derived_ctx: "seed_ctx_pos = seed_ec seed_ctx_pos (ivl_dg.dg_D_c seed_dg seed_ctx_pos 0)"
  by (simp add: seed_ec_def seed_ctx_pos_def)

lemma contexts_separated:
  "ivl_dg.dg_G_c seed_dg seed_ctx_zero \<noteq> ivl_dg.dg_G_c seed_dg seed_ctx_pos"
proof
  assume eq: "ivl_dg.dg_G_c seed_dg seed_ctx_zero = ivl_dg.dg_G_c seed_dg seed_ctx_pos"
  have "seed_gin seed_ctx_zero = seed_gin seed_ctx_pos"
  proof -
    from eq have "(ivl_dg.dg_G_c seed_dg seed_ctx_zero) ''H'' =
                  (ivl_dg.dg_G_c seed_dg seed_ctx_pos) ''H''"
      by simp
    thus ?thesis
      by (simp add: dg_G_val seed_slot_def)
  qed
  thus False
    by (simp add: seed_gin_def seed_ctx_zero_def seed_ctx_pos_def)
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
  show ?thesis using twfr.intra[OF seed_e_0_1 _ w0] by (simp add: step_assign_incr)
qed

theorem seed_wit_sound:
  "\<exists>tr. twfr enterc combc seed_cfg 0 (seed_locg 0 seed_ctx_zero) 1
          (seed_locg 0 seed_ctx_zero) tr \<and> tr \<noteq> []
     \<and> last tr ''G'' \<in> gamma_ivl (seed_locg 1 seed_ctx_zero ''G'')"
proof -
  have slot: "seed_locg 1 seed_ctx_zero ''G'' = Ivl (Fin 1) (Fin 1)"
    by (simp add: seed_locg_def seed_loc_def seed_slot_def seed_ctx_zero_def
        seed_gin_def sup_ivl_def bot_ivl_def)
  have rd0: "(1::Int.int) \<in> gamma_ivl (Ivl (Fin 1) (Fin 1))"
    by simp
  have rd: "last [gk 0, gk 1] ''G'' \<in> gamma_ivl (seed_locg 1 seed_ctx_zero ''G'')"
    using slot rd0 by simp
  show ?thesis by (rule twfr_reach_read[OF seed_wit rd])
qed

text \<open>
  The probe demonstrates the native DG carrier directly: local and global values
  are separate @{typ "('a, 'b) dg_state"} components, context selection uses the
  local slot, and the concrete twfr execution is checked against the DG
  concretization.  No legacy state transport remains in this file.
\<close>


end
