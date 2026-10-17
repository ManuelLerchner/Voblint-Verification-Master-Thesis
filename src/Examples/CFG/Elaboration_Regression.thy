theory Elaboration_Regression
  imports "Voblint_VIMP.Core_Com" "Voblint_VIMP.VIMP_Notation"
begin

section \<open>Regression: typed elaboration\<close>

text \<open>Concrete programs that pin what typed elaboration means. Each statement is
  checked by evaluation, so a change to a kind rule, a conversion or a resolution
  fails here first.\<close>

abbreviation main_p :: pname where "main_p \<equiv> STR ''main''"
abbreviation f_p :: pname where "f_p \<equiv> STR ''f''"
abbreviation g_p :: pname where "g_p \<equiv> STR ''g''"

subsection \<open>Kinds\<close>

text \<open>Ranges and wraparound at fixed kinds, and the common kind of the usual
  arithmetic conversions, which does not depend on operand order.\<close>

lemma ik_bounds_pins:
  "ik_min I8 = - (2 ^ 7)" "ik_max I8 = 2 ^ 7 - 1"
  "ik_min U8 = 0" "ik_max U8 = 2 ^ 8 - 1"
  "ik_min I32 = - (2 ^ 31)" "ik_max I32 = 2 ^ 31 - 1"
  "ik_min U32 = 0" "ik_max U32 = 2 ^ 32 - 1"
  "ik_min I64 = - (2 ^ 63)" "ik_max I64 = 2 ^ 63 - 1"
  "ik_min U64 = 0" "ik_max U64 = 2 ^ 64 - 1"
  by eval+

lemma ik_norm_pins:
  "ik_norm U8 (2 ^ 8) = 0" "ik_norm U8 (- 1) = 2 ^ 8 - 1"
  "ik_norm I8 (2 ^ 7) = - (2 ^ 7)" "ik_norm I32 (2 ^ 31) = - (2 ^ 31)"
  "ik_norm U32 (- 1) = 2 ^ 32 - 1" "ik_norm I64 42 = 42"
  by eval+

lemma usual_kind_pins:
  "usual_kind I32 I32 = I32" "usual_kind I32 U32 = U32"
  "usual_kind I32 I64 = I64" "usual_kind I32 U64 = U64"
  "usual_kind U32 I64 = I64" "usual_kind U32 U64 = U64"  "usual_kind I64 U64 = U64"
    "usual_kind U8 I16 = I32"
  "usual_kind I64 U32 = I64" "usual_kind U64 I32 = U64"
  by eval+

subsection \<open>Equal formal names, different kinds\<close>

text \<open>\<open>f\<close> and \<open>g\<close> both take a formal \<open>n\<close>, at \<^const>\<open>U8\<close> and at \<^const>\<open>I64\<close>.
  Resolution keeps the two apart, so the same argument \<open>300\<close> wraps for \<open>f\<close> and does
  not for \<open>g\<close>. The kind environment is keyed by identity, so the order in which the two
  declarations are entered does not matter.\<close>

definition formals_fg :: "pname \<Rightarrow> vname list" where
  "formals_fg p = (if p = f_p \<or> p = g_p then [STR ''n''] else [])"

definition kenv_fg :: kenv where
  "kenv_fg = int_kenv(ScopedId f_p (STR ''n'') := U8, ScopedId g_p (STR ''n'') := I64)"

definition kenv_gf :: kenv where
  "kenv_gf = int_kenv(ScopedId g_p (STR ''n'') := I64, ScopedId f_p (STR ''n'') := U8)"

lemma formals_resolve_apart:
  "resolve_var (\<lambda>_. False) f_p (STR ''n'') \<noteq> resolve_var (\<lambda>_. False) g_p (STR ''n'')"
  by (simp add: resolve_var_eq_iff)

lemma same_argument_two_kinds:
  "map (\<lambda>a. eval a (\<lambda>_. 0)) (call_args (elab_com (\<lambda>_. False) formals_fg kenv_fg main_p
      (Call () None f_p [N 300]))) = [44]"
  "map (\<lambda>a. eval a (\<lambda>_. 0)) (call_args (elab_com (\<lambda>_. False) formals_fg kenv_fg main_p
      (Call () None g_p [N 300]))) = [300]"
  by eval+

lemma declaration_order_irrelevant:
  "elab_com (\<lambda>_. False) formals_fg kenv_fg main_p (Seq (Call () None f_p [N 300]) (Call () None g_p [N 300]))
   = elab_com (\<lambda>_. False) formals_fg kenv_gf main_p (Seq (Call () None f_p [N 300]) (Call () None g_p [N 300]))"
  by eval

subsection \<open>Wraparound and the usual arithmetic conversions\<close>

text \<open>Values computed at a kind wrap there, and mixed operands meet at the common kind
  of the usual arithmetic conversions before they are compared.\<close>

abbreviation x_v :: var_id where "x_v \<equiv> ScopedId main_p (STR ''x'')"
abbreviation u_v :: var_id where "u_v \<equiv> ScopedId main_p (STR ''u'')"

definition kenv_main :: kenv where
  "kenv_main = int_kenv(u_v := U8)"

definition kenv_u32 :: kenv where
  "kenv_u32 = int_kenv(u_v := U32)"

abbreviation res_main :: "vname \<Rightarrow> var_id" where
  "res_main \<equiv> resolve_var (\<lambda>_. False) main_p"

text \<open>\<open>u = u + 1\<close> at \<^const>\<open>U8\<close>: the sum is computed at \<^const>\<open>I32\<close>, where it is
  \<open>256\<close>, and the assignment converts it to \<open>0\<close>.\<close>

lemma unsigned_wraparound:
  "eval (assign_rhs (elab_com (\<lambda>_. False) (\<lambda>_. []) kenv_main main_p
     (Assign () (STR ''u'') (Plus (V (STR ''u'')) (N 1))))) ((\<lambda>_. 0)(u_v := 255)) = 0"
  by eval

text \<open>\<open>-1 < 1u\<close> is false in C: the usual arithmetic conversions turn \<open>-1\<close> into
  \<open>4294967295\<close> before the comparison.\<close>

lemma signed_unsigned_comparison:
  "eval (elaborate_syn res_main kenv_u32 (Less (V (STR ''x'')) (V (STR ''u''))))
     ((\<lambda>_. 0)(x_v := - 1, u_v := 1)) = 0"
  by eval

text \<open>A narrow sum inside a wide comparison wraps at its own kind before the
  comparison sees it: in \<open>4294967295 < u + 1\<close> with \<open>u = 4294967295\<close> at
  \<^const>\<open>U32\<close>, the sum wraps to \<open>0\<close>, and the comparison is false although it is
  computed at \<^const>\<open>I64\<close>.\<close>

lemma narrow_inside_wide:
  "eval (elaborate_syn res_main kenv_u32 (Less (N 4294967295) (Plus (V (STR ''u'')) (N 1))))
     ((\<lambda>_. 0)(u_v := 4294967295)) = 0"
  "esyn (kenv_u32 \<circ> res_main) (Plus (V (STR ''u'')) (N 1)) = U32"
  by eval+

text \<open>The comparison above is the one the source-level typed semantics prescribes,
  and the wrapping sum stays inside its kind's range, because the store holds a value
  of every variable's kind.\<close>

lemma u32_store_in_kinds: "all_in_kinds kenv_u32 ((\<lambda>_. 0)(x_v := - 1, u_v := 4294967295))"
  by (auto simp: all_in_kinds_def kenv_u32_def int_kenv_def ik_min_def ik_max_def ik_half_def
        ik_mod_def)

lemma comparison_matches_spec:
  "eval (elaborate_syn res_main kenv_u32 (Less (V (STR ''x'')) (V (STR ''u''))))
     ((\<lambda>_. 0)(x_v := - 1, u_v := 4294967295))
   = src_eval (kenv_u32 \<circ> res_main) (esyn (kenv_u32 \<circ> res_main) (Less (V (STR ''x'')) (V (STR ''u''))))
       (Less (V (STR ''x'')) (V (STR ''u''))) ((\<lambda>_. 0)(x_v := - 1, u_v := 4294967295) \<circ> res_main)"
  by (rule eval_elaborate_syn [OF u32_store_in_kinds])

lemma wrapping_sum_in_range:
  "eval (elaborate_syn res_main kenv_u32 (Plus (V (STR ''u'')) (N 1)))
     ((\<lambda>_. 0)(x_v := - 1, u_v := 4294967295))
   \<in> ik_range (exp_kind (elaborate_syn res_main kenv_u32 (Plus (V (STR ''u'')) (N 1))))"
  unfolding elaborate_syn_def by (rule eval_in_range [OF wt_exp_elaborate u32_store_in_kinds])

subsection \<open>Division and remainder\<close>

text \<open>Signed division truncates toward zero. \<open>INT_MIN / -1\<close> overflows, which C leaves
  undefined, and wraps here. Unsigned operands divide as natural numbers.\<close>

lemma division_at_kinds:
  "eval (elaborate_syn res_main int_kenv (Div (N (- 7)) (N 2))) (\<lambda>_. 0) = - 3"
  "eval (elaborate_syn res_main int_kenv (Mod (N (- 7)) (N 2))) (\<lambda>_. 0) = - 1"
  "eval (elaborate_syn res_main int_kenv (Div (V (STR ''x'')) (N (- 1))))
     ((\<lambda>_. 0)(x_v := - (2 ^ 31))) = - (2 ^ 31)"
  "eval (elaborate_syn res_main kenv_u32 (Div (V (STR ''u'')) (N 2))) ((\<lambda>_. 0)(u_v := 7)) = 3"
  by eval+

subsection \<open>Conversions at write sites\<close>

text \<open>An assignment, an argument and a return each convert to the kind they write
  to, and only where that kind differs from the value's own.\<close>

definition kenv_ret :: kenv where
  "kenv_ret = int_kenv(u_v := U8, ReturnId main_p := U8)"

lemma conversions_inserted:
  "elab_com (\<lambda>_. False) (\<lambda>_. []) kenv_ret main_p (Assign () (STR ''u'') (V (STR ''x'')))
     = Assign () u_v (TCast U8 (TVar I32 x_v))"
  "elab_com (\<lambda>_. False) (\<lambda>_. []) kenv_ret main_p (Assign () (STR ''x'') (V (STR ''x'')))
     = Assign () x_v (TVar I32 x_v)"
  "elab_com (\<lambda>_. False) (\<lambda>_. []) kenv_ret main_p (Return () (Some (V (STR ''x''))))
     = Return () (Some (TCast U8 (TVar I32 x_v)))"
  by eval+

text \<open>The arguments of \<open>min\<close> and \<open>max\<close> meet at their common kind, as the operands of
  C's \<open>MIN\<close> macro do: in \<open>min(x, u)\<close> with \<open>u\<close> at \<^const>\<open>U32\<close>, \<open>x = -1\<close> converts
  to \<open>4294967295\<close> before the two are compared.\<close>

definition min_xu :: "(unit, vname, src_exp) gcom" where
  "min_xu = Call () (Some (STR ''u'')) special_pname_min [V (STR ''x''), V (STR ''u'')]"

lemma library_arguments_kind:
  "args_kind (kenv_u32 \<circ> res_main) [V (STR ''x''), V (STR ''u'')] = U32"
  unfolding args_kind_pair by eval

lemma library_arguments_common_kind:
  "elab_com (\<lambda>_. False) (\<lambda>_. []) kenv_u32 main_p min_xu
     = Call () (Some u_v) special_pname_min [TCast U32 (TVar I32 x_v), TVar U32 u_v]"
  "map (\<lambda>a. eval a ((\<lambda>_. 0)(x_v := - 1, u_v := 1)))
     (call_args (elab_com (\<lambda>_. False) (\<lambda>_. []) kenv_u32 main_p min_xu)) = [4294967295, 1]"
  by eval+

subsection \<open>Names after resolution and the command skeleton\<close>

text \<open>A global keeps its identity in every procedure, erasure restores the source
  names, and elaboration leaves the skeleton that location elaboration reads.\<close>

definition sample_com :: "(unit, vname, src_exp) gcom" where
  "sample_com =
     Seq (Assign () (STR ''cnt'') (Plus (V (STR ''cnt'')) (V (STR ''x''))))
         (If () (Less (V (STR ''x'')) (N 3)) (Call () (Some (STR ''x'')) f_p [V (STR ''cnt'')])
             (Return () (Some (N 0))))"

lemma global_resolution:
  "resolve_var (\<lambda>y. y = STR ''cnt'') f_p (STR ''cnt'') = resolve_var (\<lambda>y. y = STR ''cnt'') main_p (STR ''cnt'')"
  by (simp add: resolve_var_eq_iff)

lemma sample_elaboration:
  "wt_com kenv_fg (\<lambda>p. map (resolve_var (\<lambda>y. y = STR ''cnt'') p) (formals_fg p)) main_p
     (elab_com (\<lambda>y. y = STR ''cnt'') formals_fg kenv_fg main_p sample_com)
   \<and> com_erase (elab_com (\<lambda>y. y = STR ''cnt'') formals_fg kenv_fg main_p sample_com) = sample_com
   \<and> map_gcom id (\<lambda>_. ()) (\<lambda>_. ()) (elab_com (\<lambda>y. y = STR ''cnt'') formals_fg kenv_fg main_p sample_com)
       = map_gcom id (\<lambda>_. ()) (\<lambda>_. ()) sample_com"
proof -
  have "\<forall>e \<in> set3_gcom sample_com. cast_free e" by eval
  then show ?thesis by (intro conjI wt_com_elab_com com_erase_elab_com skeleton_elab_com)
qed

end
