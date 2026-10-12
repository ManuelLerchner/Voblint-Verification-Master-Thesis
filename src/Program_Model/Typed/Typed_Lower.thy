theory Typed_Lower
  imports Typed_Com "Voblint_VIMP.VIMP_Program"
begin

section \<open>Lowering typed programs to VIMP\<close>

text \<open>
  A typed program runs through the verified pipeline as an ordinary VIMP program. Lowering
  writes every conversion as a \<^const>\<open>Cast\<close>, computes every arithmetic node at its kind,
  reads every variable at its kind, and names every identity by its source name. Names
  suffice: VIMP has no shadowing, a global keeps its name in every procedure, and a local
  lives in its own activation, so within one activation a name identifies one variable.
  Kinds travel on the syntax, not in the name.

  Lowering is exact. \<open>lower_elaborate\<close> shows that the untyped evaluator
  \<^const>\<open>aval\<close> computes the typed source semantics \<^const>\<open>taval\<close> on the lowered
  expression, for every store. No typed-store premise is needed, because a lowered read
  converts the stored value to the variable's kind itself.
\<close>

text \<open>A conversion to a kind whose range contains the source kind's range changes no
  value, so lowering leaves it out; \<open>(i32) (u8) x\<close> lowers to \<open>(u8) x\<close>.\<close>

definition ik_widens :: "ikind \<Rightarrow> ikind \<Rightarrow> bool" where
  "ik_widens k ik \<longleftrightarrow> ik_min ik \<le> ik_min k \<and> ik_max k \<le> ik_max ik"

fun lower :: "texp \<Rightarrow> exp" where
  "lower (TN ik n) = N (ik_norm ik n)"
| "lower (TVar ik v) = Cast ik (V (var_name v))"
| "lower (TArith ik op a b) = Cast ik (aop_exp op (lower a) (lower b))"
| "lower (TCast ik a) = (if ik_widens (texp_kind a) ik then lower a else Cast ik (lower a))"
| "lower (TCmp op a b) = cop_exp op (lower a) (lower b)"
| "lower (TNot a) = Not (lower a)"
| "lower (TAnd a b) = And (lower a) (lower b)"
| "lower (TOr a b) = Or (lower a) (lower b)"

lemma aval_aop_exp [simp]: "\<lbrakk>aop_exp op a b\<rbrakk>\<^sub>e s = aop_eval op (\<lbrakk>a\<rbrakk>\<^sub>e s) (\<lbrakk>b\<rbrakk>\<^sub>e s)"
  by (cases op) simp_all

lemma aval_cop_exp [simp]:
  "\<lbrakk>cop_exp op a b\<rbrakk>\<^sub>e s = (if cop_eval op (\<lbrakk>a\<rbrakk>\<^sub>e s) (\<lbrakk>b\<rbrakk>\<^sub>e s) then 1 else 0)"
  by (cases op) simp_all

text \<open>Every lowered expression evaluates inside the range of its kind, which is what
  makes leaving out a widening conversion exact.\<close>

lemma aval_lower_in_range: "\<lbrakk>lower t\<rbrakk>\<^sub>e s \<in> ik_range (texp_kind t)"
  by (induction t) (auto simp: ik_widens_def)

lemma aval_lower_TCast [simp]: "\<lbrakk>lower (TCast ik a)\<rbrakk>\<^sub>e s = ik_norm ik (\<lbrakk>lower a\<rbrakk>\<^sub>e s)"
proof (cases "ik_widens (texp_kind a) ik")
  case True
  with aval_lower_in_range [of a s] have "\<lbrakk>lower a\<rbrakk>\<^sub>e s \<in> ik_range ik"
    by (auto simp: ik_widens_def)
  with True show ?thesis by simp
qed simp

theorem lower_elaborate:
  assumes "\<And>x. var_name (\<rho> x) = x"
  shows "\<lbrakk>lower (elaborate \<rho> \<kappa> ik e)\<rbrakk>\<^sub>e s = taval (\<kappa> \<circ> \<rho>) ik e s"
  by (induction e arbitrary: ik)
     (simp_all add: Let_def tcast_to_def arith_at_def assms del: lower.simps(4))

subsection \<open>Commands\<close>

text \<open>
  The analyzer runs a lowered command under the untyped semantics. \<open>lower_com_meaning\<close>
  says what that semantics then computes: every expression of the lowered command
  evaluates, on every store, to the typed meaning \<^const>\<open>taval\<close> of a source expression
  of the original command at some kind. A typed program's executions are therefore the
  untyped executions of its lowering, and each expression they evaluate has its machine
  meaning.
\<close>

abbreviation lower_com :: "'a tcom \<Rightarrow> ('a, vname, exp) gcom" where
  "lower_com \<equiv> map_gcom id var_name lower"

lemma meaning_witness:
  assumes "\<And>x. var_name (\<rho> x) = x" and "e' = lower (elaborate \<rho> \<kappa> ik a)" and "a \<in> A"
  shows "\<exists>e \<in> A. \<exists>ik. \<forall>s. \<lbrakk>e'\<rbrakk>\<^sub>e s = taval (\<kappa> \<circ> \<rho>) ik e s"
  using lower_elaborate [OF assms(1)] assms(2,3) by blast

lemma lower_elab_args_meaning:
  assumes var: "\<And>x. var_name (\<rho> x) = x"
  shows "e' \<in> set (map lower (elab_args \<rho> \<kappa> fs es))
           \<Longrightarrow> \<exists>e \<in> set es. \<exists>ik. \<forall>s. \<lbrakk>e'\<rbrakk>\<^sub>e s = taval (\<kappa> \<circ> \<rho>) ik e s"
proof (induction es arbitrary: fs)
  case Nil
  then show ?case by (cases fs) simp_all
next
  case (Cons e es)
  show ?case
  proof (cases fs)
    case Nil
    with Cons.prems obtain a where "a \<in> set (e # es)"
      and "e' = lower (elaborate \<rho> \<kappa> (esyn (\<kappa> \<circ> \<rho>) a) a)"
      by (auto simp: elaborate_syn_def)
    then show ?thesis by (rule meaning_witness [OF var, rotated])
  next
    case (Cons f fs')
    with Cons.prems have "e' = lower (elaborate \<rho> \<kappa> (\<kappa> f) e)
                            \<or> e' \<in> set (map lower (elab_args \<rho> \<kappa> fs' es))"
      by auto
    then show ?thesis
    proof
      assume "e' = lower (elaborate \<rho> \<kappa> (\<kappa> f) e)"
      then show ?thesis by (rule meaning_witness [OF var]) simp
    next
      assume "e' \<in> set (map lower (elab_args \<rho> \<kappa> fs' es))"
      with Cons.IH show ?thesis by auto
    qed
  qed
qed

lemma set3_lower_com: "set3_gcom (lower_com c) = lower ` set3_gcom c"
  by (induction c) (simp_all add: image_Un option.set_map)

lemma meaning_at:
  assumes "a \<in> A"
  shows "\<exists>e \<in> A. \<exists>ik'. \<forall>s. \<lbrakk>lower (elaborate (resolve_var \<G> q) \<kappa> ik a)\<rbrakk>\<^sub>e s
                         = taval (\<kappa> \<circ> resolve_var \<G> q) ik' e s"
  by (intro bexI [OF _ assms] exI [of _ ik] allI)
     (rule lower_elaborate [where \<rho> = "resolve_var \<G> q", OF var_name_resolve_var])

lemma elab_com_meaning:
  "x \<in> set3_gcom (elab_com \<G> fm \<kappa> q c)
     \<Longrightarrow> \<exists>e \<in> set3_gcom c. \<exists>ik. \<forall>s. \<lbrakk>lower x\<rbrakk>\<^sub>e s = taval (\<kappa> \<circ> resolve_var \<G> q) ik e s"
proof (induction c arbitrary: x)
  case (Assign i v e)
  then show ?case
    using meaning_at [of e "set3_gcom (Assign i v e)" \<G> q \<kappa> "\<kappa> (resolve_var \<G> q v)"]
    by (simp add: comp_def)
next
  case (Check i l e)
  then show ?case
    using meaning_at [of e "set3_gcom (Check i l e)" \<G> q \<kappa> "esyn (\<kappa> \<circ> resolve_var \<G> q) e"]
    by (simp add: elaborate_syn_def comp_def)
next
  case (Seq c1 c2)
  then show ?case by fastforce
next
  case (If i b c1 c2)
  then have "x = elaborate_syn (resolve_var \<G> q) \<kappa> b
               \<or> x \<in> set3_gcom (elab_com \<G> fm \<kappa> q c1) \<or> x \<in> set3_gcom (elab_com \<G> fm \<kappa> q c2)"
    by simp
  then show ?case
  proof (elim disjE)
    assume "x = elaborate_syn (resolve_var \<G> q) \<kappa> b"
    then show ?thesis
      using meaning_at [of b "set3_gcom (If i b c1 c2)" \<G> q \<kappa> "esyn (\<kappa> \<circ> resolve_var \<G> q) b"]
      by (simp add: elaborate_syn_def comp_def)
  next
    assume "x \<in> set3_gcom (elab_com \<G> fm \<kappa> q c1)"
    then show ?thesis using If.IH(1) by fastforce
  next
    assume "x \<in> set3_gcom (elab_com \<G> fm \<kappa> q c2)"
    then show ?thesis using If.IH(2) by fastforce
  qed
next
  case (While i b c)
  then have "x = elaborate_syn (resolve_var \<G> q) \<kappa> b \<or> x \<in> set3_gcom (elab_com \<G> fm \<kappa> q c)"
    by simp
  then show ?case
  proof (elim disjE)
    assume "x = elaborate_syn (resolve_var \<G> q) \<kappa> b"
    then show ?thesis
      using meaning_at [of b "set3_gcom (While i b c)" \<G> q \<kappa> "esyn (\<kappa> \<circ> resolve_var \<G> q) b"]
      by (simp add: elaborate_syn_def comp_def)
  next
    assume "x \<in> set3_gcom (elab_com \<G> fm \<kappa> q c)"
    then show ?thesis using While.IH by fastforce
  qed
next
  case (Call i dst p es)
  then have "lower x \<in> set (map lower (elab_args (resolve_var \<G> q) \<kappa> (map (resolve_var \<G> p) (fm p)) es))"
    by simp
  then show ?case
    using lower_elab_args_meaning [where \<rho> = "resolve_var \<G> q", OF var_name_resolve_var]
    by (simp add: comp_def)
next
  case (Return i e)
  then obtain a where "e = Some a" "x = elaborate (resolve_var \<G> q) \<kappa> (\<kappa> (ReturnId q)) a"
    by (cases e) auto
  then show ?case
    using meaning_at [of a "set3_gcom (Return i e)" \<G> q \<kappa> "\<kappa> (ReturnId q)"]
    by (simp add: comp_def)
qed simp_all

theorem lower_com_meaning:
  assumes "e' \<in> set3_gcom (lower_com (elab_com \<G> fm \<kappa> q c))"
  shows "\<exists>e \<in> set3_gcom c. \<exists>ik.
           \<forall>s. \<lbrakk>e'\<rbrakk>\<^sub>e s = taval (\<kappa> \<circ> resolve_var \<G> q) ik e s"
  using assms elab_com_meaning by (fastforce simp: set3_lower_com)

subsection \<open>Programs\<close>

text \<open>
  Kinds are declared per identity, and an identity without a declaration is a C \<open>int\<close>.
  \<open>typed_prog p ds\<close> elaborates every procedure of \<open>p\<close> under the declarations \<open>ds\<close>
  and lowers it. It keeps the procedure names, formals and globals, so the lowered program
  is checked, compiled and analyzed as any other.
\<close>

type_synonym kind_decls = "(var_id \<times> ikind) list"

definition kenv_of :: "kind_decls \<Rightarrow> kenv" where
  "kenv_of ds v = (case map_of ds v of Some k \<Rightarrow> k | None \<Rightarrow> I32)"

definition prog_formals :: "imp_prog \<Rightarrow> pname \<Rightarrow> vname list" where
  "prog_formals p q = (case prog_table p q of Some d \<Rightarrow> formals d | None \<Rightarrow> [])"

definition typed_proc :: "imp_prog \<Rightarrow> kind_decls \<Rightarrow> pname \<Rightarrow> proc_decl \<Rightarrow> proc_decl" where
  "typed_proc p ds q d =
     d\<lparr>body := lower_com (elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d))\<rparr>"

definition typed_prog :: "imp_prog \<Rightarrow> kind_decls \<Rightarrow> imp_prog" where
  "typed_prog p ds = p\<lparr>proc_rep := map (\<lambda>(q, d). (q, typed_proc p ds q d)) (proc_rep p)\<rparr>"

lemma declared_global_typed_prog [simp]: "declared_global (typed_prog p ds) = declared_global p"
  by (rule ext) (simp add: typed_prog_def)

text \<open>Every procedure of the typed program is the lowering of the same procedure of the
  source program, with its formals unchanged. Together with \<open>lower_com_meaning\<close>, this
  is what an execution of the typed program means: the untyped semantics of the lowered
  bodies, whose every expression computes its machine meaning.\<close>

theorem prog_table_typed_prog:
  "prog_table (typed_prog p ds) q = map_option (typed_proc p ds q) (prog_table p q)"
proof -
  have "map_of (map (\<lambda>(q, d). (q, typed_proc p ds q d)) xs) q
          = map_option (typed_proc p ds q) (map_of xs q)" for xs :: "(pname \<times> proc_decl) list"
    by (induction xs) auto
  then show ?thesis by (simp add: prog_table_def typed_prog_def)
qed

lemma typed_proc_simps [simp]:
  "formals (typed_proc p ds q d) = formals d"
  "body (typed_proc p ds q d)
     = lower_com (elab_com (declared_global p) (prog_formals p) (kenv_of ds) q (body d))"
  by (simp_all add: typed_proc_def)

text \<open>Lowering keeps the command skeleton, so the lowered program compiles to a graph of
  the same shape; only the expressions on its edges change.\<close>

theorem skeleton_lower_com:
  "map_gcom id (\<lambda>_. ()) (\<lambda>_. ()) (lower_com c) = map_gcom id (\<lambda>_. ()) (\<lambda>_. ()) c"
  by (simp add: gcom.map_comp comp_def id_def)

end
