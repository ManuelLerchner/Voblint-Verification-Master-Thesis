theory IMP2_Collecting
  imports IMP2_Semantics
begin

(*
  Collecting Semantics for IMP2.

  For each command c and input set S, `collect c S` is the set of all
  states c can produce from some s \<in> S.

  Key fact for WHILE:
    lfp of  T \<mapsto> S \<union> collect c {s \<in> T. bval b s}
  characterises loop-head-reachable states; exit states add \<not>bval b.

  Note: collect (WHILE b DO c) S \<noteq> lfp F in general —
  diverging runs contribute to lfp but not to collect.
*)

(* \<midarrow>\<midarrow> Definition \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

definition collect :: "com \<Rightarrow> store set \<Rightarrow> store set" where
  "collect c S = {t. \<exists>s \<in> S. (c, s) \<Rightarrow> t}"


(* \<midarrow>\<midarrow> Start State lemmas \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

lemma collect_empty [simp]:
  "collect c {} = {}"
  unfolding collect_def by simp

lemma collect_union [simp]:
  "collect c (S \<union> T) = collect c S \<union> collect c T"
  unfolding collect_def by blast

lemma collect_insert:
  "collect c (insert s S) = collect c {s} \<union> collect c S"
  unfolding collect_def by blast

lemma collect_mono:
  "S \<subseteq> T \<Longrightarrow> collect c S \<subseteq> collect c T"
  unfolding collect_def by blast

(* \<midarrow>\<midarrow> Structural lemmas \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)


lemma collect_SKIP [simp]:
  "collect SKIP S = S"
  unfolding collect_def by blast

lemma collect_Assign [simp]:
  "collect (x ::= a) S = {s(x := aval a s) | s. s \<in> S}"
  unfolding collect_def by blast

lemma collect_Seq[simp]:
  "collect (c1 ;; c2) S = collect c2 (collect c1 S)"
  unfolding collect_def by blast

lemma collect_If[simp]:
  "collect (IF b THEN c1 ELSE c2) S =
     collect c1 {s \<in> S. bval b s} \<union> collect c2 {s \<in> S. \<not> bval b s}"
  unfolding collect_def by auto


(* \<midarrow>\<midarrow> WHILE: fixpoint characterisation \<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow>\<midarrow> *)

definition while_fun :: "bexp \<Rightarrow> com \<Rightarrow> store set \<Rightarrow> store set \<Rightarrow> store set" where
  "while_fun b c S T = S \<union> collect c {s \<in> T. bval b s}"

lemma while_fun_mono:
  "mono (while_fun b c S)"
  unfolding mono_def while_fun_def collect_def by auto

(* \<subseteq> direction: loop execution stays in lfp and exits with \<not>b *)
lemma while_preserves_lfp:
  "\<lbrakk> (WHILE b DO c, s) \<Rightarrow> t; s \<in> lfp (while_fun b c S) \<rbrakk>
   \<Longrightarrow> t \<in> lfp (while_fun b c S) \<and> \<not> bval b t"
proof (induction "WHILE b DO c" s t rule: big_step_induct)
  case (WhileFalse s) then show ?case by simp
next
  case (WhileTrue s s' t)
  then have "s' \<in> lfp (while_fun b c S)"
    by (smt (verit, ccfv_threshold) IMP2_Collecting.collect_def UnCI lfp_unfold mem_Collect_eq
        while_fun_def while_fun_mono) 
  then show ?case
    by (simp add: WhileTrue.hyps(5))  
qed

(* \<supseteq> direction: every lfp exit state is reachable from some s₀ \<in> S *)
lemma while_lfp_exit_collect:
  "\<lbrakk> x \<in> lfp (while_fun b c S); \<not> bval b x \<rbrakk>
   \<Longrightarrow> \<exists>s \<in> S. (WHILE b DO c, s) \<Rightarrow> x"
proof -
  assume x_lfp : "x \<in> lfp (while_fun b c S)"
  assume nbx   : "\<not> bval b x"
  let ?Q = "{y. \<forall>t. (WHILE b DO c, y) \<Rightarrow> t
                 \<longrightarrow> (\<exists>s\<^sub>0 \<in> S. (WHILE b DO c, s\<^sub>0) \<Rightarrow> t)}"

  have "while_fun b c S ?Q \<subseteq> ?Q"
    unfolding while_fun_def apply(auto)
    using IMP2_Collecting.collect_def by auto

  then have "lfp (while_fun b c S) \<subseteq> ?Q"
    using lfp_lowerbound by blast
   
  with x_lfp nbx show ?thesis
    by blast
qed

lemma collect_While:
  "collect (WHILE b DO c) S = {t \<in> lfp (while_fun b c S). \<not> bval b t}"
  unfolding collect_def 
  apply(auto)
  apply (metis (no_types, lifting) UnCI lfp_unfold while_fun_def while_fun_mono
      while_preserves_lfp)
  apply (metis (no_types, lifting) UnCI lfp_unfold while_fun_def while_fun_mono
      while_preserves_lfp)
  by (simp add: while_lfp_exit_collect)
 

end