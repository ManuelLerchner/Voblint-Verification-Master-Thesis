theory Sign_Exec
  imports Exec_Bridge Sign_Domain
begin

section \<open>Sign per-domain seam: executable transfer mirror and commutation\<close>

instance sign :: bounded_warrowing ..



text \<open>
  The generic S4 effectful transport (\<open>Exec_Bridge.part_post_solution_st_to_abs_eff\<close>) is
  parameterised over an executable transfer mirror \<open>tf_st\<close> with the commutation
  hypothesis \<open>fun_of_st (tf_st a s) = apply_tf tf a (fun_of_st s)\<close>.  This theory
  discharges that obligation for the sign domain: \<open>sign_tf_st\<close> mirrors
  \<open>apply_tf sign_tf\<close> at \<open>sign st\<close>, action by action, and \<open>sign_tf_st_commute\<close>
  proves the commutation.  This is the single domain-specific piece of S4; every
  other ingredient is generic in the value domain.
\<close>

lemma fun_of_st_update:
  "fun_of_st (update_st s x v) = (fun_of_st s)(x := v)"
  by (rule ext) (metis fun_upd_apply lookup_update_diff lookup_update_same)

subsection \<open>Assume mirror: executable backward filter on \<open>sign st\<close>\<close>

text \<open>
  Executable mirrors of the abstract backward filters @{const afilter_sign}
  and @{const bfilter_sign}, computed on the finite-map state
  @{typ "sign st"}.  Each commutes with its abstract counterpart through @{const fun_of_st},
  using @{thm fun_of_st_update} for the variable write, @{thm fun_of_st_sup} for the
  de Morgan joins, and the structural induction matching the abstract definition.
\<close>

fun afilter_sign_st :: "aexp => sign => sign st => sign st" where
    "afilter_sign_st (BaseN (AExp.V x)) a s = update_st s x (meet_sign a (lookup_st s x))"
  | "afilter_sign_st (Plus  e1 e2) a s =
       (let (a1, a2) = inv_plus_sign  a (aval_sign e1 (lookup_st s)) (aval_sign e2 (lookup_st s))
        in afilter_sign_st e1 a1 (afilter_sign_st e2 a2 s))"
  | "afilter_sign_st (Minus e1 e2) a s =
       (let (a1, a2) = inv_minus_sign a (aval_sign e1 (lookup_st s)) (aval_sign e2 (lookup_st s))
        in afilter_sign_st e1 a1 (afilter_sign_st e2 a2 s))"
  | "afilter_sign_st (Times e1 e2) a s =
       (let (a1, a2) = inv_times_sign a (aval_sign e1 (lookup_st s)) (aval_sign e2 (lookup_st s))
        in afilter_sign_st e1 a1 (afilter_sign_st e2 a2 s))"
  | "afilter_sign_st _ a s = s"

fun bfilter_sign_st :: "bexp => bool => sign st => sign st" where
    "bfilter_sign_st (Less e1 e2) res s =
       (let (a1, a2) = inv_less_sign res (aval_sign e1 (lookup_st s)) (aval_sign e2 (lookup_st s))
        in afilter_sign_st e1 a1 (afilter_sign_st e2 a2 s))"
  | "bfilter_sign_st (Not b) res s = bfilter_sign_st b (\<not> res) s"
  | "bfilter_sign_st (And b1 b2) True  s = bfilter_sign_st b1 True  (bfilter_sign_st b2 True  s)"
  | "bfilter_sign_st (And b1 b2) False s = bfilter_sign_st b1 False s \<squnion> bfilter_sign_st b2 False s"
  | "bfilter_sign_st (Or  b1 b2) True  s = bfilter_sign_st b1 True  s \<squnion> bfilter_sign_st b2 True  s"
  | "bfilter_sign_st (Or  b1 b2) False s = bfilter_sign_st b1 False (bfilter_sign_st b2 False s)"
  | "bfilter_sign_st (Eq  e1 e2) True  s =
       (let a = meet_sign (aval_sign e1 (lookup_st s)) (aval_sign e2 (lookup_st s))
        in afilter_sign_st e1 a (afilter_sign_st e2 a s))"
  | "bfilter_sign_st _ _ s = s"

 
lemma afilter_sign_st_commute:
  "fun_of_st (afilter_sign_st e a s) = afilter_sign e a (fun_of_st s)"
proof (induction e arbitrary: a s)
  case (BaseN x)
  show ?case by (cases x; simp add: fun_of_st_update)
next
  case (Plus e1 e2)
  show ?case by (simp add: Plus.IH)
next
  case (Minus e1 e2)
  show ?case by (simp add: Minus.IH)
next
  case (Times e1 e2)
  show ?case by (simp add: Times.IH)
qed

lemma bfilter_sign_st_commute:
  "fun_of_st (bfilter_sign_st b res s) = bfilter_sign b res (fun_of_st s)"
proof (induction b arbitrary: res s)
  case (BaseB x)
  then show ?case by simp
next
  case (Not b)
  then show ?case by simp
next
  case (And b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: And.IH)
  next
    case False
    then show ?thesis by (simp add: And.IH)
  qed
next
  case (Or b1 b2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: Or.IH)
  next
    case False
    then show ?thesis by (simp add: Or.IH)
  qed
next
  case (Less e1 e2)
  then show ?case by (simp add: afilter_sign_st_commute split: prod.splits)
next
  case (Eq e1 e2)
  show ?case
  proof (cases res)
    case True
    then show ?thesis by (simp add: afilter_sign_st_commute Let_def)
  next
    case False
    then show ?thesis by simp
  qed
qed


definition assume_sign_st :: "bexp => sign st => sign st" where
  "assume_sign_st b s = bfilter_sign_st b True s"

definition assume_not_sign_st :: "bexp => sign st => sign st" where
  "assume_not_sign_st b s = bfilter_sign_st b False s"

lemma assume_sign_st_commute:
  "fun_of_st (assume_sign_st b s) = assume_sign b (fun_of_st s)"
  by (simp add: assume_sign_st_def assume_sign_def bfilter_sign_st_commute)

lemma assume_not_sign_st_commute:
  "fun_of_st (assume_not_sign_st b s) = assume_not_sign b (fun_of_st s)"
  by (simp add: assume_not_sign_st_def assume_not_sign_def bfilter_sign_st_commute)

subsection \<open>Enter mirror (reset locals to top, keep globals)\<close>

lemma fun_rep_enter_sign_rep:
  "fun_rep_st ((\<lambda>(dl, dg, ps). (STop, dg, filter (\<lambda>(x, _). is_global x) ps)) r)
   = (\<lambda>x. if is_global x then fun_rep_st r x else STop)"
proof -
  obtain dl dg ps where r: "r = (dl, dg, ps)" using prod_cases3 by blast
  show ?thesis unfolding r
    by (rule ext) (auto simp: map_of_filter_key split: option.split)
qed

lift_definition enter_sign_st :: "sign st \<Rightarrow> sign st"
  is "\<lambda>(dl, dg, ps). (STop, dg, filter (\<lambda>(x, _). is_global x) ps)"
  by (auto simp: eq_st_def fun_rep_enter_sign_rep fun_eq_iff)

lemma enter_sign_st_commute:
  "fun_of_st (enter_sign_st s) = enter_sign (fun_of_st s)"
  unfolding enter_sign_def
  by transfer (simp add: fun_rep_enter_sign_rep)

subsection \<open>The executable sign transfer function\<close>

fun sign_tf_st :: "edge_action \<Rightarrow> sign st \<Rightarrow> sign st" where
    "sign_tf_st EA_Nop s = s"
  | "sign_tf_st (EA_Assign x a) s = update_st s x (aval_sign a (lookup_st s))"
  | "sign_tf_st (EA_Assume b) s = assume_sign_st b s"
  | "sign_tf_st (EA_AssumeNot b) s = assume_not_sign_st b s"
  | "sign_tf_st EA_Enter s = enter_sign_st s"

subsection \<open>Sound input seed: top everywhere\<close>

text \<open>
  \<open>top_sign_st\<close> represents \<open>\<lambda>_. STop\<close> (every variable unknown).  Its
  concretisation is the whole store space (\<open>gamma_state (\<lambda>_. STop) = UNIV\<close>), so
  seeding the analysis with it makes the certified result non-vacuous -- the
  whole point of the two-region rep (a bot-default seed would force an empty
  concretisation).
\<close>

lift_definition top_sign_st :: "sign st" is "(STop, STop, [])" .

lemma lookup_top_sign_st [simp]: "lookup_st top_sign_st x = STop"
  by transfer simp

lemma fun_of_st_top_sign_st: "fun_of_st top_sign_st = (\<lambda>_. STop)"
  by (rule ext) simp

subsection \<open>C-faithful initialisation seed: globals at zero, locals unknown\<close>

text \<open>
  In C, globals are zero-initialised before \<open>main\<close> starts (ISO C \<section>6.7.9p10);
  locals are uninitialized and may hold any value (UB to read before writing).
  \<open>cinit_sign_st\<close> reflects this: global default \<open>SZero\<close>, local default \<open>STop\<close>.
  Its concretisation is \<open>cinit_stores\<close> (defined in Sign_Exec_Sound): exactly the
  stores where every global is 0 and locals are arbitrary.
  Joining any concrete write against \<open>SZero\<close> (rather than \<open>STop\<close>) lets the
  richer lattice contribute: e.g.\ \<open>SZero \<squnion> SPos = SNonNeg\<close> instead of \<open>STop\<close>.
\<close>

lift_definition cinit_sign_st :: "sign st" is "(STop, SZero, [])" .

lemma lookup_cinit_sign_st [simp]:
  "lookup_st cinit_sign_st x = (if is_global x then SZero else STop)"
  by transfer simp

lemma fun_of_st_cinit_sign_st:
  "fun_of_st cinit_sign_st = (\<lambda>x. if is_global x then SZero else STop)"
  by (rule ext) simp

subsection \<open>The executable sign transfer function\<close>

theorem sign_tf_st_commute:
  "fun_of_st (sign_tf_st a s) = apply_tf sign_tf a (fun_of_st s)"
proof (cases a)
  case EA_Nop
  then show ?thesis by simp
next
  case (EA_Assign x e)
  then show ?thesis
    by (simp add: sign_tf_def assign_sign_def fun_of_st_update)
next
  case (EA_Assume b)
  then show ?thesis
    by (simp add: sign_tf_def assume_sign_st_commute)
next
  case (EA_AssumeNot b)
  then show ?thesis apply (auto simp add: sign_tf_def)
    using assume_not_sign_st_commute by presburger
next
  case EA_Enter
  then show ?thesis by (simp add: sign_tf_def enter_sign_st_commute)
qed

subsection \<open>Executable effectful transfer record\<close>

definition sign_etf_st :: "(unit, sign st) effectful_st_transfer" where
  "sign_etf_st = \<lparr>
    etf_st_nop        = unit_edge_tree_st (sign_tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. unit_edge_tree_st (sign_tf_st (EA_Assign x e))),
    etf_st_assume     = (\<lambda>b. unit_edge_tree_st (sign_tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. unit_edge_tree_st (sign_tf_st (EA_AssumeNot b))),
    etf_st_enter      = unit_edge_tree_st (sign_tf_st EA_Enter),
    etf_st_combine    = unit_combine_tree_st
  \<rparr>"

lemma sign_etf_st_edge_tree:
  "apply_etf_st sign_etf_st a u = unit_edge_tree_st (sign_tf_st a) u"
  unfolding sign_etf_st_def by (cases a) simp_all

lemma sign_etf_st_combine_tree:
  "etf_combine_st sign_etf_st cc ex = unit_combine_tree_st cc ex"
  unfolding sign_etf_st_def by simp

lemma sign_etf_st_exists_unit:
  "\<And>a u. \<exists>f. apply_etf_st sign_etf_st a u = unit_edge_tree_st f u"
  using sign_etf_st_edge_tree by blast

subsection \<open>Executable examples\<close>

value "lookup_st top_sign_st ''x''"
value "lookup_st cinit_sign_st ''Gx''"
value "lookup_st cinit_sign_st ''x''"

value "lookup_st (sign_tf_st (EA_Assign ''x'' (IMP2_Syntax.N 1)) top_sign_st) ''x''"
value "lookup_st (sign_tf_st (EA_Assume (Less (IMP2_Syntax.V ''x'') (IMP2_Syntax.N 0))) cinit_sign_st) ''x''"

end
