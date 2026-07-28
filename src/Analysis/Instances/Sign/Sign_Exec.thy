theory Sign_Exec
  imports Exec_Bridge Sign_Domain
begin

section \<open>Sign per-domain seam: executable transfer mirror and commutation\<close>

instance sign :: bounded_warrowing ..



text \<open>
  Executable transport requires the finite-map transfer to commute with its
  abstract-state interpretation. The sign transfer proves this once, action by
  action; the generic bridge supplies the remaining solver transport.
\<close>

text \<open>
  \<open>afilter_sign_st\<close> / \<open>bfilter_sign_st\<close> and their commutation with
  @{const afilter_sign} / @{const bfilter_sign} through @{const fun_of_st}
  come from \<open>Sign_Backward\<close> -- the sign specialization of the generic
  @{locale backward_domain} executable mirror (\<open>Exec_Backward\<close>). The
  commutation induction is proved once there, not per domain.
\<close>


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

lemma enter_frame_sign_st_commute:
  "fun_of_st (enter_sign_st s) = enter_frame_sign (fun_of_st s)"
  unfolding enter_frame_sign_def
  by transfer (simp add: fun_rep_enter_sign_rep)

subsection \<open>The executable sign transfer function\<close>

fun sign_tf_st :: "edge_action \<Rightarrow> sign st \<Rightarrow> sign st" where
    "sign_tf_st EA_Nop s = s"
  | "sign_tf_st (EA_Assign x a) s = update_st s x (aval_sign a (lookup_st s))"
  | "sign_tf_st (EA_Assume b) s = assume_sign_st b s"
  | "sign_tf_st (EA_AssumeNot b) s = assume_not_sign_st b s"
  | "sign_tf_st (EA_Ret e _) s = (case e of
      None \<Rightarrow> s
    | Some a \<Rightarrow> update_st s ret_var (aval_sign a (lookup_st s)))"

lemma sign_tf_st_ret_none [simp]:
  "sign_tf_st (EA_Ret None p) = sign_tf_st EA_Nop"
  by (rule ext) simp

lemma sign_tf_st_ret_some [simp]:
  "sign_tf_st (EA_Ret (Some a) p) = sign_tf_st (EA_Assign ret_var a)"
  by (rule ext) simp

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
    by (simp add: sign_tf_def assign_sign_def fun_of_st_update_st)
next
  case (EA_Assume b)
  then show ?thesis
    by (simp add: sign_tf_def assume_sign_st_commute)
next
  case (EA_AssumeNot b)
  then show ?thesis apply (auto simp add: sign_tf_def)
    using assume_not_sign_st_commute by presburger
next
  case (EA_Ret e p)
  then show ?thesis
    by (cases e) (simp_all add: sign_tf_def fun_of_st_update_st assign_sign_def)
qed

subsection \<open>Executable effectful transfer record\<close>

text \<open>The named caller-entry transfer is shared by the effectful transfer record and the D/G
  registration, so executable entry semantics has one implementation.\<close>
definition sign_enter_st :: "vname list \<Rightarrow> aexp list \<Rightarrow> sign st \<Rightarrow> sign st" where
  "sign_enter_st xs es s =
     bind_formals_abs_st xs (map (\<lambda>e. aval_sign e (lookup_st s)) es) (enter_sign_st s)"

lemma sign_enter_st_commute:
  "fun_of_st (sign_enter_st xs es s) = tf_enter sign_tf xs es (fun_of_st s)"
  by (simp add: sign_enter_st_def sign_tf_def enter_sign_def enter_frame_sign_st_commute)

definition sign_etf_st :: "(unit, sign st) effectful_st_transfer" where
  "sign_etf_st = \<lparr>
    etf_st_nop        = unit_edge_tree_st (sign_tf_st EA_Nop),
    etf_st_assign     = (\<lambda>x e. unit_edge_tree_st (sign_tf_st (EA_Assign x e))),
    etf_st_assume     = (\<lambda>b. unit_edge_tree_st (sign_tf_st (EA_Assume b))),
    etf_st_assume_not = (\<lambda>b. unit_edge_tree_st (sign_tf_st (EA_AssumeNot b))),
    etf_st_enter      = (\<lambda>xs es. unit_edge_tree_st (sign_enter_st xs es)),
    etf_st_combine    = unit_combine_tree_st
  \<rparr>"

lemma sign_etf_st_edge_tree:
  "apply_etf_st sign_etf_st a u = unit_edge_tree_st (sign_tf_st a) u"
  unfolding sign_etf_st_def by (cases a) (auto simp: sign_etf_st_def split: option.splits)

lemma sign_etf_st_combine_tree:
  "etf_combine_st sign_etf_st dst cc ex = unit_combine_tree_st dst cc ex"
  unfolding sign_etf_st_def by simp

lemma sign_etf_st_enter_tree:
  "etf_st_enter sign_etf_st xs es u = unit_edge_tree_st (sign_enter_st xs es) u"
  unfolding sign_etf_st_def by simp

lemma sign_etf_st_enter_exists_unit:
  "\<And>u xs es. \<exists>f. etf_st_enter sign_etf_st xs es u = unit_edge_tree_st f u"
  using sign_etf_st_enter_tree by blast


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
