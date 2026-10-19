(* src/Analyses/Nonrelational/Nonrelational_Domain.thy *)
class kind_int_domain = ik_domain +
  fixes top_ik :: "ikind \<Rightarrow> 'a::{bounded_semilattice_sup_bot, order_top}"
    and of_int_ik :: "ikind \<Rightarrow> int \<Rightarrow> 'a"
    and cast_ik :: "signed_overflow_policy \<Rightarrow> ikind option \<Rightarrow> ikind \<Rightarrow> 'a \<Rightarrow> 'a"
    and arith_ik :: "signed_overflow_policy \<Rightarrow> ikind \<Rightarrow> aop \<Rightarrow> bool \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and cmp_ik :: "cop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool option"
    and meet_ik :: "'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and refine_ik :: "cop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a"
    and raw_aop_ik :: "aop \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a"
    and fits_ik :: "ikind \<Rightarrow> 'a \<Rightarrow> bool"
    and answer_ik :: "'a \<Rightarrow> answer"
    and of_answer_ik :: "ikind option \<Rightarrow> answer \<Rightarrow> 'a"
  assumes top_ik_sound: "n \<in> ik_range k \<Longrightarrow> n \<in> \<gamma> (top_ik k)"
    and of_int_ik_sound: "ik_norm k n \<in> \<gamma> (of_int_ik k n)"
    and cast_ik_sound:
      "(\<And>k'. sk = Some k' \<Longrightarrow> n \<in> ik_range k') \<Longrightarrow> n \<in> \<gamma> a
         \<Longrightarrow> ik_norm k n \<in> \<gamma> (cast_ik ovp sk k a)"
    and arith_ik_sound:
      "(operands_fit \<Longrightarrow> m \<in> ik_range k \<and> n \<in> ik_range k) \<Longrightarrow> m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b
         \<Longrightarrow> ik_norm k (aop_eval op m n) \<in> \<gamma> (arith_ik ovp k op operands_fit a b)"
    and cmp_ik_sound:
      "cmp_ik c a b = Some r \<Longrightarrow> m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> cop_eval c m n = r"
    and meet_ik_sound: "m \<in> \<gamma> a \<Longrightarrow> m \<in> \<gamma> b \<Longrightarrow> m \<in> \<gamma> (meet_ik a b)"
    and refine_ik_sound:
      "cop_eval c m n \<Longrightarrow> m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b
         \<Longrightarrow> m \<in> \<gamma> (fst (refine_ik c a b)) \<and> n \<in> \<gamma> (snd (refine_ik c a b))"
    and raw_aop_ik_sound: "m \<in> \<gamma> a \<Longrightarrow> n \<in> \<gamma> b \<Longrightarrow> aop_eval op m n \<in> \<gamma> (raw_aop_ik op a b)"
    and fits_ik_sound: "fits_ik k a \<Longrightarrow> n \<in> \<gamma> a \<Longrightarrow> n \<in> ik_range k"
    and answer_ik_sound: "n \<in> \<gamma> a \<Longrightarrow> n \<in> gamma_answer (answer_ik a)"
    and of_answer_ik_sound:
      "(\<And>k. sk = Some k \<Longrightarrow> n \<in> ik_range k) \<Longrightarrow> n \<in> gamma_answer q
         \<Longrightarrow> n \<in> \<gamma> (of_answer_ik sk q)"
