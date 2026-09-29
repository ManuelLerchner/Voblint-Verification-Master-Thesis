(* src/Analyses/Shared/Nonrelational/Nonrelational_Transfer.thy *)
locale sound_nonrelational_ops =
  sound_special_ops "n_special ops" "n_aval ops"
  + backward: backward_domain_reductive "r_intersect (n_refine ops)" "n_aval ops"
      "r_tobool (n_refine ops)" "r_inv_less (n_refine ops)" "r_inv_eq (n_refine ops)"
      "r_inv_plus (n_refine ops)" "r_inv_minus (n_refine ops)" "r_inv_times (n_refine ops)"
  + check: abstract_check_domain "q_less (n_query ops)" "q_eq (n_query ops)" gamma_state
      "n_aval ops"
  for ops :: "'a::numeric_domain nonrelational_ops" +
  assumes top_eq: "n_top ops = top"
