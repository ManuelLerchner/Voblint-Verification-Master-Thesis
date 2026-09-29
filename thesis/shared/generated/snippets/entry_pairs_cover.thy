(* src/Abstract_Interpreter/Framework/Spec/DG_Spec_Sound.thy *)
definition entry_pairs_cover ::
  "('D \<Rightarrow> 's set) \<Rightarrow> 's \<Rightarrow> 's \<Rightarrow> 'D enter_result list \<Rightarrow> bool"
where
  "entry_pairs_cover gammaD caller entered pairs \<longleftrightarrow>
     (\<exists>cont entry. (cont, entry) \<in> set pairs
        \<and> caller \<in> gammaD cont \<and> entered \<in> gammaD entry)"
