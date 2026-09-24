(* src/Program_Model/Compile/VIMP_Proc_to_CFG.thy *)
definition compile_proc ::
  "proc_table \<Rightarrow> pname \<Rightarrow> proc_decl \<Rightarrow> nat
   \<Rightarrow> nat \<times> (cfg_node \<times> edge_action \<times> cfg_node) set
        \<times> (cfg_node \<times> call_action \<times> cfg_node \<times> cfg_node) set"
where
  "compile_proc \<Pi> p decl n =
     (let r = n + csize (body decl);
          (n', ben, E, K) = compile \<Pi> p (body decl) (Statement r) n
      in (Suc r,
          insert (FunctionEntry p, EA_Body p, ben)
            (if falls_through (body decl)
             then insert (Statement r, EA_Ret None p, FunctionResult p) E
             else E),
          K))"
