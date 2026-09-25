(* src/Abstract_Interpreter/Domain/Abstract_Numeric_Queries.thy *)
locale abstract_numeric_queries = executable_numeric_queries less eq
  for less :: "'a::numeric_domain \<Rightarrow> 'a \<Rightarrow> bool option"
    and eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool option" +
  assumes less_sound[intro]:
      "less a b = Some r \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> (i < j) = r"
    and eq_sound[intro]:
      "eq a b = Some r \<Longrightarrow> i \<in> \<gamma> a \<Longrightarrow> j \<in> \<gamma> b \<Longrightarrow> (i = j) = r"
