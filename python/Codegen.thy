theory Codegen
  imports "isabelle-purepy.Typing" "isabelle-purepy.Util" "Python.Python_Setup"
begin

code_pred subty .
code_pred binop_overload .
code_pred unop_overload .

(* Overload resolution is a definite description, which cannot be executed; compiled overload rules give
   finite set of overloads to choose from *)
lemma resolve_binop_code [code]:
  "resolve_binop op \<sigma>\<^sub>1 \<sigma>\<^sub>2 =
    (let bs = set_of_pred (binop_overload_i_i_i_PPooo op \<sigma>\<^sub>1 \<sigma>\<^sub>2) in
     map_option snd (the_unique (Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> bs. \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<tau>\<^sub>2 <: \<tau>\<^sub>2') bs)))"
proof -
  have S: "set_of_pred (binop_overload_i_i_i_PPooo op \<sigma>\<^sub>1 \<sigma>\<^sub>2) = {x. binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 x}"
    by (auto simp: binop_overload_i_i_i_PPooo_def)
  have MS: "Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> {x. binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 x}. \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<tau>\<^sub>2 <: \<tau>\<^sub>2')
      {x. binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 x} = {x. binop_most_specific op \<sigma>\<^sub>1 \<sigma>\<^sub>2 x}"
    by (auto simp: binop_most_specific_def split_def)
  show ?thesis
    unfolding Let_def S MS resolve_binop_def the_unique_def by simp
qed

lemma resolve_unop_code [code]:
  "resolve_unop op \<sigma> =
    (let bs = set_of_pred (unop_overload_i_i_Poo op \<sigma>) in
     map_option snd (the_unique (Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> bs. \<tau> <: \<tau>') bs)))"
proof -
  have S: "set_of_pred (unop_overload_i_i_Poo op \<sigma>) = {x. unop_overload op \<sigma> x}"
    by (auto simp: unop_overload_i_i_Poo_def)
  have MS: "Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> {x. unop_overload op \<sigma> x}. \<tau> <: \<tau>') {x. unop_overload op \<sigma> x} =
      {x. unop_most_specific op \<sigma> x}"
    by (auto simp: unop_most_specific_def split_def)
  show ?thesis
    unfolding Let_def S MS resolve_unop_def the_unique_def by simp
qed

export_code stmt_ty
  in Python file_prefix "."

end
