theory Codegen
  imports "isabelle-purepy.Typing" "Python.Python_Setup"
begin

code_pred subty .
code_pred binop_overload .
code_pred unop_overload .

(* Resolve by enumerating overloads with compiled rules, since set comprehension is not executable *)
lemma resolve_binop_code [code]:
  "resolve_binop op \<sigma>\<^sub>1 \<sigma>\<^sub>2 =
    (let overloads = set_of_pred (binop_overload_i_i_i_PPooo op \<sigma>\<^sub>1 \<sigma>\<^sub>2);
         most_specific =
           Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> overloads. \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<tau>\<^sub>2 <: \<tau>\<^sub>2') overloads in
     if is_singleton most_specific then Some (snd (the_elem most_specific)) else None)"
proof -
  have S: "set_of_pred (binop_overload_i_i_i_PPooo op \<sigma>\<^sub>1 \<sigma>\<^sub>2) = {x. binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 x}"
    by (auto simp: binop_overload_i_i_i_PPooo_def)
  have MS: "Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> {x. binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 x}. \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<tau>\<^sub>2 <: \<tau>\<^sub>2')
      {x. binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 x} = {x. binop_most_specific op \<sigma>\<^sub>1 \<sigma>\<^sub>2 x}"
    by (auto simp: binop_most_specific_def split_def)
  show ?thesis
    unfolding Let_def S MS resolve_binop_def by simp
qed

lemma resolve_unop_code [code]:
  "resolve_unop op \<sigma> =
    (let overloads = set_of_pred (unop_overload_i_i_Poo op \<sigma>);
         most_specific = Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> overloads. \<tau> <: \<tau>') overloads in
     if is_singleton most_specific then Some (snd (the_elem most_specific)) else None)"
proof -
  have S: "set_of_pred (unop_overload_i_i_Poo op \<sigma>) = {x. unop_overload op \<sigma> x}"
    by (auto simp: unop_overload_i_i_Poo_def)
  have MS: "Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> {x. unop_overload op \<sigma> x}. \<tau> <: \<tau>') {x. unop_overload op \<sigma> x} =
      {x. unop_most_specific op \<sigma> x}"
    by (auto simp: unop_most_specific_def split_def)
  show ?thesis
    unfolding Let_def S MS resolve_unop_def by simp
qed

export_code stmt_ty
  in Python file_prefix "."

end
