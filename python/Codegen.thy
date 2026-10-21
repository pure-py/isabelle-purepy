theory Codegen
  imports "isabelle-purepy.Typing" "Python.Python_Setup"
begin

code_pred subty .
code_pred binop_overload .
code_pred unop_overload .

(* Enumerate overloads with compiled rules, since set comprehension is not executable *)
lemma binop_overloads_code [code]:
  "binop_overloads op \<sigma>\<^sub>1 \<sigma>\<^sub>2 = set_of_pred (binop_overload_i_i_i_PPooo op \<sigma>\<^sub>1 \<sigma>\<^sub>2)"
  by (auto simp: binop_overloads_def binop_overload_i_i_i_PPooo_def)

lemma unop_overloads_code [code]:
  "unop_overloads op \<sigma> = set_of_pred (unop_overload_i_i_Poo op \<sigma>)"
  by (auto simp: unop_overloads_def unop_overload_i_i_Poo_def)

export_code stmt_ty
  in Python file_prefix "."

end
