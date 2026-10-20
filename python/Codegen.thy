theory Codegen
  imports "isabelle-purepy.Typing" "Python.Python_Setup"
begin

code_pred subty .
code_pred binop_overload .
code_pred unop_overload .
code_pred eval_expr .

export_code
  mlet_result compose call_result is_closure as_real
  def_name binds assigns declares scope
  merge_undefined merge_cxt_entry override_outcome
  base_type_lit base_type sized subty join joins meet meets
  prim_name resolve_type equality_type binop_overload unop_overload numeric_literal
  scheme_cxt_entry def_signature
  in Python file_prefix "."

end
