theory Codegen
  imports "isabelle-purepy.Executable" "Python.Python_Setup"
begin

(* Abort as expression, since the backend prints it as raise statement; retire once the backend fixes this *)
code_printing constant Code.abort \<rightharpoonup> (Python) "(x for x in ()).throw(RuntimeError'(_'))"

export_code
  mlet_result compose call_result is_closure as_real
  def_name binds assigns declares scope
  merge_undefined merge_cxt_entry override_outcome
  base_type_lit base_type sized subty join joins meet meets
  prim_name resolve_type equality_type numeric_literal
  scheme_cxt_entry def_signature
  resolve_binop resolve_unop synth check merge stmt_ty
  expr_result stmt_outcome
  in Python file_prefix "."

end
