theory Codegen
  imports "isabelle-purepy.Executable" "Python.Python_Setup"
begin

(* Abort as expression in place of backend's raise statement; delete once backend prints abort as expression *)
code_printing constant Code.abort \<rightharpoonup> (Python) "(x for x in ()).throw(RuntimeError'(_'))"

export_code stmt_ty stmt_outcome
  in Python file_prefix "."

end
