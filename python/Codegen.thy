theory Codegen
  imports "isabelle-purepy.Executable" "Python.Python_Setup"
begin

(* Abort as expression, since the backend prints it as raise statement; retire once the backend fixes this *)
code_printing constant Code.abort \<rightharpoonup> (Python) "(x for x in ()).throw(RuntimeError'(_'))"

export_code stmt_ty stmt_outcome
  in Python file_prefix "."

end
