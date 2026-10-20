theory Codegen
  imports "isabelle-purepy.Executable" "Python.Python_Setup"
begin

(* The Python code generator translates an abort into a raise statement, which is a syntax error inside an
   expression. Here an abort is translated into an expression that raises the same exception; delete this
   once the generator translates aborts into expressions. *)
code_printing constant Code.abort \<rightharpoonup> (Python) "(x for x in ()).throw(RuntimeError'(_'))"

export_code stmt_ty
  in Python file_prefix "."

end
