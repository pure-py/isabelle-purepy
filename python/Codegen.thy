theory Codegen
  imports "isabelle-purepy.Executable" "Python.Python_Setup"
begin

export_code stmt_ty
  in Python file_prefix "."

end
