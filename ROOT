session "isabelle-purepy" = HOL +
  options [timeout = 600]
  sessions
    "HOL-Library"
  theories
    Util
    Syntax
    Semantics
    Determinism
    Eval
    Correctness
    Typing
    Examples

session "isabelle-purepy-python" in "python" = "isabelle-purepy" +
  options [timeout = 600]
  sessions
    Python
  theories
    Codegen
  export_files (in "python_out") "*:**"
