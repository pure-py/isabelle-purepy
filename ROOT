session "isabelle-purepy" = HOL +
  options [timeout = 1200]
  sessions
    "HOL-Library"
  theories
    Util
    Syntax
    Semantics
    Correctness
    Contexts
    Reasons
    Types
    Subtyping
    Shapes
    Matching
    Operators
    Typing
    Programs
    Examples

session "isabelle-purepy-python" in "python" = "isabelle-purepy" +
  options [timeout = 1200]
  sessions
    Python
  theories
    Codegen
  export_files (in "python_out") "*:**"
