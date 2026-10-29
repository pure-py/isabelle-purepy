session "isabelle-purepy" = HOL +
  options [timeout = 1200]
  sessions
    "HOL-Library"
  theories
    Util
    Floats
    Strings
    Positions
    Syntax
    Contexts
    Reasons
    Types
    Semantics
    Determinism
    Eval
    Correctness
    Subtyping
    Shapes
    Patterns
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
