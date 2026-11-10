session "isabelle-purepy" = HOL +
  description "mechanisation in Isabelle"
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
    Values
    Semantics
    Determinism
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

session "isabelle-purepy-soundness" in "soundness" = "isabelle-purepy" +
  description "type soundness"
  options [timeout = 1200, quick_and_dirty]
  theories
    WellFormed
    WellFormedExpressions
    WellFormedStatements
    Extension
    ExtensionExpressions
    ExtensionStatements
    ValueTyping
    ResultTyping
    Instances
    Expressions
    Attributes
    Comprehensions
    Calls
    Dispatch
    Statements
    WellFormedModules
    Soundness
