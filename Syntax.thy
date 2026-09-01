theory Syntax
    imports Main
begin

type_alias vname = string
type_alias fname = string
type_alias cname = string

(* qualified name *)
type_synonym q = "vname \<times> vname list"

(* literals *)
datatype l =
    Number int
  | String string
  | Bool bool
  | LitNone

(* patterns *)
datatype p =
    PatLiteral l
  | PatNegLit int
  | PatVar vname
  | PatWildcard
  | PatList "p list"
  | PatTuple "p list"
  | PatConstr q "p list" "(vname \<times> p) list"
  | PatDict "(string \<times> p) list"
  | PatAs p vname

(* operators *)
datatype bop = Or | And | Eq | Neq | Lt | Leq | Gt | Geq | Add | Sub | Mul | Div
datatype uop = Not | Neg

(* expressions *)
datatype e =
    Var vname                                 (* x *)
  | Literal l                                 (* 10 *)
  | Call e "e list"                           (* f (1, 2, False) *)
  | Constr q "e list" "(vname \<times> e) list"      (* C(1, 2, x = 10) *)
  | Dict "(e \<times> e) list"                       (* {"a": 1, "b": 2} *)
  | Attribute e vname                         (* c.x *)
  | Subscript e e                             (* c["a"] *)
  | BinOp bop e e                             (* x + y *)
  | UnOp uop e                                (* not x *)
  | CondExpr e e e                            (* 10 if True else 20 *)
  | List "e list"                             (* [10, 20, 40] *)
  | Tuple "e list"                            (* (10, 20, True) *)
  | ListComp e "g list"                       (* [2*x for x in ...] *)
  | DictComp "(e \<times> e)" "g list"               (* {x: x**2 for x in range(5)} *)
  | Lambda "vname list" e                     (* lambda x: x * 2 *)
  
(* guards *)
and g =
    Guard e
  | Generator vname e

(* types *)
datatype \<tau> =
    Any
  | None
  | Bool
  | Int
  | Float
  | Str
  | List \<tau>
  | Tuple "\<tau> list"
  | Dict \<tau>
  | Callable "\<tau> list" \<tau>
  | Class cname
  | Union \<tau> \<tau>

(* type annotations *)
type_synonym \<pi> = "\<tau> option"

(* return type annotations *)
type_synonym \<omega> = "\<tau> option"

(* imports *)
datatype \<iota> =
    Import q
  | FromImport q "vname list"

(* statements *)
datatype s =
    Pass
  | Seq s s
  | Assign vname \<pi> e
  | Expr e
  | Assert e
  | AssertMsg e e
  | ReturnNone
  | Return e
  | If e s "(e \<times> s) list" "e option"
  | Match e "(e \<times> s) list"
  | MutualRegion "d list"

(* function definitions *)
and d = Def fname "(vname \<times> \<pi>) list" \<omega> s

(* field lists *)
datatype \<Phi> =
    FieldList "(string \<times> \<tau>) list"
  | EmptyFieldList

(* top-level statements *)
datatype t =
    Stmt s
  | TopSeq t t
  | Dataclass cname \<Phi>
  | DataclassExtend cname cname \<Phi>

(* module body *)
datatype \<mu> = ModuleBody "\<iota> list" t

end