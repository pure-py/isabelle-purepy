theory Syntax
    imports Main
begin

type_alias vname = string
type_alias fname = string
type_alias cname = string

datatype literal = Number int | Bool bool | None

datatype bop = Or | And | Eq | Neq | Lt | Leq | Gt | Geq | Add | Sub | Mul | Div
datatype uop = Not | Neg

datatype expr =
      Var vname                     (* x *)
    | Literal literal               (* 10 *)
    | BinOp bop expr expr           (* x + y *)
    | UnOp uop expr                 (* not x *)
    | CondExpr expr expr expr       (* 10 if True else 20 *)
    | List "expr list"              (* [10, 20, 40] *)
    | Tuple "expr list"             (* (10, 20, True) *)
    | Lambda "vname list" expr      (* lambda x: x * 2 *)

datatype stmt =
      Pass
    | Assign vname expr
    | Expr expr
    | Assert expr
    | AssertMsg expr expr
    | ReturnNone
    | Return expr
    | If expr "stmt list" "(expr \<times> stmt list) list"
    | IfElse  expr "stmt list" "(expr \<times> stmt list) list" "stmt list"
    | MutualRegion "func list"

and func = DefFunc fname "vname list" "stmt list"

end