theory Syntax
    imports Main
begin

type_alias vname = string

(* qualified name, aka non-empty list of vars *)
type_synonym qualified_name = "vname \<times> vname list"

(* literals *)
datatype l =
    LitNumber int
  | LitString string
  | LitBool bool
  | LitNone

(* patterns *)
datatype p =
    PatLiteral l
  | PatNegLit int
  | PatVar vname
  | PatWildcard
  | PatList "p list"
  | PatTuple "p list"
  | PatConstr qualified_name "p list" "(vname \<times> p) list"
  | PatDict "(vname \<times> p) list"
  | PatAs p vname

(* operators *)
datatype bop = 
    BOpEq 
  | BOpNeq 
  | BOpLt 
  | BOpLeq 
  | BOpGt 
  | BOpGeq 
  | BOpBitOr
  | BOpAdd 
  | BOpSub 
  | BOpMul 
  | BOpDiv

datatype uop = UOpNot | UOpNeg

(* expressions *)
datatype expr =
    ExprVar vname                                                 (* x *)
  | ExprLiteral l                                                 (* 10 *)
  | ExprCall expr "expr list" "(vname \<times> expr) list"              (* f(1, 2, x = 10) *)
  | ExprDict "(expr \<times> expr) list"                                 (* {"a": 1, "b": 2} *)
  | ExprAttribute expr vname                                      (* c.x *)
  | ExprSubscript expr "expr list"                                (* c["a"] *)
  | ExprBinOp bop expr expr                                       (* x + y *)
  | ExprUnOp uop expr                                             (* not x *)
  | ExprAnd expr expr                                             (* x and y *)
  | ExprOr expr expr                                              (* x or y *)
  | ExprCond expr expr expr                                       (* 10 if True else 20 *)
  | ExprList "expr list"                                          (* [10, 20, 40] *)
  | ExprTuple "expr list"                                         (* (10, 20, True) *)
  | ExprListComp expr "guard list"                                (* [2*x for x in ...] *)
  | ExprDictComp "(expr \<times> expr)" "guard list"                     (* {x: x**2 for x in range(5)} *)
  | ExprLambda "vname list" expr                                  (* lambda x: x * 2 *)
  
(* guards *)
and guard =
    Guard expr
  | Generator vname expr

(* types *)
datatype \<tau> =
    TypeAny
  | TypeNone
  | TypeBool
  | TypeInt
  | TypeFloat
  | TypeStr
  | TypeList \<tau>
  | TypeTuple "\<tau> list"
  | TypeDict \<tau>
  | TypeCallable "\<tau> list" \<tau>
  | TypeClass vname
  | TypeUnion \<tau> \<tau>

(* type annotations *)
type_synonym \<pi> = "\<tau> option"

(* return type annotations *)
type_synonym \<omega> = "\<tau> option"

(* imports *)
datatype \<iota> =
    Import qualified_name
  | FromImport qualified_name "vname list"

(* statements *)
datatype stmt =
    StmtPass
  | StmtSeq stmt stmt
  | StmtAssign vname \<pi> expr
  | StmtExpr expr
  | StmtAssert expr
  | StmtAssertMsg expr expr
  | StmtReturnNone
  | StmtReturn expr
  | StmtIf expr stmt "(expr \<times> stmt) list" "stmt option"
  | StmtMatch expr "(p \<times> stmt) list"
  | StmtMutualRegion "func list"

(* function definitions *)
and func = Def vname "(vname \<times> \<pi>) list" \<omega> stmt

(* field lists *)
datatype \<Phi> =
    FieldList "(string \<times> \<tau>) list"
  | EmptyFieldList

(* top-level statements *)
datatype t =
    Stmt stmt
  | TopSeq t t
  | Dataclass vname \<Phi>
  | DataclassExtend vname vname \<Phi>

(* module body *)
datatype \<mu> = ModuleBody "\<iota> list" t

end