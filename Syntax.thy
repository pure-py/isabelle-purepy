theory Syntax
    imports Main
begin

type_alias var = string

(* qualified name, aka non-empty list of vars *)
type_synonym qualified_name = "var \<times> var list"

(* literals *)
datatype lit =
    LitNumber int
  | LitString string
  | LitBool bool
  | LitNone

(* patterns *)
datatype pat =
    PatLiteral lit
  | PatNegLit int
  | PatVar var
  | PatWildcard
  | PatList "pat list"
  | PatTuple "pat list"
  | PatConstr qualified_name "pat list" "(var \<times> pat) list"
  | PatDict "(var \<times> pat) list"
  | PatAs pat var

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
    ExprVar var                                    (* x *)
  | ExprLiteral lit                                (* 10 *)
  | ExprCall expr "expr list" "(var \<times> expr) list"  (* f(1, 2, x = 10) *)
  | ExprDict "(expr \<times> expr) list"                  (* {"a": 1, "b": 2} *)
  | ExprAttribute expr var                         (* c.x *)
  | ExprSubscript expr "expr list"                 (* c["a"] *)
  | ExprBinOp bop expr expr                        (* x + y *)
  | ExprUnOp uop expr                              (* not x *)
  | ExprAnd expr expr                              (* x and y *)
  | ExprOr expr expr                               (* x or y *)
  | ExprCond expr expr expr                        (* 10 if True else 20 *)
  | ExprList "expr list"                           (* [10, 20, 40] *)
  | ExprTuple "expr list"                          (* (10, 20, True) *)
  | ExprListComp expr "guard list"                 (* [2*x for x in ...] *)
  | ExprDictComp "(expr \<times> expr)" "guard list"      (* {x: x**2 for x in range(5)} *)
  | ExprLambda "var list" expr                     (* lambda x: x * 2 *)

(* guards *)
and guard =
    Guard expr
  | Generator var expr

(* types *)
datatype ty =
    TypeAny
  | TypeNone
  | TypeBool
  | TypeInt
  | TypeFloat
  | TypeStr
  | TypeList ty
  | TypeTuple "ty list"
  | TypeDict ty
  | TypeCallable "ty list" ty
  | TypeClass var
  | TypeUnion ty ty

(* imports *)
datatype import =
    Import qualified_name
  | FromImport qualified_name "var list"

(* statements *)
datatype stmt =
    StmtPass
  | StmtSeq stmt stmt
  | StmtAssign var "ty option" expr
  | StmtExpr expr
  | StmtAssert expr
  | StmtAssertMsg expr expr
  | StmtReturnNone
  | StmtReturn expr
  | StmtIf expr stmt "(expr \<times> stmt) list" "stmt option"
  | StmtMatch expr "(pat \<times> stmt) list"
  | StmtMutualRegion "func list"

(* function definitions *)
and func = Def var "(var \<times> ty) list" ty stmt

(* field lists *)
datatype fields =
    FieldList "(string \<times> ty) list"
  | EmptyFieldList

(* top-level statements *)
datatype top_stmt =
    Stmt stmt
  | TopSeq top_stmt top_stmt
  | Dataclass var fields
  | DataclassExtend var var fields

(* module body *)
datatype module_body = ModuleBody "import list" top_stmt

end
