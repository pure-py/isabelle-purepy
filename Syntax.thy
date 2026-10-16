theory Syntax
  imports Complex_Main
begin

type_alias var = string

type_synonym name = "var \<times> var list"

datatype lit =
    LitInt int
  | LitFloat real  (* reals, so nan is not modelled *)
  | LitString string
  | LitBool bool
  | LitNone

type_synonym 'u args = "'u list \<times> (var \<times> 'u) list"

datatype pat =
    PatLiteral lit                 (* 10 *)
  | PatVar var                     (* x *)
  | PatWildcard                    (* _ *)
  | PatList "pat list"             (* [p, q] *)
  | PatTuple "pat list"            (* (p, q) *)
  | PatConstr name "pat args"      (* C(p, x=q) *)
  | PatDict "(string \<times> pat) list"  (* {"a": p} *)
  | PatAs pat var                  (* p as x *)

datatype bop =
    BOpBitOr
  | BOpEq
  | BOpNeq
  | BOpLt
  | BOpLeq
  | BOpGt
  | BOpGeq
  | BOpAdd
  | BOpSub
  | BOpMul
  | BOpDiv
  | BOpFloorDiv
  | BOpMod
  | BOpPow
  | BOpIn
  | BOpNotIn

datatype uop = UOpNot | UOpPos | UOpNeg

datatype expr =
    ExprVar var                              (* x *)
  | ExprLiteral lit                          (* 10 *)
  | ExprCall expr "expr args"                (* f(1, 2, x=10) *)
  | ExprDict "(expr \<times> expr) list"            (* {"a": 1, "b": 2} *)
  | ExprAttribute expr var                   (* c.x *)
  | ExprSubscript expr expr                  (* c["a"] *)
  | ExprBinOp bop expr expr                  (* x + y *)
  | ExprUnOp uop expr                        (* not x *)
  | ExprAnd expr expr                        (* x and y *)
  | ExprOr expr expr                         (* x or y *)
  | ExprCond expr expr expr                  (* 10 if b else 20 *)
  | ExprList "expr list"                     (* [10, 20, 40] *)
  | ExprTuple "expr list"                    (* (10, 20, True) *)
  | ExprListComp expr "qualifier list"       (* [2 * x for x in xs] *)
  | ExprDictComp expr expr "qualifier list"  (* {x: x ** 2 for x in xs} *)
  | ExprLambda "var list" expr               (* lambda x: x * 2 *)
and qualifier =
    Guard expr                               (* if x > 0 *)
  | Generator var expr                       (* for x in xs *)

datatype prim_ty =
    TyObject
  | TyNever
  | TyNone
  | TyBool
  | TyInt
  | TyFloat
  | TyStr
  | TySized

datatype ty_expr =
    TyExprPrim prim_ty
  | TyExprList ty_expr
  | TyExprTuple "ty_expr list"
  | TyExprDict ty_expr
  | TyExprCallable "ty_expr list" ty_expr
  | TyExprLiteral lit
  | TyExprName name "ty_expr list"
  | TyExprUnion ty_expr ty_expr

datatype ty =
    TyPrim prim_ty
  | TyList ty
  | TyTuple "ty list"
  | TyDict ty
  | TyCallable "ty list" ty
  | TyLiteral lit
  | TyVar var
  | TyClass name "ty list"
  | TyUnion ty ty

datatype scheme =
    TyScheme "var list" ty
  | FieldScheme "var list" "(var \<times> ty) list"

datatype import =
    Import name
  | FromImport name "var list"

datatype stmt =
    StmtPass                                             (* pass *)
  | StmtSeq stmt stmt                                    (* s; t *)
  | StmtDeclare var ty_expr                              (* x: int *)
  | StmtAssign var "ty_expr option" expr                 (* x: int = e *)
  | StmtExpr expr                                        (* f(x) *)
  | StmtAssert expr                                      (* assert e *)
  | StmtAssertMsg expr expr                              (* assert e, "msg" *)
  | StmtReturnNone                                       (* return *)
  | StmtReturn expr                                      (* return e *)
  | StmtIf expr stmt "(expr \<times> stmt) list" "stmt option"  (* if e: s else: t *)
  | StmtMatch expr "(pat \<times> stmt) list"                   (* match e: case p: s *)
  | StmtMutualRegion "func list"                         (* def f(): s *)
and func = Def var "(var \<times> ty_expr) list" ty_expr stmt   (* def f(x: T) -> U: s *)

datatype fields =
    FieldList "(var \<times> ty_expr) list"
  | EmptyFieldList

datatype type_def =
    Dataclass var "var list" fields
  | DataclassExtend var "var list" name "ty_expr list" fields
  | TypeAlias var "var list" ty_expr

datatype top_stmt =
    Stmt stmt
  | TopSeq top_stmt top_stmt
  | TypeDefs "type_def list"

datatype module_body = ModuleBody "import list" top_stmt

end
