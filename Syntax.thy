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
    PatLiteral lit
  | PatVar var
  | PatWildcard
  | PatList "pat list"
  | PatTuple "pat list"
  | PatConstr name "pat args"
  | PatDict "(string \<times> pat) list"
  | PatAs pat var

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
    ExprVar var
  | ExprLiteral lit
  | ExprCall expr "expr args"
  | ExprDict "(expr \<times> expr) list"
  | ExprAttribute expr var
  | ExprSubscript expr expr
  | ExprBinOp bop expr expr
  | ExprUnOp uop expr
  | ExprAnd expr expr
  | ExprOr expr expr
  | ExprCond expr expr expr
  | ExprList "expr list"
  | ExprTuple "expr list"
  | ExprListComp expr "qualifier list"
  | ExprDictComp expr expr "qualifier list"
  | ExprLambda "var list" expr
and qualifier =
    Guard expr
  | Generator var expr

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
    StmtPass
  | StmtSeq stmt stmt
  | StmtDeclare var ty_expr
  | StmtAssign var "ty_expr option" expr
  | StmtExpr expr
  | StmtAssert expr
  | StmtAssertMsg expr expr
  | StmtReturnNone
  | StmtReturn expr
  | StmtIf expr stmt "(expr \<times> stmt) list" "stmt option"
  | StmtMatch expr "(pat \<times> stmt) list"
  | StmtMutualRegion "func list"
and func = Def var "var list" "(var \<times> ty_expr) list" ty_expr stmt

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
