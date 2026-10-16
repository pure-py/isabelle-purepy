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
    PatLiteral lit                 \<comment> \<open>\<^verbatim>\<open>10\<close>\<close>
  | PatVar var                     \<comment> \<open>\<^verbatim>\<open>x\<close>\<close>
  | PatWildcard                    \<comment> \<open>\<^verbatim>\<open>_\<close>\<close>
  | PatList "pat list"             \<comment> \<open>\<^verbatim>\<open>[p, q]\<close>\<close>
  | PatTuple "pat list"            \<comment> \<open>\<^verbatim>\<open>(p, q)\<close>\<close>
  | PatConstr name "pat args"      \<comment> \<open>\<^verbatim>\<open>C(p, x=q)\<close>\<close>
  | PatDict "(string \<times> pat) list"  \<comment> \<open>\<^verbatim>\<open>{"a": p}\<close>\<close>
  | PatAs pat var                  \<comment> \<open>\<^verbatim>\<open>p as x\<close>\<close>

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
    ExprVar var                                  \<comment> \<open>\<^verbatim>\<open>x\<close>\<close>
  | ExprLiteral lit                              \<comment> \<open>\<^verbatim>\<open>10\<close>\<close>
  | ExprCall expr "expr args"                    \<comment> \<open>\<^verbatim>\<open>f(1, 2, x=10)\<close>\<close>
  | ExprDict "(expr \<times> expr) list"                \<comment> \<open>\<^verbatim>\<open>{"a": 1, "b": 2}\<close>\<close>
  | ExprAttribute expr var                       \<comment> \<open>\<^verbatim>\<open>c.x\<close>\<close>
  | ExprSubscript expr expr                      \<comment> \<open>\<^verbatim>\<open>c["a"]\<close>\<close>
  | ExprBinOp bop expr expr                      \<comment> \<open>\<^verbatim>\<open>x + y\<close>\<close>
  | ExprUnOp uop expr                            \<comment> \<open>\<^verbatim>\<open>not x\<close>\<close>
  | ExprAnd expr expr                            \<comment> \<open>\<^verbatim>\<open>x and y\<close>\<close>
  | ExprOr expr expr                             \<comment> \<open>\<^verbatim>\<open>x or y\<close>\<close>
  | ExprCond expr expr expr                      \<comment> \<open>\<^verbatim>\<open>10 if b else 20\<close>\<close>
  | ExprList "expr list"                         \<comment> \<open>\<^verbatim>\<open>[10, 20, 40]\<close>\<close>
  | ExprTuple "expr list"                        \<comment> \<open>\<^verbatim>\<open>(10, 20, True)\<close>\<close>
  | ExprListComp expr "qualifier list"           \<comment> \<open>\<^verbatim>\<open>[2 * x for x in xs]\<close>\<close>
  | ExprDictComp expr expr "qualifier list"      \<comment> \<open>\<^verbatim>\<open>{x: x ** 2 for x in xs}\<close>\<close>
  | ExprLambda "var list" expr                   \<comment> \<open>\<^verbatim>\<open>lambda x: x * 2\<close>\<close>
and qualifier =
    Guard expr                                   \<comment> \<open>\<^verbatim>\<open>if x > 0\<close>\<close>
  | Generator var expr                           \<comment> \<open>\<^verbatim>\<open>for x in xs\<close>\<close>

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
    StmtPass                                             \<comment> \<open>\<^verbatim>\<open>pass\<close>\<close>
  | StmtSeq stmt stmt                                    \<comment> \<open>\<^verbatim>\<open>s; t\<close>\<close>
  | StmtDeclare var ty_expr                              \<comment> \<open>\<^verbatim>\<open>x: int\<close>\<close>
  | StmtAssign var "ty_expr option" expr                 \<comment> \<open>\<^verbatim>\<open>x: int = e\<close>\<close>
  | StmtExpr expr                                        \<comment> \<open>\<^verbatim>\<open>f(x)\<close>\<close>
  | StmtAssert expr                                      \<comment> \<open>\<^verbatim>\<open>assert e\<close>\<close>
  | StmtAssertMsg expr expr                              \<comment> \<open>\<^verbatim>\<open>assert e, "msg"\<close>\<close>
  | StmtReturnNone                                       \<comment> \<open>\<^verbatim>\<open>return\<close>\<close>
  | StmtReturn expr                                      \<comment> \<open>\<^verbatim>\<open>return e\<close>\<close>
  | StmtIf expr stmt "(expr \<times> stmt) list" "stmt option"  \<comment> \<open>\<^verbatim>\<open>if e: s else: t\<close>\<close>
  | StmtMatch expr "(pat \<times> stmt) list"                   \<comment> \<open>\<^verbatim>\<open>match e: case p: s\<close>\<close>
  | StmtMutualRegion "func list"                         \<comment> \<open>\<^verbatim>\<open>def f(): s\<close>\<close>
and func = Def var "(var \<times> ty_expr) list" ty_expr stmt
  \<comment> \<open>\<^verbatim>\<open>def f(x: T) -> U: s\<close>\<close>

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
