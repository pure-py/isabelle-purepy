theory Syntax
  imports Complex_Main Util
begin

type_alias var = string

type_synonym name = "var nonempty"

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
    object
  | Never
  | NoneType
  | bool
  | int
  | float
  | str
  | Sized

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

datatype ty_scheme = TyScheme "var list" ty

datatype field_scheme = FieldScheme "var list" "(var \<times> ty) list"

datatype import =
    Import name
  | FromImport name "var list"

(* Two spec forms differing only in an omitted component share a constructor, with an option for the
   component. A dataclass always has a field list; an empty field list is written `pass` *)
datatype stmt =
    StmtPass
  | StmtSeq stmt stmt
  | StmtDeclare var ty_expr
  | StmtAssign var "ty_expr option" expr
  | StmtExpr expr
  | StmtAssert expr "expr option"
  | StmtReturn "expr option"
  | StmtIf expr stmt "(expr \<times> stmt) list" "stmt option"
  | StmtMatch expr "(pat \<times> stmt) list"
  | StmtMutualRegion "func list"
and func = Def var "var list" "(var \<times> ty_expr) list" ty_expr stmt

type_synonym fields = "(var \<times> ty_expr) list"

datatype type_def =
    Dataclass var "var list" "(name \<times> ty_expr list) option" fields
  | TypeStmt var "var list" ty_expr

datatype top_stmt =
    Stmt stmt
  | TopSeq top_stmt top_stmt
  | TypeDefs "type_def list"

datatype module_body = ModuleBody "import list" top_stmt

fun prefix_of :: "name \<Rightarrow> name \<Rightarrow> bool" (infix "\<preceq>" 50)
where
"(y, ys) \<preceq> (y', ys') = (y = y' \<and> take (length ys) ys' = ys)"

definition proper_prefix_of :: "name \<Rightarrow> name \<Rightarrow> bool" (infix "\<prec>" 50)
where
"q \<prec> q' = (q \<preceq> q' \<and> q \<noteq> q')"

(* Shortest first *)
fun proper_prefixes :: "name \<Rightarrow> name list"
where
"proper_prefixes (y, ys) = map (\<lambda>i. (y, take i ys)) [0..<length ys]"

definition unique_to :: "name \<Rightarrow> name \<Rightarrow> name list"
where
"unique_to q' q = filter (\<lambda>p. \<not> p \<preceq> q) (proper_prefixes q')"

definition builtins :: name where "builtins = (''builtins'', [])"
definition main :: name where "main = (''__main__'', [])"

fun def_name :: "func \<Rightarrow> var"
where
"def_name (Def f _ _ _ _) = f"

fun type_def_name :: "type_def \<Rightarrow> var"
where
"type_def_name (Dataclass c _ _ _) = c" |
"type_def_name (TypeStmt x _ _) = x"

fun binds_pat :: "pat \<Rightarrow> var set"
where
"binds_pat (PatVar x) = {x}" |
"binds_pat (PatAs p x) = binds_pat p \<union> {x}" |
"binds_pat (PatList ps) = \<Union> (set (map binds_pat ps))" |
"binds_pat (PatTuple ps) = \<Union> (set (map binds_pat ps))" |
"binds_pat (PatConstr q (ps, kps)) = \<Union> (set (map binds_pat ps)) \<union> \<Union> (set (map (binds_pat \<circ> snd) kps))" |
"binds_pat (PatDict kps) = \<Union> (set (map (binds_pat \<circ> snd) kps))" |
"binds_pat _ = {}"

fun binds_stmt :: "stmt \<Rightarrow> var set"
where
"binds_stmt (StmtSeq s s') = binds_stmt s \<union> binds_stmt s'" |
"binds_stmt (StmtIf _ s elifs else') =
  binds_stmt s \<union> \<Union> (set (map (\<lambda>(_, s'). binds_stmt s') elifs))
  \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> binds_stmt s')" |
"binds_stmt (StmtMatch _ cases) = \<Union> (set (map (\<lambda>(p, s). binds_pat p \<union> binds_stmt s) cases))" |
"binds_stmt _ = {}"

fun binds_quals :: "qualifier list \<Rightarrow> var set"
where
"binds_quals [] = {}" |
"binds_quals (Guard _ # gs) = binds_quals gs" |
"binds_quals (Generator x _ # gs) = {x} \<union> binds_quals gs"

fun binds_top :: "top_stmt \<Rightarrow> var set"
where
"binds_top (Stmt s) = binds_stmt s" |
"binds_top (TopSeq t t') = binds_top t \<union> binds_top t'" |
"binds_top (TypeDefs \<chi>s) = {}"

fun assigns_stmt :: "stmt \<Rightarrow> var set"
where
"assigns_stmt (StmtDeclare x _) = {x}" |
"assigns_stmt (StmtAssign x _ _) = {x}" |
"assigns_stmt (StmtSeq s s') = assigns_stmt s \<union> assigns_stmt s'" |
"assigns_stmt (StmtMutualRegion ds) = set (map def_name ds)" |
"assigns_stmt (StmtIf _ s elifs else') =
  assigns_stmt s \<union> \<Union> (set (map (\<lambda>(_, s'). assigns_stmt s') elifs))
  \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> assigns_stmt s')" |
"assigns_stmt (StmtMatch _ cases) = \<Union> (set (map (\<lambda>(p, s). binds_pat p \<union> assigns_stmt s) cases))" |
"assigns_stmt _ = {}"

fun assigns_top :: "top_stmt \<Rightarrow> var set"
where
"assigns_top (Stmt s) = assigns_stmt s" |
"assigns_top (TopSeq t t') = assigns_top t \<union> assigns_top t'" |
"assigns_top (TypeDefs \<chi>s) = set (map type_def_name \<chi>s)"

fun declares_stmt :: "stmt \<Rightarrow> var list"
where
"declares_stmt (StmtDeclare x _) = [x]" |
"declares_stmt (StmtAssign x (Some _) _) = [x]" |
"declares_stmt (StmtSeq s s') = declares_stmt s @ declares_stmt s'" |
"declares_stmt (StmtMutualRegion ds) = map def_name ds" |
"declares_stmt (StmtIf _ s elifs else') =
  declares_stmt s @ concat (map (\<lambda>(_, s'). declares_stmt s') elifs)
  @ (case else' of None \<Rightarrow> [] | Some s' \<Rightarrow> declares_stmt s')" |
"declares_stmt (StmtMatch _ cases) = concat (map (\<lambda>(_, s). declares_stmt s) cases)" |
"declares_stmt _ = []"

fun declares_imports :: "import list \<Rightarrow> var list"
where
"declares_imports [] = []" |
"declares_imports (Import (x, xs) # \<iota>s) =
  (if list_ex (\<lambda>\<iota>. case \<iota> of Import (x', _) \<Rightarrow> x' = x | _ \<Rightarrow> False) \<iota>s then declares_imports \<iota>s
   else x # declares_imports \<iota>s)" |
"declares_imports (FromImport q xs # \<iota>s) = xs @ declares_imports \<iota>s"

fun declares_top :: "top_stmt \<Rightarrow> var list"
where
"declares_top (Stmt s) = declares_stmt s" |
"declares_top (TopSeq t t') = declares_top t @ declares_top t'" |
"declares_top (TypeDefs \<chi>s) = map type_def_name \<chi>s"

fun fv_expr :: "expr \<Rightarrow> var set" and fv_quals :: "qualifier list \<Rightarrow> var set"
where
"fv_expr (ExprVar x) = {x}" |
"fv_expr (ExprLiteral _) = {}" |
"fv_expr (ExprCall e (es, kws)) = fv_expr e \<union> \<Union> (set (map fv_expr es)) \<union> \<Union> (set (map (fv_expr \<circ> snd) kws))" |
"fv_expr (ExprDict kvs) = \<Union> (set (map (fv_expr \<circ> fst) kvs)) \<union> \<Union> (set (map (fv_expr \<circ> snd) kvs))" |
"fv_expr (ExprAttribute e _) = fv_expr e" |
"fv_expr (ExprSubscript e e') = fv_expr e \<union> fv_expr e'" |
"fv_expr (ExprBinOp _ e e') = fv_expr e \<union> fv_expr e'" |
"fv_expr (ExprUnOp _ e) = fv_expr e" |
"fv_expr (ExprAnd e e') = fv_expr e \<union> fv_expr e'" |
"fv_expr (ExprOr e e') = fv_expr e \<union> fv_expr e'" |
"fv_expr (ExprCond e\<^sub>1 e e\<^sub>2) = fv_expr e\<^sub>1 \<union> fv_expr e \<union> fv_expr e\<^sub>2" |
"fv_expr (ExprList es) = \<Union> (set (map fv_expr es))" |
"fv_expr (ExprTuple es) = \<Union> (set (map fv_expr es))" |
"fv_expr (ExprListComp e gs) = fv_quals gs \<union> (fv_expr e - binds_quals gs)" |
"fv_expr (ExprDictComp e e' gs) = fv_quals gs \<union> ((fv_expr e \<union> fv_expr e') - binds_quals gs)" |
"fv_expr (ExprLambda xs e) = fv_expr e - set xs" |

"fv_quals [] = {}" |
"fv_quals (Guard e # gs) = fv_expr e \<union> fv_quals gs" |
"fv_quals (Generator x e # gs) = fv_expr e \<union> (fv_quals gs - {x})"

fun captures_expr :: "expr \<Rightarrow> var set" and captures_quals :: "qualifier list \<Rightarrow> var set"
where
"captures_expr (ExprVar _) = {}" |
"captures_expr (ExprLiteral _) = {}" |
"captures_expr (ExprCall e (es, kws)) =
  captures_expr e \<union> \<Union> (set (map captures_expr es)) \<union> \<Union> (set (map (captures_expr \<circ> snd) kws))" |
"captures_expr (ExprDict kvs) =
  \<Union> (set (map (captures_expr \<circ> fst) kvs)) \<union> \<Union> (set (map (captures_expr \<circ> snd) kvs))" |
"captures_expr (ExprAttribute e _) = captures_expr e" |
"captures_expr (ExprSubscript e e') = captures_expr e \<union> captures_expr e'" |
"captures_expr (ExprBinOp _ e e') = captures_expr e \<union> captures_expr e'" |
"captures_expr (ExprUnOp _ e) = captures_expr e" |
"captures_expr (ExprAnd e e') = captures_expr e \<union> captures_expr e'" |
"captures_expr (ExprOr e e') = captures_expr e \<union> captures_expr e'" |
"captures_expr (ExprCond e\<^sub>1 e e\<^sub>2) = captures_expr e\<^sub>1 \<union> captures_expr e \<union> captures_expr e\<^sub>2" |
"captures_expr (ExprList es) = \<Union> (set (map captures_expr es))" |
"captures_expr (ExprTuple es) = \<Union> (set (map captures_expr es))" |
"captures_expr (ExprListComp e gs) = captures_quals gs \<union> (captures_expr e - binds_quals gs)" |
"captures_expr (ExprDictComp e e' gs) =
  captures_quals gs \<union> ((captures_expr e \<union> captures_expr e') - binds_quals gs)" |
"captures_expr (ExprLambda xs e) = fv_expr e - set xs" |

"captures_quals [] = {}" |
"captures_quals (Guard e # gs) = captures_expr e \<union> captures_quals gs" |
"captures_quals (Generator x e # gs) = captures_expr e \<union> (captures_quals gs - {x})"

(* u marks a variable unbound: the value or the context entry *)
definition scope_stmt :: "'a \<Rightarrow> var list \<Rightarrow> stmt \<Rightarrow> (var, 'a) fmap option"
where
"scope_stmt u ys s =
  (if distinct ys \<and> distinct (declares_stmt s) \<and> set ys \<inter> set (declares_stmt s) = {}
      \<and> set ys \<inter> binds_stmt s = {} \<and> set (declares_stmt s) \<inter> binds_stmt s = {}
   then Some (fmconst (assigns_stmt s - set ys) u)
   else None)"

definition scope_top :: "'a \<Rightarrow> var list \<Rightarrow> top_stmt \<Rightarrow> (var, 'a) fmap option"
where
"scope_top u ys t =
  (if distinct ys \<and> distinct (declares_top t) \<and> set ys \<inter> set (declares_top t) = {} \<and> set ys \<inter> binds_top t = {}
      \<and> set (declares_top t) \<inter> binds_top t = {}
   then Some (fmconst (assigns_top t - set ys) u)
   else None)"

fun prim_name :: "prim_ty \<Rightarrow> var"
where
"prim_name object = ''object''" |
"prim_name Never = ''Never''" |
"prim_name NoneType = ''None''" |
"prim_name bool = ''bool''" |
"prim_name int = ''int''" |
"prim_name float = ''float''" |
"prim_name str = ''str''" |
"prim_name Sized = ''Sized''"

fun numeric_literal :: "expr \<Rightarrow> bool"
where
"numeric_literal (ExprLiteral (LitInt _)) = True" |
"numeric_literal (ExprLiteral (LitFloat _)) = True" |
"numeric_literal _ = False"

fun dotted_name :: "expr \<Rightarrow> name option"
where
"dotted_name (ExprVar x) = Some (x, [])" |
"dotted_name (ExprAttribute e x) = map_option (\<lambda>q. snoc q x) (dotted_name e)" |
"dotted_name _ = None"

(* Targets of plain assignments, in order *)
fun assign_targets_stmt :: "stmt \<Rightarrow> var list"
where
"assign_targets_stmt (StmtAssign x None _) = [x]" |
"assign_targets_stmt (StmtSeq s s') = assign_targets_stmt s @ assign_targets_stmt s'" |
"assign_targets_stmt (StmtIf _ s elifs else') =
  assign_targets_stmt s @ concat (map (\<lambda>(_, s'). assign_targets_stmt s') elifs)
  @ (case else' of None \<Rightarrow> [] | Some s' \<Rightarrow> assign_targets_stmt s')" |
"assign_targets_stmt (StmtMatch _ cases) = concat (map (\<lambda>(_, s). assign_targets_stmt s) cases)" |
"assign_targets_stmt _ = []"

fun assign_targets_top :: "top_stmt \<Rightarrow> var list"
where
"assign_targets_top (Stmt s) = assign_targets_stmt s" |
"assign_targets_top (TopSeq t t') = assign_targets_top t @ assign_targets_top t'" |
"assign_targets_top (TypeDefs _) = []"

fun fv_ty :: "ty \<Rightarrow> var set"
where
"fv_ty (TyVar \<alpha>) = {\<alpha>}" |
"fv_ty (TyList \<tau>) = fv_ty \<tau>" |
"fv_ty (TyDict \<tau>) = fv_ty \<tau>" |
"fv_ty (TyTuple \<tau>s) = \<Union> (set (map fv_ty \<tau>s))" |
"fv_ty (TyCallable \<sigma>s \<tau>) = \<Union> (set (map fv_ty \<sigma>s)) \<union> fv_ty \<tau>" |
"fv_ty (TyClass _ \<tau>s) = \<Union> (set (map fv_ty \<tau>s))" |
"fv_ty (TyUnion \<sigma> \<tau>) = fv_ty \<sigma> \<union> fv_ty \<tau>" |
"fv_ty _ = {}"

(* Whether a synthesis rule applies to the expression *)
fun synthesises :: "expr \<Rightarrow> bool"
where
"synthesises (ExprLambda _ _) = False" |
"synthesises (ExprCond e\<^sub>1 _ e\<^sub>2) = (synthesises e\<^sub>1 \<or> synthesises e\<^sub>2)" |
"synthesises (ExprList es) = list_ex synthesises es" |
"synthesises (ExprDict kvs) = list_ex (synthesises \<circ> snd) kvs" |
"synthesises (ExprTuple es) = list_all synthesises es" |
"synthesises (ExprListComp e _) = synthesises e" |
"synthesises (ExprDictComp _ e _) = synthesises e" |
"synthesises (ExprCall (ExprLambda _ e) (es, _)) = (synthesises e \<and> list_all synthesises es)" |
"synthesises _ = True"

definition prim_of_name :: "var \<Rightarrow> prim_ty option"
where
"prim_of_name x = find (\<lambda>\<nu>. prim_name \<nu> = x) [object, Never, NoneType, bool, int, float, str, Sized]"

(* Type expression denoted by an expression, as in an annotation; None if it denotes none *)
function (sequential)
  parse_annotation :: "expr \<Rightarrow> ty_expr option" and
  parse_annotations :: "expr list \<Rightarrow> ty_expr list option"
where
"parse_annotation (ExprLiteral LitNone) = Some (TyExprPrim NoneType)" |
"parse_annotation (ExprVar x) =
  Some (case prim_of_name x of Some \<nu> \<Rightarrow> TyExprPrim \<nu> | None \<Rightarrow> TyExprName (x, []) [])" |
"parse_annotation (ExprAttribute e x) = map_option (\<lambda>q. TyExprName q []) (dotted_name (ExprAttribute e x))" |
"parse_annotation (ExprBinOp BOpBitOr e e') = do {
   \<psi> \<leftarrow> parse_annotation e; \<psi>' \<leftarrow> parse_annotation e'; Some (TyExprUnion \<psi> \<psi>')
 }" |
"parse_annotation (ExprSubscript e e') =
  (let head = (case e of ExprVar x \<Rightarrow> Some x | _ \<Rightarrow> None) in
   if head = Some ''Literal'' then
     (case e' of ExprLiteral (LitFloat _) \<Rightarrow> None | ExprLiteral l \<Rightarrow> Some (TyExprLiteral l) | _ \<Rightarrow> None)
   else if head = Some ''Callable'' then
     (case e' of
        ExprTuple [ExprList es, e''] \<Rightarrow> do {
          \<psi>s \<leftarrow> parse_annotations es; \<psi> \<leftarrow> parse_annotation e''; Some (TyExprCallable \<psi>s \<psi>)
        }
      | _ \<Rightarrow> None)
   else do {
     \<psi>s \<leftarrow> (case e' of ExprTuple es \<Rightarrow> parse_annotations es | _ \<Rightarrow> parse_annotations [e']);
     if head = Some ''list'' then (case \<psi>s of [\<psi>] \<Rightarrow> Some (TyExprList \<psi>) | _ \<Rightarrow> None)
     else if head = Some ''tuple'' then Some (TyExprTuple \<psi>s)
     else if head = Some ''dict'' then (case \<psi>s of [TyExprPrim str, \<psi>] \<Rightarrow> Some (TyExprDict \<psi>) | _ \<Rightarrow> None)
     else map_option (\<lambda>q. TyExprName q \<psi>s) (dotted_name e)
   })" |
"parse_annotation _ = None" |

"parse_annotations [] = Some []" |
"parse_annotations (e # es) = do { \<psi> \<leftarrow> parse_annotation e; \<psi>s \<leftarrow> parse_annotations es; Some (\<psi> # \<psi>s) }"
by pat_completeness auto

termination
by (relation "measure (\<lambda>x. case x of Inl e \<Rightarrow> 2 * size e + 1 | Inr es \<Rightarrow> 2 * size_list size es)") auto

consts
  binds :: "'a \<Rightarrow> var set"
  assigns :: "'a \<Rightarrow> var set"
  declares :: "'a \<Rightarrow> var list"
  fv :: "'a \<Rightarrow> var set"
  captures :: "'a \<Rightarrow> var set"
  assign_targets :: "'a \<Rightarrow> var list"
  scope :: "'u \<Rightarrow> 'y \<Rightarrow> 'a \<Rightarrow> (var, 'u) fmap option"

adhoc_overloading binds \<rightleftharpoons> binds_pat binds_stmt binds_quals binds_top
adhoc_overloading assigns \<rightleftharpoons> assigns_stmt assigns_top
adhoc_overloading declares \<rightleftharpoons> declares_stmt declares_top declares_imports
adhoc_overloading fv \<rightleftharpoons> fv_expr fv_quals fv_ty
adhoc_overloading captures \<rightleftharpoons> captures_expr captures_quals
adhoc_overloading assign_targets \<rightleftharpoons> assign_targets_stmt assign_targets_top
adhoc_overloading scope \<rightleftharpoons> scope_stmt scope_top

end
