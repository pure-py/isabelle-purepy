(* Abstract syntax and its analyses *)
theory Syntax
  imports Complex_Main Util Floats Strings
begin

type_synonym name = "var nonempty"

type_synonym pos = "nat \<times> nat"

(* Syntax node with its position in the source, as line and column *)
datatype 'a located = At (pos_of: pos) (node: 'a)

lemma size_located_node [simp]: "size_located f e = Suc (f (node e))"
  by (cases e) simp

lemma size_located_measure [measure_function]: "is_measure f \<Longrightarrow> is_measure (size_located f)"
  by (rule is_measure_trivial)

(* Termination through lists of located nodes and of pairs with a located node, in the normal form of size *)
lemma size_node_elem: "x \<in> set xs \<Longrightarrow> size (node x) < size_list (\<lambda>x. Suc (size (node x))) xs"
  by (induction xs) auto

lemma size_node_snd_elem:
  "(a, b) \<in> set xs \<Longrightarrow> size (node b) < size_list (\<lambda>x. Suc (Suc (size (node (snd x))))) xs"
  by (induction xs) auto

lemma size_node_snd_elem':
  "b \<in> set (map snd xs) \<Longrightarrow> size (node b) < size_list (\<lambda>x. Suc (Suc (size (node (snd x))))) xs"
  by (auto dest: size_node_snd_elem)

lemma size_node_pair_fst_elem:
  "(a, b) \<in> set xs
   \<Longrightarrow> size (node a) < size_list (\<lambda>x. Suc (Suc (Suc (size (node (fst x)) + size (node (snd x)))))) xs"
  by (induction xs) auto

lemma size_node_pair_snd_elem:
  "(a, b) \<in> set xs
   \<Longrightarrow> size (node b) < size_list (\<lambda>x. Suc (Suc (Suc (size (node (fst x)) + size (node (snd x)))))) xs"
  by (induction xs) auto

lemma size_list_node_fst:
  "size_list ((\<lambda>e. Suc (size (node e))) \<circ> fst) kvs
   \<le> size_list (\<lambda>x. Suc (Suc (Suc (size (node (fst x)) + size (node (snd x)))))) kvs"
  by (rule size_list_pointwise) simp

lemma size_list_node_snd:
  "size_list ((\<lambda>e. Suc (size (node e))) \<circ> snd) kvs
   \<le> size_list (\<lambda>x. Suc (Suc (Suc (size (node (fst x)) + size (node (snd x)))))) kvs"
  by (rule size_list_pointwise) simp

definition no_position :: pos where "no_position = (0, 0)"

datatype lit =
    LitInt int
  | LitFloat float
  | LitString str
  | LitBool bool
  | LitNone

type_synonym 'u args = "'u list \<times> (var \<times> 'u) list"

datatype pat =
    PatLiteral lit
  | PatVar var
  | PatWildcard
  | PatList "pat located list"
  | PatTuple "pat located list"
  | PatConstr name "pat located args"
  | PatDict "(str \<times> pat located) list"
  | PatAs "pat located" var

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
  | ExprCall "expr located" "expr located args"
  | ExprDict "(expr located \<times> expr located) list"
  | ExprAttribute "expr located" var
  | ExprSubscript "expr located" "expr located"
  | ExprBinOp bop "expr located" "expr located"
  | ExprUnOp uop "expr located"
  | ExprAnd "expr located" "expr located"
  | ExprOr "expr located" "expr located"
  | ExprCond "expr located" "expr located" "expr located"
  | ExprList "expr located list"
  | ExprTuple "expr located list"
  | ExprListComp "expr located" "qualifier list"
  | ExprDictComp "expr located" "expr located" "qualifier list"
  | ExprLambda "var list" "expr located"
and qualifier =
    Guard "expr located"
  | Generator var "expr located"

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
  | TyExprList "ty_expr located"
  | TyExprTuple "ty_expr located list"
  | TyExprDict "ty_expr located"
  | TyExprCallable "ty_expr located list" "ty_expr located"
  | TyExprLiteral lit
  | TyExprName name "ty_expr located list"
  | TyExprUnion "ty_expr located" "ty_expr located"

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

datatype sequence_kind = TupleKind | ListKind | RangeKind

datatype ty_scheme = TyScheme "var list" ty

datatype field_scheme = FieldScheme "var list" "(var \<times> ty) list"

datatype import =
    Import name
  | FromImport name "var list"

(* Two spec forms differing only in an omitted component share a constructor, with an option for the
   component. A dataclass always has a field list; an empty field list is written `pass` *)
datatype stmt =
    StmtPass
  | StmtSeq "stmt located" "stmt located"
  | StmtDeclare var "ty_expr located"
  | StmtAssign var "ty_expr located option" "expr located"
  | StmtExpr "expr located"
  | StmtAssert "expr located" "expr located option"
  | StmtReturn "expr located option"
  | StmtIf "expr located" "stmt located" "(expr located \<times> stmt located) list" "stmt located option"
  | StmtMatch "expr located" "(pat located \<times> stmt located) list"
  | StmtMutualRegion "func located list"
and func = Def var "var list" "(var \<times> ty_expr located) list" "ty_expr located" "stmt located"

type_synonym fields = "(var \<times> ty_expr located) list"

datatype type_def =
    Dataclass var "var list" "(name \<times> ty_expr located list) option" fields
  | TypeStmt var "var list" "ty_expr located"

datatype top_stmt =
    Stmt "stmt located"
  | TopSeq top_stmt top_stmt
  | TypeDefs "type_def located list"

datatype module_body = ModuleBody "import located list" top_stmt

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

definition builtins :: name where "builtins = (var ''builtins'', [])"
definition main :: name where "main = (var ''__main__'', [])"

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
"binds_pat (PatAs p x) = binds_pat (node p) \<union> {x}" |
"binds_pat (PatList ps) = \<Union> (set (map (binds_pat \<circ> node) ps))" |
"binds_pat (PatTuple ps) = \<Union> (set (map (binds_pat \<circ> node) ps))" |
"binds_pat (PatConstr q (ps, kps)) =
  \<Union> (set (map (binds_pat \<circ> node) ps)) \<union> \<Union> (set (map (binds_pat \<circ> node \<circ> snd) kps))" |
"binds_pat (PatDict kps) = \<Union> (set (map (binds_pat \<circ> node \<circ> snd) kps))" |
"binds_pat _ = {}"

fun binds_stmt :: "stmt \<Rightarrow> var set"
where
"binds_stmt (StmtSeq s s') = binds_stmt (node s) \<union> binds_stmt (node s')" |
"binds_stmt (StmtIf _ s elifs else') =
  binds_stmt (node s) \<union> \<Union> (set (map (\<lambda>(_, s'). binds_stmt (node s')) elifs))
  \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> binds_stmt (node s'))" |
"binds_stmt (StmtMatch _ cases) =
  \<Union> (set (map (\<lambda>(p, s). binds_pat (node p) \<union> binds_stmt (node s)) cases))" |
"binds_stmt _ = {}"

fun binds_quals :: "qualifier list \<Rightarrow> var set"
where
"binds_quals [] = {}" |
"binds_quals (Guard _ # gs) = binds_quals gs" |
"binds_quals (Generator x _ # gs) = {x} \<union> binds_quals gs"

fun binds_top :: "top_stmt \<Rightarrow> var set"
where
"binds_top (Stmt s) = binds_stmt (node s)" |
"binds_top (TopSeq t t') = binds_top t \<union> binds_top t'" |
"binds_top (TypeDefs \<chi>s) = {}"

fun assigns_stmt :: "stmt \<Rightarrow> var set"
where
"assigns_stmt (StmtDeclare x _) = {x}" |
"assigns_stmt (StmtAssign x _ _) = {x}" |
"assigns_stmt (StmtSeq s s') = assigns_stmt (node s) \<union> assigns_stmt (node s')" |
"assigns_stmt (StmtMutualRegion ds) = set (map (def_name \<circ> node) ds)" |
"assigns_stmt (StmtIf _ s elifs else') =
  assigns_stmt (node s) \<union> \<Union> (set (map (\<lambda>(_, s'). assigns_stmt (node s')) elifs))
  \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> assigns_stmt (node s'))" |
"assigns_stmt (StmtMatch _ cases) =
  \<Union> (set (map (\<lambda>(p, s). binds_pat (node p) \<union> assigns_stmt (node s)) cases))" |
"assigns_stmt _ = {}"

fun assigns_top :: "top_stmt \<Rightarrow> var set"
where
"assigns_top (Stmt s) = assigns_stmt (node s)" |
"assigns_top (TopSeq t t') = assigns_top t \<union> assigns_top t'" |
"assigns_top (TypeDefs \<chi>s) = set (map (type_def_name \<circ> node) \<chi>s)"

fun declares_stmt :: "stmt \<Rightarrow> var list"
where
"declares_stmt (StmtDeclare x _) = [x]" |
"declares_stmt (StmtAssign x (Some _) _) = [x]" |
"declares_stmt (StmtSeq s s') = declares_stmt (node s) @ declares_stmt (node s')" |
"declares_stmt (StmtMutualRegion ds) = map (def_name \<circ> node) ds" |
"declares_stmt (StmtIf _ s elifs else') =
  declares_stmt (node s) @ concat (map (\<lambda>(_, s'). declares_stmt (node s')) elifs)
  @ (case else' of None \<Rightarrow> [] | Some s' \<Rightarrow> declares_stmt (node s'))" |
"declares_stmt (StmtMatch _ cases) = concat (map (\<lambda>(_, s). declares_stmt (node s)) cases)" |
"declares_stmt _ = []"

fun declares_imports :: "import located list \<Rightarrow> var list"
where
"declares_imports [] = []" |
"declares_imports (At _ (Import (x, xs)) # \<iota>s) =
  (if list_ex (\<lambda>\<iota>. case node \<iota> of Import (x', _) \<Rightarrow> x' = x | _ \<Rightarrow> False) \<iota>s then declares_imports \<iota>s
   else x # declares_imports \<iota>s)" |
"declares_imports (At _ (FromImport q xs) # \<iota>s) = xs @ declares_imports \<iota>s"

fun declares_top :: "top_stmt \<Rightarrow> var list"
where
"declares_top (Stmt s) = declares_stmt (node s)" |
"declares_top (TopSeq t t') = declares_top t @ declares_top t'" |
"declares_top (TypeDefs \<chi>s) = map (type_def_name \<circ> node) \<chi>s"

fun fv_expr :: "expr \<Rightarrow> var set" and fv_quals :: "qualifier list \<Rightarrow> var set"
where
"fv_expr (ExprVar x) = {x}" |
"fv_expr (ExprLiteral _) = {}" |
"fv_expr (ExprCall e (es, kws)) =
  fv_expr (node e) \<union> \<Union> (set (map (fv_expr \<circ> node) es)) \<union> \<Union> (set (map (fv_expr \<circ> node \<circ> snd) kws))" |
"fv_expr (ExprDict kvs) =
  \<Union> (set (map (fv_expr \<circ> node \<circ> fst) kvs)) \<union> \<Union> (set (map (fv_expr \<circ> node \<circ> snd) kvs))" |
"fv_expr (ExprAttribute e _) = fv_expr (node e)" |
"fv_expr (ExprSubscript e e') = fv_expr (node e) \<union> fv_expr (node e')" |
"fv_expr (ExprBinOp _ e e') = fv_expr (node e) \<union> fv_expr (node e')" |
"fv_expr (ExprUnOp _ e) = fv_expr (node e)" |
"fv_expr (ExprAnd e e') = fv_expr (node e) \<union> fv_expr (node e')" |
"fv_expr (ExprOr e e') = fv_expr (node e) \<union> fv_expr (node e')" |
"fv_expr (ExprCond e\<^sub>1 e e\<^sub>2) = fv_expr (node e\<^sub>1) \<union> fv_expr (node e) \<union> fv_expr (node e\<^sub>2)" |
"fv_expr (ExprList es) = \<Union> (set (map (fv_expr \<circ> node) es))" |
"fv_expr (ExprTuple es) = \<Union> (set (map (fv_expr \<circ> node) es))" |
"fv_expr (ExprListComp e gs) = fv_quals gs \<union> (fv_expr (node e) - binds_quals gs)" |
"fv_expr (ExprDictComp e e' gs) = fv_quals gs \<union> ((fv_expr (node e) \<union> fv_expr (node e')) - binds_quals gs)" |
"fv_expr (ExprLambda xs e) = fv_expr (node e) - set xs" |

"fv_quals [] = {}" |
"fv_quals (Guard e # gs) = fv_expr (node e) \<union> fv_quals gs" |
"fv_quals (Generator x e # gs) = fv_expr (node e) \<union> (fv_quals gs - {x})"

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

fun subterms :: "ty \<Rightarrow> ty list"
where
"subterms (TyUnion \<sigma> \<tau>) = subterms \<sigma> @ subterms \<tau>" |
"subterms (TyList \<tau>) = TyList \<tau> # subterms \<tau>" |
"subterms (TyDict \<tau>) = TyDict \<tau> # subterms \<tau>" |
"subterms (TyTuple \<tau>s) = TyTuple \<tau>s # concat (map subterms \<tau>s)" |
"subterms (TyCallable \<tau>s \<tau>) = TyCallable \<tau>s \<tau> # concat (map subterms \<tau>s) @ subterms \<tau>" |
"subterms (TyClass C \<tau>s) = TyClass C \<tau>s # concat (map subterms \<tau>s)" |
"subterms \<tau> = [\<tau>]"

fun captures_expr :: "expr \<Rightarrow> var set" and captures_quals :: "qualifier list \<Rightarrow> var set"
where
"captures_expr (ExprVar _) = {}" |
"captures_expr (ExprLiteral _) = {}" |
"captures_expr (ExprCall e (es, kws)) =
  captures_expr (node e) \<union> \<Union> (set (map (captures_expr \<circ> node) es))
  \<union> \<Union> (set (map (captures_expr \<circ> node \<circ> snd) kws))" |
"captures_expr (ExprDict kvs) =
  \<Union> (set (map (captures_expr \<circ> node \<circ> fst) kvs)) \<union> \<Union> (set (map (captures_expr \<circ> node \<circ> snd) kvs))" |
"captures_expr (ExprAttribute e _) = captures_expr (node e)" |
"captures_expr (ExprSubscript e e') = captures_expr (node e) \<union> captures_expr (node e')" |
"captures_expr (ExprBinOp _ e e') = captures_expr (node e) \<union> captures_expr (node e')" |
"captures_expr (ExprUnOp _ e) = captures_expr (node e)" |
"captures_expr (ExprAnd e e') = captures_expr (node e) \<union> captures_expr (node e')" |
"captures_expr (ExprOr e e') = captures_expr (node e) \<union> captures_expr (node e')" |
"captures_expr (ExprCond e\<^sub>1 e e\<^sub>2) =
  captures_expr (node e\<^sub>1) \<union> captures_expr (node e) \<union> captures_expr (node e\<^sub>2)" |
"captures_expr (ExprList es) = \<Union> (set (map (captures_expr \<circ> node) es))" |
"captures_expr (ExprTuple es) = \<Union> (set (map (captures_expr \<circ> node) es))" |
"captures_expr (ExprListComp e gs) = captures_quals gs \<union> (captures_expr (node e) - binds_quals gs)" |
"captures_expr (ExprDictComp e e' gs) =
  captures_quals gs \<union> ((captures_expr (node e) \<union> captures_expr (node e')) - binds_quals gs)" |
"captures_expr (ExprLambda xs e) = fv_expr (node e) - set xs" |

"captures_quals [] = {}" |
"captures_quals (Guard e # gs) = captures_expr (node e) \<union> captures_quals gs" |
"captures_quals (Generator x e # gs) = captures_expr (node e) \<union> (captures_quals gs - {x})"

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
"prim_name object = var ''object''" |
"prim_name Never = var ''Never''" |
"prim_name NoneType = var ''None''" |
"prim_name bool = var ''bool''" |
"prim_name int = var ''int''" |
"prim_name float = var ''float''" |
"prim_name str = var ''str''" |
"prim_name Sized = var ''Sized''"

fun numeric_literal :: "expr \<Rightarrow> bool"
where
"numeric_literal (ExprLiteral (LitInt _)) = True" |
"numeric_literal (ExprLiteral (LitFloat _)) = True" |
"numeric_literal _ = False"

fun short_name :: "name \<Rightarrow> var"
where
"short_name (x, xs) = (if xs = [] then x else last xs)"

fun lambda_of :: "expr \<Rightarrow> (var list \<times> expr located) option"
where
"lambda_of (ExprLambda xs e) = Some (xs, e)" |
"lambda_of _ = None"

lemma lambda_of_size: "lambda_of e = Some (xs, e') \<Longrightarrow> size (node e') < size e"
  by (cases e) auto

fun dotted_name :: "expr \<Rightarrow> name option"
where
"dotted_name (ExprVar x) = Some (x, [])" |
"dotted_name (ExprAttribute e x) = map_option (\<lambda>q. snoc q x) (dotted_name (node e))" |
"dotted_name _ = None"

(* Targets of plain assignments, in order *)
fun assign_targets_stmt :: "stmt \<Rightarrow> var list"
where
"assign_targets_stmt (StmtAssign x None _) = [x]" |
"assign_targets_stmt (StmtSeq s s') = assign_targets_stmt (node s) @ assign_targets_stmt (node s')" |
"assign_targets_stmt (StmtIf _ s elifs else') =
  assign_targets_stmt (node s) @ concat (map (\<lambda>(_, s'). assign_targets_stmt (node s')) elifs)
  @ (case else' of None \<Rightarrow> [] | Some s' \<Rightarrow> assign_targets_stmt (node s'))" |
"assign_targets_stmt (StmtMatch _ cases) = concat (map (\<lambda>(_, s). assign_targets_stmt (node s)) cases)" |
"assign_targets_stmt _ = []"

fun assign_targets_top :: "top_stmt \<Rightarrow> var list"
where
"assign_targets_top (Stmt s) = assign_targets_stmt (node s)" |
"assign_targets_top (TopSeq t t') = assign_targets_top t @ assign_targets_top t'" |
"assign_targets_top (TypeDefs _) = []"

definition prim_of_name :: "var \<Rightarrow> prim_ty option"
where
"prim_of_name x = find (\<lambda>\<nu>. prim_name \<nu> = x) [object, Never, NoneType, bool, int, float, str, Sized]"

(* Arguments of a subscript *)
fun subscript_args :: "expr located \<Rightarrow> expr located list"
where
"subscript_args (At _ (ExprTuple es)) = es" |
"subscript_args e = [e]"

(* Type expression denoted by an expression, at the same positions *)
fun type_expr_of :: "expr located \<Rightarrow> ty_expr located option"
where
"type_expr_of (At p (ExprLiteral LitNone)) = Some (At p (TyExprPrim NoneType))" |
"type_expr_of (At p (ExprVar x)) =
  Some (At p (case prim_of_name x of Some \<nu> \<Rightarrow> TyExprPrim \<nu> | None \<Rightarrow> TyExprName (x, []) []))" |
"type_expr_of (At p (ExprAttribute e x)) =
  map_option (\<lambda>q. At p (TyExprName q [])) (dotted_name (ExprAttribute e x))" |
"type_expr_of (At p (ExprBinOp BOpBitOr e e')) = do {
   \<psi> \<leftarrow> type_expr_of e; \<psi>' \<leftarrow> type_expr_of e'; Some (At p (TyExprUnion \<psi> \<psi>'))
 }" |
"type_expr_of (At p (ExprSubscript e e')) =
  (let head = (case node e of ExprVar x \<Rightarrow> Some x | _ \<Rightarrow> None) in
   if head = Some (var ''Literal'') then
     (case node e' of
        ExprLiteral (LitFloat _) \<Rightarrow> None
      | ExprLiteral l \<Rightarrow> Some (At p (TyExprLiteral l))
      | _ \<Rightarrow> None)
   else if head = Some (var ''Callable'') then
     (case e' of
        At _ (ExprTuple [At _ (ExprList es), e'']) \<Rightarrow> do {
          \<psi>s \<leftarrow> those (map type_expr_of es); \<psi> \<leftarrow> type_expr_of e''; Some (At p (TyExprCallable \<psi>s \<psi>))
        }
      | _ \<Rightarrow> None)
   else do {
     \<psi>s \<leftarrow> those (case e' of At _ (ExprTuple es) \<Rightarrow> map type_expr_of es | _ \<Rightarrow> [type_expr_of e']);
     if head = Some (var ''list'') then (case \<psi>s of [\<psi>] \<Rightarrow> Some (At p (TyExprList \<psi>)) | _ \<Rightarrow> None)
     else if head = Some (var ''tuple'') then Some (At p (TyExprTuple \<psi>s))
     else if head = Some (var ''dict'')
     then (case \<psi>s of [At _ (TyExprPrim str), \<psi>] \<Rightarrow> Some (At p (TyExprDict \<psi>)) | _ \<Rightarrow> None)
     else map_option (\<lambda>q. At p (TyExprName q \<psi>s)) (dotted_name (node e))
   })" |
"type_expr_of _ = None"

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
