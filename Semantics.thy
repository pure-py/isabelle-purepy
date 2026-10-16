theory Semantics
    imports Syntax HOL.Map
begin

(* Free o for outcomes, as in the spec *)
no_notation (ASCII) comp (infixl \<open>o\<close> 55)

datatype val =
      VLit lit
    | VList "val list"
    | VTuple "val list"
    | VLamClosure "var \<rightharpoonup> val" "var list" expr  ("Lam'(_, _, _')")
    | VDefClosure "var \<rightharpoonup> val" "func list" nat  ("Def'(_, _, _')")
    | VUnbound

type_synonym env = "var \<rightharpoonup> val"
abbreviation \<epsilon> :: env where "\<epsilon> \<equiv> Map.empty"

datatype termination_kind =
    TypeError
  | IndexError
  | KeyError
  | ZeroDivisionError
  | AssertionError "val option"
  | AttributeError
  | SystemExit int
  | Undef

datatype 'a result = Val 'a | Aborts termination_kind

datatype outcome = Assigns env | Returns val | Aborts\<^sub>o termination_kind

consts mlet :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"

fun mlet_result :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result"
where
"mlet_result (Val v) f = f v" |
"mlet_result (Aborts \<kappa>) f = Aborts \<kappa>"

fun mlet_outcome :: "'a result \<Rightarrow> ('a \<Rightarrow> outcome) \<Rightarrow> outcome"
where
"mlet_outcome (Val v) f = f v" |
"mlet_outcome (Aborts \<kappa>) f = Aborts\<^sub>o \<kappa>"

adhoc_overloading mlet \<rightleftharpoons> mlet_result mlet_outcome

fun compose :: "outcome \<Rightarrow> outcome \<Rightarrow> outcome" (infixl "\<bullet>" 70)
where
"Assigns \<rho> \<bullet> Assigns \<rho>' = Assigns (\<rho> ++ \<rho>')" |
"Assigns \<rho> \<bullet> o = o" |
"Returns v \<bullet> o = Returns v" |
"Aborts\<^sub>o \<kappa> \<bullet> o = Aborts\<^sub>o \<kappa>"

fun call_result :: "outcome \<Rightarrow> val result"
where
"call_result (Returns v) = Val v" |
"call_result (Assigns \<rho>) = Val (VLit LitNone)" |
"call_result (Aborts\<^sub>o \<kappa>) = Aborts \<kappa>"

fun is_closure :: "val \<Rightarrow> bool"
where
"is_closure Lam(_, _, _) = True" |
"is_closure Def(_, _, _) = True" |
"is_closure _ = False"

fun eq :: "val \<Rightarrow> val \<Rightarrow> bool result" and eq_elems :: "val list \<Rightarrow> val list \<Rightarrow> bool result"
where
"eq (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (n = n')" |
"eq (VLit (LitString w)) (VLit (LitString w')) = Val (w = w')" |
"eq (VLit (LitBool b)) (VLit (LitBool b')) = Val (b = b')" |
"eq (VLit LitNone) (VLit LitNone) = Val True" |
"eq (VLit (LitBool _)) (VLit (LitNumber _)) = Aborts Undef" |
"eq (VLit (LitNumber _)) (VLit (LitBool _)) = Aborts Undef" |
"eq (VList vs) (VList vs') = eq_elems vs vs'" |
"eq (VTuple vs) (VTuple vs') = eq_elems vs vs'" |
"eq Lam(_, _, _) Lam(_, _, _) = Aborts Undef" |
"eq Lam(_, _, _) Def(_, _, _) = Aborts Undef" |
"eq Def(_, _, _) Lam(_, _, _) = Aborts Undef" |
"eq Def(_, _, _) Def(_, _, _) = Aborts Undef" |
"eq _ _ = Val False" |

"eq_elems [] [] = Val True" |
"eq_elems (v # vs) (v' # vs') =
  (if length vs \<noteq> length vs' then Val False
   else if eq v v' = Val True then eq_elems vs vs' else eq v v')" |
"eq_elems _ _ = Val False"

fun contains :: "val \<Rightarrow> val \<Rightarrow> bool result" and contains_elems :: "val list \<Rightarrow> val \<Rightarrow> bool result"
where
"contains (VList vs) v = contains_elems vs v" |
"contains (VTuple vs) v = contains_elems vs v" |
"contains (VLit (LitString w')) (VLit (LitString w)) = Val (\<exists>w1 w2. w' = w1 @ w @ w2)" |
"contains _ _ = Aborts TypeError" |

"contains_elems [] v = Val False" |
"contains_elems (v' # vs) v = (if eq v v' = Val False then contains_elems vs v else eq v v')"

fun binop_meaning :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"binop_meaning BOpEq v v' = mlet (eq v v') (\<lambda>b. Val (VLit (LitBool b)))" |
"binop_meaning BOpNeq v v' = mlet (eq v v') (\<lambda>b. Val (VLit (LitBool (\<not> b))))" |
"binop_meaning BOpIn v v' = mlet (contains v' v) (\<lambda>b. Val (VLit (LitBool b)))" |
"binop_meaning BOpNotIn v v' = mlet (contains v' v) (\<lambda>b. Val (VLit (LitBool (\<not> b))))" |
"binop_meaning BOpLt (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitBool (n < n')))" |
"binop_meaning BOpLeq (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitBool (n \<le> n')))" |
"binop_meaning BOpGt (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitBool (n > n')))" |
"binop_meaning BOpGeq (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitBool (n \<ge> n')))" |
"binop_meaning BOpAdd (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitNumber (n + n')))" |
"binop_meaning BOpSub (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitNumber (n - n')))" |
"binop_meaning BOpMul (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitNumber (n * n')))" |
"binop_meaning BOpDiv (VLit (LitNumber n)) (VLit (LitNumber n')) =
  (if n' = 0 then Aborts ZeroDivisionError else Val (VLit (LitNumber (n div n'))))" |
"binop_meaning BOpFloorDiv (VLit (LitNumber n)) (VLit (LitNumber n')) =
  (if n' = 0 then Aborts ZeroDivisionError else Val (VLit (LitNumber (n div n'))))" |
"binop_meaning BOpMod (VLit (LitNumber n)) (VLit (LitNumber n')) =
  (if n' = 0 then Aborts ZeroDivisionError else Val (VLit (LitNumber (n mod n'))))" |
"binop_meaning BOpPow (VLit (LitNumber n)) (VLit (LitNumber n')) =
  (if n' < 0 then Aborts TypeError else Val (VLit (LitNumber (n ^ nat n'))))" |
"binop_meaning _ _ _ = Aborts TypeError"

fun unop_meaning :: "uop \<Rightarrow> val \<Rightarrow> val result"
where
"unop_meaning UOpNot (VLit (LitBool b)) = Val (VLit (LitBool (\<not> b)))" |
"unop_meaning UOpPos (VLit (LitNumber n)) = Val (VLit (LitNumber n))" |
"unop_meaning UOpNeg (VLit (LitNumber n)) = Val (VLit (LitNumber (- n)))" |
"unop_meaning _ _ = Aborts TypeError"

fun def_name :: "func \<Rightarrow> var"
where
"def_name (Def f _ _ _) = f"

fun binds_pat :: "pat \<Rightarrow> var set"
where
"binds_pat (PatVar x) = {x}" |
"binds_pat (PatAs p x) = binds_pat p \<union> {x}" |
"binds_pat (PatList ps) = \<Union> (set (map binds_pat ps))" |
"binds_pat (PatTuple ps) = \<Union> (set (map binds_pat ps))" |
"binds_pat (PatConstr q (ps, kps)) = \<Union> (set (map binds_pat ps)) \<union> \<Union> (set (map (binds_pat \<circ> snd) kps))" |
"binds_pat (PatDict kps) = \<Union> (set (map (binds_pat \<circ> snd) kps))" |
"binds_pat _ = {}"

fun binds :: "stmt \<Rightarrow> var set"
where
"binds (StmtSeq s s') = binds s \<union> binds s'" |
"binds (StmtIf _ s elifs else') =
  binds s \<union> \<Union> (set (map (\<lambda>(_, s'). binds s') elifs)) \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> binds s')" |
"binds (StmtMatch _ cases) = \<Union> (set (map (\<lambda>(p, s). binds_pat p \<union> binds s) cases))" |
"binds _ = {}"

fun assigns :: "stmt \<Rightarrow> var set"
where
"assigns (StmtDeclare x _) = {x}" |
"assigns (StmtAssign x _ _) = {x}" |
"assigns (StmtSeq s s') = assigns s \<union> assigns s'" |
"assigns (StmtMutualRegion ds) = set (map def_name ds)" |
"assigns (StmtIf _ s elifs else') =
  assigns s \<union> \<Union> (set (map (\<lambda>(_, s'). assigns s') elifs)) \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> assigns s')" |
"assigns (StmtMatch _ cases) = \<Union> (set (map (\<lambda>(p, s). binds_pat p \<union> assigns s) cases))" |
"assigns _ = {}"

fun declares :: "stmt \<Rightarrow> var list"
where
"declares (StmtDeclare x _) = [x]" |
"declares (StmtAssign x (Some _) _) = [x]" |
"declares (StmtSeq s s') = declares s @ declares s'" |
"declares (StmtMutualRegion ds) = map def_name ds" |
"declares (StmtIf _ s elifs else') =
  declares s @ concat (map (\<lambda>(_, s'). declares s') elifs) @ (case else' of None \<Rightarrow> [] | Some s' \<Rightarrow> declares s')" |
"declares (StmtMatch _ cases) = concat (map (\<lambda>(_, s). declares s) cases)" |
"declares _ = []"

definition scope :: "var set \<Rightarrow> stmt \<Rightarrow> env option"
where
"scope Y s =
  (if distinct (declares s) \<and> Y \<inter> set (declares s) = {} \<and> Y \<inter> binds s = {} \<and> set (declares s) \<inter> binds s = {}
   then Some (\<lambda>x. if x \<in> assigns s - Y then Some VUnbound else None)
   else None)"

abbreviation true :: val where "true \<equiv> VLit (LitBool True)"
abbreviation false :: val where "false \<equiv> VLit (LitBool False)"

type_synonym elif_block = "(expr \<times> stmt) list \<times> stmt option"

inductive
  eval_expr  :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"            ("_, _ \<Rightarrow>\<^sub>e _" [60,0,60] 60) and
  eval_exprs :: "env \<Rightarrow> expr list \<Rightarrow> val list result \<Rightarrow> bool"  ("_, _ \<Rightarrow>\<^sub>e\<^sub>s _" [60,0,60] 60) and
  eval_stmt  :: "env \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"               ("_, _ \<Rightarrow>\<^sub>s _" [60,0,60] 60) and
  eval_elif  :: "env \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"         ("_, _ \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f _" [60,0,60] 60)
where
EvalVar: "\<rho> x = Some v \<Longrightarrow> \<rho>, ExprVar x \<Rightarrow>\<^sub>e Val v" |
EvalLiteral: "\<rho>, ExprLiteral l \<Rightarrow>\<^sub>e Val (VLit l)" |
EvalLambda: "\<rho>, ExprLambda xs e \<Rightarrow>\<^sub>e Val Lam(\<rho>, xs, e)" |
EvalUnOp: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, ExprUnOp op e \<Rightarrow>\<^sub>e mlet r (unop_meaning op)" |
EvalBinOp: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, e' \<Rightarrow>\<^sub>e r \<rbrakk>
  \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e mlet r (binop_meaning op v)" |
EvalBinOpFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalAndFalse: "\<rho>, e \<Rightarrow>\<^sub>e Val false \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e Val false" |
EvalAndTrue: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val true ; \<rho>, e' \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e r" |
EvalAndFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalOrTrue: "\<rho>, e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e Val true" |
EvalOrFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, e' \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e r" |
EvalOrFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalCondTrue: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val true ; \<rho>, e1 \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e r" |
EvalCondFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, e2 \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e r" |
EvalCondFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalList: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val vs \<Longrightarrow> \<rho>, ExprList es \<Rightarrow>\<^sub>e Val (VList vs)" |
EvalListFail: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<Longrightarrow> \<rho>, ExprList es \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalTuple: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val vs \<Longrightarrow> \<rho>, ExprTuple es \<Rightarrow>\<^sub>e Val (VTuple vs)" |
EvalTupleFail: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<Longrightarrow> \<rho>, ExprTuple es \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalCallLambda:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xs = length us
  ; \<rho>'(xs [\<mapsto>] us), e' \<Rightarrow>\<^sub>e r
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e r" |
EvalCallLambdaArity:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xs \<noteq> length us
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalCallDef:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val Def(\<rho>', ds, j)
  ; ds ! j = Def f xps \<psi> s
  ; vs = map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds]
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xps = length us
  ; scope (set (map fst xps)) s = Some \<rho>s
  ; \<rho>'(map def_name ds [\<mapsto>] vs, map fst xps [\<mapsto>] us) ++ \<rho>s, s \<Rightarrow>\<^sub>s o
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e call_result o" |
EvalCallDefArity:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val Def(\<rho>', ds, j)
  ; ds ! j = Def f xps \<psi> s
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xps \<noteq> length us
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalCallNonFun:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us ; \<not> is_closure v \<rbrakk>
  \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalCallFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalCallFailArgs:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts \<kappa>" |

EvalExprsNil: "\<rho>, [] \<Rightarrow>\<^sub>e\<^sub>s Val []" |
EvalExprsCons: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s r \<rbrakk>
  \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s mlet r (\<lambda>vs. Val (v # vs))" |
EvalExprsFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa>" |

EvalPass: "\<rho>, StmtPass \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalAssign: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtAssign x \<pi> e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. Assigns [x \<mapsto> v])" |
EvalExprStmt: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtExpr e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. Assigns \<epsilon>)" |
EvalReturn: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtReturn e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. Returns v)" |
EvalReturnNone: "\<rho>, StmtReturnNone \<Rightarrow>\<^sub>s Returns (VLit LitNone)" |
EvalDefs:
  "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]
  \<Longrightarrow> \<rho>, StmtMutualRegion ds \<Rightarrow>\<^sub>s Assigns (\<epsilon>(map def_name ds [\<mapsto>] vs))" |
EvalAssert: "\<rho>, e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, StmtAssert e \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalAssertFalse: "\<rho>, e \<Rightarrow>\<^sub>e Val false \<Longrightarrow> \<rho>, StmtAssert e \<Rightarrow>\<^sub>s Aborts\<^sub>o (AssertionError None)" |
EvalAssertFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssert e \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalAssertMsg: "\<rho>, e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, StmtAssertMsg e e' \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalAssertMsgFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, e' \<Rightarrow>\<^sub>e r \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssertMsg e e' \<Rightarrow>\<^sub>s mlet r (\<lambda>w. Aborts\<^sub>o (AssertionError (Some w)))" |
EvalAssertMsgFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssertMsg e e' \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalIfTrue: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val true ; \<rho>, s \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s o" |
EvalIfFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, (elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s o" |
EvalIfFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalSeq: "\<lbrakk> \<rho>, s \<Rightarrow>\<^sub>s Assigns \<rho>' ; \<rho> ++ \<rho>', s' \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s Assigns \<rho>' \<bullet> o" |
EvalSeqReturn: "\<rho>, s \<Rightarrow>\<^sub>s Returns v \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s Returns v" |
EvalSeqFail: "\<rho>, s \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa> \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |

EvalIfNone: "\<rho>, ([], None) \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f Assigns \<epsilon>" |
EvalElse: "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<rho>, ([], Some s) \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifTrue: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val true ; \<rho>, s \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, (elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<rbrakk>
  \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f Aborts\<^sub>o \<kappa>"

lemmas eval_induct = eval_expr_eval_exprs_eval_stmt_eval_elif.inducts

end
