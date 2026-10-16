theory Semantics
    imports Syntax HOL.Map
begin

(* Free o for outcomes, as in the spec *)
no_notation (ASCII) comp (infixl \<open>o\<close> 55)

datatype val =
      VLit l
    | VList "val list"
    | VTuple "val list"
    | VLamClosure "vname \<rightharpoonup> val" "vname list" expr    ("Lam'(_, _, _')")
    | VDefClosure "vname \<rightharpoonup> val" "func list" nat      ("Def'(_, _, _')")
    | VUnbound

type_synonym \<rho> = "vname \<rightharpoonup> val"
abbreviation \<epsilon> :: \<rho> where "\<epsilon> \<equiv> Map.empty"

datatype \<kappa> =
    TypeError
  | IndexError
  | KeyError
  | ZeroDivisionError
  | AssertionError "val option"
  | AttributeError
  | SystemExit int
  | Undef

datatype 'a result = Val 'a | Aborts \<kappa>

type_synonym r = "val result"

datatype normal_outcome = Assigns \<rho> | Returns val

type_synonym outcome = "normal_outcome result"

fun mlet :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result"
where
"mlet (Val v) f = f v" |
"mlet (Aborts \<kappa>) f = Aborts \<kappa>"

fun compose :: "outcome \<Rightarrow> outcome \<Rightarrow> outcome" (infixl "\<bullet>" 70)
where
"Val (Assigns \<rho>) \<bullet> Val (Assigns \<rho>') = Val (Assigns (\<rho> ++ \<rho>'))" |
"Val (Assigns \<rho>) \<bullet> o = o" |
"Val (Returns v) \<bullet> o = Val (Returns v)" |
"Aborts \<kappa> \<bullet> o = Aborts \<kappa>"

fun call_result :: "outcome \<Rightarrow> r"
where
"call_result (Val (Returns v)) = Val v" |
"call_result (Val (Assigns \<rho>)) = Val (VLit LitNone)" |
"call_result (Aborts \<kappa>) = Aborts \<kappa>"

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

fun binop_meaning :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> r"
where
"binop_meaning BOpEq v v' = mlet (eq v v') (\<lambda>b. Val (VLit (LitBool b)))" |
"binop_meaning BOpNeq v v' = mlet (eq v v') (\<lambda>b. Val (VLit (LitBool (\<not> b))))" |
"binop_meaning BOpLt (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitBool (n < n')))" |
"binop_meaning BOpLeq (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitBool (n \<le> n')))" |
"binop_meaning BOpGt (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitBool (n > n')))" |
"binop_meaning BOpGeq (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitBool (n \<ge> n')))" |
"binop_meaning BOpAdd (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitNumber (n + n')))" |
"binop_meaning BOpSub (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitNumber (n - n')))" |
"binop_meaning BOpMul (VLit (LitNumber n)) (VLit (LitNumber n')) = Val (VLit (LitNumber (n * n')))" |
"binop_meaning BOpDiv (VLit (LitNumber n)) (VLit (LitNumber n')) =
  (if n' = 0 then Aborts ZeroDivisionError else Val (VLit (LitNumber (n div n'))))" |
"binop_meaning _ _ _ = Aborts TypeError"

fun unop_meaning :: "uop \<Rightarrow> val \<Rightarrow> r"
where
"unop_meaning UOpNot (VLit (LitBool b)) = Val (VLit (LitBool (\<not> b)))" |
"unop_meaning UOpNeg (VLit (LitNumber n)) = Val (VLit (LitNumber (- n)))" |
"unop_meaning _ _ = Aborts TypeError"

fun def_name :: "func \<Rightarrow> vname"
where
"def_name (Def f _ _ _) = f"

fun binds_pat :: "p \<Rightarrow> vname set"
where
"binds_pat (PatVar x) = {x}" |
"binds_pat (PatAs p x) = binds_pat p \<union> {x}" |
"binds_pat (PatList ps) = \<Union> (set (map binds_pat ps))" |
"binds_pat (PatTuple ps) = \<Union> (set (map binds_pat ps))" |
"binds_pat (PatConstr q ps kps) = \<Union> (set (map binds_pat ps)) \<union> \<Union> (set (map (binds_pat \<circ> snd) kps))" |
"binds_pat (PatDict kps) = \<Union> (set (map (binds_pat \<circ> snd) kps))" |
"binds_pat _ = {}"

fun binds :: "stmt \<Rightarrow> vname set"
where
"binds (StmtSeq s s') = binds s \<union> binds s'" |
"binds (StmtIf _ s elifs else') =
  binds s \<union> \<Union> (set (map (\<lambda>(_, s'). binds s') elifs)) \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> binds s')" |
"binds (StmtMatch _ cases) = \<Union> (set (map (\<lambda>(p, s). binds_pat p \<union> binds s) cases))" |
"binds _ = {}"

fun assigns :: "stmt \<Rightarrow> vname set"
where
"assigns (StmtAssign x _ _) = {x}" |
"assigns (StmtSeq s s') = assigns s \<union> assigns s'" |
"assigns (StmtMutualRegion ds) = set (map def_name ds)" |
"assigns (StmtIf _ s elifs else') =
  assigns s \<union> \<Union> (set (map (\<lambda>(_, s'). assigns s') elifs)) \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> assigns s')" |
"assigns (StmtMatch _ cases) = \<Union> (set (map (\<lambda>(p, s). binds_pat p \<union> assigns s) cases))" |
"assigns _ = {}"

fun declares :: "stmt \<Rightarrow> vname list"
where
"declares (StmtAssign x (Some _) _) = [x]" |
"declares (StmtSeq s s') = declares s @ declares s'" |
"declares (StmtMutualRegion ds) = map def_name ds" |
"declares (StmtIf _ s elifs else') =
  declares s @ concat (map (\<lambda>(_, s'). declares s') elifs) @ (case else' of None \<Rightarrow> [] | Some s' \<Rightarrow> declares s')" |
"declares (StmtMatch _ cases) = concat (map (\<lambda>(_, s). declares s) cases)" |
"declares _ = []"

definition scope :: "vname set \<Rightarrow> stmt \<Rightarrow> \<rho> option"
where
"scope Y s =
  (if distinct (declares s) \<and> Y \<inter> set (declares s) = {} \<and> Y \<inter> binds s = {} \<and> set (declares s) \<inter> binds s = {}
   then Some (\<lambda>x. if x \<in> assigns s - Y then Some VUnbound else None)
   else None)"

abbreviation true :: val where "true \<equiv> VLit (LitBool True)"
abbreviation false :: val where "false \<equiv> VLit (LitBool False)"

type_synonym elif_block = "(expr \<times> stmt) list \<times> stmt option"

inductive
  eval_expr  :: "\<rho> \<Rightarrow> expr \<Rightarrow> r \<Rightarrow> bool"                     ("_ \<turnstile>\<^sub>e _ \<Rightarrow> _" [60,0,60] 60) and
  eval_exprs :: "\<rho> \<Rightarrow> expr list \<Rightarrow> val list result \<Rightarrow> bool"    ("_ \<turnstile>\<^sub>e\<^sub>s _ \<Rightarrow> _" [60,0,60] 60) and
  eval_stmt  :: "\<rho> \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"                     ("_ \<turnstile>\<^sub>s _ \<Rightarrow> _" [60,0,60] 60) and
  eval_elif  :: "\<rho> \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"               ("_ \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f _ \<Rightarrow> _" [60,0,60] 60)
where
EvalVar: "\<rho> x = Some v \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprVar x \<Rightarrow> Val v" |
EvalLiteral: "\<rho> \<turnstile>\<^sub>e ExprLiteral l \<Rightarrow> Val (VLit l)" |
EvalLambda: "\<rho> \<turnstile>\<^sub>e ExprLambda xs e \<Rightarrow> Val Lam(\<rho>, xs, e)" |
EvalUnOp: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> r \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprUnOp op e \<Rightarrow> mlet r (unop_meaning op)" |
EvalBinOp: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val v ; \<rho> \<turnstile>\<^sub>e e' \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprBinOp op e e' \<Rightarrow> mlet r (binop_meaning op v)" |
EvalBinOpFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprBinOp op e e' \<Rightarrow> Aborts \<kappa>" |
EvalAndFalse: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val false \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprAnd e e' \<Rightarrow> Val false" |
EvalAndTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val true ; \<rho> \<turnstile>\<^sub>e e' \<Rightarrow> r \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprAnd e e' \<Rightarrow> r" |
EvalAndFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprAnd e e' \<Rightarrow> Aborts \<kappa>" |
EvalOrTrue: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val true \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprOr e e' \<Rightarrow> Val true" |
EvalOrFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val false ; \<rho> \<turnstile>\<^sub>e e' \<Rightarrow> r \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprOr e e' \<Rightarrow> r" |
EvalOrFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprOr e e' \<Rightarrow> Aborts \<kappa>" |
EvalCondTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val true ; \<rho> \<turnstile>\<^sub>e e1 \<Rightarrow> r \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCond e1 e e2 \<Rightarrow> r" |
EvalCondFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val false ; \<rho> \<turnstile>\<^sub>e e2 \<Rightarrow> r \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCond e1 e e2 \<Rightarrow> r" |
EvalCondFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCond e1 e e2 \<Rightarrow> Aborts \<kappa>" |
EvalList: "\<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Val vs \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprList es \<Rightarrow> Val (VList vs)" |
EvalListFail: "\<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprList es \<Rightarrow> Aborts \<kappa>" |
EvalTuple: "\<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Val vs \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprTuple es \<Rightarrow> Val (VTuple vs)" |
EvalTupleFail: "\<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprTuple es \<Rightarrow> Aborts \<kappa>" |
EvalCallLambda:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val Lam(\<rho>', xs, e')
  ; \<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Val us
  ; length xs = length us
  ; \<rho>'(xs [\<mapsto>] us) \<turnstile>\<^sub>e e' \<Rightarrow> r
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCall e es [] \<Rightarrow> r" |
EvalCallLambdaArity:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val Lam(\<rho>', xs, e')
  ; \<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Val us
  ; length xs \<noteq> length us
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCall e es [] \<Rightarrow> Aborts TypeError" |
EvalCallDef:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val Def(\<rho>', ds, j)
  ; ds ! j = Def f xps \<omega> s
  ; vs = map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds]
  ; \<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Val us
  ; length xps = length us
  ; scope (set (map fst xps)) s = Some \<rho>s
  ; \<rho>'(map def_name ds [\<mapsto>] vs, map fst xps [\<mapsto>] us) ++ \<rho>s \<turnstile>\<^sub>s s \<Rightarrow> o
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCall e es [] \<Rightarrow> call_result o" |
EvalCallDefArity:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val Def(\<rho>', ds, j)
  ; ds ! j = Def f xps \<omega> s
  ; \<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Val us
  ; length xps \<noteq> length us
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCall e es [] \<Rightarrow> Aborts TypeError" |
EvalCallNonFun:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val v ; \<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Val us ; \<not> is_closure v \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCall e es [] \<Rightarrow> Aborts TypeError" |
EvalCallFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCall e es [] \<Rightarrow> Aborts \<kappa>" |
EvalCallFailArgs:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val v ; \<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCall e es [] \<Rightarrow> Aborts \<kappa>" |

EvalExprsNil: "\<rho> \<turnstile>\<^sub>e\<^sub>s [] \<Rightarrow> Val []" |
EvalExprsCons: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val v ; \<rho> \<turnstile>\<^sub>e\<^sub>s es \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>s e # es \<Rightarrow> mlet r (\<lambda>vs. Val (v # vs))" |
EvalExprsFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>s e # es \<Rightarrow> Aborts \<kappa>" |

EvalPass: "\<rho> \<turnstile>\<^sub>s StmtPass \<Rightarrow> Val (Assigns \<epsilon>)" |
EvalAssign: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> r \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssign x \<pi> e \<Rightarrow> mlet r (\<lambda>v. Val (Assigns [x \<mapsto> v]))" |
EvalExprStmt: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> r \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtExpr e \<Rightarrow> mlet r (\<lambda>v. Val (Assigns \<epsilon>))" |
EvalReturn: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> r \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtReturn e \<Rightarrow> mlet r (\<lambda>v. Val (Returns v))" |
EvalReturnNone: "\<rho> \<turnstile>\<^sub>s StmtReturnNone \<Rightarrow> Val (Returns (VLit LitNone))" |
EvalDefs:
  "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtMutualRegion ds \<Rightarrow> Val (Assigns (\<epsilon>(map def_name ds [\<mapsto>] vs)))" |
EvalAssert: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val true \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssert e \<Rightarrow> Val (Assigns \<epsilon>)" |
EvalAssertFalse: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val false \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssert e \<Rightarrow> Aborts (AssertionError None)" |
EvalAssertFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssert e \<Rightarrow> Aborts \<kappa>" |
EvalAssertMsg: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val true \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssertMsg e e' \<Rightarrow> Val (Assigns \<epsilon>)" |
EvalAssertMsgFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val false ; \<rho> \<turnstile>\<^sub>e e' \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssertMsg e e' \<Rightarrow> mlet r (\<lambda>w. Aborts (AssertionError (Some w)))" |
EvalAssertMsgFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssertMsg e e' \<Rightarrow> Aborts \<kappa>" |
EvalIfTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val true ; \<rho> \<turnstile>\<^sub>s s \<Rightarrow> o \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtIf e s elifs else' \<Rightarrow> o" |
EvalIfFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val false ; \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f (elifs, else') \<Rightarrow> o \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtIf e s elifs else' \<Rightarrow> o" |
EvalIfFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtIf e s elifs else' \<Rightarrow> Aborts \<kappa>" |
EvalSeq: "\<lbrakk> \<rho> \<turnstile>\<^sub>s s \<Rightarrow> Val (Assigns \<rho>') ; \<rho> ++ \<rho>' \<turnstile>\<^sub>s s' \<Rightarrow> o \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtSeq s s' \<Rightarrow> Val (Assigns \<rho>') \<bullet> o" |
EvalSeqReturn: "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Val (Returns v) \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtSeq s s' \<Rightarrow> Val (Returns v)" |
EvalSeqFail: "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtSeq s s' \<Rightarrow> Aborts \<kappa>" |

EvalIfNone: "\<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ([], None) \<Rightarrow> Val (Assigns \<epsilon>)" |
EvalElse: "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> o \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ([], Some s) \<Rightarrow> o" |
EvalElifTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val true ; \<rho> \<turnstile>\<^sub>s s \<Rightarrow> o \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ((e, s) # elifs, else') \<Rightarrow> o" |
EvalElifFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> Val false ; \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f (elifs, else') \<Rightarrow> o \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ((e, s) # elifs, else') \<Rightarrow> o" |
EvalElifFail: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> Aborts \<kappa> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ((e, s) # elifs, else') \<Rightarrow> Aborts \<kappa>"

lemmas eval_induct = eval_expr_eval_exprs_eval_stmt_eval_elif.inducts

end
