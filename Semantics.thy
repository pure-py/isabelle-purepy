theory Semantics
    imports Syntax HOL.Map 
begin

datatype val =
      VLit l
    | VList "val list"
    | VTuple "val list"
    | VClosure "vname \<rightharpoonup> val" "vname list" expr    ("\<langle>_,_,_\<rangle>\<^sub>\<lambda>")
    | VDefClosure "vname \<rightharpoonup> val" "func list" nat   ("\<langle>_,_,_\<rangle>\<^sub>C")

type_synonym \<rho> = "vname \<rightharpoonup> val"
definition \<epsilon> :: \<rho> where "\<epsilon> = Map.empty"

datatype r = Assigns \<rho> | Returns val

fun (sequential) r_dot :: "r \<Rightarrow> r \<Rightarrow> r option" (infixl "\<bullet>" 70)
where
"(Assigns \<rho>) \<bullet> (Assigns \<rho>') = Some (Assigns (\<rho> ++ \<rho>'))" |
"(Assigns \<rho>) \<bullet> (Returns v) = Some (Returns v)" |
"_ \<bullet> _ = None"

fun unwrap :: "r \<Rightarrow> val option"
where
"unwrap (Returns v) = Some v" |
"unwrap (Assigns _) = None"

definition binop_eval :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val option" where
"binop_eval op v1 v2 = (case (op, v1, v2) of
    (BOpOr,  VLit (LitBool b1), VLit (LitBool b2)) \<Rightarrow> Some (VLit (LitBool (b1 \<or> b2)))
  | (BOpAnd, VLit (LitBool b1), VLit (LitBool b2)) \<Rightarrow> Some (VLit (LitBool (b1 \<and> b2)))
  | (BOpEq,  VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow> Some (VLit (LitBool (n1 = n2)))
  | (BOpEq,  VLit (LitBool b1), VLit (LitBool b2)) \<Rightarrow> Some (VLit (LitBool (b1 = b2)))
  | (BOpNeq, VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow> Some (VLit (LitBool (n1 \<noteq> n2)))
  | (BOpNeq, VLit (LitBool b1), VLit (LitBool b2)) \<Rightarrow> Some (VLit (LitBool (b1 \<noteq> b2)))
  | (BOpLt,  VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow> Some (VLit (LitBool (n1 < n2)))
  | (BOpLeq, VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow> Some (VLit (LitBool (n1 \<le> n2)))
  | (BOpGt,  VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow> Some (VLit (LitBool (n1 > n2)))
  | (BOpGeq, VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow> Some (VLit (LitBool (n1 \<ge> n2)))
  | (BOpAdd, VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow> Some (VLit (LitNumber (n1 + n2)))
  | (BOpSub, VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow> Some (VLit (LitNumber (n1 - n2)))
  | (BOpMul, VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow> Some (VLit (LitNumber (n1 * n2)))
  | (BOpDiv, VLit (LitNumber n1), VLit (LitNumber n2)) \<Rightarrow>
      Some (VLit (LitNumber (n1 div n2)))
  | _ \<Rightarrow> None)"

definition unop_eval :: "uop \<Rightarrow> val \<Rightarrow> val option" where
"unop_eval op v = (case (op, v) of
    (UOpNot, VLit (LitBool b)) => Some (VLit (LitBool (\<not>b)))
  | (UOpNeg, VLit (LitNumber n)) => Some (VLit (LitNumber (-n)))
  | _ => None)"

type_synonym elif_block = "(expr \<times> stmt) list \<times> stmt option"

inductive 
  eval_expr  :: "\<rho> \<Rightarrow> expr  \<Rightarrow> val \<Rightarrow> bool"    ("_ \<turnstile>\<^sub>e _ \<Rightarrow> _" [60,0,60] 60) and
  eval_stmt  :: "\<rho> \<Rightarrow> stmt  \<Rightarrow> r   \<Rightarrow> bool"    ("_ \<turnstile>\<^sub>s _ \<Rightarrow> _" [60,0,60] 60) and
  eval_elif  :: "\<rho> \<Rightarrow> elif_block \<Rightarrow> r \<Rightarrow> bool" ("_ \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f _ \<Rightarrow> _" [60, 0, 60] 60)
where
EvalVar: "\<lbrakk> \<rho> x = Some v \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprVar x \<Rightarrow> v" |
EvalLit: "\<rho> \<turnstile>\<^sub>e ExprLiteral l \<Rightarrow> VLit l" |
EvalBinOp: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e1 \<Rightarrow> v1 ; \<rho> \<turnstile>\<^sub>e e2 \<Rightarrow> v2 ; binop_eval op v1 v2 = Some v' \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprBinOp op e1 e2 \<Rightarrow> v'" |
EvalUnOp: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v ; unop_eval op v = Some v' \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprUnOp op e \<Rightarrow> v'" |
EvalCondExprTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e c \<Rightarrow> VLit (LitBool True) ; \<rho> \<turnstile>\<^sub>e t \<Rightarrow> v \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCond t c e \<Rightarrow> v" | 
EvalCondExprFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e c \<Rightarrow> VLit (LitBool False) ; \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCond t c e \<Rightarrow> v" |
EvalList: "\<lbrakk> list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprList es \<Rightarrow> VList vals" |
EvalTuple: "\<lbrakk> list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprTuple es \<Rightarrow> VTuple vals" |
EvalCallLambda:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>', xs, e'\<rangle>\<^sub>\<lambda>
  ; list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) args u'
  ; \<rho>'(xs [\<mapsto>] u') \<turnstile>\<^sub>e e' \<Rightarrow> v
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCall e args \<Rightarrow> v" |
EvalCallDef:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>', ds, j\<rangle>\<^sub>C
  ; vs = map (\<lambda>i. \<langle>\<rho>', ds, i\<rangle>\<^sub>C) [0..<length ds]
  ; fs = map (\<lambda> d . (case d of (Def f _ _ _) => f)) ds
  ; xs = map (\<lambda> d . (case d of (Def _ x _ _) \<Rightarrow> map fst x)) ds
  ; bs = map (\<lambda> d . (case d of (Def _ _ _ b) \<Rightarrow> b)) ds
  ; list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) args u'
  ; (\<rho>'(fs [\<mapsto>] vs))((xs ! j) [\<mapsto>] u') \<turnstile>\<^sub>s (bs ! j) \<Rightarrow> r
  ; unwrap r = Some r'
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e ExprCall e args \<Rightarrow> r'" |
EvalLambda: "\<rho> \<turnstile>\<^sub>e ExprLambda args e \<Rightarrow> \<langle>\<rho>, args, e\<rangle>\<^sub>\<lambda>" |

(* EvalBlockAssigns:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>s s \<Rightarrow> (Assigns \<rho>') ; (\<rho> ++ \<rho>') \<turnstile>\<^sub>s b \<Rightarrow> r ; (Assigns \<rho>') \<bullet> r = Some r' \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s (s # b) \<Rightarrow> r'" |
EvalBlockReturns:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>s s \<Rightarrow> Returns v \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>s (s # b) \<Rightarrow> Returns v" | *)

EvalPass: "\<rho> \<turnstile>\<^sub>s StmtPass \<Rightarrow> Assigns \<epsilon>" |
EvalAssign: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssign x _ e \<Rightarrow> Assigns [x \<mapsto> v]" |
EvalExpr: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtExpr e \<Rightarrow> Assigns \<epsilon>" |
EvalAssert: 
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v ; v \<noteq> VLit (LitBool False) \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssert e \<Rightarrow> Assigns \<epsilon>" |
EvalAssertMsg:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v ; v \<noteq> VLit (LitBool False) \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtAssertMsg e e' \<Rightarrow> Assigns \<epsilon>" |
EvalReturnNone: "\<rho> \<turnstile>\<^sub>s StmtReturnNone \<Rightarrow> Returns (VLit LitNone)" |
EvalReturn: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtReturn e \<Rightarrow> Returns v" |
EvalIfTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> VLit (LitBool True) ; \<rho> \<turnstile>\<^sub>s b \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtIf e b elifs else' \<Rightarrow> r" |
EvalIfFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> VLit (LitBool False) ; \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f (elifs, else') \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtIf e b elifs else' \<Rightarrow> r" |
EvalMutual: 
  "\<lbrakk> vs = map (\<lambda> i . \<langle>\<rho>, ds, i\<rangle>\<^sub>C) [0..<length ds]
  ; fs = map (\<lambda> d . (case d of Def f _ _ _ \<Rightarrow> f)) ds
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>s StmtMutualRegion ds \<Rightarrow> Assigns (\<epsilon>(fs [\<mapsto>] vs))" | 

EvalElifEmpty: "\<rho> \<turnstile>\<^sub>s b \<Rightarrow> r \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ([], Some b) \<Rightarrow> r" |
EvalElifTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> VLit (Bool True) ; \<rho> \<turnstile>\<^sub>s b \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ((e, b) # elifs', else') \<Rightarrow> r" |
EvalElifFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> VLit (Bool False) ; \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f (elifs', else') \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ((e, b) # elifs', else') \<Rightarrow> r"

lemmas eval_induct = eval_expr_eval_stmt_eval_elif.inducts

end