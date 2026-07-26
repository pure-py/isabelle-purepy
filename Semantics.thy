theory Semantics
    imports Syntax HOL.Map
begin

datatype val =
      VLit literal
    | VList "val list"
    | VTuple "val list"
    | VClosure "vname \<rightharpoonup> val" "vname list" expr    ("\<langle>_,_,_\<rangle>\<^sub>\<lambda>")
    | VDefClosure "vname \<rightharpoonup> val" "func list" nat   ("\<langle>_,_,_\<rangle>\<^sub>C")

type_synonym \<rho> = "vname \<rightharpoonup> val"
definition \<epsilon> :: \<rho> where "\<epsilon> = Map.empty"

fun (sequential) "\<rho>_dot" :: "\<rho> \<Rightarrow> \<rho> \<Rightarrow> \<rho>" (infixl "\<cdot>" 70)
where "\<rho> \<cdot> \<rho>' = \<rho> ++ \<rho>'"

datatype r = Assigns \<rho> | Returns val

fun (sequential) r_dot :: "r \<Rightarrow> r \<Rightarrow> r option" (infixl "\<bullet>" 70)
where
"Assigns \<rho> \<bullet> Assigns \<rho>' = Some (Assigns (\<rho> \<cdot> \<rho>'))" |
"Assigns \<rho> \<bullet> Returns v = Some (Returns v)" |
"_ \<bullet> _ = None"

fun unwrap :: "r \<Rightarrow> val option"
where
"unwrap (Returns v) = Some v" |
"unwrap (Assigns _) = None"

definition binop_eval :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val option" where
"binop_eval op v1 v2 = (case (op, v1, v2) of
    (Or,  VLit (Bool b1), VLit (Bool b2)) \<Rightarrow> Some (VLit (Bool (b1 \<or> b2)))
  | (And, VLit (Bool b1), VLit (Bool b2)) \<Rightarrow> Some (VLit (Bool (b1 \<and> b2)))
  | (Eq,  VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Bool (n1 = n2)))
  | (Eq,  VLit (Bool b1), VLit (Bool b2)) \<Rightarrow> Some (VLit (Bool (b1 = b2)))
  | (Neq, VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Bool (n1 \<noteq> n2)))
  | (Neq, VLit (Bool b1), VLit (Bool b2)) \<Rightarrow> Some (VLit (Bool (b1 \<noteq> b2)))
  | (Lt,  VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Bool (n1 < n2)))
  | (Leq, VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Bool (n1 \<le> n2)))
  | (Gt,  VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Bool (n1 > n2)))
  | (Geq, VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Bool (n1 \<ge> n2)))
  | (Add, VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Number (n1 + n2)))
  | (Sub, VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Number (n1 - n2)))
  | (Mul, VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Number (n1 * n2)))
  | (Div, VLit (Number n1), VLit (Number n2)) \<Rightarrow>
      Some (VLit (Number (n1 div n2)))
  | _ \<Rightarrow> None)"

definition unop_eval :: "uop \<Rightarrow> val \<Rightarrow> val option" where
"unop_eval op v = (case (op, v) of
    (Not, VLit (Bool b)) => Some (VLit (Bool (\<not>b)))
  | (Neg, VLit (Number n)) => Some (VLit (Number (-n)))
  | _ => None)"

type_synonym elif_block = "(expr \<times> block) list \<times> block option"

inductive 
  eval_expr  :: "\<rho> \<Rightarrow> expr  \<Rightarrow> val \<Rightarrow> bool"    ("_ \<turnstile>\<^sub>e _ \<Rightarrow> _" [60,0,60] 60) and
  eval_block :: "\<rho> \<Rightarrow> block \<Rightarrow> r   \<Rightarrow> bool"    ("_ \<turnstile>\<^sub>b _ \<Rightarrow> _" [60,0,60] 60) and
  eval_stmt  :: "\<rho> \<Rightarrow> stmt  \<Rightarrow> r   \<Rightarrow> bool"    ("_ \<turnstile>\<^sub>s _ \<Rightarrow> _" [60,0,60] 60) and
  eval_elif  :: "\<rho> \<Rightarrow> elif_block \<Rightarrow> r \<Rightarrow> bool" ("_ \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f _ \<Rightarrow> _" [60, 0, 60] 60)
where
EvalVar: "\<lbrakk> \<rho> x = Some v \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e Var x \<Rightarrow> v" |
EvalLit: "\<rho> \<turnstile>\<^sub>e Literal l \<Rightarrow> VLit l" |
EvalBinOp: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e1 \<Rightarrow> v1 ; \<rho> \<turnstile>\<^sub>e e2 \<Rightarrow> v2 ; binop_eval op v1 v2 = Some v' \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e BinOp op e1 e2 \<Rightarrow> v'" |
EvalUnOp: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v ; unop_eval op v = Some v' \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e UnOp op e \<Rightarrow> v'" |
EvalCondExprTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e c \<Rightarrow> VLit (Bool True) ; \<rho> \<turnstile>\<^sub>e t \<Rightarrow> v \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e CondExpr t c e \<Rightarrow> v" | 
EvalCondExprFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e c \<Rightarrow> VLit (Bool False) ; \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e CondExpr t c e \<Rightarrow> v" |
EvalList: "\<lbrakk> list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e List es \<Rightarrow> VList vals" |
EvalTuple: "\<lbrakk> list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e Tuple es \<Rightarrow> VTuple vals" |
EvalCallLambda:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>', xs, e'\<rangle>\<^sub>\<lambda>
  ; list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) args u'
  ; \<rho>'(xs [\<mapsto>] u') \<turnstile>\<^sub>e e' \<Rightarrow> v
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e Call e args \<Rightarrow> v" |
EvalCallDef:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>', ds, j\<rangle>\<^sub>C
  ; vs = map (\<lambda>i. \<langle>\<rho>', ds, i\<rangle>\<^sub>C) [0..<length ds]
  ; fs = map (\<lambda> d . (case d of (DefFunc f _ _) => f)) ds
  ; xs = map (\<lambda> d . (case d of (DefFunc _ x _) \<Rightarrow> x)) ds
  ; bs = map (\<lambda> d . (case d of (DefFunc _ _ b) \<Rightarrow> b)) ds
  ; list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) args u'
  ; (\<rho>'(fs [\<mapsto>] vs))((xs ! j) [\<mapsto>] u') \<turnstile>\<^sub>b (bs ! j) \<Rightarrow> r
  ; unwrap r = Some r'
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e Call e args \<Rightarrow> r'" |
EvalLambda: "\<rho> \<turnstile>\<^sub>e Lambda args e \<Rightarrow> \<langle>\<rho>, args, e\<rangle>\<^sub>\<lambda>" |

EvalBlock:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>s s \<Rightarrow> (Assigns \<rho>') ; (\<rho> \<cdot> \<rho>') \<turnstile>\<^sub>b b \<Rightarrow> r ; (Assigns \<rho>') \<bullet> r = Some r' \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>b (s # b) \<Rightarrow> r'" |

EvalPass: "\<rho> \<turnstile>\<^sub>s Pass \<Rightarrow> Assigns \<epsilon>" |
EvalAssign: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<^sub>s Assign x e \<Rightarrow> Assigns [x \<mapsto> v]" |
EvalExpr: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<^sub>s Expr e \<Rightarrow> Assigns \<epsilon>" |
EvalAssert: 
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v ; v \<noteq> VLit (Bool False) \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>s Assert e \<Rightarrow> Assigns \<epsilon>" |
EvalAssertMsg:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v ; v \<noteq> VLit (Bool False) \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s AssertMsg e e' \<Rightarrow> Assigns \<epsilon>" |
EvalReturnNone: "\<rho> \<turnstile>\<^sub>s ReturnNone \<Rightarrow> Returns (VLit LitNone)" |
EvalReturn: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<Longrightarrow> \<rho> \<turnstile>\<^sub>s Return e \<Rightarrow> Returns v" |
EvalIfTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> VLit (Bool True) ; \<rho> \<turnstile>\<^sub>b b \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s If e b elifs else' \<Rightarrow> r" |
EvalIfFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> VLit (Bool True) ; \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f (elifs, else') \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>s If e b elifs else' \<Rightarrow> r" |
EvalMutual: 
  "\<lbrakk> vs = map (\<lambda> i . \<langle>\<rho>, ds, i\<rangle>\<^sub>C) [0..<length ds]
  ; fs = map (\<lambda> d . (case d of DefFunc f _ _ \<Rightarrow> f)) ds
  \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>s MutualRegion ds \<Rightarrow> Assigns (\<epsilon>(fs [\<mapsto>] vs))" | 

EvalElifEmpty: "\<rho> \<turnstile>\<^sub>b b \<Rightarrow> r \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ([], Some b) \<Rightarrow> r" |
EvalElifTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> VLit (Bool True) ; \<rho> \<turnstile>\<^sub>b b \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ((e, b) # elifs', else') \<Rightarrow> r" |
EvalElifFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> VLit (Bool False) ; \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f (elifs', else') \<Rightarrow> r \<rbrakk>
  \<Longrightarrow> \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ((e, b) # elifs', else') \<Rightarrow> r"

end