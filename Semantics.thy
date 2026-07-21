theory Semantics
    imports Syntax
begin

datatype val =
      VLit literal
    | VList "val list" 
    | VTuple "val list"
    | VClosure "vname \<Rightarrow> val" "vname list" expr

type_synonym "\<rho>" = "vname \<Rightarrow> val"

datatype r =
      Assigns "\<rho>"
    | Returns val

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
   | (Div, VLit (Number n1), VLit (Number n2)) \<Rightarrow> Some (VLit (Number (n1 div n2)))
   | _ \<Rightarrow> Option.None)"

definition unop_eval :: "uop \<Rightarrow> val \<Rightarrow> val option" where
  "unop_eval op v = (case (op, v) of
    (Not, VLit (Bool b)) => Some (VLit (Bool (\<not>b)))
  | (Neg, VLit (Number n)) => Some (VLit (Number (-n)))
  | _ => Option.None)"

inductive expr_eval :: "\<rho> \<Rightarrow> expr \<Rightarrow> val \<Rightarrow> bool" ("_ \<turnstile>\<^sub>e _ \<Rightarrow> _" [60,0,60] 60)
where
EvalVar: "\<rho> \<turnstile>\<^sub>e Var x \<Rightarrow> \<rho> x" |
EvalLit: "\<rho> \<turnstile>\<^sub>e Literal l \<Rightarrow> VLit l" |
EvalBinOp: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e1 \<Rightarrow> v1 ; \<rho> \<turnstile>\<^sub>e e2 \<Rightarrow> v2 ; binop_eval op v1 v2 = Some v' \<rbrakk> \<Longrightarrow> 
    \<rho> \<turnstile>\<^sub>e BinOp op e1 e2 \<Rightarrow> v'" |
EvalUnOp: "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v ; unop_eval op v = Some v' \<rbrakk> \<Longrightarrow> \<rho> \<turnstile>\<^sub>e UnOp op e \<Rightarrow> v'" |
EvalCondExprTrue: "\<lbrakk> \<rho> \<turnstile>\<^sub>e c \<Rightarrow> VLit (Bool True) ; \<rho> \<turnstile>\<^sub>e t \<Rightarrow> v \<rbrakk> \<Longrightarrow> 
    \<rho> \<turnstile>\<^sub>e CondExpr t c e \<Rightarrow> v" | 
EvalCondExprFalse: "\<lbrakk> \<rho> \<turnstile>\<^sub>e c \<Rightarrow> VLit (Bool False) ; \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<rbrakk> \<Longrightarrow> 
    \<rho> \<turnstile>\<^sub>e CondExpr t c e \<Rightarrow> v" |
EvalList: "\<lbrakk> list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals \<rbrakk> \<Longrightarrow> 
    \<rho> \<turnstile>\<^sub>e List es \<Rightarrow> VList vals" |
EvalTuple: "\<lbrakk> list_all2 (\<lambda> e v . \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals \<rbrakk> \<Longrightarrow> 
    \<rho> \<turnstile>\<^sub>e Tuple es \<Rightarrow> VTuple vals" |
EvalLambda: "\<rho> \<turnstile>\<^sub>e Lambda args e \<Rightarrow> VClosure \<rho> args e"

inductive_cases VarE: "\<rho> \<turnstile>\<^sub>e Var x \<Rightarrow> v"
inductive_cases LitE: "\<rho> \<turnstile>\<^sub>e Literal l \<Rightarrow> v" 
inductive_cases BinOpE: "\<rho> \<turnstile>\<^sub>e BinOp op e1 e2 \<Rightarrow> v"
inductive_cases UnOpE: "\<rho> \<turnstile>\<^sub>e UnOp op e \<Rightarrow> v" 
inductive_cases CondExprE: "\<rho> \<turnstile>\<^sub>e CondExpr e1 e2 e3 \<Rightarrow> v"
inductive_cases ListE: "\<rho> \<turnstile>\<^sub>e List es \<Rightarrow> v"
inductive_cases TupleE: "\<rho> \<turnstile>\<^sub>e Tuple es \<Rightarrow> v"
inductive_cases LambdaE: "\<rho> \<turnstile>\<^sub>e Lambda args e \<Rightarrow> v"

lemma list_all2_deterministic:
  assumes
    "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vs1"
    "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vs2"
    "\<And>e v1 v2.
       e \<in> set es \<Longrightarrow>
       \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v1 \<Longrightarrow>
       \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v2 \<Longrightarrow>
       v1 = v2"
  shows
    "vs1 = vs2"
using assms
apply (induction arbitrary: vs2 rule: list_all2_induct)
  apply blast
 apply (metis list.set_intros(1,2) list_all2_Cons1)
done

lemma expr_eval_deterministic:
    "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v1 ; \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v2 \<rbrakk> \<Longrightarrow> v1 = v2"
apply (induction e arbitrary: \<rho> v1 v2)
        apply (erule VarE, erule VarE, simp)
       apply (erule LitE, erule LitE, simp)
      apply (erule BinOpE, erule BinOpE, force)
     apply (erule UnOpE, erule UnOpE, force)
    apply (erule CondExprE, erule CondExprE)
      using CondExprE apply blast+
   apply (erule ListE, erule ListE, blast intro: list_all2_deterministic)
  apply (erule TupleE, erule TupleE, blast intro: list_all2_deterministic)
 apply (erule LambdaE, erule LambdaE, simp)
done

end