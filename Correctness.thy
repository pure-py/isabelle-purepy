theory Correctness
    imports Eval
begin

inductive_cases VarE: "\<rho> \<turnstile>\<^sub>e Var x \<Rightarrow> v"
inductive_cases LitE: "\<rho> \<turnstile>\<^sub>e Literal l \<Rightarrow> v"
inductive_cases BinOpE: "\<rho> \<turnstile>\<^sub>e BinOp op e1 e2 \<Rightarrow> v"
inductive_cases UnOpE: "\<rho> \<turnstile>\<^sub>e UnOp op e \<Rightarrow> v"
inductive_cases CondExprE: "\<rho> \<turnstile>\<^sub>e CondExpr e1 e2 e3 \<Rightarrow> v"
inductive_cases ListE: "\<rho> \<turnstile>\<^sub>e List es \<Rightarrow> v"
inductive_cases TupleE: "\<rho> \<turnstile>\<^sub>e Tuple es \<Rightarrow> v"
inductive_cases LambdaE: "\<rho> \<turnstile>\<^sub>e Lambda args e \<Rightarrow> v"
inductive_cases CallE: "\<rho> \<turnstile>\<^sub>e Call f args \<Rightarrow> v"

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

lemma determinism:
  "\<lbrakk> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v1 ; \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v2 \<rbrakk> \<Longrightarrow> v1 = v2"
proof (induction e arbitrary: \<rho> v1 v2)
  case (Var x)
  then show ?case
  by (metis option.inject VarE)
next
  case (Literal x)
  then show ?case
  by (metis LitE)
next
  case (BinOp x1a e1 e2)
  then show ?case
  by (metis option.inject BinOpE)
next
  case (UnOp x1a e)
  then show ?case
  by (metis option.inject UnOpE)
next
  case (CondExpr e1 e2 e3)
  then show ?case
  by (metis (full_types) CondExprE literal.inject(2) val.inject(1))
next
  case (List x)
  then show ?case
  by (metis ListE list_all2_deterministic)
next
  case (Tuple x)
  then show ?case
  by (metis TupleE list_all2_deterministic)
next
  case (Lambda x1a e)
  then show ?case
  by (metis LambdaE)
next
  case (Call e x2a)
  then show ?case
  sorry
qed

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
apply (erule CallE, erule CallE)
try
oops

lemma eval_exprs_list_all2:
  "eval_exprs \<rho> es = Some vs \<Longrightarrow> list_all2 (\<lambda>e v. eval_expr \<rho> e = Some v) es vs"
proof (induction es arbitrary: vs)
  case Nil
  then show ?case by simp
next
  case (Cons e es)
  then show ?case
    by (auto split: option.splits)
qed

lemma eval_expr_sound:
    "eval_expr \<rho> e = Some v \<Longrightarrow> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v"
apply (induction e arbitrary: \<rho> v)
apply (simp add: EvalVar)
apply (simp add: EvalLit)
apply (simp add: EvalBinOp)
apply (metis (no_types, lifting) EvalBinOp not_Some_eq option.simps(4,5))
apply (simp add: EvalUnOp)
apply (metis EvalUnOp is_none_code(2) option.case_eq_if option.distinct(1) option.split_sel_asm)
apply (simp split: option.splits val.splits literal.splits bool.splits)
apply safe
apply (rule EvalCondExprTrue, blast, blast)
apply (rule EvalCondExprFalse, blast, blast)
apply (simp add: EvalList)
apply (smt (verit, ccfv_threshold) EvalList eval_exprs_list_all2 is_none_code(2) list.rel_mono_strong option.case_eq_if option.distinct(1) option.sel option.split_sel_asm)
apply (simp add: EvalTuple)
apply (smt (verit, ccfv_threshold) EvalTuple eval_exprs_list_all2 is_none_code(2) list.rel_mono_strong option.case_eq_if option.distinct(1) option.sel option.split_sel_asm)
apply (metis option.inject eval_expr.simps(8) EvalLambda)
sorry

lemma eval_exprs_complete_aux:
  "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vs \<Longrightarrow>
   (\<And>e v. e \<in> set es \<Longrightarrow> \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<Longrightarrow> eval_expr \<rho> e = Some v) \<Longrightarrow>
   eval_exprs \<rho> es = Some vs"
apply (induction es arbitrary: vs)
 apply simp
 using list.rel_cases 
 apply force
done

lemma eval_expr_complete:
    "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<Longrightarrow> eval_expr \<rho> e = Some v"
apply (induction e arbitrary: \<rho> v)
        apply (metis eval_expr.simps(1) VarE)
       apply (metis LitE eval_expr.simps(2))
      apply (metis (no_types, lifting) BinOpE eval_expr.simps(3) option.simps(5))
     apply (metis UnOpE eval_expr.simps(4) option.simps(5))
    apply (simp split: option.splits val.splits literal.splits bool.splits)
    (* apply (smt (verit, best) CondExprE literal.distinct(1,5) literal.inject(2) option.inject val.distinct(1,3,5) val.inject(1))
   apply (simp add: EvalList)
   apply (metis ListE eval_exprs_complete_aux option.case_eq_if option.distinct(1) option.sel)
  apply (metis (lifting) TupleE eval_expr.simps(7) eval_exprs_complete_aux option.case_eq_if option.distinct(1) option.sel)
 apply (metis LambdaE eval_expr.simps(8)) *)
sorry

theorem expr_eval_correct:
    "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<longleftrightarrow> eval_expr \<rho> e = Some v"
by (metis eval_expr_sound eval_expr_complete)

end