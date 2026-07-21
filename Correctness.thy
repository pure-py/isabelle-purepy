theory Correctness
    imports Eval
begin

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
done

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
    apply (smt (verit, best) CondExprE literal.distinct(1,5) literal.inject(2) option.inject val.distinct(1,3,5) val.inject(1))
   apply (simp add: EvalList)
   apply (metis ListE eval_exprs_complete_aux option.case_eq_if option.distinct(1) option.sel)
  apply (metis (lifting) TupleE eval_expr.simps(7) eval_exprs_complete_aux option.case_eq_if option.distinct(1) option.sel)
 apply (metis LambdaE eval_expr.simps(8))
done

theorem expr_eval_correct:
    "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<longleftrightarrow> eval_expr \<rho> e = Some v"
by (metis eval_expr_sound eval_expr_complete)

end