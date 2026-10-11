theory Examples
    imports Semantics
begin

definition ex_add :: expr
where "ex_add = ExprBinOp BOpAdd (ExprLiteral (LitNumber 10)) (ExprLiteral (LitNumber 20))"

lemma ex_add_eval:
    "\<epsilon> \<turnstile>\<^sub>e ex_add \<Rightarrow> VLit (LitNumber 30)"
apply (simp add: ex_add_def)
apply (rule EvalBinOp EvalLit)+
by (simp add: binop_eval_def)

definition ex_lambda :: expr
where "ex_lambda =
    ExprCall
        (ExprLambda [''x''] (ExprBinOp BOpAdd (ExprVar ''x'') (ExprLiteral (LitNumber 1))))
        [ ExprLiteral (LitNumber 2) ] []"

lemma ex_lambda_eval:
    "\<epsilon> \<turnstile>\<^sub>e ex_lambda \<Rightarrow> VLit (LitNumber 3)"
apply (simp add: ex_lambda_def)
apply (rule EvalCallLambda EvalLambda)
apply (auto intro: eval_expr_eval_stmt_eval_elif.intros)
apply (rule EvalBinOp)
apply (auto intro: eval_expr_eval_stmt_eval_elif.EvalLit)
apply (rule EvalVar)
apply simp
by (simp add: binop_eval_def)

(* even/odd example removed: needs sequencing semantics, dropped with the block judgement *)

end
