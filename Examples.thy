theory Examples
    imports Semantics
begin

definition ex_add :: expr
where "ex_add = ExprBinOp BOpAdd (ExprLiteral (LitNumber 10)) (ExprLiteral (LitNumber 20))"

lemma ex_add_eval: "\<epsilon>, ex_add \<Rightarrow>\<^sub>e Val (VLit (LitNumber 30))"
proof -
  have "\<epsilon>, ex_add \<Rightarrow>\<^sub>e mlet (Val (VLit (LitNumber 20))) (binop_meaning BOpAdd (VLit (LitNumber 10)))"
    unfolding ex_add_def by (rule EvalBinOp[OF EvalLiteral EvalLiteral])
  then show ?thesis by simp
qed

definition ex_lambda :: expr
where "ex_lambda =
    ExprCall
        (ExprLambda [''x''] (ExprBinOp BOpAdd (ExprVar ''x'') (ExprLiteral (LitNumber 1))))
        ([ExprLiteral (LitNumber 2)], [])"

lemma ex_lambda_eval: "\<epsilon>, ex_lambda \<Rightarrow>\<^sub>e Val (VLit (LitNumber 3))"
proof -
  have args: "\<epsilon>, [ExprLiteral (LitNumber 2)] \<Rightarrow>\<^sub>e\<^sub>s Val [VLit (LitNumber 2)]"
    using EvalExprsCons[OF EvalLiteral EvalExprsNil] by simp
  let ?\<rho> = "\<epsilon>([''x''] [\<mapsto>] [VLit (LitNumber 2)])"
  have "?\<rho>, ExprVar ''x'' \<Rightarrow>\<^sub>e Val (VLit (LitNumber 2))" by (rule EvalVar) simp
  then have "?\<rho>, ExprBinOp BOpAdd (ExprVar ''x'') (ExprLiteral (LitNumber 1))
    \<Rightarrow>\<^sub>e mlet (Val (VLit (LitNumber 1))) (binop_meaning BOpAdd (VLit (LitNumber 2)))"
    by (rule EvalBinOp[OF _ EvalLiteral])
  then have body:
    "?\<rho>, ExprBinOp BOpAdd (ExprVar ''x'') (ExprLiteral (LitNumber 1)) \<Rightarrow>\<^sub>e Val (VLit (LitNumber 3))"
    by simp
  show ?thesis
    unfolding ex_lambda_def by (rule EvalCallLambda[OF EvalLambda args _ body]) simp
qed


end
