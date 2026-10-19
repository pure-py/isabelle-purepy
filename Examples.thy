theory Examples
    imports Semantics
begin

definition ex_add :: expr
where "ex_add = ExprBinOp BOpAdd (ExprLiteral (LitInt 10)) (ExprLiteral (LitInt 20))"

lemma ex_add_eval: "\<epsilon>, ex_add \<Rightarrow>\<^sub>e Val (VLit (LitInt 30))"
proof -
  have "\<epsilon>, ex_add \<Rightarrow>\<^sub>e mlet (Val (VLit (LitInt 20))) (binop_meaning BOpAdd (VLit (LitInt 10)))"
    unfolding ex_add_def by (rule EvalBinOp[OF EvalLiteral EvalLiteral])
  then show ?thesis by simp
qed

definition ex_lambda :: expr
where "ex_lambda =
    ExprCall
        (ExprLambda [''x''] (ExprBinOp BOpAdd (ExprVar ''x'') (ExprLiteral (LitInt 1))))
        ([ExprLiteral (LitInt 2)], [])"

lemma ex_lambda_eval: "\<epsilon>, ex_lambda \<Rightarrow>\<^sub>e Val (VLit (LitInt 3))"
proof -
  have args: "\<epsilon>, [ExprLiteral (LitInt 2)] \<Rightarrow>\<^sub>e\<^sub>s Val [VLit (LitInt 2)]"
    using EvalExprsCons[OF EvalLiteral EvalExprsNil] by simp
  let ?\<rho> = "\<epsilon>([''x''] [\<mapsto>] [VLit (LitInt 2)])"
  have "?\<rho>, ExprVar ''x'' \<Rightarrow>\<^sub>e Val (VLit (LitInt 2))" by (rule EvalVar) simp
  then have "?\<rho>, ExprBinOp BOpAdd (ExprVar ''x'') (ExprLiteral (LitInt 1))
    \<Rightarrow>\<^sub>e mlet (Val (VLit (LitInt 1))) (binop_meaning BOpAdd (VLit (LitInt 2)))"
    by (rule EvalBinOp[OF _ EvalLiteral])
  then have body:
    "?\<rho>, ExprBinOp BOpAdd (ExprVar ''x'') (ExprLiteral (LitInt 1)) \<Rightarrow>\<^sub>e Val (VLit (LitInt 3))"
    by simp
  show ?thesis
    unfolding ex_lambda_def by (rule EvalCallLambda[OF EvalLambda args _ body]) simp
qed

end
