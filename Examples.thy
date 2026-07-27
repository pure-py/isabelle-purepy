theory Examples
    imports Semantics
begin

definition ex_add :: expr
where "ex_add = BinOp Add (Literal (Number 10)) (Literal (Number 20))"

lemma ex_add_eval:
    "\<epsilon> \<turnstile>\<^sub>e ex_add \<Rightarrow> VLit (Number 30)"
apply (simp add: ex_add_def)
apply (rule EvalBinOp EvalLit)+
by (simp add: binop_eval_def)

definition ex_lambda :: expr
where "ex_lambda = 
    Call 
        (Lambda [''x''] (BinOp Add (Var ''x'') (Literal (Number 1))))
        [ Literal (Number 2) ]"

lemma ex_lambda_eval:
    "\<epsilon> \<turnstile>\<^sub>e ex_lambda \<Rightarrow> VLit (Number 3)"
apply (simp add: ex_lambda_def)
apply (rule EvalCallLambda EvalLambda)
apply (auto intro: eval_expr_eval_block_eval_stmt_eval_elif.intros)
apply (rule EvalBinOp)
apply (auto intro: eval_expr_eval_block_eval_stmt_eval_elif.EvalLit)
apply (rule EvalVar)
apply simp
by (simp add: binop_eval_def)


(*
def even(x):
    if x = 0: 
        return True
    else: 
        return (odd (x - 1))
*)
definition func_even :: func
where "func_even = DefFunc ''even'' [''x''] [
    If (BinOp Eq (Var ''x'') (Literal (Number 0)))
        [Return (Literal (Bool True))]
        []
        (Some [
            Return 
                (Call (Var ''odd'')
                    [BinOp Sub (Var ''x'') (Literal (Number 1))])
        ])
]"

(*
def odd(x):
    if x = 0: 
        return False
    else: 
        return (even (x - 1))
*)
definition func_odd :: func
where "func_odd = DefFunc ''odd'' [''x''] [
    If (BinOp Eq (Var ''x'') (Literal (Number 0)))
        [Return (Literal (Bool False))]
        []
        (Some [
            Return 
                (Call (Var ''even'')
                    [BinOp Sub (Var ''x'') (Literal (Number 1))])
        ])
]"

definition ex_even_odd :: block
where "ex_even_odd = [
    MutualRegion [func_even , func_odd],
    Assign ''it'' (Call (Var ''even'') [Literal (Number 10)])
]"

thm ex_even_odd_def

lemma ex_even_odd_eval:
    "\<epsilon> \<turnstile>\<^sub>b ex_even_odd \<Rightarrow> Assigns \<sigma>' \<Longrightarrow> \<sigma>' ''it'' = Some (VLit (Bool True))"
apply (simp only: ex_even_odd_def)
apply (erule eval_block.cases)
apply (erule eval_block.cases)
apply (simp add: func_even_def func_odd_def)
using eval_block.cases by blast

lemma ex_even_odd_eval':
    "\<epsilon> \<turnstile>\<^sub>b ex_even_odd \<Rightarrow> Assigns \<sigma>' \<Longrightarrow> \<sigma>' ''it'' = Some (VLit (Bool False))"
apply (simp only: ex_even_odd_def)
apply (erule eval_block.cases)
apply (erule eval_block.cases)
apply (simp add: func_even_def func_odd_def)
using eval_block.cases by blast

end