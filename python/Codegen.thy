(* Operator resolution and subtyping in executable form; Python generation *)
theory Codegen
  imports "isabelle-purepy.Programs" "isabelle-purepy.Eval" "Python.Python_Setup"
begin

code_pred subty .
code_pred binop_overload .
code_pred unop_overload .

(* Compute sets of overloads by the predicates compiled above, since their defining comprehensions can't be
   executed *)
lemma binop_overloads_code [code]:
  "binop_overloads \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 = set_of_pred (binop_overload_i_i_i_i_PPooo \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2)"
  by (auto simp: binop_overloads_def binop_overload_i_i_i_i_PPooo_def)

lemma unop_overloads_code [code]:
  "unop_overloads \<Sigma> op \<sigma> = set_of_pred (unop_overload_i_i_i_Poo \<Sigma> op \<sigma>)"
  by (auto simp: unop_overloads_def unop_overload_i_i_i_Poo_def)

(* Natural numbers are target integers, so the evaluator's equations can't match the fuel against 0 and Suc. One
   equation per function tests the fuel; the equations for positive fuel are stated for a step function. *)
definition eval_expr_step where "eval_expr_step n = eval_expr (Suc n)"
definition eval_exprs_step where "eval_exprs_step n = eval_exprs (Suc n)"
definition eval_stmt_step where "eval_stmt_step n = eval_stmt (Suc n)"
definition eval_elif_step where "eval_elif_step n = eval_elif (Suc n)"
definition eval_quals_step where "eval_quals_step n = eval_quals (Suc n)"
definition eval_gen_step where "eval_gen_step n = eval_gen (Suc n)"
definition eval_comp_step where "eval_comp_step n = eval_comp (Suc n)"
definition eval_entries_step where "eval_entries_step n = eval_entries (Suc n)"
lemmas eval_steps_def = eval_expr_step_def eval_exprs_step_def eval_stmt_step_def eval_elif_step_def
  eval_quals_step_def eval_gen_step_def eval_comp_step_def eval_entries_step_def

lemma eval_fuel_code [code]:
  "eval_expr n \<rho> e = (if n = 0 then OutOfFuel else eval_expr_step (n - 1) \<rho> e)"
  "eval_exprs n \<rho> es = (if n = 0 then OutOfFuel else eval_exprs_step (n - 1) \<rho> es)"
  "eval_stmt n \<rho> s = (if n = 0 then OutOfFuel else eval_stmt_step (n - 1) \<rho> s)"
  "eval_elif n \<rho> eb = (if n = 0 then OutOfFuel else eval_elif_step (n - 1) \<rho> eb)"
  "eval_quals n \<rho> gs = (if n = 0 then OutOfFuel else eval_quals_step (n - 1) \<rho> gs)"
  "eval_gen n \<rho> x us gs = (if n = 0 then OutOfFuel else eval_gen_step (n - 1) \<rho> x us gs)"
  "eval_comp n \<rho>s e = (if n = 0 then OutOfFuel else eval_comp_step (n - 1) \<rho>s e)"
  "eval_entries n \<rho>s e e' = (if n = 0 then OutOfFuel else eval_entries_step (n - 1) \<rho>s e e')"
  by (cases n; simp add: eval_steps_def)+

lemmas eval_step_code [code] =
  eval_expr.simps(2-)[folded eval_steps_def] eval_exprs.simps(2-)[folded eval_steps_def]
  eval_stmt.simps(2-)[folded eval_steps_def] eval_elif.simps(2-)[folded eval_steps_def]
  eval_quals.simps(2-)[folded eval_steps_def] eval_gen.simps(2-)[folded eval_steps_def]
  eval_comp.simps(2-)[folded eval_steps_def] eval_entries.simps(2-)[folded eval_steps_def]

export_code check_program eval_expr eval_stmt
  in Python file_prefix "."

end
