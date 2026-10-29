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

(* A definition in the evaluation locale has no code equation of its own *)
declare evaluation.field_map_def [code]

(* Natural numbers are target integers, so the evaluator's equations can't match the fuel against 0 and Suc. One
   equation per function tests the fuel; the equations for positive fuel are stated for a step function. *)
definition run_expr_step where "run_expr_step \<Sigma> n = evaluation.run_expr \<Sigma> (Suc n)"
definition run_exprs_step where "run_exprs_step \<Sigma> n = evaluation.run_exprs \<Sigma> (Suc n)"
definition run_stmt_step where "run_stmt_step \<Sigma> n = evaluation.run_stmt \<Sigma> (Suc n)"
definition run_elif_step where "run_elif_step \<Sigma> n = evaluation.run_elif \<Sigma> (Suc n)"
definition run_quals_step where "run_quals_step \<Sigma> n = evaluation.run_quals \<Sigma> (Suc n)"
definition run_gen_step where "run_gen_step \<Sigma> n = evaluation.run_gen \<Sigma> (Suc n)"
definition run_comp_step where "run_comp_step \<Sigma> n = evaluation.run_comp \<Sigma> (Suc n)"
definition run_entries_step where "run_entries_step \<Sigma> n = evaluation.run_entries \<Sigma> (Suc n)"
lemmas run_steps_def = run_expr_step_def run_exprs_step_def run_stmt_step_def run_elif_step_def
  run_quals_step_def run_gen_step_def run_comp_step_def run_entries_step_def

lemma run_fuel_code [code]:
  "evaluation.run_expr \<Sigma> n \<rho> e = (if n = 0 then OutOfFuel else run_expr_step \<Sigma> (n - 1) \<rho> e)"
  "evaluation.run_exprs \<Sigma> n \<rho> es = (if n = 0 then OutOfFuel else run_exprs_step \<Sigma> (n - 1) \<rho> es)"
  "evaluation.run_stmt \<Sigma> n \<rho> s = (if n = 0 then OutOfFuel else run_stmt_step \<Sigma> (n - 1) \<rho> s)"
  "evaluation.run_elif \<Sigma> n \<rho> eb = (if n = 0 then OutOfFuel else run_elif_step \<Sigma> (n - 1) \<rho> eb)"
  "evaluation.run_quals \<Sigma> n \<rho> gs = (if n = 0 then OutOfFuel else run_quals_step \<Sigma> (n - 1) \<rho> gs)"
  "evaluation.run_gen \<Sigma> n \<rho> x us gs = (if n = 0 then OutOfFuel else run_gen_step \<Sigma> (n - 1) \<rho> x us gs)"
  "evaluation.run_comp \<Sigma> n \<rho>s e = (if n = 0 then OutOfFuel else run_comp_step \<Sigma> (n - 1) \<rho>s e)"
  "evaluation.run_entries \<Sigma> n \<rho>s e e' = (if n = 0 then OutOfFuel else run_entries_step \<Sigma> (n - 1) \<rho>s e e')"
  by (cases n; simp only: run_steps_def evaluation.run_expr.simps(1) evaluation.run_exprs.simps(1)
    evaluation.run_stmt.simps(1) evaluation.run_elif.simps(1) evaluation.run_quals.simps(1)
    evaluation.run_gen.simps(1) evaluation.run_comp.simps(1) evaluation.run_entries.simps(1)
    simp_thms if_True if_False nat.distinct(2) diff_Suc_1)+

lemmas run_step_code [code] =
  evaluation.run_expr.simps(2-)[folded run_steps_def] evaluation.run_exprs.simps(2-)[folded run_steps_def]
  evaluation.run_stmt.simps(2-)[folded run_steps_def] evaluation.run_elif.simps(2-)[folded run_steps_def]
  evaluation.run_quals.simps(2-)[folded run_steps_def] evaluation.run_gen.simps(2-)[folded run_steps_def]
  evaluation.run_comp.simps(2-)[folded run_steps_def] evaluation.run_entries.simps(2-)[folded run_steps_def]

export_code check_program evaluation.run_expr evaluation.run_stmt
  in Python file_prefix "."

end
