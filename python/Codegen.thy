(* Operator resolution and subtyping in executable form; Python generation *)
theory Codegen
  imports "isabelle-purepy.Programs" "isabelle-purepy.Eval" "Python.Python_Setup"
begin

(* Floats as Python's float. Equality of representations, since HOL equality is reflexive; Python's == is given
   by the semantics *)
code_printing
    type_constructor float \<rightharpoonup> (Python) "float"
  | constant "HOL.equal :: float \<Rightarrow> float \<Rightarrow> bool" \<rightharpoonup> (Python) "(repr'(_') == repr'(_'))"

(* Strings as Python's str *)
code_printing
    type_constructor str \<rightharpoonup> (Python) "str"
  | constant "HOL.equal :: str \<Rightarrow> str \<Rightarrow> bool" \<rightharpoonup> (Python) "(_ == _)"
  | constant "(\<le>) :: str \<Rightarrow> str \<Rightarrow> bool" \<rightharpoonup> (Python) "(_ <= _)"
  | constant "(<) :: str \<Rightarrow> str \<Rightarrow> bool" \<rightharpoonup> (Python) "(_ < _)"
  | constant substring \<rightharpoonup> (Python) "(_ in _)"

(* Identifiers as Python's str *)
code_printing
    type_constructor var \<rightharpoonup> (Python) "str"
  | constant "HOL.equal :: var \<Rightarrow> var \<Rightarrow> bool" \<rightharpoonup> (Python) "(_ == _)"
  | constant "(\<le>) :: var \<Rightarrow> var \<Rightarrow> bool" \<rightharpoonup> (Python) "(_ <= _)"
  | constant "(<) :: var \<Rightarrow> var \<Rightarrow> bool" \<rightharpoonup> (Python) "(_ < _)"
  | constant var \<rightharpoonup> (Python) "\"\".join'(_')"

(* The equations of the lifted string operations aren't executable, and their printings replace them *)
declare [[code drop: substring str_of str_chars str_append str_concat]]

(* Strings written in the theories, and the characters of a string *)
code_printing
    constant str_of \<rightharpoonup> (Python) "\"\".join'(_')"
  | constant str_chars \<rightharpoonup> (Python) "list'(_')"
  | constant str_append \<rightharpoonup> (Python) "(_ + _)"
  | constant str_concat \<rightharpoonup> (Python) "\"\".join'(_')"

(* Float arithmetic as Python's, and conversion between floats and extended reals through a helper module *)
code_printing
    constant float_neg \<rightharpoonup> (Python) "(- _)"
  | constant float_add \<rightharpoonup> (Python) "(_ + _)"
  | constant float_sub \<rightharpoonup> (Python) "(_ - _)"
  | constant float_mul \<rightharpoonup> (Python) "(_ * _)"
  | constant float_div \<rightharpoonup> (Python) "(_ '/ _)"
  | constant float_floordiv \<rightharpoonup> (Python) "(_ '/'/ _)"
  | constant float_mod \<rightharpoonup> (Python) "(_ % _)"
  | constant nan \<rightharpoonup> (Python) "float'(\"nan\"')"
  | constant negative \<rightharpoonup> (Python) "('_'_import'_'_'(\"math\"').copysign'(1.0, _') < 0)"
  | constant real_of_float \<rightharpoonup> (Python) "'_'_import'_'_'(\"Purepy'_Floats\"').real'_of'_float'(_')"
  | constant fl \<rightharpoonup> (Python) "'_'_import'_'_'(\"Purepy'_Floats\"').fl'(_')"
  | code_module "Purepy_Floats.py" \<rightharpoonup> (Python)
\<open>import fractions
import math
import Option
import Extended_Real
import Real
import Rat


def real_of_float(x):
    if math.isnan(x):
        return Option.None_()
    if math.isinf(x):
        return Option.Some(Extended_Real.PInfty() if x > 0 else Extended_Real.MInfty())
    return Option.Some(Extended_Real.ereal_(Real.Ratreal(Rat.Frct(x.as_integer_ratio()))))


def fl(y):
    if isinstance(y, Extended_Real.PInfty):
        return math.inf
    if isinstance(y, Extended_Real.MInfty):
        return -math.inf
    n, d = y.a.a.a
    try:
        return float(fractions.Fraction(n, d))
    except OverflowError:
        return math.inf if n > 0 else -math.inf
\<close>

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

(* A definition or function in the evaluation locale has no code equation of its own *)
declare evaluation.overload_def [code] evaluation.tuple_overload_def [code] evaluation.overloads.simps [code]
  evaluation.select.simps [code] evaluation.binop_meaning_def [code] evaluation.unop_meaning.simps [code]
  evaluation.field_map_def [code] evaluation.match.simps [code] evaluation.match_all.simps [code]
  evaluation.match_dict.simps [code] evaluation.match_kws.simps [code] evaluation.match_fields.simps [code]
  evaluation.dispatch.simps [code] evaluation.type_args_of_def [code] evaluation.type_value_def [code]
  evaluation.run_top.simps [code]

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
  "evaluation.run_comp \<Sigma> n \<rho>s ec = (if n = 0 then OutOfFuel else run_comp_step \<Sigma> (n - 1) \<rho>s ec)"
  "evaluation.run_entries \<Sigma> n \<rho>s ec ec' = (if n = 0 then OutOfFuel else run_entries_step \<Sigma> (n - 1) \<rho>s ec ec')"
  by (cases n; simp only: run_steps_def evaluation.run_expr.simps(1) evaluation.run_exprs.simps(1)
    evaluation.run_stmt.simps(1) evaluation.run_elif.simps(1) evaluation.run_quals.simps(1)
    evaluation.run_gen.simps(1) evaluation.run_comp.simps(1) evaluation.run_entries.simps(1)
    simp_thms if_True if_False nat.distinct(2) diff_Suc_1)+

lemmas run_step_code [code] =
  evaluation.run_expr.simps(2-)[folded run_steps_def] evaluation.run_exprs.simps(2-)[folded run_steps_def]
  evaluation.run_stmt.simps(2-)[folded run_steps_def] evaluation.run_elif.simps(2-)[folded run_steps_def]
  evaluation.run_quals.simps(2-)[folded run_steps_def] evaluation.run_gen.simps(2-)[folded run_steps_def]
  evaluation.run_comp.simps(2-)[folded run_steps_def] evaluation.run_entries.simps(2-)[folded run_steps_def]

(* The same for the order of loading, whose functions also take the program *)
declare loading.submods_env_def [code] loading.run_mod_def [code] loading.run_mods.simps [code]
  loading.run_program_def [code]

definition run_loads_step where "run_loads_step M n = loading.run_loads M (Suc n)"
definition run_submod_loads_step where "run_submod_loads_step M n = loading.run_submod_loads M (Suc n)"
definition run_imports_loads_step where "run_imports_loads_step M n = loading.run_imports_loads M (Suc n)"
definition run_import_loads_step where "run_import_loads_step M n = loading.run_import_loads M (Suc n)"
lemmas run_loads_steps_def =
  run_loads_step_def run_submod_loads_step_def run_imports_loads_step_def run_import_loads_step_def

lemma run_loads_fuel_code [code]:
  "loading.run_loads M n qs qs' = (if n = 0 then OutOfFuel else run_loads_step M (n - 1) qs qs')"
  "loading.run_submod_loads M n qs q xs = (if n = 0 then OutOfFuel else run_submod_loads_step M (n - 1) qs q xs)"
  "loading.run_imports_loads M n qs q \<iota>s = (if n = 0 then OutOfFuel else run_imports_loads_step M (n - 1) qs q \<iota>s)"
  "loading.run_import_loads M n qs q \<iota> = (if n = 0 then OutOfFuel else run_import_loads_step M (n - 1) qs q \<iota>)"
  by (cases n; simp only: run_loads_steps_def loading.run_loads.simps(1) loading.run_submod_loads.simps(1)
    loading.run_imports_loads.simps(1) loading.run_import_loads.simps(1)
    simp_thms if_True if_False nat.distinct(2) diff_Suc_1)+

lemmas run_loads_step_code [code] =
  loading.run_loads.simps(2-)[folded run_loads_steps_def]
  loading.run_submod_loads.simps(2-)[folded run_loads_steps_def]
  loading.run_imports_loads.simps(2-)[folded run_loads_steps_def]
  loading.run_import_loads.simps(2-)[folded run_loads_steps_def]

export_code check_program check_module predefined_classes main
  evaluation.run_expr evaluation.run_stmt evaluation.run_top loading.run_program
  in Python file_prefix "."

end
