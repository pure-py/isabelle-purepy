theory Eval
    imports Semantics "HOL-Library.Sublist"
begin

(* Free o for outcomes again, after importing Sublist *)
no_notation (ASCII) comp (infixl \<open>o\<close> 55)

(* Stuck where no rule applies, OutOfFuel where the fuel runs out first *)
datatype 'a fuelled = Done 'a | Stuck | OutOfFuel

fun flet :: "'a result fuelled \<Rightarrow> ('a \<Rightarrow> 'b result fuelled) \<Rightarrow> 'b result fuelled"
where
"flet (Done (Val v)) f = f v" |
"flet (Done (Aborts \<kappa>)) f = Done (Aborts \<kappa>)" |
"flet Stuck f = Stuck" |
"flet OutOfFuel f = OutOfFuel"

(* Code equations by case on the comparison, since values have no executable equality *)
lemma eq_elems_code [code]:
  "eq_elems [] [] = Val True"
  "eq_elems (v # vs) (v' # vs') =
    (if length vs \<noteq> length vs' then Val False
     else case eq v v' of Val True \<Rightarrow> eq_elems vs vs' | r \<Rightarrow> r)"
  "eq_elems [] (v' # vs') = Val False"
  "eq_elems (v # vs) [] = Val False"
  by (auto split: result.split bool.split)

lemma contains_code [code]:
  "contains v' v =
    (case v' of
      VList vs \<Rightarrow> contains_elems vs v
    | VTuple vs \<Rightarrow> contains_elems vs v
    | VLit (LitString w') \<Rightarrow> (case v of VLit (LitString w) \<Rightarrow> Val (sublist w w') | _ \<Rightarrow> Aborts TypeError)
    | _ \<Rightarrow> Aborts TypeError)"
  by (cases v'; cases v; auto simp: sublist_def split: lit.split)

lemma contains_elems_code [code]:
  "contains_elems [] v = Val False"
  "contains_elems (v' # vs) v = (case eq v v' of Val False \<Rightarrow> contains_elems vs v | r \<Rightarrow> r)"
  by (auto split: result.split bool.split)

fun as_bool :: "val \<Rightarrow> bool option"
where
"as_bool (VLit (LitBool b)) = Some b" |
"as_bool _ = None"

(* Calls to defs are Stuck until statements are evaluated *)
fun
  eval_expr  :: "nat \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> val result fuelled" and
  eval_exprs :: "nat \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> val list result fuelled"
where
"eval_expr 0 \<rho> e = OutOfFuel" |
"eval_expr (Suc n) \<rho> (ExprVar x) = 
  (case \<rho> x of Some v \<Rightarrow> Done (Val v) | None \<Rightarrow> Done (Aborts (NameError x)))" |
"eval_expr (Suc n) \<rho> (ExprLiteral l) = Done (Val (VLit l))" |
"eval_expr (Suc n) \<rho> (ExprLambda xs e) = Done (Val Lam(\<rho>, xs, e))" |
"eval_expr (Suc n) \<rho> (ExprUnOp op e) = flet (eval_expr n \<rho> e) (\<lambda>v. Done (unop_meaning op v))" |
"eval_expr (Suc n) \<rho> (ExprBinOp op e e') =
  flet (eval_expr n \<rho> e) (\<lambda>v. flet (eval_expr n \<rho> e') (\<lambda>v'. Done (binop_meaning op v v')))" |
"eval_expr (Suc n) \<rho> (ExprAnd e e') =
  flet (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some False \<Rightarrow> Done (Val false)
  | Some True \<Rightarrow> eval_expr n \<rho> e'
  | None \<Rightarrow> Done (Aborts TypeError))" |
"eval_expr (Suc n) \<rho> (ExprOr e e') =
  flet (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Val true)
  | Some False \<Rightarrow> eval_expr n \<rho> e'
  | None \<Rightarrow> Done (Aborts TypeError))" |
"eval_expr (Suc n) \<rho> (ExprCond e1 e e2) =
  flet (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> eval_expr n \<rho> e1
  | Some False \<Rightarrow> eval_expr n \<rho> e2
  | None \<Rightarrow> Done (Aborts TypeError))" |
"eval_expr (Suc n) \<rho> (ExprList es) = flet (eval_exprs n \<rho> es) (\<lambda>vs. Done (Val (VList vs)))" |
"eval_expr (Suc n) \<rho> (ExprTuple es) = flet (eval_exprs n \<rho> es) (\<lambda>vs. Done (Val (VTuple vs)))" |
"eval_expr (Suc n) \<rho> (ExprCall e (es, [])) =
  flet (eval_expr n \<rho> e) (\<lambda>v. flet (eval_exprs n \<rho> es) (\<lambda>us. case v of
    Lam(\<rho>', xs, e') \<Rightarrow>
      if length xs = length us then eval_expr n (\<rho>'(xs [\<mapsto>] us)) e' else Done (Aborts TypeError)
  | Def(\<rho>', ds, j) \<Rightarrow>
      if j < length ds then
        (case ds ! j of Def f \<alpha>s xps \<psi> s \<Rightarrow>
          if length xps = length us then Stuck
          else Done (Aborts TypeError))
      else Stuck
  | _ \<Rightarrow> Done (Aborts TypeError)))" |
"eval_expr (Suc n) \<rho> _ = Stuck" |

"eval_exprs 0 \<rho> es = OutOfFuel" |
"eval_exprs (Suc n) \<rho> [] = Done (Val [])" |
"eval_exprs (Suc n) \<rho> (e # es) =
  flet (eval_expr n \<rho> e) (\<lambda>v. flet (eval_exprs n \<rho> es) (\<lambda>vs. Done (Val (v # vs))))"

end
