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
    | VDict \<delta> \<Rightarrow> (case v of VLit (LitString w) \<Rightarrow> Val (w \<in> set (map fst \<delta>)) | _ \<Rightarrow> Aborts Excluded)
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

fun flet_outcome :: "'a result fuelled \<Rightarrow> ('a \<Rightarrow> outcome fuelled) \<Rightarrow> outcome fuelled"
where
"flet_outcome (Done (Val v)) f = f v" |
"flet_outcome (Done (Aborts \<kappa>)) f = Done (Aborts\<^sub>o \<kappa>)" |
"flet_outcome Stuck f = Stuck" |
"flet_outcome OutOfFuel f = OutOfFuel"

(* Sequential composition: run f on the environment of an Assigns, and compose the outcomes *)
fun fseq :: "outcome fuelled \<Rightarrow> (env \<Rightarrow> outcome fuelled) \<Rightarrow> outcome fuelled"
where
"fseq (Done (Assigns \<rho>')) f = map_fuelled (\<lambda>o. Assigns \<rho>' \<otimes>\<^sub>o o) (f \<rho>')" |
"fseq (Done o) f = Done o" |
"fseq Stuck f = Stuck" |
"fseq OutOfFuel f = OutOfFuel"

function (sequential)
  eval_expr  :: "nat \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> val result fuelled" and
  eval_exprs :: "nat \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> val list result fuelled" and
  eval_stmt  :: "nat \<Rightarrow> env \<Rightarrow> stmt \<Rightarrow> outcome fuelled" and
  eval_elif  :: "nat \<Rightarrow> env \<Rightarrow> elif_block \<Rightarrow> outcome fuelled" and
  eval_quals :: "nat \<Rightarrow> env \<Rightarrow> qualifier list \<Rightarrow> env list result fuelled" and
  eval_gen   :: "nat \<Rightarrow> env \<Rightarrow> var \<Rightarrow> val list \<Rightarrow> qualifier list \<Rightarrow> env list result fuelled" and
  eval_comp  :: "nat \<Rightarrow> env list \<Rightarrow> expr \<Rightarrow> val list result fuelled" and
  eval_entries :: "nat \<Rightarrow> env list \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> (string \<times> val) list result fuelled"
where
"eval_expr 0 \<rho> e = OutOfFuel" |
"eval_expr (Suc n) \<rho> (ExprVar x) = 
  (case fmlookup \<rho> x of
    Some VUnbound \<Rightarrow> Done (Aborts NameError)
  | Some v \<Rightarrow> Done (Val v)
  | None \<Rightarrow> Done (Aborts NameError))" |
"eval_expr (Suc n) \<rho> (ExprLiteral l) = Done (Val (VLit l))" |
"eval_expr (Suc n) \<rho> (ExprLambda xs e) = Done (Val Lam(\<rho>, xs, e))" |
"eval_expr (Suc n) \<rho> (ExprUnOp op e) = flet (eval_expr n \<rho> e) (\<lambda>v. Done (unop_meaning op v))" |
"eval_expr (Suc n) \<rho> (ExprBinOp op e e') =
  flet (eval_expr n \<rho> e) (\<lambda>v. flet (eval_expr n \<rho> e') (\<lambda>v'. Done (binop_meaning op v v')))" |
"eval_expr (Suc n) \<rho> (ExprAnd e e') =
  flet (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some False \<Rightarrow> Done (Val false)
  | Some True \<Rightarrow> eval_expr n \<rho> e'
  | None \<Rightarrow> Done (Aborts Excluded))" |
"eval_expr (Suc n) \<rho> (ExprOr e e') =
  flet (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Val true)
  | Some False \<Rightarrow> eval_expr n \<rho> e'
  | None \<Rightarrow> Done (Aborts Excluded))" |
"eval_expr (Suc n) \<rho> (ExprCond e1 e e2) =
  flet (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> eval_expr n \<rho> e1
  | Some False \<Rightarrow> eval_expr n \<rho> e2
  | None \<Rightarrow> Done (Aborts Excluded))" |
"eval_expr (Suc n) \<rho> (ExprList es) = flet (eval_exprs n \<rho> es) (\<lambda>vs. Done (Val (VList vs)))" |
"eval_expr (Suc n) \<rho> (ExprTuple es) = flet (eval_exprs n \<rho> es) (\<lambda>vs. Done (Val (VTuple vs)))" |
"eval_expr (Suc n) \<rho> (ExprDict kes) =
  flet (eval_exprs n \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes))) (\<lambda>vs. case dict_entries vs of
    Some \<delta> \<Rightarrow> Done (Val (VDict (update [] \<delta>)))
  | None \<Rightarrow> Done (Aborts Excluded))" |
"eval_expr (Suc n) \<rho> (ExprListComp e gs) =
  flet (eval_quals n \<rho> gs) (\<lambda>\<rho>s. flet (eval_comp n \<rho>s e) (\<lambda>vs. Done (Val (VList vs))))" |
"eval_expr (Suc n) \<rho> (ExprDictComp e e' gs) =
  flet (eval_quals n \<rho> gs) (\<lambda>\<rho>s. flet (eval_entries n \<rho>s e e') (\<lambda>\<delta>. Done (Val (VDict (update [] \<delta>)))))" |
"eval_expr (Suc n) \<rho> (ExprSubscript e e') =
  flet (eval_expr n \<rho> e) (\<lambda>v. flet (eval_expr n \<rho> e') (\<lambda>v'. Done (getitem v v')))" |
"eval_expr (Suc n) \<rho> (ExprCall e (es, [])) =
  flet (eval_expr n \<rho> e) (\<lambda>v. flet (eval_exprs n \<rho> es) (\<lambda>us. case v of
    Lam(\<rho>', xs, e') \<Rightarrow>
      if length xs = length us then eval_expr n (\<rho>' \<otimes> fmap_of_list (zip xs us)) e' else Done (Aborts TypeError)
  | Def(\<rho>', ds, j) \<Rightarrow>
      if j < length ds then
        (case ds ! j of Def f \<alpha>s xps \<psi> s \<Rightarrow>
          if length xps = length us then
            (case scope VUnbound (map fst xps) s of
              Some \<rho>s \<Rightarrow>
                map_fuelled call_result
                  (eval_stmt n
                    (\<rho>' \<otimes> fmap_of_list (zip (map def_name ds) (map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds]))
                       \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s) s)
            | None \<Rightarrow> Stuck)
          else Done (Aborts TypeError))
      else Stuck
  | _ \<Rightarrow> Done (Aborts TypeError)))" |
"eval_expr (Suc n) \<rho> _ = Stuck" |

"eval_exprs 0 \<rho> es = OutOfFuel" |
"eval_exprs (Suc n) \<rho> [] = Done (Val [])" |
"eval_exprs (Suc n) \<rho> (e # es) =
  flet (eval_expr n \<rho> e) (\<lambda>v. flet (eval_exprs n \<rho> es) (\<lambda>vs. Done (Val (v # vs))))" |

"eval_stmt 0 \<rho> s = OutOfFuel" |
"eval_stmt (Suc n) \<rho> StmtPass = Done (Assigns \<epsilon>)" |
"eval_stmt (Suc n) \<rho> (StmtDeclare x \<psi>) = Done (Assigns \<epsilon>)" |
"eval_stmt (Suc n) \<rho> (StmtAssign x \<pi> e) = flet_outcome (eval_expr n \<rho> e) (\<lambda>v. Done (Assigns (fmupd x v \<epsilon>)))" |
"eval_stmt (Suc n) \<rho> (StmtExpr e) = flet_outcome (eval_expr n \<rho> e) (\<lambda>v. Done (Assigns \<epsilon>))" |
"eval_stmt (Suc n) \<rho> (StmtReturn (Some e)) = flet_outcome (eval_expr n \<rho> e) (\<lambda>v. Done (Returns v))" |
"eval_stmt (Suc n) \<rho> (StmtReturn None) = Done (Returns (VLit LitNone))" |
"eval_stmt (Suc n) \<rho> (StmtMutualRegion ds) =
  Done (Assigns (fmap_of_list (zip (map def_name ds) (map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]))))" |
"eval_stmt (Suc n) \<rho> (StmtAssert e None) =
  flet_outcome (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Assigns \<epsilon>)
  | Some False \<Rightarrow> Done (Aborts\<^sub>o (AssertionError None))
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |
"eval_stmt (Suc n) \<rho> (StmtAssert e (Some e')) =
  flet_outcome (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Assigns \<epsilon>)
  | Some False \<Rightarrow>
      flet_outcome (eval_expr n \<rho> e') (\<lambda>v'. case v' of
        VLit (LitString w) \<Rightarrow> Done (Aborts\<^sub>o (AssertionError (Some w)))
      | _ \<Rightarrow> Done (Aborts\<^sub>o Excluded))
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |
"eval_stmt (Suc n) \<rho> (StmtIf e s elifs else') =
  flet_outcome (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> eval_stmt n \<rho> s
  | Some False \<Rightarrow> eval_elif n \<rho> (elifs, else')
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |
"eval_stmt (Suc n) \<rho> (StmtSeq s s') = fseq (eval_stmt n \<rho> s) (\<lambda>\<rho>'. eval_stmt n (\<rho> \<otimes> \<rho>') s')" |
"eval_stmt (Suc n) \<rho> (StmtMatch e cases) =
  flet_outcome (eval_expr n \<rho> e) (\<lambda>v. case dispatch \<rho> v cases of
    Val (\<rho>', s') \<Rightarrow> map_fuelled (\<lambda>o. Assigns \<rho>' \<otimes>\<^sub>o o) (eval_stmt n (\<rho> \<otimes> \<rho>') s')
  | Aborts \<kappa> \<Rightarrow> Done (Aborts\<^sub>o \<kappa>))" |

"eval_elif 0 \<rho> eb = OutOfFuel" |
"eval_elif (Suc n) \<rho> ([], None) = Done (Assigns \<epsilon>)" |
"eval_elif (Suc n) \<rho> ([], Some s) = eval_stmt n \<rho> s" |
"eval_elif (Suc n) \<rho> ((e, s) # elifs, else') =
  flet_outcome (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> eval_stmt n \<rho> s
  | Some False \<Rightarrow> eval_elif n \<rho> (elifs, else')
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |

"eval_quals 0 \<rho> gs = OutOfFuel" |
"eval_quals (Suc n) \<rho> [] = Done (Val [\<rho>])" |
"eval_quals (Suc n) \<rho> (Guard e # gs) =
  flet (eval_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> eval_quals n \<rho> gs
  | Some False \<Rightarrow> Done (Val [])
  | None \<Rightarrow> Done (Aborts Excluded))" |
"eval_quals (Suc n) \<rho> (Generator x e # gs) =
  flet (eval_expr n \<rho> e) (\<lambda>v. case iter v of
    Some us \<Rightarrow> eval_gen n \<rho> x us gs
  | None \<Rightarrow> Done (Aborts TypeError))" |

"eval_gen 0 \<rho> x us gs = OutOfFuel" |
"eval_gen (Suc n) \<rho> x [] gs = Done (Val [])" |
"eval_gen (Suc n) \<rho> x (u # us) gs =
  flet (eval_quals n (fmupd x u \<rho>) gs) (\<lambda>\<rho>s. flet (eval_gen n \<rho> x us gs) (\<lambda>\<rho>ss. Done (Val (\<rho>s @ \<rho>ss))))" |

"eval_comp 0 \<rho>s e = OutOfFuel" |
"eval_comp (Suc n) [] e = Done (Val [])" |
"eval_comp (Suc n) (\<rho> # \<rho>s) e =
  flet (eval_expr n \<rho> e) (\<lambda>v. flet (eval_comp n \<rho>s e) (\<lambda>vs. Done (Val (v # vs))))" |

"eval_entries 0 \<rho>s e e' = OutOfFuel" |
"eval_entries (Suc n) [] e e' = Done (Val [])" |
"eval_entries (Suc n) (\<rho> # \<rho>s) e e' =
  flet (eval_expr n \<rho> e) (\<lambda>k. case k of
    VLit (LitString w) \<Rightarrow>
      flet (eval_expr n \<rho> e') (\<lambda>v. flet (eval_entries n \<rho>s e e') (\<lambda>\<delta>. Done (Val ((w, v) # \<delta>))))
  | _ \<Rightarrow> Done (Aborts Excluded))"
by pat_completeness auto

(* Every call decreases the fuel, the first argument of each function *)
termination
  by (relation "measure (case_sum (case_sum (case_sum fst fst) (case_sum fst fst))
                                  (case_sum (case_sum fst fst) (case_sum fst fst)))") auto

lemmas eval_fun_induct =
  eval_expr_eval_exprs_eval_stmt_eval_elif_eval_quals_eval_gen_eval_comp_eval_entries.induct

end
