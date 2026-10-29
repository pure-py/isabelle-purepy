(* Evaluation as a function with fuel, and its executable code equations *)
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

(* The continuation runs only on the value computed, so recursive calls inside it know that value *)
lemma flet_cong [fundef_cong]:
  assumes "m = m'" "\<And>v. m' = Done (Val v) \<Longrightarrow> f v = f' v"
  shows "flet m f = flet m' f'"
proof (cases m')
  case (Done r)
  with assms show ?thesis by (cases r) simp_all
qed (use assms in simp_all)

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

context evaluation
begin

function (sequential)
  run_expr  :: "nat \<Rightarrow> env \<Rightarrow> expr \<Rightarrow> val result fuelled" and
  run_exprs :: "nat \<Rightarrow> env \<Rightarrow> expr list \<Rightarrow> val list result fuelled" and
  run_stmt  :: "nat \<Rightarrow> env \<Rightarrow> stmt \<Rightarrow> outcome fuelled" and
  run_elif  :: "nat \<Rightarrow> env \<Rightarrow> elif_block \<Rightarrow> outcome fuelled" and
  run_quals :: "nat \<Rightarrow> env \<Rightarrow> qualifier list \<Rightarrow> env list result fuelled" and
  run_gen   :: "nat \<Rightarrow> env \<Rightarrow> var \<Rightarrow> val list \<Rightarrow> qualifier list \<Rightarrow> env list result fuelled" and
  run_comp  :: "nat \<Rightarrow> env list \<Rightarrow> expr \<Rightarrow> val list result fuelled" and
  run_entries :: "nat \<Rightarrow> env list \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> (string \<times> val) list result fuelled"
where
"run_expr 0 \<rho> e = OutOfFuel" |
"run_expr (Suc n) \<rho> (ExprVar x) = 
  (case fmlookup \<rho> x of
    Some VUnbound \<Rightarrow> Done (Aborts NameError)
  | Some v \<Rightarrow> Done (Val v)
  | None \<Rightarrow> Done (Aborts NameError))" |
"run_expr (Suc n) \<rho> (ExprLiteral l) = Done (Val (VLit l))" |
"run_expr (Suc n) \<rho> (ExprLambda xs e) = Done (Val Lam(\<rho>, xs, e))" |
"run_expr (Suc n) \<rho> (ExprUnOp op e) = flet (run_expr n \<rho> e) (\<lambda>v. Done (unop_meaning op v))" |
"run_expr (Suc n) \<rho> (ExprBinOp op e e') =
  flet (run_expr n \<rho> e) (\<lambda>v. flet (run_expr n \<rho> e') (\<lambda>v'. Done (binop_meaning op v v')))" |
"run_expr (Suc n) \<rho> (ExprAnd e e') =
  flet (run_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some False \<Rightarrow> Done (Val false)
  | Some True \<Rightarrow> run_expr n \<rho> e'
  | None \<Rightarrow> Done (Aborts Excluded))" |
"run_expr (Suc n) \<rho> (ExprOr e e') =
  flet (run_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Val true)
  | Some False \<Rightarrow> run_expr n \<rho> e'
  | None \<Rightarrow> Done (Aborts Excluded))" |
"run_expr (Suc n) \<rho> (ExprCond e1 e e2) =
  flet (run_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_expr n \<rho> e1
  | Some False \<Rightarrow> run_expr n \<rho> e2
  | None \<Rightarrow> Done (Aborts Excluded))" |
"run_expr (Suc n) \<rho> (ExprList es) = flet (run_exprs n \<rho> es) (\<lambda>vs. Done (Val (VList vs)))" |
"run_expr (Suc n) \<rho> (ExprTuple es) = flet (run_exprs n \<rho> es) (\<lambda>vs. Done (Val (VTuple vs)))" |
"run_expr (Suc n) \<rho> (ExprDict kes) =
  flet (run_exprs n \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes))) (\<lambda>vs. case dict_entries vs of
    Some \<delta> \<Rightarrow> Done (Val (VDict (update [] \<delta>)))
  | None \<Rightarrow> Done (Aborts Excluded))" |
"run_expr (Suc n) \<rho> (ExprListComp e gs) =
  flet (run_quals n \<rho> gs) (\<lambda>\<rho>s. flet (run_comp n \<rho>s e) (\<lambda>vs. Done (Val (VList vs))))" |
"run_expr (Suc n) \<rho> (ExprDictComp e e' gs) =
  flet (run_quals n \<rho> gs) (\<lambda>\<rho>s. flet (run_entries n \<rho>s e e') (\<lambda>\<delta>. Done (Val (VDict (update [] \<delta>)))))" |
"run_expr (Suc n) \<rho> (ExprSubscript e e') =
  flet (run_expr n \<rho> e) (\<lambda>v. case class_of v of
    Some C \<Rightarrow> if type_args_of e' = None then Stuck else Done (Val (VClass C))
  | None \<Rightarrow> flet (run_expr n \<rho> e') (\<lambda>v'. Done (getitem v v')))" |
"run_expr (Suc n) \<rho> (ExprCall e (es, kws)) =
  flet (run_expr n \<rho> e) (\<lambda>v. case class_of v of
    Some C \<Rightarrow>
      flet (run_exprs n \<rho> (es @ map snd kws)) (\<lambda>us.
        case field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) of
          Some xus \<Rightarrow> Done (Val (VObject C xus))
        | None \<Rightarrow> Stuck)
  | None \<Rightarrow>
      if kws \<noteq> [] then Stuck else
      flet (run_exprs n \<rho> es) (\<lambda>us. case v of
        Lam(\<rho>', xs, e') \<Rightarrow>
          if length xs = length us then run_expr n (\<rho>' \<otimes> fmap_of_list (zip xs us)) e' else Done (Aborts TypeError)
      | Def(\<rho>', ds, j) \<Rightarrow>
          if j < length ds then
            (case ds ! j of Def f \<alpha>s xps \<psi> s \<Rightarrow>
              if length xps = length us then
                (case scope VUnbound (map fst xps) s of
                  Some \<rho>s \<Rightarrow>
                    map_fuelled call_result
                      (run_stmt n
                        (\<rho>' \<otimes> fmap_of_list (zip (map def_name ds) (map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds]))
                           \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s) s)
                | None \<Rightarrow> Stuck)
              else Done (Aborts TypeError))
          else Stuck
      | _ \<Rightarrow> Done (Aborts TypeError)))" |
"run_expr (Suc n) \<rho> _ = Stuck" |

"run_exprs 0 \<rho> es = OutOfFuel" |
"run_exprs (Suc n) \<rho> [] = Done (Val [])" |
"run_exprs (Suc n) \<rho> (e # es) =
  flet (run_expr n \<rho> e) (\<lambda>v. flet (run_exprs n \<rho> es) (\<lambda>vs. Done (Val (v # vs))))" |

"run_stmt 0 \<rho> s = OutOfFuel" |
"run_stmt (Suc n) \<rho> StmtPass = Done (Assigns \<epsilon>)" |
"run_stmt (Suc n) \<rho> (StmtDeclare x \<psi>) = Done (Assigns \<epsilon>)" |
"run_stmt (Suc n) \<rho> (StmtAssign x \<pi> e) = flet_outcome (run_expr n \<rho> e) (\<lambda>v. Done (Assigns (fmupd x v \<epsilon>)))" |
"run_stmt (Suc n) \<rho> (StmtExpr e) = flet_outcome (run_expr n \<rho> e) (\<lambda>v. Done (Assigns \<epsilon>))" |
"run_stmt (Suc n) \<rho> (StmtReturn (Some e)) = flet_outcome (run_expr n \<rho> e) (\<lambda>v. Done (Returns v))" |
"run_stmt (Suc n) \<rho> (StmtReturn None) = Done (Returns (VLit LitNone))" |
"run_stmt (Suc n) \<rho> (StmtMutualRegion ds) =
  Done (Assigns (fmap_of_list (zip (map def_name ds) (map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]))))" |
"run_stmt (Suc n) \<rho> (StmtAssert e None) =
  flet_outcome (run_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Assigns \<epsilon>)
  | Some False \<Rightarrow> Done (Aborts\<^sub>o (AssertionError None))
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |
"run_stmt (Suc n) \<rho> (StmtAssert e (Some e')) =
  flet_outcome (run_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Assigns \<epsilon>)
  | Some False \<Rightarrow>
      flet_outcome (run_expr n \<rho> e') (\<lambda>v'. case v' of
        VLit (LitString w) \<Rightarrow> Done (Aborts\<^sub>o (AssertionError (Some w)))
      | _ \<Rightarrow> Done (Aborts\<^sub>o Excluded))
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |
"run_stmt (Suc n) \<rho> (StmtIf e s elifs else') =
  flet_outcome (run_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_stmt n \<rho> s
  | Some False \<Rightarrow> run_elif n \<rho> (elifs, else')
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |
"run_stmt (Suc n) \<rho> (StmtSeq s s') = fseq (run_stmt n \<rho> s) (\<lambda>\<rho>'. run_stmt n (\<rho> \<otimes> \<rho>') s')" |
"run_stmt (Suc n) \<rho> (StmtMatch e cases) =
  flet_outcome (run_expr n \<rho> e) (\<lambda>v. case dispatch \<rho> v cases of
    Val (\<rho>', s') \<Rightarrow> map_fuelled (\<lambda>o. Assigns \<rho>' \<otimes>\<^sub>o o) (run_stmt n (\<rho> \<otimes> \<rho>') s')
  | Aborts \<kappa> \<Rightarrow> Done (Aborts\<^sub>o \<kappa>))" |

"run_elif 0 \<rho> eb = OutOfFuel" |
"run_elif (Suc n) \<rho> ([], None) = Done (Assigns \<epsilon>)" |
"run_elif (Suc n) \<rho> ([], Some s) = run_stmt n \<rho> s" |
"run_elif (Suc n) \<rho> ((e, s) # elifs, else') =
  flet_outcome (run_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_stmt n \<rho> s
  | Some False \<Rightarrow> run_elif n \<rho> (elifs, else')
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |

"run_quals 0 \<rho> gs = OutOfFuel" |
"run_quals (Suc n) \<rho> [] = Done (Val [\<rho>])" |
"run_quals (Suc n) \<rho> (Guard e # gs) =
  flet (run_expr n \<rho> e) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_quals n \<rho> gs
  | Some False \<Rightarrow> Done (Val [])
  | None \<Rightarrow> Done (Aborts Excluded))" |
"run_quals (Suc n) \<rho> (Generator x e # gs) =
  flet (run_expr n \<rho> e) (\<lambda>v. case iter v of
    Some us \<Rightarrow> run_gen n \<rho> x us gs
  | None \<Rightarrow> Done (Aborts TypeError))" |

"run_gen 0 \<rho> x us gs = OutOfFuel" |
"run_gen (Suc n) \<rho> x [] gs = Done (Val [])" |
"run_gen (Suc n) \<rho> x (u # us) gs =
  flet (run_quals n (fmupd x u \<rho>) gs) (\<lambda>\<rho>s. flet (run_gen n \<rho> x us gs) (\<lambda>\<rho>ss. Done (Val (\<rho>s @ \<rho>ss))))" |

"run_comp 0 \<rho>s e = OutOfFuel" |
"run_comp (Suc n) [] e = Done (Val [])" |
"run_comp (Suc n) (\<rho> # \<rho>s) e =
  flet (run_expr n \<rho> e) (\<lambda>v. flet (run_comp n \<rho>s e) (\<lambda>vs. Done (Val (v # vs))))" |

"run_entries 0 \<rho>s e e' = OutOfFuel" |
"run_entries (Suc n) [] e e' = Done (Val [])" |
"run_entries (Suc n) (\<rho> # \<rho>s) e e' =
  flet (run_expr n \<rho> e) (\<lambda>k. case k of
    VLit (LitString w) \<Rightarrow>
      flet (run_expr n \<rho> e') (\<lambda>v. flet (run_entries n \<rho>s e e') (\<lambda>\<delta>. Done (Val ((w, v) # \<delta>))))
  | _ \<Rightarrow> Done (Aborts Excluded))"
by pat_completeness auto

(* Every call decreases the fuel, the first argument of each function *)
termination
  by (relation "measure (case_sum (case_sum (case_sum fst fst) (case_sum fst fst))
                                  (case_sum (case_sum fst fst) (case_sum fst fst)))") auto


lemmas eval_fun_induct =
  run_expr_run_exprs_run_stmt_run_elif_run_quals_run_gen_run_comp_run_entries.induct

end

end
