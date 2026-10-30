(* Evaluation as a function with fuel, and its executable code equations *)
theory Eval
    imports Semantics
begin

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
    | VLit (LitString w') \<Rightarrow> (case v of VLit (LitString w) \<Rightarrow> Val (substring w w') | _ \<Rightarrow> Aborts TypeError)
    | VObject C xvs \<Rightarrow> if C = range_class then Aborts Excluded else Aborts TypeError
    | _ \<Rightarrow> Aborts TypeError)"
  by (cases v'; cases v; auto split: lit.split)

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
  run_exprs :: "nat \<Rightarrow> env \<Rightarrow> expr located list \<Rightarrow> val list result fuelled" and
  run_stmt  :: "nat \<Rightarrow> env \<Rightarrow> stmt \<Rightarrow> outcome fuelled" and
  run_elif  :: "nat \<Rightarrow> env \<Rightarrow> elif_block \<Rightarrow> outcome fuelled" and
  run_quals :: "nat \<Rightarrow> env \<Rightarrow> qualifier located list \<Rightarrow> env list result fuelled" and
  run_gen   :: "nat \<Rightarrow> env \<Rightarrow> var \<Rightarrow> val list \<Rightarrow> qualifier located list \<Rightarrow> env list result fuelled" and
  run_comp  :: "nat \<Rightarrow> env list \<Rightarrow> expr located \<Rightarrow> val list result fuelled" and
  run_entries :: "nat \<Rightarrow> env list \<Rightarrow> expr located \<Rightarrow> expr located \<Rightarrow> (str \<times> val) list result fuelled"
where
"run_expr 0 \<rho> e = OutOfFuel" |
"run_expr (Suc n) \<rho> (ExprVar x) = 
  (case fmlookup \<rho> x of
    Some VUnbound \<Rightarrow> Done (Aborts NameError)
  | Some v \<Rightarrow> Done (Val v)
  | None \<Rightarrow> Done (Aborts NameError))" |
"run_expr (Suc n) \<rho> (ExprLiteral l) = Done (Val (VLit l))" |
"run_expr (Suc n) \<rho> (ExprLambda xs e) = Done (Val Lam(\<rho>, xs, e))" |
"run_expr (Suc n) \<rho> (ExprUnOp op e) = flet (run_expr n \<rho> (node e)) (\<lambda>v. Done (unop_meaning op v))" |
"run_expr (Suc n) \<rho> (ExprBinOp op e e') =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. flet (run_expr n \<rho> (node e')) (\<lambda>v'. Done (binop_meaning op v v')))" |
"run_expr (Suc n) \<rho> (ExprAnd e e') =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some False \<Rightarrow> Done (Val false)
  | Some True \<Rightarrow> run_expr n \<rho> (node e')
  | None \<Rightarrow> Done (Aborts Excluded))" |
"run_expr (Suc n) \<rho> (ExprOr e e') =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Val true)
  | Some False \<Rightarrow> run_expr n \<rho> (node e')
  | None \<Rightarrow> Done (Aborts Excluded))" |
"run_expr (Suc n) \<rho> (ExprCond e1 e e2) =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_expr n \<rho> (node e1)
  | Some False \<Rightarrow> run_expr n \<rho> (node e2)
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
  flet (run_expr n \<rho> (node e)) (\<lambda>v. case class_of v of
    Some C \<Rightarrow> if type_args_of e' = None then Stuck else Done (Val (VClass C))
  | None \<Rightarrow> flet (run_expr n \<rho> (node e')) (\<lambda>v'. Done (getitem v v')))" |
"run_expr (Suc n) \<rho> (ExprAttribute e x) =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. case fields_of v of
    Some xvs \<Rightarrow> (case map_of xvs x of Some u \<Rightarrow> Done (Val u) | None \<Rightarrow> Done (Aborts AttributeError))
  | None \<Rightarrow>
      (case module_env_of v of
         Some \<rho>' \<Rightarrow> (case fmlookup \<rho>' x of Some u \<Rightarrow> Done (Val u) | None \<Rightarrow> Done (Aborts AttributeError))
       | None \<Rightarrow> Done (Aborts Excluded)))" |
"run_expr (Suc n) \<rho> (ExprCall e (es, kws)) =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. case class_of v of
    Some C \<Rightarrow>
      flet (run_exprs n \<rho> (es @ map snd kws)) (\<lambda>us.
        case field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) of
          Some xus \<Rightarrow> Done (Val (VObject C xus))
        | None \<Rightarrow> Done (Aborts TypeError))
  | None \<Rightarrow>
      if kws \<noteq> [] then Stuck else
      flet (run_exprs n \<rho> es) (\<lambda>us. case v of
        Lam(\<rho>', xs, e') \<Rightarrow>
          if length xs = length us then run_expr n (\<rho>' \<otimes> fmap_of_list (zip xs us)) (node e') else Done (Aborts TypeError)
      | Def(\<rho>', ds, j) \<Rightarrow>
          if j < length ds then
            (case node (ds ! j) of Def f \<alpha>s xps \<psi> s \<Rightarrow>
              if length xps = length us then
                (case scope VUnbound (map fst xps) s of
                  Some \<rho>s \<Rightarrow>
                    map_fuelled call_result
                      (run_stmt n
                        (\<rho>' \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) (map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds]))
                           \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s) (node s))
                | None \<Rightarrow> Stuck)
              else Done (Aborts TypeError))
          else Stuck
      | VPrim f \<Rightarrow> Done (prim_meaning f us)
      | _ \<Rightarrow> Done (Aborts TypeError)))" |

"run_exprs 0 \<rho> es = OutOfFuel" |
"run_exprs (Suc n) \<rho> [] = Done (Val [])" |
"run_exprs (Suc n) \<rho> (e # es) =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. flet (run_exprs n \<rho> es) (\<lambda>vs. Done (Val (v # vs))))" |

"run_stmt 0 \<rho> s = OutOfFuel" |
"run_stmt (Suc n) \<rho> StmtPass = Done (Assigns \<epsilon>)" |
"run_stmt (Suc n) \<rho> (StmtDeclare x \<psi>) = Done (Assigns \<epsilon>)" |
"run_stmt (Suc n) \<rho> (StmtAssign x \<pi> e) = flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. Done (Assigns (fmupd x v \<epsilon>)))" |
"run_stmt (Suc n) \<rho> (StmtExpr e) = flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. Done (Assigns \<epsilon>))" |
"run_stmt (Suc n) \<rho> (StmtReturn (Some e)) = flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. Done (Returns v))" |
"run_stmt (Suc n) \<rho> (StmtReturn None) = Done (Returns (VLit LitNone))" |
"run_stmt (Suc n) \<rho> (StmtMutualRegion ds) =
  Done (Assigns (fmap_of_list (zip (map (def_name \<circ> node) ds) (map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]))))" |
"run_stmt (Suc n) \<rho> (StmtAssert e None) =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Assigns \<epsilon>)
  | Some False \<Rightarrow> Done (Aborts\<^sub>o (AssertionError None))
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |
"run_stmt (Suc n) \<rho> (StmtAssert e (Some e')) =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (Assigns \<epsilon>)
  | Some False \<Rightarrow>
      flet_outcome (run_expr n \<rho> (node e')) (\<lambda>v'. case v' of
        VLit (LitString w) \<Rightarrow> Done (Aborts\<^sub>o (AssertionError (Some w)))
      | _ \<Rightarrow> Done (Aborts\<^sub>o Excluded))
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |
"run_stmt (Suc n) \<rho> (StmtIf e s elifs else') =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_stmt n \<rho> (node s)
  | Some False \<Rightarrow> run_elif n \<rho> (elifs, else')
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |
"run_stmt (Suc n) \<rho> (StmtSeq s s') = fseq (run_stmt n \<rho> (node s)) (\<lambda>\<rho>'. run_stmt n (\<rho> \<otimes> \<rho>') (node s'))" |
"run_stmt (Suc n) \<rho> (StmtMatch e cases) =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case dispatch \<rho> v cases of
    Val (\<rho>', s') \<Rightarrow> map_fuelled (\<lambda>o. Assigns \<rho>' \<otimes>\<^sub>o o) (run_stmt n (\<rho> \<otimes> \<rho>') (node s'))
  | Aborts \<kappa> \<Rightarrow> Done (Aborts\<^sub>o \<kappa>))" |

"run_elif 0 \<rho> eb = OutOfFuel" |
"run_elif (Suc n) \<rho> ([], None) = Done (Assigns \<epsilon>)" |
"run_elif (Suc n) \<rho> ([], Some s) = run_stmt n \<rho> (node s)" |
"run_elif (Suc n) \<rho> ((e, s) # elifs, else') =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_stmt n \<rho> (node s)
  | Some False \<Rightarrow> run_elif n \<rho> (elifs, else')
  | None \<Rightarrow> Done (Aborts\<^sub>o Excluded))" |

"run_quals 0 \<rho> gs = OutOfFuel" |
"run_quals (Suc n) \<rho> [] = Done (Val [\<rho>])" |
"run_quals (Suc n) \<rho> (At p (Guard e) # gs) =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_quals n \<rho> gs
  | Some False \<Rightarrow> Done (Val [])
  | None \<Rightarrow> Done (Aborts Excluded))" |
"run_quals (Suc n) \<rho> (At p (Generator x e) # gs) =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. case iter v of
    Some us \<Rightarrow> run_gen n \<rho> x us gs
  | None \<Rightarrow> Done (Aborts TypeError))" |

"run_gen 0 \<rho> x us gs = OutOfFuel" |
"run_gen (Suc n) \<rho> x [] gs = Done (Val [])" |
"run_gen (Suc n) \<rho> x (u # us) gs =
  flet (run_quals n (fmupd x u \<rho>) gs) (\<lambda>\<rho>s. flet (run_gen n \<rho> x us gs) (\<lambda>\<rho>ss. Done (Val (\<rho>s @ \<rho>ss))))" |

"run_comp 0 \<rho>s e = OutOfFuel" |
"run_comp (Suc n) [] e = Done (Val [])" |
"run_comp (Suc n) (\<rho> # \<rho>s) e =
  flet (run_expr n \<rho> (node e)) (\<lambda>v. flet (run_comp n \<rho>s e) (\<lambda>vs. Done (Val (v # vs))))" |

"run_entries 0 \<rho>s e e' = OutOfFuel" |
"run_entries (Suc n) [] e e' = Done (Val [])" |
"run_entries (Suc n) (\<rho> # \<rho>s) e e' =
  flet (run_expr n \<rho> (node e)) (\<lambda>k. case k of
    VLit (LitString w) \<Rightarrow>
      flet (run_expr n \<rho> (node e')) (\<lambda>v. flet (run_entries n \<rho>s e e') (\<lambda>\<delta>. Done (Val ((w, v) # \<delta>))))
  | _ \<Rightarrow> Done (Aborts Excluded))"
by pat_completeness auto

(* Every call decreases the fuel, the first argument of each function *)
termination
  by (relation "measure (case_sum (case_sum (case_sum fst fst) (case_sum fst fst))
                                  (case_sum (case_sum fst fst) (case_sum fst fst)))") auto


lemmas eval_fun_induct =
  run_expr_run_exprs_run_stmt_run_elif_run_quals_run_gen_run_comp_run_entries.induct

(* Top-level statements, each plain statement with fuel n; Stuck on a return before a further statement, which no
   rule covers *)
primrec run_top :: "nat \<Rightarrow> name \<Rightarrow> env \<Rightarrow> top_stmt \<Rightarrow> outcome fuelled"
where
"run_top n q \<rho> (Stmt s) = run_stmt n \<rho> (node s)" |
"run_top n q \<rho> (TopSeq t t') =
  (case run_top n q \<rho> t of
     Done (Assigns \<rho>') \<Rightarrow> map_fuelled (\<lambda>o. Assigns \<rho>' \<otimes>\<^sub>o o) (run_top n q (\<rho> \<otimes> \<rho>') t')
   | Done (Returns v) \<Rightarrow> Stuck
   | r \<Rightarrow> r)" |
"run_top n q \<rho> (TypeDefs \<chi>s) =
  Done (Assigns (fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_value q \<chi>s j)) [0..<length \<chi>s])))"

end

context loading
begin

(* Evaluator: each loading step consumes fuel, so an import cycle runs out of fuel, as it has no derivation; the
   statements of a module body run with the same fuel *)
function (sequential) run_mod :: "nat \<Rightarrow> name \<Rightarrow> env result fuelled"
and run_imports :: "nat \<Rightarrow> name \<Rightarrow> import located list \<Rightarrow> env result fuelled"
and run_sub     :: "nat \<Rightarrow> name \<Rightarrow> env \<Rightarrow> var list \<Rightarrow> env result fuelled"
and run_imp     :: "nat \<Rightarrow> env \<Rightarrow> var \<Rightarrow> val result fuelled"
and run_imps    :: "nat \<Rightarrow> env \<Rightarrow> var list \<Rightarrow> val list result fuelled"
and run_mods    :: "nat \<Rightarrow> name list \<Rightarrow> unit result fuelled"
where
"run_mod 0 q = OutOfFuel" |
"run_mod (Suc n) q =
  (case fmlookup predefined_env q of
     Some \<rho> \<Rightarrow> Done (Val \<rho>)
   | None \<Rightarrow>
       (case fmlookup M q of
          None \<Rightarrow> Stuck
        | Some (ModuleBody \<iota>s t) \<Rightarrow>
            flet (run_imports n q \<iota>s) (\<lambda>\<rho>'.
              case scope VUnbound (declares \<iota>s) t of
                None \<Rightarrow> Stuck
              | Some \<rho>s \<Rightarrow>
                  (case run_top n q (builtins_env \<otimes> \<rho>' \<otimes> \<rho>s) t of
                     Done (Assigns \<rho>'') \<Rightarrow> Done (Val (submods_env q \<otimes> \<rho>''))
                   | Done (Aborts\<^sub>o \<kappa>) \<Rightarrow> Done (Aborts \<kappa>)
                   | Done (Returns v) \<Rightarrow> Stuck
                   | Stuck \<Rightarrow> Stuck
                   | OutOfFuel \<Rightarrow> OutOfFuel))))" |

"run_imports 0 q \<iota>s = OutOfFuel" |
"run_imports (Suc n) q [] = Done (Val \<epsilon>)" |
"run_imports (Suc n) q (At p (Import (x, xs)) # \<iota>s) =
  flet (run_mod n (x, [])) (\<lambda>\<rho>. flet (run_sub n (x, []) \<rho> xs) (\<lambda>\<rho>''. flet (run_imports n q \<iota>s) (\<lambda>\<rho>'.
    Done (Val (fmupd x (VModLoaded (x, []) \<rho>'') \<epsilon> \<uplus>\<^sub>v \<rho>')))))" |
"run_imports (Suc n) q (At p (FromImport q' xs) # \<iota>s) =
  flet (run_mods n (unique_to q' q)) (\<lambda>_. flet (run_mod n q') (\<lambda>\<rho>. flet (run_imps n \<rho> xs) (\<lambda>vs.
    flet (run_imports n q \<iota>s) (\<lambda>\<rho>''. Done (Val (fmap_of_list (zip xs vs) \<uplus>\<^sub>v \<rho>''))))))" |

"run_sub 0 q \<rho> xs = OutOfFuel" |
"run_sub (Suc n) q \<rho> [] = Done (Val \<rho>)" |
"run_sub (Suc n) q \<rho> (x # xs) =
  flet (run_mod n (snoc q x)) (\<lambda>\<rho>'. flet (run_sub n (snoc q x) \<rho>' xs) (\<lambda>\<rho>''.
    Done (Val (\<rho> \<uplus>\<^sub>v fmupd x (VModLoaded (snoc q x) \<rho>'') \<epsilon>))))" |

"run_imp 0 \<rho> x = OutOfFuel" |
"run_imp (Suc n) \<rho> x =
  (case fmlookup \<rho> x of
     None \<Rightarrow> Stuck
   | Some v \<Rightarrow>
       (case stub_of v of
          Some q' \<Rightarrow> flet (run_mod n q') (\<lambda>\<rho>'. Done (Val (VModLoaded q' \<rho>')))
        | None \<Rightarrow> Done (Val v)))" |

"run_imps 0 \<rho> xs = OutOfFuel" |
"run_imps (Suc n) \<rho> [] = Done (Val [])" |
"run_imps (Suc n) \<rho> (x # xs) = flet (run_imp n \<rho> x) (\<lambda>v. flet (run_imps n \<rho> xs) (\<lambda>vs. Done (Val (v # vs))))" |

"run_mods 0 qs = OutOfFuel" |
"run_mods (Suc n) [] = Done (Val ())" |
"run_mods (Suc n) (q # qs) = flet (run_mod n q) (\<lambda>_. run_mods n qs)"
by pat_completeness auto

termination
  by (relation "measure (case_sum (case_sum fst (case_sum fst fst)) (case_sum fst (case_sum fst fst)))") auto

definition run_program :: "nat \<Rightarrow> termination_kind fuelled"
where
"run_program n =
  (case run_mod n main of
     Done (Val \<rho>) \<Rightarrow> Done (SystemExit 0)
   | Done (Aborts \<kappa>) \<Rightarrow> Done \<kappa>
   | Stuck \<Rightarrow> Stuck
   | OutOfFuel \<Rightarrow> OutOfFuel)"

lemmas run_loading_induct = run_mod_run_imports_run_sub_run_imp_run_imps_run_mods.induct

end

end
