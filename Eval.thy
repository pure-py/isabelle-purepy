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

fun as_bool :: "val \<Rightarrow> bool option"
where
"as_bool (VLit (LitBool b)) = Some b" |
"as_bool _ = None"

fun flet_outcome :: "'a result fuelled \<Rightarrow> ('a \<Rightarrow> outcome fuelled) \<Rightarrow> outcome fuelled"
where
"flet_outcome (Done (Val v)) f = f v" |
"flet_outcome (Done (Aborts \<kappa>)) f = Done (aborts\<^sub>o \<kappa>)" |
"flet_outcome Stuck f = Stuck" |
"flet_outcome OutOfFuel f = OutOfFuel"

(* Sequential composition: run f on the environment of an Assigns, and compose the outcomes *)
fun fseq :: "outcome fuelled \<Rightarrow> (env \<Rightarrow> outcome fuelled) \<Rightarrow> outcome fuelled"
where
"fseq (Done (us, Assigns \<rho>')) f = map_fuelled (\<lambda>o. (us, Assigns \<rho>') \<otimes> o) (f \<rho>')" |
"fseq (Done o) f = Done o" |
"fseq Stuck f = Stuck" |
"fseq OutOfFuel f = OutOfFuel"

(* Result of a function body, which prints nothing *)
fun body_result :: "outcome fuelled \<Rightarrow> val result fuelled"
where
"body_result (Done ([], \<omega>)) = Done (result_of \<omega>)" |
"body_result (Done _) = Stuck" |
"body_result Stuck = Stuck" |
"body_result OutOfFuel = OutOfFuel"

fun fbind :: "'a fuelled \<Rightarrow> ('a \<Rightarrow> 'b fuelled) \<Rightarrow> 'b fuelled"
where
"fbind (Done x) f = f x" |
"fbind Stuck f = Stuck" |
"fbind OutOfFuel f = OutOfFuel"

lemma fbind_cong [fundef_cong]:
  assumes "m = m'" "\<And>x. m' = Done x \<Longrightarrow> f x = f' x"
  shows "fbind m f = fbind m' f'"
  using assms by (cases m') simp_all

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
                    body_result
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
"run_stmt (Suc n) \<rho> StmtPass = Done (assigns\<^sub>o \<epsilon>)" |
"run_stmt (Suc n) \<rho> (StmtDeclare x \<psi>) = Done (assigns\<^sub>o \<epsilon>)" |
"run_stmt (Suc n) \<rho> (StmtAssign x \<pi> e) = flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. Done (assigns\<^sub>o (fmupd x v \<epsilon>)))" |
"run_stmt (Suc n) \<rho> (StmtExpr e) = flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. Done (assigns\<^sub>o \<epsilon>))" |
"run_stmt (Suc n) \<rho> (StmtPrint e) = flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. Done ([v], Assigns \<epsilon>))" |
"run_stmt (Suc n) \<rho> (StmtReturn (Some e)) = flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. Done (returns\<^sub>o v))" |
"run_stmt (Suc n) \<rho> (StmtReturn None) = Done (returns\<^sub>o (VLit LitNone))" |
"run_stmt (Suc n) \<rho> (StmtMutualRegion ds) =
  Done (assigns\<^sub>o (fmap_of_list (zip (map (def_name \<circ> node) ds) (map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]))))" |
"run_stmt (Suc n) \<rho> (StmtAssert e None) =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (assigns\<^sub>o \<epsilon>)
  | Some False \<Rightarrow> Done (aborts\<^sub>o (AssertionError None))
  | None \<Rightarrow> Done (aborts\<^sub>o Excluded))" |
"run_stmt (Suc n) \<rho> (StmtAssert e (Some e')) =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> Done (assigns\<^sub>o \<epsilon>)
  | Some False \<Rightarrow>
      flet_outcome (run_expr n \<rho> (node e')) (\<lambda>v'. case v' of
        VLit (LitString w) \<Rightarrow> Done (aborts\<^sub>o (AssertionError (Some w)))
      | _ \<Rightarrow> Done (aborts\<^sub>o Excluded))
  | None \<Rightarrow> Done (aborts\<^sub>o Excluded))" |
"run_stmt (Suc n) \<rho> (StmtIf e s elifs else') =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_stmt n \<rho> (node s)
  | Some False \<Rightarrow> run_elif n \<rho> (elifs, else')
  | None \<Rightarrow> Done (aborts\<^sub>o Excluded))" |
"run_stmt (Suc n) \<rho> (StmtSeq s s') = fseq (run_stmt n \<rho> (node s)) (\<lambda>\<rho>'. run_stmt n (\<rho> \<otimes> \<rho>') (node s'))" |
"run_stmt (Suc n) \<rho> (StmtMatch e cases) =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case dispatch \<rho> v cases of
    Val (\<rho>', s') \<Rightarrow> map_fuelled (\<lambda>o. assigns\<^sub>o \<rho>' \<otimes> o) (run_stmt n (\<rho> \<otimes> \<rho>') (node s'))
  | Aborts \<kappa> \<Rightarrow> Done (aborts\<^sub>o \<kappa>))" |

"run_elif 0 \<rho> eb = OutOfFuel" |
"run_elif (Suc n) \<rho> ([], None) = Done (assigns\<^sub>o \<epsilon>)" |
"run_elif (Suc n) \<rho> ([], Some s) = run_stmt n \<rho> (node s)" |
"run_elif (Suc n) \<rho> ((e, s) # elifs, else') =
  flet_outcome (run_expr n \<rho> (node e)) (\<lambda>v. case as_bool v of
    Some True \<Rightarrow> run_stmt n \<rho> (node s)
  | Some False \<Rightarrow> run_elif n \<rho> (elifs, else')
  | None \<Rightarrow> Done (aborts\<^sub>o Excluded))" |

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
     Done (us, Assigns \<rho>') \<Rightarrow> map_fuelled (\<lambda>o. (us, Assigns \<rho>') \<otimes> o) (run_top n q (\<rho> \<otimes> \<rho>') t')
   | Done (us, Returns v) \<Rightarrow> Stuck
   | r \<Rightarrow> r)" |
"run_top n q \<rho> (TypeDefs \<chi>s) =
  Done (assigns\<^sub>o (fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_value q \<chi>s j)) [0..<length \<chi>s])))"

end

context loading
begin

(* Order of loading as by loads, each step consuming fuel *)
function (sequential)
  run_loads :: "nat \<Rightarrow> name list \<Rightarrow> name list \<Rightarrow> name list fuelled" and
  run_submod_loads :: "nat \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> var list \<Rightarrow> name list fuelled" and
  run_imports_loads :: "nat \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> import located list \<Rightarrow> name list fuelled" and
  run_import_loads :: "nat \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> import \<Rightarrow> name list fuelled"
where
"run_loads 0 qs qs' = OutOfFuel" |
"run_loads (Suc n) qs [] = Done qs" |
"run_loads (Suc n) qs (q # qs') =
  (if q \<in> set qs \<or> q |\<in>| fmdom \<P> then run_loads n qs qs'
   else case the (fmlookup \<M> q) of
     ModuleBody \<iota>s t \<Rightarrow> fbind (run_imports_loads n qs q \<iota>s) (\<lambda>qs''. run_loads n (qs'' @ [q]) qs'))" |

"run_submod_loads 0 qs q xs = OutOfFuel" |
"run_submod_loads (Suc n) qs q [] = Done qs" |
"run_submod_loads (Suc n) qs q (x # xs) =
  (if q |\<notin>| fmdom \<P> \<and> Qualified q x |\<in>| fmdom \<M> \<and> x \<notin> set (declares (the (fmlookup \<M> q)))
   then fbind (run_loads n qs [Qualified q x]) (\<lambda>qs'. run_submod_loads n qs' q xs)
   else run_submod_loads n qs q xs)" |

"run_imports_loads 0 qs q \<iota>s = OutOfFuel" |
"run_imports_loads (Suc n) qs q [] = Done qs" |
"run_imports_loads (Suc n) qs q (\<iota> # \<iota>s) =
  fbind (run_import_loads n qs q (node \<iota>)) (\<lambda>qs'. run_imports_loads n qs' q \<iota>s)" |

"run_import_loads 0 qs q \<iota> = OutOfFuel" |
"run_import_loads (Suc n) qs q (Import q') = run_loads n qs (proper_prefixes q' @ [q'])" |
"run_import_loads (Suc n) qs q (FromImport q' xs) =
  fbind (run_loads n qs (unique_to q' q @ [q'])) (\<lambda>qs'. run_submod_loads n qs' q' xs)"
by pat_completeness auto

termination
  by (relation "measure (case_sum (case_sum fst fst) (case_sum fst fst))") auto

lemmas run_loads_induct = run_loads_run_submod_loads_run_imports_loads_run_import_loads.induct

definition run_mod :: "nat \<Rightarrow> name \<Rightarrow> (name, env) fmap \<Rightarrow> outcome fuelled"
where
"run_mod n q \<L> =
  (case fmlookup \<M> q of
     None \<Rightarrow> Stuck
   | Some (ModuleBody \<iota>s t) \<Rightarrow>
       (case scope VUnbound (declares \<iota>s) t of
          None \<Rightarrow> Stuck
        | Some \<rho>s \<Rightarrow> run_top n q (the (fmlookup \<L> builtins) \<otimes> imports_env \<L> \<iota>s \<otimes> \<rho>s) t))"

(* Modules in the order of loading, each with the environments of those loaded before it; Stuck on a return at
   the top level, which no rule covers *)
fun run_mods :: "nat \<Rightarrow> name list \<Rightarrow> (name, env) fmap \<Rightarrow> outcome fuelled"
where
"run_mods n [] \<L> = Done (assigns\<^sub>o \<epsilon>)" |
"run_mods n (q # qs) \<L> =
  (case run_mod n q \<L> of
     Done (vs, Assigns \<rho>) \<Rightarrow>
       map_fuelled (\<lambda>o. (vs, Assigns \<epsilon>) \<otimes> o) (run_mods n qs (fmupd q (submods_env q \<otimes> \<rho>) \<L>))
   | Done (vs, Returns v) \<Rightarrow> Stuck
   | r \<Rightarrow> r)"

(* Printed values and termination kind of the program, with command-line arguments \<A> *)
definition run_program :: "nat \<Rightarrow> str list \<Rightarrow> (val list \<times> termination_kind) fuelled"
where
"run_program n \<A> =
  fbind (run_loads n [] [main]) (\<lambda>qs.
    case run_mods n qs (\<E> \<A>) of
      Done (vs, Assigns \<rho>) \<Rightarrow> Done (vs, SystemExit 0)
    | Done (vs, Aborts\<^sub>\<omega> \<kappa>) \<Rightarrow> Done (vs, \<kappa>)
    | Done (vs, Returns v) \<Rightarrow> Stuck
    | Stuck \<Rightarrow> Stuck
    | OutOfFuel \<Rightarrow> OutOfFuel)"

end

end
