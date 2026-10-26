theory Typing
  imports Operators
begin

(* Type at which a variable is bound or declared *)
fun var_ty :: "cxt_entry \<Rightarrow> ty option"
where
"var_ty (Ty \<tau>) = Some \<tau>" |
"var_ty (DU \<tau>) = Some \<tau>" |
"var_ty (PU \<tau>) = Some \<tau>" |
"var_ty _ = None"

(* Merge of a context entry with undefined *)
fun possibly_unassigned :: "cxt_entry \<Rightarrow> cxt_entry"
where
"possibly_unassigned (Ty \<tau>) = PU \<tau>" |
"possibly_unassigned (DU \<tau>) = PU \<tau>" |
"possibly_unassigned (PU \<tau>) = PU \<tau>" |
"possibly_unassigned (Scheme \<pi>) = PUScheme \<pi>" |
"possibly_unassigned (PUScheme \<pi>) = PUScheme \<pi>" |
"possibly_unassigned _ = undefined"

fun merge_cxt_entry :: "class_table \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry"
where
"merge_cxt_entry \<Sigma> (Some (Ty \<sigma>)) (Some (Ty \<tau>)) = Ty (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)" |
"merge_cxt_entry \<Sigma> (Some (Scheme \<pi>)) (Some (PUScheme \<pi>')) = (if \<pi> = \<pi>' then PUScheme \<pi> else undefined)" |
"merge_cxt_entry \<Sigma> (Some (PUScheme \<pi>)) (Some (Scheme \<pi>')) = (if \<pi> = \<pi>' then PUScheme \<pi> else undefined)" |
"merge_cxt_entry \<Sigma> (Some \<theta>) (Some \<theta>') =
  (if \<theta> = \<theta>' then \<theta>
   else case (var_ty \<theta>, var_ty \<theta>') of (Some \<sigma>, Some \<tau>) \<Rightarrow> PU (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>) | _ \<Rightarrow> undefined)" |
"merge_cxt_entry \<Sigma> (Some \<theta>) None = possibly_unassigned \<theta>" |
"merge_cxt_entry \<Sigma> None (Some \<theta>) = possibly_unassigned \<theta>" |
"merge_cxt_entry \<Sigma> None None = undefined"

definition merge :: "class_table \<Rightarrow> cxt \<Rightarrow> cxt \<Rightarrow> cxt"
where
"merge \<Sigma> \<Gamma> \<Gamma>' = fmmap_keys (\<lambda>x _. merge_cxt_entry \<Sigma> (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x)) (\<Gamma> \<otimes> \<Gamma>')"

syntax "_merge" :: "cxt \<Rightarrow> class_table \<Rightarrow> cxt \<Rightarrow> cxt" ("_ \<oplus>\<^bsub>_\<^esub> _" [65, 0, 66] 65)
translations "\<Gamma> \<oplus>\<^bsub>\<Sigma>\<^esub> \<Gamma>'" \<rightleftharpoons> "CONST merge \<Sigma> \<Gamma> \<Gamma>'"

datatype static_outcome = Assigns\<^sub>R cxt | Returns\<^sub>R

fun merge_outcome :: "class_table \<Rightarrow> static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome"
where
"merge_outcome \<Sigma> (Assigns\<^sub>R \<Delta>) (Assigns\<^sub>R \<Delta>') = Assigns\<^sub>R (\<Delta> \<oplus>\<^bsub>\<Sigma>\<^esub> \<Delta>')" |
"merge_outcome \<Sigma> R Returns\<^sub>R = R" |
"merge_outcome \<Sigma> Returns\<^sub>R R = R"

fun merges :: "class_table \<Rightarrow> (reason + static_outcome) list \<Rightarrow> reason + static_outcome"
where
"merges \<Sigma> [] = Inr Returns\<^sub>R" |
"merges \<Sigma> (m # ms) = do { R \<leftarrow> m; R' \<leftarrow> merges \<Sigma> ms; Inr (merge_outcome \<Sigma> R R') }"

fun override_outcome :: "static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome" (infixl "\<otimes>\<^sub>R" 100)
where
"Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R Assigns\<^sub>R \<Delta>' = Assigns\<^sub>R (\<Delta> \<otimes> \<Delta>')" |
"_ \<otimes>\<^sub>R _ = Returns\<^sub>R"

definition attr_module :: "name \<Rightarrow> cxt \<Rightarrow> var \<Rightarrow> name \<Rightarrow> reason + ty"
where
"attr_module q \<Gamma> x q' =
  (case fmlookup \<Gamma> x of
     None \<Rightarrow> Inl (UnknownMember x q)
   | Some (Ty \<tau>) \<Rightarrow> Inr \<tau>
   | Some (ModStub q'') \<Rightarrow> Inl (SubmoduleNotImported q'')
   | Some (ModChecked _ _) \<Rightarrow> Inl (ModuleAsValue q')
   | Some (Type _) \<Rightarrow> Inl (ClassAsValue q')
   | Some (TypeAlias _ _ _ _) \<Rightarrow> Inl (TypeAliasAsValue q')
   | Some PredefName \<Rightarrow> Inl (PredefinedNameAsValue q')
   | Some (Scheme _) \<Rightarrow> Inl (TypeSchemeAsValue q')
   | Some TypeVar \<Rightarrow> undefined
   | Some _ \<Rightarrow> Inl (UnassignedMember x q))"

(* Failure if one of the variables bound by qualifiers with bindings \<Delta> is in X, the variables captured by
   lambdas *)
definition captured :: "var set \<Rightarrow> cxt \<Rightarrow> reason + unit"
where
"captured X \<Delta> =
  (let Y = X \<inter> fset (fmdom \<Delta>) in if Y = {} then Inr () else Inl (CapturedGeneratorVariable (Min Y)))"

definition lambda_arguments :: "var list \<Rightarrow> (var \<times> expr) list \<Rightarrow> expr list \<Rightarrow> (reason + ty) list \<Rightarrow> reason + cxt"
where
"lambda_arguments xs kws es \<sigma>s = do {
   ensure (kws = []) KeywordArgumentsNotConstructor;
   ensure (length xs = length es) (CallArityMismatch (length xs) (length es));
   \<tau>s \<leftarrow> those_sum \<sigma>s;
   if distinct xs then Inr (fmap_of_list (zip xs (map Ty \<tau>s))) else Inl undefined
 }"

(* Name bound at a type scheme checked against \<tau>, by var-scheme; None for other expressions *)
definition var_scheme :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> (reason + unit) option"
where
"var_scheme \<Sigma> \<Gamma> e \<tau> =
  (case scheme_of_name \<Gamma> e of
     Some (TyScheme \<alpha>s \<sigma>) \<Rightarrow> Some (do {
       \<tau>s \<leftarrow> type_arguments (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s;
       let \<sigma>' = subst \<tau>s \<alpha>s \<sigma>;
       ensure (\<Sigma> \<turnstile> \<sigma>' <: \<tau>) (TypeMismatch \<tau> \<sigma>')
     })
   | None \<Rightarrow> None)"

function (sequential)
  synth_expr :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> reason + ty" and
  synth_exprs :: "class_table \<Rightarrow> cxt \<Rightarrow> expr list \<Rightarrow> (reason + ty) list" and
  elements_join :: "class_table \<Rightarrow> cxt \<Rightarrow> expr list \<Rightarrow> reason + ty" and
  callee :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> expr list \<Rightarrow> reason + ty" and
  call_at :: "class_table \<Rightarrow> cxt \<Rightarrow> ty \<Rightarrow> (var \<times> expr) list \<Rightarrow> expr list \<Rightarrow> reason + ty" and
  check_expr :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> reason + unit" and
  check_expr' :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> (reason + unit) option" and
  check_exprs :: "class_table \<Rightarrow> cxt \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> reason + unit" and
  check_args :: "class_table \<Rightarrow> cxt \<Rightarrow> (var \<times> expr) list \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> reason + unit" and
  quals :: "class_table \<Rightarrow> cxt \<Rightarrow> qualifier list \<Rightarrow> reason + cxt"
where
"synth_expr \<Sigma> \<Gamma> (ExprVar x) = (case fmlookup \<Gamma> x of Some (Ty \<tau>) \<Rightarrow> Inr \<tau> | \<theta> \<Rightarrow> Inl (var_reason x \<theta>))" |
"synth_expr \<Sigma> \<Gamma> (ExprLiteral l) = Inr (case l of LitFloat _ \<Rightarrow> TyPrim float | _ \<Rightarrow> TyLiteral l)" |
"synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) =
  (case e of
     ExprLambda xs e' \<Rightarrow> do {
       \<Delta> \<leftarrow> lambda_arguments xs kws es (synth_exprs \<Sigma> \<Gamma> es); synth_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e'
     }
   | _ \<Rightarrow>
     (case constructor_class \<Sigma> \<Gamma> e of
        Some m \<Rightarrow> do {
          (C, explicit) \<leftarrow> m;
          case fields \<Sigma> C of
            FieldScheme \<alpha>s x\<sigma>s \<Rightarrow> do {
              \<sigma>es \<leftarrow> constructor_args C (FieldScheme \<alpha>s x\<sigma>s) es kws;
              case explicit of
                Some \<tau>s \<Rightarrow> do {
                  those_sum (map (\<lambda>(\<sigma>, e'). check_expr \<Sigma> \<Gamma> e' (subst \<tau>s \<alpha>s \<sigma>)) \<sigma>es);
                  Inr (TyClass C \<tau>s)
                }
              | None \<Rightarrow> do {
                  let synthesising = filter (synthesises \<circ> snd) \<sigma>es;
                  \<tau>s' \<leftarrow> those_sum (map (synth_expr \<Sigma> \<Gamma> \<circ> snd) synthesising);
                  \<tau>s \<leftarrow> type_arguments (type_args_seq \<Sigma> \<alpha>s (map fst synthesising) \<tau>s') \<alpha>s;
                  those_sum (map (\<lambda>(\<sigma>, e'). check_expr \<Sigma> \<Gamma> e' (subst \<tau>s \<alpha>s \<sigma>)) \<sigma>es);
                  Inr (TyClass C \<tau>s)
                }
            }
        }
      | None \<Rightarrow> do { \<sigma> \<leftarrow> callee \<Sigma> \<Gamma> e es; call_at \<Sigma> \<Gamma> \<sigma> kws es }))" |
"synth_expr \<Sigma> \<Gamma> (ExprBinOp op e e') = do {
   \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e;
   \<sigma>' \<leftarrow> synth_expr \<Sigma> \<Gamma> e';
   case resolve_binop \<Sigma> op \<sigma> \<sigma>' of Some \<tau> \<Rightarrow> Inr \<tau> | None \<Rightarrow> Inl (NoBinaryOverload op \<sigma> \<sigma>')
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprUnOp op e) =
  (if op = UOpNeg \<and> numeric_literal e then Inl undefined
   else do {
     \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e;
     case resolve_unop \<Sigma> op \<sigma> of Some \<tau> \<Rightarrow> Inr \<tau> | None \<Rightarrow> Inl (NoUnaryOverload op \<sigma>)
   })" |
"synth_expr \<Sigma> \<Gamma> (ExprAnd e e') =
  do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); check_expr \<Sigma> \<Gamma> e' (TyPrim bool); Inr (TyPrim bool) }" |
"synth_expr \<Sigma> \<Gamma> (ExprOr e e') =
  do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); check_expr \<Sigma> \<Gamma> e' (TyPrim bool); Inr (TyPrim bool) }" |
"synth_expr \<Sigma> \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) = do {
   check_expr \<Sigma> \<Gamma> e (TyPrim bool);
   case (synth_expr \<Sigma> \<Gamma> e\<^sub>1, synth_expr \<Sigma> \<Gamma> e\<^sub>2) of
     (Inr \<sigma>\<^sub>1, Inr \<sigma>\<^sub>2) \<Rightarrow> Inr (\<sigma>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<sigma>\<^sub>2)
   | (Inr \<sigma>\<^sub>1, Inl _) \<Rightarrow> do { check_expr \<Sigma> \<Gamma> e\<^sub>2 \<sigma>\<^sub>1; Inr \<sigma>\<^sub>1 }
   | (Inl _, Inr \<sigma>\<^sub>2) \<Rightarrow> do { check_expr \<Sigma> \<Gamma> e\<^sub>1 \<sigma>\<^sub>2; Inr \<sigma>\<^sub>2 }
   | (r\<^sub>1, r\<^sub>2) \<Rightarrow> Inl (synth_failure [r\<^sub>1, r\<^sub>2])
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprList es) = do { \<tau> \<leftarrow> elements_join \<Sigma> \<Gamma> es; Inr (TyList \<tau>) }" |
"synth_expr \<Sigma> \<Gamma> (ExprTuple es) = do { \<tau>s \<leftarrow> those_sum (synth_exprs \<Sigma> \<Gamma> es); Inr (TyTuple \<tau>s) }" |
"synth_expr \<Sigma> \<Gamma> (ExprAttribute e x) =
  (case dotted_name e of
     Some q \<Rightarrow>
       (case (resolve_name \<Gamma> q, lookup \<Gamma> q) of
          (Some (ModChecked q' \<Gamma>'), _) \<Rightarrow> attr_module q' \<Gamma>' x (snoc q x)
        | (_, Some (ModStub q')) \<Rightarrow> Inl (SubmoduleNotImported q')
        | _ \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e; attribute_type \<Sigma> \<sigma> x })
   | None \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e; attribute_type \<Sigma> \<sigma> x })" |
"synth_expr \<Sigma> \<Gamma> (ExprSubscript e e') = do {
   \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e;
   subscript_type \<Sigma> \<sigma> (check_expr \<Sigma> \<Gamma> e' (TyPrim int)) (check_expr \<Sigma> \<Gamma> e' (TyPrim str)) (synth_expr \<Sigma> \<Gamma> e')
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprDict kvs) = do {
   check_exprs \<Sigma> \<Gamma> (map fst kvs) (replicate (length kvs) (TyPrim str));
   \<tau> \<leftarrow> elements_join \<Sigma> \<Gamma> (map snd kvs);
   Inr (TyDict \<tau>)
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprListComp e gs) = do {
   \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs;
   captured (captures e) \<Delta>;
   \<tau> \<leftarrow> synth_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e;
   Inr (TyList (base_type \<tau>))
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprDictComp e e' gs) = do {
   \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs;
   captured (captures e \<union> captures e') \<Delta>;
   check_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str);
   \<tau> \<leftarrow> synth_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e';
   Inr (TyDict (base_type \<tau>))
 }" |
"synth_expr \<Sigma> \<Gamma> _ = Inl NotSynthesised" |

"synth_exprs \<Sigma> \<Gamma> [] = []" |
"synth_exprs \<Sigma> \<Gamma> (e # es) = synth_expr \<Sigma> \<Gamma> e # synth_exprs \<Sigma> \<Gamma> es" |

"callee \<Sigma> \<Gamma> e es =
  (case scheme_of_name \<Gamma> e of
     Some (TyScheme \<alpha>s (TyCallable \<sigma>s \<sigma>)) \<Rightarrow>
       (let synthesising = filter (synthesises \<circ> snd) (zip \<sigma>s es) in do {
          \<tau>s \<leftarrow> those_sum (map (synth_expr \<Sigma> \<Gamma> \<circ> snd) synthesising);
          \<tau>s' \<leftarrow> type_arguments (type_args_seq \<Sigma> \<alpha>s (map fst synthesising) \<tau>s) \<alpha>s;
          Inr (TyCallable (map (subst \<tau>s' \<alpha>s) \<sigma>s) (subst \<tau>s' \<alpha>s \<sigma>))
        })
   | Some _ \<Rightarrow> undefined
   | None \<Rightarrow> synth_expr \<Sigma> \<Gamma> e)" |

"call_at \<Sigma> \<Gamma> (TyUnion \<sigma> \<sigma>') kws es =
  do { \<tau> \<leftarrow> call_at \<Sigma> \<Gamma> \<sigma> kws es; \<tau>' \<leftarrow> call_at \<Sigma> \<Gamma> \<sigma>' kws es; Inr (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') }" |
"call_at \<Sigma> \<Gamma> (TyCallable \<sigma>s \<tau>) kws es = do {
   check_args \<Sigma> \<Gamma> kws es \<sigma>s;
   ensure (\<tau> \<noteq> TyPrim NoneType) (MypyCompatibility NoneResult);
   Inr \<tau>
 }" |
"call_at \<Sigma> \<Gamma> \<sigma> _ _ = Inl (NotCallable \<sigma>)" |

"elements_join \<Sigma> \<Gamma> es =
  (let \<sigma>s = synth_exprs \<Sigma> \<Gamma> es; \<tau> = joins \<Sigma> (map (base_type \<circ> projr) (filter (Not \<circ> isl) \<sigma>s)) in
   if \<not> list_all isl \<sigma>s then do {
     those_sum (map (\<lambda>j. check_expr \<Sigma> \<Gamma> (es ! j) \<tau>) (filter (\<lambda>j. isl (\<sigma>s ! j)) [0..<length es]));
     Inr \<tau>
   }
   else Inl (synth_failure \<sigma>s))" |

"check_expr \<Sigma> \<Gamma> e \<tau> =
  (case check_expr' \<Sigma> \<Gamma> e \<tau> of
     Some (Inr ()) \<Rightarrow> Inr ()
   | Some (Inl r) \<Rightarrow> (case synth_expr \<Sigma> \<Gamma> e of Inr \<sigma> \<Rightarrow> if \<Sigma> \<turnstile> \<sigma> <: \<tau> then Inr () else Inl r | Inl _ \<Rightarrow> Inl r)
   | None \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e; ensure (\<Sigma> \<turnstile> \<sigma> <: \<tau>) (TypeMismatch \<tau> \<sigma>) })" |

"check_expr' \<Sigma> \<Gamma> (ExprLambda xs e) \<tau> =
  Some (case \<tau> of
     TyCallable \<tau>s \<tau>' \<Rightarrow>
       if length xs \<noteq> length \<tau>s then Inl (LambdaTypeMismatch \<tau> (Some (length xs)))
       else if distinct xs then check_expr \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e \<tau>' else Inl undefined
   | _ \<Rightarrow> Inl (LambdaTypeMismatch \<tau> None))" |
"check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> =
  (case e of
     ExprLambda xs e' \<Rightarrow> Some (do {
       \<Delta> \<leftarrow> lambda_arguments xs kws es (synth_exprs \<Sigma> \<Gamma> es); check_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau>
     })
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprList es) \<tau> =
  (case \<tau> of TyList \<tau>' \<Rightarrow> Some (check_exprs \<Sigma> \<Gamma> es (replicate (length es) \<tau>')) | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprTuple es) \<tau> =
  (case \<tau> of TyTuple \<tau>s \<Rightarrow> if length es = length \<tau>s then Some (check_exprs \<Sigma> \<Gamma> es \<tau>s) else None | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) \<tau> =
  Some (do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); check_expr \<Sigma> \<Gamma> e\<^sub>1 \<tau>; check_expr \<Sigma> \<Gamma> e\<^sub>2 \<tau> })" |
"check_expr' \<Sigma> \<Gamma> (ExprDict kvs) \<tau> =
  (case \<tau> of
     TyDict \<tau>' \<Rightarrow> Some (do {
       check_exprs \<Sigma> \<Gamma> (map fst kvs) (replicate (length kvs) (TyPrim str));
       check_exprs \<Sigma> \<Gamma> (map snd kvs) (replicate (length kvs) \<tau>')
     })
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprListComp e gs) \<tau> =
  (case \<tau> of
     TyList \<tau>' \<Rightarrow> Some (do { \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs; captured (captures e) \<Delta>; check_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau>' })
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprDictComp e e' gs) \<tau> =
  (case \<tau> of
     TyDict \<tau>' \<Rightarrow> Some (do {
       \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs;
       captured (captures e \<union> captures e') \<Delta>;
       check_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str);
       check_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau>'
     })
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprVar x) \<tau> = var_scheme \<Sigma> \<Gamma> (ExprVar x) \<tau>" |
"check_expr' \<Sigma> \<Gamma> (ExprAttribute e x) \<tau> = var_scheme \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>" |
"check_expr' \<Sigma> \<Gamma> _ _ = None" |

"check_exprs \<Sigma> \<Gamma> [] [] = Inr ()" |
"check_exprs \<Sigma> \<Gamma> (e # es) (\<tau> # \<tau>s) = do { check_expr \<Sigma> \<Gamma> e \<tau>; check_exprs \<Sigma> \<Gamma> es \<tau>s }" |
"check_exprs \<Sigma> \<Gamma> _ _ = undefined" |

"check_args \<Sigma> \<Gamma> kws es \<sigma>s = do {
   ensure (kws = []) KeywordArgumentsNotConstructor;
   ensure (length \<sigma>s = length es) (CallArityMismatch (length \<sigma>s) (length es));
   check_exprs \<Sigma> \<Gamma> es \<sigma>s
 }" |

"quals \<Sigma> \<Gamma> [] = Inr fmempty" |
"quals \<Sigma> \<Gamma> (Guard e # gs) = do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); quals \<Sigma> \<Gamma> gs }" |
"quals \<Sigma> \<Gamma> (Generator x e # gs) = do {
   \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e;
   \<tau> \<leftarrow> (case elem_type \<Sigma> \<sigma> of Some \<tau> \<Rightarrow> Inr \<tau> | None \<Rightarrow> Inl (NotIterable \<sigma>));
   ensure (x \<notin> captures gs) (CapturedGeneratorVariable x);
   \<Delta> \<leftarrow> quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs;
   Inr (fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)
 }"
by pat_completeness auto

termination
by (relation "measures [\<lambda>x. case x of
     Inl (Inl (Inl (_, _, e))) \<Rightarrow> size e
   | Inl (Inl (Inr (_, _, es))) \<Rightarrow> size_list size es
   | Inl (Inr (Inl (_, _, es))) \<Rightarrow> size_list size es
   | Inl (Inr (Inr (Inl (_, _, e, es)))) \<Rightarrow> size e + size_list size es
   | Inl (Inr (Inr (Inr (_, _, _, kws, es)))) \<Rightarrow> size_list size es + size_list (\<lambda>p. Suc (size (snd p))) kws
   | Inr (Inl (Inl (_, _, e, _))) \<Rightarrow> size e
   | Inr (Inl (Inr (_, _, e, _))) \<Rightarrow> size e
   | Inr (Inr (Inl (_, _, es, _))) \<Rightarrow> size_list size es
   | Inr (Inr (Inr (Inl (_, _, kws, es, _)))) \<Rightarrow> size_list size es + size_list (\<lambda>p. Suc (size (snd p))) kws
   | Inr (Inr (Inr (Inr (_, _, gs)))) \<Rightarrow> size_list size gs,
   \<lambda>x. case x of
     Inl (Inl (Inl _)) \<Rightarrow> 0
   | Inl (Inl (Inr _)) \<Rightarrow> 0
   | Inl (Inr (Inl _)) \<Rightarrow> 1
   | Inl (Inr (Inr (Inl _))) \<Rightarrow> 4
   | Inl (Inr (Inr (Inr _))) \<Rightarrow> 4
   | Inr (Inl (Inl _)) \<Rightarrow> 2
   | Inr (Inl (Inr _)) \<Rightarrow> 1
   | Inr (Inr (Inl _)) \<Rightarrow> 2
   | Inr (Inr (Inr (Inl _))) \<Rightarrow> 3
   | Inr (Inr (Inr (Inr _))) \<Rightarrow> 0,
   \<lambda>x. case x of Inl (Inr (Inr (Inr (_, _, \<tau>, _, _)))) \<Rightarrow> size \<tau> | _ \<Rightarrow> 0]")
   (auto dest!: nth_mem constructor_args_elem set_zip_rightD
     dest: size_list_snd_elem size_list_snd_elem' size_list_elem[where f = size]
     intro: size_list_estimation' size_list_elem
     simp: less_Suc_eq_le size_list_fst size_list_snd)

(* Context entry for a type scheme, which is a plain type when its parameter list is empty *)
fun signature_entry :: "ty_scheme \<Rightarrow> cxt_entry"
where
"signature_entry (TyScheme [] \<tau>) = Ty \<tau>" |
"signature_entry \<pi> = Scheme \<pi>"

fun def_signature :: "class_table \<Rightarrow> cxt \<Rightarrow> func \<Rightarrow> reason + ty_scheme"
where
"def_signature \<Sigma> \<Gamma> (Def f \<alpha>s xps \<psi> s) =
   (let \<Gamma>' = \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar in do {
      \<sigma>s \<leftarrow> those_sum (map (resolve_type \<Sigma> \<Gamma>' \<circ> snd) xps);
      \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma>' \<psi>;
      Inr (TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>))
    })"

(* Call statement at callee type \<sigma>, by call-stmt and call-stmt-union *)
fun call_stmt_at :: "class_table \<Rightarrow> cxt \<Rightarrow> ty \<Rightarrow> (var \<times> expr) list \<Rightarrow> expr list \<Rightarrow> reason + unit"
where
"call_stmt_at \<Sigma> \<Gamma> (TyUnion \<sigma> \<sigma>') kws es = do { call_stmt_at \<Sigma> \<Gamma> \<sigma> kws es; call_stmt_at \<Sigma> \<Gamma> \<sigma>' kws es }" |
"call_stmt_at \<Sigma> \<Gamma> (TyCallable \<sigma>s (TyPrim NoneType)) kws es = check_args \<Sigma> \<Gamma> kws es \<sigma>s" |
"call_stmt_at \<Sigma> \<Gamma> \<sigma> kws es = do { call_at \<Sigma> \<Gamma> \<sigma> kws es; Inr () }"

abbreviation false_lit :: expr where "false_lit \<equiv> ExprLiteral (LitBool False)"

(* Failure for the first assignment target of xs which isn't in X, declared or a pattern variable of Y *)
definition check_assignments_declared :: "var set \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> var set \<Rightarrow> reason + unit"
where
"check_assignments_declared X xs ys Y =
  (case find (\<lambda>x. x \<notin> X \<and> x \<notin> set ys \<and> x \<notin> Y) xs of
     Some x \<Rightarrow> Inl (UndeclaredAssignment x)
   | None \<Rightarrow> Inr ())"

fun check_stmt :: "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> stmt \<Rightarrow> reason + static_outcome"
and check_elifs :: "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> (expr \<times> stmt) list \<Rightarrow> (reason + static_outcome) list"
and check_defs :: "class_table \<Rightarrow> cxt \<Rightarrow> func list \<Rightarrow> ty_scheme list \<Rightarrow> reason + unit"
and check_def :: "class_table \<Rightarrow> cxt \<Rightarrow> func \<Rightarrow> ty_scheme \<Rightarrow> reason + unit"
where
"check_stmt \<Sigma> \<Gamma> \<zeta> StmtPass = Inr (Assigns\<^sub>R fmempty)" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtDeclare x \<psi>) = do { \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; Inr (Assigns\<^sub>R (fmupd x (DU \<tau>) fmempty)) }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x None e) =
  (case fmlookup \<Gamma> x of
     Some (DU \<tau>) \<Rightarrow> do { check_expr \<Sigma> \<Gamma> e \<tau>; Inr (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty)) }
   | \<theta> \<Rightarrow> Inl (assign_reason x \<theta>))" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x (Some \<psi>) e) = do {
   \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; check_expr \<Sigma> \<Gamma> e \<tau>; Inr (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty))
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) =
  (case e of
     ExprCall e' (es, kws) \<Rightarrow>
       if (case e' of ExprLambda _ _ \<Rightarrow> True | _ \<Rightarrow> False) \<or> class_of_name \<Gamma> e' \<noteq> None
       then do { synth_expr \<Sigma> \<Gamma> e; Inr (Assigns\<^sub>R fmempty) }
       else do { \<sigma> \<leftarrow> callee \<Sigma> \<Gamma> e' es; call_stmt_at \<Sigma> \<Gamma> \<sigma> kws es; Inr (Assigns\<^sub>R fmempty) }
   | _ \<Rightarrow> do { synth_expr \<Sigma> \<Gamma> e; Inr (Assigns\<^sub>R fmempty) })" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = do {
   (if e = false_lit then Inr () else check_expr \<Sigma> \<Gamma> e (TyPrim bool));
   (case e' of Some e'' \<Rightarrow> check_expr \<Sigma> \<Gamma> e'' (TyPrim str) | None \<Rightarrow> Inr ());
   Inr (if e = false_lit then Returns\<^sub>R else Assigns\<^sub>R fmempty)
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn None) =
  (case \<zeta> of
     Some \<tau> \<Rightarrow>
       if \<Sigma> \<turnstile> \<tau> \<approx> TyPrim NoneType then Inr Returns\<^sub>R
       else Inl (mypy_only_if (\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>) (BareReturn \<tau>))
   | None \<Rightarrow> undefined)" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn (Some e)) =
  (case \<zeta> of Some \<tau> \<Rightarrow> do { check_expr \<Sigma> \<Gamma> e \<tau>; Inr Returns\<^sub>R } | None \<Rightarrow> undefined)" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = do {
   check_expr \<Sigma> \<Gamma> e (TyPrim bool);
   merges \<Sigma> (check_stmt \<Sigma> \<Gamma> \<zeta> s # check_elifs \<Sigma> \<Gamma> \<zeta> elifs
           @ [case else' of Some s' \<Rightarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s' | None \<Rightarrow> Inr (Assigns\<^sub>R fmempty)])
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = do {
   R \<leftarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s;
   case R of
     Assigns\<^sub>R \<Delta> \<Rightarrow> do { R' \<leftarrow> check_stmt \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s'; Inr (Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R R') }
   | Returns\<^sub>R \<Rightarrow> Inl UnreachableStatement
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMutualRegion ds) = do {
   \<pi>s \<leftarrow> those_sum (map (def_signature \<Sigma> \<Gamma>) ds);
   let \<Delta> = fmap_of_list (zip (map def_name ds) (map signature_entry \<pi>s));
   check_defs \<Sigma> (\<Gamma> \<otimes> \<Delta>) ds \<pi>s;
   Inr (Assigns\<^sub>R \<Delta>)
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMatch e bs) = undefined" |

"check_elifs \<Sigma> \<Gamma> \<zeta> [] = []" |
"check_elifs \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs) =
  (do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); check_stmt \<Sigma> \<Gamma> \<zeta> s }) # check_elifs \<Sigma> \<Gamma> \<zeta> elifs" |

"check_defs \<Sigma> \<Gamma> [] [] = Inr ()" |
"check_defs \<Sigma> \<Gamma> (d # ds) (\<pi> # \<pi>s) = do { check_def \<Sigma> \<Gamma> d \<pi>; check_defs \<Sigma> \<Gamma> ds \<pi>s }" |
"check_defs \<Sigma> \<Gamma> _ _ = undefined" |

"check_def \<Sigma> \<Gamma> (Def f \<alpha>s xps \<psi> s) (TyScheme \<alpha>s' (TyCallable \<sigma>s \<tau>)) =
  (let xs = map fst xps in do {
     check_assignments_declared (set xs) (assign_targets s) (declares s) (binds s);
     \<Delta> \<leftarrow> (case scope Unbound xs s of Some \<Delta> \<Rightarrow> Inr \<Delta> | None \<Rightarrow> Inl (scope_reason xs (declares s) (binds s)));
     if length xs = length \<sigma>s then do {
       R \<leftarrow> check_stmt \<Sigma> (\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> fmap_of_list (zip xs (map Ty \<sigma>s)) \<otimes> \<Delta>) (Some \<tau>) s;
       if R = Returns\<^sub>R \<or> \<Sigma> \<turnstile> \<tau> \<approx> TyPrim NoneType then Inr ()
       else Inl (mypy_only_if (\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>) (MissingReturn f \<tau>))
     }
     else Inl undefined
   })" |
"check_def \<Sigma> \<Gamma> _ _ = undefined"

fun check_type_def :: "class_table \<Rightarrow> cxt \<Rightarrow> type_def \<Rightarrow> reason + unit"
where
"check_type_def \<Sigma> \<Gamma> (Dataclass c \<alpha>s b \<phi>) = do {
   check_predefined \<Gamma> ''dataclass'';
   those_sum (map (resolve_type \<Sigma> \<Gamma> \<circ> snd) \<phi>);
   base_class \<leftarrow>
     (case b of
        None \<Rightarrow> Inr None
      | Some (q', \<psi>s) \<Rightarrow>
          (case resolve_name \<Gamma> q' of
             Some (Type D) \<Rightarrow> do { resolve_type \<Sigma> \<Gamma> (TyExprName q' \<psi>s); Inr (Some D) }
           | _ \<Rightarrow> Inl (not_type_name \<Gamma> q')));
   (case redeclared {} (map fst \<phi>) of Some x \<Rightarrow> Inl (DuplicateField x c) | None \<Rightarrow> Inr ());
   (case base_class of
      Some D \<Rightarrow>
        (case find (\<lambda>x. x \<in> set (field_names \<Sigma> D)) (map fst \<phi>) of
           Some x \<Rightarrow> Inl (InheritedField x c (short_name D))
         | None \<Rightarrow> Inr ())
    | None \<Rightarrow> Inr ())
 }" |
"check_type_def \<Sigma> \<Gamma> (TypeStmt x \<alpha>s \<psi>) = do { resolve_type \<Sigma> \<Gamma> \<psi>; Inr () }"

fun check_top_stmt :: "class_table \<Rightarrow> name \<Rightarrow> cxt \<Rightarrow> top_stmt \<Rightarrow> reason + static_outcome \<times> class_table"
where
"check_top_stmt \<Sigma> q \<Gamma> (Stmt s) = do { R \<leftarrow> check_stmt \<Sigma> \<Gamma> None s; Inr (R, \<Sigma>) }" |
"check_top_stmt \<Sigma> q \<Gamma> (TopSeq t t') = do {
   (R, \<Sigma>') \<leftarrow> check_top_stmt \<Sigma> q \<Gamma> t;
   case R of
     Assigns\<^sub>R \<Delta> \<Rightarrow> do {
       (R', \<Sigma>'') \<leftarrow> check_top_stmt \<Sigma>' q (\<Gamma> \<otimes> \<Delta>) t';
       Inr (Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R R', \<Sigma>'')
     }
   | Returns\<^sub>R \<Rightarrow> Inl TopLevelAssertFalse
 }" |
"check_top_stmt \<Sigma> q \<Gamma> (TypeDefs \<chi>s) =
  (let js = [0..<length \<chi>s];
       \<Delta> = fmap_of_list (map (\<lambda>j. (type_def_name (\<chi>s ! j), type_entry \<Gamma> q \<chi>s j)) js);
       \<Sigma>' = fold (\<lambda>j \<Sigma>''. \<Sigma>'' \<otimes> class_table \<Gamma> q \<chi>s j) js \<Sigma> in
   do {
     those_sum (map (\<lambda>j. check_type_def \<Sigma>' (type_context \<Gamma> q \<chi>s j) (\<chi>s ! j)) js);
     Inr (Assigns\<^sub>R \<Delta>, \<Sigma>')
   })"

end
