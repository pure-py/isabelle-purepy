(* Type resolution, substitution, class definitions and well-formed class tables *)
theory Types
  imports Reasons
begin

fun base_type_lit :: "lit \<Rightarrow> ty"
where
"base_type_lit (LitInt _) = TyPrim int" |
"base_type_lit (LitFloat _) = TyPrim float" |
"base_type_lit (LitString _) = TyPrim str" |
"base_type_lit (LitBool _) = TyPrim bool" |
"base_type_lit LitNone = TyPrim NoneType"

fun base_type :: "ty \<Rightarrow> ty"
where
"base_type (TyLiteral l) = base_type_lit l" |
"base_type \<tau> = \<tau>"

fun literal_type :: "ty \<Rightarrow> bool"
where
"literal_type (TyLiteral _) = True" |
"literal_type _ = False"

fun sized :: "ty \<Rightarrow> bool"
where
"sized (TyList _) = True" |
"sized (TyDict _) = True" |
"sized (TyPrim str) = True" |
"sized (TyTuple _) = True" |
"sized (TyClass C []) = (C = range_class)" |
"sized _ = False"

fun subst :: "ty list \<Rightarrow> var list \<Rightarrow> ty \<Rightarrow> ty"
where
"subst \<tau>s \<alpha>s (TyVar \<alpha>) = (case map_of (zip \<alpha>s \<tau>s) \<alpha> of Some \<tau> \<Rightarrow> \<tau> | None \<Rightarrow> TyVar \<alpha>)" |
"subst \<tau>s \<alpha>s (TyList \<sigma>) = TyList (subst \<tau>s \<alpha>s \<sigma>)" |
"subst \<tau>s \<alpha>s (TyTuple \<sigma>s) = TyTuple (map (subst \<tau>s \<alpha>s) \<sigma>s)" |
"subst \<tau>s \<alpha>s (TyDict \<sigma>) = TyDict (subst \<tau>s \<alpha>s \<sigma>)" |
"subst \<tau>s \<alpha>s (TyCallable \<sigma>s \<sigma>) = TyCallable (map (subst \<tau>s \<alpha>s) \<sigma>s) (subst \<tau>s \<alpha>s \<sigma>)" |
"subst \<tau>s \<alpha>s (TyClass C \<sigma>s) = TyClass C (map (subst \<tau>s \<alpha>s) \<sigma>s)" |
"subst \<tau>s \<alpha>s (TyUnion \<sigma> \<sigma>') = TyUnion (subst \<tau>s \<alpha>s \<sigma>) (subst \<tau>s \<alpha>s \<sigma>')" |
"subst \<tau>s \<alpha>s \<sigma> = \<sigma>"

definition check_predefined :: "cxt \<Rightarrow> var \<Rightarrow> unit may_fail"
where
"check_predefined \<Gamma> x = ensure (fmlookup \<Gamma> x = Some PredefName) (NotPredefinedName x)"

(* Check of predefined name x heading a type expression, which selects the rule for the type expression *)
definition check_type_head :: "cxt \<Rightarrow> var \<Rightarrow> unit may_fail"
where
"check_type_head \<Gamma> x = map_sum (SelectsNoRule JudgementResolveType) id (check_predefined \<Gamma> x)"

definition type_params :: "class_table \<Rightarrow> name \<Rightarrow> var list"
where
"type_params \<Sigma> C =
  (case fmlookup \<Sigma> C of
     Some (ClassDef _ _ \<chi>s i) \<Rightarrow> (case node (\<chi>s ! i) of Dataclass _ \<alpha>s _ _ \<Rightarrow> \<alpha>s | TypeStmt _ _ _ \<Rightarrow> undefined)
   | None \<Rightarrow> undefined)"

definition type_entry :: "cxt \<Rightarrow> name \<Rightarrow> type_def located list \<Rightarrow> nat \<Rightarrow> cxt_entry"
where
"type_entry \<Gamma> q \<chi>s i =
  (case node (\<chi>s ! i) of Dataclass c _ _ _ \<Rightarrow> Type (Qualified q c) | TypeStmt _ _ _ \<Rightarrow> TypeAlias \<Gamma> q \<chi>s i)"

definition type_context :: "cxt \<Rightarrow> name \<Rightarrow> type_def located list \<Rightarrow> nat \<Rightarrow> cxt"
where
"type_context \<Gamma> q \<chi>s i =
  (let entries = \<lambda>js. fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_entry \<Gamma> q \<chi>s j)) js) in
   case node (\<chi>s ! i) of
     TypeStmt _ \<alpha>s _ \<Rightarrow> \<Gamma> \<otimes> entries [0..<length \<chi>s] \<otimes> fmconst (set \<alpha>s) TypeVar
   | Dataclass _ \<alpha>s _ _ \<Rightarrow> \<Gamma> \<otimes> entries [0..<i] \<otimes> fmconst (set \<alpha>s) TypeVar)"

(* A holds the aliases being resolved, so that a cyclic alias is rejected; n bounds the nesting of alias
   resolution, and the number of alias definitions reachable from the context suffices, since the aliases in A
   are distinct *)
fun resolve_type' :: "class_table \<Rightarrow> cxt \<Rightarrow> (name \<times> var) list \<Rightarrow> nat \<Rightarrow> ty_expr \<Rightarrow> ty may_fail"
where
"resolve_type' \<Sigma> \<Gamma> A n (TyExprPrim \<nu>) = do { check_type_head \<Gamma> (prim_name \<nu>); Ok (TyPrim \<nu>) }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprName q \<psi>s) =
  (if \<psi>s = [] \<and> (case q of Simple x \<Rightarrow> fmlookup \<Gamma> x = Some TypeVar | Qualified _ _ \<Rightarrow> False)
   then Ok (TyVar (root q))
   else case resolve_name \<Gamma> q of
     Some (Type C) \<Rightarrow> by_rule RuleTyClass (do {
       \<tau>s \<leftarrow> those_sum (map (resolve_type' \<Sigma> \<Gamma> A n) \<psi>s);
       let m = length (type_params \<Sigma> C);
       if length \<tau>s = m then Ok (TyClass C \<tau>s) else Fail (ClassArityMismatch q m (length \<tau>s))
     })
   | Some (TypeAlias \<Gamma>' q' \<chi>s i) \<Rightarrow>
       (case node (\<chi>s ! i) of
          TypeStmt x \<alpha>s \<psi> \<Rightarrow> by_rule RuleTyAlias (do {
            \<sigma>s \<leftarrow> those_sum (map (resolve_type' \<Sigma> \<Gamma> A n) \<psi>s);
            ensure (length \<sigma>s = length \<alpha>s) (TypeAliasArityMismatch q (length \<alpha>s) (length \<sigma>s));
            ensure ((q', x) \<notin> set A) (Violates RuleTypeAlias (CyclicTypeAlias x));
            \<tau> \<leftarrow> (case n of
                   Suc n' \<Rightarrow> resolve_type' \<Sigma> (type_context \<Gamma>' q' \<chi>s i) ((q', x) # A) n' \<psi>
                 | 0 \<Rightarrow> undefined);
            Ok (subst \<sigma>s \<alpha>s \<tau>)
          })
        | _ \<Rightarrow> undefined)
   | _ \<Rightarrow> Fail (SelectsNoRule JudgementResolveType (not_type_name \<Gamma> q)))" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprLiteral l) = do { check_type_head \<Gamma> (var ''Literal''); Ok (TyLiteral l) }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprList \<psi>) =
  do { check_type_head \<Gamma> (var ''list''); \<tau> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>; Ok (TyList \<tau>) }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprDict \<psi>) = do {
   check_type_head \<Gamma> (var ''dict''); by_rule RuleTyDict (check_predefined \<Gamma> (var ''str''));
   \<tau> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>; Ok (TyDict \<tau>)
 }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprTuple \<psi>s) = do {
   check_type_head \<Gamma> (var ''tuple'');
   \<tau>s \<leftarrow> those_sum (map (resolve_type' \<Sigma> \<Gamma> A n) \<psi>s); Ok (TyTuple \<tau>s)
 }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprCallable \<psi>s \<psi>) = do {
   check_type_head \<Gamma> (var ''Callable'');
   \<sigma>s \<leftarrow> those_sum (map (resolve_type' \<Sigma> \<Gamma> A n) \<psi>s);
   \<tau> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>;
   Ok (TyCallable \<sigma>s \<tau>)
 }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprUnion \<psi> \<psi>') = do {
   \<sigma> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>; \<tau> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>'; Ok (TyUnion \<sigma> \<tau>)
 }"

definition resolve_type :: "class_table \<Rightarrow> cxt \<Rightarrow> ty_expr \<Rightarrow> ty may_fail"
where
"resolve_type \<Sigma> \<Gamma> \<psi> = resolve_type' \<Sigma> \<Gamma> [] (aliases \<Gamma>) \<psi>"

definition base :: "class_table \<Rightarrow> name \<Rightarrow> (name \<times> ty list) option"
where
"base \<Sigma> C =
  (case fmlookup \<Sigma> C of
     Some (ClassDef \<Gamma> q \<chi>s i) \<Rightarrow>
       (case node (\<chi>s ! i) of
          Dataclass _ _ None _ \<Rightarrow> None
        | Dataclass _ _ (Some (q', \<psi>s)) _ \<Rightarrow>
            (case resolve_type \<Sigma> (type_context \<Gamma> q \<chi>s i) (TyExprName q' \<psi>s) of
               Ok (TyClass D \<sigma>s) \<Rightarrow> Some (D, \<sigma>s)
             | _ \<Rightarrow> undefined)
        | TypeStmt _ _ _ \<Rightarrow> undefined)
   | None \<Rightarrow> undefined)"

(* Composition of two substitutions, applied to a type with free type variables among those of the first *)
lemma subst_subst:
  "\<lbrakk> fv \<sigma> \<subseteq> set \<alpha>s ; length \<sigma>s = length \<alpha>s \<rbrakk>
  \<Longrightarrow> subst \<tau>s \<alpha>s' (subst \<sigma>s \<alpha>s \<sigma>) = subst (map (subst \<tau>s \<alpha>s') \<sigma>s) \<alpha>s \<sigma>"
proof (induction \<sigma>)
  case (TyVar \<alpha>)
  then obtain \<tau> where "map_of (zip \<alpha>s \<sigma>s) \<alpha> = Some \<tau>" using map_of_zip_is_Some by fastforce
  with TyVar show ?case by (simp add: map_of_zip_map_snd)
qed (simp_all cong: map_cong, blast+)

lemma subst_base_type_lit [simp]: "subst \<tau>s \<alpha>s (base_type_lit l) = base_type_lit l"
  by (cases l) simp_all

lemma sized_subst: "\<nexists>\<alpha>. \<sigma> = TyVar \<alpha> \<Longrightarrow> sized (subst \<tau>s \<alpha>s \<sigma>) = sized \<sigma>"
  by (cases \<sigma>) (auto elim: sized.elims)

(* Type instantiating only classes of \<Sigma>, each at as many type arguments as it has type parameters *)
fun wf_ty :: "class_table \<Rightarrow> ty \<Rightarrow> bool"
where
"wf_ty \<Sigma> (TyList \<tau>) = wf_ty \<Sigma> \<tau>" |
"wf_ty \<Sigma> (TyTuple \<tau>s) = (\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>)" |
"wf_ty \<Sigma> (TyDict \<tau>) = wf_ty \<Sigma> \<tau>" |
"wf_ty \<Sigma> (TyCallable \<sigma>s \<tau>) = ((\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>) \<and> wf_ty \<Sigma> \<tau>)" |
"wf_ty \<Sigma> (TyClass C \<tau>s) =
  (C |\<in>| fmdom \<Sigma> \<and> length \<tau>s = length (type_params \<Sigma> C) \<and> (\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>))" |
"wf_ty \<Sigma> (TyUnion \<sigma> \<tau>) = (wf_ty \<Sigma> \<sigma> \<and> wf_ty \<Sigma> \<tau>)" |
"wf_ty \<Sigma> _ = True"

lemma wf_ty_subst: "\<lbrakk> wf_ty \<Sigma> \<sigma> ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> (subst \<tau>s \<alpha>s \<sigma>)"
  by (induction \<sigma>) (auto split: option.splits dest!: map_of_SomeD set_zip_rightD)

(* Class table with each base class a well-formed type over the type parameters of its class *)
definition wf_class_table :: "class_table \<Rightarrow> bool"
where
"wf_class_table \<Sigma> =
  (\<forall>C D \<sigma>s. C |\<in>| fmdom \<Sigma> \<longrightarrow> base \<Sigma> C = Some (D, \<sigma>s)
     \<longrightarrow> wf_ty \<Sigma> (TyClass D \<sigma>s) \<and> (\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> set (type_params \<Sigma> C)))"

lemma wf_class_table_base:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> (TyClass C \<tau>s) ; base \<Sigma> C = Some (D, \<sigma>s) \<rbrakk>
  \<Longrightarrow> wf_ty \<Sigma> (TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s))"
  unfolding wf_class_table_def by (auto intro: wf_ty_subst)

(* Base class at substituted type arguments, as the substitution applied to the base class at the type
   arguments *)
lemma base_subst:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> (TyClass C \<tau>s) ; base \<Sigma> C = Some (D, \<sigma>s) \<rbrakk>
  \<Longrightarrow> TyClass D (map (subst (map (subst \<tau>s' \<alpha>s) \<tau>s) (type_params \<Sigma> C)) \<sigma>s) =
      subst \<tau>s' \<alpha>s (TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s))"
  unfolding wf_class_table_def by (auto simp: subst_subst cong: map_cong)

fun instantiate :: "field_scheme \<Rightarrow> ty list \<Rightarrow> (var \<times> ty) list"
where
"instantiate (FieldScheme \<alpha>s x\<sigma>s) \<tau>s = map (\<lambda>(x, \<sigma>). (x, subst \<tau>s \<alpha>s \<sigma>)) x\<sigma>s"

(* Ancestors of class C at type arguments \<tau>s, each with its type arguments, through at most n base classes;
   the base-class relation is acyclic, so the number of classes in \<Sigma> suffices *)
fun instantiated_ancestors_upto :: "nat \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> (name \<times> ty list) list"
where
"instantiated_ancestors_upto 0 \<Sigma> C \<tau>s = undefined" |
"instantiated_ancestors_upto (Suc n) \<Sigma> C \<tau>s =
  (C, \<tau>s) # (case base \<Sigma> C of
                 None \<Rightarrow> []
               | Some (D, \<sigma>s) \<Rightarrow> instantiated_ancestors_upto n \<Sigma> D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s))"

definition instantiated_ancestors :: "class_table \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> (name \<times> ty list) list"
where
"instantiated_ancestors \<Sigma> C \<tau>s = instantiated_ancestors_upto (fcard (fmdom \<Sigma>)) \<Sigma> C \<tau>s"

definition ancestors :: "class_table \<Rightarrow> name \<Rightarrow> name list"
where
"ancestors \<Sigma> C = map fst (instantiated_ancestors \<Sigma> C (map TyVar (type_params \<Sigma> C)))"

(* Type arguments of ancestor D of class C at type arguments \<tau>s *)
definition instantiated_ancestor :: "class_table \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> name \<Rightarrow> ty list"
where
"instantiated_ancestor \<Sigma> C \<tau>s D = the (map_of (instantiated_ancestors \<Sigma> C \<tau>s) D)"

(* Fields declared by class C itself, at type arguments \<tau>s *)
definition declared_fields :: "class_table \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> (var \<times> ty) list"
where
"declared_fields \<Sigma> C \<tau>s =
  (case fmlookup \<Sigma> C of
     Some (ClassDef \<Gamma> q \<chi>s i) \<Rightarrow>
       (case node (\<chi>s ! i) of
          Dataclass _ \<alpha>s _ \<phi> \<Rightarrow>
            map (\<lambda>(x, \<psi>). (x, subst \<tau>s \<alpha>s (projr (resolve_type \<Sigma> (type_context \<Gamma> q \<chi>s i) \<psi>)))) \<phi>
        | TypeStmt _ _ _ \<Rightarrow> undefined)
   | None \<Rightarrow> undefined)"

definition fields :: "class_table \<Rightarrow> name \<Rightarrow> field_scheme"
where
"fields \<Sigma> C =
  (let \<alpha>s = type_params \<Sigma> C in
   FieldScheme \<alpha>s
     (concat (rev (map (\<lambda>(D, \<sigma>s). declared_fields \<Sigma> D \<sigma>s) (instantiated_ancestors \<Sigma> C (map TyVar \<alpha>s))))))"

definition field_types :: "class_table \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> ty list"
where
"field_types \<Sigma> C \<sigma>s = map snd (instantiate (fields \<Sigma> C) \<sigma>s)"

definition field_names :: "class_table \<Rightarrow> name \<Rightarrow> var list"
where
"field_names \<Sigma> C = (case fields \<Sigma> C of FieldScheme _ x\<sigma>s \<Rightarrow> map fst x\<sigma>s)"

definition class_table :: "cxt \<Rightarrow> name \<Rightarrow> type_def located list \<Rightarrow> nat \<Rightarrow> class_table"
where
"class_table \<Gamma> q \<chi>s i =
  (case node (\<chi>s ! i) of
     Dataclass c _ _ _ \<Rightarrow> fmupd (Qualified q c) (ClassDef \<Gamma> q \<chi>s i) fmempty
   | TypeStmt _ _ _ \<Rightarrow> fmempty)"

(* Failure unless n positional arguments and keywords ys supply exactly the fields xs, with arity and unknown as
   helpers for building failure reasons *)
definition check_field_map ::
  "(nat \<Rightarrow> nat \<Rightarrow> reason) \<Rightarrow> (var list \<Rightarrow> reason) \<Rightarrow> var list \<Rightarrow> nat \<Rightarrow> var list \<Rightarrow> unit may_fail"
where
"check_field_map arity unknown xs n ys =
  (if n + length ys \<noteq> length xs then Fail (arity (length xs) (n + length ys))
   else if set ys \<noteq> set (drop n xs) then Fail (unknown (sorted_list_of_set (set (drop n xs))))
   else Ok ())"

(* Type of the field of C supplied by each argument, in order *)
definition constructor_args ::
  "name \<Rightarrow> field_scheme \<Rightarrow> expr located list \<Rightarrow> (var \<times> expr located) list
   \<Rightarrow> (ty \<times> expr located) list may_fail"
where
"constructor_args C \<pi> es kws =
  (case \<pi> of FieldScheme _ x\<sigma>s \<Rightarrow> do {
     check_field_map (ConstructorArityMismatch (short_name C)) (UnknownConstructorKeyword (short_name C))
       (map fst x\<sigma>s) (length es) (map fst kws);
     Ok (zip (map snd (take (length es) x\<sigma>s)) es @ map (\<lambda>(y, e). (the (map_of x\<sigma>s y), e)) kws)
   })"

(* Class of constructor callee e, with the type arguments supplied by e, if any *)
definition constructor_class ::
  "class_table \<Rightarrow> cxt \<Rightarrow> expr located \<Rightarrow> (name \<times> ty list option) may_fail option"
where
"constructor_class \<Sigma> \<Gamma> e =
  (case (class_of_name \<Gamma> (node e), node e) of
     (Some C, _) \<Rightarrow> Some (Ok (C, None))
   | (None, ExprSubscript e' e'') \<Rightarrow>
       if class_of_name \<Gamma> (node e') = None then None
       else
         (case type_expr_of e of
            Some \<psi> \<Rightarrow>
              Some (by_rule RuleConstrExplicit (do {
                \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; case \<tau> of TyClass C \<tau>s \<Rightarrow> Ok (C, Some \<tau>s) | _ \<Rightarrow> undefined
              }))
          | None \<Rightarrow>
              (let e''' = the (find (\<lambda>e'''. type_expr_of e''' = None) (subscript_args e'')) in
               Some (Fail (Located (pos_of e''')
                 (SelectsNoRule JudgementResolveType (NotTypeExpression e'''))))))
   | _ \<Rightarrow> None)"

lemma constructor_args_elem:
  "\<lbrakk> constructor_args C \<pi> es kws = Ok \<sigma>es ; (\<sigma>, e) \<in> set \<sigma>es \<rbrakk> \<Longrightarrow> e \<in> set es \<or> e \<in> set (map snd kws)"
  unfolding constructor_args_def
  by (cases \<pi>) (fastforce simp: bind_sum_def image_iff split: sum.splits dest!: set_zip_rightD)

end
