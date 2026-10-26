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

definition check_predefined :: "cxt \<Rightarrow> var \<Rightarrow> reason + unit"
where
"check_predefined \<Gamma> x = ensure (fmlookup \<Gamma> x = Some PredefName) (NotPredefinedName x)"

definition type_params :: "class_table \<Rightarrow> name \<Rightarrow> var list"
where
"type_params \<Sigma> C =
  (case fmlookup \<Sigma> C of
     Some (ClassDef _ _ \<chi>s i) \<Rightarrow> (case \<chi>s ! i of Dataclass _ \<alpha>s _ _ \<Rightarrow> \<alpha>s | TypeStmt _ _ _ \<Rightarrow> undefined)
   | None \<Rightarrow> undefined)"

definition type_entry :: "cxt \<Rightarrow> name \<Rightarrow> type_def list \<Rightarrow> nat \<Rightarrow> cxt_entry"
where
"type_entry \<Gamma> q \<chi>s i =
  (case \<chi>s ! i of Dataclass c _ _ _ \<Rightarrow> Type (snoc q c) | TypeStmt _ _ _ \<Rightarrow> TypeAlias \<Gamma> q \<chi>s i)"

definition type_context :: "cxt \<Rightarrow> name \<Rightarrow> type_def list \<Rightarrow> nat \<Rightarrow> cxt"
where
"type_context \<Gamma> q \<chi>s i =
  (let entries = \<lambda>js. fmap_of_list (map (\<lambda>j. (type_def_name (\<chi>s ! j), type_entry \<Gamma> q \<chi>s j)) js) in
   case \<chi>s ! i of
     TypeStmt _ \<alpha>s _ \<Rightarrow> \<Gamma> \<otimes> entries [0..<length \<chi>s] \<otimes> fmconst (set \<alpha>s) TypeVar
   | Dataclass _ \<alpha>s _ _ \<Rightarrow> \<Gamma> \<otimes> entries [0..<i] \<otimes> fmconst (set \<alpha>s) TypeVar)"

(* A holds the aliases being resolved, so that a cyclic alias is rejected; n bounds the aliases resolved
   along a path, which are distinct, by the alias definitions reachable from the context *)
fun resolve_type' :: "class_table \<Rightarrow> cxt \<Rightarrow> (name \<times> var) list \<Rightarrow> nat \<Rightarrow> ty_expr \<Rightarrow> reason + ty"
where
"resolve_type' \<Sigma> \<Gamma> A n (TyExprPrim \<nu>) = do { check_predefined \<Gamma> (prim_name \<nu>); Inr (TyPrim \<nu>) }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprName q \<psi>s) =
  (if snd q = [] \<and> \<psi>s = [] \<and> fmlookup \<Gamma> (fst q) = Some TypeVar then Inr (TyVar (fst q))
   else case resolve_name \<Gamma> q of
     Some (Type C) \<Rightarrow> do {
       \<tau>s \<leftarrow> those_sum (map (resolve_type' \<Sigma> \<Gamma> A n) \<psi>s);
       let m = length (type_params \<Sigma> C);
       if length \<tau>s = m then Inr (TyClass C \<tau>s) else Inl (ClassArityMismatch q m (length \<tau>s))
     }
   | Some (TypeAlias \<Gamma>' q' \<chi>s i) \<Rightarrow>
       (case \<chi>s ! i of
          TypeStmt x \<alpha>s \<psi> \<Rightarrow> do {
            \<sigma>s \<leftarrow> those_sum (map (resolve_type' \<Sigma> \<Gamma> A n) \<psi>s);
            ensure (length \<sigma>s = length \<alpha>s) (TypeAliasArityMismatch q (length \<alpha>s) (length \<sigma>s));
            ensure ((q', x) \<notin> set A) (CyclicTypeAlias x);
            \<tau> \<leftarrow> (case n of
                   Suc n' \<Rightarrow> resolve_type' \<Sigma> (type_context \<Gamma>' q' \<chi>s i) ((q', x) # A) n' \<psi>
                 | 0 \<Rightarrow> undefined);
            Inr (subst \<sigma>s \<alpha>s \<tau>)
          }
        | _ \<Rightarrow> undefined)
   | _ \<Rightarrow> Inl (not_type_name \<Gamma> q))" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprLiteral l) = do { check_predefined \<Gamma> ''Literal''; Inr (TyLiteral l) }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprList \<psi>) =
  do { check_predefined \<Gamma> ''list''; \<tau> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>; Inr (TyList \<tau>) }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprDict \<psi>) = do {
   check_predefined \<Gamma> ''dict''; check_predefined \<Gamma> ''str''; \<tau> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>; Inr (TyDict \<tau>)
 }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprTuple \<psi>s) = do {
   check_predefined \<Gamma> ''tuple''; \<tau>s \<leftarrow> those_sum (map (resolve_type' \<Sigma> \<Gamma> A n) \<psi>s); Inr (TyTuple \<tau>s)
 }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprCallable \<psi>s \<psi>) = do {
   check_predefined \<Gamma> ''Callable'';
   \<sigma>s \<leftarrow> those_sum (map (resolve_type' \<Sigma> \<Gamma> A n) \<psi>s);
   \<tau> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>;
   Inr (TyCallable \<sigma>s \<tau>)
 }" |
"resolve_type' \<Sigma> \<Gamma> A n (TyExprUnion \<psi> \<psi>') = do {
   \<sigma> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>; \<tau> \<leftarrow> resolve_type' \<Sigma> \<Gamma> A n \<psi>'; Inr (TyUnion \<sigma> \<tau>)
 }"

definition resolve_type :: "class_table \<Rightarrow> cxt \<Rightarrow> ty_expr \<Rightarrow> reason + ty"
where
"resolve_type \<Sigma> \<Gamma> \<psi> = resolve_type' \<Sigma> \<Gamma> [] (aliases \<Gamma>) \<psi>"

definition base :: "class_table \<Rightarrow> name \<Rightarrow> (name \<times> ty list) option"
where
"base \<Sigma> C =
  (case fmlookup \<Sigma> C of
     Some (ClassDef \<Gamma> q \<chi>s i) \<Rightarrow>
       (case \<chi>s ! i of
          Dataclass _ _ None _ \<Rightarrow> None
        | Dataclass _ _ (Some (q', \<psi>s)) _ \<Rightarrow>
            (case resolve_type \<Sigma> (type_context \<Gamma> q \<chi>s i) (TyExprName q' \<psi>s) of
               Inr (TyClass D \<sigma>s) \<Rightarrow> Some (D, \<sigma>s)
             | _ \<Rightarrow> undefined)
        | TypeStmt _ _ _ \<Rightarrow> undefined)
   | None \<Rightarrow> undefined)"

fun instantiate :: "field_scheme \<Rightarrow> ty list \<Rightarrow> (var \<times> ty) list"
where
"instantiate (FieldScheme \<alpha>s x\<sigma>s) \<tau>s = map (\<lambda>(x, \<sigma>). (x, subst \<tau>s \<alpha>s \<sigma>)) x\<sigma>s"

(* Fields of class C, through at most n base classes; the base-class relation is acyclic, so the number of
   classes in \<Sigma> suffices *)
fun fields_upto :: "nat \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> field_scheme"
where
"fields_upto 0 \<Sigma> C = undefined" |
"fields_upto (Suc n) \<Sigma> C =
  (case fmlookup \<Sigma> C of
     Some (ClassDef \<Gamma> q \<chi>s i) \<Rightarrow>
       (case \<chi>s ! i of
          Dataclass _ \<alpha>s _ \<phi> \<Rightarrow>
            let own = map (\<lambda>(x, \<psi>). (x, projr (resolve_type \<Sigma> (type_context \<Gamma> q \<chi>s i) \<psi>))) \<phi> in
            FieldScheme \<alpha>s
              (case base \<Sigma> C of None \<Rightarrow> own | Some (D, \<sigma>s) \<Rightarrow> instantiate (fields_upto n \<Sigma> D) \<sigma>s @ own)
        | TypeStmt _ _ _ \<Rightarrow> undefined)
   | None \<Rightarrow> undefined)"

definition fields :: "class_table \<Rightarrow> name \<Rightarrow> field_scheme"
where
"fields \<Sigma> C = fields_upto (fcard (fmdom \<Sigma>)) \<Sigma> C"

(* Class C and its base classes, through at most n of them *)
fun ancestors_upto :: "nat \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> name list"
where
"ancestors_upto 0 \<Sigma> C = undefined" |
"ancestors_upto (Suc n) \<Sigma> C = C # (case base \<Sigma> C of None \<Rightarrow> [] | Some (D, _) \<Rightarrow> ancestors_upto n \<Sigma> D)"

definition ancestors :: "class_table \<Rightarrow> name \<Rightarrow> name list"
where
"ancestors \<Sigma> C = ancestors_upto (fcard (fmdom \<Sigma>)) \<Sigma> C"

(* Type arguments of ancestor D of class C at type arguments \<tau>s, through at most n base classes *)
fun instantiated_ancestor_upto :: "nat \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> name \<Rightarrow> ty list"
where
"instantiated_ancestor_upto 0 \<Sigma> C \<tau>s D = undefined" |
"instantiated_ancestor_upto (Suc n) \<Sigma> C \<tau>s D =
  (if C = D then \<tau>s
   else case base \<Sigma> C of
     Some (D', \<sigma>s) \<Rightarrow> instantiated_ancestor_upto n \<Sigma> D' (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s) D
   | None \<Rightarrow> undefined)"

definition instantiated_ancestor :: "class_table \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> name \<Rightarrow> ty list"
where
"instantiated_ancestor \<Sigma> C \<tau>s D = instantiated_ancestor_upto (fcard (fmdom \<Sigma>)) \<Sigma> C \<tau>s D"

definition field_names :: "class_table \<Rightarrow> name \<Rightarrow> var list"
where
"field_names \<Sigma> C = (case fields \<Sigma> C of FieldScheme _ x\<sigma>s \<Rightarrow> map fst x\<sigma>s)"

definition class_table :: "cxt \<Rightarrow> name \<Rightarrow> type_def list \<Rightarrow> nat \<Rightarrow> class_table"
where
"class_table \<Gamma> q \<chi>s i =
  (case \<chi>s ! i of
     Dataclass c _ _ _ \<Rightarrow> fmupd (snoc q c) (ClassDef \<Gamma> q \<chi>s i) fmempty
   | TypeStmt _ _ _ \<Rightarrow> fmempty)"

definition check_field_map :: "name \<Rightarrow> var list \<Rightarrow> nat \<Rightarrow> var list \<Rightarrow> reason + unit"
where
"check_field_map C xs n ys =
  (if n + length ys \<noteq> length xs then Inl (ConstructorArityMismatch (short_name C) (length xs) (n + length ys))
   else if set ys \<noteq> set (drop n xs)
   then Inl (UnknownConstructorKeyword (short_name C) (sorted_list_of_set (set (drop n xs))))
   else Inr ())"

(* Type of the field of C supplied by each argument, in order *)
definition constructor_args ::
  "name \<Rightarrow> field_scheme \<Rightarrow> expr list \<Rightarrow> (var \<times> expr) list \<Rightarrow> reason + (ty \<times> expr) list"
where
"constructor_args C \<pi> es kws =
  (case \<pi> of FieldScheme _ x\<sigma>s \<Rightarrow> do {
     check_field_map C (map fst x\<sigma>s) (length es) (map fst kws);
     Inr (zip (map snd (take (length es) x\<sigma>s)) es @ map (\<lambda>(y, e). (the (map_of x\<sigma>s y), e)) kws)
   })"

(* Class of constructor callee e, with its type arguments if explicit *)
definition constructor_class :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> (reason + name \<times> ty list option) option"
where
"constructor_class \<Sigma> \<Gamma> e =
  (case (class_of_name \<Gamma> e, e) of
     (Some C, _) \<Rightarrow> Some (Inr (C, None))
   | (None, ExprSubscript e' _) \<Rightarrow>
       if class_of_name \<Gamma> e' = None then None
       else
         (case parse_annotation e of
            Some \<psi> \<Rightarrow>
              Some (do { \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; case \<tau> of TyClass C \<tau>s \<Rightarrow> Inr (C, Some \<tau>s) | _ \<Rightarrow> undefined })
          | None \<Rightarrow> undefined)
   | _ \<Rightarrow> None)"

lemma constructor_args_elem:
  "\<lbrakk> constructor_args C \<pi> es kws = Inr \<sigma>es ; (\<sigma>, e) \<in> set \<sigma>es \<rbrakk> \<Longrightarrow> e \<in> set es \<or> e \<in> set (map snd kws)"
  unfolding constructor_args_def
  by (cases \<pi>) (fastforce simp: bind_sum_def image_iff split: sum.splits dest!: set_zip_rightD)

end
