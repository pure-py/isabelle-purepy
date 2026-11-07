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

lemma fv_base_type_lit [simp]: "fv (base_type_lit l) = {}"
  by (cases l) simp_all

lemma fv_base_type [simp]: "fv (base_type \<tau>) = fv \<tau>"
  by (cases \<tau>) simp_all

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

fun is_union :: "ty \<Rightarrow> bool"
where
"is_union (TyUnion _ _) = True" |
"is_union _ = False"

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

(* Predefined name heading a type expression, checked by successful type resolution *)
lemma resolve_type_head:
  assumes "resolve_type' \<Sigma> \<Gamma> A n \<psi> = Ok \<tau>"
  shows "case \<psi> of
           TyExprLiteral _ \<Rightarrow> fmlookup \<Gamma> (var ''Literal'') = Some PredefName
         | TyExprList _ \<Rightarrow> fmlookup \<Gamma> (var ''list'') = Some PredefName
         | TyExprDict _ \<Rightarrow> fmlookup \<Gamma> (var ''dict'') = Some PredefName
         | TyExprTuple _ \<Rightarrow> fmlookup \<Gamma> (var ''tuple'') = Some PredefName
         | TyExprCallable _ _ \<Rightarrow> fmlookup \<Gamma> (var ''Callable'') = Some PredefName
         | _ \<Rightarrow> True"
  using assms
  by (cases \<psi>)
     (auto simp: check_type_head_def check_predefined_def ensure_def bind_sum_def split: sum.splits if_splits)

(* Type supplied as the type arguments of a class name, as the class at as many type arguments as it has type
   parameters *)
lemma resolve_type_subscript_class:
  assumes C: "class_of_name \<Gamma> (node e') = Some C"
    and \<psi>: "type_expr_of (At p (ExprSubscript e' e'')) = Some \<psi>" and \<tau>: "resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau>"
  shows "\<exists>\<tau>s. \<tau> = TyClass C \<tau>s \<and> length \<tau>s = length (type_params \<Sigma> C)"
proof -
  from C obtain q where q: "dotted_name (node e') = Some q" and entry: "resolve_name \<Gamma> q = Some (Type C)"
    by (auto simp: class_of_name_def entry_of_def bind_eq_Some_conv split: option.splits cxt_entry.splits)
  have head: "fmlookup \<Gamma> x \<noteq> Some PredefName" if "node e' = ExprVar x" for x
    using that q entry by (auto simp: resolve_name_def)
  have \<tau>': "resolve_type' \<Sigma> \<Gamma> [] (aliases \<Gamma>) \<psi> = Ok \<tau>" using \<tau> by (simp add: resolve_type_def)
  from type_expr_of_subscript[OF \<psi>] resolve_type_head[OF \<tau>'] head q obtain \<psi>s where "\<psi> = TyExprName q \<psi>s"
    by auto
  moreover have "\<not> (\<psi>s = [] \<and> (case q of Simple x \<Rightarrow> fmlookup \<Gamma> x = Some TypeVar | Qualified _ _ \<Rightarrow> False))"
    for \<psi>s
    using resolve_name_lookup[OF entry] by (cases q) auto
  ultimately show ?thesis using \<tau>' entry by (auto simp: Let_def bind_sum_def split: sum.splits if_splits)
qed

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

lemma subst_TyVar [simp]: "subst (map TyVar \<alpha>s) \<alpha>s = id"
proof
  fix \<sigma>
  show "subst (map TyVar \<alpha>s) \<alpha>s \<sigma> = id \<sigma>" by (induction \<sigma>) (auto simp: map_of_zip_map intro: map_idI)
qed

lemma subst_fresh: "fv \<tau> \<inter> set \<alpha>s = {} \<Longrightarrow> subst \<tau>s \<alpha>s \<tau> = \<tau>"
proof (induction \<tau>)
  case (TyVar \<alpha>)
  then have "map_of (zip \<alpha>s \<tau>s) \<alpha> = None" by (auto simp: map_of_eq_None_iff dest: set_zip_leftD)
  then show ?case by simp
qed (auto intro: map_idI)

lemma subst_closed: "fv \<tau> = {} \<Longrightarrow> subst \<tau>s \<alpha>s \<tau> = \<tau>"
  by (simp add: subst_fresh)

lemma subst_Nil [simp]: "subst [] \<alpha>s \<tau> = \<tau>"
  by (induction \<tau>) (auto intro: map_idI)

lemma fv_subst: "\<lbrakk> fv \<sigma> \<subseteq> set \<alpha>s ; length \<tau>s = length \<alpha>s \<rbrakk> \<Longrightarrow> fv (subst \<tau>s \<alpha>s \<sigma>) \<subseteq> \<Union> (fv ` set \<tau>s)"
proof (induction \<sigma>)
  case (TyVar \<alpha>)
  then obtain \<tau> where "map_of (zip \<alpha>s \<tau>s) \<alpha> = Some \<tau>" using map_of_zip_is_Some by fastforce
  then show ?case by (auto dest: map_of_SomeD set_zip_rightD)
next
  case (TyTuple \<sigma>s)
  then show ?case by (fastforce simp: UN_subset_iff)
next
  case (TyCallable \<sigma>s \<sigma>)
  then show ?case by (fastforce simp: UN_subset_iff)
next
  case (TyClass C \<sigma>s)
  then show ?case by (fastforce simp: UN_subset_iff)
qed auto

lemma fv_subst_minus:
  "length \<tau>s = length \<alpha>s \<Longrightarrow> fv (subst \<tau>s \<alpha>s \<sigma>) \<subseteq> \<Union> (fv ` set \<tau>s) \<union> (fv \<sigma> - set \<alpha>s)"
proof (induction \<sigma>)
  case (TyVar \<alpha>)
  show ?case
  proof (cases "\<alpha> \<in> set \<alpha>s")
    case True
    with TyVar obtain \<tau> where "map_of (zip \<alpha>s \<tau>s) \<alpha> = Some \<tau>" using map_of_zip_is_Some by fastforce
    then show ?thesis by (auto dest: map_of_SomeD set_zip_rightD)
  next
    case False
    then have "map_of (zip \<alpha>s \<tau>s) \<alpha> = None" by (auto simp: map_of_eq_None_iff dest: set_zip_leftD)
    with False show ?thesis by simp
  qed
qed (fastforce simp: UN_subset_iff)+

(* Composition of two substitutions, applied to the types of a list of pairs, each type with free type variables
   among those of the first *)
lemma map_subst_subst:
  "\<lbrakk> \<forall>(x, \<sigma>) \<in> set x\<sigma>s. fv \<sigma> \<subseteq> set \<alpha>s ; length \<sigma>s = length \<alpha>s \<rbrakk>
  \<Longrightarrow> map (\<lambda>(x, \<sigma>). (x, subst \<tau>s \<alpha>s' \<sigma>)) (map (\<lambda>(x, \<sigma>). (x, subst \<sigma>s \<alpha>s \<sigma>)) x\<sigma>s) =
      map (\<lambda>(x, \<sigma>). (x, subst (map (subst \<tau>s \<alpha>s') \<sigma>s) \<alpha>s \<sigma>)) x\<sigma>s"
  by (induction x\<sigma>s) (auto simp: subst_subst)

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

(* Class C with at most n classes in its chain of base classes, itself included *)
fun inherits_within :: "nat \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> bool"
where
"inherits_within 0 \<Sigma> C = False" |
"inherits_within (Suc n) \<Sigma> C = (case base \<Sigma> C of None \<Rightarrow> True | Some (D, _) \<Rightarrow> inherits_within n \<Sigma> D)"

(* Class table of dataclasses, each with fewer classes in its chain of base classes than the table has, a base
   class other than range which is a well-formed type over its type parameters, declared fields with types over
   them, and distinct field names *)
definition wf_class_table :: "class_table \<Rightarrow> bool"
where
"wf_class_table \<Sigma> =
  (\<forall>C. C |\<in>| fmdom \<Sigma> \<longrightarrow>
     (\<exists>\<Gamma> q \<chi>s i c \<alpha>s b \<phi>. fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i) \<and> node (\<chi>s ! i) = Dataclass c \<alpha>s b \<phi>)
     \<and> inherits_within (fcard (fmdom \<Sigma>)) \<Sigma> C
     \<and> (\<forall>D \<sigma>s. base \<Sigma> C = Some (D, \<sigma>s)
          \<longrightarrow> D \<noteq> range_class \<and> wf_ty \<Sigma> (TyClass D \<sigma>s) \<and> (\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> set (type_params \<Sigma> C)))
     \<and> (\<forall>(x, \<sigma>) \<in> set (declared_fields \<Sigma> C (map TyVar (type_params \<Sigma> C))). fv \<sigma> \<subseteq> set (type_params \<Sigma> C))
     \<and> distinct (field_names \<Sigma> C))"

lemma wf_class_table_dataclass:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>"
  obtains \<Gamma> q \<chi>s i c b \<phi> where "fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i)"
    and "node (\<chi>s ! i) = Dataclass c (type_params \<Sigma> C) b \<phi>"
proof -
  have "\<exists>\<Gamma> q \<chi>s i c \<alpha>s b \<phi>. fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i) \<and> node (\<chi>s ! i) = Dataclass c \<alpha>s b \<phi>"
    using assms unfolding wf_class_table_def by blast
  then obtain \<Gamma> q \<chi>s i c \<alpha>s b \<phi> where "fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i)"
    and "node (\<chi>s ! i) = Dataclass c \<alpha>s b \<phi>"
    by blast
  moreover from this have "type_params \<Sigma> C = \<alpha>s" by (simp add: type_params_def)
  ultimately show thesis using that[of \<Gamma> q \<chi>s i c b \<phi>] by simp
qed

lemma wf_class_table_inherits:
  "\<lbrakk> wf_class_table \<Sigma> ; C |\<in>| fmdom \<Sigma> \<rbrakk> \<Longrightarrow> inherits_within (fcard (fmdom \<Sigma>)) \<Sigma> C"
  unfolding wf_class_table_def by blast

lemma wf_class_table_baseD:
  "\<lbrakk> wf_class_table \<Sigma> ; C |\<in>| fmdom \<Sigma> ; base \<Sigma> C = Some (D, \<sigma>s) \<rbrakk>
  \<Longrightarrow> D \<noteq> range_class \<and> wf_ty \<Sigma> (TyClass D \<sigma>s) \<and> (\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> set (type_params \<Sigma> C))"
  unfolding wf_class_table_def by blast

lemma wf_class_table_declared_fields:
  "\<lbrakk> wf_class_table \<Sigma> ; C |\<in>| fmdom \<Sigma> ; (x, \<sigma>) \<in> set (declared_fields \<Sigma> C (map TyVar (type_params \<Sigma> C))) \<rbrakk>
  \<Longrightarrow> fv \<sigma> \<subseteq> set (type_params \<Sigma> C)"
  unfolding wf_class_table_def by fast

lemma wf_class_table_distinct: "\<lbrakk> wf_class_table \<Sigma> ; C |\<in>| fmdom \<Sigma> \<rbrakk> \<Longrightarrow> distinct (field_names \<Sigma> C)"
  unfolding wf_class_table_def by blast

lemma wf_class_table_base:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> (TyClass C \<tau>s) ; base \<Sigma> C = Some (D, \<sigma>s) \<rbrakk>
  \<Longrightarrow> wf_ty \<Sigma> (TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s))"
  using wf_class_table_baseD[of \<Sigma> C D \<sigma>s] by (auto intro: wf_ty_subst)

(* Base class at substituted type arguments, as the substitution applied to the base class at the type
   arguments *)
lemma base_subst:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> (TyClass C \<tau>s) ; base \<Sigma> C = Some (D, \<sigma>s) \<rbrakk>
  \<Longrightarrow> TyClass D (map (subst (map (subst \<tau>s' \<alpha>s) \<tau>s) (type_params \<Sigma> C)) \<sigma>s) =
      subst \<tau>s' \<alpha>s (TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s))"
  using wf_class_table_baseD[of \<Sigma> C D \<sigma>s] by (auto simp: subst_subst cong: map_cong)

(* Declared fields at type arguments \<tau>s, as the substitution of \<tau>s into the declared fields at the type
   parameters *)
lemma declared_fields_subst:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>"
  shows "declared_fields \<Sigma> C \<tau>s =
         map (\<lambda>(x, \<sigma>). (x, subst \<tau>s (type_params \<Sigma> C) \<sigma>)) (declared_fields \<Sigma> C (map TyVar (type_params \<Sigma> C)))"
proof -
  from assms obtain \<Gamma> q \<chi>s i c b \<phi> where "fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i)"
    and "node (\<chi>s ! i) = Dataclass c (type_params \<Sigma> C) b \<phi>"
    by (rule wf_class_table_dataclass)
  then show ?thesis by (simp add: declared_fields_def case_prod_beta)
qed

lemma instantiated_ancestors_upto_mono:
  "\<lbrakk> inherits_within n \<Sigma> C ; n \<le> m \<rbrakk>
  \<Longrightarrow> instantiated_ancestors_upto m \<Sigma> C \<tau>s = instantiated_ancestors_upto n \<Sigma> C \<tau>s"
proof (induction n arbitrary: m C \<tau>s)
  case (Suc n)
  then obtain m' where "m = Suc m'" and "n \<le> m'" by (cases m) auto
  with Suc show ?case by (auto split: option.splits)
qed simp

(* Fields declared by the ancestors of class C at type arguments \<tau>s, through at most n base classes, from the
   furthest ancestor *)
abbreviation ancestor_fields :: "nat \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> (var \<times> ty) list"
where
"ancestor_fields n \<Sigma> C \<tau>s \<equiv>
  concat (rev (map (\<lambda>(D, \<sigma>s). declared_fields \<Sigma> D \<sigma>s) (instantiated_ancestors_upto n \<Sigma> C \<tau>s)))"

(* Fields of the ancestors of class C at type arguments \<tau>s, as the substitution of \<tau>s into the fields at the
   type parameters, whose types are over the type parameters *)
lemma ancestor_fields_subst:
  assumes "wf_class_table \<Sigma>"
  shows "\<lbrakk> C |\<in>| fmdom \<Sigma> ; inherits_within n \<Sigma> C \<rbrakk> \<Longrightarrow>
    ancestor_fields n \<Sigma> C \<tau>s =
      map (\<lambda>(x, \<sigma>). (x, subst \<tau>s (type_params \<Sigma> C) \<sigma>)) (ancestor_fields n \<Sigma> C (map TyVar (type_params \<Sigma> C)))
    \<and> (\<forall>(x, \<sigma>) \<in> set (ancestor_fields n \<Sigma> C (map TyVar (type_params \<Sigma> C))). fv \<sigma> \<subseteq> set (type_params \<Sigma> C))"
proof (induction n arbitrary: C \<tau>s)
  case 0
  then show ?case by simp
next
  case (Suc n)
  let ?\<alpha>s = "type_params \<Sigma> C"
  show ?case
  proof (cases "base \<Sigma> C")
    case None
    with assms Suc(2) show ?thesis
      by (auto simp: declared_fields_subst[OF assms Suc(2), of \<tau>s] dest: wf_class_table_declared_fields)
  next
    case (Some D\<sigma>s)
    then obtain D \<sigma>s where base: "base \<Sigma> C = Some (D, \<sigma>s)" by (cases D\<sigma>s) simp
    with wf_class_table_baseD[OF assms Suc(2)] have D: "D |\<in>| fmdom \<Sigma>"
      and len: "length \<sigma>s = length (type_params \<Sigma> D)" and fv: "\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> set ?\<alpha>s" by auto
    from Suc(3) base have "inherits_within n \<Sigma> D" by simp
    note IH = Suc.IH[OF D this]
    let ?\<phi> = "ancestor_fields n \<Sigma> D (map TyVar (type_params \<Sigma> D))"
    have fv_D: "\<forall>(x, \<sigma>) \<in> set ?\<phi>. fv \<sigma> \<subseteq> set (type_params \<Sigma> D)" using IH by blast
    have subst_D: "ancestor_fields n \<Sigma> D (map (subst \<tau>s ?\<alpha>s) \<sigma>s) =
          map (\<lambda>(x, \<sigma>). (x, subst \<tau>s ?\<alpha>s \<sigma>)) (ancestor_fields n \<Sigma> D \<sigma>s)"
      using map_subst_subst[OF fv_D len]
      by (simp only: IH[of "map (subst \<tau>s ?\<alpha>s) \<sigma>s", THEN conjunct1] IH[of \<sigma>s, THEN conjunct1])
    have fv_anc: "fv \<sigma> \<subseteq> set ?\<alpha>s" if "(x, \<sigma>) \<in> set (ancestor_fields n \<Sigma> D \<sigma>s)" for x \<sigma>
    proof -
      from that obtain \<sigma>' where "(x, \<sigma>') \<in> set ?\<phi>" and \<sigma>: "\<sigma> = subst \<sigma>s (type_params \<Sigma> D) \<sigma>'"
        unfolding IH[of \<sigma>s, THEN conjunct1] by auto
      with fv_D have "fv \<sigma>' \<subseteq> set (type_params \<Sigma> D)" by blast
      from fv_subst[OF this len] fv show ?thesis unfolding \<sigma> by blast
    qed
    have C: "ancestor_fields (Suc n) \<Sigma> C \<delta>s =
             ancestor_fields n \<Sigma> D (map (subst \<delta>s ?\<alpha>s) \<sigma>s) @ declared_fields \<Sigma> C \<delta>s" for \<delta>s
      using base by simp
    have TyVar: "ancestor_fields (Suc n) \<Sigma> C (map TyVar ?\<alpha>s) =
                 ancestor_fields n \<Sigma> D \<sigma>s @ declared_fields \<Sigma> C (map TyVar ?\<alpha>s)"
      unfolding C by simp
    show ?thesis
    proof
      show "ancestor_fields (Suc n) \<Sigma> C \<tau>s =
            map (\<lambda>(x, \<sigma>). (x, subst \<tau>s ?\<alpha>s \<sigma>)) (ancestor_fields (Suc n) \<Sigma> C (map TyVar ?\<alpha>s))"
        unfolding C[of \<tau>s] TyVar subst_D by (simp add: declared_fields_subst[OF assms Suc(2), of \<tau>s])
      show "\<forall>(x, \<sigma>) \<in> set (ancestor_fields (Suc n) \<Sigma> C (map TyVar ?\<alpha>s)). fv \<sigma> \<subseteq> set ?\<alpha>s"
        unfolding TyVar set_append using fv_anc wf_class_table_declared_fields[OF assms Suc(2)] by blast
    qed
  qed
qed

lemma fields_ancestor_fields:
  "fields \<Sigma> C =
   FieldScheme (type_params \<Sigma> C) (ancestor_fields (fcard (fmdom \<Sigma>)) \<Sigma> C (map TyVar (type_params \<Sigma> C)))"
  by (simp add: fields_def instantiated_ancestors_def Let_def)

lemma instantiate_fields:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>"
  shows "instantiate (fields \<Sigma> C) \<tau>s = ancestor_fields (fcard (fmdom \<Sigma>)) \<Sigma> C \<tau>s"
  using ancestor_fields_subst[OF assms(1, 2) wf_class_table_inherits[OF assms], of \<tau>s]
  by (simp add: fields_ancestor_fields)

lemma fields_fv:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>"
  shows "\<forall>(x, \<sigma>) \<in> set (instantiate (fields \<Sigma> C) (map TyVar (type_params \<Sigma> C))). fv \<sigma> \<subseteq> set (type_params \<Sigma> C)"
  unfolding instantiate_fields[OF assms]
  using ancestor_fields_subst[OF assms(1, 2) wf_class_table_inherits[OF assms]] by (rule conjunct2)

lemma instantiate_fields_subst:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "length \<sigma>s = length (type_params \<Sigma> C)"
  shows "instantiate (fields \<Sigma> C) (map (subst \<tau>s \<alpha>s) \<sigma>s) =
         map (\<lambda>(x, \<sigma>). (x, subst \<tau>s \<alpha>s \<sigma>)) (instantiate (fields \<Sigma> C) \<sigma>s)"
proof -
  obtain x\<sigma>s where fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    by (simp add: fields_ancestor_fields)
  with fields_fv[OF assms(1, 2)] have "\<forall>(x, \<sigma>) \<in> set x\<sigma>s. fv \<sigma> \<subseteq> set (type_params \<Sigma> C)" by simp
  from map_subst_subst[OF this assms(3)] fields show ?thesis by simp
qed

(* Fields of class C at type arguments \<tau>s, as those of its base class at the substituted base class arguments
   followed by those declared by C *)
lemma instantiate_fields_base:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "base \<Sigma> C = Some (D, \<sigma>s)"
  shows "instantiate (fields \<Sigma> C) \<tau>s =
         instantiate (fields \<Sigma> D) (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s) @ declared_fields \<Sigma> C \<tau>s"
proof -
  have within: "inherits_within (fcard (fmdom \<Sigma>)) \<Sigma> C" using assms(1, 2) by (rule wf_class_table_inherits)
  then obtain n where n: "fcard (fmdom \<Sigma>) = Suc n" by (cases "fcard (fmdom \<Sigma>)") simp_all
  with within assms(3) have within_D: "inherits_within n \<Sigma> D" by simp
  have D: "D |\<in>| fmdom \<Sigma>" using wf_class_table_baseD[OF assms] by simp
  have "instantiate (fields \<Sigma> D) \<gamma>s = ancestor_fields n \<Sigma> D \<gamma>s" for \<gamma>s
    by (simp only: instantiate_fields[OF assms(1) D] n
        instantiated_ancestors_upto_mono[OF within_D le_SucI[OF le_refl]])
  with assms(3) show ?thesis by (simp add: instantiate_fields[OF assms(1, 2)] n)
qed

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

(* Class of a constructor callee, as the class of the callee or the class to which the callee applies type
   arguments, which are resolved at the class *)
lemma constructor_class_Ok:
  assumes "constructor_class \<Sigma> \<Gamma> e = Some (Ok (C, explicit))"
  shows "explicit = None \<and> class_of_name \<Gamma> (node e) = Some C
    \<or> (\<exists>e' e'' \<psi> \<tau>s. node e = ExprSubscript e' e'' \<and> class_of_name \<Gamma> (node e') = Some C \<and> explicit = Some \<tau>s
         \<and> resolve_type \<Sigma> \<Gamma> \<psi> = Ok (TyClass C \<tau>s) \<and> length \<tau>s = length (type_params \<Sigma> C))"
proof (cases "class_of_name \<Gamma> (node e)")
  case (Some C')
  with assms show ?thesis by (simp add: constructor_class_def)
next
  case None
  obtain p e0 where e: "e = At p e0" by (cases e)
  have "\<exists>e' e''. e0 = ExprSubscript e' e''"
    using assms None by (cases e0) (simp_all add: constructor_class_def e)
  then obtain e' e'' where e0: "e0 = ExprSubscript e' e''" by blast
  have "\<exists>C' \<psi>. class_of_name \<Gamma> (node e') = Some C' \<and> type_expr_of e = Some \<psi>"
    using assms None by (auto simp: constructor_class_def e e0 Let_def split: option.splits if_splits)
  then obtain C' \<psi> where C': "class_of_name \<Gamma> (node e') = Some C'" and \<psi>: "type_expr_of e = Some \<psi>" by blast
  obtain \<tau> where \<tau>: "resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau>"
    using assms None C' \<psi> by (cases "resolve_type \<Sigma> \<Gamma> \<psi>") (auto simp: constructor_class_def e e0 bind_sum_def)
  from resolve_type_subscript_class[OF C' \<psi>[unfolded e e0] \<tau>] obtain \<tau>s
    where \<tau>': "\<tau> = TyClass C' \<tau>s" and len: "length \<tau>s = length (type_params \<Sigma> C')"
    by blast
  have "C' = C \<and> explicit = Some \<tau>s"
    using assms None C' \<psi> \<tau> \<tau>' by (simp add: constructor_class_def e e0 bind_sum_def)
  with e e0 C' \<tau> \<tau>' len show ?thesis by auto
qed

lemma constructor_args_elem:
  "\<lbrakk> constructor_args C \<pi> es kws = Ok \<sigma>es ; (\<sigma>, e) \<in> set \<sigma>es \<rbrakk> \<Longrightarrow> e \<in> set es \<or> e \<in> set (map snd kws)"
  unfolding constructor_args_def
  by (cases \<pi>) (fastforce simp: bind_sum_def image_iff split: sum.splits dest!: set_zip_rightD)

lemma constructor_args_Ok:
  assumes "constructor_args C (FieldScheme \<alpha>s x\<sigma>s) es kws = Ok \<sigma>es"
  shows "length es + length kws = length x\<sigma>s" and "set (map fst kws) = set (drop (length es) (map fst x\<sigma>s))"
    and "\<sigma>es = zip (map snd (take (length es) x\<sigma>s)) es @ map (\<lambda>(y, e). (the (map_of x\<sigma>s y), e)) kws"
  using assms by (auto simp: constructor_args_def check_field_map_def bind_sum_def split: sum.splits if_splits)

lemma constructor_args_exprs:
  assumes "constructor_args C (FieldScheme \<alpha>s x\<sigma>s) es kws = Ok \<sigma>es"
  shows "map snd \<sigma>es = es @ map snd kws"
    and "map fst \<sigma>es = map snd (take (length es) x\<sigma>s) @ map (\<lambda>(y, _). the (map_of x\<sigma>s y)) kws"
  using constructor_args_Ok(1, 3)[OF assms] by (simp_all add: split_def min_def)

(* Type of the field supplied by each constructor argument, as a field type *)
lemma constructor_args_field:
  assumes "constructor_args C (FieldScheme \<alpha>s x\<sigma>s) es kws = Ok \<sigma>es" and "(\<sigma>, e') \<in> set \<sigma>es"
  shows "\<sigma> \<in> snd ` set x\<sigma>s"
proof -
  note kws = constructor_args_Ok(2)[OF assms(1)]
  from assms(2) constructor_args_Ok(3)[OF assms(1)]
  consider "\<sigma> \<in> set (map snd (take (length es) x\<sigma>s))" | y where "(y, e') \<in> set kws" and "\<sigma> = the (map_of x\<sigma>s y)"
    by (auto dest: set_zip_leftD)
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (auto dest: in_set_takeD)
  next
    case 2
    then have "y \<in> set (map fst kws)" by force
    with kws have "y \<in> set (map fst x\<sigma>s)" by (auto dest: in_set_dropD)
    then obtain \<sigma>' where "map_of x\<sigma>s y = Some \<sigma>'" by (cases "map_of x\<sigma>s y") (auto simp: map_of_eq_None_iff)
    with 2 show ?thesis by (force dest: map_of_SomeD)
  qed
qed

end
