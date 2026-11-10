(* Well-formedness of the class tables and contexts produced by type regions and modules *)
theory WellFormedModules
  imports ExtensionStatements
begin

subsection \<open>Class tables of type regions\<close>

(* Class table \<Sigma> extended with the classes of type region \<chi>s of module q, defined in context \<Gamma> *)
abbreviation region_table :: "cxt \<Rightarrow> name \<Rightarrow> type_def located list \<Rightarrow> class_table \<Rightarrow> class_table"
where "region_table \<Gamma> q \<chi>s \<Sigma> \<equiv> fold (\<lambda>j \<Sigma>'. \<Sigma>' \<otimes> class_table \<Gamma> q \<chi>s j) [0..<length \<chi>s] \<Sigma>"

(* Definition j of type region \<chi>s is a class named c *)
abbreviation defines_class :: "type_def located list \<Rightarrow> nat \<Rightarrow> var \<Rightarrow> bool"
where "defines_class \<chi>s j c \<equiv> \<exists>\<alpha>s b \<phi>. node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>"

lemma fmlookup_add_in: "x |\<in>| fmdom n \<Longrightarrow> fmlookup (m \<otimes> n) x = fmlookup n x"
  and fmlookup_add_notin: "x |\<notin>| fmdom n \<Longrightarrow> fmlookup (m \<otimes> n) x = fmlookup m x"
  by simp_all

lemma class_table_lookup:
  "fmlookup (class_table \<Gamma> q \<chi>s j) C =
   (case node (\<chi>s ! j) of
      Dataclass c _ _ _ \<Rightarrow> if C = Qualified q c then Some (ClassDef \<Gamma> q \<chi>s j) else None
    | TypeStmt _ _ _ \<Rightarrow> None)"
  by (simp add: class_table_def split: type_def.splits)

lemma class_table_dom:
  "fmdom (class_table \<Gamma> q \<chi>s j) =
   (case node (\<chi>s ! j) of Dataclass c _ _ _ \<Rightarrow> {|Qualified q c|} | TypeStmt _ _ _ \<Rightarrow> {||})"
  by (simp add: class_table_def split: type_def.splits)

lemma fold_class_table_notin:
  "\<forall>j \<in> set js. \<forall>c. defines_class \<chi>s j c \<longrightarrow> C \<noteq> Qualified q c
  \<Longrightarrow> fmlookup (fold (\<lambda>j \<Sigma>'. \<Sigma>' \<otimes> class_table \<Gamma> q \<chi>s j) js \<Sigma>) C = fmlookup \<Sigma> C"
proof (induction js arbitrary: \<Sigma>)
  case (Cons j js)
  have "fmlookup (\<Sigma> \<otimes> class_table \<Gamma> q \<chi>s j) C = fmlookup \<Sigma> C"
    using Cons.prems by (auto simp: class_table_lookup split: type_def.splits)
  with Cons show ?case by simp
qed simp

lemma fold_class_table_in:
  "\<lbrakk> distinct js ; j \<in> set js ; node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>
   ; \<forall>j' \<in> set js. j' \<noteq> j \<longrightarrow> type_def_name (node (\<chi>s ! j')) \<noteq> c \<rbrakk>
  \<Longrightarrow> fmlookup (fold (\<lambda>j \<Sigma>'. \<Sigma>' \<otimes> class_table \<Gamma> q \<chi>s j) js \<Sigma>) (Qualified q c) = Some (ClassDef \<Gamma> q \<chi>s j)"
proof (induction js arbitrary: \<Sigma>)
  case (Cons j' js)
  show ?case
  proof (cases "j' = j")
    case True
    have "\<forall>j'' \<in> set js. \<forall>c'. defines_class \<chi>s j'' c' \<longrightarrow> Qualified q c \<noteq> Qualified q c'"
      using Cons.prems(1, 4) True by fastforce
    from fold_class_table_notin[OF this] Cons.prems(3) True show ?thesis
      by (simp add: class_table_lookup class_table_dom)
  next
    case False
    with Cons.IH[of "\<Sigma> \<otimes> class_table \<Gamma> q \<chi>s j'"] Cons.prems show ?thesis by simp
  qed
qed simp

lemma fold_class_table_dom:
  "C |\<in>| fmdom (fold (\<lambda>j \<Sigma>'. \<Sigma>' \<otimes> class_table \<Gamma> q \<chi>s j) js \<Sigma>)
   \<longleftrightarrow> C |\<in>| fmdom \<Sigma> \<or> (\<exists>j \<in> set js. \<exists>c. defines_class \<chi>s j c \<and> C = Qualified q c)"
proof (induction js arbitrary: \<Sigma>)
  case (Cons j js)
  have "C |\<in>| fmdom (\<Sigma> \<otimes> class_table \<Gamma> q \<chi>s j) \<longleftrightarrow> C |\<in>| fmdom \<Sigma> \<or> (\<exists>c. defines_class \<chi>s j c \<and> C = Qualified q c)"
    by (auto simp: class_table_dom split: type_def.splits)
  with Cons.IH[of "\<Sigma> \<otimes> class_table \<Gamma> q \<chi>s j"] show ?case by auto
qed simp

lemma region_table_subset:
  assumes "\<forall>j < length \<chi>s. \<forall>c. defines_class \<chi>s j c \<longrightarrow> Qualified q c |\<notin>| fmdom \<Sigma>"
  shows "\<Sigma> \<subseteq>\<^sub>f region_table \<Gamma> q \<chi>s \<Sigma>"
proof -
  have "fmlookup (region_table \<Gamma> q \<chi>s \<Sigma>) C = Some ce" if "fmlookup \<Sigma> C = Some ce" for C ce
  proof -
    have "\<forall>j \<in> set [0..<length \<chi>s]. \<forall>c. defines_class \<chi>s j c \<longrightarrow> C \<noteq> Qualified q c"
      using assms that by (auto simp: fmlookup_dom_iff)
    from fold_class_table_notin[OF this] that show ?thesis by simp
  qed
  then show ?thesis by (auto simp: fmsubset_alt_def fmpred_iff)
qed

lemma fmadd_absorb: "m \<subseteq>\<^sub>f n \<Longrightarrow> n \<otimes> m = n"
  by (rule fmap_ext) (auto simp: fmsubset_alt_def fmpred_iff split: option.splits)

(* Classes of a type region already in the table, added again *)
lemma fold_class_table_fixed:
  "\<forall>j \<in> set js. class_table \<Gamma> q \<chi>s j \<subseteq>\<^sub>f \<Sigma> \<Longrightarrow> fold (\<lambda>j \<Sigma>'. \<Sigma>' \<otimes> class_table \<Gamma> q \<chi>s j) js \<Sigma> = \<Sigma>"
  by (induction js) (simp_all add: fmadd_absorb)

lemma inherits_within_mono: "\<lbrakk> inherits_within n \<Sigma> C ; n \<le> m \<rbrakk> \<Longrightarrow> inherits_within m \<Sigma> C"
proof (induction n arbitrary: m C)
  case (Suc n)
  then obtain m' where "m = Suc m'" and "n \<le> m'" by (cases m) auto
  with Suc show ?case by (auto split: option.splits)
qed simp

lemma those_sum_map_Ok_all: "\<lbrakk> those_sum (map f xs) = Ok ys ; x \<in> set xs \<rbrakk> \<Longrightarrow> \<exists>y. f x = Ok y"
  using those_sum_map_Ok[of f xs ys] by (auto simp: list_all2_conv_all_nth in_set_conv_nth)

subsection \<open>Contexts of type definitions\<close>

lemma type_entry_fv [simp]: "fv_entry (type_entry \<Gamma> q \<chi>s j) = {}"
  by (simp add: type_entry_def split: type_def.splits)

lemma type_entry_TypeVar [simp]: "type_entry \<Gamma> q \<chi>s j \<noteq> TypeVar" "TypeVar \<noteq> type_entry \<Gamma> q \<chi>s j"
  by (simp_all add: type_entry_def split: type_def.splits)

lemma tyvars_add3: "tyvars (\<Gamma> \<otimes> \<Delta> \<otimes> \<Delta>') \<subseteq> tyvars \<Gamma> \<union> tyvars \<Delta> \<union> tyvars \<Delta>'"
  using tyvars_add[of "\<Gamma> \<otimes> \<Delta>" \<Delta>'] tyvars_add[of \<Gamma> \<Delta>] by blast

(* Context in which definition i of a type region is checked, well-formed when the classes of the region are in
   the table *)
lemma type_context_wf:
  assumes "tyvars \<Gamma> = {}" and "wf_cxt \<Sigma> \<Gamma>" and "i < length \<chi>s"
    and "\<forall>\<chi> \<in> set \<chi>s. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q c |\<in>| fmdom \<Sigma>"
  shows "wf_cxt \<Sigma> (type_context \<Gamma> q \<chi>s i)"
proof (cases "node (\<chi>s ! i)")
  case (Dataclass c \<alpha>s b \<phi>)
  from type_context_dataclass_wf[OF assms this] show ?thesis .
next
  case (TypeStmt x \<alpha>s \<psi>)
  with assms have "wf_entry \<Sigma> (TypeAlias \<Gamma> q \<chi>s i)" by simp
  from type_context_alias(1)[OF this TypeStmt] show ?thesis .
qed

(* Type variables of the context of definition i of a type region: the type parameters of the definition *)
lemma type_context_tyvars:
  assumes "tyvars \<Gamma> = {}"
    and "node (\<chi>s ! i) = Dataclass c \<alpha>s b \<phi> \<or> node (\<chi>s ! i) = TypeStmt x \<alpha>s \<psi>"
  shows "tyvars (type_context \<Gamma> q \<chi>s i) \<subseteq> set \<alpha>s"
proof -
  have entries: "tyvars (fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_entry \<Gamma> q \<chi>s j)) js)) = {}"
    for js
    by (rule tyvars_empty) (auto simp: fmlookup_of_list dest!: map_of_SomeD)
  have *: "tyvars (\<Gamma> \<otimes> fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_entry \<Gamma> q \<chi>s j)) js)
          \<otimes> fmconst (set \<alpha>s) TypeVar) \<subseteq> set \<alpha>s" for js
    using tyvars_add3 assms(1) entries tyvars_fmconst by blast
  from assms(2) show ?thesis
  proof
    assume "node (\<chi>s ! i) = Dataclass c \<alpha>s b \<phi>"
    then show ?thesis using *[of "[0..<i]"] by (simp add: type_context_def Let_def)
  next
    assume "node (\<chi>s ! i) = TypeStmt x \<alpha>s \<psi>"
    then show ?thesis using *[of "[0..<length \<chi>s]"] by (simp add: type_context_def Let_def)
  qed
qed

(* Lookup of a module through a context extended by entries other than checked modules *)
lemma lookup_add_module:
  assumes "\<forall>x \<theta>. fmlookup \<Delta> x = Some \<theta> \<longrightarrow> (\<forall>q \<Gamma>'. \<theta> \<noteq> ModChecked q \<Gamma>')"
    and "lookup (\<Gamma> \<otimes> \<Delta>) p = Some (ModChecked q \<Gamma>')"
  shows "lookup \<Gamma> p = Some (ModChecked q \<Gamma>')"
  using assms(2)
proof (induction p arbitrary: q \<Gamma>')
  case (Simple x)
  then show ?case using assms(1) by (auto simp: fmlookup_dom_iff split: if_splits)
next
  case (Qualified p x)
  then show ?case by (auto split: option.splits cxt_entry.splits)
qed

(* Class named in the context of a class definition of a type region: in the defining context, or an earlier
   class of the region *)
lemma type_context_class:
  assumes "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" and "resolve_name (type_context \<Gamma> q \<chi>s j) q' = Some (Type D)"
  shows "resolve_name \<Gamma> q' = Some (Type D) \<or> (\<exists>j' < j. \<exists>c'. defines_class \<chi>s j' c' \<and> D = Qualified q c')"
proof -
  let ?\<Delta> = "fmap_of_list (map (\<lambda>j'. (type_def_name (node (\<chi>s ! j')), type_entry \<Gamma> q \<chi>s j')) [0..<j])
             \<otimes> fmconst (set \<alpha>s) TypeVar"
  have cxt: "type_context \<Gamma> q \<chi>s j = \<Gamma> \<otimes> ?\<Delta>" by (simp add: type_context_def Let_def assms(1))
  have entries: "\<theta> = TypeVar \<or> (\<exists>j' < j. \<theta> = type_entry \<Gamma> q \<chi>s j')" if "fmlookup ?\<Delta> x = Some \<theta>" for x \<theta>
  proof (cases "x |\<in>| fmdom (fmconst (set \<alpha>s) TypeVar)")
    case True
    with that show ?thesis by (auto dest: fmconst_entry)
  next
    case False
    with that have "map_of (map (\<lambda>j'. (type_def_name (node (\<chi>s ! j')), type_entry \<Gamma> q \<chi>s j')) [0..<j]) x = Some \<theta>"
      by (simp add: fmlookup_of_list)
    then obtain j' where "j' < j" and "\<theta> = type_entry \<Gamma> q \<chi>s j'" by (auto dest!: map_of_SomeD)
    then show ?thesis by blast
  qed
  have no_module: "\<forall>x \<theta>. fmlookup ?\<Delta> x = Some \<theta> \<longrightarrow> (\<forall>q'' \<Gamma>'. \<theta> \<noteq> ModChecked q'' \<Gamma>')"
    using entries by (fastforce simp: type_entry_def split: type_def.splits)
  show ?thesis
  proof (cases q')
    case (Simple x)
    with assms(2) have look: "fmlookup (\<Gamma> \<otimes> ?\<Delta>) x = Some (Type D)"
      by (auto simp: cxt resolve_name_def split: option.splits cxt_entry.splits)
    show ?thesis
    proof (cases "x |\<in>| fmdom ?\<Delta>")
      case False
      from look[unfolded fmlookup_add_notin[OF False]] show ?thesis by (simp add: Simple resolve_name_def)
    next
      case True
      then obtain \<theta> where \<theta>: "fmlookup ?\<Delta> x = Some \<theta>" unfolding fmlookup_dom_iff by blast
      with look[unfolded fmlookup_add_in[OF True]] have "\<theta> = Type D" by simp
      with entries[OF \<theta>] obtain j' where "j' < j" and "type_entry \<Gamma> q \<chi>s j' = Type D" by auto
      then show ?thesis by (auto simp: type_entry_def split: type_def.splits)
    qed
  next
    case (Qualified p x)
    with assms(2) obtain q'' \<Gamma>' where look: "lookup (\<Gamma> \<otimes> ?\<Delta>) p = Some (ModChecked q'' \<Gamma>')"
      and "fmlookup \<Gamma>' x = Some (Type D)"
      by (auto simp: cxt resolve_name_def split: option.splits cxt_entry.splits)
    with lookup_add_module[OF no_module look] show ?thesis by (simp add: Qualified resolve_name_def)
  qed
qed

(* Class name applied to type arguments, resolved to the class at those arguments *)
lemma resolve_type_class:
  assumes "resolve_name \<Gamma> q = Some (Type D)" and "resolve_type \<Sigma> \<Gamma> (TyExprName q \<psi>s) = Ok \<tau>"
  shows "\<exists>\<sigma>s. \<tau> = TyClass D \<sigma>s"
proof -
  have "\<not> (\<psi>s = [] \<and> (case q of Simple x \<Rightarrow> fmlookup \<Gamma> x = Some TypeVar | Qualified _ _ \<Rightarrow> False))"
    using assms(1) by (cases q) (auto simp: resolve_name_def)
  with assms show ?thesis by (auto simp: resolve_type_def bind_sum_Ok Let_def split: if_splits)
qed

subsection \<open>Fields\<close>

lemma fst_case_prod [simp]: "fst (case xy of (x, y) \<Rightarrow> (x, f x y)) = fst xy"
  by (cases xy) simp

lemma declared_fields_names: "map fst (declared_fields \<Sigma> C \<tau>s) = map fst (declared_fields \<Sigma> C \<tau>s')"
  by (simp add: declared_fields_def split: option.splits class_entry.splits type_def.splits)

lemma ancestor_fields_names: "map fst (ancestor_fields n \<Sigma> C \<tau>s) = map fst (ancestor_fields n \<Sigma> C \<tau>s')"
proof (induction n arbitrary: C \<tau>s \<tau>s')
  case (Suc n)
  show ?case
  proof (cases "base \<Sigma> C")
    case (Some D\<sigma>s)
    then obtain D \<sigma>s where "base \<Sigma> C = Some (D, \<sigma>s)" by (cases D\<sigma>s) simp
    with Suc.IH[of D] show ?thesis by (simp add: declared_fields_names[of \<Sigma> C \<tau>s \<tau>s'])
  qed (simp add: declared_fields_names[of \<Sigma> C \<tau>s \<tau>s'])
qed simp

(* Field names of a class without a base class: those it declares *)
lemma field_names_no_base:
  assumes "fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i)" and "node (\<chi>s ! i) = Dataclass c \<alpha>s b \<phi>"
    and "base \<Sigma> C = None"
  shows "field_names \<Sigma> C = map fst \<phi>"
proof -
  obtain n where n: "fcard (fmdom \<Sigma>) = Suc n" using fcard_fmdom_Suc[OF fmdomI[OF assms(1)]] by blast
  show ?thesis
    using assms by (simp add: field_names_def fields_ancestor_fields n declared_fields_def)
qed

(* Field names of a class with a base class: those of the base class followed by those it declares *)
lemma field_names_base:
  assumes "fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i)" and "node (\<chi>s ! i) = Dataclass c \<alpha>s b \<phi>"
    and "base \<Sigma> C = Some (D, \<sigma>s)" and "inherits_within (fcard (fmdom \<Sigma>)) \<Sigma> C"
  shows "field_names \<Sigma> C = field_names \<Sigma> D @ map fst \<phi>"
proof -
  obtain n where n: "fcard (fmdom \<Sigma>) = Suc n" using assms(4) by (cases "fcard (fmdom \<Sigma>)") simp_all
  have D: "inherits_within n \<Sigma> D" using assms(3, 4) n by simp
  have declared: "map fst (declared_fields \<Sigma> C \<tau>s) = map fst \<phi>" for \<tau>s
    using assms(1, 2) by (simp add: declared_fields_def)
  have "field_names \<Sigma> C
    = map fst (ancestor_fields n \<Sigma> D (map (subst (map TyVar (type_params \<Sigma> C)) (type_params \<Sigma> C)) \<sigma>s)) @ map fst \<phi>"
    by (simp add: field_names_def fields_ancestor_fields n assms(3) declared)
  moreover have "map fst (ancestor_fields n \<Sigma> D \<tau>s) = field_names \<Sigma> D" for \<tau>s
    unfolding field_names_def fields_ancestor_fields n field_scheme.case
      instantiated_ancestors_upto_mono[OF D le_SucI[OF le_refl]]
    by (rule ancestor_fields_names)
  ultimately show ?thesis by simp
qed

subsection \<open>Checking of class definitions\<close>

lemma bind_sum_OkE: "\<lbrakk> bind_sum m f = Ok y ; \<And>x. \<lbrakk> m = Ok x ; f x = Ok y \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  by (auto simp: bind_sum_Ok)

(* Facts established by checking a class definition *)
lemma check_dataclass_Ok:
  assumes "check_type_def \<Sigma> \<Gamma> (At p (Dataclass c \<alpha>s b \<phi>)) = Ok ()"
  shows "distinct \<alpha>s \<and> distinct (map fst \<phi>) \<and> (\<forall>(x, \<psi>) \<in> set \<phi>. \<exists>\<tau>. resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau>)
    \<and> (\<forall>q' \<psi>s. b = Some (q', \<psi>s) \<longrightarrow>
         (\<exists>D \<sigma>s. resolve_name \<Gamma> q' = Some (Type D) \<and> D \<noteq> range_class
            \<and> resolve_type \<Sigma> \<Gamma> (TyExprName q' \<psi>s) = Ok (TyClass D \<sigma>s)
            \<and> (\<forall>x \<in> set (map fst \<phi>). x \<notin> set (field_names \<Sigma> D))))"
  using assms
  unfolding check_type_def.simps locate_Ok by_rule_Ok
  apply (elim bind_sum_OkE)
  apply (intro conjI allI impI)
     apply (fastforce split: option.splits dest: redeclared_None)
    apply (fastforce split: option.splits dest: redeclared_None)
   apply (fastforce dest: those_sum_map_Ok_all)
  apply (clarsimp simp: bind_sum_Ok split: option.splits cxt_entry.splits if_splits)
  apply (auto simp: find_None_iff dest: resolve_type_class)
  done

subsection \<open>Well-formed class tables of type regions\<close>

(* Class table of a type region checked from a well-formed table in which its classes are fresh *)
lemma region_table_wf:
  assumes wf: "wf_class_table \<Sigma>" and pre: "predefined_classes \<subseteq>\<^sub>f \<Sigma>"
    and \<Gamma>: "wf_cxt \<Sigma> \<Gamma>" and tyvars: "tyvars \<Gamma> = {}"
    and fresh: "\<forall>j < length \<chi>s. \<forall>c. defines_class \<chi>s j c \<longrightarrow> Qualified q c |\<notin>| fmdom \<Sigma>"
    and distinct: "distinct (map (type_def_name \<circ> node) \<chi>s)"
    and chk: "\<forall>j < length \<chi>s. check_type_def (region_table \<Gamma> q \<chi>s \<Sigma>) (type_context \<Gamma> q \<chi>s j) (\<chi>s ! j) = Ok ()"
  shows "wf_class_table (region_table \<Gamma> q \<chi>s \<Sigma>)"
proof -
  let ?\<Sigma>' = "region_table \<Gamma> q \<chi>s \<Sigma>"
  let ?N = "fcard (fmdom \<Sigma>)"
  have names: "type_def_name (node (\<chi>s ! j')) \<noteq> c"
    if "j < length \<chi>s" and "j' < length \<chi>s" and "j' \<noteq> j" and "defines_class \<chi>s j c" for j j' c
  proof -
    from that(4) have "type_def_name (node (\<chi>s ! j)) = c" by auto
    with distinct that(1-3) show ?thesis by (auto simp: distinct_conv_nth)
  qed
  have new: "fmlookup ?\<Sigma>' (Qualified q c) = Some (ClassDef \<Gamma> q \<chi>s j)"
    if "j < length \<chi>s" and "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" for j c \<alpha>s b \<phi>
  proof (rule fold_class_table_in)
    show "\<forall>j' \<in> set [0..<length \<chi>s]. j' \<noteq> j \<longrightarrow> type_def_name (node (\<chi>s ! j')) \<noteq> c"
      using names[OF that(1)] that(2) by auto
  qed (use that in simp_all)
  have old: "fmlookup ?\<Sigma>' C = fmlookup \<Sigma> C" if "C |\<in>| fmdom \<Sigma>" for C
    using fresh that by (intro fold_class_table_notin) auto
  have dom: "C |\<in>| fmdom ?\<Sigma>' \<longleftrightarrow> C |\<in>| fmdom \<Sigma> \<or> (\<exists>j < length \<chi>s. \<exists>c. defines_class \<chi>s j c \<and> C = Qualified q c)"
    for C
    by (auto simp: fold_class_table_dom)
  have region: "\<forall>\<chi> \<in> set \<chi>s. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q c |\<in>| fmdom ?\<Sigma>'"
    by (auto simp: dom in_set_conv_nth)
  have sub: "\<Sigma> \<subseteq>\<^sub>f ?\<Sigma>'" by (rule region_table_subset[OF fresh])
  interpret extension \<Sigma> ?\<Sigma>' by unfold_locales (fact wf sub pre)+
  have dom_sub: "fmdom \<Sigma> |\<subseteq>| fmdom ?\<Sigma>'" by (auto intro: dom_ext)
  have params: "type_params ?\<Sigma>' (Qualified q c) = \<alpha>s"
    if "j < length \<chi>s" and "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" for j c \<alpha>s b \<phi>
    using new[OF that] that(2) by (simp add: type_params_def)
  have cxt: "wf_cxt ?\<Sigma>' (type_context \<Gamma> q \<chi>s j)" if "j < length \<chi>s" for j
    using tyvars wf_cxt_ext[OF \<Gamma>] that region by (rule type_context_wf)
  have cxt_tyvars: "tyvars (type_context \<Gamma> q \<chi>s j) \<subseteq> set \<alpha>s" if "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>"
    for j c \<alpha>s b \<phi>
    using type_context_tyvars[OF tyvars disjI1[OF that]] .
  (* Facts established by checking a class definition of the region *)
  have checked: "distinct \<alpha>s \<and> distinct (map fst \<phi>)
    \<and> (\<forall>(x, \<psi>) \<in> set \<phi>. \<exists>\<tau>. resolve_type ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) \<psi> = Ok \<tau>)
    \<and> (\<forall>q' \<psi>s. b = Some (q', \<psi>s) \<longrightarrow>
         (\<exists>D \<sigma>s. resolve_name (type_context \<Gamma> q \<chi>s j) q' = Some (Type D) \<and> D \<noteq> range_class
            \<and> resolve_type ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) (TyExprName q' \<psi>s) = Ok (TyClass D \<sigma>s)
            \<and> (\<forall>x \<in> set (map fst \<phi>). x \<notin> set (field_names ?\<Sigma>' D))))"
    if j: "j < length \<chi>s" and node: "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" for j c \<alpha>s b \<phi>
  proof -
    obtain p where \<chi>: "\<chi>s ! j = At p (Dataclass c \<alpha>s b \<phi>)" using node by (cases "\<chi>s ! j") simp
    from chk j have "check_type_def ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) (At p (Dataclass c \<alpha>s b \<phi>)) = Ok ()"
      unfolding \<chi>[symmetric] by blast
    from check_dataclass_Ok[OF this] show ?thesis .
  qed
  have base_new: "(b = None \<longrightarrow> base ?\<Sigma>' (Qualified q c) = None)
    \<and> (\<forall>q' \<psi>s. b = Some (q', \<psi>s) \<longrightarrow>
         (\<exists>D \<sigma>s. base ?\<Sigma>' (Qualified q c) = Some (D, \<sigma>s) \<and> resolve_name (type_context \<Gamma> q \<chi>s j) q' = Some (Type D)
            \<and> D \<noteq> range_class \<and> resolve_type ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) (TyExprName q' \<psi>s) = Ok (TyClass D \<sigma>s)
            \<and> (\<forall>x \<in> set (map fst \<phi>). x \<notin> set (field_names ?\<Sigma>' D))))"
    if j: "j < length \<chi>s" and node: "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" for j c \<alpha>s b \<phi>
  proof (intro conjI impI allI)
    assume "b = None"
    with new[OF that] node show "base ?\<Sigma>' (Qualified q c) = None" by (simp add: base_def)
  next
    fix q' \<psi>s
    assume b: "b = Some (q', \<psi>s)"
    with checked[OF that] obtain D \<sigma>s where D: "resolve_name (type_context \<Gamma> q \<chi>s j) q' = Some (Type D)"
      and "D \<noteq> range_class" and rt: "resolve_type ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) (TyExprName q' \<psi>s) = Ok (TyClass D \<sigma>s)"
      and "\<forall>x \<in> set (map fst \<phi>). x \<notin> set (field_names ?\<Sigma>' D)"
      by blast
    moreover have "base ?\<Sigma>' (Qualified q c) = Some (D, \<sigma>s)" using new[OF that] node b rt by (simp add: base_def)
    ultimately show "\<exists>D \<sigma>s. base ?\<Sigma>' (Qualified q c) = Some (D, \<sigma>s)
      \<and> resolve_name (type_context \<Gamma> q \<chi>s j) q' = Some (Type D) \<and> D \<noteq> range_class
      \<and> resolve_type ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) (TyExprName q' \<psi>s) = Ok (TyClass D \<sigma>s)
      \<and> (\<forall>x \<in> set (map fst \<phi>). x \<notin> set (field_names ?\<Sigma>' D))"
      by blast
  qed
  (* Base class of a class of the region: in \<Sigma>, or an earlier class of the region *)
  have base_class: "D |\<in>| fmdom \<Sigma> \<or> (\<exists>j' < j. \<exists>c'. defines_class \<chi>s j' c' \<and> D = Qualified q c')"
    if "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" and "resolve_name (type_context \<Gamma> q \<chi>s j) q' = Some (Type D)"
    for j c \<alpha>s b \<phi> q' D
    using type_context_class[OF that] resolve_name_wf[OF \<Gamma>, of q' "Type D"] by auto
  (* Classes of the region, counted in order *)
  define cnt where "cnt = (\<lambda>j. length (filter (\<lambda>j'. \<exists>c. defines_class \<chi>s j' c) [0..<j]))"
  define news where "news = map (\<lambda>j. Qualified q (type_def_name (node (\<chi>s ! j)))) (filter (\<lambda>j. \<exists>c. defines_class \<chi>s j c) [0..<length \<chi>s])"
  have cnt_less: "cnt j' < cnt j" if "j' < j" and "defines_class \<chi>s j' c" for j j' c
  proof -
    have "[0..<j] = [0..<j'] @ [j'..<j]" using upt_add_eq_append[of 0 j' "j - j'"] that(1) by simp
    moreover have "filter (\<lambda>j'. \<exists>c. defines_class \<chi>s j' c) [j'..<j] \<noteq> []"
      using that by (auto simp: filter_empty_conv intro!: bexI[of _ j'])
    ultimately show ?thesis unfolding cnt_def by (simp add: filter_append)
  qed
  have cnt_le: "cnt j \<le> length news" if "j \<le> length \<chi>s" for j
  proof -
    have "[0..<length \<chi>s] = [0..<j] @ [j..<length \<chi>s]" using upt_add_eq_append[of 0 j "length \<chi>s - j"] that by simp
    then show ?thesis unfolding cnt_def news_def by (simp add: filter_append)
  qed
  have "distinct news"
  proof -
    let ?js = "filter (\<lambda>j. \<exists>c. defines_class \<chi>s j c) [0..<length \<chi>s]"
    have "inj_on (\<lambda>j. Qualified q (type_def_name (node (\<chi>s ! j)))) (set ?js)"
    proof (intro inj_onI)
      fix j j'
      assume j: "j \<in> set ?js" and j': "j' \<in> set ?js"
        and eq: "Qualified q (type_def_name (node (\<chi>s ! j))) = Qualified q (type_def_name (node (\<chi>s ! j')))"
      from j obtain c where jc: "j < length \<chi>s" "defines_class \<chi>s j c" by auto
      have c: "type_def_name (node (\<chi>s ! j)) = c" using jc(2) by auto
      show "j = j'" using names[OF jc(1) _ _ jc(2), of j'] j' eq c by auto
    qed
    then show ?thesis unfolding news_def by (simp add: distinct_map)
  qed
  have dom': "fmdom ?\<Sigma>' = fmdom \<Sigma> |\<union>| fset_of_list news"
  proof (rule fset_eqI)
    fix C
    have "(\<exists>j < length \<chi>s. \<exists>c. defines_class \<chi>s j c \<and> C = Qualified q c) \<longleftrightarrow> C \<in> set news"
      unfolding news_def by force
    then show "C |\<in>| fmdom ?\<Sigma>' \<longleftrightarrow> C |\<in>| fmdom \<Sigma> |\<union>| fset_of_list news" by (simp add: dom fset_of_list_elem)
  qed
  have card: "fcard (fmdom ?\<Sigma>') = ?N + length news"
  proof -
    have disj: "fmdom \<Sigma> |\<inter>| fset_of_list news = {||}"
      using fresh unfolding news_def by (auto simp: fset_of_list_elem)
    show ?thesis
      unfolding dom' fcard_funion_disjoint[OF disj]
      by (simp add: fcard.rep_eq fset_of_list.rep_eq distinct_card \<open>distinct news\<close>)
  qed
  (* Chain of base classes of a class of the region: within the classes of \<Sigma> and the earlier classes of the
     region *)
  have inherits: "inherits_within (?N + Suc (cnt j)) ?\<Sigma>' (Qualified q c)"
    if "j < length \<chi>s" and "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" for j c \<alpha>s b \<phi>
    using that
  proof (induction j arbitrary: c \<alpha>s b \<phi> rule: less_induct)
    case (less j)
    show ?case
    proof (cases b)
      case None
      with base_new[OF less.prems] show ?thesis by simp
    next
      case (Some q'\<psi>s)
      then obtain q' \<psi>s where b: "b = Some (q', \<psi>s)" by (cases q'\<psi>s) simp
      from base_new[OF less.prems] b obtain D \<sigma>s where base: "base ?\<Sigma>' (Qualified q c) = Some (D, \<sigma>s)"
        and D: "resolve_name (type_context \<Gamma> q \<chi>s j) q' = Some (Type D)"
        by blast
      from base_class[OF less.prems(2) D] show ?thesis
      proof
        assume "D |\<in>| fmdom \<Sigma>"
        with wf have "inherits_within ?N \<Sigma> D" by (rule wf_class_table_inherits)
        then have "inherits_within ?N ?\<Sigma>' D" by (simp add: inherits_within_ext[OF \<open>D |\<in>| fmdom \<Sigma>\<close>])
        then have "inherits_within (?N + cnt j) ?\<Sigma>' D" by (rule inherits_within_mono) simp
        with base show ?thesis by simp
      next
        assume "\<exists>j' < j. \<exists>c'. defines_class \<chi>s j' c' \<and> D = Qualified q c'"
        then obtain j' c' \<alpha>s' b' \<phi>' where "j' < j" and node': "node (\<chi>s ! j') = Dataclass c' \<alpha>s' b' \<phi>'"
          and D': "D = Qualified q c'"
          by blast
        from less.IH[OF \<open>j' < j\<close> _ node'] less.prems(1) \<open>j' < j\<close>
        have "inherits_within (?N + Suc (cnt j')) ?\<Sigma>' D" by (simp add: D')
        moreover have "?N + Suc (cnt j') \<le> ?N + cnt j" using cnt_less[OF \<open>j' < j\<close>] node' by fastforce
        ultimately have "inherits_within (?N + cnt j) ?\<Sigma>' D" by (rule inherits_within_mono)
        with base show ?thesis by simp
      qed
    qed
  qed
  have inherits': "inherits_within (fcard (fmdom ?\<Sigma>')) ?\<Sigma>' (Qualified q c)"
    if "j < length \<chi>s" and "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" for j c \<alpha>s b \<phi>
  proof (rule inherits_within_mono[OF inherits[OF that]])
    have "cnt j < cnt (Suc j)" using cnt_less[of j "Suc j"] that(2) by blast
    with cnt_le[of "Suc j"] that(1) show "?N + Suc (cnt j) \<le> fcard (fmdom ?\<Sigma>')" by (simp add: card)
  qed
  (* Field names of a class of the region: distinct *)
  have fields: "distinct (field_names ?\<Sigma>' (Qualified q c))"
    if "j < length \<chi>s" and "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" for j c \<alpha>s b \<phi>
    using that
  proof (induction j arbitrary: c \<alpha>s b \<phi> rule: less_induct)
    case (less j)
    have distinct_\<phi>: "distinct (map fst \<phi>)" using checked[OF less.prems] by blast
    show ?case
    proof (cases b)
      case None
      with base_new[OF less.prems] have "base ?\<Sigma>' (Qualified q c) = None" by simp
      from field_names_no_base[OF new[OF less.prems] less.prems(2) this] distinct_\<phi> show ?thesis by simp
    next
      case (Some q'\<psi>s)
      then obtain q' \<psi>s where b: "b = Some (q', \<psi>s)" by (cases q'\<psi>s) simp
      from base_new[OF less.prems] b obtain D \<sigma>s where base: "base ?\<Sigma>' (Qualified q c) = Some (D, \<sigma>s)"
        and D: "resolve_name (type_context \<Gamma> q \<chi>s j) q' = Some (Type D)"
        and disjoint: "\<forall>x \<in> set (map fst \<phi>). x \<notin> set (field_names ?\<Sigma>' D)"
        by blast
      have "field_names ?\<Sigma>' (Qualified q c) = field_names ?\<Sigma>' D @ map fst \<phi>"
        by (rule field_names_base[OF new[OF less.prems] less.prems(2) base inherits'[OF less.prems]])
      moreover have "distinct (field_names ?\<Sigma>' D)"
        using base_class[OF less.prems(2) D]
      proof
        assume "D |\<in>| fmdom \<Sigma>"
        from wf_class_table_distinct[OF wf this] show ?thesis by (simp add: field_names_ext[OF \<open>D |\<in>| fmdom \<Sigma>\<close>])
      next
        assume "\<exists>j' < j. \<exists>c'. defines_class \<chi>s j' c' \<and> D = Qualified q c'"
        with less.IH less.prems(1) show ?thesis by (auto simp: less_trans)
      qed
      ultimately show ?thesis using distinct_\<phi> disjoint by auto
    qed
  qed
  (* Conditions on each class of the extended table *)
  have "(\<exists>\<Gamma>' q' \<chi>s' i c \<alpha>s b \<phi>. fmlookup ?\<Sigma>' C = Some (ClassDef \<Gamma>' q' \<chi>s' i) \<and> node (\<chi>s' ! i) = Dataclass c \<alpha>s b \<phi>)
    \<and> (\<forall>\<Gamma>' q' \<chi>s' i. fmlookup ?\<Sigma>' C = Some (ClassDef \<Gamma>' q' \<chi>s' i)
         \<longrightarrow> tyvars \<Gamma>' = {} \<and> wf_cxt ?\<Sigma>' \<Gamma>' \<and> i < length \<chi>s'
           \<and> (\<forall>\<chi> \<in> set \<chi>s'. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q' c |\<in>| fmdom ?\<Sigma>'))
    \<and> inherits_within (fcard (fmdom ?\<Sigma>')) ?\<Sigma>' C
    \<and> (\<forall>D \<sigma>s. base ?\<Sigma>' C = Some (D, \<sigma>s)
         \<longrightarrow> D \<noteq> range_class \<and> wf_ty ?\<Sigma>' (TyClass D \<sigma>s) \<and> (\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> set (type_params ?\<Sigma>' C)))
    \<and> (\<forall>(x, \<sigma>) \<in> set (declared_fields ?\<Sigma>' C (map TyVar (type_params ?\<Sigma>' C))).
         wf_ty ?\<Sigma>' \<sigma> \<and> fv \<sigma> \<subseteq> set (type_params ?\<Sigma>' C))
    \<and> distinct (type_params ?\<Sigma>' C) \<and> distinct (field_names ?\<Sigma>' C)"
    if C: "C |\<in>| fmdom ?\<Sigma>'" for C
  proof -
    from C dom consider "C |\<in>| fmdom \<Sigma>"
      | j c \<alpha>s b \<phi> where "j < length \<chi>s" and "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" and "C = Qualified q c"
      by blast
    then show ?thesis
    proof cases
      case 1
      note wfC = wf[unfolded wf_class_table_def, rule_format, OF 1]
      have "inherits_within (fcard (fmdom ?\<Sigma>')) ?\<Sigma>' C"
        using wfC inherits_within_ext[OF 1] fcard_mono[OF dom_sub] by (blast intro: inherits_within_mono)
      moreover have "\<forall>\<Gamma>' q' \<chi>s' i. fmlookup ?\<Sigma>' C = Some (ClassDef \<Gamma>' q' \<chi>s' i)
         \<longrightarrow> tyvars \<Gamma>' = {} \<and> wf_cxt ?\<Sigma>' \<Gamma>' \<and> i < length \<chi>s'
           \<and> (\<forall>\<chi> \<in> set \<chi>s'. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q' c |\<in>| fmdom ?\<Sigma>')"
        using wfC unfolding old[OF 1] by (blast intro: wf_cxt_ext dom_ext)
      moreover have "\<forall>D \<sigma>s. base ?\<Sigma>' C = Some (D, \<sigma>s)
         \<longrightarrow> D \<noteq> range_class \<and> wf_ty ?\<Sigma>' (TyClass D \<sigma>s) \<and> (\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> set (type_params ?\<Sigma>' C))"
        using wfC unfolding base_ext[OF 1] type_params_ext[OF 1] by (blast intro: wf_ty_ext)
      moreover have "\<forall>(x, \<sigma>) \<in> set (declared_fields ?\<Sigma>' C (map TyVar (type_params ?\<Sigma>' C))).
         wf_ty ?\<Sigma>' \<sigma> \<and> fv \<sigma> \<subseteq> set (type_params ?\<Sigma>' C)"
        using wfC unfolding declared_fields_ext[OF 1] type_params_ext[OF 1] by (blast intro: wf_ty_ext)
      ultimately show ?thesis
        using wfC unfolding old[OF 1] type_params_ext[OF 1] field_names_ext[OF 1] by blast
    next
      case 2
      note look = new[OF 2(1, 2)] and params = params[OF 2(1, 2)] and cxt = cxt[OF 2(1)]
      have tyvars_cxt: "tyvars (type_context \<Gamma> q \<chi>s j) \<subseteq> set \<alpha>s" using cxt_tyvars[OF 2(2)] .
      have base: "D \<noteq> range_class \<and> wf_ty ?\<Sigma>' (TyClass D \<sigma>s) \<and> (\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> set \<alpha>s)"
        if "base ?\<Sigma>' C = Some (D, \<sigma>s)" for D \<sigma>s
      proof (cases b)
        case None
        with base_new[OF 2(1, 2)] that show ?thesis by (simp add: 2(3))
      next
        case (Some q'\<psi>s)
        then obtain q' \<psi>s where b: "b = Some (q', \<psi>s)" by (cases q'\<psi>s) simp
        from base_new[OF 2(1, 2)] b that obtain \<sigma>s' where "D \<noteq> range_class"
          and rt: "resolve_type ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) (TyExprName q' \<psi>s) = Ok (TyClass D \<sigma>s)"
          by (auto simp: 2(3))
        from resolve_type_wf[OF cxt rt] tyvars_cxt \<open>D \<noteq> range_class\<close> show ?thesis by auto
      qed
      have fields_wf: "wf_ty ?\<Sigma>' \<sigma> \<and> fv \<sigma> \<subseteq> set \<alpha>s"
        if "(x, \<sigma>) \<in> set (declared_fields ?\<Sigma>' C (map TyVar \<alpha>s))" for x \<sigma>
      proof -
        from that obtain \<psi> where "(x, \<psi>) \<in> set \<phi>" and \<sigma>: "\<sigma> = projr (resolve_type ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) \<psi>)"
          using look 2(2) by (auto simp: declared_fields_def 2(3))
        with checked[OF 2(1, 2)] obtain \<tau> where \<tau>: "resolve_type ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) \<psi> = Ok \<tau>" by blast
        from resolve_type_wf[OF cxt \<tau>] tyvars_cxt show ?thesis by (auto simp: \<sigma> \<tau>)
      qed
      have look': "fmlookup ?\<Sigma>' C = Some (ClassDef \<Gamma> q \<chi>s j)" using look 2(3) by simp
      have params': "type_params ?\<Sigma>' C = \<alpha>s" using params 2(3) by simp
      show ?thesis
        apply (intro conjI)
        subgoal using look' 2(2) by blast
        subgoal using look' tyvars wf_cxt_ext[OF \<Gamma>] 2(1) region by auto
        subgoal using inherits'[OF 2(1, 2)] 2(3) by simp
        subgoal using base params' by auto
        subgoal using fields_wf params' by auto
        subgoal using checked[OF 2(1, 2)] params' by auto
        subgoal using fields[OF 2(1, 2)] 2(3) by simp
        done
    qed
  qed
  then show ?thesis unfolding wf_class_table_def by blast
qed


subsection \<open>Entries bound by statements\<close>

(* Entry bound or declared by a statement: a type or a type scheme, possibly unassigned *)
abbreviation var_entry :: "cxt_entry \<Rightarrow> bool"
where "var_entry \<theta> \<equiv> var_ty \<theta> \<noteq> None \<or> scheme_of \<theta> \<noteq> None"

lemma merge_entry_var:
  "\<lbrakk> merge_cxt_entry \<Sigma> b e e' = Some \<theta> ; \<forall>\<theta>'. e = Some \<theta>' \<longrightarrow> var_entry \<theta>' ; \<forall>\<theta>'. e' = Some \<theta>' \<longrightarrow> var_entry \<theta>' \<rbrakk>
  \<Longrightarrow> var_entry \<theta>"
  by (cases e; cases e') (auto elim!: possibly_unassigned.elims dest!: merge_cxt_entry_cases)

lemma merge_var:
  assumes "merge \<Sigma> X \<Gamma> \<Gamma>' = Ok \<Gamma>''" and "\<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> var_entry \<theta>"
    and "\<forall>x \<theta>. fmlookup \<Gamma>' x = Some \<theta> \<longrightarrow> var_entry \<theta>" and "fmlookup \<Gamma>'' x = Some \<theta>"
  shows "var_entry \<theta>"
proof -
  have "x |\<in>| fmdom (\<Gamma> \<otimes> \<Gamma>')" using assms(4) merge_dom[OF assms(1)] by (auto simp: fmlookup_dom_iff)
  with merge_lookup[OF assms(1)] assms(4)
  have "merge_cxt_entry \<Sigma> (x \<in> X) (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x) = Some \<theta>" by simp
  moreover have "\<forall>\<theta>'. fmlookup \<Gamma> x = Some \<theta>' \<longrightarrow> var_entry \<theta>'" using assms(2) by blast
  moreover have "\<forall>\<theta>'. fmlookup \<Gamma>' x = Some \<theta>' \<longrightarrow> var_entry \<theta>'" using assms(3) by blast
  ultimately show ?thesis by (rule merge_entry_var)
qed

lemma merge_outcome_var:
  assumes "merge_outcome \<Sigma> X R R' = Ok (Assigns\<^sub>R \<Delta> r)"
    and "\<And>\<Delta>' r' x \<theta>. \<lbrakk> R = Assigns\<^sub>R \<Delta>' r' \<or> R' = Assigns\<^sub>R \<Delta>' r' ; fmlookup \<Delta>' x = Some \<theta> \<rbrakk> \<Longrightarrow> var_entry \<theta>"
    and "fmlookup \<Delta> x = Some \<theta>"
  shows "var_entry \<theta>"
proof (cases "(\<Sigma>, X, R, R')" rule: merge_outcome.cases)
  case (1 \<Sigma> X \<Delta>\<^sub>1 r\<^sub>1 \<Delta>\<^sub>2 r\<^sub>2)
  with assms(1) obtain \<Delta>'' where m: "merge \<Sigma> X \<Delta>\<^sub>1 \<Delta>\<^sub>2 = Ok \<Delta>''" and \<Delta>: "\<Delta> = \<Delta>''" by (auto simp: bind_sum_Ok)
  show ?thesis
  proof (rule merge_var[OF m])
    show "\<forall>x \<theta>. fmlookup \<Delta>\<^sub>1 x = Some \<theta> \<longrightarrow> var_entry \<theta>" using assms(2) 1 by blast
    show "\<forall>x \<theta>. fmlookup \<Delta>\<^sub>2 x = Some \<theta> \<longrightarrow> var_entry \<theta>" using assms(2) 1 by blast
    show "fmlookup \<Delta>'' x = Some \<theta>" using assms(3) \<Delta> by simp
  qed
qed (use assms in auto)

lemma merges_var:
  assumes "merges \<Sigma> X ms = Ok (Assigns\<^sub>R \<Delta> r)"
    and "\<And>\<Delta>' r' x \<theta>. \<lbrakk> Ok (Assigns\<^sub>R \<Delta>' r') \<in> set ms ; fmlookup \<Delta>' x = Some \<theta> \<rbrakk> \<Longrightarrow> var_entry \<theta>"
    and "fmlookup \<Delta> x = Some \<theta>"
  shows "var_entry \<theta>"
proof -
  let ?f = "\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }"
  from assms(1) obtain Rs where Rs: "those_sum ms = Ok Rs"
    and fold: "foldr ?f Rs (Ok Returns\<^sub>R) = Ok (Assigns\<^sub>R \<Delta> r)"
    by (auto simp: merges_def bind_sum_Ok)
  have "var_entry \<theta>"
    if "foldr ?f Rs (Ok Returns\<^sub>R) = Ok (Assigns\<^sub>R \<Delta> r)" and "fmlookup \<Delta> x = Some \<theta>"
      and "\<And>\<Delta>' r' x \<theta>. \<lbrakk> Assigns\<^sub>R \<Delta>' r' \<in> set Rs ; fmlookup \<Delta>' x = Some \<theta> \<rbrakk> \<Longrightarrow> var_entry \<theta>"
    for Rs \<Delta> r x \<theta>
    using that
  proof (induction Rs arbitrary: \<Delta> r x \<theta>)
    case (Cons R Rs)
    from Cons.prems(1) obtain R' where R': "foldr ?f Rs (Ok Returns\<^sub>R) = Ok R'"
      and m: "merge_outcome \<Sigma> X R R' = Ok (Assigns\<^sub>R \<Delta> r)"
      by (auto simp: bind_sum_Ok)
    show ?case
    proof (rule merge_outcome_var[OF m _ Cons.prems(2)])
      fix \<Delta>' r' x \<theta>
      assume disj: "R = Assigns\<^sub>R \<Delta>' r' \<or> R' = Assigns\<^sub>R \<Delta>' r'" and look: "fmlookup \<Delta>' x = Some \<theta>"
      from disj show "var_entry \<theta>"
      proof
        assume "R = Assigns\<^sub>R \<Delta>' r'"
        then show ?thesis by (intro Cons.prems(3)[of \<Delta>' r' x \<theta>, OF _ look]) simp
      next
        assume R'': "R' = Assigns\<^sub>R \<Delta>' r'"
        show ?thesis by (rule Cons.IH[OF R'[unfolded R''] look]) (metis Cons.prems(3) list.set_intros(2))
      qed
    qed
  qed simp
  moreover have "var_entry \<theta>'" if "Assigns\<^sub>R \<Delta>' r' \<in> set Rs" and "fmlookup \<Delta>' x' = Some \<theta>'" for \<Delta>' r' x' \<theta>'
  proof -
    from that(1) obtain i where "i < length Rs" and "Rs ! i = Assigns\<^sub>R \<Delta>' r'" by (auto simp: in_set_conv_nth)
    with those_sum_Ok[OF Rs] have "ms ! i = Ok (Assigns\<^sub>R \<Delta>' r')" and "i < length ms"
      by (auto simp: list_all2_conv_all_nth)
    then have "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set ms" by (metis nth_mem)
    from assms(2)[OF this that(2)] show ?thesis .
  qed
  ultimately show ?thesis using fold assms(3) by blast
qed

lemma signature_entry_var: "var_entry (signature_entry \<pi>)"
proof (cases \<pi>)
  case (TyScheme \<alpha>s \<tau>)
  then show ?thesis by (cases \<alpha>s) simp_all
qed

lemma match_cases_entries:
  "\<lbrakk> match_cases \<Sigma> \<Gamma> \<tau> L ps = Ok (\<Delta>s, \<tau>', L') ; \<Delta> \<in> set \<Delta>s ; fmlookup \<Delta> x = Some \<theta> \<rbrakk> \<Longrightarrow> \<exists>\<sigma>. \<theta> = Ty \<sigma>"
proof (induction ps arbitrary: \<tau> L \<Delta>s)
  case (Cons p ps)
  then show ?case by (auto simp: bind_sum_Ok or_else_def split: option.splits prod.splits)
qed simp

(* Entries bound by a statement: types or type schemes, possibly unassigned *)
lemma check_stmt_entries:
  "\<lbrakk> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r) ; fmlookup \<Delta> x = Some \<theta> \<rbrakk> \<Longrightarrow> var_entry \<theta>"
  "\<lbrakk> check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta> r) ; fmlookup \<Delta> x = Some \<theta> \<rbrakk> \<Longrightarrow> var_entry \<theta>"
  "check_def \<Sigma> \<Gamma> d \<pi> = m \<Longrightarrow> True"
  "check_def_at \<Sigma> \<Gamma> d' \<pi> = m \<Longrightarrow> True"
proof (induction \<Sigma> \<Gamma> \<zeta> s and \<Sigma> \<Gamma> \<zeta> s' and \<Sigma> \<Gamma> d \<pi> and \<Sigma> \<Gamma> d' \<pi> arbitrary: \<Delta> r x \<theta> and \<Delta> r x \<theta>
    rule: check_stmt_check_stmt_at_check_def_check_def_at.induct)
  case (10 \<Sigma> \<Gamma> \<zeta> e s elifs else')
  from "10.prems"(1) obtain z where e: "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok z"
    and m: "merges \<Sigma> (set (declares (StmtIf e s elifs else')))
              (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok (Assigns\<^sub>R \<Delta> r)"
    unfolding check_stmt_if by (auto simp: bind_sum_Ok)
  show ?case
  proof (rule merges_var[OF m _ "10.prems"(2)])
    fix \<Delta>' r' x' \<theta>'
    assume mem: "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))"
      and look: "fmlookup \<Delta>' x' = Some \<theta>'"
    from mem consider (s) "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta>' r')"
      | (elif) e' s' z' where "(e', s') \<in> set elifs" and "check_expr_at \<Sigma> \<Gamma> e' (TyPrim bool) = Ok z'"
          and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta>' r')"
      | (else) s' where "else' = Some s'" and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta>' r')"
      | (none) "\<Delta>' = fmempty"
      by (auto simp: Ok_bind_sum split: option.splits)
    then show "var_entry \<theta>'"
    proof cases
      case s
      from "10.IH"(1)[OF e s look] show ?thesis .
    next
      case elif
      from "10.IH"(2)[OF e elif(1) refl elif(2, 3) look] show ?thesis .
    next
      case else
      from "10.IH"(3)[OF e else look] show ?thesis .
    next
      case none
      with look show ?thesis by simp
    qed
  qed
next
  case (11 \<Sigma> \<Gamma> \<zeta> s s')
  from check_seq[OF "11.prems"(1)] obtain \<Delta>\<^sub>1 r\<^sub>1 R\<^sub>2 where s: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1)"
    and s': "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>1) \<zeta> s' = Ok R\<^sub>2" and R: "Assigns\<^sub>R \<Delta> r = Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1 \<otimes> R\<^sub>2"
    by blast
  from R obtain \<Delta>\<^sub>2 r\<^sub>2 where R\<^sub>2: "R\<^sub>2 = Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2" and \<Delta>: "\<Delta> = \<Delta>\<^sub>1 \<otimes> \<Delta>\<^sub>2" by (cases R\<^sub>2) auto
  show ?case
  proof (cases "fmlookup \<Delta>\<^sub>2 x")
    case None
    with "11.prems"(2) \<Delta> have "fmlookup \<Delta>\<^sub>1 x = Some \<theta>" by (simp add: fmlookup_dom_iff)
    from "11.IH"(1)[OF s this] show ?thesis .
  next
    case (Some \<theta>')
    with "11.prems"(2) \<Delta> have "\<theta>' = \<theta>" by (simp add: fmlookup_dom_iff)
    from "11.IH"(2)[OF s refl s'[unfolded R\<^sub>2] Some[unfolded this]] show ?thesis .
  qed
next
  case (12 \<Sigma> \<Gamma> \<zeta> ds)
  from "12.prems"(1) obtain \<pi>s
    where \<Delta>: "\<Delta> = fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))"
    by (auto simp: bind_sum_Ok Let_def)
  from "12.prems"(2) obtain \<pi> where "\<theta> = signature_entry \<pi>"
    by (auto simp: \<Delta> fmlookup_of_list dest!: map_of_SomeD set_zip_rightD)
  then show ?case using signature_entry_var[of \<pi>] by simp
next
  case (13 \<Sigma> \<Gamma> \<zeta> e bs)
  from "13.prems"(1) obtain \<sigma> \<Delta>s \<tau> L where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
    and mc: "match_cases \<Sigma> \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst bs) = Ok (\<Delta>s, \<tau>, L)"
    and m: "merges \<Sigma> (set (declares (StmtMatch e bs))) (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L) = Ok (Assigns\<^sub>R \<Delta> r)"
    by (rule check_match)
  show ?case
  proof (rule merges_var[OF m _ "13.prems"(2)])
    fix \<Delta>' r' x' \<theta>'
    assume mem: "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L)"
      and look: "fmlookup \<Delta>' x' = Some \<theta>'"
    show "var_entry \<theta>'"
    proof (cases "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set (map2 (\<lambda>\<Delta> (_, s). do {
                    R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) }) \<Delta>s bs)")
      case True
      from Ok_in_set_map2[OF True] obtain \<Delta>\<^sub>p p s R where b: "(\<Delta>\<^sub>p, (p, s)) \<in> set (zip \<Delta>s bs)"
        and R: "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>p) \<zeta> s = Ok R" and \<Delta>': "Assigns\<^sub>R \<Delta>\<^sub>p None \<otimes> R = Assigns\<^sub>R \<Delta>' r'"
        by (auto simp: bind_sum_Ok split: prod.splits)
      from \<Delta>' obtain \<Delta>\<^sub>2 r\<^sub>2 where R\<^sub>2: "R = Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2" and \<Delta>'': "\<Delta>' = \<Delta>\<^sub>p \<otimes> \<Delta>\<^sub>2" by (cases R) auto
      show ?thesis
      proof (cases "fmlookup \<Delta>\<^sub>2 x'")
        case None
        with look \<Delta>'' have "fmlookup \<Delta>\<^sub>p x' = Some \<theta>'" by (simp add: fmlookup_dom_iff)
        from match_cases_entries[OF mc set_zip_leftD[OF b] this] show ?thesis by auto
      next
        case (Some \<theta>'')
        with look \<Delta>'' have "\<theta>'' = \<theta>'" by (simp add: fmlookup_dom_iff)
        from "13.IH"[OF \<sigma> mc refl refl b refl refl R[unfolded R\<^sub>2] Some[unfolded this]] show ?thesis .
      qed
    next
      case False
      with mem look show ?thesis by (auto simp: match_branches_def split: if_splits)
    qed
  qed
next
  case (14 \<Sigma> \<Gamma> \<zeta> p s)
  then show ?case by (cases "check_stmt \<Sigma> \<Gamma> \<zeta> s") (auto split: static_outcome.splits)
qed (auto simp: bind_sum_Ok check_unbound_def ensure_def Let_def split: option.splits cxt_entry.splits if_splits)

subsection \<open>Top-level statements\<close>

lemma declares_top_simps [simp]:
  "declares (TopSeq t t') = declares t @ declares t'"
  "declares (TypeDefs \<chi>s) = map (type_def_name \<circ> node) \<chi>s"
  by (simp_all add: declares_top_def)

lemma declarations_stmt_assigns: "set (map node (declarations_stmt s)) \<subseteq> assigns (node s)"
  by (induction s rule: declarations_stmt.induct) (fastforce split: option.splits)+

(* Names declared by a top-level statement, assigned by it *)
lemma declares_top_assigns: "set (declares (t :: top_stmt)) \<subseteq> assigns t"
proof (induction t)
  case (Stmt s)
  show ?case using declarations_stmt_assigns[of s] by (simp add: declares_top_def)
qed auto

lemma finite_assigns_stmt: "finite (assigns_stmt s)"
  by (induction s rule: assigns_stmt.induct) (auto simp: finite_binds_pat split: option.splits)

lemma finite_assigns_top: "finite (assigns (t :: top_stmt))"
  by (induction t) (auto simp: finite_assigns_stmt)

lemma fold_fmadd_out: "fold (\<lambda>j E. E \<otimes> g j) js A = A \<otimes> fold (\<lambda>j E. E \<otimes> g j) js fmempty"
proof (induction js arbitrary: A)
  case (Cons j js)
  show ?case using Cons.IH[of "A \<otimes> g j"] Cons.IH[of "g j"] by simp
qed simp

lemma fmsubset_refl[simp]: "m \<subseteq>\<^sub>f m"
  by (auto simp: fmsubset_alt_def fmpred_iff)

lemma fmsubset_antisym: "\<lbrakk> m \<subseteq>\<^sub>f n ; n \<subseteq>\<^sub>f m \<rbrakk> \<Longrightarrow> m = n"
  unfolding fmsubset_alt_def fmpred_iff by (intro fmap_ext) (metis option.exhaust)

lemma fmsubset_trans: "\<lbrakk> m \<subseteq>\<^sub>f n ; n \<subseteq>\<^sub>f p \<rbrakk> \<Longrightarrow> m \<subseteq>\<^sub>f p"
  by (auto simp: fmsubset_alt_def fmpred_iff)

lemma not_Returns: "R \<noteq> Returns\<^sub>R \<Longrightarrow> \<exists>\<Delta> r. R = Assigns\<^sub>R \<Delta> r"
  by (cases R) auto

lemma override_Assigns:
  "Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1 \<otimes> R = Assigns\<^sub>R \<Delta> r \<Longrightarrow> \<exists>\<Delta>\<^sub>2 r\<^sub>2. R = Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2 \<and> \<Delta> = \<Delta>\<^sub>1 \<otimes> \<Delta>\<^sub>2"
  by (cases R) auto

lemma defines_class_declares: "\<lbrakk> j < length \<chi>s ; defines_class \<chi>s j c \<rbrakk> \<Longrightarrow> c \<in> set (declares (TypeDefs \<chi>s))"
  using nth_mem[of j \<chi>s] by (auto simp: declares_top_simps intro!: image_eqI[of _ _ "\<chi>s ! j"])

(* Classes added by a top-level statement: named by its declarations and owned by its module *)
lemma check_top_stmt_dom:
  "\<lbrakk> check_top_stmt \<Sigma> q \<Gamma> t = Ok (R, \<Sigma>') ; C |\<in>| fmdom \<Sigma>' ; C |\<notin>| fmdom \<Sigma> \<rbrakk>
  \<Longrightarrow> \<exists>c \<in> set (declares t). C = Qualified q c"
proof (induction t arbitrary: \<Sigma> \<Gamma> R \<Sigma>')
  case (Stmt s)
  then show ?case by (auto simp: bind_sum_Ok)
next
  case (TopSeq t t')
  from TopSeq.prems(1) obtain \<Delta> r \<Sigma>\<^sub>1 R' where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>\<^sub>1)"
    and t': "check_top_stmt \<Sigma>\<^sub>1 q (\<Gamma> \<otimes> \<Delta>) t' = Ok (R', \<Sigma>')"
    by (auto simp: bind_sum_Ok split: static_outcome.splits dest!: not_Returns override_Assigns)
  show ?case
  proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>1")
    case True
    from TopSeq.IH(1)[OF t True TopSeq.prems(3)] show ?thesis by auto
  next
    case False
    from TopSeq.IH(2)[OF t' TopSeq.prems(2) False] show ?thesis by auto
  qed
next
  case (TypeDefs \<chi>s)
  from TypeDefs.prems(1) have \<Sigma>': "\<Sigma>' = region_table \<Gamma> q \<chi>s \<Sigma>" by (auto simp: Let_def bind_sum_Ok)
  from TypeDefs.prems(2, 3) obtain j c where jc: "j < length \<chi>s" "defines_class \<chi>s j c" "C = Qualified q c"
    unfolding \<Sigma>' fold_class_table_dom by auto
  show ?case using defines_class_declares[OF jc(1, 2)] jc(3) by blast
qed

(* Class table produced by a top-level statement: the table it was checked from, extended by classes named by
   its declarations *)
lemma check_top_stmt_adds:
  "check_top_stmt \<Sigma> q \<Gamma> t = Ok (R, \<Sigma>')
  \<Longrightarrow> \<exists>E. \<Sigma>' = \<Sigma> \<otimes> E \<and> (\<forall>C. C |\<in>| fmdom E \<longrightarrow> (\<exists>c \<in> set (declares t). C = Qualified q c))"
proof (induction t arbitrary: \<Sigma> \<Gamma> R \<Sigma>')
  case (Stmt s)
  then show ?case by (auto simp: bind_sum_Ok intro: exI[of _ fmempty])
next
  case (TopSeq t t')
  from TopSeq.prems obtain \<Delta> r \<Sigma>\<^sub>1 R' where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>\<^sub>1)"
    and t': "check_top_stmt \<Sigma>\<^sub>1 q (\<Gamma> \<otimes> \<Delta>) t' = Ok (R', \<Sigma>')"
    by (auto simp: bind_sum_Ok split: static_outcome.splits dest!: not_Returns override_Assigns)
  from TopSeq.IH(1)[OF t] obtain E\<^sub>1 where "\<Sigma>\<^sub>1 = \<Sigma> \<otimes> E\<^sub>1"
    and E\<^sub>1: "\<forall>C. C |\<in>| fmdom E\<^sub>1 \<longrightarrow> (\<exists>c \<in> set (declares t). C = Qualified q c)" by blast
  moreover from TopSeq.IH(2)[OF t'] obtain E\<^sub>2 where "\<Sigma>' = \<Sigma>\<^sub>1 \<otimes> E\<^sub>2"
    and E\<^sub>2: "\<forall>C. C |\<in>| fmdom E\<^sub>2 \<longrightarrow> (\<exists>c \<in> set (declares t'). C = Qualified q c)" by blast
  ultimately have "\<Sigma>' = \<Sigma> \<otimes> (E\<^sub>1 \<otimes> E\<^sub>2)" by simp
  with E\<^sub>1 E\<^sub>2 show ?case by (intro exI[of _ "E\<^sub>1 \<otimes> E\<^sub>2"]) auto
next
  case (TypeDefs \<chi>s)
  let ?E = "fold (\<lambda>j E. E \<otimes> class_table \<Gamma> q \<chi>s j) [0..<length \<chi>s] fmempty"
  from TypeDefs.prems have \<Sigma>': "\<Sigma>' = region_table \<Gamma> q \<chi>s \<Sigma>" by (auto simp: Let_def bind_sum_Ok)
  have "\<Sigma>' = \<Sigma> \<otimes> ?E" unfolding \<Sigma>' by (rule fold_fmadd_out)
  moreover have "\<exists>c \<in> set (declares (TypeDefs \<chi>s)). C = Qualified q c" if "C |\<in>| fmdom ?E" for C
  proof -
    from that obtain j c where jc: "j < length \<chi>s" "defines_class \<chi>s j c" "C = Qualified q c"
      unfolding fold_class_table_dom by auto
    show ?thesis using defines_class_declares[OF jc(1, 2)] jc(3) by blast
  qed
  ultimately show ?case by blast
qed

(* Class table and bindings of a top-level statement checked from a well-formed table in which its classes are
   fresh *)
lemma check_top_stmt_wf:
  assumes "check_top_stmt \<Sigma> q \<Gamma> t = Ok (R, \<Sigma>')" and "wf_class_table \<Sigma>" and "predefined_classes \<subseteq>\<^sub>f \<Sigma>"
    and "wf_cxt \<Sigma> \<Gamma>" and "tyvars \<Gamma> = {}"
    and "\<forall>c \<in> set (declares t). Qualified q c |\<notin>| fmdom \<Sigma>" and "distinct (declares t)"
  shows "\<Sigma> \<subseteq>\<^sub>f \<Sigma>' \<and> wf_class_table \<Sigma>' \<and> (\<forall>\<Delta> r. R = Assigns\<^sub>R \<Delta> r \<longrightarrow> wf_cxt \<Sigma>' \<Delta> \<and> tyvars \<Delta> = {})"
  using assms
proof (induction t arbitrary: \<Sigma> \<Gamma> R \<Sigma>')
  case (Stmt s)
  from Stmt.prems(1) have R: "check_stmt_at \<Sigma> \<Gamma> None s = Ok R" and \<Sigma>': "\<Sigma>' = \<Sigma>" by (auto simp: bind_sum_Ok)
  show ?case using check_stmt_wf(2)[OF _ Stmt.prems(2, 4)] R Stmt.prems(2, 5) by (auto simp: \<Sigma>' fmsubset_refl)
next
  case (TopSeq t t')
  from TopSeq.prems(1) obtain \<Delta> r \<Sigma>\<^sub>1 R' where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>\<^sub>1)"
    and t': "check_top_stmt \<Sigma>\<^sub>1 q (\<Gamma> \<otimes> \<Delta>) t' = Ok (R', \<Sigma>')" and R: "R = Assigns\<^sub>R \<Delta> r \<otimes> R'"
    by (auto simp: bind_sum_Ok split: static_outcome.splits dest!: not_Returns override_Assigns)
  from TopSeq.prems(6, 7) have "\<forall>c \<in> set (declares t). Qualified q c |\<notin>| fmdom \<Sigma>" and "distinct (declares t)"
    by auto
  note IH1 = TopSeq.IH(1)[OF t TopSeq.prems(2-5) this]
  then have sub1: "\<Sigma> \<subseteq>\<^sub>f \<Sigma>\<^sub>1" and wf1: "wf_class_table \<Sigma>\<^sub>1" and \<Delta>: "wf_cxt \<Sigma>\<^sub>1 \<Delta>" "tyvars \<Delta> = {}" by auto
  have fresh': "\<forall>c \<in> set (declares t'). Qualified q c |\<notin>| fmdom \<Sigma>\<^sub>1"
  proof
    fix c
    assume c: "c \<in> set (declares t')"
    with TopSeq.prems(6) have "Qualified q c |\<notin>| fmdom \<Sigma>" by simp
    moreover have "c \<notin> set (declares t)" using TopSeq.prems(7) c by auto
    ultimately show "Qualified q c |\<notin>| fmdom \<Sigma>\<^sub>1" using check_top_stmt_dom[OF t] by blast
  qed
  have "wf_cxt \<Sigma>\<^sub>1 (\<Gamma> \<otimes> \<Delta>)" using wf_cxt_mono[OF TopSeq.prems(4) sub1] \<Delta>(1) by (rule wf_cxt_add)
  moreover have "tyvars (\<Gamma> \<otimes> \<Delta>) = {}" using tyvars_add[of \<Gamma> \<Delta>] TopSeq.prems(5) \<Delta>(2) by blast
  moreover have "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using TopSeq.prems(3) sub1 by (rule fmsubset_trans)
  ultimately have IH2: "\<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>' \<and> wf_class_table \<Sigma>'
      \<and> (\<forall>\<Delta>' r'. R' = Assigns\<^sub>R \<Delta>' r' \<longrightarrow> wf_cxt \<Sigma>' \<Delta>' \<and> tyvars \<Delta>' = {})"
    using TopSeq.IH(2)[OF t' wf1 _ _ _ fresh'] TopSeq.prems(7) by auto
  then have sub2: "\<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>'" by simp
  have "wf_cxt \<Sigma>' \<Delta>'' \<and> tyvars \<Delta>'' = {}" if "R = Assigns\<^sub>R \<Delta>'' r''" for \<Delta>'' r''
  proof -
    from that R obtain \<Delta>' r' where "R' = Assigns\<^sub>R \<Delta>' r'" and \<Delta>'': "\<Delta>'' = \<Delta> \<otimes> \<Delta>'" by (cases R') auto
    with IH2 have "wf_cxt \<Sigma>' \<Delta>'" and "tyvars \<Delta>' = {}" by auto
    with wf_cxt_mono[OF \<Delta>(1) sub2] \<Delta>(2) show ?thesis using tyvars_add[of \<Delta> \<Delta>'] by (auto simp: \<Delta>'' wf_cxt_add)
  qed
  with fmsubset_trans[OF sub1 sub2] IH2 show ?case by blast
next
  case (TypeDefs \<chi>s)
  let ?\<Sigma>' = "region_table \<Gamma> q \<chi>s \<Sigma>"
  let ?\<Delta> = "fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_entry \<Gamma> q \<chi>s j)) [0..<length \<chi>s])"
  from TypeDefs.prems(1) have chk: "\<forall>j < length \<chi>s. check_type_def ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) (\<chi>s ! j) = Ok ()"
    and \<Sigma>': "\<Sigma>' = ?\<Sigma>'" and R: "R = Assigns\<^sub>R ?\<Delta> None"
    by (auto simp: Let_def bind_sum_Ok dest!: those_sum_map_Ok_all)
  have fresh: "\<forall>j < length \<chi>s. \<forall>c. defines_class \<chi>s j c \<longrightarrow> Qualified q c |\<notin>| fmdom \<Sigma>"
    using TypeDefs.prems(6) by (blast intro: defines_class_declares)
  have distinct: "distinct (map (type_def_name \<circ> node) \<chi>s)" using TypeDefs.prems(7) by simp
  have wf': "wf_class_table ?\<Sigma>'" by (rule region_table_wf[OF TypeDefs.prems(2, 3, 4, 5) fresh distinct chk])
  have sub: "\<Sigma> \<subseteq>\<^sub>f ?\<Sigma>'" by (rule region_table_subset[OF fresh])
  have region: "\<forall>\<chi> \<in> set \<chi>s. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q c |\<in>| fmdom ?\<Sigma>'"
    by (auto simp: fold_class_table_dom in_set_conv_nth)
  have "wf_cxt ?\<Sigma>' ?\<Delta>"
    using type_entry_wf[OF TypeDefs.prems(5) wf_cxt_mono[OF TypeDefs.prems(4) sub] _ region]
    by (auto intro!: wf_cxt_of_list)
  moreover have "tyvars ?\<Delta> = {}" by (rule tyvars_empty) (auto simp: fmlookup_of_list dest!: map_of_SomeD)
  ultimately show ?case using sub wf' by (simp add: \<Sigma>' R)
qed

(* Variable bound by a top-level statement checked in \<Gamma>: assigned by the statement, or unbound or declared in
   \<Gamma> *)
lemma check_top_stmt_bound:
  "\<lbrakk> check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>') ; x |\<in>| fmdom \<Delta> \<rbrakk>
  \<Longrightarrow> x \<in> assigns t \<or> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))"
proof (induction t arbitrary: \<Sigma> \<Gamma> \<Delta> r \<Sigma>')
  case (Stmt s)
  then show ?case by (auto simp: bind_sum_Ok dest: check_stmt_bound(2))
next
  case (TopSeq t t')
  from TopSeq.prems(1) obtain \<Delta>\<^sub>1 r\<^sub>1 \<Sigma>\<^sub>1 \<Delta>\<^sub>2 r\<^sub>2 where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1, \<Sigma>\<^sub>1)"
    and t': "check_top_stmt \<Sigma>\<^sub>1 q (\<Gamma> \<otimes> \<Delta>\<^sub>1) t' = Ok (Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2, \<Sigma>')" and \<Delta>: "\<Delta> = \<Delta>\<^sub>1 \<otimes> \<Delta>\<^sub>2"
    by (auto simp: bind_sum_Ok split: static_outcome.splits dest!: not_Returns override_Assigns)
  show ?case
  proof (cases "x |\<in>| fmdom \<Delta>\<^sub>1")
    case True
    from TopSeq.IH(1)[OF t True] show ?thesis by auto
  next
    case False
    with TopSeq.prems(2) \<Delta> have "x |\<in>| fmdom \<Delta>\<^sub>2" by simp
    from TopSeq.IH(2)[OF t' this] False show ?thesis by auto
  qed
next
  case (TypeDefs \<chi>s)
  then show ?case by (fastforce simp: Let_def bind_sum_Ok fset_of_list_elem in_set_conv_nth)
qed

(* Entries bound by a top-level statement: those of statements, classes and type aliases *)
lemma check_top_stmt_entries:
  "\<lbrakk> check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>') ; fmlookup \<Delta> x = Some \<theta> \<rbrakk>
  \<Longrightarrow> var_entry \<theta> \<or> (\<exists>C. \<theta> = Type C) \<or> (\<exists>\<Gamma>' q' \<chi>s i. \<theta> = TypeAlias \<Gamma>' q' \<chi>s i)"
proof (induction t arbitrary: \<Sigma> \<Gamma> \<Delta> r \<Sigma>')
  case (Stmt s)
  then show ?case by (auto simp: bind_sum_Ok dest: check_stmt_entries(2))
next
  case (TopSeq t t')
  from TopSeq.prems(1) obtain \<Delta>\<^sub>1 r\<^sub>1 \<Sigma>\<^sub>1 \<Delta>\<^sub>2 r\<^sub>2 where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1, \<Sigma>\<^sub>1)"
    and t': "check_top_stmt \<Sigma>\<^sub>1 q (\<Gamma> \<otimes> \<Delta>\<^sub>1) t' = Ok (Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2, \<Sigma>')" and \<Delta>: "\<Delta> = \<Delta>\<^sub>1 \<otimes> \<Delta>\<^sub>2"
    by (auto simp: bind_sum_Ok split: static_outcome.splits dest!: not_Returns override_Assigns)
  show ?case
  proof (cases "fmlookup \<Delta>\<^sub>2 x")
    case None
    with TopSeq.prems(2) \<Delta> have "fmlookup \<Delta>\<^sub>1 x = Some \<theta>" by (simp add: fmlookup_dom_iff)
    from TopSeq.IH(1)[OF t this] show ?thesis .
  next
    case (Some \<theta>')
    with TopSeq.prems(2) \<Delta> have "\<theta>' = \<theta>" by (simp add: fmlookup_dom_iff)
    from TopSeq.IH(2)[OF t' Some[unfolded this]] show ?thesis .
  qed
next
  case (TypeDefs \<chi>s)
  then show ?case
    by (auto simp: Let_def bind_sum_Ok fmlookup_of_list type_entry_def split: type_def.splits dest!: map_of_SomeD)
qed

lemma concat_pairs_image:
  "(a, b) \<in> set ps \<Longrightarrow> f ` set (g a b) \<subseteq> f ` set (concat (map (\<lambda>(a, b). g a b) ps))"
  by (induction ps) auto

lemma assigns_stmt_binders_mem:
  "x \<in> assigns (node s) \<Longrightarrow> x \<in> node ` set (declarations_stmt s) \<union> node ` set (pat_bound_stmt s)
     \<union> node ` set (assign_targets_stmt s)"
proof (induction s arbitrary: x rule: declarations_stmt.induct)
  case (5 p e s elifs else')
  from "5.prems" consider (s) "x \<in> assigns (node s)" | (elif) a b where "(a, b) \<in> set elifs" "x \<in> assigns (node b)"
    | (else) s' where "else' = Some s'" "x \<in> assigns (node s')"
    by (auto split: option.splits prod.splits)
  then show ?case
  proof cases
    case s
    from "5.IH"(1)[OF s] show ?thesis by (simp only: declarations_stmt.simps pat_bound_stmt.simps assign_targets_stmt.simps set_append image_Un) blast
  next
    case elif
    from "5.IH"(2)[OF elif(1) refl elif(2)]
      concat_pairs_image[OF elif(1), of node "\<lambda>_ y. declarations_stmt y"]
      concat_pairs_image[OF elif(1), of node "\<lambda>_ y. pat_bound_stmt y"]
      concat_pairs_image[OF elif(1), of node "\<lambda>_ y. assign_targets_stmt y"]
    show ?thesis by (simp only: declarations_stmt.simps pat_bound_stmt.simps assign_targets_stmt.simps set_append image_Un) blast
  next
    case else
    from "5.IH"(3)[OF else] show ?thesis by (simp only: declarations_stmt.simps pat_bound_stmt.simps assign_targets_stmt.simps set_append image_Un else(1) option.case) blast
  qed
next
  case (6 p e cases)
  from "6.prems" obtain q s where qs: "(q, s) \<in> set cases" and x: "x \<in> binds_pat (node q) \<or> x \<in> assigns (node s)"
    by (auto split: prod.splits)
  let ?g = "\<lambda>q s. map (At p) (sorted_list_of_set (binds_pat (node q))) @ pat_bound_stmt s"
  have pat: "binds_pat (node q) \<subseteq> node ` set (?g q s)"
  proof
    fix y
    assume "y \<in> binds_pat (node q)"
    then have "At p y \<in> set (?g q s)" by (simp add: finite_binds_pat)
    then show "y \<in> node ` set (?g q s)" by (rule rev_image_eqI) simp
  qed
  from x show ?case
  proof
    assume "x \<in> binds_pat (node q)"
    with pat concat_pairs_image[OF qs, of node ?g] show ?thesis by (simp only: declarations_stmt.simps pat_bound_stmt.simps assign_targets_stmt.simps set_append image_Un) blast
  next
    assume "x \<in> assigns (node s)"
    from "6.IH"[OF qs refl this]
      concat_pairs_image[OF qs, of node "\<lambda>_ y. declarations_stmt y"]
      concat_pairs_image[OF qs, of node ?g]
      concat_pairs_image[OF qs, of node "\<lambda>_ y. assign_targets_stmt y"]
    show ?thesis by (simp only: declarations_stmt.simps pat_bound_stmt.simps assign_targets_stmt.simps set_append image_Un) blast
  qed
qed (auto simp: image_Un image_image split: option.splits)

(* Variables assigned by a statement: declared, bound by a pattern or the target of a plain assignment *)
lemma assigns_stmt_binders:
  "assigns (node s) \<subseteq> set (map node (declarations_stmt s)) \<union> binds s \<union> set (map node (assign_targets s))"
  using assigns_stmt_binders_mem[of _ s] by (auto simp: binds_stmt_def)

lemma assigns_top_binders:
  "assigns (t :: top_stmt) \<subseteq> set (declares t) \<union> binds t \<union> set (map node (assign_targets t))"
proof (induction t)
  case (Stmt s)
  show ?case using assigns_stmt_binders[of s] by (simp add: declares_top_def binds_top_def binds_stmt_def)
qed (auto simp: binds_top_def)

(* Targets of plain assignments of a top-level statement, declared or bound by a pattern *)
lemma check_assignments_declared_top:
  "\<lbrakk> check_assignments_declared {} (assign_targets (t :: top_stmt)) (declares t) (binds t) = Ok ()
   ; x \<in> set (map node (assign_targets t)) \<rbrakk>
  \<Longrightarrow> x \<in> set (declares t) \<or> x \<in> binds t"
  by (auto simp: check_assignments_declared_def find_None_iff split: option.splits)

subsection \<open>Modules\<close>

declare check_module.simps [simp del] check_imports.simps [simp del] submodules.simps [simp del]
  imports_entry.simps [simp del] imports_entries.simps [simp del] check_modules.simps [simp del]

lemma locate_in_Ok [simp]: "(locate_in q p m = Ok r) = (m = Ok r)"
  by (simp add: locate_in_def)

lemma variables_nonempty: "variables q \<noteq> []"
  by (induction q) auto

lemma root_variables: "variables q = x # xs \<Longrightarrow> root q = x"
  by (induction q arbitrary: xs) (auto simp: variables_nonempty append_eq_Cons_conv)

lemma extend_cxt_dom [simp]: "fmdom (\<Gamma> \<uplus> \<Gamma>') = fmdom \<Gamma> |\<union>| fmdom \<Gamma>'"
  by (simp add: extend_cxt.simps)

lemma submods_lookup:
  "fmlookup (submods \<M> q) x = (if Qualified q x |\<in>| fmdom \<M> then Some (ModStub (Qualified q x)) else None)"
  by (auto simp: submods.rep_eq fmlookup_dom_iff dom_def)

(* Members of the predefined module of builtins: neither unbound nor declared without assignment *)
lemma builtins_entry:
  "fmlookup (the (fmlookup \<P> builtins)) x = Some \<theta> \<Longrightarrow> \<theta> \<noteq> Unbound \<and> (\<forall>\<tau>. \<theta> \<noteq> DU \<tau>)"
  by (auto simp: \<P>_def builtins_def name_of_def fmlookup_of_list split: if_splits dest!: map_of_SomeD)

lemma imports_entries_length: "imports_entries \<M> V \<Sigma> q q' \<Gamma> xs = Ok (\<theta>s, \<Sigma>') \<Longrightarrow> length \<theta>s = length xs"
  by (induction xs arbitrary: \<Sigma> \<theta>s \<Sigma>') (auto simp: imports_entries.simps bind_sum_Ok)

(* Names declared by imports, bound by their context *)
lemma check_imports_declares:
  "\<lbrakk> check_imports \<M> V \<Sigma> q \<iota>s = Ok (\<Gamma>, \<Sigma>') ; x \<in> set (declares \<iota>s) \<rbrakk> \<Longrightarrow> x |\<in>| fmdom \<Gamma>"
proof (induction \<iota>s arbitrary: \<Sigma> \<Gamma> \<Sigma>')
  case (Cons \<iota> \<iota>s)
  obtain p i where \<iota>: "\<iota> = At p i" by (cases \<iota>)
  show ?case
  proof (cases i)
    case (Import q')
    obtain y ys where vars: "variables q' = y # ys" using variables_nonempty by (cases "variables q'") auto
    from Cons.prems(1) obtain \<Sigma>\<^sub>2 \<Delta>' \<Gamma>'' where rest: "check_imports \<M> V \<Sigma>\<^sub>2 q \<iota>s = Ok (\<Gamma>'', \<Sigma>')"
      and \<Gamma>: "\<Gamma> = fmupd y (ModChecked (Simple y) \<Delta>') fmempty \<uplus> \<Gamma>''"
      by (auto simp: \<iota> Import check_imports.simps vars bind_sum_Ok)
    from Cons.prems(2) have "x = root q' \<or> x \<in> set (declares \<iota>s)"
      by (auto simp: \<iota> Import declares_imports_def split: if_splits)
    with Cons.IH[OF rest] root_variables[OF vars] show ?thesis by (auto simp: \<Gamma>)
  next
    case (FromImport q' xs)
    from Cons.prems(1) obtain \<Sigma>\<^sub>2 \<Delta> \<Sigma>\<^sub>3 \<theta>s \<Gamma>'' where ent: "imports_entries \<M> V \<Sigma>\<^sub>2 q q' \<Delta> xs = Ok (\<theta>s, \<Sigma>\<^sub>3)"
      and rest: "check_imports \<M> V \<Sigma>\<^sub>3 q \<iota>s = Ok (\<Gamma>'', \<Sigma>')" and \<Gamma>: "\<Gamma> = fmap_of_list (zip xs \<theta>s) \<uplus> \<Gamma>''"
      by (auto simp: \<iota> FromImport check_imports.simps bind_sum_Ok split: option.splits)
    from Cons.prems(2) have "x \<in> set xs \<or> x \<in> set (declares \<iota>s)" by (auto simp: \<iota> FromImport declares_imports_def)
    with Cons.IH[OF rest] imports_entries_length[OF ent] show ?thesis by (auto simp: \<Gamma> fset_of_list_elem)
  qed
qed (simp add: check_imports.simps declares_imports_def)

(* Checking of a module with a body *)
lemma check_module_body:
  assumes "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>')" and "fmlookup \<P> q = None"
  obtains \<iota>s t \<Gamma>' \<Sigma>\<^sub>1 \<Gamma>\<^sub>s \<Delta> r
  where "fmlookup \<M> q = Some (ModuleBody \<iota>s t)" and "q \<notin> set V"
    and "check_imports \<M> (V @ [q]) \<Sigma> q \<iota>s = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
    and "redeclared node {} (declarations \<iota>s) = None"
    and "scope Unbound (declares \<iota>s) t = Some \<Gamma>\<^sub>s"
    and "check_assignments_declared {} (assign_targets t) (declares t) (binds t) = Ok ()"
    and "check_top_stmt \<Sigma>\<^sub>1 q (the (fmlookup \<P> builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>')"
    and "(fmdom \<Gamma>' |\<union>| fmdom \<Gamma>\<^sub>s) |\<inter>| fmdom (submods \<M> q) = {||}"
    and "\<Gamma> = submods \<M> q \<otimes> \<Delta>"
  using assms
  by (auto simp: check_module.simps[of \<M> V \<Sigma> q' q] bind_sum_Ok Let_def
      split: if_splits option.splits module_body.splits static_outcome.splits dest!: not_Returns)

(* Submodule of a module with a body: a stub in the module's signature, its name neither declared nor
   assigned by the module *)
lemma check_module_stub:
  assumes "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>')" and "fmlookup \<P> q = None" and "Qualified q x |\<in>| fmdom \<M>"
  obtains \<iota>s t where "fmlookup \<M> q = Some (ModuleBody \<iota>s t)" and "fmlookup \<Gamma> x = Some (ModStub (Qualified q x))"
    and "x \<notin> set (declares \<iota>s)" and "x \<notin> set (declares t)"
proof -
  from assms(1, 2) obtain \<iota>s t \<Gamma>' \<Sigma>\<^sub>1 \<Gamma>\<^sub>s \<Delta> r where M: "fmlookup \<M> q = Some (ModuleBody \<iota>s t)"
    and imp: "check_imports \<M> (V @ [q]) \<Sigma> q \<iota>s = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
    and sc: "scope Unbound (declares \<iota>s) t = Some \<Gamma>\<^sub>s"
    and top: "check_top_stmt \<Sigma>\<^sub>1 q (the (fmlookup \<P> builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>')"
    and X: "(fmdom \<Gamma>' |\<union>| fmdom \<Gamma>\<^sub>s) |\<inter>| fmdom (submods \<M> q) = {||}" and \<Gamma>: "\<Gamma> = submods \<M> q \<otimes> \<Delta>"
    by (rule check_module_body)
  have S: "fmlookup (submods \<M> q) x = Some (ModStub (Qualified q x))" using assms(3) by (simp add: submods_lookup)
  with X have notin: "x |\<notin>| fmdom \<Gamma>'" "x |\<notin>| fmdom \<Gamma>\<^sub>s" by (auto simp: fmlookup_dom_iff fset_eq_iff)
  have \<Gamma>\<^sub>s: "\<Gamma>\<^sub>s = fmconst (assigns t - set (declares \<iota>s)) Unbound" using sc by (simp add: scope_top_def split: if_splits)
  have assigns: "x \<notin> assigns t"
  proof
    assume "x \<in> assigns t"
    with notin(2) have "x \<in> set (declares \<iota>s)"
      by (auto simp: \<Gamma>\<^sub>s fmlookup_dom_iff fmlookup_fmconst[OF finite_Diff[OF finite_assigns_top]] split: if_splits)
    with check_imports_declares[OF imp] notin(1) show False by blast
  qed
  have "x |\<notin>| fmdom \<Delta>"
  proof
    assume "x |\<in>| fmdom \<Delta>"
    from check_top_stmt_bound[OF top this] assigns notin
    have "fmlookup (the (fmlookup \<P> builtins)) x = Some Unbound
      \<or> (\<exists>\<tau>. fmlookup (the (fmlookup \<P> builtins)) x = Some (DU \<tau>))"
      by simp
    with builtins_entry show False by blast
  qed
  with S \<Gamma> have "fmlookup \<Gamma> x = Some (ModStub (Qualified q x))" by simp
  moreover have "x \<notin> set (declares \<iota>s)" using check_imports_declares[OF imp] notin(1) by blast
  moreover have "x \<notin> set (declares t)" using declares_top_assigns assigns by blast
  ultimately show thesis by (rule that[OF M])
qed

(* Classes added by checking from a table: owned by modules not being checked *)
lemma check_module_owners:
  "\<lbrakk> check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>') ; C |\<in>| fmdom \<Sigma>' ; C |\<notin>| fmdom \<Sigma> \<rbrakk>
  \<Longrightarrow> \<exists>p c. C = Qualified p c \<and> p \<notin> set V"
  "\<lbrakk> check_imports \<M> V \<Sigma> q \<iota>s = Ok (\<Gamma>, \<Sigma>') ; C |\<in>| fmdom \<Sigma>' ; C |\<notin>| fmdom \<Sigma> \<rbrakk>
  \<Longrightarrow> \<exists>p c. C = Qualified p c \<and> p \<notin> set V"
  "\<lbrakk> submodules \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs = Ok (\<Gamma>, \<Sigma>') ; C |\<in>| fmdom \<Sigma>' ; C |\<notin>| fmdom \<Sigma> \<rbrakk>
  \<Longrightarrow> \<exists>p c. C = Qualified p c \<and> p \<notin> set V"
  "\<lbrakk> imports_entry \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 x = Ok (\<theta>, \<Sigma>') ; C |\<in>| fmdom \<Sigma>' ; C |\<notin>| fmdom \<Sigma> \<rbrakk>
  \<Longrightarrow> \<exists>p c. C = Qualified p c \<and> p \<notin> set V"
  "\<lbrakk> imports_entries \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs = Ok (\<theta>s, \<Sigma>') ; C |\<in>| fmdom \<Sigma>' ; C |\<notin>| fmdom \<Sigma> \<rbrakk>
  \<Longrightarrow> \<exists>p c. C = Qualified p c \<and> p \<notin> set V"
  "\<lbrakk> check_modules \<M> V \<Sigma> q qs = Ok \<Sigma>' ; C |\<in>| fmdom \<Sigma>' ; C |\<notin>| fmdom \<Sigma> \<rbrakk>
  \<Longrightarrow> \<exists>p c. C = Qualified p c \<and> p \<notin> set V"
proof (induction \<M> V \<Sigma> q' q and \<M> V \<Sigma> q \<iota>s and \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs and \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 x
    and \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs and \<M> V \<Sigma> q qs
    arbitrary: \<Gamma> \<Sigma>' and \<Gamma> \<Sigma>' and \<Gamma> \<Sigma>' and \<theta> \<Sigma>' and \<theta>s \<Sigma>' and \<Sigma>'
    rule: check_module_check_imports_submodules_imports_entry_imports_entries_check_modules.induct)
  case (1 \<M> V \<Sigma> q' q)
  show ?case
  proof (cases "fmlookup \<P> q")
    case (Some \<Gamma>\<^sub>0)
    with "1.prems" show ?thesis by (simp add: check_module.simps[of \<M> V \<Sigma> q' q])
  next
    case None
    from check_module_body[OF "1.prems"(1) None] obtain \<iota>s t \<Gamma>' \<Sigma>\<^sub>1 \<Gamma>\<^sub>s \<Delta> r
      where M: "fmlookup \<M> q = Some (ModuleBody \<iota>s t)" and V: "q \<notin> set V"
      and imp: "check_imports \<M> (V @ [q]) \<Sigma> q \<iota>s = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
      and top: "check_top_stmt \<Sigma>\<^sub>1 q (the (fmlookup \<P> builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>')" .
    show ?thesis
    proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>1")
      case True
      from "1.IH"[OF None V M refl imp True "1.prems"(3)] show ?thesis by auto
    next
      case False
      from check_top_stmt_dom[OF top "1.prems"(2) False] V show ?thesis by blast
    qed
  qed
next
  case (2 \<M> V \<Sigma> q)
  then show ?case by (simp add: check_imports.simps)
next
  case (3 \<M> V \<Sigma> q p q' \<iota>s)
  obtain y ys where vars: "variables q' = y # ys" using variables_nonempty by (cases "variables q'") auto
  from "3.prems"(1) obtain u \<Delta> \<Sigma>\<^sub>1 \<Delta>' \<Sigma>\<^sub>2 \<Gamma>''
    where ens: "ensure (\<not> q \<prec> q') (q, ImportOfContainedModule q' q) = Ok u"
    and m: "check_module \<M> V \<Sigma> q (Simple y) = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and sub: "submodules \<M> V \<Sigma>\<^sub>1 q (Simple y) \<Delta> ys = Ok (\<Delta>', \<Sigma>\<^sub>2)"
    and rest: "check_imports \<M> V \<Sigma>\<^sub>2 q \<iota>s = Ok (\<Gamma>'', \<Sigma>')"
    by (auto simp: check_imports.simps vars bind_sum_Ok)
  show ?case
  proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>1")
    case True
    from "3.IH"(1)[OF vars ens m True "3.prems"(3)] show ?thesis .
  next
    case notin1: False
    show ?thesis
    proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>2")
      case True
      from "3.IH"(2)[OF vars ens m refl sub True notin1] show ?thesis .
    next
      case False
      from "3.IH"(3)[OF vars ens m refl sub refl rest "3.prems"(2) False] show ?thesis .
    qed
  qed
next
  case (4 \<M> V \<Sigma> q p q' xs \<iota>s)
  from "4.prems"(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 \<theta>s \<Sigma>\<^sub>3 \<Gamma>'' where m: "check_module \<M> V \<Sigma> q q' = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and ms: "check_modules \<M> V \<Sigma>\<^sub>1 q (unique_to q' q) = Ok \<Sigma>\<^sub>2" and red: "redeclared id {} xs = None"
    and ent: "imports_entries \<M> V \<Sigma>\<^sub>2 q q' \<Delta> xs = Ok (\<theta>s, \<Sigma>\<^sub>3)"
    and rest: "check_imports \<M> V \<Sigma>\<^sub>3 q \<iota>s = Ok (\<Gamma>'', \<Sigma>')"
    by (auto simp: check_imports.simps bind_sum_Ok split: option.splits)
  have red': "(case redeclared id {} xs of None \<Rightarrow> Ok () | Some x \<Rightarrow> Fail (q, DuplicateImportedName x)) = Ok ()"
    by (simp add: red)
  show ?case
  proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>1")
    case True
    from "4.IH"(1)[OF m True "4.prems"(3)] show ?thesis .
  next
    case notin1: False
    show ?thesis
    proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>2")
      case True
      from "4.IH"(2)[OF m refl ms True notin1] show ?thesis .
    next
      case notin2: False
      show ?thesis
      proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>3")
        case True
        from "4.IH"(3)[OF m refl ms red' ent True notin2] show ?thesis .
      next
        case False
        from "4.IH"(4)[OF m refl ms red' ent refl rest "4.prems"(2) False] show ?thesis .
      qed
    qed
  qed
next
  case (5 \<M> V \<Sigma> q q' \<Gamma>)
  then show ?case by (simp add: submodules.simps)
next
  case (6 \<M> V \<Sigma> q q' \<Gamma> x xs)
  from "6.prems"(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Delta>' where m: "check_module \<M> V \<Sigma> q (Qualified q' x) = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and sub: "submodules \<M> V \<Sigma>\<^sub>1 q (Qualified q' x) \<Delta> xs = Ok (\<Delta>', \<Sigma>')"
    by (auto simp: submodules.simps bind_sum_Ok)
  show ?case
  proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>1")
    case True
    from "6.IH"(1)[OF m True "6.prems"(3)] show ?thesis .
  next
    case False
    from "6.IH"(2)[OF m refl sub "6.prems"(2) False] show ?thesis .
  qed
next
  case (7 \<M> V \<Sigma> q q' \<Gamma> x)
  show ?case
  proof (cases "fmlookup \<Gamma> x")
    case (Some \<theta>')
    show ?thesis
    proof (cases \<theta>')
      case (ModStub q'')
      with Some "7.prems"(1) obtain \<Gamma>' where m: "check_module \<M> V \<Sigma> q q'' = Ok (\<Gamma>', \<Sigma>')"
        by (auto simp: imports_entry.simps bind_sum_Ok)
      from "7.IH"[OF Some ModStub m "7.prems"(2, 3)] show ?thesis .
    qed (use Some "7.prems" in \<open>auto simp: imports_entry.simps split: option.splits\<close>)
  qed (use "7.prems" in \<open>auto simp: imports_entry.simps split: option.splits\<close>)
next
  case (8 \<M> V \<Sigma> q q' \<Gamma>)
  then show ?case by (simp add: imports_entries.simps)
next
  case (9 \<M> V \<Sigma> q q' \<Gamma> x xs)
  from "9.prems"(1) obtain \<theta>' \<Sigma>\<^sub>1 \<theta>s' where e: "imports_entry \<M> V \<Sigma> q q' \<Gamma> x = Ok (\<theta>', \<Sigma>\<^sub>1)"
    and rest: "imports_entries \<M> V \<Sigma>\<^sub>1 q q' \<Gamma> xs = Ok (\<theta>s', \<Sigma>')"
    by (auto simp: imports_entries.simps bind_sum_Ok)
  show ?case
  proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>1")
    case True
    from "9.IH"(1)[OF e True "9.prems"(3)] show ?thesis .
  next
    case False
    from "9.IH"(2)[OF e refl rest "9.prems"(2) False] show ?thesis .
  qed
next
  case (10 \<M> V \<Sigma> q)
  then show ?case by (simp add: check_modules.simps)
next
  case (11 \<M> V \<Sigma> q q' qs)
  from "11.prems"(1) obtain \<Gamma>' \<Sigma>\<^sub>1 where m: "check_module \<M> V \<Sigma> q q' = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
    and rest: "check_modules \<M> V \<Sigma>\<^sub>1 q qs = Ok \<Sigma>'"
    by (auto simp: check_modules.simps bind_sum_Ok)
  show ?case
  proof (cases "C |\<in>| fmdom \<Sigma>\<^sub>1")
    case True
    from "11.IH"(1)[OF m True "11.prems"(3)] show ?thesis .
  next
    case False
    from "11.IH"(2)[OF m refl rest "11.prems"(2) False] show ?thesis .
  qed
qed

end
