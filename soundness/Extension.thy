(* Stability of the type checker under extension of the class table *)
theory Extension
  imports WellFormed
begin

declare meet.simps [simp del] needs_eq_class.simps [simp del]

subsection \<open>Inclusion of class tables\<close>

lemma fmsubset_lookup: "\<lbrakk> \<Sigma> \<subseteq>\<^sub>f \<Sigma>' ; fmlookup \<Sigma> C = Some ce \<rbrakk> \<Longrightarrow> fmlookup \<Sigma>' C = Some ce"
  by (auto simp: fmsubset_alt_def fmpred_iff)

lemma fmsubset_dom: "\<lbrakk> \<Sigma> \<subseteq>\<^sub>f \<Sigma>' ; C |\<in>| fmdom \<Sigma> \<rbrakk> \<Longrightarrow> C |\<in>| fmdom \<Sigma>'"
  by (auto simp: fmlookup_dom_iff dest: fmsubset_lookup)

lemma type_params_mono:
  assumes "\<Sigma> \<subseteq>\<^sub>f \<Sigma>'" and "C |\<in>| fmdom \<Sigma>"
  shows "type_params \<Sigma>' C = type_params \<Sigma> C"
proof -
  from assms(2) obtain ce where "fmlookup \<Sigma> C = Some ce" by (auto simp: fmlookup_dom_iff)
  with fmsubset_lookup[OF assms(1) this] show ?thesis by (simp add: type_params_def)
qed

lemma wf_ty_mono: "\<lbrakk> \<Sigma> \<subseteq>\<^sub>f \<Sigma>' ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma>' \<tau>"
  by (induction \<tau>) (auto simp: type_params_mono dest: fmsubset_dom)

lemma wf_entry_wf_cxt_mono:
  "\<lbrakk> wf_entry \<Sigma> \<theta> ; \<Sigma> \<subseteq>\<^sub>f \<Sigma>' \<rbrakk> \<Longrightarrow> wf_entry \<Sigma>' \<theta>"
  "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; \<Sigma> \<subseteq>\<^sub>f \<Sigma>' \<rbrakk> \<Longrightarrow> wf_cxt \<Sigma>' \<Gamma>"
  by (induction \<Sigma> \<theta> and \<Sigma> \<Gamma> rule: wf_entry_wf_cxt.induct)
     (auto simp: wf_cxt.simps list_all_iff wf_ty_mono intro: fmsubset_dom)

lemmas wf_entry_mono = wf_entry_wf_cxt_mono(1) and wf_cxt_mono = wf_entry_wf_cxt_mono(2)

(* Entry for a type definition of a region whose classes are in the class table, defined in a well-formed
   context without type variables *)
lemma type_entry_wf:
  assumes "tyvars \<Gamma> = {}" and "wf_cxt \<Sigma> \<Gamma>" and "j < length \<chi>s"
    and "\<forall>\<chi> \<in> set \<chi>s. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q c |\<in>| fmdom \<Sigma>"
  shows "wf_entry \<Sigma> (type_entry \<Gamma> q \<chi>s j)"
proof (cases "node (\<chi>s ! j)")
  case (Dataclass c \<alpha>s b \<phi>)
  with assms(4) nth_mem[OF assms(3)] have "Qualified q c |\<in>| fmdom \<Sigma>" by blast
  with Dataclass show ?thesis by (simp add: type_entry_def)
next
  case (TypeStmt x \<alpha>s \<psi>)
  with assms show ?thesis by (simp add: type_entry_def)
qed

lemma type_context_dataclass_wf:
  assumes "tyvars \<Gamma> = {}" and "wf_cxt \<Sigma> \<Gamma>" and "i < length \<chi>s"
    and "\<forall>\<chi> \<in> set \<chi>s. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q c |\<in>| fmdom \<Sigma>"
    and "node (\<chi>s ! i) = Dataclass c \<alpha>s b \<phi>"
  shows "wf_cxt \<Sigma> (type_context \<Gamma> q \<chi>s i)"
proof -
  have cxt: "type_context \<Gamma> q \<chi>s i
    = \<Gamma> \<otimes> fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_entry \<Gamma> q \<chi>s j)) [0..<i])
      \<otimes> fmconst (set \<alpha>s) TypeVar"
    by (simp add: type_context_def Let_def assms(5))
  show ?thesis
    unfolding cxt
    by (intro wf_cxt_add wf_cxt_fmconst wf_cxt_of_list assms(2))
       (auto intro!: type_entry_wf[OF assms(1, 2) _ assms(4)] intro: less_trans[OF _ assms(3)])
qed

subsection \<open>Classes\<close>

(* Well-formed class table \<Sigma> included in \<Sigma>' *)
locale extension =
  fixes \<Sigma> \<Sigma>' :: class_table
  assumes wf_table: "wf_class_table \<Sigma>" and extends: "\<Sigma> \<subseteq>\<^sub>f \<Sigma>'"
    and predefined: "predefined_classes \<subseteq>\<^sub>f \<Sigma>"
begin

lemma range_dom: "range_class |\<in>| fmdom \<Sigma>"
  using fmsubset_dom[OF predefined] by (simp add: predefined_classes_def)

lemma range_params: "type_params \<Sigma> range_class = []"
  using fmsubset_lookup[OF predefined, of range_class] by (simp add: predefined_classes_def type_params_def)

lemma wf_range: "wf_ty \<Sigma> (TyClass range_class [])"
  by (simp add: range_dom range_params)

lemma lookup_ext: "fmlookup \<Sigma> C = Some ce \<Longrightarrow> fmlookup \<Sigma>' C = Some ce"
  by (rule fmsubset_lookup[OF extends])

lemma dom_ext: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> C |\<in>| fmdom \<Sigma>'"
  by (rule fmsubset_dom[OF extends])

lemma type_params_ext: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> type_params \<Sigma>' C = type_params \<Sigma> C"
  by (rule type_params_mono[OF extends])

lemma wf_ty_ext: "wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_ty \<Sigma>' \<tau>"
  by (rule wf_ty_mono[OF extends])

lemma wf_cxt_ext: "wf_cxt \<Sigma> \<Gamma> \<Longrightarrow> wf_cxt \<Sigma>' \<Gamma>"
  by (rule wf_cxt_mono[OF _ extends])

lemma resolve_type'_ext: "wf_cxt \<Sigma> \<Gamma> \<Longrightarrow> resolve_type' \<Sigma>' \<Gamma> A n \<psi> = resolve_type' \<Sigma> \<Gamma> A n \<psi>"
proof (induction n arbitrary: \<Gamma> A \<psi> rule: less_induct)
  case (less n)
  from less.prems show ?case
  proof (induction \<psi>)
    case (TyExprName q \<psi>s)
    have args: "map (resolve_type' \<Sigma>' \<Gamma> A n) \<psi>s = map (resolve_type' \<Sigma> \<Gamma> A n) \<psi>s"
      using TyExprName.IH TyExprName.prems by (intro map_cong) simp_all
    show ?case
    proof (cases "\<psi>s = [] \<and> (case q of Simple x \<Rightarrow> fmlookup \<Gamma> x = Some TypeVar | Qualified _ _ \<Rightarrow> False)")
      case False
      show ?thesis
      proof (cases "resolve_name \<Gamma> q")
        case (Some \<theta>)
        note wf\<theta> = resolve_name_wf[OF TyExprName.prems Some]
        show ?thesis
        proof (cases \<theta>)
          case (Type C)
          with wf\<theta> have "C |\<in>| fmdom \<Sigma>" by simp
          with False Some Type show ?thesis by (simp add: args type_params_ext)
        next
          case (TypeAlias \<Gamma>' q' \<chi>s i)
          with wf\<theta> have wf': "wf_entry \<Sigma> (TypeAlias \<Gamma>' q' \<chi>s i)" by simp
          then obtain x \<alpha>s \<psi>' where \<chi>: "node (\<chi>s ! i) = TypeStmt x \<alpha>s \<psi>'" by auto
          have "resolve_type' \<Sigma>' (type_context \<Gamma>' q' \<chi>s i) ((q', x) # A) n' \<psi>'
                = resolve_type' \<Sigma> (type_context \<Gamma>' q' \<chi>s i) ((q', x) # A) n' \<psi>'"
            if "n = Suc n'" for n'
            using less.IH[OF _ type_context_alias(1)[OF wf' \<chi>]] that by simp
          with False Some TypeAlias \<chi> show ?thesis unfolding resolve_type'.simps args by (cases n) auto
        qed (use False Some in simp_all)
      qed (use False in simp)
    qed (use TyExprName.prems in \<open>cases q, simp_all\<close>)
  qed (simp_all cong: map_cong)
qed

lemma resolve_type_ext: "wf_cxt \<Sigma> \<Gamma> \<Longrightarrow> resolve_type \<Sigma>' \<Gamma> \<psi> = resolve_type \<Sigma> \<Gamma> \<psi>"
  by (simp add: resolve_type_def resolve_type'_ext)

(* Context of a class entry, well-formed *)
lemma class_context_wf:
  assumes "fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i)"
  shows "wf_cxt \<Sigma> (type_context \<Gamma> q \<chi>s i)"
proof -
  have C: "C |\<in>| fmdom \<Sigma>" using assms by (rule fmdomI)
  obtain \<Gamma>' q' \<chi>s' i' c b \<phi> where "fmlookup \<Sigma> C = Some (ClassDef \<Gamma>' q' \<chi>s' i')"
    and "node (\<chi>s' ! i') = Dataclass c (type_params \<Sigma> C) b \<phi>"
    by (rule wf_class_table_dataclass[OF wf_table C])
  with assms have "node (\<chi>s ! i) = Dataclass c (type_params \<Sigma> C) b \<phi>" by simp
  moreover have "tyvars \<Gamma> = {}" and "wf_cxt \<Sigma> \<Gamma>" and "i < length \<chi>s"
    and "\<forall>\<chi> \<in> set \<chi>s. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q c |\<in>| fmdom \<Sigma>"
    using wf_table C assms unfolding wf_class_table_def by blast+
  ultimately show ?thesis by (rule type_context_dataclass_wf[rotated -1])
qed

lemma base_ext: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> base \<Sigma>' C = base \<Sigma> C"
proof -
  assume "C |\<in>| fmdom \<Sigma>"
  then obtain ce where "fmlookup \<Sigma> C = Some ce" by (auto simp: fmlookup_dom_iff)
  then obtain \<Gamma> q \<chi>s i where ce: "fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i)" by (cases ce) simp
  show ?thesis
    unfolding base_def ce lookup_ext[OF ce]
    by (cases "node (\<chi>s ! i)")
       (auto simp: resolve_type_ext[OF class_context_wf[OF ce]] split: option.splits sum.splits ty.splits)
qed

lemma declared_fields_ext: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> declared_fields \<Sigma>' C \<tau>s = declared_fields \<Sigma> C \<tau>s"
proof -
  assume "C |\<in>| fmdom \<Sigma>"
  then obtain ce where "fmlookup \<Sigma> C = Some ce" by (auto simp: fmlookup_dom_iff)
  then obtain \<Gamma> q \<chi>s i where ce: "fmlookup \<Sigma> C = Some (ClassDef \<Gamma> q \<chi>s i)" by (cases ce) simp
  show ?thesis
    unfolding declared_fields_def ce lookup_ext[OF ce]
    by (cases "node (\<chi>s ! i)") (simp_all add: resolve_type_ext[OF class_context_wf[OF ce]] case_prod_beta)
qed

lemma base_dom: "\<lbrakk> C |\<in>| fmdom \<Sigma> ; base \<Sigma> C = Some (D, \<sigma>s) \<rbrakk> \<Longrightarrow> D |\<in>| fmdom \<Sigma>"
  using wf_class_table_baseD[OF wf_table] by simp

lemma inherits_within_ext: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> inherits_within n \<Sigma>' C = inherits_within n \<Sigma> C"
proof (induction n arbitrary: C)
  case (Suc n)
  then show ?case by (auto simp: base_ext dest: base_dom split: option.splits)
qed simp

lemma instantiated_ancestors_upto_ext:
  "C |\<in>| fmdom \<Sigma> \<Longrightarrow> instantiated_ancestors_upto n \<Sigma>' C \<tau>s = instantiated_ancestors_upto n \<Sigma> C \<tau>s"
proof (induction n arbitrary: C \<tau>s)
  case (Suc n)
  then show ?case by (auto simp: base_ext type_params_ext dest: base_dom split: option.splits)
qed simp

lemma instantiated_ancestors_ext:
  assumes "C |\<in>| fmdom \<Sigma>"
  shows "instantiated_ancestors \<Sigma>' C \<tau>s = instantiated_ancestors \<Sigma> C \<tau>s"
proof -
  have "fcard (fmdom \<Sigma>) \<le> fcard (fmdom \<Sigma>')" by (intro fcard_mono fsubsetI dom_ext)
  from instantiated_ancestors_upto_mono[OF wf_class_table_inherits[OF wf_table assms] this] show ?thesis
    unfolding instantiated_ancestors_def by (simp add: instantiated_ancestors_upto_ext[OF assms])
qed

lemma ancestors_ext: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> ancestors \<Sigma>' C = ancestors \<Sigma> C"
  by (simp add: ancestors_def instantiated_ancestors_ext type_params_ext)

lemma instantiated_ancestor_ext:
  "C |\<in>| fmdom \<Sigma> \<Longrightarrow> instantiated_ancestor \<Sigma>' C \<tau>s D = instantiated_ancestor \<Sigma> C \<tau>s D"
  by (simp add: instantiated_ancestor_def instantiated_ancestors_ext)

lemma fields_ext:
  assumes "C |\<in>| fmdom \<Sigma>"
  shows "fields \<Sigma>' C = fields \<Sigma> C"
proof -
  let ?\<tau>s = "map TyVar (type_params \<Sigma> C)"
  have "D |\<in>| fmdom \<Sigma>" if "(D, \<sigma>s) \<in> set (instantiated_ancestors \<Sigma> C ?\<tau>s)" for D \<sigma>s
    using instantiated_ancestors_wf[OF wf_table _ that] assms by simp
  then show ?thesis
    by (auto simp: fields_def Let_def type_params_ext[OF assms] instantiated_ancestors_ext[OF assms]
        declared_fields_ext intro!: arg_cong[where f = concat] arg_cong[where f = rev] map_cong)
qed

lemma field_types_ext: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> field_types \<Sigma>' C \<sigma>s = field_types \<Sigma> C \<sigma>s"
  by (simp add: field_types_def fields_ext)

lemma field_names_ext: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> field_names \<Sigma>' C = field_names \<Sigma> C"
  by (simp add: field_names_def fields_ext)

subsection \<open>Subtyping\<close>

lemma subty_ext_imp:
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: \<tau> ; wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<Sigma>' \<turnstile> \<sigma> <: \<tau>"
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s ; \<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma> ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<Sigma>' \<turnstile> \<sigma>s [<:] \<tau>s"
proof (induction rule: subty_subtys.inducts)
  case (SubtyClassExtend C D \<sigma>s \<tau>s \<tau>')
  from SubtyClassExtend(4) have C: "C |\<in>| fmdom \<Sigma>" by simp
  have IH: "\<Sigma>' \<turnstile> TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s) <: \<tau>'"
    using SubtyClassExtend(3)[OF wf_class_table_base[OF wf_table SubtyClassExtend(4) SubtyClassExtend(1)]
        SubtyClassExtend(5)] .
  show ?case
  proof (rule subty_subtys.SubtyClassExtend)
    show "base \<Sigma>' C = Some (D, \<sigma>s)" using SubtyClassExtend(1) by (simp add: base_ext[OF C])
    show "\<Sigma>' \<turnstile> TyClass D (map (subst \<tau>s (type_params \<Sigma>' C)) \<sigma>s) <: \<tau>'"
      using IH by (simp add: type_params_ext[OF C])
  qed
next
  case SubtyUnionLeft
  then show ?case by (auto intro: subty_subtys.SubtyUnionLeft)
next
  case SubtyUnionRight
  then show ?case by (auto intro: subty_subtys.SubtyUnionRight)
qed (auto intro: subty_subtys.intros(1, 3-12, 15-))

lemma subty_ext_rev:
  "\<lbrakk> \<Sigma>' \<turnstile> \<sigma> <: \<tau> ; wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>"
  "\<lbrakk> \<Sigma>' \<turnstile> \<sigma>s [<:] \<tau>s ; \<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma> ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s"
proof (induction rule: subty_subtys.inducts)
  case (SubtyClassExtend C D \<sigma>s \<tau>s \<tau>')
  from SubtyClassExtend(4) have C: "C |\<in>| fmdom \<Sigma>" by simp
  with SubtyClassExtend(1) have base: "base \<Sigma> C = Some (D, \<sigma>s)" by (simp add: base_ext)
  from SubtyClassExtend(3)[OF _ SubtyClassExtend(5)]
    wf_class_table_base[OF wf_table SubtyClassExtend(4) base]
  show ?case by (auto simp: type_params_ext[OF C] intro: subty_subtys.SubtyClassExtend[OF base])
next
  case SubtyUnionLeft
  then show ?case by (auto intro: subty_subtys.SubtyUnionLeft)
next
  case SubtyUnionRight
  then show ?case by (auto intro: subty_subtys.SubtyUnionRight)
qed (auto intro: subty_subtys.intros(1, 3-12, 15-))

lemma subty_ext: "\<lbrakk> wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> (\<Sigma>' \<turnstile> \<sigma> <: \<tau>) = (\<Sigma> \<turnstile> \<sigma> <: \<tau>)"
  using subty_ext_imp(1) subty_ext_rev(1) by blast

lemma join_ext: "\<lbrakk> wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<sigma> \<squnion>\<^bsub>\<Sigma>'\<^esub> \<tau> = \<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>"
  by (simp add: join_def subty_ext)

lemma joins_ext: "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<Longrightarrow> joins \<Sigma>' \<tau>s = joins \<Sigma> \<tau>s"
  by (induction \<tau>s) (simp_all add: joins_def join_ext wf_joins[unfolded joins_def])

end


subsection \<open>Meets, elements, subscripts and attributes\<close>

lemma meet_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> meet \<Sigma>' \<sigma> \<tau> = meet \<Sigma> \<sigma> \<tau>"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_ty \<Sigma> \<sigma>' ; wf_ty \<Sigma> \<tau>' \<rbrakk> \<Longrightarrow> meet_incomparable \<Sigma>' \<sigma>' \<tau>' = meet_incomparable \<Sigma> \<sigma>' \<tau>'"
proof (induction \<Sigma> \<sigma> \<tau> and \<Sigma> \<sigma>' \<tau>' rule: meet_meet_incomparable.induct)
  case (1 \<Sigma> \<sigma> \<tau>)
  then show ?case by (auto simp: meet.simps extension.subty_ext)
next
  case (4 \<Sigma> \<sigma>s \<sigma> \<tau>s \<tau>)
  show ?case
  proof (cases "length \<sigma>s = length \<tau>s")
    case True
    have "a \<squnion>\<^bsub>\<Sigma>'\<^esub> b = a \<squnion>\<^bsub>\<Sigma>\<^esub> b" if "(a, b) \<in> set (zip \<sigma>s \<tau>s)" for a b
      using "4.prems" set_zip_leftD[OF that] set_zip_rightD[OF that] by (auto intro: extension.join_ext)
    then have "map2 (\<lambda>\<sigma>' \<tau>'. \<sigma>' \<squnion>\<^bsub>\<Sigma>'\<^esub> \<tau>') \<sigma>s \<tau>s = map2 (\<lambda>\<sigma>' \<tau>'. \<sigma>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') \<sigma>s \<tau>s"
      by (intro map_cong[OF refl]) auto
    with "4.IH"[OF True] "4.prems" True show ?thesis by simp
  qed simp
next
  case (5 \<Sigma> \<sigma>s \<tau>s)
  show ?case
  proof (cases "length \<sigma>s = length \<tau>s")
    case True
    have "meet \<Sigma>' a b = meet \<Sigma> a b" if "(a, b) \<in> set (zip \<sigma>s \<tau>s)" for a b
      using "5.IH"[OF True that refl] "5.prems" set_zip_leftD[OF that] set_zip_rightD[OF that] by auto
    then have "map2 (meet \<Sigma>') \<sigma>s \<tau>s = map2 (meet \<Sigma>) \<sigma>s \<tau>s" by (intro map_cong[OF refl]) auto
    with True show ?thesis by simp
  qed simp
qed (auto simp: extension.subty_ext extension.join_ext wf_meet)

context extension
begin

lemmas meet_ext = meet_mono(1)[OF extension_axioms]

lemma elem_type_ext: "wf_ty \<Sigma> \<tau> \<Longrightarrow> elem_type \<Sigma>' \<tau> = elem_type \<Sigma> \<tau>"
proof (induction \<tau>)
  case (TyUnion \<sigma> \<tau>)
  then show ?case by (auto simp: join_ext wf_elem_type split: option.splits)
next
  case (TyTuple \<tau>s)
  then have "\<forall>\<tau> \<in> set (map base_type \<tau>s). wf_ty \<Sigma> \<tau>" by (auto intro: wf_base_type)
  then show ?case by (simp add: joins_ext)
next
  case (TyPrim p)
  then show ?case by (cases p) simp_all
next
  case (TyLiteral l)
  then show ?case by (cases l) simp_all
next
  case (TyClass C \<tau>s)
  then show ?case by (cases \<tau>s) simp_all
qed simp_all

lemma subscript_type_ext:
  "wf_ty \<Sigma> \<sigma> \<Longrightarrow> subscript_type \<Sigma>' \<sigma> int_ok str_ok p idx = subscript_type \<Sigma> \<sigma> int_ok str_ok p idx"
proof (induction \<sigma>)
  case (TyUnion \<sigma> \<sigma>')
  then show ?case by (auto simp: bind_sum_def join_ext subscript_type_wf split: sum.splits)
next
  case (TyTuple \<tau>s)
  then show ?case by (auto simp: bind_sum_def joins_ext split: sum.splits ty.splits lit.splits prim_ty.splits)
qed simp_all

lemma attribute_type_ext: "wf_ty \<Sigma> \<sigma> \<Longrightarrow> attribute_type \<Sigma>' \<sigma> x = attribute_type \<Sigma> \<sigma> x"
proof (induction \<sigma>)
  case (TyUnion \<sigma> \<sigma>')
  then show ?case by (auto simp: bind_sum_def join_ext attribute_type_wf[OF wf_table] split: sum.splits)
qed (simp_all add: fields_ext)

lemma subtyping_rule_ext: "wf_ty \<Sigma> \<sigma> \<Longrightarrow> subtyping_rule \<Sigma>' \<sigma> \<tau> = subtyping_rule \<Sigma> \<sigma> \<tau>"
  by (cases "(\<Sigma>', \<sigma>, \<tau>)" rule: subtyping_rule.cases) (auto simp: base_ext)

lemma mismatch_ext: "wf_ty \<Sigma> \<sigma> \<Longrightarrow> mismatch \<Sigma>' \<tau> \<sigma> = mismatch \<Sigma> \<tau> \<sigma>"
  by (simp add: mismatch_def subtyping_rule_ext)

subsection \<open>Instances and type arguments\<close>

lemma instance_above_ext:
  assumes "wf_ty \<Sigma> \<tau>" and "C |\<in>| fmdom \<Sigma>"
  shows "instance_above \<Sigma>' C \<tau> = instance_above \<Sigma> C \<tau>"
proof (cases \<tau>)
  case (TyPrim p)
  then show ?thesis using assms by (cases p) (simp_all add: type_params_ext)
qed (use assms in \<open>auto simp: ancestors_ext instantiated_ancestor_ext\<close>)

lemma instance_below_ext:
  assumes "wf_ty \<Sigma> \<tau>" and "C |\<in>| fmdom \<Sigma>"
  shows "instance_below \<Sigma>' C \<tau> = instance_below \<Sigma> C \<tau>"
proof (cases \<tau>)
  case (TyClass D \<sigma>s)
  let ?\<alpha>s = "type_params \<Sigma> C"
  have eq: "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma>' \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> C \<tau>s D) \<sigma>s
          = list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> C \<tau>s D) \<sigma>s"
    if m: "match_args_seq (instantiated_ancestor \<Sigma> C (map TyVar ?\<alpha>s) D) \<sigma>s = Matched \<gamma>"
    and args: "type_args_of \<gamma> ?\<alpha>s = Ok \<tau>s" and anc: "D \<in> set (ancestors \<Sigma> C)" for \<gamma> \<tau>s
  proof -
    have wf\<sigma>s: "\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>" using assms(1) TyClass by simp
    have "wf_ty \<Sigma> \<tau>" if "\<tau> \<in> set \<tau>s" for \<tau>
      using type_args_of_elem[OF args that] match_args_seq_bound[OF m _ wf\<sigma>s] by blast
    then have "wf_ty \<Sigma> (TyClass C \<tau>s)" using assms(2) type_args_of_length[OF args] by simp
    from instantiated_ancestor_wf[OF wf_table this anc]
    have "\<forall>\<rho> \<in> set (instantiated_ancestor \<Sigma> C \<tau>s D). wf_ty \<Sigma> \<rho>" by simp
    with wf\<sigma>s show ?thesis unfolding list_all2_conv_all_nth by (auto simp: subty_ext nth_mem)
  qed
  show ?thesis
    using assms TyClass
    by (auto simp: Let_def ancestors_ext type_params_ext instantiated_ancestor_ext eq
        split: arg_match.splits sum.splits)
next
  case (TyPrim p)
  then show ?thesis using assms by (cases p) (simp_all add: type_params_ext)
qed simp_all

lemma instance_at_ext: "\<lbrakk> wf_ty \<Sigma> \<tau> ; C |\<in>| fmdom \<Sigma> \<rbrakk> \<Longrightarrow> instance_at \<Sigma>' C \<tau> = instance_at \<Sigma> C \<tau>"
  by (auto simp: instance_at_def instance_above_ext instance_below_ext split: instances.splits)

(* Bindings of type variables at well-formed types *)
definition wf_bindings :: "(var, ty) fmap \<Rightarrow> bool"
where
"wf_bindings \<gamma> = (\<forall>\<alpha> \<tau>. fmlookup \<gamma> \<alpha> = Some \<tau> \<longrightarrow> wf_ty \<Sigma> \<tau>)"

lemma join_cxt_ext:
  assumes "wf_bindings \<gamma>" and "wf_bindings \<gamma>'"
  shows "join_cxt \<Sigma>' \<gamma> \<gamma>' = join_cxt \<Sigma> \<gamma> \<gamma>'"
proof (rule fmap_ext)
  fix \<alpha>
  show "fmlookup (join_cxt \<Sigma>' \<gamma> \<gamma>') \<alpha> = fmlookup (join_cxt \<Sigma> \<gamma> \<gamma>') \<alpha>"
    using assms unfolding wf_bindings_def
    by (cases "fmlookup \<gamma> \<alpha>"; cases "fmlookup \<gamma>' \<alpha>") (auto simp: join_cxt_def fmlookup_fmmap_keys join_ext)
qed

lemma wf_bindings_join_cxt: "\<lbrakk> wf_bindings \<gamma> ; wf_bindings \<gamma>' \<rbrakk> \<Longrightarrow> wf_bindings (join_cxt \<Sigma> \<gamma> \<gamma>')"
  unfolding wf_bindings_def by (auto elim!: join_cxt_lookup intro: wf_join)

lemma wf_bindings_empty: "wf_bindings fmempty"
  by (simp add: wf_bindings_def)

lemma wf_bindings_foldr: "\<forall>\<gamma> \<in> set \<gamma>s. wf_bindings \<gamma> \<Longrightarrow> wf_bindings (foldr (join_cxt \<Sigma>) \<gamma>s fmempty)"
  by (induction \<gamma>s) (simp_all add: wf_bindings_empty wf_bindings_join_cxt)

lemma wf_bindings_type_args: "wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_bindings (type_args \<Sigma> \<alpha>s \<sigma> \<tau>)"
  unfolding wf_bindings_def using type_args_range(1)[OF wf_table] by blast

lemma instance_at_wf_ext: "\<lbrakk> wf_ty \<Sigma> \<tau> ; instance_at \<Sigma> C \<tau> = Instance \<tau>s \<rbrakk> \<Longrightarrow> \<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>'"
  using instance_at_wf[OF wf_table] by blast

end

lemma type_args_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> type_args \<Sigma>' \<alpha>s \<sigma> \<tau> = type_args \<Sigma> \<alpha>s \<sigma> \<tau>"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; \<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma> ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<rbrakk>
  \<Longrightarrow> type_args_seq \<Sigma>' \<alpha>s \<sigma>s \<tau>s = type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s"
proof (induction \<Sigma> \<alpha>s \<sigma> \<tau> and \<Sigma> \<alpha>s \<sigma>s \<tau>s rule: type_args_type_args_seq.induct)
  case (10 \<Sigma> \<alpha>s \<sigma>s \<tau>s)
  interpret extension \<Sigma> \<Sigma>' by fact
  have "type_args \<Sigma>' \<alpha>s \<sigma> \<tau> = type_args \<Sigma> \<alpha>s \<sigma> \<tau>" if "(\<sigma>, \<tau>) \<in> set (zip \<sigma>s \<tau>s)" for \<sigma> \<tau>
    using "10.IH"[OF that refl "10.prems"(1)] "10.prems"(2, 3) set_zip_leftD[OF that] set_zip_rightD[OF that]
    by auto
  then have args: "map2 (type_args \<Sigma>' \<alpha>s) \<sigma>s \<tau>s = map2 (type_args \<Sigma> \<alpha>s) \<sigma>s \<tau>s"
    by (intro map_cong[OF refl]) auto
  have "foldr (join_cxt \<Sigma>') \<gamma>s fmempty = foldr (join_cxt \<Sigma>) \<gamma>s fmempty" if "\<forall>\<gamma> \<in> set \<gamma>s. wf_bindings \<gamma>" for \<gamma>s
    using that by (induction \<gamma>s) (simp_all add: join_cxt_ext wf_bindings_foldr)
  moreover have "\<forall>\<gamma> \<in> set (map2 (type_args \<Sigma> \<alpha>s) \<sigma>s \<tau>s). wf_bindings \<gamma>"
    using "10.prems"(3) by (auto dest: set_zip_rightD intro: wf_bindings_type_args)
  ultimately show ?case by (simp add: args)
qed (auto simp: extension.join_cxt_ext extension.wf_bindings_type_args extension.instance_at_ext
     extension.subty_ext extension.instance_at_wf_ext split: instances.splits)

context extension
begin

lemmas type_args_ext = type_args_mono(1)[OF extension_axioms]
  and type_args_seq_ext = type_args_mono(2)[OF extension_axioms]

subsection \<open>Operators\<close>

lemma needs_eq_dom_ext: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> (C, \<xi>) \<in> needs_eq_dom \<Sigma>' \<longleftrightarrow> (C, \<xi>) \<in> needs_eq_dom \<Sigma>"
  by (auto simp: needs_eq_dom_mem fmlookup_dom_iff type_params_ext dest: lookup_ext split: option.splits)

end

lemma needs_eq_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> needs_eq \<Sigma>' D \<tau> \<xi> = needs_eq \<Sigma> D \<tau> \<xi>"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; C |\<in>| fmdom \<Sigma> \<rbrakk> \<Longrightarrow> needs_eq_class \<Sigma>' D C \<xi> = needs_eq_class \<Sigma> D C \<xi>"
proof (induction \<Sigma> D \<tau> \<xi> and \<Sigma> D C \<xi> rule: needs_eq_needs_eq_class.induct)
  case (7 \<Sigma> D C \<sigma>s \<xi>)
  interpret extension \<Sigma> \<Sigma>' by fact
  have C: "C |\<in>| fmdom \<Sigma>" using "7.prems"(2) by simp
  have *: "needs_eq_class \<Sigma>' D C (Some \<alpha>) = needs_eq_class \<Sigma> D C (Some \<alpha>)
           \<and> needs_eq \<Sigma>' D \<sigma> \<xi> = needs_eq \<Sigma> D \<sigma> \<xi>"
    if "(\<alpha>, \<sigma>) \<in> set (zip (type_params \<Sigma> C) \<sigma>s)" for \<alpha> \<sigma>
    using "7.IH" that "7.prems" C set_zip_rightD[OF that] by auto
  have eq: "list_ex (\<lambda>(\<alpha>, \<sigma>). needs_eq_class \<Sigma>' D C (Some \<alpha>) \<and> needs_eq \<Sigma>' D \<sigma> \<xi>) (zip (type_params \<Sigma> C) \<sigma>s)
          = list_ex (\<lambda>(\<alpha>, \<sigma>). needs_eq_class \<Sigma> D C (Some \<alpha>) \<and> needs_eq \<Sigma> D \<sigma> \<xi>) (zip (type_params \<Sigma> C) \<sigma>s)"
    unfolding list_ex_iff by (rule bex_cong[OF refl]) (auto simp: * split: prod.splits)
  have none: "needs_eq_class \<Sigma>' D C None = needs_eq_class \<Sigma> D C None" if "\<xi> = None"
    using "7.IH" that "7.prems" C by auto
  show ?case unfolding needs_eq.simps type_params_ext[OF C] eq by (cases \<xi>) (simp_all add: none)
next
  case (9 \<Sigma> D C \<xi>)
  interpret extension \<Sigma> \<Sigma>' by fact
  obtain x\<tau>s where fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<tau>s"
    by (simp add: fields_ancestor_fields)
  have wf: "wf_ty \<Sigma> \<tau>" if "(x, \<tau>) \<in> set x\<tau>s" for x \<tau>
  proof -
    have "(x, \<tau>) \<in> set (instantiate (fields \<Sigma> C) (map TyVar (type_params \<Sigma> C)))"
      using that by (simp add: fields case_prod_beta)
    moreover have "wf_ty \<Sigma> (TyClass C (map TyVar (type_params \<Sigma> C)))" using "9.prems"(2) by simp
    ultimately show ?thesis by (rule fields_wf[OF wf_table, rotated])
  qed
  have IH: "needs_eq \<Sigma>' (insert (C, \<xi>) D) \<tau> \<xi> = needs_eq \<Sigma> (insert (C, \<xi>) D) \<tau> \<xi>"
    if "(C, \<xi>) \<in> needs_eq_dom \<Sigma> \<and> (C, \<xi>) \<notin> D" and "(x, \<tau>) \<in> set x\<tau>s" for x \<tau>
    using "9.IH"[OF that(1) fields that(2) refl "9.prems"(1) wf[OF that(2)]] .
  have eq: "list_ex (\<lambda>(_, \<tau>). needs_eq \<Sigma>' (insert (C, \<xi>) D) \<tau> \<xi>) x\<tau>s
          = list_ex (\<lambda>(_, \<tau>). needs_eq \<Sigma> (insert (C, \<xi>) D) \<tau> \<xi>) x\<tau>s"
    if "(C, \<xi>) \<in> needs_eq_dom \<Sigma> \<and> (C, \<xi>) \<notin> D"
    unfolding list_ex_iff by (rule bex_cong[OF refl]) (auto simp: IH[OF that] split: prod.splits)
  show ?case
    unfolding needs_eq_class.simps needs_eq_dom_ext[OF "9.prems"(2)] fields_ext[OF "9.prems"(2)] fields
    by (simp add: eq)
qed (auto simp: list_ex_iff)

context extension
begin

lemmas needs_eq_ext = needs_eq_mono(1)[OF extension_axioms]

lemma equality_type_ext: "wf_ty \<Sigma> \<tau> \<Longrightarrow> equality_type \<Sigma>' \<tau> = equality_type \<Sigma> \<tau>"
  by (simp add: equality_type_def needs_eq_ext)

lemma binop_overload_ext:
  assumes "wf_ty \<Sigma> \<sigma>\<^sub>1" and "wf_ty \<Sigma> \<sigma>\<^sub>2"
  shows "binop_overload \<Sigma>' op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega> = binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega>"
proof
  assume "binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega>"
  then show "binop_overload \<Sigma>' op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega>"
    using assms
    by (induction rule: binop_overload.induct)
       (auto simp: subty_ext equality_type_ext joins_ext join_ext[symmetric] wf_base_type wf_joins
        intro: binop_overload.intros)
next
  assume "binop_overload \<Sigma>' op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega>"
  then show "binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega>"
    using assms
    by (induction rule: binop_overload.induct)
       (auto simp: subty_ext equality_type_ext joins_ext join_ext wf_base_type wf_joins
        intro: binop_overload.intros)
qed

lemma unop_overload_ext:
  assumes "wf_ty \<Sigma> \<sigma>"
  shows "unop_overload \<Sigma>' op \<sigma> \<omega> = unop_overload \<Sigma> op \<sigma> \<omega>"
proof
  assume "unop_overload \<Sigma> op \<sigma> \<omega>"
  then show "unop_overload \<Sigma>' op \<sigma> \<omega>"
    using assms
    by (induction rule: unop_overload.induct) (auto simp: subty_ext wf_base_type intro: unop_overload.intros)
next
  assume "unop_overload \<Sigma>' op \<sigma> \<omega>"
  then show "unop_overload \<Sigma> op \<sigma> \<omega>"
    using assms
    by (induction rule: unop_overload.induct) (auto simp: subty_ext wf_base_type intro: unop_overload.intros)
qed

lemma binop_overloads_ext:
  "\<lbrakk> wf_ty \<Sigma> \<sigma>\<^sub>1 ; wf_ty \<Sigma> \<sigma>\<^sub>2 \<rbrakk> \<Longrightarrow> binop_overloads \<Sigma>' op \<sigma>\<^sub>1 \<sigma>\<^sub>2 = binop_overloads \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2"
  by (simp add: binop_overloads_def binop_overload_ext)

lemma unop_overloads_ext: "wf_ty \<Sigma> \<sigma> \<Longrightarrow> unop_overloads \<Sigma>' op \<sigma> = unop_overloads \<Sigma> op \<sigma>"
  by (simp add: unop_overloads_def unop_overload_ext)

lemma resolve_binop_ext:
  assumes "wf_ty \<Sigma> \<sigma>\<^sub>1" and "wf_ty \<Sigma> \<sigma>\<^sub>2"
  shows "resolve_binop \<Sigma>' op \<sigma>\<^sub>1 \<sigma>\<^sub>2 = resolve_binop \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2"
proof -
  let ?O = "binop_overloads \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2"
  have wf: "wf_ty \<Sigma> \<tau>\<^sub>1 \<and> wf_ty \<Sigma> \<tau>\<^sub>2" if "((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>) \<in> ?O" for \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>
    using binop_overload_operands[OF _ assms] that by (auto simp: binop_overloads_def)
  have inner: "(\<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> ?O. \<Sigma>' \<turnstile> \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<Sigma>' \<turnstile> \<tau>\<^sub>2 <: \<tau>\<^sub>2')
             = (\<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> ?O. \<Sigma> \<turnstile> \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<Sigma> \<turnstile> \<tau>\<^sub>2 <: \<tau>\<^sub>2')"
    if "((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>) \<in> ?O" for \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>
    using wf[OF that] by (intro ball_cong[OF refl]) (auto simp: subty_ext dest: wf split: prod.splits)
  have "Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> ?O. \<Sigma>' \<turnstile> \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<Sigma>' \<turnstile> \<tau>\<^sub>2 <: \<tau>\<^sub>2') ?O
      = Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> ?O. \<Sigma> \<turnstile> \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<Sigma> \<turnstile> \<tau>\<^sub>2 <: \<tau>\<^sub>2') ?O"
  proof (rule set_eqI)
    fix \<omega> :: "(ty \<times> ty) \<times> ty"
    obtain \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau> where \<omega>: "\<omega> = ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>)" by (metis prod.collapse)
    show "\<omega> \<in> Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> ?O. \<Sigma>' \<turnstile> \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<Sigma>' \<turnstile> \<tau>\<^sub>2 <: \<tau>\<^sub>2') ?O
       \<longleftrightarrow> \<omega> \<in> Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> ?O. \<Sigma> \<turnstile> \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<Sigma> \<turnstile> \<tau>\<^sub>2 <: \<tau>\<^sub>2') ?O"
      unfolding \<omega> by (cases "((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>) \<in> ?O") (simp_all add: inner)
  qed
  then show ?thesis by (simp add: resolve_binop_def Let_def binop_overloads_ext[OF assms])
qed

lemma resolve_unop_ext:
  assumes "wf_ty \<Sigma> \<sigma>"
  shows "resolve_unop \<Sigma>' op \<sigma> = resolve_unop \<Sigma> op \<sigma>"
proof -
  let ?O = "unop_overloads \<Sigma> op \<sigma>"
  have wf: "wf_ty \<Sigma> \<tau>" if "(\<tau>, \<tau>') \<in> ?O" for \<tau> \<tau>'
    using unop_overload_types that by (fastforce simp: unop_overloads_def)
  have inner: "(\<forall>(\<tau>', _) \<in> ?O. \<Sigma>' \<turnstile> \<tau> <: \<tau>') = (\<forall>(\<tau>', _) \<in> ?O. \<Sigma> \<turnstile> \<tau> <: \<tau>')" if "(\<tau>, \<tau>'') \<in> ?O" for \<tau> \<tau>''
    using wf[OF that] by (intro ball_cong[OF refl]) (auto simp: subty_ext dest: wf split: prod.splits)
  have "Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> ?O. \<Sigma>' \<turnstile> \<tau> <: \<tau>') ?O
      = Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> ?O. \<Sigma> \<turnstile> \<tau> <: \<tau>') ?O"
  proof (rule set_eqI)
    fix \<omega> :: "ty \<times> ty"
    obtain \<tau> \<tau>'' where \<omega>: "\<omega> = (\<tau>, \<tau>'')" by (cases \<omega>)
    show "\<omega> \<in> Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> ?O. \<Sigma>' \<turnstile> \<tau> <: \<tau>') ?O
       \<longleftrightarrow> \<omega> \<in> Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> ?O. \<Sigma> \<turnstile> \<tau> <: \<tau>') ?O"
      unfolding \<omega> by (cases "(\<tau>, \<tau>'') \<in> ?O") (simp_all add: inner)
  qed
  then show ?thesis by (simp add: resolve_unop_def Let_def unop_overloads_ext[OF assms])
qed

lemma resolve_binop_union_ext:
  "\<lbrakk> wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<sigma>' \<rbrakk> \<Longrightarrow> resolve_binop_union \<Sigma>' op \<sigma> \<sigma>' = resolve_binop_union \<Sigma> op \<sigma> \<sigma>'"
proof (induction "size \<sigma> + size \<sigma>'" arbitrary: \<sigma> \<sigma>' rule: less_induct)
  case less
  have IH: "resolve_binop_union \<Sigma>' op \<rho> \<rho>' = resolve_binop_union \<Sigma> op \<rho> \<rho>'"
    if "size \<rho> + size \<rho>' < size \<sigma> + size \<sigma>'" and "wf_ty \<Sigma> \<rho>" and "wf_ty \<Sigma> \<rho>'" for \<rho> \<rho>'
    using less.hyps[OF that] .
  have wf: "wf_ty \<Sigma> \<tau>" if "resolve_binop_union \<Sigma> op \<rho> \<rho>' = Some \<tau>" and "wf_ty \<Sigma> \<rho>" and "wf_ty \<Sigma> \<rho>'" for \<rho> \<rho>' \<tau>
    using resolve_binop_union_wf[OF that(2, 3) that(1)] by simp
  show ?case
  proof (cases "resolve_binop \<Sigma> op \<sigma> \<sigma>'")
    case (Some \<tau>)
    then show ?thesis
      unfolding resolve_binop_union.simps[of \<Sigma>' op \<sigma> \<sigma>'] resolve_binop_union.simps[of \<Sigma> op \<sigma> \<sigma>']
      by (simp del: resolve_binop_union.simps add: resolve_binop_ext[OF less.prems])
  next
    case None
    then show ?thesis
      unfolding resolve_binop_union.simps[of \<Sigma>' op \<sigma> \<sigma>'] resolve_binop_union.simps[of \<Sigma> op \<sigma> \<sigma>']
      using less.prems
      by (cases \<sigma>; cases \<sigma>')
         (auto simp del: resolve_binop_union.simps
          simp add: resolve_binop_ext IH join_ext wf split: option.splits Option.bind_splits)
  qed
qed

subsection \<open>Values of a type\<close>

lemma has_float_values_ext: "wf_ty \<Sigma> \<tau> \<Longrightarrow> has_float_values \<Sigma>' \<tau> = has_float_values \<Sigma> \<tau>"
proof (induction \<tau>)
  case (TyLiteral l)
  then show ?case by (cases l) (simp_all add: subty_ext)
qed (simp_all add: subty_ext)

lemma has_dict_values_ext: "wf_ty \<Sigma> \<tau> \<Longrightarrow> has_dict_values \<Sigma>' \<tau> = has_dict_values \<Sigma> \<tau>"
  by (induction \<tau>) (auto simp: subty_ext)

end

lemma has_values_mono: "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> has_values \<Sigma>' k \<tau> = has_values \<Sigma> k \<tau>"
  by (induction \<Sigma> k \<tau> rule: has_values.induct)
     (auto simp: extension.subty_ext extension.range_dom extension.range_params)

context extension
begin

lemmas has_values_ext = has_values_mono[OF extension_axioms]

end

end
