(* Soundness of evaluation of subscripts and attributes *)
theory Attributes
  imports Expressions
begin

context evaluation
begin

(* Element at an integer index of a sequence with elements satisfying P, or an index error *)
lemma getitem_elems:
  assumes "elems v = Some vs" and "\<forall>u \<in> set vs. P u"
  shows "wf_result P (getitem v (VLit (LitInt n)))"
  using assms by (cases v rule: elems.cases) (auto simp: Let_def nat_less_iff)

(* String, as a sequence of strings *)
lemma str_elems: "\<exists>vs. elems (VLit (LitString w)) = Some vs \<and> (\<forall>u \<in> set vs. \<turnstile> u : Ty (TyPrim str))"
  by (auto intro: wf_str_char)

(* Subscript of a value typed at a type with base type str *)
lemma subscript_str:
  assumes "base_type \<sigma> = TyPrim str" and "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    and "wf_result (\<lambda>u. \<exists>n. u = VLit (LitInt n)) r"
  shows "result_typed (mlet r (getitem v)) (TyPrim str)"
proof -
  have "\<exists>w. v = VLit (LitString w)"
  proof (cases \<sigma>)
    case (TyPrim p)
    with assms(1, 2) show ?thesis by (auto dest: wf_str[OF _ SubtyRefl])
  next
    case (TyLiteral l)
    with assms(1, 2) show ?thesis by (cases l) (auto dest: wf_lit)
  qed (use assms(1) in simp_all)
  then obtain w where v: "v = VLit (LitString w)" by blast
  from str_elems obtain vs where "elems v = Some vs" and "\<forall>u \<in> set vs. \<turnstile> u : Ty (TyPrim str)"
    unfolding v by blast
  note get = getitem_elems[OF this]
  with assms(3) show ?thesis by (cases r) auto
qed

(* Result of a subscript of a value typed at \<sigma>, with the index typed by the checks and synthesis supplied to
   the typing of the subscript *)
lemma subscript_result:
  assumes "subscript_type \<Sigma> \<sigma> int_ok str_ok p idx = Ok \<tau>" and "\<turnstile> v : Ty (inst \<eta> \<sigma>)" and "wf_inst \<Sigma> \<eta>"
    and int: "int_ok = Ok () \<Longrightarrow> wf_result (\<lambda>u. \<exists>n. u = VLit (LitInt n)) r"
    and str: "str_ok = Ok () \<Longrightarrow> wf_result (\<lambda>u. \<exists>w. u = VLit (LitString w)) r"
    and idx: "\<And>\<iota>. idx = Ok \<iota> \<Longrightarrow> result_typed r (inst \<eta> \<iota>)"
  shows "result_typed (mlet r (getitem v)) (inst \<eta> \<tau>)"
  using assms(1, 2)
proof (induction \<sigma> arbitrary: \<tau> v)
  case (TyUnion \<sigma>1 \<sigma>2)
  from TyUnion.prems(1) obtain \<tau>1 \<tau>2 where \<tau>1: "subscript_type \<Sigma> \<sigma>1 int_ok str_ok p idx = Ok \<tau>1"
    and \<tau>2: "subscript_type \<Sigma> \<sigma>2 int_ok str_ok p idx = Ok \<tau>2" and \<tau>: "\<tau> = \<tau>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>2"
    by (auto simp: bind_sum_def split: sum.splits)
  have wf: "wf_ty \<Sigma> \<tau>"
    using subscript_type_wf[OF wf_ty_inst_inv[OF wf_val_ty[OF TyUnion.prems(2)]] TyUnion.prems(1)] by simp
  from TyUnion.prems(2) have "\<turnstile> v : Ty (inst \<eta> \<sigma>1) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>2)" by (auto dest: wf_val_union)
  then show ?case
  proof
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>1)"
    from result_typed_sub[OF TyUnion.IH(1)[OF \<tau>1 this] join_upper(1) wf[unfolded \<tau>] assms(3)] \<tau> show ?thesis
      by simp
  next
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>2)"
    from result_typed_sub[OF TyUnion.IH(2)[OF \<tau>2 this] join_upper(2) wf[unfolded \<tau>] assms(3)] \<tau> show ?thesis
      by simp
  qed
next
  case (TyList \<sigma>')
  then have "int_ok = Ok ()" and \<tau>: "\<tau> = \<sigma>'" by (auto simp: bind_sum_def split: sum.splits)
  with int have r: "wf_result (\<lambda>u. \<exists>n. u = VLit (LitInt n)) r" by blast
  from TyList.prems(2) obtain vs where v: "v = VList vs" and vs: "\<forall>u \<in> set vs. \<turnstile> u : Ty (inst \<eta> \<sigma>')"
    by (auto elim: wf_list)
  have "elems v = Some vs" by (simp add: v)
  note get = getitem_elems[OF this vs]
  with r \<tau> show ?case by (cases r) auto
next
  case (TyDict \<sigma>')
  then have "str_ok = Ok ()" and \<tau>: "\<tau> = \<sigma>'" by (auto simp: bind_sum_def split: sum.splits)
  with str have r: "wf_result (\<lambda>u. \<exists>w. u = VLit (LitString w)) r" by blast
  from TyDict.prems(2) obtain \<delta> where v: "v = VDict \<delta>"
    and \<delta>: "\<forall>w u. (w, u) \<in> set \<delta> \<longrightarrow> \<turnstile> u : Ty (inst \<eta> \<sigma>')"
    by (auto elim: wf_dict)
  have get: "wf_result (\<lambda>u. \<turnstile> u : Ty (inst \<eta> \<sigma>')) (getitem v (VLit (LitString w)))" for w
    using \<delta> by (auto simp: v split: option.splits dest!: map_of_SomeD)
  with r \<tau> show ?case by (cases r) auto
next
  case (TyTuple \<sigma>s)
  from TyTuple.prems(2) obtain vs where v: "v = VTuple vs"
    and vs: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs (map (inst \<eta>) \<sigma>s)"
    by (auto elim: wf_tuple)
  have len: "length vs = length \<sigma>s" using vs by (auto dest: list_all2_lengthD)
  from TyTuple.prems(1) obtain \<iota> where \<iota>: "idx = Ok \<iota>" by (auto simp: bind_sum_def split: sum.splits)
  with idx have r: "result_typed r (inst \<eta> \<iota>)" by blast
  show ?case
  proof (cases "\<iota> = TyPrim int")
    case True
    with TyTuple.prems(1) \<iota> have \<tau>: "\<tau> = joins \<Sigma> \<sigma>s" by (simp add: bind_sum_def)
    have wfs: "\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>" using wf_ty_inst_inv[OF wf_val_ty[OF TyTuple.prems(2)]] by simp
    have "\<turnstile> u : Ty (inst \<eta> (joins \<Sigma> \<sigma>s))" if "u \<in> set vs" for u
    proof -
      from that obtain k where k: "k < length vs" and u: "u = vs ! k" by (auto simp: in_set_conv_nth)
      from list_all2_nthD[OF vs k] k len u have "\<turnstile> u : Ty (inst \<eta> (\<sigma>s ! k))" by simp
      from wf_val_inst_sub[OF this joins_upper[OF wfs] joins_wf[OF wfs] assms(3)] k len show ?thesis by simp
    qed
    moreover have "elems v = Some vs" by (simp add: v)
    ultimately have get: "wf_result (\<lambda>u. \<turnstile> u : Ty (inst \<eta> (joins \<Sigma> \<sigma>s))) (getitem v (VLit (LitInt n)))" for n
      by (blast intro: getitem_elems)
    with r True \<tau> show ?thesis by (cases r) (auto dest: wf_int[OF _ SubtyRefl])
  next
    case False
    have "\<exists>n. \<iota> = TyLiteral (LitInt n)"
      using TyTuple.prems(1) \<iota> False by (auto simp: bind_sum_def split: ty.splits lit.splits prim_ty.splits)
    then obtain n where \<iota>': "\<iota> = TyLiteral (LitInt n)" by blast
    define i where "i = (if n < 0 then of_nat (length \<sigma>s) + n else n)"
    have range: "0 \<le> i" "i < of_nat (length \<sigma>s)" and \<tau>: "\<tau> = \<sigma>s ! nat i"
      using TyTuple.prems(1) \<iota> \<iota>' by (auto simp: bind_sum_def Let_def i_def split: if_splits)
    have k: "nat i < length vs" using range len by (simp add: nat_less_iff)
    from list_all2_nthD[OF vs k] len \<tau> k have elem: "\<turnstile> vs ! nat i : Ty (inst \<eta> \<tau>)" by simp
    have "getitem v (VLit (LitInt n)) = Val (vs ! nat i)" using v range len by (auto simp: Let_def i_def)
    with r \<iota>' elem show ?thesis by (cases r) (auto dest!: wf_lit)
  qed
next
  case (TyPrim p)
  then have "base_type (TyPrim p) = TyPrim str" and "int_ok = Ok ()" and "\<tau> = TyPrim str"
    by (auto simp: bind_sum_def split: if_splits sum.splits)
  with int subscript_str[OF this(1) TyPrim.prems(2)] show ?case by simp
next
  case (TyLiteral l)
  then have "base_type (TyLiteral l) = TyPrim str" and "int_ok = Ok ()" and "\<tau> = TyPrim str"
    by (auto simp: bind_sum_def split: if_splits sum.splits)
  with int subscript_str[OF this(1) TyLiteral.prems(2)] show ?case by simp
qed (simp_all split: if_splits)

lemma subscript_sound:
  assumes callee: "sound_expr \<rho> (node e) (Val v)" and nonclass: "\<not> is_class v"
    and index: "sound_expr \<rho> (node e') r"
  shows "sound_expr \<rho> (ExprSubscript e e') (mlet r (getitem v))"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprSubscript e e') = Ok \<tau>"
  then obtain \<sigma> where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
    and sub: "subscript_type \<Sigma> \<sigma> (check_expr_at \<Sigma> \<Gamma> e' (TyPrim int)) (check_expr_at \<Sigma> \<Gamma> e' (TyPrim str))
      (pos_of e') (synth_expr_at \<Sigma> \<Gamma> e') = Ok \<tau>"
    by (auto simp: bind_sum_def split: sum.splits)
  from sound_expr_synth_at[OF callee env \<sigma>] have v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by simp
  show "result_typed (mlet r (getitem v)) (inst \<eta> \<tau>)"
  proof (rule subscript_result[OF sub v wf_env_wf_inst[OF env]])
    assume "check_expr_at \<Sigma> \<Gamma> e' (TyPrim int) = Ok ()"
    from prim_operand[OF index env this] show "wf_result (\<lambda>u. \<exists>n. u = VLit (LitInt n)) r"
      by (cases r) (auto dest: wf_int[OF _ SubtyRefl])
  next
    assume "check_expr_at \<Sigma> \<Gamma> e' (TyPrim str) = Ok ()"
    from prim_operand[OF index env this] show "wf_result (\<lambda>u. \<exists>w. u = VLit (LitString w)) r"
      by (cases r) (auto dest: wf_str[OF _ SubtyRefl])
  next
    fix \<iota>
    assume "synth_expr_at \<Sigma> \<Gamma> e' = Ok \<iota>"
    from sound_expr_synth_at[OF index env this] show "result_typed r (inst \<eta> \<iota>)" .
  qed
next
  fix \<eta> \<Gamma> \<tau>
  assume "check_expr' \<Sigma> \<Gamma> (ExprSubscript e e') \<tau> = Some (Ok ())"
  then show "result_typed (mlet r (getitem v)) (inst \<eta> \<tau>)" by (simp add: var_scheme_None)
next
  fix \<eta> \<Gamma>
  assume "call_stmt \<Sigma> \<Gamma> (ExprSubscript e e')"
  then show "result_typed (mlet r (getitem v)) (inst \<eta> (TyPrim object))" by simp
next
  show "sound_name \<rho> (ExprSubscript e e') (mlet r (getitem v))"
    unfolding sound_name_def
  proof (intro allI impI)
    fix \<eta> \<Gamma> \<theta>
    assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "expr_entry \<Gamma> (ExprSubscript e e') = Some \<theta>"
    then obtain C where "class_of_name \<Gamma> (node e) = Some C" by auto
    from sound_expr_class[OF callee env class_of_name_entry[OF this]] nonclass
    show "wf_result (\<lambda>v'. \<turnstile> v' : inst_entry \<eta> \<theta>) (mlet r (getitem v))" by simp
  qed
qed

lemma class_type_args_sound:
  assumes "sound_expr \<rho> (node e) (Val (VClass C))" and "type_args_of e' = Some \<psi>s"
  shows "sound_expr \<rho> (ExprSubscript e e') (Val (VClass C))"
proof (rule sound_exprI)
  show "sound_name \<rho> (ExprSubscript e e') (Val (VClass C))"
    using assms(1) by (auto simp: sound_name_def dest!: class_of_name_entry dest: sound_expr_name)
qed (auto simp: bind_sum_def var_scheme_None dest!: sound_expr_synth_at[OF assms(1)] wf_class_ty
    split: sum.splits)

lemma subscript_fail_sound:
  assumes "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprSubscript e e') (Aborts \<kappa>)"
proof (rule sound_exprI)
  show "sound_name \<rho> (ExprSubscript e e') (Aborts \<kappa>)"
    using assms by (auto simp: sound_name_def dest!: class_of_name_entry dest: sound_expr_name)
qed (auto simp: bind_sum_def var_scheme_None dest: sound_expr_synth_at[OF assms] split: sum.splits)

(* Field of class C at type arguments \<tau>s, a subtype of the attribute type of a type above the class *)
lemma attribute_field:
  "\<lbrakk> \<Sigma> \<turnstile> TyClass C \<tau>s <: inst \<eta> \<sigma> ; attribute_type \<Sigma> \<sigma> x = Ok \<tau> ; wf_ty \<Sigma> (TyClass C \<tau>s) ; wf_ty \<Sigma> \<sigma>
   ; wf_inst \<Sigma> \<eta> \<rbrakk>
  \<Longrightarrow> \<exists>\<sigma>'. map_of (instantiate (fields \<Sigma> C) \<tau>s) x = Some \<sigma>' \<and> \<Sigma> \<turnstile> \<sigma>' <: inst \<eta> \<tau>"
proof (induction \<sigma> arbitrary: \<tau>)
  case (TyUnion \<sigma> \<sigma>'')
  from TyUnion(4) obtain \<tau>' \<tau>'' where \<tau>': "attribute_type \<Sigma> \<sigma> x = Ok \<tau>'"
    and \<tau>'': "attribute_type \<Sigma> \<sigma>'' x = Ok \<tau>''" and \<tau>: "\<tau> = \<tau>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>''"
    by (auto simp: bind_sum_def split: sum.splits)
  have wf: "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> \<sigma>''" using TyUnion(6) by simp_all
  have wf': "wf_ty \<Sigma> \<tau>'" "wf_ty \<Sigma> \<tau>''"
    using attribute_type_wf[OF wf_class_table wf(1) \<tau>'] attribute_type_wf[OF wf_class_table wf(2) \<tau>'']
    by simp_all
  have wf\<tau>: "wf_ty \<Sigma> (\<tau>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>'')" using wf' by (rule join_wf)
  have sub: "\<Sigma> \<turnstile> inst \<eta> \<tau>' <: inst \<eta> \<tau>"
    unfolding \<tau> using inst_subty[OF wf_class_table join_upper(1)] wf'(1) wf\<tau> by blast
  have sub'': "\<Sigma> \<turnstile> inst \<eta> \<tau>'' <: inst \<eta> \<tau>"
    unfolding \<tau> using inst_subty[OF wf_class_table join_upper(2)] wf'(2) wf\<tau> by blast
  have trans: "\<Sigma> \<turnstile> \<sigma>' <: inst \<eta> \<tau>"
    if "map_of (instantiate (fields \<Sigma> C) \<tau>s) x = Some \<sigma>'" and "\<Sigma> \<turnstile> \<sigma>' <: inst \<eta> \<tau>\<^sub>0"
    and "\<Sigma> \<turnstile> inst \<eta> \<tau>\<^sub>0 <: inst \<eta> \<tau>" and "wf_ty \<Sigma> \<tau>\<^sub>0" for \<sigma>' \<tau>\<^sub>0
  proof -
    have "wf_ty \<Sigma> \<sigma>'" using fields_wf[OF wf_class_table TyUnion(5)] that(1) by (auto dest: map_of_SomeD)
    from subty_trans[OF wf_class_table this inst_wf[OF TyUnion(7) that(4)] that(2, 3)] show ?thesis .
  qed
  from nonunion_subty_union(1)[OF TyUnion(3)[simplified] refl, simplified] show ?case
  proof
    assume "\<Sigma> \<turnstile> TyClass C \<tau>s <: inst \<eta> \<sigma>"
    from TyUnion(1)[OF this \<tau>' TyUnion(5) wf(1) TyUnion(7)] obtain \<sigma>'
      where "map_of (instantiate (fields \<Sigma> C) \<tau>s) x = Some \<sigma>'" and "\<Sigma> \<turnstile> \<sigma>' <: inst \<eta> \<tau>'" by blast
    with trans[OF this sub wf'(1)] show ?thesis by blast
  next
    assume "\<Sigma> \<turnstile> TyClass C \<tau>s <: inst \<eta> \<sigma>''"
    from TyUnion(2)[OF this \<tau>'' TyUnion(5) wf(2) TyUnion(7)] obtain \<sigma>'
      where "map_of (instantiate (fields \<Sigma> C) \<tau>s) x = Some \<sigma>'" and "\<Sigma> \<turnstile> \<sigma>' <: inst \<eta> \<tau>''" by blast
    with trans[OF this sub'' wf'(2)] show ?thesis by blast
  qed
next
  case (TyClass D \<sigma>s)
  then have look: "map_of (instantiate (fields \<Sigma> D) \<sigma>s) x = Some \<tau>"
    by (simp add: or_else_def split: option.splits)
  have "finite (\<Union> (fv ` set \<sigma>s) \<union> fv \<tau>)" by (simp add: finite_fv)
  then obtain \<alpha>s where \<alpha>s: "\<And>\<tau>'. fv \<tau>' \<subseteq> \<Union> (fv ` set \<sigma>s) \<union> fv \<tau> \<Longrightarrow> inst \<eta> \<tau>' = subst (map \<eta> \<alpha>s) \<alpha>s \<tau>'"
    using inst_subst_cover by blast
  have \<sigma>s: "map (inst \<eta>) \<sigma>s = map (subst (map \<eta> \<alpha>s) \<alpha>s) \<sigma>s" by (intro map_cong[OF refl] \<alpha>s) auto
  have \<tau>: "inst \<eta> \<tau> = subst (map \<eta> \<alpha>s) \<alpha>s \<tau>" by (rule \<alpha>s) simp
  from look have "map_of (instantiate (fields \<Sigma> D) (map (inst \<eta>) \<sigma>s)) x = Some (inst \<eta> \<tau>)"
    using TyClass(5) instantiate_fields_subst[OF wf_class_table, of D \<sigma>s "map \<eta> \<alpha>s" \<alpha>s]
    unfolding \<sigma>s \<tau> by (simp add: map_of_map_snd)
  moreover from TyClass(2) have "\<Sigma> \<turnstile> TyClass C \<tau>s <: TyClass D (map (inst \<eta>) \<sigma>s)" by simp
  moreover have "C |\<in>| fmdom \<Sigma>" using TyClass(4) by simp
  ultimately show ?case using subty_class_fields(1)[OF wf_class_table _ refl refl] by blast
qed simp_all

(* Attribute typed through a checked module, at a member type, member scheme or type variable, or through the
   type synthesised by the object *)
lemma attr_typed:
  assumes "has_type \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>"
  obtains (module_ty) q q' \<Gamma>' \<sigma> where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
      and "fmlookup \<Gamma>' x = Some (Ty \<sigma>)" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    | (module_scheme) q q' \<Gamma>' \<alpha>s \<sigma> \<tau>s where "dotted_name (node e) = Some q"
      and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')" and "fmlookup \<Gamma>' x = Some (Scheme (TyScheme \<alpha>s \<sigma>))"
      and "Subtyping.type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s" and "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: \<tau>"
    | (module_tyvar) q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
      and "fmlookup \<Gamma>' x = Some TypeVar"
    | (object) \<sigma> \<sigma>' where "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'" and "\<Sigma> \<turnstile> \<sigma>' <: \<tau>"
proof -
  have synth: thesis if "synth_expr \<Sigma> \<Gamma> (ExprAttribute e x) = Ok \<sigma>'" and "\<Sigma> \<turnstile> \<sigma>' <: \<tau>" for \<sigma>'
  proof (cases "module_attribute \<Gamma> (node e) x")
    case None
    with that show ?thesis by (auto simp: bind_sum_def split: sum.splits intro: object)
  next
    case (Some m)
    with that(1) obtain q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
      and "fmlookup \<Gamma>' x = Some (Ty \<sigma>') \<or> fmlookup \<Gamma>' x = Some TypeVar"
      by (auto simp: module_attribute_def attr_module_def bind_eq_Some_conv
          split: option.splits cxt_entry.splits)
    with that(2) show ?thesis by (blast intro: module_ty module_tyvar)
  qed
  have scheme: thesis if "var_scheme \<Sigma> \<Gamma> (ExprAttribute e x) \<tau> = Some (Ok ())"
  proof -
    from that obtain q q' \<Gamma>' \<alpha>s \<sigma> \<tau>s where "dotted_name (node e) = Some q"
      and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')" and "fmlookup \<Gamma>' x = Some (Scheme (TyScheme \<alpha>s \<sigma>))"
      and "Subtyping.type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s" and "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: \<tau>"
      by (auto simp: var_scheme_def scheme_of_name_def entry_of_def resolve_name_def bind_sum_def ensure_def
          Let_def bind_eq_Some_conv split: option.splits cxt_entry.splits ty_scheme.splits if_splits sum.splits)
    then show ?thesis by (rule module_scheme)
  qed
  from assms show thesis unfolding has_type_def by (auto dest!: check_expr_cases intro: synth scheme SubtyRefl)
qed

(* Value of a dotted name bound to a checked module, as a loaded module with its environment typed by the
   context of the module *)
lemma sound_expr_module_env:
  assumes "sound_expr \<rho> e (Val v)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "dotted_name e = Some q"
    and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
  shows "\<exists>\<rho>' \<eta>'. v = VModLoaded q' \<rho>' \<and> \<eta>' \<turnstile> \<rho>' : \<Gamma>'"
  using sound_expr_module[OF assms, unfolded wf_result.simps(1)] by (rule wf_mod_checked)

(* Attribute of an expression with a value which is not a loaded module, typed through the type synthesised by
   the expression *)
lemma attr_typed_object:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<not> is_loaded_module v" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and "has_type \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>"
  obtains \<sigma> \<sigma>' where "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'" and "\<Sigma> \<turnstile> \<sigma>' <: \<tau>"
  using assms(4)
proof (cases rule: attr_typed)
  case (module_ty q q' \<Gamma>' \<sigma>)
  from sound_expr_module_env[OF assms(1, 3) module_ty(1, 2)] assms(2) show thesis by auto
next
  case (module_scheme q q' \<Gamma>' \<alpha>s \<sigma> \<tau>s)
  from sound_expr_module_env[OF assms(1, 3) module_scheme(1, 2)] assms(2) show thesis by auto
next
  case (module_tyvar q q' \<Gamma>')
  from sound_expr_module_env[OF assms(1, 3) module_tyvar(1, 2)] assms(2) show thesis by auto
next
  case (object \<sigma> \<sigma>')
  then show thesis by (rule that)
qed

(* Name clause for an attribute of an expression with a value which is not a loaded module *)
lemma sound_name_attr:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<not> is_loaded_module v"
  shows "sound_name \<rho> (ExprAttribute e x) r"
  unfolding sound_name_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<theta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "expr_entry \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
    and "fmlookup \<Gamma>' x = Some \<theta>"
    unfolding expr_entry_simps by (rule entry_of_attribute)
  from sound_expr_module_env[OF assms(1) env this(1, 2)] assms(2)
  show "wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r" by auto
qed

(* Field x of an object, typed by the attribute type of x at a type of the object *)
lemma object_attribute:
  assumes "\<turnstile> VObject C xvs : Ty (inst \<eta> \<sigma>)" and "attribute_type \<Sigma> \<sigma> x = Ok \<tau>" and "wf_inst \<Sigma> \<eta>"
  obtains v where "map_of xvs x = Some v" and "\<turnstile> v : Ty (inst \<eta> \<tau>)"
proof -
  from assms(1) obtain \<tau>s where C: "wf_ty \<Sigma> (TyClass C \<tau>s)"
    and names: "map fst xvs = field_names \<Sigma> C"
    and fields: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s)"
    and sub: "\<Sigma> \<turnstile> TyClass C \<tau>s <: inst \<eta> \<sigma>"
    by (rule wf_object)
  have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" by (rule wf_ty_inst_inv[OF wf_val_ty[OF assms(1)]])
  from attribute_field[OF sub assms(2) C wf\<sigma> assms(3)] obtain \<sigma>'
    where field: "map_of (instantiate (fields \<Sigma> C) \<tau>s) x = Some \<sigma>'"
    and sub': "\<Sigma> \<turnstile> \<sigma>' <: inst \<eta> \<tau>"
    by blast
  have "wf_ty \<Sigma> (inst \<eta> \<tau>)"
    using attribute_type_wf[OF wf_class_table wf\<sigma> assms(2)] by (auto intro: inst_wf[OF assms(3)])
  moreover obtain v where "map_of xvs x = Some v" and "\<turnstile> v : Ty \<sigma>'"
    by (rule object_field[OF names fields field])
  ultimately show thesis using that wf_val_sub[OF _ sub'] by blast
qed

lemma attr_object_sound:
  assumes "sound_expr \<rho> (node e) (Val (VObject C xvs))" and "map_of xvs x = Some v"
  shows "sound_expr \<rho> (ExprAttribute e x) (Val v)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>"
  obtain \<sigma> \<sigma>' where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and attr: "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'"
    and sub: "\<Sigma> \<turnstile> \<sigma>' <: \<tau>"
    by (rule attr_typed_object[OF assms(1) _ env typed]) simp
  from sound_expr_synth_at[OF assms(1) env synth] have "\<turnstile> VObject C xvs : Ty (inst \<eta> \<sigma>)" by simp
  from object_attribute[OF this attr wf_env_wf_inst[OF env]] assms(2) have "\<turnstile> v : Ty (inst \<eta> \<sigma>')" by auto
  with sub has_type_wf[OF wf_env_wf_cxt[OF env] typed] wf_env_wf_inst[OF env]
  show "result_typed (Val v) (inst \<eta> \<tau>)" by (auto intro: wf_val_inst_sub)
next
  show "sound_name \<rho> (ExprAttribute e x) (Val v)" using assms(1) by (rule sound_name_attr) simp
qed

lemma attr_object_missing_sound:
  assumes "sound_expr \<rho> (node e) (Val (VObject C xvs))" and "map_of xvs x = None"
  shows "sound_expr \<rho> (ExprAttribute e x) (Aborts AttributeError)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>"
  obtain \<sigma> \<sigma>' where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and attr: "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'"
    by (rule attr_typed_object[OF assms(1) _ env typed]) simp
  from sound_expr_synth_at[OF assms(1) env synth] have "\<turnstile> VObject C xvs : Ty (inst \<eta> \<sigma>)" by simp
  from object_attribute[OF this attr wf_env_wf_inst[OF env]] assms(2)
  show "result_typed (Aborts AttributeError) (inst \<eta> \<tau>)" by auto
next
  show "sound_name \<rho> (ExprAttribute e x) (Aborts AttributeError)"
    using assms(1) by (rule sound_name_attr) simp
qed

(* Member of a loaded module named by an entry of the context of the module, typed by the entry *)
lemma module_attr_entry:
  assumes "sound_expr \<rho> (node e) (Val (VModLoaded q' \<rho>'))" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "dotted_name (node e) = Some q"
    and "lookup \<Gamma> q = Some (ModChecked q'' \<Gamma>')" and "fmlookup \<Gamma>' x = Some \<theta>"
  obtains v where "fmlookup \<rho>' x = Some v" and "\<turnstile> v : \<theta>" and "fv_entry \<theta> = {}"
proof -
  from sound_expr_module_env[OF assms(1-4)] obtain \<eta>' where env': "\<eta>' \<turnstile> \<rho>' : \<Gamma>'" by auto
  have closed: "tyvars \<Gamma>' = {}" using lookup_wf[OF wf_env_wf_cxt[OF assms(2)] assms(4)] by simp
  with assms(5) have "\<theta> \<noteq> TypeVar" by (auto dest: module_member_TypeVar)
  from module_member[OF env' closed assms(5) this] that show thesis by blast
qed

(* Attribute of a loaded module typed at \<tau>, as a member of the module typed at \<tau> *)
lemma attr_module_typed:
  assumes "sound_expr \<rho> (node e) (Val (VModLoaded q' \<rho>'))" and env: "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and "has_type \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>"
  obtains v where "fmlookup \<rho>' x = Some v" and "\<turnstile> v : Ty (inst \<eta> \<tau>)"
  using assms(3)
proof (cases rule: attr_typed)
  case (module_ty q q'' \<Gamma>' \<sigma>)
  from module_attr_entry[OF assms(1, 2) module_ty(1-3)] obtain v where lookup: "fmlookup \<rho>' x = Some v"
    and "\<turnstile> v : Ty \<sigma>" and "fv \<sigma> = {}"
    by auto
  then have "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by (simp add: inst_closed_ty)
  from that[OF lookup wf_val_inst_sub[OF this module_ty(4) has_type_wf[OF wf_env_wf_cxt[OF env] assms(3)]
      wf_env_wf_inst[OF env]]]
  show thesis .
next
  case (module_scheme q q'' \<Gamma>' \<alpha>s \<sigma> \<tau>s)
  from module_attr_entry[OF assms(1, 2) module_scheme(1-3)] obtain v where lookup: "fmlookup \<rho>' x = Some v"
    and "\<turnstile> v : Scheme (TyScheme \<alpha>s \<sigma>)" and "fv_entry (Scheme (TyScheme \<alpha>s \<sigma>)) = {}"
    by blast
  then have "\<turnstile> v : inst_entry \<eta> (Scheme (TyScheme \<alpha>s \<sigma>))" by (simp only: inst_entry_closed)
  from scheme_instance_typed[OF this wf_env_wf_inst[OF env] has_type_wf[OF wf_env_wf_cxt[OF env] assms(3)]
      module_scheme(4, 5)]
  show thesis by (rule that[OF lookup])
next
  case (module_tyvar q q'' \<Gamma>')
  from lookup_wf[OF wf_env_wf_cxt[OF env] module_tyvar(2)] module_tyvar(3) show thesis
    by (auto dest: module_member_TypeVar)
next
  case (object \<sigma> \<sigma>')
  from sound_expr_synth_at[OF assms(1, 2) object(1)] show thesis by (auto dest: wf_mod_loaded)
qed

(* Name clause for an attribute of a loaded module, whose result is the member of the module when it has one *)
lemma sound_name_module:
  assumes "sound_expr \<rho> (node e) (Val (VModLoaded q' \<rho>'))" and "\<And>v. fmlookup \<rho>' x = Some v \<Longrightarrow> r = Val v"
  shows "sound_name \<rho> (ExprAttribute e x) r"
  unfolding sound_name_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<theta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "expr_entry \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q'' \<Gamma>' where q: "dotted_name (node e) = Some q"
    and mod: "lookup \<Gamma> q = Some (ModChecked q'' \<Gamma>')" and x: "fmlookup \<Gamma>' x = Some \<theta>"
    unfolding expr_entry_simps by (rule entry_of_attribute)
  obtain v where "fmlookup \<rho>' x = Some v" and "\<turnstile> v : \<theta>" and "fv_entry \<theta> = {}"
    by (rule module_attr_entry[OF assms(1) env q mod x])
  with assms(2)[OF this(1)] show "wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r" by (simp add: inst_entry_closed)
qed

lemma attr_module_sound:
  assumes "sound_expr \<rho> (node e) (Val (VModLoaded q' \<rho>'))" and "fmlookup \<rho>' x = Some v"
  shows "sound_expr \<rho> (ExprAttribute e x) (Val v)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "has_type \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>"
  from attr_module_typed[OF assms(1) this] assms(2) show "result_typed (Val v) (inst \<eta> \<tau>)" by simp
next
  show "sound_name \<rho> (ExprAttribute e x) (Val v)" by (rule sound_name_module[OF assms(1)]) (simp add: assms(2))
qed

lemma attr_module_missing_sound:
  assumes "sound_expr \<rho> (node e) (Val (VModLoaded q' \<rho>'))" and "fmlookup \<rho>' x = None"
  shows "sound_expr \<rho> (ExprAttribute e x) (Aborts AttributeError)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "has_type \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>"
  from attr_module_typed[OF assms(1) this] assms(2) show "result_typed (Aborts AttributeError) (inst \<eta> \<tau>)"
    by simp
next
  show "sound_name \<rho> (ExprAttribute e x) (Aborts AttributeError)"
    by (rule sound_name_module[OF assms(1)]) (simp add: assms(2))
qed

lemma attr_nonobject_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<not> is_object v" and "\<not> is_loaded_module v"
  shows "sound_expr \<rho> (ExprAttribute e x) (Aborts Excluded)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>"
  obtain \<sigma> \<sigma>' where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and attr: "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'"
    by (rule attr_typed_object[OF assms(1, 3) env typed])
  from sound_expr_synth_at[OF assms(1) env synth] have "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by simp
  moreover from attr have "object_type (inst \<eta> \<sigma>)"
    by (blast intro: object_type_inst attribute_type_object_type)
  ultimately show "result_typed (Aborts Excluded) (inst \<eta> \<tau>)" using assms(2) wf_object_type by blast
next
  show "sound_name \<rho> (ExprAttribute e x) (Aborts Excluded)" using assms(1, 3) by (rule sound_name_attr)
qed

lemma attr_fail_sound:
  assumes "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprAttribute e x) (Aborts \<kappa>)"
  unfolding sound_expr_def sound_name_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<Gamma> (ExprAttribute e x) \<tau>"
  from typed show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)"
    by (cases rule: attr_typed) (auto dest: sound_expr_module[OF assms env] sound_expr_synth_at[OF assms env])
next
  fix \<eta> \<Gamma> \<theta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "expr_entry \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
    and "fmlookup \<Gamma>' x = Some \<theta>"
    unfolding expr_entry_simps by (rule entry_of_attribute)
  from sound_expr_module[OF assms env this(1, 2)]
  show "wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) (Aborts \<kappa>)" by simp
qed

end

end
