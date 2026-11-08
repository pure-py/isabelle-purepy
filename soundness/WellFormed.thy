(* Well-formedness and type variables of the types produced by the type checker *)
theory WellFormed
  imports "isabelle-purepy.Programs"
begin

subsection \<open>Classes\<close>

lemma instantiated_ancestors_upto_names:
  "map fst (instantiated_ancestors_upto n \<Sigma> C \<tau>s) = map fst (instantiated_ancestors_upto n \<Sigma> C \<tau>s')"
  by (induction n arbitrary: C \<tau>s \<tau>s') (auto split: option.splits)

(* Ancestor of class C at well-formed type arguments \<tau>s: well-formed, at type arguments over those of \<tau>s *)
lemma instantiated_ancestors_upto_wf:
  assumes "wf_class_table \<Sigma>"
  shows "\<lbrakk> C |\<in>| fmdom \<Sigma> ; inherits_within n \<Sigma> C ; wf_ty \<Sigma> (TyClass C \<tau>s)
          ; (D, \<sigma>s) \<in> set (instantiated_ancestors_upto n \<Sigma> C \<tau>s) \<rbrakk>
    \<Longrightarrow> wf_ty \<Sigma> (TyClass D \<sigma>s) \<and> (\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> \<Union> (fv ` set \<tau>s))"
proof (induction n arbitrary: C \<tau>s)
  case (Suc n)
  let ?\<alpha>s = "type_params \<Sigma> C"
  show ?case
  proof (cases "base \<Sigma> C")
    case None
    with Suc.prems(3, 4) show ?thesis by auto
  next
    case (Some E\<rho>s)
    then obtain E \<rho>s where base: "base \<Sigma> C = Some (E, \<rho>s)" by (cases E\<rho>s) simp
    from Suc.prems(4) base consider "D = C" "\<sigma>s = \<tau>s"
      | "(D, \<sigma>s) \<in> set (instantiated_ancestors_upto n \<Sigma> E (map (subst \<tau>s ?\<alpha>s) \<rho>s))"
      by auto
    then show ?thesis
    proof cases
      case 1
      with Suc.prems(3) show ?thesis by auto
    next
      case 2
      from wf_class_table_baseD[OF assms Suc.prems(1) base] have E: "E |\<in>| fmdom \<Sigma>"
        and fv: "\<forall>\<rho> \<in> set \<rho>s. fv \<rho> \<subseteq> set ?\<alpha>s"
        by auto
      from Suc.prems(2) base have "inherits_within n \<Sigma> E" by simp
      from Suc.IH[OF E this wf_class_table_base[OF assms Suc.prems(3) base] 2]
      have wf: "wf_ty \<Sigma> (TyClass D \<sigma>s)"
        and sub: "\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> \<Union> (fv ` set (map (subst \<tau>s ?\<alpha>s) \<rho>s))"
        by auto
      have "fv (subst \<tau>s ?\<alpha>s \<rho>) \<subseteq> \<Union> (fv ` set \<tau>s)" if "\<rho> \<in> set \<rho>s" for \<rho>
        using fv_subst[OF bspec[OF fv that]] Suc.prems(3) by simp
      then have "\<Union> (fv ` set (map (subst \<tau>s ?\<alpha>s) \<rho>s)) \<subseteq> \<Union> (fv ` set \<tau>s)" by auto
      with wf sub show ?thesis by (meson subset_trans)
    qed
  qed
qed simp

lemma instantiated_ancestors_wf:
  assumes "wf_class_table \<Sigma>" and "wf_ty \<Sigma> (TyClass C \<tau>s)" and "(D, \<sigma>s) \<in> set (instantiated_ancestors \<Sigma> C \<tau>s)"
  shows "wf_ty \<Sigma> (TyClass D \<sigma>s) \<and> (\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> \<Union> (fv ` set \<tau>s))"
proof -
  have C: "C |\<in>| fmdom \<Sigma>" using assms(2) by simp
  from assms(3) show ?thesis
    unfolding instantiated_ancestors_def
    by (rule instantiated_ancestors_upto_wf[OF assms(1) C wf_class_table_inherits[OF assms(1) C] assms(2)])
qed

lemma ancestors_instantiated: "set (ancestors \<Sigma> C) = fst ` set (instantiated_ancestors \<Sigma> C \<tau>s)"
  unfolding ancestors_def instantiated_ancestors_def
  by (subst instantiated_ancestors_upto_names[of _ _ _ _ \<tau>s]) simp

(* Type arguments of ancestor D of class C at well-formed type arguments \<tau>s *)
lemma instantiated_ancestor_wf:
  assumes "wf_class_table \<Sigma>" and "wf_ty \<Sigma> (TyClass C \<tau>s)" and "D \<in> set (ancestors \<Sigma> C)"
  shows "wf_ty \<Sigma> (TyClass D (instantiated_ancestor \<Sigma> C \<tau>s D))
    \<and> (\<forall>\<sigma> \<in> set (instantiated_ancestor \<Sigma> C \<tau>s D). fv \<sigma> \<subseteq> \<Union> (fv ` set \<tau>s))"
proof -
  have "map_of (instantiated_ancestors \<Sigma> C \<tau>s) D \<noteq> None"
    using assms(3) by (simp add: map_of_eq_None_iff ancestors_instantiated[of \<Sigma> C \<tau>s])
  then obtain \<sigma>s where "map_of (instantiated_ancestors \<Sigma> C \<tau>s) D = Some \<sigma>s" by blast
  with instantiated_ancestors_wf[OF assms(1, 2) map_of_SomeD[OF this]] show ?thesis
    by (simp add: instantiated_ancestor_def)
qed

subsection \<open>Joins and meets\<close>

lemma wf_join: "\<lbrakk> wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)"
  by (simp add: join_def)

lemma wf_joins: "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_ty \<Sigma> (joins \<Sigma> \<tau>s)"
  by (induction \<tau>s) (simp_all add: joins_def wf_join)

lemma wf_base_type_lit [simp]: "wf_ty \<Sigma> (base_type_lit l)"
  by (cases l) simp_all

lemma wf_base_type: "wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_ty \<Sigma> (base_type \<tau>)"
  by (cases \<tau>) simp_all

lemma fv_join_elem: "x \<in> fv (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>) \<Longrightarrow> x \<in> fv \<sigma> \<or> x \<in> fv \<tau>"
  by (auto simp: join_def split: if_splits)

lemma fv_meet_elem:
  "\<forall>x. x \<in> fv (meet \<Sigma> \<sigma> \<tau>) \<longrightarrow> x \<in> fv \<sigma> \<or> x \<in> fv \<tau>"
  "\<forall>x. x \<in> fv (meet_incomparable \<Sigma> \<sigma>' \<tau>') \<longrightarrow> x \<in> fv \<sigma>' \<or> x \<in> fv \<tau>'"
proof (induction \<Sigma> \<sigma> \<tau> and \<Sigma> \<sigma>' \<tau>' rule: meet_meet_incomparable.induct)
  case (4 \<Sigma> \<sigma>s \<sigma> \<tau>s \<tau>)
  show ?case
  proof (intro allI impI)
    fix x
    assume x: "x \<in> fv (meet_incomparable \<Sigma> (TyCallable \<sigma>s \<sigma>) (TyCallable \<tau>s \<tau>))"
    then have len: "length \<sigma>s = length \<tau>s" by (auto split: if_splits)
    from x consider a b where "(a, b) \<in> set (zip \<sigma>s \<tau>s)" and "x \<in> fv (a \<squnion>\<^bsub>\<Sigma>\<^esub> b)" | "x \<in> fv (meet \<Sigma> \<sigma> \<tau>)"
      by (auto split: if_splits)
    then show "x \<in> fv (TyCallable \<sigma>s \<sigma>) \<or> x \<in> fv (TyCallable \<tau>s \<tau>)"
    proof cases
      case 1
      with fv_join_elem[OF 1(2)] set_zip_leftD[OF 1(1)] set_zip_rightD[OF 1(1)] show ?thesis by auto
    next
      case 2
      with "4.IH"[OF len] show ?thesis by auto
    qed
  qed
next
  case (5 \<Sigma> \<sigma>s \<tau>s)
  show ?case
  proof (intro allI impI)
    fix x
    assume "x \<in> fv (meet_incomparable \<Sigma> (TyTuple \<sigma>s) (TyTuple \<tau>s))"
    then have len: "length \<sigma>s = length \<tau>s" by (auto split: if_splits)
    from \<open>x \<in> fv (meet_incomparable \<Sigma> (TyTuple \<sigma>s) (TyTuple \<tau>s))\<close> obtain a b
      where ab: "(a, b) \<in> set (zip \<sigma>s \<tau>s)" and "x \<in> fv (meet \<Sigma> a b)"
      by (auto split: if_splits)
    with "5.IH"[OF len ab refl] have "x \<in> fv a \<or> x \<in> fv b" by auto
    with set_zip_leftD[OF ab] set_zip_rightD[OF ab] show "x \<in> fv (TyTuple \<sigma>s) \<or> x \<in> fv (TyTuple \<tau>s)" by auto
  qed
qed (auto split: if_splits dest!: fv_join_elem)

lemma fv_meet: "fv (meet \<Sigma> \<sigma> \<tau>) \<subseteq> fv \<sigma> \<union> fv \<tau>"
  using fv_meet_elem(1) by blast

lemma wf_meet:
  "wf_ty \<Sigma> \<sigma> \<Longrightarrow> wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_ty \<Sigma> (meet \<Sigma> \<sigma> \<tau>)"
  "wf_ty \<Sigma> \<sigma>' \<Longrightarrow> wf_ty \<Sigma> \<tau>' \<Longrightarrow> wf_ty \<Sigma> (meet_incomparable \<Sigma> \<sigma>' \<tau>')"
proof (induction \<Sigma> \<sigma> \<tau> and \<Sigma> \<sigma>' \<tau>' rule: meet_meet_incomparable.induct)
  case (4 \<Sigma> \<sigma>s \<sigma> \<tau>s \<tau>)
  show ?case
  proof (cases "length \<sigma>s = length \<tau>s")
    case True
    have "wf_ty \<Sigma> (a \<squnion>\<^bsub>\<Sigma>\<^esub> b)" if "(a, b) \<in> set (zip \<sigma>s \<tau>s)" for a b
      using "4.prems" set_zip_leftD[OF that] set_zip_rightD[OF that] by (auto intro: wf_join)
    with "4.IH"[OF True] "4.prems" True show ?thesis by auto
  qed simp
next
  case (5 \<Sigma> \<sigma>s \<tau>s)
  show ?case
  proof (cases "length \<sigma>s = length \<tau>s")
    case True
    have "wf_ty \<Sigma> (meet \<Sigma> a b)" if "(a, b) \<in> set (zip \<sigma>s \<tau>s)" for a b
      using "5.IH"[OF True that refl] "5.prems" set_zip_leftD[OF that] set_zip_rightD[OF that] by auto
    with True show ?thesis by auto
  qed simp
qed (auto split: if_splits intro: wf_join)

subsection \<open>Elements, subscripts and attributes\<close>

lemma wf_elem_type: "\<lbrakk> wf_ty \<Sigma> \<sigma> ; elem_type \<Sigma> \<sigma> = Some \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
proof (induction \<sigma> arbitrary: \<tau>)
  case (TyPrim p)
  then show ?case by (cases p) auto
next
  case (TyLiteral l)
  then show ?case by (cases l) auto
next
  case (TyClass C \<tau>s)
  then show ?case by (cases \<tau>s) (auto split: if_splits)
next
  case (TyTuple \<tau>s)
  then show ?case by (auto intro!: wf_joins wf_base_type)
next
  case (TyUnion \<sigma> \<sigma>')
  show ?case
  proof (cases "elem_type \<Sigma> \<sigma>")
    case (Some \<tau>\<^sub>1)
    show ?thesis
    proof (cases "elem_type \<Sigma> \<sigma>'")
      case (Some \<tau>\<^sub>2)
      with \<open>elem_type \<Sigma> \<sigma> = Some \<tau>\<^sub>1\<close> TyUnion.prems have \<tau>: "\<tau> = \<tau>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>2" and "wf_ty \<Sigma> \<sigma>" and "wf_ty \<Sigma> \<sigma>'"
        by simp_all
      with TyUnion.IH(1)[OF _ \<open>elem_type \<Sigma> \<sigma> = Some \<tau>\<^sub>1\<close>] TyUnion.IH(2)[OF _ Some] show ?thesis
        by (simp add: wf_join)
    qed (use TyUnion.prems(2) \<open>elem_type \<Sigma> \<sigma> = Some \<tau>\<^sub>1\<close> in simp)
  qed (use TyUnion.prems(2) in simp)
next
  case (TyList \<sigma>)
  from TyList.prems show ?case by auto
next
  case (TyDict \<sigma>)
  from TyDict.prems show ?case by auto
next
  case (TyCallable \<sigma>s \<sigma>)
  from TyCallable.prems show ?case by auto
next
  case (TyVar \<alpha>)
  from TyVar.prems show ?case by auto
qed

(* Type of a subscript of a value of well-formed type \<sigma>: well-formed and over the type variables of \<sigma> *)
lemma subscript_type_wf:
  "\<lbrakk> wf_ty \<Sigma> \<sigma> ; subscript_type \<Sigma> \<sigma> int_ok str_ok p idx = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma>"
proof (induction \<Sigma> \<sigma> int_ok str_ok p idx arbitrary: \<tau> rule: subscript_type.induct)
  case (1 \<Sigma> \<sigma> \<sigma>' int_ok str_ok p idx)
  have wf: "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> \<sigma>'" using "1.prems"(1) by simp_all
  from "1.prems"(2) obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where "subscript_type \<Sigma> \<sigma> int_ok str_ok p idx = Ok \<tau>\<^sub>1"
    and "subscript_type \<Sigma> \<sigma>' int_ok str_ok p idx = Ok \<tau>\<^sub>2" and \<tau>: "\<tau> = \<tau>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>2"
    by (auto simp: bind_sum_Ok)
  from "1.IH"(1)[OF wf(1) this(1)] "1.IH"(2)[OF this(1) wf(2) this(2)] show ?case
    unfolding \<tau> by (auto intro: wf_join dest!: fv_join_elem)
next
  case (4 \<Sigma> \<tau>s int_ok str_ok p idx)
  from "4.prems"(2) obtain \<iota> where "idx = Ok \<iota>"
    and \<tau>: "(case \<iota> of
              TyLiteral (LitInt n) \<Rightarrow>
                let i = (if n < 0 then of_nat (length \<tau>s) + n else n)
                in if 0 \<le> i \<and> i < of_nat (length \<tau>s) then Ok (\<tau>s ! nat i)
                   else Fail (Located p (Violates (if n < 0 then RuleSubscriptTupleNeg else RuleSubscriptTuple)
                                            (TupleIndexOutOfRange n (length \<tau>s))))
            | TyPrim int \<Rightarrow> Ok (joins \<Sigma> \<tau>s)
            | _ \<Rightarrow> Fail (Located p (Violates RuleSubscriptTupleInt (TypeMismatch (TyPrim int) \<iota>)))) = Ok \<tau>"
    by (auto simp: bind_sum_Ok)
  show ?case
  proof (cases \<iota>)
    case (TyLiteral l)
    with \<tau> obtain i where "0 \<le> i" and "i < of_nat (length \<tau>s)" and "\<tau> = \<tau>s ! nat i"
      by (cases l) (auto simp: Let_def split: if_splits)
    then have "\<tau> \<in> set \<tau>s" by (simp add: nat_less_iff)
    with "4.prems"(1) show ?thesis by auto
  next
    case (TyPrim q)
    with \<tau> have "\<tau> = joins \<Sigma> \<tau>s" by (cases q) auto
    with "4.prems"(1) show ?thesis by (auto intro!: wf_joins dest!: fv_joins[THEN subsetD])
  qed (use \<tau> in auto)
qed (auto simp: bind_sum_Ok split: if_splits)

lemma attribute_type_wf:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> \<sigma> ; attribute_type \<Sigma> \<sigma> x = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma>"
proof (induction \<Sigma> \<sigma> x arbitrary: \<tau> rule: attribute_type.induct)
  case (1 \<Sigma> \<sigma> \<sigma>' x)
  have wf: "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> \<sigma>'" using "1.prems"(2) by simp_all
  from "1.prems"(3) obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where "attribute_type \<Sigma> \<sigma> x = Ok \<tau>\<^sub>1" and "attribute_type \<Sigma> \<sigma>' x = Ok \<tau>\<^sub>2"
    and \<tau>: "\<tau> = \<tau>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>2"
    by (auto simp: bind_sum_Ok)
  from "1.IH"(1)[OF "1.prems"(1) wf(1) this(1)] "1.IH"(2)[OF this(1) "1.prems"(1) wf(2) this(2)] show ?case
    unfolding \<tau> by (auto intro: wf_join dest!: fv_join_elem)
next
  case (2 \<Sigma> C \<sigma>s x)
  then have "(x, \<tau>) \<in> set (instantiate (fields \<Sigma> C) \<sigma>s)"
    by (auto simp: or_else_def split: option.splits dest: map_of_SomeD)
  with fields_wf[OF "2.prems"(1, 2) this] fields_fv_inst[OF "2.prems"(1, 2) this] show ?case by auto
qed simp_all

subsection \<open>Instances and type arguments\<close>

lemma product_lists_replicate: "\<lbrakk> xs \<in> set (product_lists (replicate n L)) ; x \<in> set xs \<rbrakk> \<Longrightarrow> x \<in> set L"
  by (induction n arbitrary: xs) auto

(* Candidate type argument of class C from the type arguments \<sigma>s of a class, a join of subterms of \<sigma>s and
   object *)
lemma instantiation_candidates_wf:
  assumes "wf_ty \<Sigma> (TyClass D \<sigma>s)" and "\<tau>s \<in> set (instantiation_candidates \<Sigma> C \<sigma>s)" and "\<tau> \<in> set \<tau>s"
  shows "fv \<tau> \<subseteq> \<Union> (fv ` set \<sigma>s) \<and> wf_ty \<Sigma> \<tau>"
proof -
  let ?\<rho>s = "remdups (concat (map subterms \<sigma>s) @ [TyPrim object])"
  from product_lists_replicate[OF assms(2)[unfolded instantiation_candidates_def] assms(3)]
  obtain \<rho>s where "\<rho>s \<in> set (subseqs ?\<rho>s)" and \<tau>: "\<tau> = joins \<Sigma> \<rho>s" by auto
  then have "set \<rho>s \<subseteq> set ?\<rho>s" using subseqs_powset[of ?\<rho>s] by blast
  then have "fv \<rho> \<subseteq> \<Union> (fv ` set \<sigma>s) \<and> wf_ty \<Sigma> \<rho>" if "\<rho> \<in> set \<rho>s" for \<rho>
  proof -
    from that \<open>set \<rho>s \<subseteq> set ?\<rho>s\<close> consider \<sigma> where "\<sigma> \<in> set \<sigma>s" and "\<rho> \<in> set (subterms \<sigma>)"
      | "\<rho> = TyPrim object"
      by auto
    then show ?thesis
    proof cases
      case 1
      with assms(1) have "wf_ty \<Sigma> \<sigma>" by auto
      with 1 fv_subterm[OF 1(2)] show ?thesis by (auto intro: wf_ty_subterm)
    qed simp
  qed
  then have wf: "\<forall>\<rho> \<in> set \<rho>s. wf_ty \<Sigma> \<rho>" and fv: "\<Union> (fv ` set \<rho>s) \<subseteq> \<Union> (fv ` set \<sigma>s)" by auto
  from wf_joins[OF wf] subset_trans[OF fv_joins fv] show ?thesis unfolding \<tau> by blast
qed

lemma instance_above_wf:
  assumes "wf_class_table \<Sigma>" and "wf_ty \<Sigma> \<tau>" and "instance_above \<Sigma> C \<tau> = Instance \<tau>s"
  shows "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fv \<tau> \<and> wf_ty \<Sigma> \<tau>'"
proof (cases \<tau>)
  case (TyClass D \<sigma>s)
  with assms(3) have anc: "C \<in> set (ancestors \<Sigma> D)" and \<tau>s: "\<tau>s = instantiated_ancestor \<Sigma> D \<sigma>s C"
    by (auto split: if_splits)
  from instantiated_ancestor_wf[OF assms(1) assms(2)[unfolded TyClass] anc] show ?thesis
    unfolding \<tau>s TyClass by auto
next
  case (TyPrim p)
  with assms(3) show ?thesis by (cases p) (auto split: if_splits)
qed (use assms(3) in auto)

lemma instance_below_wf:
  assumes "wf_ty \<Sigma> \<tau>" and "instance_below \<Sigma> C \<tau> = Instance \<tau>s"
  shows "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fv \<tau> \<and> wf_ty \<Sigma> \<tau>'"
proof (cases \<tau>)
  case (TyClass D \<sigma>s)
  with assms(2) obtain \<tau>ss
    where "filter (\<lambda>\<tau>s. list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> C \<tau>s D) \<sigma>s)
             (instantiation_candidates \<Sigma> C \<sigma>s) = \<tau>s # \<tau>ss"
    by (auto split: if_splits list.splits)
  then have "\<tau>s \<in> set (instantiation_candidates \<Sigma> C \<sigma>s)"
    by (metis filter_is_subset list.set_intros(1) subsetD)
  with instantiation_candidates_wf[OF assms(1)[unfolded TyClass] this] show ?thesis by (simp add: TyClass)
next
  case (TyPrim p)
  with assms(2) show ?thesis by (cases p) (auto split: if_splits)
qed (use assms(2) in auto)

(* Type arguments at which class C is instantiated by a well-formed type \<tau>: well-formed and over the type
   variables of \<tau> *)
lemma instance_at_wf:
  assumes "wf_class_table \<Sigma>" and "wf_ty \<Sigma> \<tau>" and "instance_at \<Sigma> C \<tau> = Instance \<tau>s"
  shows "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fv \<tau> \<and> wf_ty \<Sigma> \<tau>'"
proof (cases "instance_above \<Sigma> C \<tau>")
  case (Instance \<tau>s')
  with assms(3) have "\<tau>s' = \<tau>s" by (simp add: instance_at_def)
  with instance_above_wf[OF assms(1, 2) Instance] show ?thesis by simp
next
  case NoInstance
  with assms(3) have "instance_below \<Sigma> C \<tau> = Instance \<tau>s" by (simp add: instance_at_def)
  from instance_below_wf[OF assms(2) this] show ?thesis .
next
  case Undetermined
  with assms(3) show ?thesis by (simp add: instance_at_def)
qed

(* Type at which a type variable is bound by the join of two bindings *)
lemma join_cxt_lookup:
  assumes "fmlookup (join_cxt \<Sigma> \<gamma> \<gamma>') \<alpha> = Some \<tau>"
  obtains (left) "fmlookup \<gamma> \<alpha> = Some \<tau>" | (right) "fmlookup \<gamma>' \<alpha> = Some \<tau>"
    | (both) \<sigma> \<sigma>' where "fmlookup \<gamma> \<alpha> = Some \<sigma>" and "fmlookup \<gamma>' \<alpha> = Some \<sigma>'" and "\<tau> = \<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<sigma>'"
  using assms by (auto simp: join_cxt_def fmlookup_dom_iff split: option.splits if_splits)

(* Property of the type bound to a type variable by a fold of joins of bindings, holding of each binding's types
   and preserved by join *)
lemma foldr_join_cxt_lookup:
  assumes "fmlookup (foldr (join_cxt \<Sigma>) \<gamma>s fmempty) \<alpha> = Some \<tau>"
    and "\<forall>\<gamma> \<in> set \<gamma>s. \<forall>\<tau>'. fmlookup \<gamma> \<alpha> = Some \<tau>' \<longrightarrow> P \<tau>'" and "\<And>\<tau> \<tau>'. \<lbrakk> P \<tau> ; P \<tau>' \<rbrakk> \<Longrightarrow> P (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>')"
  shows "P \<tau>"
  using assms by (induction \<gamma>s arbitrary: \<tau>) (auto elim!: join_cxt_lookup)

lemma instance_at_wf_elem:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> \<tau> ; instance_at \<Sigma> C \<tau> = Instance \<tau>s \<rbrakk>
  \<Longrightarrow> \<forall>\<tau>' \<in> set \<tau>s. (\<forall>x. x \<in> fv \<tau>' \<longrightarrow> x \<in> fv \<tau>) \<and> wf_ty \<Sigma> \<tau>'"
  using instance_at_wf by blast

(* Step of the induction below for a type \<tau> \<squnion> \<tau>' matched by a type other than a variable *)
lemma type_args_union_range:
  assumes "\<And>\<tau>''. \<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> \<tau> ; fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha> = Some \<tau>'' \<rbrakk>
            \<Longrightarrow> (\<forall>x. x \<in> fv \<tau>'' \<longrightarrow> x \<in> fv \<tau>) \<and> wf_ty \<Sigma> \<tau>''"
    and "\<And>\<tau>''. \<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> \<tau>' ; fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>') \<alpha> = Some \<tau>'' \<rbrakk>
            \<Longrightarrow> (\<forall>x. x \<in> fv \<tau>'' \<longrightarrow> x \<in> fv \<tau>') \<and> wf_ty \<Sigma> \<tau>''"
    and "wf_class_table \<Sigma>" and "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')"
    and "fmlookup (type_args \<Sigma> \<alpha>s \<sigma> (TyUnion \<tau> \<tau>')) \<alpha> = Some \<tau>''" and "\<forall>\<beta>. \<sigma> \<noteq> TyVar \<beta>"
  shows "(\<forall>x. x \<in> fv \<tau>'' \<longrightarrow> x \<in> fv (TyUnion \<tau> \<tau>')) \<and> wf_ty \<Sigma> \<tau>''"
proof -
  have wf: "wf_ty \<Sigma> \<tau>" "wf_ty \<Sigma> \<tau>'" using assms(4) by simp_all
  note IH = assms(1)[OF assms(3) wf(1)] assms(2)[OF assms(3) wf(2)]
  from assms(5, 6) have "fmlookup (join_cxt \<Sigma> (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) (type_args \<Sigma> \<alpha>s \<sigma> \<tau>')) \<alpha> = Some \<tau>''"
    by (cases \<sigma>) simp_all
  then show ?thesis
  proof (cases rule: join_cxt_lookup)
    case left
    from IH(1)[OF left] show ?thesis by auto
  next
    case right
    from IH(2)[OF right] show ?thesis by auto
  next
    case (both \<rho> \<rho>')
    from IH(1)[OF both(1)] IH(2)[OF both(2)] show ?thesis
      unfolding both(3) by (auto intro: wf_join dest!: fv_join_elem)
  qed
qed

(* Step of the induction below for a class type matched against a type other than a union *)
lemma type_args_class_range:
  assumes "\<And>\<tau>s \<tau>''. \<lbrakk> wf_class_table \<Sigma> ; instance_at \<Sigma> C \<tau> = Instance \<tau>s ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>
             ; fmlookup (type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s) \<alpha> = Some \<tau>'' \<rbrakk>
            \<Longrightarrow> (\<forall>x. x \<in> fv \<tau>'' \<longrightarrow> (\<exists>\<tau> \<in> set \<tau>s. x \<in> fv \<tau>)) \<and> wf_ty \<Sigma> \<tau>''"
    and "wf_class_table \<Sigma>" and "wf_ty \<Sigma> \<tau>" and "fmlookup (type_args \<Sigma> \<alpha>s (TyClass C \<sigma>s) \<tau>) \<alpha> = Some \<tau>'"
    and "\<forall>\<rho> \<rho>'. \<tau> \<noteq> TyUnion \<rho> \<rho>'"
  shows "(\<forall>x. x \<in> fv \<tau>' \<longrightarrow> x \<in> fv \<tau>) \<and> wf_ty \<Sigma> \<tau>'"
proof -
  from assms(4, 5) obtain \<tau>s where inst: "instance_at \<Sigma> C \<tau> = Instance \<tau>s"
    and lookup: "fmlookup (type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s) \<alpha> = Some \<tau>'"
    by (cases \<tau>) (auto split: instances.splits)
  from instance_at_wf_elem[OF assms(2, 3) inst] have wf: "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>"
    and fv: "\<forall>\<tau>'' \<in> set \<tau>s. \<forall>x. x \<in> fv \<tau>'' \<longrightarrow> x \<in> fv \<tau>"
    by auto
  from assms(1)[OF assms(2) inst wf lookup] fv show ?thesis by blast
qed

(* Step of the induction below for a union matched against a type other than a union *)
lemma type_args_union_left_range:
  assumes "\<And>\<tau>'. \<lbrakk> \<not> (\<Sigma> \<turnstile> \<tau> <: \<sigma> \<and> fv \<sigma> \<inter> set \<alpha>s = {} \<or> \<Sigma> \<turnstile> \<tau> <: \<sigma>' \<and> fv \<sigma>' \<inter> set \<alpha>s = {})
             ; wf_class_table \<Sigma> ; wf_ty \<Sigma> \<tau> ; fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha> = Some \<tau>' \<rbrakk>
            \<Longrightarrow> (\<forall>x. x \<in> fv \<tau>' \<longrightarrow> x \<in> fv \<tau>) \<and> wf_ty \<Sigma> \<tau>'"
    and "\<And>\<tau>'. \<lbrakk> \<not> (\<Sigma> \<turnstile> \<tau> <: \<sigma> \<and> fv \<sigma> \<inter> set \<alpha>s = {} \<or> \<Sigma> \<turnstile> \<tau> <: \<sigma>' \<and> fv \<sigma>' \<inter> set \<alpha>s = {})
             ; wf_class_table \<Sigma> ; wf_ty \<Sigma> \<tau> ; fmlookup (type_args \<Sigma> \<alpha>s \<sigma>' \<tau>) \<alpha> = Some \<tau>' \<rbrakk>
            \<Longrightarrow> (\<forall>x. x \<in> fv \<tau>' \<longrightarrow> x \<in> fv \<tau>) \<and> wf_ty \<Sigma> \<tau>'"
    and "wf_class_table \<Sigma>" and "wf_ty \<Sigma> \<tau>" and "fmlookup (type_args \<Sigma> \<alpha>s (TyUnion \<sigma> \<sigma>') \<tau>) \<alpha> = Some \<tau>'"
    and "\<forall>\<rho> \<rho>'. \<tau> \<noteq> TyUnion \<rho> \<rho>'"
  shows "(\<forall>x. x \<in> fv \<tau>' \<longrightarrow> x \<in> fv \<tau>) \<and> wf_ty \<Sigma> \<tau>'"
proof -
  from assms(5, 6)
  have "\<not> (\<Sigma> \<turnstile> \<tau> <: \<sigma> \<and> fv \<sigma> \<inter> set \<alpha>s = {} \<or> \<Sigma> \<turnstile> \<tau> <: \<sigma>' \<and> fv \<sigma>' \<inter> set \<alpha>s = {})
    \<and> fmlookup (join_cxt \<Sigma> (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) (type_args \<Sigma> \<alpha>s \<sigma>' \<tau>)) \<alpha> = Some \<tau>'"
    by (cases \<tau>) (auto split: if_splits)
  then have cond: "\<not> (\<Sigma> \<turnstile> \<tau> <: \<sigma> \<and> fv \<sigma> \<inter> set \<alpha>s = {} \<or> \<Sigma> \<turnstile> \<tau> <: \<sigma>' \<and> fv \<sigma>' \<inter> set \<alpha>s = {})"
    and lookup: "fmlookup (join_cxt \<Sigma> (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) (type_args \<Sigma> \<alpha>s \<sigma>' \<tau>)) \<alpha> = Some \<tau>'"
    by blast+
  note IH = assms(1)[OF cond assms(3, 4)] assms(2)[OF cond assms(3, 4)]
  from lookup show ?thesis
  proof (cases rule: join_cxt_lookup)
    case left
    from IH(1)[OF left] show ?thesis .
  next
    case right
    from IH(2)[OF right] show ?thesis .
  next
    case (both \<rho> \<rho>')
    from IH(1)[OF both(1)] IH(2)[OF both(2)] show ?thesis
      unfolding both(3) by (auto intro: wf_join dest!: fv_join_elem)
  qed
qed

(* Type bound to a type variable by matching \<sigma> against well-formed \<tau>: over the type variables of \<tau> and
   well-formed *)
lemma type_args_range:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> \<tau> ; fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha> = Some \<tau>' \<rbrakk>
  \<Longrightarrow> (\<forall>x. x \<in> fv \<tau>' \<longrightarrow> x \<in> fv \<tau>) \<and> wf_ty \<Sigma> \<tau>'"
  "\<lbrakk> wf_class_table \<Sigma> ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> ; fmlookup (type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s) \<alpha> = Some \<tau>' \<rbrakk>
  \<Longrightarrow> (\<forall>x. x \<in> fv \<tau>' \<longrightarrow> (\<exists>\<tau> \<in> set \<tau>s. x \<in> fv \<tau>)) \<and> wf_ty \<Sigma> \<tau>'"
proof (induction \<Sigma> \<alpha>s \<sigma> \<tau> and \<Sigma> \<alpha>s \<sigma>s \<tau>s arbitrary: \<tau>' and \<tau>' rule: type_args_type_args_seq.induct)
  case (1 \<Sigma> \<alpha>s \<alpha>' \<tau>)
  then show ?case by (auto simp: wf_base_type split: if_splits)
next
  case "2_1"
  from "2_1.IH" "2_1.prems" show ?case by (rule type_args_union_range) auto
next
  case "2_2"
  from "2_2.IH" "2_2.prems" show ?case by (rule type_args_union_range) auto
next
  case "2_3"
  from "2_3.IH" "2_3.prems" show ?case by (rule type_args_union_range) auto
next
  case "2_4"
  from "2_4.IH" "2_4.prems" show ?case by (rule type_args_union_range) auto
next
  case "2_5"
  from "2_5.IH" "2_5.prems" show ?case by (rule type_args_union_range) auto
next
  case "2_6"
  from "2_6.IH" "2_6.prems" show ?case by (rule type_args_union_range) auto
next
  case "2_7"
  from "2_7.IH" "2_7.prems" show ?case by (rule type_args_union_range) auto
next
  case "2_8"
  from "2_8.IH" "2_8.prems" show ?case by (rule type_args_union_range) auto
next
  case (3 \<Sigma> \<alpha>s \<sigma> \<tau>)
  from "3.prems" have "wf_ty \<Sigma> \<tau>" and "fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha> = Some \<tau>'" by simp_all
  from "3.IH"[OF "3.prems"(1) this] show ?case by simp
next
  case (4 \<Sigma> \<alpha>s \<sigma> \<tau>)
  from "4.prems" have "wf_ty \<Sigma> \<tau>" and "fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha> = Some \<tau>'" by simp_all
  from "4.IH"[OF "4.prems"(1) this] show ?case by simp
next
  case (5 \<Sigma> \<alpha>s \<sigma>s \<tau>s)
  from "5.prems" have "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>" and "fmlookup (type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s) \<alpha> = Some \<tau>'"
    by simp_all
  from "5.IH"[OF "5.prems"(1) this] show ?case by auto
next
  case (6 \<Sigma> \<alpha>s \<sigma>s \<sigma> \<tau>s \<tau>)
  from "6.prems" have "\<forall>\<tau>' \<in> set (\<tau> # \<tau>s). wf_ty \<Sigma> \<tau>'"
    and "fmlookup (type_args_seq \<Sigma> \<alpha>s (\<sigma> # \<sigma>s) (\<tau> # \<tau>s)) \<alpha> = Some \<tau>'"
    by simp_all
  from "6.IH"[OF "6.prems"(1) this] show ?case by auto
next
  case "7_1"
  from "7_1.IH" "7_1.prems" show ?case by (rule type_args_class_range) auto
next
  case "7_2"
  from "7_2.IH" "7_2.prems" show ?case by (rule type_args_class_range) auto
next
  case "7_3"
  from "7_3.IH" "7_3.prems" show ?case by (rule type_args_class_range) auto
next
  case "7_4"
  from "7_4.IH" "7_4.prems" show ?case by (rule type_args_class_range) auto
next
  case "7_5"
  from "7_5.IH" "7_5.prems" show ?case by (rule type_args_class_range) auto
next
  case "7_6"
  from "7_6.IH" "7_6.prems" show ?case by (rule type_args_class_range) auto
next
  case "7_7"
  from "7_7.IH" "7_7.prems" show ?case by (rule type_args_class_range) auto
next
  case "7_8"
  from "7_8.IH" "7_8.prems" show ?case by (rule type_args_class_range) auto
next
  case "8_1"
  from "8_1.IH" "8_1.prems" show ?case by (rule type_args_union_left_range) auto
next
  case "8_2"
  from "8_2.IH" "8_2.prems" show ?case by (rule type_args_union_left_range) auto
next
  case "8_3"
  from "8_3.IH" "8_3.prems" show ?case by (rule type_args_union_left_range) auto
next
  case "8_4"
  from "8_4.IH" "8_4.prems" show ?case by (rule type_args_union_left_range) auto
next
  case "8_5"
  from "8_5.IH" "8_5.prems" show ?case by (rule type_args_union_left_range) auto
next
  case "8_6"
  from "8_6.IH" "8_6.prems" show ?case by (rule type_args_union_left_range) auto
next
  case "8_7"
  from "8_7.IH" "8_7.prems" show ?case by (rule type_args_union_left_range) auto
next
  case "8_8"
  from "8_8.IH" "8_8.prems" show ?case by (rule type_args_union_left_range) auto
next
  case (10 \<Sigma> \<alpha>s \<sigma>s \<tau>s)
  let ?P = "\<lambda>\<tau>'. (\<forall>x. x \<in> fv \<tau>' \<longrightarrow> (\<exists>\<tau> \<in> set \<tau>s. x \<in> fv \<tau>)) \<and> wf_ty \<Sigma> \<tau>'"
  have elem: "?P \<tau>'" if "\<gamma> \<in> set (map2 (type_args \<Sigma> \<alpha>s) \<sigma>s \<tau>s)" and "fmlookup \<gamma> \<alpha> = Some \<tau>'" for \<gamma> \<tau>'
  proof -
    from that(1) obtain \<sigma> \<tau> where mem: "(\<sigma>, \<tau>) \<in> set (zip \<sigma>s \<tau>s)" and \<gamma>: "\<gamma> = type_args \<Sigma> \<alpha>s \<sigma> \<tau>" by auto
    from "10.prems"(2) set_zip_rightD[OF mem] have wf: "wf_ty \<Sigma> \<tau>" by auto
    from "10.IH"[OF mem refl "10.prems"(1) wf that(2)[unfolded \<gamma>]] set_zip_rightD[OF mem] show ?thesis by auto
  qed
  show ?case
  proof (rule foldr_join_cxt_lookup[OF "10.prems"(3)[unfolded type_args_seq.simps]])
    show "\<forall>\<gamma> \<in> set (map2 (type_args \<Sigma> \<alpha>s) \<sigma>s \<tau>s). \<forall>\<tau>'. fmlookup \<gamma> \<alpha> = Some \<tau>' \<longrightarrow> ?P \<tau>'" using elem by blast
    show "?P (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>')" if "?P \<tau>" and "?P \<tau>'" for \<tau> \<tau>'
      using that by (blast intro: wf_join dest: fv_join_elem)
  qed
qed simp_all


subsection \<open>Operators\<close>

(* Result type of an operator overload at well-formed operand types *)
lemma binop_overload_result:
  "\<lbrakk> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega> ; wf_ty \<Sigma> \<sigma>\<^sub>1 ; wf_ty \<Sigma> \<sigma>\<^sub>2 \<rbrakk>
  \<Longrightarrow> wf_ty \<Sigma> (snd \<omega>) \<and> fv (snd \<omega>) \<subseteq> fv \<sigma>\<^sub>1 \<union> fv \<sigma>\<^sub>2"
  by (induction rule: binop_overload.induct) (auto simp: wf_base_type intro: wf_join dest!: fv_join_elem)

lemma resolve_binop_union_wf:
  "\<lbrakk> wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<sigma>' ; resolve_binop_union \<Sigma> op \<sigma> \<sigma>' = Some \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma> \<union> fv \<sigma>'"
proof (induction "size \<sigma> + size \<sigma>'" arbitrary: \<sigma> \<sigma>' \<tau> rule: less_induct)
  case less
  from less.prems(3) show ?case
  proof (cases rule: resolve_binop_union_cases)
    case overload
    from resolve_binop_overload[OF overload] obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where "binop_overload \<Sigma> op \<sigma> \<sigma>' ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>)" .
    from binop_overload_result[OF this less.prems(1, 2)] show ?thesis by simp
  next
    case (left \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
    with less.prems(1) have "wf_ty \<Sigma> \<sigma>\<^sub>1" and "wf_ty \<Sigma> \<sigma>\<^sub>2" by simp_all
    from less.hyps[OF _ this(1) less.prems(2) left(2)] less.hyps[OF _ this(2) less.prems(2) left(3)] left(1, 4)
    show ?thesis by (auto intro: wf_join dest!: fv_join_elem)
  next
    case (right \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
    with less.prems(2) have "wf_ty \<Sigma> \<sigma>\<^sub>1" and "wf_ty \<Sigma> \<sigma>\<^sub>2" by simp_all
    from less.hyps[OF _ less.prems(1) this(1) right(2)] less.hyps[OF _ less.prems(1) this(2) right(3)]
      right(1, 4)
    show ?thesis by (auto intro: wf_join dest!: fv_join_elem)
  qed
qed

lemma resolve_unop_wf: "resolve_unop \<Sigma> op \<sigma> = Some \<tau> \<Longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> = {}"
  by (auto elim!: resolve_unop_overload dest!: unop_overload_types)

subsection \<open>Names\<close>

lemma resolve_name_fv:
  assumes "wf_cxt \<Sigma> \<Gamma>" and "resolve_name \<Gamma> q = Some \<theta>"
  shows "fv_entry \<theta> \<subseteq> tyvars \<Gamma>"
proof (cases q)
  case (Simple x)
  with resolve_name_lookup[OF assms(2)] have "fmlookup \<Gamma> x = Some \<theta>" by simp
  then show ?thesis by (rule tyvars_entry)
next
  case (Qualified q' x)
  with lookup_qualified_fv[OF assms(1) resolve_name_lookup[OF assms(2)[unfolded Qualified]]] show ?thesis
    by simp
qed

lemma class_of_name_dom: "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; class_of_name \<Gamma> e = Some C \<rbrakk> \<Longrightarrow> C |\<in>| fmdom \<Sigma>"
  by (auto simp: class_of_name_def entry_of_def bind_eq_Some_conv split: option.splits cxt_entry.splits
      dest!: resolve_name_wf)

(* Scheme of a name, callable with a well-formed body over the type variables of the context *)
lemma scheme_of_name_wf:
  assumes "wf_cxt \<Sigma> \<Gamma>" and "scheme_of_name \<Gamma> e = Some (TyScheme \<alpha>s \<tau>)"
  shows "wf_ty \<Sigma> \<tau> \<and> (\<exists>\<sigma>s \<sigma>. \<tau> = TyCallable \<sigma>s \<sigma>) \<and> fv \<tau> - set \<alpha>s \<subseteq> tyvars \<Gamma>"
proof -
  from assms(2) obtain q where "resolve_name \<Gamma> q = Some (Scheme (TyScheme \<alpha>s \<tau>))"
    by (auto simp: scheme_of_name_def entry_of_def bind_eq_Some_conv split: option.splits cxt_entry.splits)
  from resolve_name_wf[OF assms(1) this] resolve_name_fv[OF assms(1) this] show ?thesis by simp
qed

lemma tyvars_TypeVar: "fmlookup \<Gamma> x = Some TypeVar \<Longrightarrow> x \<in> tyvars \<Gamma>"
  by (auto simp: tyvars_def fmlookup_dom'_iff)

(* Attribute of a module whose context has no type variables *)
lemma attr_module_Ok: "\<lbrakk> tyvars \<Gamma> = {} ; attr_module q \<Gamma> x q' = Ok \<tau> \<rbrakk> \<Longrightarrow> fmlookup \<Gamma> x = Some (Ty \<tau>)"
  by (auto simp: attr_module_def split: option.splits cxt_entry.splits dest: tyvars_TypeVar)

lemma module_attribute_Ok:
  assumes "module_attribute \<Gamma> e x = Some (Ok \<tau>)"
  obtains q q' \<Gamma>' where "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')" and "attr_module q' \<Gamma>' x (Qualified q x) = Ok \<tau>"
proof -
  from assms obtain q where "dotted_name e = Some q"
    and m: "(case lookup \<Gamma> q of
               Some (ModChecked q' \<Gamma>') \<Rightarrow> Some (attr_module q' \<Gamma>' x (Qualified q x))
             | Some (ModStub q') \<Rightarrow> Some (Fail (Violates RuleQualified (SubmoduleNotImported q')))
             | _ \<Rightarrow> None) = Some (Ok \<tau>)"
    by (cases "dotted_name e") (simp_all add: module_attribute_def)
  then obtain q' \<Gamma>' where "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
    by (cases "lookup \<Gamma> q") (auto split: cxt_entry.splits)
  with m have "attr_module q' \<Gamma>' x (Qualified q x) = Ok \<tau>" by simp
  with \<open>lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')\<close> show thesis by (rule that)
qed

(* Attribute of a checked module: well-formed and closed, since the context of the module is *)
lemma module_attribute_wf:
  assumes "wf_cxt \<Sigma> \<Gamma>" and "module_attribute \<Gamma> e x = Some (Ok \<tau>)"
  shows "wf_ty \<Sigma> \<tau> \<and> fv \<tau> = {}"
proof -
  from assms(2) obtain q q' \<Gamma>' where "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
    and "attr_module q' \<Gamma>' x (Qualified q x) = Ok \<tau>"
    by (rule module_attribute_Ok)
  from lookup_wf[OF assms(1) this(1)] have tv: "tyvars \<Gamma>' = {}" and wf: "wf_cxt \<Sigma> \<Gamma>'" by simp_all
  from attr_module_Ok[OF tv \<open>attr_module q' \<Gamma>' x (Qualified q x) = Ok \<tau>\<close>]
  have x: "fmlookup \<Gamma>' x = Some (Ty \<tau>)" .
  from wf_cxt_lookup[OF wf x] tyvars_entry[OF x] tv show ?thesis by simp
qed

subsection \<open>Contexts\<close>

lemma tyvars_bound:
  assumes "\<And>x \<theta>. fmlookup \<Delta> x = Some \<theta> \<Longrightarrow> \<theta> \<noteq> TypeVar \<and> fv_entry \<theta> \<subseteq> V"
  shows "tyvars \<Delta> \<subseteq> V"
proof
  fix x
  assume "x \<in> tyvars \<Delta>"
  then consider "fmlookup \<Delta> x = Some TypeVar" | y \<theta> where "fmlookup \<Delta> y = Some \<theta>" and "x \<in> fv_entry \<theta>"
    by (auto simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff)
  then show "x \<in> V"
  proof cases
    case 1
    with assms show ?thesis by blast
  next
    case 2
    with assms[OF 2(1)] show ?thesis by blast
  qed
qed

(* Context of parameters at well-formed types over the type variables V *)
lemma params_cxt_wf:
  assumes "params_cxt xs \<tau>s = Ok \<Delta>" and "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> V"
  shows "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> V"
proof -
  from assms(1) have \<Delta>: "\<Delta> = fmap_of_list (zip xs (map Ty \<tau>s))" by (auto simp: params_cxt_def split: if_splits)
  have entries: "\<theta> \<noteq> TypeVar \<and> wf_entry \<Sigma> \<theta> \<and> fv_entry \<theta> \<subseteq> V" if "fmlookup \<Delta> x = Some \<theta>" for x \<theta>
  proof -
    from that obtain \<tau> where "\<tau> \<in> set \<tau>s" and "\<theta> = Ty \<tau>"
      by (auto simp: \<Delta> fmlookup_of_list dest!: map_of_SomeD set_zip_rightD)
    with assms(2) show ?thesis by auto
  qed
  then have "wf_cxt \<Sigma> \<Delta>" by (auto simp: wf_cxt_iff)
  moreover have "tyvars \<Delta> \<subseteq> V" by (rule tyvars_bound) (use entries in blast)
  ultimately show ?thesis ..
qed

subsection \<open>Type arguments inferred from arguments\<close>

lemma type_args_of_elem:
  "\<lbrakk> type_args_of \<gamma> \<alpha>s = Ok \<tau>s ; \<tau> \<in> set \<tau>s \<rbrakk> \<Longrightarrow> \<exists>\<alpha>. fmlookup \<gamma> \<alpha> = Some \<tau>"
  by (auto simp: type_args_of_def or_else_def dest!: those_sum_map_Ok_elem split: option.splits)

(* Type arguments inferred from the argument types which synthesise, well-formed and over the type variables V
   when those are *)
lemma inferred_type_args_wf:
  assumes "wf_class_table \<Sigma>" and "inferred_type_args \<Sigma> \<alpha>s \<sigma>s ms = Ok \<tau>s"
    and "\<forall>\<tau>. Ok \<tau> \<in> set ms \<longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> V"
  shows "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> V"
proof
  fix \<tau>
  assume \<tau>: "\<tau> \<in> set \<tau>s"
  let ?\<sigma>\<tau>s = "filter (Not \<circ> isl \<circ> snd) (zip \<sigma>s ms)"
  from assms(2) have "type_args_of (type_args_seq \<Sigma> \<alpha>s (map fst ?\<sigma>\<tau>s) (map (projr \<circ> snd) ?\<sigma>\<tau>s)) \<alpha>s = Ok \<tau>s"
    by (auto simp: inferred_type_args_def Let_def split: sum.splits)
  from type_args_of_elem[OF this \<tau>] obtain \<alpha>
    where lookup: "fmlookup (type_args_seq \<Sigma> \<alpha>s (map fst ?\<sigma>\<tau>s) (map (projr \<circ> snd) ?\<sigma>\<tau>s)) \<alpha> = Some \<tau>" ..
  have ok: "wf_ty \<Sigma> \<tau>' \<and> fv \<tau>' \<subseteq> V" if "\<tau>' \<in> set (map (projr \<circ> snd) ?\<sigma>\<tau>s)" for \<tau>'
  proof -
    from that obtain m where "m \<in> set ms" and "\<not> isl m" and "\<tau>' = projr m" by (auto dest: set_zip_rightD)
    then have "Ok \<tau>' \<in> set ms" by (cases m) auto
    with assms(3) show ?thesis by blast
  qed
  from type_args_range(2)[OF assms(1) _ lookup] ok show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> V" by blast
qed

subsection \<open>Expressions\<close>

(* Types synthesised in a well-formed context: well-formed and over the type variables of the context; bindings
   of qualifiers likewise *)
lemma synth_wf:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> \<forall>\<tau>. synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> \<forall>\<tau>. synth_expr_at \<Sigma> \<Gamma> e' = Ok \<tau> \<longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> \<forall>\<tau>. elements_join \<Sigma> \<Gamma> es = Ok \<tau> \<longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> \<forall>\<tau>. callee \<Sigma> \<Gamma> e' es = Ok \<tau> \<longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
  "wf_ty \<Sigma> \<sigma> \<Longrightarrow> \<forall>\<tau>. synth_call \<Sigma> \<Gamma> e' \<sigma> kws es = Ok \<tau> \<longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma>"
  "check_expr \<Sigma> \<Gamma> e \<tau>\<^sub>0 = m \<Longrightarrow> True"
  "check_expr_at \<Sigma> \<Gamma> e' \<tau>\<^sub>0 = m \<Longrightarrow> True"
  "check_expr' \<Sigma> \<Gamma> e \<tau>\<^sub>0 = m' \<Longrightarrow> True"
  "check_args \<Sigma> \<Gamma> e' kws es \<sigma>s = m \<Longrightarrow> True"
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> \<forall>\<Delta>. quals \<Sigma> \<Gamma> gs = Ok \<Delta> \<longrightarrow> wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
proof (induction \<Sigma> \<Gamma> e and \<Sigma> \<Gamma> e' and \<Sigma> \<Gamma> es and \<Sigma> \<Gamma> e' es and \<Sigma> \<Gamma> e' \<sigma> kws es and \<Sigma> \<Gamma> e \<tau>\<^sub>0
    and \<Sigma> \<Gamma> e' \<tau>\<^sub>0 and \<Sigma> \<Gamma> e \<tau>\<^sub>0 and \<Sigma> \<Gamma> e' kws es \<sigma>s and \<Sigma> \<Gamma> gs
    rule:
      synth_expr_synth_expr_at_elements_join_callee_synth_call_check_expr_check_expr_at_check_expr'_check_args_quals.induct)
  case (1 \<Sigma> \<Gamma> x)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_expr \<Sigma> \<Gamma> (ExprVar x) = Ok \<tau>"
    then have "fmlookup \<Gamma> x = Some (Ty \<tau>)" by (auto split: option.splits cxt_entry.splits)
    with wf_cxt_lookup[OF "1.prems"(2) this] tyvars_entry[OF this] show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" by simp
  qed
next
  case (2 \<Sigma> \<Gamma> l)
  then show ?case by (auto split: lit.splits)
next
  case (3 \<Sigma> \<Gamma> e es kws)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>"
    show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
    proof (cases "lambda_of (node e)")
      case (Some xe)
      then obtain xs e' where lam: "lambda_of (node e) = Some (xs, e')" by (cases xe) simp
      with synth obtain \<Delta> where args: "lambda_args e xs kws es (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<Delta>"
        and body: "synth_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' = Ok \<tau>"
        by (auto simp: bind_sum_Ok)
      from args obtain \<tau>s where \<tau>s: "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
        and \<Delta>: "params_cxt xs \<tau>s = Ok \<Delta>"
        by (auto simp: lambda_args_def bind_sum_Ok)
      have "wf_ty \<Sigma> \<tau>' \<and> fv \<tau>' \<subseteq> tyvars \<Gamma>" if "\<tau>' \<in> set \<tau>s" for \<tau>'
        using those_sum_map_Ok_elem[OF \<tau>s that] "3.IH"(6)[OF lam refl _ "3.prems"] by blast
      then have \<Delta>': "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>" using params_cxt_wf[OF \<Delta>] by blast
      with "3.prems"(2) have cxt: "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>)" by (auto intro: wf_cxt_add)
      from "3.IH"(7)[OF lam refl args "3.prems"(1) cxt] body have "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars (\<Gamma> \<otimes> \<Delta>)" by blast
      with tyvars_add[of \<Gamma> \<Delta>] \<Delta>' show ?thesis by blast
    next
      case None
      show ?thesis
      proof (cases "constructor_class \<Sigma> \<Gamma> e")
        case (Some m)
        from constr_synth[OF synth None Some] obtain C explicit x\<sigma>s \<sigma>es \<tau>s where m: "m = Ok (C, explicit)"
          and fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
          and cargs: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
          and \<tau>: "\<tau> = TyClass C \<tau>s"
          and explicit: "explicit = Some \<tau>s \<or> explicit = None
            \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C) (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es)
                = Ok \<tau>s" .
        from constructor_class_Ok[OF Some[unfolded m]] "3.prems"(2) have C: "C |\<in>| fmdom \<Sigma>"
          by (auto dest: class_of_name_dom)
        from explicit show ?thesis
        proof
          assume "explicit = Some \<tau>s"
          with constructor_class_Ok[OF Some[unfolded m]] obtain \<psi> where "resolve_type \<Sigma> \<Gamma> \<psi> = Ok (TyClass C \<tau>s)"
            by auto
          from resolve_type_wf[OF "3.prems"(2) this] show ?thesis by (simp add: \<tau>)
        next
          assume inferred: "explicit = None
            \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C) (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
          have "wf_ty \<Sigma> \<tau>' \<and> fv \<tau>' \<subseteq> tyvars \<Gamma>" if "Ok \<tau>' \<in> set (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es)" for \<tau>'
          proof -
            from that obtain z where "z \<in> set \<sigma>es" and "synth_expr_at \<Sigma> \<Gamma> (snd z) = Ok \<tau>'" by auto
            with "3.IH"(3)[OF None Some m refl fields cargs _ this(1) "3.prems"] inferred show ?thesis by blast
          qed
          with inferred_type_args_wf[OF "3.prems"(1), of _ _ _ _ "tyvars \<Gamma>"] inferred
          have "\<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>' \<and> fv \<tau>' \<subseteq> tyvars \<Gamma>" by blast
          with C inferred_type_args_length inferred show ?thesis by (auto simp: \<tau>)
        qed
      next
        case cc: None
        with synth None obtain \<sigma> where callee: "callee \<Sigma> \<Gamma> e es = Ok \<sigma>"
          and call: "synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau>"
          by (auto simp: bind_sum_Ok)
        from "3.IH"(1)[OF None cc "3.prems"] callee have \<sigma>: "wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> tyvars \<Gamma>" by blast
        from "3.IH"(2)[OF None cc callee] \<sigma> call have "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma>" by blast
        with \<sigma> show ?thesis by blast
      qed
    qed
  qed
next
  case (4 \<Sigma> \<Gamma> op e e')
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_expr \<Sigma> \<Gamma> (ExprBinOp op e e') = Ok \<tau>"
    then obtain \<sigma> \<sigma>' where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and \<sigma>': "synth_expr_at \<Sigma> \<Gamma> e' = Ok \<sigma>'"
      and res: "resolve_binop_union \<Sigma> op \<sigma> \<sigma>' = Some \<tau>"
      by (auto simp: bind_sum_Ok or_else_def split: option.splits)
    from "4.IH" "4.prems" \<sigma> \<sigma>' have "wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> tyvars \<Gamma>" and "wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> tyvars \<Gamma>" by blast+
    with resolve_binop_union_wf[OF _ _ res] show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" by blast
  qed
next
  case (5 \<Sigma> \<Gamma> op e)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_expr \<Sigma> \<Gamma> (ExprUnOp op e) = Ok \<tau>"
    then obtain \<sigma> where "resolve_unop \<Sigma> op \<sigma> = Some \<tau>"
      by (auto simp: bind_sum_Ok or_else_def split: if_splits option.splits)
    from resolve_unop_wf[OF this] show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" by simp
  qed
next
  case (8 \<Sigma> \<Gamma> e\<^sub>1 e e\<^sub>2)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume synth: "synth_expr \<Sigma> \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) = Ok \<tau>"
    then have chk: "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()" by (auto simp: bind_sum_Ok)
    note IH = "8.IH"(2)[OF chk "8.prems"] "8.IH"(3)[OF chk "8.prems"]
    from synth show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
    proof (cases rule: synth_cond)
      case (1 \<sigma>\<^sub>1 \<sigma>\<^sub>2)
      with IH show ?thesis by (auto intro: wf_join dest!: fv_join_elem)
    next
      case 2
      with IH show ?thesis by blast
    next
      case 3
      with IH show ?thesis by blast
    qed
  qed
next
  case (9 \<Sigma> \<Gamma> es)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_expr \<Sigma> \<Gamma> (ExprList es) = Ok \<tau>"
    then obtain \<tau>' where "es \<noteq> []" and "elements_join \<Sigma> \<Gamma> es = Ok \<tau>'" and "\<tau> = TyList \<tau>'"
      by (auto simp: bind_sum_Ok split: if_splits)
    with "9.IH"[OF this(1) "9.prems"] show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" by auto
  qed
next
  case (10 \<Sigma> \<Gamma> es)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_expr \<Sigma> \<Gamma> (ExprTuple es) = Ok \<tau>"
    then obtain \<tau>s where \<tau>s: "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s" and \<tau>: "\<tau> = TyTuple \<tau>s"
      by (auto simp: bind_sum_Ok)
    have "wf_ty \<Sigma> \<tau>' \<and> fv \<tau>' \<subseteq> tyvars \<Gamma>" if "\<tau>' \<in> set \<tau>s" for \<tau>'
      using those_sum_map_Ok_elem[OF \<tau>s that] "10.IH"[OF _ "10.prems"] by blast
    then show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" unfolding \<tau> by auto
  qed
next
  case (11 \<Sigma> \<Gamma> e x)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume synth: "synth_expr \<Sigma> \<Gamma> (ExprAttribute e x) = Ok \<tau>"
    show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
    proof (cases "module_attribute \<Gamma> (node e) x")
      case (Some m)
      with synth have "module_attribute \<Gamma> (node e) x = Some (Ok \<tau>)" by simp
      from module_attribute_wf[OF "11.prems"(2) this] show ?thesis by simp
    next
      case None
      with synth obtain \<sigma> where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and attr: "attribute_type \<Sigma> \<sigma> x = Ok \<tau>"
        by (auto simp: bind_sum_Ok)
      from "11.IH"[OF None "11.prems"] \<sigma> have "wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> tyvars \<Gamma>" by blast
      with attribute_type_wf[OF "11.prems"(1) _ attr] show ?thesis by blast
    qed
  qed
next
  case (12 \<Sigma> \<Gamma> e e')
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_expr \<Sigma> \<Gamma> (ExprSubscript e e') = Ok \<tau>"
    then obtain \<sigma> where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
      and sub: "subscript_type \<Sigma> \<sigma> (check_expr_at \<Sigma> \<Gamma> e' (TyPrim int)) (check_expr_at \<Sigma> \<Gamma> e' (TyPrim str))
                  (pos_of e') (synth_expr_at \<Sigma> \<Gamma> e') = Ok \<tau>"
      by (auto simp: bind_sum_Ok)
    from "12.IH" "12.prems" \<sigma> have "wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> tyvars \<Gamma>" by blast
    with subscript_type_wf[OF _ sub] show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" by blast
  qed
next
  case (13 \<Sigma> \<Gamma> kvs)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_expr \<Sigma> \<Gamma> (ExprDict kvs) = Ok \<tau>"
    then obtain \<tau>' where "kvs \<noteq> []"
      and "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e (TyPrim str)) (map fst kvs)) = Ok ()"
      and "elements_join \<Sigma> \<Gamma> (map snd kvs) = Ok \<tau>'" and "\<tau> = TyDict \<tau>'"
      by (auto simp: bind_sum_Ok split: if_splits)
    with "13.IH"(2)[OF this(1, 2) "13.prems"] show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" by auto
  qed
next
  case (14 \<Sigma> \<Gamma> e gs)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_expr \<Sigma> \<Gamma> (ExprListComp e gs) = Ok \<tau>"
    then obtain \<Delta> \<tau>' where quals: "quals \<Sigma> \<Gamma> gs = Ok \<Delta>" and cap: "captured gs (captures (node e)) \<Delta> = Ok ()"
      and body: "synth_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e = Ok \<tau>'" and \<tau>: "\<tau> = TyList (base_type \<tau>')"
      by (auto simp: bind_sum_Ok)
    from "14.IH"(1)[OF "14.prems"] quals have \<Delta>: "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>" by blast
    with "14.prems"(2) have cxt: "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>)" by (auto intro: wf_cxt_add)
    from "14.IH"(2)[OF quals cap "14.prems"(1) cxt] body have "wf_ty \<Sigma> \<tau>' \<and> fv \<tau>' \<subseteq> tyvars (\<Gamma> \<otimes> \<Delta>)" by blast
    with tyvars_add[of \<Gamma> \<Delta>] \<Delta> show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" unfolding \<tau> by (auto simp: wf_base_type)
  qed
next
  case (15 \<Sigma> \<Gamma> e e' gs)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_expr \<Sigma> \<Gamma> (ExprDictComp e e' gs) = Ok \<tau>"
    then obtain \<Delta> \<tau>' where quals: "quals \<Sigma> \<Gamma> gs = Ok \<Delta>"
      and cap: "captured gs (captures (node e) \<union> captures (node e')) \<Delta> = Ok ()"
      and key: "check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str) = Ok ()"
      and body: "synth_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' = Ok \<tau>'" and \<tau>: "\<tau> = TyDict (base_type \<tau>')"
      by (auto simp: bind_sum_Ok)
    from "15.IH"(1)[OF "15.prems"] quals have \<Delta>: "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>" by blast
    with "15.prems"(2) have cxt: "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>)" by (auto intro: wf_cxt_add)
    from "15.IH"(3)[OF quals cap key "15.prems"(1) cxt] body have "wf_ty \<Sigma> \<tau>' \<and> fv \<tau>' \<subseteq> tyvars (\<Gamma> \<otimes> \<Delta>)"
      by blast
    with tyvars_add[of \<Gamma> \<Delta>] \<Delta> show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" unfolding \<tau> by (auto simp: wf_base_type)
  qed
next
  case (17 \<Sigma> \<Gamma> p e)
  from "17.IH"[OF "17.prems"] show ?case by simp
next
  case (18 \<Sigma> \<Gamma> e es)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume callee: "callee \<Sigma> \<Gamma> e es = Ok \<tau>"
    show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
    proof (cases "scheme_of_name \<Gamma> (node e)")
      case None
      with "18.IH"(1)[OF None "18.prems"] callee show ?thesis by (simp add: callee.simps)
    next
      case (Some \<pi>)
      then obtain \<alpha>s \<sigma>\<^sub>0 where \<pi>: "\<pi> = TyScheme \<alpha>s \<sigma>\<^sub>0" by (cases \<pi>)
      from scheme_of_name_wf[OF "18.prems"(2) Some[unfolded \<pi>]] obtain \<sigma>s \<sigma>
        where \<sigma>\<^sub>0: "\<sigma>\<^sub>0 = TyCallable \<sigma>s \<sigma>" and wf: "wf_ty \<Sigma> (TyCallable \<sigma>s \<sigma>)"
        and fv: "fv (TyCallable \<sigma>s \<sigma>) - set \<alpha>s \<subseteq> tyvars \<Gamma>"
        by auto
      from Some \<pi> \<sigma>\<^sub>0 callee obtain \<tau>s
        where \<tau>s: "inferred_type_args \<Sigma> \<alpha>s \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
        and \<tau>: "\<tau> = TyCallable (map (subst \<tau>s \<alpha>s) \<sigma>s) (subst \<tau>s \<alpha>s \<sigma>)"
        by (auto simp: callee.simps bind_sum_Ok)
      have "wf_ty \<Sigma> \<tau>' \<and> fv \<tau>' \<subseteq> tyvars \<Gamma>" if "Ok \<tau>' \<in> set (map (synth_expr_at \<Sigma> \<Gamma>) es)" for \<tau>'
      proof -
        from that obtain e'' where "e'' \<in> set es" and "synth_expr_at \<Sigma> \<Gamma> e'' = Ok \<tau>'" by auto
        with "18.IH"(2)[OF Some[unfolded \<pi> \<sigma>\<^sub>0] refl refl this(1) "18.prems"] show ?thesis by blast
      qed
      from inferred_type_args_wf[OF "18.prems"(1) \<tau>s] this
      have \<tau>s': "\<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>' \<and> fv \<tau>' \<subseteq> tyvars \<Gamma>" by blast
      have len: "length \<tau>s = length \<alpha>s" using \<tau>s by (rule inferred_type_args_length)
      have step: "wf_ty \<Sigma> (subst \<tau>s \<alpha>s \<rho>) \<and> fv (subst \<tau>s \<alpha>s \<rho>) \<subseteq> tyvars \<Gamma>"
        if "wf_ty \<Sigma> \<rho>" and "fv \<rho> - set \<alpha>s \<subseteq> tyvars \<Gamma>" for \<rho>
        using wf_ty_subst[OF that(1)] fv_subst_minus[OF len, of \<rho>] \<tau>s' that(2) by blast
      from step[of \<sigma>] wf fv have res: "wf_ty \<Sigma> (subst \<tau>s \<alpha>s \<sigma>) \<and> fv (subst \<tau>s \<alpha>s \<sigma>) \<subseteq> tyvars \<Gamma>" by auto
      have args: "wf_ty \<Sigma> (subst \<tau>s \<alpha>s \<rho>) \<and> fv (subst \<tau>s \<alpha>s \<rho>) \<subseteq> tyvars \<Gamma>" if "\<rho> \<in> set \<sigma>s" for \<rho>
        using step[of \<rho>] wf fv that by auto
      show ?thesis unfolding \<tau> using res args by (auto simp: UN_subset_iff)
    qed
  qed
next
  case (19 \<Sigma> \<Gamma> e \<sigma> \<sigma>' kws es)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    assume "synth_call \<Sigma> \<Gamma> e (TyUnion \<sigma> \<sigma>') kws es = Ok \<tau>"
    then obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where "synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau>\<^sub>1" and "synth_call \<Sigma> \<Gamma> e \<sigma>' kws es = Ok \<tau>\<^sub>2"
      and \<tau>: "\<tau> = \<tau>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>2"
      by (auto simp: bind_sum_Ok)
    with "19.IH"(1) "19.IH"(2)[OF this(1)] "19.prems" show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv (TyUnion \<sigma> \<sigma>')"
      unfolding \<tau> by (auto intro: wf_join dest!: fv_join_elem)
  qed
next
  case (20 \<Sigma> \<Gamma> e \<sigma>s \<tau> kws es)
  then show ?case by (auto simp: bind_sum_Ok ensure_def split: if_splits)
next
  case (22 \<Sigma> \<Gamma> es)
  show ?case
  proof (intro allI impI)
    fix \<tau>
    let ?\<sigma>s = "map (synth_expr_at \<Sigma> \<Gamma>) es"
    let ?\<rho>s = "map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s)"
    assume "elements_join \<Sigma> \<Gamma> es = Ok \<tau>"
    then have \<tau>: "\<tau> = joins \<Sigma> ?\<rho>s" by (auto simp: elements_join.simps Let_def bind_sum_Ok split: if_splits)
    have elems: "wf_ty \<Sigma> \<rho> \<and> fv \<rho> \<subseteq> tyvars \<Gamma>" if "\<rho> \<in> set ?\<rho>s" for \<rho>
    proof -
      from that obtain e'' where e: "e'' \<in> set es" and nl: "\<not> isl (synth_expr_at \<Sigma> \<Gamma> e'')"
        and \<rho>: "\<rho> = base_type (projr (synth_expr_at \<Sigma> \<Gamma> e''))"
        by auto
      from nl obtain \<sigma> where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e'' = Ok \<sigma>" by (cases "synth_expr_at \<Sigma> \<Gamma> e''") auto
      from "22.IH"(1)[OF e "22.prems"] \<sigma> have "wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> tyvars \<Gamma>" by blast
      then show ?thesis unfolding \<rho> \<sigma> by (simp add: wf_base_type)
    qed
    have wf: "\<forall>\<rho> \<in> set ?\<rho>s. wf_ty \<Sigma> \<rho>" using elems by blast
    have fv: "\<Union> (fv ` set ?\<rho>s) \<subseteq> tyvars \<Gamma>" unfolding UN_subset_iff using elems by blast
    from wf_joins[OF wf] subset_trans[OF fv_joins fv] show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
      unfolding \<tau> by blast
  qed
next
  case (35 \<Sigma> \<Gamma>)
  then show ?case by (auto simp: tyvars_def)
next
  case (36 \<Sigma> \<Gamma> p e gs)
  then show ?case by (auto simp: bind_sum_Ok)
next
  case (37 \<Sigma> \<Gamma> p x e gs)
  show ?case
  proof (intro allI impI)
    fix \<Delta>
    assume "quals \<Sigma> \<Gamma> (At p (Generator x e) # gs) = Ok \<Delta>"
    then obtain \<tau> \<Delta>' where gen: "by_rule RuleQualGenerator (do {
          \<sigma> \<leftarrow> synth_expr_at \<Sigma> \<Gamma> e;
          \<tau> \<leftarrow> or_else (Located (pos_of e) (NotIterable \<sigma>)) (elem_type \<Sigma> \<sigma>);
          ensure (x \<notin> captures gs) (Located p (CapturedGeneratorVariable x));
          Ok \<tau>
        }) = Ok \<tau>"
      and quals: "quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>'" and \<Delta>: "\<Delta> = fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>'"
      by (auto simp: bind_sum_Ok)
    from gen obtain \<sigma> where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and elem: "elem_type \<Sigma> \<sigma> = Some \<tau>"
      by (auto simp: bind_sum_Ok or_else_def ensure_def split: option.splits if_splits)
    from "37.IH"(1)[OF "37.prems"] \<sigma> have "wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> tyvars \<Gamma>" by blast
    with wf_elem_type[OF _ elem] elem_type_fv[OF elem] have \<tau>: "wf_ty \<Sigma> \<tau>" "fv \<tau> \<subseteq> tyvars \<Gamma>" by auto
    let ?\<Gamma>' = "\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty"
    have cxt: "wf_cxt \<Sigma> ?\<Gamma>'" using "37.prems"(2) \<tau>(1) by (auto intro: wf_cxt_add wf_cxt_upd)
    have tyvars: "tyvars ?\<Gamma>' \<subseteq> tyvars \<Gamma>"
      using tyvars_add[of \<Gamma> "fmupd x (Ty \<tau>) fmempty"] tyvars_single[of "Ty \<tau>" x, simplified] \<tau>(2) by blast
    from "37.IH"(2)[OF gen "37.prems"(1) cxt] quals have \<Delta>': "wf_cxt \<Sigma> \<Delta>' \<and> tyvars \<Delta>' \<subseteq> tyvars ?\<Gamma>'" by blast
    have "wf_cxt \<Sigma> \<Delta>" unfolding \<Delta> by (intro wf_cxt_add wf_cxt_upd wf_cxt_empty) (simp_all add: \<tau>(1) \<Delta>')
    moreover have "tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
      unfolding \<Delta>
      using tyvars_add[of "fmupd x (Ty \<tau>) fmempty" \<Delta>'] tyvars_single[of "Ty \<tau>" x, simplified] \<tau>(2) \<Delta>' tyvars
      by blast
    ultimately show "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>" ..
  qed
qed (auto simp: bind_sum_Ok)


subsection \<open>Patterns\<close>

lemma disjuncts_wf: "\<lbrakk> wf_ty \<Sigma> \<tau> ; \<sigma> \<in> set (disjuncts \<tau>) \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> fv \<tau>"
  by (induction \<tau> rule: disjuncts.induct) auto

lemma has_values_union: "has_values \<Sigma> k (TyUnion \<sigma> \<tau>) \<longleftrightarrow> has_values \<Sigma> k \<sigma> \<or> has_values \<Sigma> k \<tau>"
  by (cases k) simp_all

lemma those_sum_map_Ok_id [simp]: "those_sum (map Ok xs) = Ok xs"
  by (induction xs) simp_all

(* Success of a sequence of results, the sequences of a prefix and a suffix succeed *)
lemma those_sum_append:
  assumes "those_sum (xs @ ys) = Ok zs"
  shows "\<exists>zs'. those_sum xs = Ok zs'" and "\<exists>zs'. those_sum ys = Ok zs'"
  using those_sum_eq[OF assms] by (auto simp: append_eq_map_conv)

(* Bindings at the disjuncts of two types, bindings at the disjuncts of each *)
lemma bindings_at_append:
  "bindings_at \<Sigma> \<Gamma> p (ms @ ms') = Ok \<Delta>
  \<Longrightarrow> (\<exists>\<Delta>'. bindings_at \<Sigma> \<Gamma> p ms = Ok \<Delta>') \<and> (\<exists>\<Delta>'. bindings_at \<Sigma> \<Gamma> p ms' = Ok \<Delta>')"
  unfolding bindings_at_def bind_sum_Ok map_append by (blast dest: those_sum_append)

(* Pattern checked against a union, checked against each side *)
lemma check_pat_union:
  "\<lbrakk> check_pat \<Sigma> \<Gamma> p \<tau> = Ok \<Delta> ; \<tau> = TyUnion \<sigma> \<sigma>' \<rbrakk>
  \<Longrightarrow> (\<exists>\<Delta>'. check_pat \<Sigma> \<Gamma> p \<sigma> = Ok \<Delta>') \<and> (\<exists>\<Delta>'. check_pat \<Sigma> \<Gamma> p \<sigma>' = Ok \<Delta>')"
  "\<lbrakk> check_pat_at \<Sigma> \<Gamma> p' \<tau>' = Ok \<Delta>' ; \<tau>' = TyUnion \<sigma> \<sigma>' \<rbrakk>
  \<Longrightarrow> (\<exists>\<Delta>''. check_pat_at \<Sigma> \<Gamma> p' \<sigma> = Ok \<Delta>'') \<and> (\<exists>\<Delta>''. check_pat_at \<Sigma> \<Gamma> p' \<sigma>' = Ok \<Delta>'')"
proof (induction \<Sigma> \<Gamma> p \<tau> and \<Sigma> \<Gamma> p' \<tau>' arbitrary: \<Delta> \<sigma> \<sigma>' and \<Delta>' \<sigma> \<sigma>' rule: check_pat_check_pat_at.induct)
  case (3 \<Sigma> \<Gamma> p x \<tau>)
  from "3.prems" obtain \<Delta>\<^sub>p where "check_unbound \<Gamma> x = Ok ()" and "check_pat_at \<Sigma> \<Gamma> p \<tau> = Ok \<Delta>\<^sub>p"
    by (auto simp: bind_sum_Ok)
  with "3.IH"[OF this "3.prems"(2)] show ?case by (auto simp: bind_sum_Ok)
next
  case (5 \<Sigma> \<Gamma> ps \<tau>)
  then show ?case
    by (auto simp: bind_sum_Ok ensure_def has_values_union dest!: bindings_at_append split: if_splits)
next
  case (6 \<Sigma> \<Gamma> ps \<tau>)
  then show ?case
    by (auto simp: bind_sum_Ok ensure_def has_values_union dest!: bindings_at_append split: if_splits)
next
  case (7 \<Sigma> \<Gamma> kps \<tau>)
  then show ?case by (auto dest!: bindings_at_append)
next
  case (8 \<Sigma> \<Gamma> q ps kps \<tau>)
  then show ?case by (auto simp: bind_sum_Ok dest!: bindings_at_append)
qed (auto simp: bind_sum_Ok)

lemma check_pat_at_node:
  "check_pat_at \<Sigma> \<Gamma> p \<tau> = Ok \<Delta> \<Longrightarrow> check_pat \<Sigma> \<Gamma> (node p) \<tau> = Ok \<Delta>"
  by (cases p) simp

(* Class of a constructor pattern checked against a type, in the class table *)
lemma check_pattern_class_dom:
  "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; check_pattern_class \<Gamma> q = Ok C \<rbrakk> \<Longrightarrow> C |\<in>| fmdom \<Sigma> \<and> pattern_class \<Gamma> q = C"
  by (auto simp: check_pattern_class_def pattern_class_def split: option.splits cxt_entry.splits if_splits
      dest!: resolve_name_wf)

(* Class C instantiated by well-formed \<tau>, as a well-formed type when C is in the class table *)
lemma instance_at_class_wf:
  assumes "wf_class_table \<Sigma>" and "wf_ty \<Sigma> \<tau>" and "instance_at \<Sigma> C \<tau> = Instance \<tau>s" and "C |\<in>| fmdom \<Sigma>"
  shows "wf_ty \<Sigma> (TyClass C \<tau>s)"
proof -
  have len: "length \<tau>s = length (type_params \<Sigma> C)"
  proof (cases "instance_above \<Sigma> C \<tau>")
    case (Instance \<tau>s')
    with assms(3) have \<tau>s': "\<tau>s' = \<tau>s" by (simp add: instance_at_def)
    show ?thesis
    proof (cases \<tau>)
      case (TyClass D \<sigma>s)
      with Instance have anc: "C \<in> set (ancestors \<Sigma> D)" and "\<tau>s' = instantiated_ancestor \<Sigma> D \<sigma>s C"
        by (auto split: if_splits)
      with instantiated_ancestor_wf[OF assms(1) assms(2)[unfolded TyClass] anc] \<tau>s' show ?thesis by simp
    next
      case (TyPrim p)
      with Instance \<tau>s' show ?thesis by (cases p) (auto split: if_splits)
    qed (use Instance in auto)
  next
    case NoInstance
    with assms(3) have below: "instance_below \<Sigma> C \<tau> = Instance \<tau>s" by (simp add: instance_at_def)
    show ?thesis
    proof (cases \<tau>)
      case (TyClass D \<sigma>s)
      with below obtain \<tau>ss
        where "filter (\<lambda>\<tau>s. list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> C \<tau>s D) \<sigma>s)
                 (instantiation_candidates \<Sigma> C \<sigma>s) = \<tau>s # \<tau>ss"
        by (auto split: if_splits list.splits)
      then have "\<tau>s \<in> set (instantiation_candidates \<Sigma> C \<sigma>s)"
        by (metis filter_is_subset list.set_intros(1) subsetD)
      then show ?thesis
        unfolding instantiation_candidates_def by (auto dest!: in_set_product_lists_length)
    next
      case (TyPrim p)
      with below show ?thesis by (cases p) (auto split: if_splits)
    qed (use below in auto)
  next
    case Undetermined
    with assms(3) show ?thesis by (simp add: instance_at_def)
  qed
  with instance_at_wf[OF assms(1-3)] assms(4) show ?thesis by auto
qed

(* Type matched by a constructor pattern at a type other than a union *)
lemma matched_as_constr_wf:
  assumes "wf_class_table \<Sigma>" and "wf_cxt \<Sigma> \<Gamma>" and "wf_ty \<Sigma> \<tau>" and "check_pat \<Sigma> \<Gamma> (PatConstr q a) \<tau> = Ok \<Delta>"
    and "\<forall>\<sigma> \<sigma>'. \<tau> \<noteq> TyUnion \<sigma> \<sigma>'"
  shows "wf_ty \<Sigma> (matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q a)) \<and> fv (matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q a)) \<subseteq> fv \<tau>"
proof -
  obtain ps kps where a: "a = (ps, kps)" by (cases a)
  from assms(4) obtain C where cls: "check_pattern_class \<Gamma> q = Ok C" by (auto simp: a bind_sum_Ok)
  from check_pattern_class_dom[OF assms(2) cls] have C: "C |\<in>| fmdom \<Sigma>" and pc: "pattern_class \<Gamma> q = C" by auto
  have eq: "matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q a) =
    (case instance_at \<Sigma> C \<tau> of Instance \<sigma>s \<Rightarrow> meet \<Sigma> \<tau> (TyClass C \<sigma>s) | _ \<Rightarrow> TyPrim Never)"
    using assms(5) by (cases \<tau>) (auto simp: Let_def pc)
  show ?thesis
  proof (cases "instance_at \<Sigma> C \<tau>")
    case (Instance \<sigma>s)
    from instance_at_class_wf[OF assms(1, 3) Instance C] have "wf_ty \<Sigma> (TyClass C \<sigma>s)" .
    from wf_meet(1)[OF assms(3) this] have wf: "wf_ty \<Sigma> (meet \<Sigma> \<tau> (TyClass C \<sigma>s))" .
    have "fv (TyClass C \<sigma>s) \<subseteq> fv \<tau>" using instance_at_wf[OF assms(1, 3) Instance] by auto
    with fv_meet[of \<Sigma> \<tau> "TyClass C \<sigma>s"] have fv: "fv (meet \<Sigma> \<tau> (TyClass C \<sigma>s)) \<subseteq> fv \<tau>" by blast
    show ?thesis unfolding eq Instance instances.case by (intro conjI wf fv)
  qed (simp_all add: eq)
qed

(* Type matched by a pattern at a well-formed type it is checked against: well-formed and over the type
   variables of the type *)
lemma matched_as_wf:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> ; check_pat \<Sigma> \<Gamma> p \<tau> = Ok \<Delta> \<rbrakk>
  \<Longrightarrow> wf_ty \<Sigma> (matched_as \<Sigma> \<Gamma> \<tau> p) \<and> fv (matched_as \<Sigma> \<Gamma> \<tau> p) \<subseteq> fv \<tau>"
proof (induction \<Sigma> \<Gamma> \<tau> p arbitrary: \<Delta> rule: matched_as.induct)
  case (1 \<Sigma> \<Gamma> \<sigma> \<tau> p)
  from check_pat_union(1)[OF "1.prems"(4) refl] obtain \<Delta>\<^sub>1 \<Delta>\<^sub>2 where "check_pat \<Sigma> \<Gamma> p \<sigma> = Ok \<Delta>\<^sub>1"
    and "check_pat \<Sigma> \<Gamma> p \<tau> = Ok \<Delta>\<^sub>2"
    by blast
  with "1.IH"(1)[OF "1.prems"(1, 2) _ this(1)] "1.IH"(2)[OF "1.prems"(1, 2) _ this(2)] "1.prems"(3)
  show ?case by (auto intro: wf_join dest!: fv_join_elem)
next
  case (7 \<Sigma> \<Gamma> \<tau>s ps)
  show ?case
  proof (cases "length \<tau>s = length ps")
    case True
    from "7.prems"(4) obtain \<Delta>' where "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<tau>s) = Ok \<Delta>'"
      by (auto simp: bind_sum_Ok bindings_at_def True)
    then obtain \<Delta>s where "those_sum (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<tau>s) = Ok \<Delta>s"
      by (auto simp: pattern_bindings_def bind_sum_Ok)
    then have checked: "\<exists>\<Delta>'. check_pat_at \<Sigma> \<Gamma> p \<sigma> = Ok \<Delta>'" if "(p, \<sigma>) \<in> set (zip ps \<tau>s)" for p \<sigma>
      using that by (auto simp: list_all2_conv_all_nth in_set_conv_nth dest!: those_sum_Ok)
    have "wf_ty \<Sigma> (matched_as \<Sigma> \<Gamma> \<sigma> (node p)) \<and> fv (matched_as \<Sigma> \<Gamma> \<sigma> (node p)) \<subseteq> fv \<sigma>"
      if "(\<sigma>, p) \<in> set (zip \<tau>s ps)" for \<sigma> p
    proof -
      from that have "(p, \<sigma>) \<in> set (zip ps \<tau>s)" by (auto simp: in_set_zip)
      from checked[OF this] obtain \<Delta>' where "check_pat \<Sigma> \<Gamma> (node p) \<sigma> = Ok \<Delta>'" by (auto dest: check_pat_at_node)
      moreover have "wf_ty \<Sigma> \<sigma>" using "7.prems"(3) set_zip_leftD[OF that] by auto
      ultimately show ?thesis using "7.IH"[OF True that refl "7.prems"(1, 2)] by blast
    qed
    then have elems: "wf_ty \<Sigma> (matched_as \<Sigma> \<Gamma> a (node b))
        \<and> fv (matched_as \<Sigma> \<Gamma> a (node b)) \<subseteq> \<Union> (fv ` set \<tau>s)"
      if "(a, b) \<in> set (zip \<tau>s ps)" for a b
      using that set_zip_leftD[OF that] by blast
    have wf: "\<forall>\<rho> \<in> set (map2 (\<lambda>\<tau> p. matched_as \<Sigma> \<Gamma> \<tau> (node p)) \<tau>s ps). wf_ty \<Sigma> \<rho>" using elems by auto
    have fv: "\<Union> (fv ` set (map2 (\<lambda>\<tau> p. matched_as \<Sigma> \<Gamma> \<tau> (node p)) \<tau>s ps)) \<subseteq> \<Union> (fv ` set \<tau>s)"
      unfolding UN_subset_iff using elems by auto
    from wf fv True show ?thesis by simp
  qed (use "7.prems"(3) in simp)
next
  case "10_1"
  from "10_1.prems" show ?case by (rule matched_as_constr_wf) auto
next
  case "10_2"
  from "10_2.prems" show ?case by (rule matched_as_constr_wf) auto
next
  case "10_3"
  from "10_3.prems" show ?case by (rule matched_as_constr_wf) auto
next
  case "10_4"
  from "10_4.prems" show ?case by (rule matched_as_constr_wf) auto
next
  case "10_5"
  from "10_5.prems" show ?case by (rule matched_as_constr_wf) auto
next
  case "10_6"
  from "10_6.prems" show ?case by (rule matched_as_constr_wf) auto
next
  case "10_7"
  from "10_7.prems" show ?case by (rule matched_as_constr_wf) auto
next
  case "10_8"
  from "10_8.prems" show ?case by (rule matched_as_constr_wf) auto
qed (auto simp: bind_sum_Ok intro: wf_meet(1) dest!: fv_meet[THEN subsetD] check_pat_at_node)


(* Type remaining after a pattern at a well-formed type: well-formed and over the type variables of the type *)
lemma remaining_wf:
  "wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_ty \<Sigma> (remaining \<Sigma> \<Gamma> \<tau> p) \<and> fv (remaining \<Sigma> \<Gamma> \<tau> p) \<subseteq> fv \<tau>"
proof (induction \<Sigma> \<Gamma> \<tau> p rule: remaining.induct)
  case (1 \<Sigma> \<Gamma> \<sigma> \<tau> p)
  then show ?case by (auto intro: wf_join dest!: fv_join_elem)
next
  case (8 \<Sigma> \<Gamma> \<tau>s ps)
  show ?case
  proof (cases "length \<tau>s = length ps")
    case True
    let ?\<rho>s = "map2 (\<lambda>\<tau> p. remaining \<Sigma> \<Gamma> \<tau> (node p)) \<tau>s ps"
    have elem: "wf_ty \<Sigma> (?\<rho>s ! i) \<and> fv (?\<rho>s ! i) \<subseteq> fv (\<tau>s ! i)" if "i < length \<tau>s" for i
    proof -
      have "(\<tau>s ! i, ps ! i) \<in> set (zip \<tau>s ps)" using that True by (auto simp: in_set_zip)
      moreover have "wf_ty \<Sigma> (\<tau>s ! i)" using "8.prems" that by auto
      ultimately show ?thesis using "8.IH"[OF True _ refl, of "\<tau>s ! i" "ps ! i"] that True by simp
    qed
    show ?thesis
    proof (cases "filter (\<lambda>i. ?\<rho>s ! i \<noteq> TyPrim Never) [0..<length ?\<rho>s]")
      case Nil
      with True show ?thesis by (simp add: Let_def)
    next
      case (Cons i ks)
      show ?thesis
      proof (cases ks)
        case Nil
        with Cons have f: "filter (\<lambda>i. ?\<rho>s ! i \<noteq> TyPrim Never) [0..<length ?\<rho>s] = [i]" by simp
        then have "i \<in> set (filter (\<lambda>i. ?\<rho>s ! i \<noteq> TyPrim Never) [0..<length ?\<rho>s])" by simp
        then have i: "i < length \<tau>s" using True by simp
        have r: "remaining \<Sigma> \<Gamma> (TyTuple \<tau>s) (PatTuple ps) = TyTuple (\<tau>s[i := ?\<rho>s ! i])"
          using True f by (simp add: Let_def)
        have sub: "set (\<tau>s[i := ?\<rho>s ! i]) \<subseteq> insert (?\<rho>s ! i) (set \<tau>s)" by (rule set_update_subset_insert)
        have fv\<rho>: "fv (?\<rho>s ! i) \<subseteq> fv (TyTuple \<tau>s)" using elem[OF i] nth_mem[OF i] by auto
        have "wf_ty \<Sigma> \<rho> \<and> fv \<rho> \<subseteq> fv (TyTuple \<tau>s)" if "\<rho> \<in> set (\<tau>s[i := ?\<rho>s ! i])" for \<rho>
        proof -
          from that sub consider "\<rho> = ?\<rho>s ! i" | "\<rho> \<in> set \<tau>s" by auto
          then show ?thesis using elem[OF i] fv\<rho> "8.prems" by cases auto
        qed
        then show ?thesis unfolding r by (auto simp: UN_subset_iff)
      next
        case (Cons j js)
        with \<open>filter _ _ = i # ks\<close> True "8.prems" show ?thesis by (simp add: Let_def)
      qed
    qed
  qed (use "8.prems" in simp)
qed (auto simp: Let_def split: instances.splits if_splits)

subsection \<open>Pattern bindings\<close>

lemma fold_fmadd_lookup:
  "fmlookup (fold (\<otimes>) \<Delta>s \<Delta>) x = Some \<sigma> \<Longrightarrow> fmlookup \<Delta> x = Some \<sigma> \<or> (\<exists>\<Delta>' \<in> set \<Delta>s. fmlookup \<Delta>' x = Some \<sigma>)"
proof (induction \<Delta>s arbitrary: \<Delta>)
  case (Cons a \<Delta>s)
  from Cons.IH[OF Cons.prems[simplified]] show ?case by (auto split: if_splits)
qed simp

lemma fmdom'_fold_fmadd: "fmdom' (fold (\<otimes>) \<Delta>s \<Delta>) = fmdom' \<Delta> \<union> \<Union> (fmdom' ` set \<Delta>s)"
  by (induction \<Delta>s arbitrary: \<Delta>) auto

lemma map2_replicate: "map2 f xs (replicate (length xs) y) = map (\<lambda>x. f x y) xs"
  by (induction xs) simp_all

(* Bindings of sub-patterns ps checked against types \<sigma>s: the domain the variables of ps, and each type bound
   well-formed and over V when the bindings of each sub-pattern are *)
lemma pattern_bindings_wf:
  assumes "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) = Ok \<Delta>" and "length ps = length \<sigma>s"
    and sub: "\<And>p \<sigma> \<Delta>'. \<lbrakk> (p, \<sigma>) \<in> set (zip ps \<sigma>s) ; check_pat_at \<Sigma> \<Gamma> p \<sigma> = Ok \<Delta>' \<rbrakk>
      \<Longrightarrow> fmdom' \<Delta>' = binds (node p) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> V)"
  shows "fmdom' \<Delta> = \<Union> ((binds \<circ> node) ` set ps) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta> x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> V)"
proof -
  from assms(1) obtain \<Delta>s where \<Delta>s: "those_sum (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) = Ok \<Delta>s"
    and \<Delta>: "\<Delta> = fold (\<otimes>) \<Delta>s fmempty"
    by (auto simp: pattern_bindings_def bind_sum_Ok)
  from those_sum_map_Ok[OF \<Delta>s]
  have rel: "list_all2 (\<lambda>z \<Delta>'. check_pat_at \<Sigma> \<Gamma> (fst z) (snd z) = Ok \<Delta>') (zip ps \<sigma>s) \<Delta>s"
    by (simp add: case_prod_beta)
  have each: "\<exists>p \<sigma>. (p, \<sigma>) \<in> set (zip ps \<sigma>s) \<and> check_pat_at \<Sigma> \<Gamma> p \<sigma> = Ok \<Delta>'" if "\<Delta>' \<in> set \<Delta>s" for \<Delta>'
  proof -
    from that obtain i where i: "i < length \<Delta>s" and \<Delta>': "\<Delta>' = \<Delta>s ! i" by (auto simp: in_set_conv_nth)
    with rel assms(2) have "check_pat_at \<Sigma> \<Gamma> (ps ! i) (\<sigma>s ! i) = Ok \<Delta>'" and "(ps ! i, \<sigma>s ! i) \<in> set (zip ps \<sigma>s)"
      by (auto simp: list_all2_conv_all_nth in_set_zip)
    then show ?thesis by blast
  qed
  have doms: "fmdom' \<Delta>' = binds (node p)" if "(p, \<sigma>) \<in> set (zip ps \<sigma>s)" and "check_pat_at \<Sigma> \<Gamma> p \<sigma> = Ok \<Delta>'"
    for p \<sigma> \<Delta>'
    using sub[OF that] by blast
  have "\<Union> (fmdom' ` set \<Delta>s) = \<Union> ((binds \<circ> node) ` set ps)"
  proof
    show "\<Union> (fmdom' ` set \<Delta>s) \<subseteq> \<Union> ((binds \<circ> node) ` set ps)"
      using each doms by (fastforce dest: set_zip_leftD)
    show "\<Union> ((binds \<circ> node) ` set ps) \<subseteq> \<Union> (fmdom' ` set \<Delta>s)"
    proof
      fix x
      assume "x \<in> \<Union> ((binds \<circ> node) ` set ps)"
      then obtain i where i: "i < length ps" and x: "x \<in> binds (node (ps ! i))" by (auto simp: in_set_conv_nth)
      have "(ps ! i, \<sigma>s ! i) \<in> set (zip ps \<sigma>s)" using i assms(2) by (auto simp: in_set_zip)
      moreover have "check_pat_at \<Sigma> \<Gamma> (ps ! i) (\<sigma>s ! i) = Ok (\<Delta>s ! i)" and "\<Delta>s ! i \<in> set \<Delta>s"
        using rel i assms(2) by (auto simp: list_all2_conv_all_nth)
      ultimately show "x \<in> \<Union> (fmdom' ` set \<Delta>s)" using doms x by blast
    qed
  qed
  then have "fmdom' \<Delta> = \<Union> ((binds \<circ> node) ` set ps)" by (simp add: \<Delta> fmdom'_fold_fmadd)
  moreover have "wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> V" if "fmlookup \<Delta> x = Some \<sigma>'" for x \<sigma>'
  proof -
    from fold_fmadd_lookup[OF that[unfolded \<Delta>]] obtain \<Delta>' where "\<Delta>' \<in> set \<Delta>s" and "fmlookup \<Delta>' x = Some \<sigma>'"
      by auto
    with each[OF this(1)] sub show ?thesis by blast
  qed
  ultimately show ?thesis by blast
qed

(* Bindings of a pattern at a type, from the bindings at the disjuncts of the type: domain the variables of
   the pattern, and types bound well-formed and over the type variables of the type when those at each disjunct
   are *)
lemma bindings_at_wf:
  assumes "bindings_at \<Sigma> \<Gamma> p (map f (disjuncts \<tau>)) = Ok \<Delta>"
    and dom: "\<And>\<sigma> \<Delta>'. \<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; f \<sigma> = Some (Ok \<Delta>') \<rbrakk> \<Longrightarrow> fmdom' \<Delta>' = binds p"
    and wf: "\<And>\<sigma> \<Delta>' x \<sigma>'. \<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; f \<sigma> = Some (Ok \<Delta>') ; fmlookup \<Delta>' x = Some \<sigma>' \<rbrakk>
      \<Longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> fv \<tau>"
  shows "fmdom' \<Delta> = binds p \<and> (\<forall>x \<sigma>. fmlookup \<Delta> x = Some \<sigma> \<longrightarrow> wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> fv \<tau>)"
proof -
  let ?g = "\<lambda>m. case m of
                  Some m' \<Rightarrow> m'
                | None \<Rightarrow> do {
                    all_sum (map (check_unbound \<Gamma>) (sorted_list_of_set (binds p)));
                    Ok (fmconst (binds p) (TyPrim Never))
                  }"
  from assms(1) obtain \<Delta>s where \<Delta>s: "those_sum (map ?g (map f (disjuncts \<tau>))) = Ok \<Delta>s"
    and \<Delta>: "\<Delta> = fmmap_keys (\<lambda>x _. joins \<Sigma> (map (\<lambda>\<Delta>'. the (fmlookup \<Delta>' x)) \<Delta>s)) (hd \<Delta>s)"
    unfolding bindings_at_def bind_sum_Ok by auto
  have each: "fmdom' \<Delta>' = binds p \<and> (\<forall>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> fv \<tau>)"
    if "\<Delta>' \<in> set \<Delta>s" for \<Delta>'
  proof -
    from those_sum_map_Ok_elem[OF \<Delta>s that] obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and g: "?g (f \<sigma>) = Ok \<Delta>'"
      by auto
    show ?thesis
    proof (cases "f \<sigma>")
      case None
      with g have "\<Delta>' = fmconst (binds p) (TyPrim Never)" by (auto simp: bind_sum_Ok)
      then show ?thesis by (auto simp: fmlookup_dom'_iff fmlookup_fmconst[OF finite_binds_pat] split: if_splits)
    next
      case (Some m)
      with g have "f \<sigma> = Some (Ok \<Delta>')" by simp
      with dom[OF \<sigma> this] wf[OF \<sigma> this] show ?thesis by blast
    qed
  qed
  have "\<Delta>s \<noteq> []" using those_sum_map_Ok[OF \<Delta>s] disjuncts_nonempty[of \<tau>] by (auto dest: list_all2_lengthD)
  then have hd: "hd \<Delta>s \<in> set \<Delta>s" by simp
  have dom: "fmdom' \<Delta> = binds p" using each[OF hd] by (simp add: \<Delta> fmdom'_alt_def)
  moreover have "wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> fv \<tau>" if look: "fmlookup \<Delta> x = Some \<sigma>" for x \<sigma>
  proof -
    let ?\<rho>s = "map (\<lambda>\<Delta>'. the (fmlookup \<Delta>' x)) \<Delta>s"
    from look have x: "x \<in> fmdom' (hd \<Delta>s)" and \<sigma>: "\<sigma> = joins \<Sigma> ?\<rho>s"
      by (auto simp: \<Delta> fmlookup_fmmap_keys fmlookup_dom'_iff)
    have elems: "wf_ty \<Sigma> \<rho> \<and> fv \<rho> \<subseteq> fv \<tau>" if "\<rho> \<in> set ?\<rho>s" for \<rho>
    proof -
      from that obtain \<Delta>' where \<Delta>': "\<Delta>' \<in> set \<Delta>s" and \<rho>: "\<rho> = the (fmlookup \<Delta>' x)" by auto
      from each[OF \<Delta>'] each[OF hd] x have "x \<in> fmdom' \<Delta>'" by simp
      then obtain \<sigma>' where "fmlookup \<Delta>' x = Some \<sigma>'" by (auto simp: fmlookup_dom'_iff)
      with each[OF \<Delta>'] \<rho> show ?thesis by simp
    qed
    have wf: "\<forall>\<rho> \<in> set ?\<rho>s. wf_ty \<Sigma> \<rho>" using elems by blast
    have fv: "\<Union> (fv ` set ?\<rho>s) \<subseteq> fv \<tau>" unfolding UN_subset_iff using elems by blast
    from wf_joins[OF wf] subset_trans[OF fv_joins fv] show ?thesis unfolding \<sigma> by blast
  qed
  ultimately show ?thesis by blast
qed


lemma length_filter_eq_one: "\<lbrakk> distinct xs ; y \<in> set xs \<rbrakk> \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) = 1"
proof -
  assume "distinct xs" and "y \<in> set xs"
  then have "{x. x = y} \<inter> set xs = {y}" by auto
  with distinct_length_filter[OF \<open>distinct xs\<close>, of "\<lambda>x. x = y"] show ?thesis by simp
qed

(* Sub-patterns of a constructor pattern supplying the fields after the positional ones by keyword: one for each
   such field, and the keyword patterns among them *)
lemma field_patterns_cover:
  assumes "distinct xs" and "n + length kps = length xs" and "set (map fst kps) = set (drop n xs)"
  shows "length (concat (map (\<lambda>x. concat (map (\<lambda>(y, p). if y = x then [p] else []) kps)) (drop n xs)))
         = length kps"
    and "set (concat (map (\<lambda>x. concat (map (\<lambda>(y, p). if y = x then [p] else []) kps)) (drop n xs)))
         = set (map snd kps)"
proof -
  let ?g = "\<lambda>x. concat (map (\<lambda>(y, p). if y = x then [p] else []) kps)"
  have dist': "distinct (drop n xs)" using assms(1) by simp
  have "card (set (map fst kps)) = length (map fst kps)"
    using distinct_card[OF dist'] assms(2, 3) by simp
  then have dist: "distinct (map fst kps)" by (rule card_distinct)
  have g1: "length (?g x) = 1" if "x \<in> set (drop n xs)" for x
  proof -
    have "length (?g x) = length (filter (\<lambda>y. y = x) (map fst kps))" by (induction kps) auto
    with length_filter_eq_one[OF dist that[folded assms(3)]] show ?thesis by simp
  qed
  have "map (length \<circ> ?g) (drop n xs) = map (\<lambda>_. 1) (drop n xs)" by (rule map_cong) (auto simp: g1)
  then show "length (concat (map ?g (drop n xs))) = length kps"
    using assms(2) by (simp add: length_concat map_replicate_const sum_list_replicate)
  show "set (concat (map ?g (drop n xs))) = set (map snd kps)"
  proof
    show "set (concat (map ?g (drop n xs))) \<subseteq> set (map snd kps)" by (force split: if_splits)
    show "set (map snd kps) \<subseteq> set (concat (map ?g (drop n xs)))"
    proof
      fix p
      assume "p \<in> set (map snd kps)"
      then obtain y where yp: "(y, p) \<in> set kps" by auto
      then have "y \<in> set (drop n xs)" using assms(3) by force
      with yp show "p \<in> set (concat (map ?g (drop n xs)))" by force
    qed
  qed
qed

lemma length_field_types: "length (field_types \<Sigma> C \<sigma>s) = length (field_names \<Sigma> C)"
  by (cases "fields \<Sigma> C") (simp add: field_types_def field_names_def)

(* Bindings of a pattern checked against a well-formed type: the variables of the pattern, at well-formed types
   over the type variables of the type *)
lemma check_pat_wf:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> ; check_pat \<Sigma> \<Gamma> p \<tau> = Ok \<Delta> \<rbrakk>
  \<Longrightarrow> fmdom' \<Delta> = binds p \<and> (\<forall>x \<sigma>. fmlookup \<Delta> x = Some \<sigma> \<longrightarrow> wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> fv \<tau>)"
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau>' ; check_pat_at \<Sigma> \<Gamma> p' \<tau>' = Ok \<Delta>' \<rbrakk>
  \<Longrightarrow> fmdom' \<Delta>' = binds (node p') \<and> (\<forall>x \<sigma>. fmlookup \<Delta>' x = Some \<sigma> \<longrightarrow> wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> fv \<tau>')"
proof (induction \<Sigma> \<Gamma> p \<tau> and \<Sigma> \<Gamma> p' \<tau>' arbitrary: \<Delta> and \<Delta>' rule: check_pat_check_pat_at.induct)
  case (2 \<Sigma> \<Gamma> x \<tau>)
  then show ?case by (auto simp: bind_sum_Ok split: if_splits)
next
  case (3 \<Sigma> \<Gamma> p x \<tau>)
  from "3.prems"(4) obtain \<Delta>\<^sub>p where unb: "check_unbound \<Gamma> x = Ok ()" and p: "check_pat_at \<Sigma> \<Gamma> p \<tau> = Ok \<Delta>\<^sub>p"
    and \<Delta>: "\<Delta> = \<Delta>\<^sub>p \<otimes> fmupd x (matched_as \<Sigma> \<Gamma> \<tau> (node p)) fmempty"
    by (auto simp: bind_sum_Ok)
  from matched_as_wf[OF "3.prems"(1-3) check_pat_at_node[OF p]] "3.IH"[OF unb "3.prems"(1-3) p] show ?case
    by (auto simp: \<Delta> split: if_splits)
next
  case (5 \<Sigma> \<Gamma> ps \<tau>)
  let ?f = "\<lambda>\<sigma>. case \<sigma> of
              TyTuple \<sigma>s \<Rightarrow>
                if length \<sigma>s = length ps then Some (pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s))
                else None
            | _ \<Rightarrow> None"
  from "5.prems"(4) obtain u where ens: "by_rule RuleCheckTupleNone (do {
      ensure (\<not> has_values \<Sigma> ListKind \<tau>) (SequenceKindMismatch TupleKind \<tau> ListKind);
      ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch TupleKind \<tau> RangeKind)
    }) = Ok u"
    and b: "bindings_at \<Sigma> \<Gamma> (PatTuple ps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
    by (auto simp: bind_sum_Ok)
  have sub: "fmdom' \<Delta>' = binds (PatTuple ps) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> fv \<tau>)"
    if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')" for \<sigma> \<Delta>'
  proof -
    from f obtain \<sigma>s where \<sigma>s: "\<sigma> = TyTuple \<sigma>s" and len: "length \<sigma>s = length ps"
      and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) = Ok \<Delta>'"
      by (auto split: ty.splits if_splits)
    from disjuncts_wf[OF "5.prems"(3) \<sigma>] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" and fv\<sigma>: "fv \<sigma> \<subseteq> fv \<tau>" by auto
    have "fmdom' \<Delta>'' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>'' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> fv \<tau>)"
      if mem: "(p, \<sigma>') \<in> set (zip ps \<sigma>s)" and chk: "check_pat_at \<Sigma> \<Gamma> p \<sigma>' = Ok \<Delta>''" for p \<sigma>' \<Delta>''
    proof -
      have wf\<sigma>': "wf_ty \<Sigma> \<sigma>'" and fv\<sigma>': "fv \<sigma>' \<subseteq> fv \<sigma>" using wf\<sigma> set_zip_rightD[OF mem] by (auto simp: \<sigma>s)
      from "5.IH"[OF ens \<sigma> \<sigma>s len mem refl "5.prems"(1, 2) wf\<sigma>' chk] fv\<sigma>' fv\<sigma> show ?thesis by blast
    qed
    from pattern_bindings_wf[OF pb len[symmetric] this] show ?thesis by auto
  qed
  from bindings_at_wf[OF b] sub show ?case by blast
next
  case (6 \<Sigma> \<Gamma> ps \<tau>)
  let ?f = "\<lambda>\<sigma>. case \<sigma> of
              TyList \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p. check_pat_at \<Sigma> \<Gamma> p \<sigma>') ps))
            | _ \<Rightarrow> None"
  from "6.prems"(4) obtain u where ens: "by_rule RuleCheckListNone (do {
      ensure (\<not> has_values \<Sigma> TupleKind \<tau>) (SequenceKindMismatch ListKind \<tau> TupleKind);
      ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch ListKind \<tau> RangeKind)
    }) = Ok u"
    and b: "bindings_at \<Sigma> \<Gamma> (PatList ps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
    by (auto simp: bind_sum_Ok)
  have sub: "fmdom' \<Delta>' = binds (PatList ps) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> fv \<tau>)"
    if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')" for \<sigma> \<Delta>'
  proof -
    from f obtain \<sigma>' where \<sigma>': "\<sigma> = TyList \<sigma>'"
      and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps (replicate (length ps) \<sigma>')) = Ok \<Delta>'"
      by (auto simp: map2_replicate split: ty.splits)
    from disjuncts_wf[OF "6.prems"(3) \<sigma>] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>'" and fv\<sigma>: "fv \<sigma>' \<subseteq> fv \<tau>" by (auto simp: \<sigma>')
    have "fmdom' \<Delta>'' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>'' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> fv \<tau>)"
      if mem: "(p, \<sigma>'') \<in> set (zip ps (replicate (length ps) \<sigma>'))" and chk: "check_pat_at \<Sigma> \<Gamma> p \<sigma>'' = Ok \<Delta>''"
      for p \<sigma>'' \<Delta>''
    proof -
      from mem have p: "p \<in> set ps" and "\<sigma>'' = \<sigma>'" by (auto dest: set_zip_leftD set_zip_rightD)
      from "6.IH"[OF ens \<sigma> \<sigma>' p "6.prems"(1, 2) wf\<sigma> chk[unfolded this(2)]] fv\<sigma> this(2) show ?thesis by blast
    qed
    from pattern_bindings_wf[OF pb _ this] show ?thesis by auto
  qed
  from bindings_at_wf[OF b] sub show ?case by blast
next
  case (7 \<Sigma> \<Gamma> kps \<tau>)
  let ?f = "\<lambda>\<sigma>. case \<sigma> of
              TyDict \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p. check_pat_at \<Sigma> \<Gamma> p \<sigma>') (map snd kps)))
            | _ \<Rightarrow> None"
  from "7.prems"(4) have b: "bindings_at \<Sigma> \<Gamma> (PatDict kps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
    by (simp only: check_pat.simps)
  have sub: "fmdom' \<Delta>' = binds (PatDict kps) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> fv \<tau>)"
    if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')" for \<sigma> \<Delta>'
  proof -
    from f obtain \<sigma>' where \<sigma>': "\<sigma> = TyDict \<sigma>'"
      and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) (map snd kps) (replicate (length kps) \<sigma>')) = Ok \<Delta>'"
      by (auto simp: map2_replicate[of _ "map snd kps", simplified] split: ty.splits)
    from disjuncts_wf[OF "7.prems"(3) \<sigma>] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>'" and fv\<sigma>: "fv \<sigma>' \<subseteq> fv \<tau>" by (auto simp: \<sigma>')
    have "fmdom' \<Delta>'' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>'' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> fv \<tau>)"
      if mem: "(p, \<sigma>'') \<in> set (zip (map snd kps) (replicate (length kps) \<sigma>'))"
      and chk: "check_pat_at \<Sigma> \<Gamma> p \<sigma>'' = Ok \<Delta>''" for p \<sigma>'' \<Delta>''
    proof -
      from mem have p: "p \<in> set (map snd kps)" and "\<sigma>'' = \<sigma>'" by (auto dest: set_zip_leftD set_zip_rightD)
      from "7.IH"[OF \<sigma> \<sigma>' p "7.prems"(1, 2) wf\<sigma> chk[unfolded this(2)]] fv\<sigma> this(2) show ?thesis by blast
    qed
    from pattern_bindings_wf[OF pb _ this] show ?thesis by auto
  qed
  from bindings_at_wf[OF b] sub show ?case by blast
next
  case (8 \<Sigma> \<Gamma> q ps kps \<tau>)
  from "8.prems"(4) obtain C where cls: "check_pattern_class \<Gamma> q = Ok C"
    and fm: "check_field_map (PatternArityMismatch (short_name C)) (UnknownFieldInPattern (short_name C))
               (field_names \<Sigma> C) (length ps) (map fst kps) = Ok ()"
    and b: "bindings_at \<Sigma> \<Gamma> (PatConstr q (ps, kps))
              (map (\<lambda>\<sigma>. case instance_at \<Sigma> C \<sigma> of
                          Instance \<sigma>s \<Rightarrow>
                            Some (pattern_bindings
                              (map2 (check_pat_at \<Sigma> \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s)))
                        | NoInstance \<Rightarrow> None
                        | Undetermined \<Rightarrow>
                            Some (Fail (Violates
                              (if instance_above \<Sigma> C \<sigma> = Undetermined then RuleInstanceAbove
                               else RuleInstanceBelow)
                              (PatternClassUndetermined (short_name C) \<sigma>))))
                (disjuncts \<tau>)) = Ok \<Delta>"
    by (auto simp: bind_sum_Ok)
  let ?f = "\<lambda>\<sigma>. case instance_at \<Sigma> C \<sigma> of
              Instance \<sigma>s \<Rightarrow>
                Some (pattern_bindings
                  (map2 (check_pat_at \<Sigma> \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s)))
            | NoInstance \<Rightarrow> None
            | Undetermined \<Rightarrow>
                Some (Fail (Violates
                  (if instance_above \<Sigma> C \<sigma> = Undetermined then RuleInstanceAbove else RuleInstanceBelow)
                  (PatternClassUndetermined (short_name C) \<sigma>)))"
  from check_pattern_class_dom[OF "8.prems"(2) cls] have C: "C |\<in>| fmdom \<Sigma>" by simp
  from fm have len_kps: "length ps + length kps = length (field_names \<Sigma> C)"
    and keys: "set (map fst kps) = set (drop (length ps) (field_names \<Sigma> C))"
    by (auto simp: check_field_map_def split: if_splits)
  from field_patterns_cover[OF wf_class_table_distinct[OF "8.prems"(1) C] len_kps keys]
  have len_fp: "length (field_patterns \<Sigma> C (ps, kps)) = length (field_names \<Sigma> C)"
    and set_fp: "set (field_patterns \<Sigma> C (ps, kps)) = set ps \<union> set (map snd kps)"
    using len_kps by simp_all
  have sub: "fmdom' \<Delta>' = binds (PatConstr q (ps, kps))
      \<and> (\<forall>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> fv \<tau>)"
    if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')" for \<sigma> \<Delta>'
  proof -
    from f obtain \<sigma>s where inst: "instance_at \<Sigma> C \<sigma> = Instance \<sigma>s"
      and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s))
                 = Ok \<Delta>'"
      by (auto split: instances.splits)
    from disjuncts_wf[OF "8.prems"(3) \<sigma>] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" and fv\<sigma>: "fv \<sigma> \<subseteq> fv \<tau>" by auto
    have wfC: "wf_ty \<Sigma> (TyClass C \<sigma>s)" by (rule instance_at_class_wf[OF "8.prems"(1) wf\<sigma> inst C])
    have fv\<sigma>s: "\<Union> (fv ` set \<sigma>s) \<subseteq> fv \<sigma>" using instance_at_wf[OF "8.prems"(1) wf\<sigma> inst] by auto
    have "fmdom' \<Delta>'' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>'' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> fv \<tau>)"
      if mem: "(p, \<sigma>') \<in> set (zip (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s))"
      and chk: "check_pat_at \<Sigma> \<Gamma> p \<sigma>' = Ok \<Delta>''" for p \<sigma>' \<Delta>''
    proof -
      from set_zip_rightD[OF mem] have wf\<sigma>': "wf_ty \<Sigma> \<sigma>'" and fv\<sigma>': "fv \<sigma>' \<subseteq> \<Union> (fv ` set \<sigma>s)"
        using field_types_wf[OF "8.prems"(1) wfC] field_types_fv[OF "8.prems"(1) wfC] by auto
      from "8.IH"[OF cls fm \<sigma> inst mem refl "8.prems"(1, 2) wf\<sigma>' chk] fv\<sigma>' fv\<sigma>s fv\<sigma> show ?thesis by blast
    qed
    from pattern_bindings_wf[OF pb _ this] len_fp length_field_types[of \<Sigma> C \<sigma>s] set_fp show ?thesis
      by auto
  qed
  from bindings_at_wf[OF b] sub show ?case by blast
next
  case (9 \<Sigma> \<Gamma> p q \<tau>)
  then show ?case by simp
qed auto


subsection \<open>Statements\<close>

lemma tyvars_fmempty [simp]: "tyvars fmempty = {}"
  by (rule tyvars_empty) simp

lemma wf_entry_PUScheme: "wf_entry \<Sigma> (PUScheme \<pi> b) = wf_entry \<Sigma> (Scheme \<pi>)"
  by (cases \<pi>) simp_all

lemma wf_entry_var_ty: "\<lbrakk> var_ty \<theta> = Some \<sigma> ; wf_entry \<Sigma> \<theta> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<sigma>"
  by (auto dest!: var_ty_Some)

lemma possibly_unassigned_wf: "\<lbrakk> possibly_unassigned b \<theta> = Some \<theta>' ; wf_entry \<Sigma> \<theta> \<rbrakk> \<Longrightarrow> wf_entry \<Sigma> \<theta>'"
  by (cases "(b, \<theta>)" rule: possibly_unassigned.cases) (auto simp: wf_entry_PUScheme)

(* Merge of well-formed entries, well-formed *)
lemma merge_entry_wf:
  "\<lbrakk> merge_cxt_entry \<Sigma> b e e' = Some \<theta>'' ; \<forall>\<theta> \<in> set_option e. wf_entry \<Sigma> \<theta> ; \<forall>\<theta> \<in> set_option e'. wf_entry \<Sigma> \<theta> \<rbrakk>
  \<Longrightarrow> wf_entry \<Sigma> \<theta>''"
proof (cases e)
  case (Some \<theta>)
  show "\<lbrakk> merge_cxt_entry \<Sigma> b e e' = Some \<theta>'' ; \<forall>\<theta> \<in> set_option e. wf_entry \<Sigma> \<theta> ; \<forall>\<theta> \<in> set_option e'. wf_entry \<Sigma> \<theta> \<rbrakk>
    \<Longrightarrow> wf_entry \<Sigma> \<theta>''"
  proof (cases e')
    case (Some \<theta>')
    assume "merge_cxt_entry \<Sigma> b e e' = Some \<theta>''" and "\<forall>\<theta> \<in> set_option e. wf_entry \<Sigma> \<theta>"
      and "\<forall>\<theta> \<in> set_option e'. wf_entry \<Sigma> \<theta>"
    with \<open>e = Some \<theta>\<close> Some merge_cxt_entry_cases[of \<Sigma> b \<theta> \<theta>' \<theta>''] show ?thesis
      by (auto intro!: wf_join simp: wf_entry_PUScheme dest!: scheme_of_Some var_ty_Some)
  qed (use Some in \<open>auto dest: possibly_unassigned_wf\<close>)
qed (cases e'; auto dest: possibly_unassigned_wf)

lemma merge_wf:
  assumes "merge \<Sigma> X \<Gamma> \<Gamma>' = Ok \<Gamma>''" and "wf_cxt \<Sigma> \<Gamma>" and "wf_cxt \<Sigma> \<Gamma>'"
  shows "wf_cxt \<Sigma> \<Gamma>''"
proof (rule wf_cxt_iff[THEN iffD2], intro allI impI)
  fix x \<theta>''
  assume look: "fmlookup \<Gamma>'' x = Some \<theta>''"
  with merge_dom[OF assms(1)] have "x |\<in>| fmdom (\<Gamma> \<otimes> \<Gamma>')" by (auto simp: fmlookup_dom_iff)
  with look have "merge_cxt_entry \<Sigma> (x \<in> X) (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x) = Some \<theta>''"
    by (simp add: merge_lookup[OF assms(1)])
  then show "wf_entry \<Sigma> \<theta>''"
    by (rule merge_entry_wf) (auto dest: wf_cxt_lookup[OF assms(2)] wf_cxt_lookup[OF assms(3)] split: option.splits)
qed

(* Bindings of a merge of static outcomes, well-formed and over the given type variables when those of each
   outcome are *)
lemma merges_wf:
  assumes "merges \<Sigma> X ms = Ok (Assigns\<^sub>R \<Delta> r)"
    and "\<And>\<Delta>' r'. Ok (Assigns\<^sub>R \<Delta>' r') \<in> set ms \<Longrightarrow> wf_cxt \<Sigma> \<Delta>' \<and> tyvars \<Delta>' \<subseteq> V"
  shows "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> V"
proof
  let ?f = "\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }"
  from assms(1) obtain Rs where Rs: "those_sum ms = Ok Rs"
    and fold: "foldr ?f Rs (Ok Returns\<^sub>R) = Ok (Assigns\<^sub>R \<Delta> r)"
    by (auto simp: merges_def bind_sum_Ok)
  have wf: "wf_cxt \<Sigma> \<Delta>"
    if "foldr ?f Rs (Ok Returns\<^sub>R) = Ok (Assigns\<^sub>R \<Delta> r)" and "\<And>\<Delta>' r'. Assigns\<^sub>R \<Delta>' r' \<in> set Rs \<Longrightarrow> wf_cxt \<Sigma> \<Delta>'"
    for Rs \<Delta> r
    using that
  proof (induction Rs arbitrary: \<Delta> r)
    case (Cons R Rs)
    from Cons.prems(1) obtain R' where R': "foldr ?f Rs (Ok Returns\<^sub>R) = Ok R'"
      and m: "merge_outcome \<Sigma> X R R' = Ok (Assigns\<^sub>R \<Delta> r)"
      by (auto simp: bind_sum_Ok)
    show ?case
    proof (cases R')
      case (Assigns\<^sub>R \<Delta>' r')
      have wf': "wf_cxt \<Sigma> \<Delta>'"
        by (rule Cons.IH[OF R'[unfolded \<open>R' = Assigns\<^sub>R \<Delta>' r'\<close>]]) (meson Cons.prems(2) list.set_intros(2))
      show ?thesis
      proof (cases R)
        case (Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1)
        with m \<open>R' = Assigns\<^sub>R \<Delta>' r'\<close> obtain \<Delta>'' where "merge \<Sigma> X \<Delta>\<^sub>1 \<Delta>' = Ok \<Delta>''" and "\<Delta> = \<Delta>''"
          by (auto simp: bind_sum_Ok)
        with merge_wf[OF this(1)] Cons.prems(2)[of \<Delta>\<^sub>1 r\<^sub>1] wf' Assigns\<^sub>R show ?thesis by simp
      next
        case Returns\<^sub>R
        with m \<open>R' = Assigns\<^sub>R \<Delta>' r'\<close> wf' show ?thesis by simp
      qed
    next
      case Returns\<^sub>R
      with m Cons.prems(2) show ?thesis by (cases R) auto
    qed
  qed simp
  show "wf_cxt \<Sigma> \<Delta>"
  proof (rule wf[OF fold])
    fix \<Delta>' r'
    assume "Assigns\<^sub>R \<Delta>' r' \<in> set Rs"
    then have "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set ms" using those_sum_eq[OF Rs] by simp
    with assms(2) show "wf_cxt \<Sigma> \<Delta>'" by blast
  qed
  show "tyvars \<Delta> \<subseteq> V"
  proof
    fix \<alpha>
    assume "\<alpha> \<in> tyvars \<Delta>"
    from merges_tyvars[OF assms(1) this] obtain \<Delta>' r'
      where "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set ms" and "\<alpha> \<in> tyvars \<Delta>'" .
    with assms(2) show "\<alpha> \<in> V" by blast
  qed
qed

lemma signature_entry_fv: "fv_entry (signature_entry \<pi>) = fv_scheme \<pi> \<and> signature_entry \<pi> \<noteq> TypeVar"
proof (cases \<pi>)
  case (TyScheme \<alpha>s \<tau>)
  then show ?thesis by (cases \<alpha>s) auto
qed

(* Signature of a function definition in a well-formed context: a well-formed entry, over the type variables of
   the context *)
lemma def_signature_wf:
  assumes "wf_cxt \<Sigma> \<Gamma>" and "def_signature \<Sigma> \<Gamma> d = Ok \<pi>"
  shows "wf_entry \<Sigma> (signature_entry \<pi>) \<and> fv_scheme \<pi> \<subseteq> tyvars \<Gamma>"
proof (cases d)
  case (Def f \<alpha>s xps \<psi> s)
  let ?\<Gamma>' = "\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar"
  from assms(2) Def obtain \<sigma>s \<tau> where \<sigma>s: "those_sum (map (resolve_type \<Sigma> ?\<Gamma>' \<circ> snd) xps) = Ok \<sigma>s"
    and \<tau>: "resolve_type \<Sigma> ?\<Gamma>' \<psi> = Ok \<tau>" and \<pi>: "\<pi> = TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>)"
    by (auto simp: Let_def bind_sum_def split: sum.splits option.splits)
  have wf\<Gamma>': "wf_cxt \<Sigma> ?\<Gamma>'" using assms(1) by (intro wf_cxt_add wf_cxt_fmconst) simp_all
  have sub: "\<And>x. x \<in> tyvars ?\<Gamma>' \<Longrightarrow> x \<in> tyvars \<Gamma> \<or> x \<in> set \<alpha>s" using tyvars_add tyvars_fmconst by blast
  have "wf_ty \<Sigma> \<sigma> \<and> fv \<sigma> \<subseteq> tyvars ?\<Gamma>'" if "\<sigma> \<in> set \<sigma>s" for \<sigma>
  proof -
    from those_sum_map_Ok_elem[OF \<sigma>s that] obtain xp where "resolve_type \<Sigma> ?\<Gamma>' (snd xp) = Ok \<sigma>" by auto
    from resolve_type_wf[OF wf\<Gamma>' this] show ?thesis .
  qed
  then have \<sigma>s': "\<And>\<sigma>. \<sigma> \<in> set \<sigma>s \<Longrightarrow> wf_ty \<Sigma> \<sigma>"
    and \<sigma>s'': "\<And>\<sigma> x. \<sigma> \<in> set \<sigma>s \<Longrightarrow> x \<in> fv \<sigma> \<Longrightarrow> x \<in> tyvars \<Gamma> \<or> x \<in> set \<alpha>s"
    using sub by blast+
  from resolve_type_wf[OF wf\<Gamma>' \<tau>] have \<tau>': "wf_ty \<Sigma> \<tau>" and \<tau>'': "\<And>x. x \<in> fv \<tau> \<Longrightarrow> x \<in> tyvars \<Gamma> \<or> x \<in> set \<alpha>s"
    using sub by blast+
  show ?thesis using \<sigma>s' \<sigma>s'' \<tau>' \<tau>'' by (cases \<alpha>s) (auto simp: \<pi>)
qed

(* Entries of mutually recursive definitions in a well-formed context: well-formed, over the type variables of
   the context *)
lemma defs_wf:
  assumes "wf_cxt \<Sigma> \<Gamma>"
    and "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s"
  shows "wf_cxt \<Sigma> (fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s)))
    \<and> tyvars (fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))) \<subseteq> tyvars \<Gamma>"
proof -
  let ?\<Delta> = "fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))"
  have sig: "wf_entry \<Sigma> (signature_entry \<pi>) \<and> fv_scheme \<pi> \<subseteq> tyvars \<Gamma>" if "\<pi> \<in> set \<pi>s" for \<pi>
  proof -
    from those_sum_map_Ok_elem[OF assms(2) that] obtain d where "def_signature \<Sigma> \<Gamma> (node d) = Ok \<pi>" by auto
    from def_signature_wf[OF assms(1) this] show ?thesis .
  qed
  have entry: "\<exists>\<pi> \<in> set \<pi>s. \<theta> = signature_entry \<pi>" if "fmlookup ?\<Delta> x = Some \<theta>" for x \<theta>
    using that by (auto simp: fmlookup_of_list dest!: map_of_SomeD set_zip_rightD)
  have sig': "\<And>\<pi> x. \<pi> \<in> set \<pi>s \<Longrightarrow> x \<in> fv_scheme \<pi> \<Longrightarrow> x \<in> tyvars \<Gamma>" using sig by blast
  show ?thesis
  proof
    show "wf_cxt \<Sigma> ?\<Delta>" by (rule wf_cxt_iff[THEN iffD2]) (auto dest!: entry sig)
    show "tyvars ?\<Delta> \<subseteq> tyvars \<Gamma>"
      by (rule tyvars_bound) (auto dest!: entry dest: sig' simp: signature_entry_fv)
  qed
qed

(* Bindings of the cases of a match at a well-formed scrutinee type: well-formed, over the type variables of the
   type *)
lemma match_cases_wf:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> ; match_cases \<Sigma> \<Gamma> \<tau> L ps = Ok (\<Delta>s, \<tau>', L') ; \<Delta> \<in> set \<Delta>s \<rbrakk>
  \<Longrightarrow> wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> fv \<tau>"
proof (induction ps arbitrary: \<tau> L \<Delta>s)
  case (Cons p ps)
  from Cons.prems(4) obtain \<Delta>\<^sub>p \<Delta>s' L\<^sub>1 where p: "check_pat_at \<Sigma> \<Gamma> p \<tau> = Ok \<Delta>\<^sub>p"
    and \<Delta>s: "\<Delta>s = fmmap Ty \<Delta>\<^sub>p # \<Delta>s'"
    and ps: "match_cases \<Sigma> \<Gamma> (remaining \<Sigma> \<Gamma> \<tau> (node p)) L\<^sub>1 ps = Ok (\<Delta>s', \<tau>', L')"
    by (auto simp: bind_sum_Ok split: prod.splits)
  from Cons.prems(5) \<Delta>s consider (head) "\<Delta> = fmmap Ty \<Delta>\<^sub>p" | (tail) "\<Delta> \<in> set \<Delta>s'" by auto
  then show ?case
  proof cases
    case head
    from check_pat_wf(2)[OF Cons.prems(1-3) p]
    have wf: "\<And>x \<sigma>. fmlookup \<Delta>\<^sub>p x = Some \<sigma> \<Longrightarrow> wf_ty \<Sigma> \<sigma>"
      and fv: "\<And>x \<sigma> y. fmlookup \<Delta>\<^sub>p x = Some \<sigma> \<Longrightarrow> y \<in> fv \<sigma> \<Longrightarrow> y \<in> fv \<tau>" by blast+
    show ?thesis unfolding head
      by (intro conjI wf_cxt_iff[THEN iffD2] tyvars_bound) (auto dest: wf fv split: option.splits)
  next
    case tail
    from remaining_wf[OF Cons.prems(3)] have wf: "wf_ty \<Sigma> (remaining \<Sigma> \<Gamma> \<tau> (node p))"
      and fv: "fv (remaining \<Sigma> \<Gamma> \<tau> (node p)) \<subseteq> fv \<tau>" by auto
    from Cons.IH[OF Cons.prems(1, 2) wf ps tail] fv show ?thesis by (meson subset_trans)
  qed
qed simp

(* Bindings of a statement checked in a well-formed context: well-formed, over the type variables in scope *)
lemma check_stmt_wf:
  "\<lbrakk> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r) ; wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> \<rbrakk>
  \<Longrightarrow> wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
  "\<lbrakk> check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta> r) ; wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> \<rbrakk>
  \<Longrightarrow> wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
  "check_def \<Sigma> \<Gamma> d \<pi> = m \<Longrightarrow> True"
  "check_def_at \<Sigma> \<Gamma> d' \<pi> = m \<Longrightarrow> True"
proof (induction \<Sigma> \<Gamma> \<zeta> s and \<Sigma> \<Gamma> \<zeta> s' and \<Sigma> \<Gamma> d \<pi> and \<Sigma> \<Gamma> d' \<pi> arbitrary: \<Delta> r and \<Delta> r
    rule: check_stmt_check_stmt_at_check_def_check_def_at.induct)
  case (2 \<Sigma> \<Gamma> \<zeta> x \<psi>)
  from "2.prems"(1) obtain \<tau> where \<tau>: "resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau>" and \<Delta>: "\<Delta> = fmupd x (DU \<tau>) fmempty"
    by (auto simp: bind_sum_Ok)
  from resolve_type_wf[OF "2.prems"(3) \<tau>] show ?case by (auto simp: \<Delta> tyvars_single intro: wf_cxt_upd)
next
  case (3 \<Sigma> \<Gamma> \<zeta> x e)
  from "3.prems"(1) obtain \<tau> where look: "fmlookup \<Gamma> x = Some (DU \<tau>)" and \<Delta>: "\<Delta> = fmupd x (Ty \<tau>) fmempty"
    by (auto simp: bind_sum_Ok split: option.splits cxt_entry.splits)
  from wf_cxt_lookup[OF "3.prems"(3) look] tyvars_entry[OF look] show ?case
    by (auto simp: \<Delta> tyvars_single intro: wf_cxt_upd)
next
  case (4 \<Sigma> \<Gamma> \<zeta> x \<psi> e)
  from "4.prems"(1) obtain \<tau> where \<tau>: "resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau>" and \<Delta>: "\<Delta> = fmupd x (Ty \<tau>) fmempty"
    by (auto simp: bind_sum_Ok)
  from resolve_type_wf[OF "4.prems"(3) \<tau>] show ?case by (auto simp: \<Delta> tyvars_single intro: wf_cxt_upd)
next
  case (10 \<Sigma> \<Gamma> \<zeta> e s elifs else')
  from "10.prems"(1) obtain z where e: "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok z"
    and m: "merges \<Sigma> (set (declares (StmtIf e s elifs else')))
              (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok (Assigns\<^sub>R \<Delta> r)"
    unfolding check_stmt_if by (auto simp: bind_sum_Ok)
  show ?case
  proof (rule merges_wf[OF m])
    fix \<Delta>' r'
    assume "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))"
    then consider (s) "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta>' r')"
      | (elif) e' s' z' where "(e', s') \<in> set elifs" and "check_expr_at \<Sigma> \<Gamma> e' (TyPrim bool) = Ok z'"
          and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta>' r')"
      | (else) s' where "else' = Some s'" and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta>' r')"
      | (none) "\<Delta>' = fmempty"
      by (auto simp: Ok_bind_sum split: option.splits)
    then show "wf_cxt \<Sigma> \<Delta>' \<and> tyvars \<Delta>' \<subseteq> tyvars \<Gamma>"
    proof cases
      case s
      from "10.IH"(1)[OF e s "10.prems"(2, 3)] show ?thesis .
    next
      case elif
      from "10.IH"(2)[OF e elif(1) refl elif(2, 3) "10.prems"(2, 3)] show ?thesis .
    next
      case else
      from "10.IH"(3)[OF e else "10.prems"(2, 3)] show ?thesis .
    next
      case none
      then show ?thesis by simp
    qed
  qed
next
  case (11 \<Sigma> \<Gamma> \<zeta> s s')
  from check_seq[OF "11.prems"(1)] obtain \<Delta>\<^sub>1 r\<^sub>1 R\<^sub>2 where s: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1)"
    and s': "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>1) \<zeta> s' = Ok R\<^sub>2" and R: "Assigns\<^sub>R \<Delta> r = Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1 \<otimes> R\<^sub>2"
    by blast
  from R obtain \<Delta>\<^sub>2 r\<^sub>2 where R\<^sub>2: "R\<^sub>2 = Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2" and \<Delta>: "\<Delta> = \<Delta>\<^sub>1 \<otimes> \<Delta>\<^sub>2" by (cases R\<^sub>2) auto
  from "11.IH"(1)[OF s "11.prems"(2, 3)] have wf\<^sub>1: "wf_cxt \<Sigma> \<Delta>\<^sub>1" and tv\<^sub>1: "tyvars \<Delta>\<^sub>1 \<subseteq> tyvars \<Gamma>" by auto
  have "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>1)" using "11.prems"(3) wf\<^sub>1 by (rule wf_cxt_add)
  from "11.IH"(2)[OF s refl s'[unfolded R\<^sub>2] "11.prems"(2) this] tv\<^sub>1 tyvars_add[of \<Gamma> \<Delta>\<^sub>1]
  have wf\<^sub>2: "wf_cxt \<Sigma> \<Delta>\<^sub>2" and tv\<^sub>2: "tyvars \<Delta>\<^sub>2 \<subseteq> tyvars \<Gamma>" by auto
  from wf_cxt_add[OF wf\<^sub>1 wf\<^sub>2] tyvars_add[of \<Delta>\<^sub>1 \<Delta>\<^sub>2] tv\<^sub>1 tv\<^sub>2 show ?case by (auto simp: \<Delta>)
next
  case (12 \<Sigma> \<Gamma> \<zeta> ds)
  from "12.prems"(1) obtain \<pi>s
    where sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s"
    and \<Delta>: "\<Delta> = fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))"
    by (auto simp: bind_sum_Ok Let_def)
  from defs_wf[OF "12.prems"(3) sigs] show ?case by (simp add: \<Delta>)
next
  case (13 \<Sigma> \<Gamma> \<zeta> e bs)
  from "13.prems"(1) obtain \<sigma> \<Delta>s \<tau> L where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
    and mc: "match_cases \<Sigma> \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst bs) = Ok (\<Delta>s, \<tau>, L)"
    and m: "merges \<Sigma> (set (declares (StmtMatch e bs))) (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L) = Ok (Assigns\<^sub>R \<Delta> r)"
    by (rule check_match)
  from synth_wf(2)[OF "13.prems"(2, 3)] \<sigma> have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" and fv\<sigma>: "fv \<sigma> \<subseteq> tyvars \<Gamma>" by auto
  show ?case
  proof (rule merges_wf[OF m])
    fix \<Delta>' r'
    assume mem: "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L)"
    show "wf_cxt \<Sigma> \<Delta>' \<and> tyvars \<Delta>' \<subseteq> tyvars \<Gamma>"
    proof (cases "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set (map2 (\<lambda>\<Delta> (_, s). do {
                    R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) }) \<Delta>s bs)")
      case True
      from Ok_in_set_map2[OF True] obtain \<Delta>\<^sub>p p s R where b: "(\<Delta>\<^sub>p, (p, s)) \<in> set (zip \<Delta>s bs)"
        and R: "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>p) \<zeta> s = Ok R" and \<Delta>': "Assigns\<^sub>R \<Delta>\<^sub>p None \<otimes> R = Assigns\<^sub>R \<Delta>' r'"
        by (auto simp: bind_sum_Ok split: prod.splits)
      from \<Delta>' obtain \<Delta>\<^sub>2 r\<^sub>2 where R\<^sub>2: "R = Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2" and \<Delta>'': "\<Delta>' = \<Delta>\<^sub>p \<otimes> \<Delta>\<^sub>2" by (cases R) auto
      from match_cases_wf[OF "13.prems"(2, 3) wf\<sigma> mc set_zip_leftD[OF b]] fv\<sigma>
      have wf\<^sub>p: "wf_cxt \<Sigma> \<Delta>\<^sub>p" and tv\<^sub>p: "tyvars \<Delta>\<^sub>p \<subseteq> tyvars \<Gamma>" by (blast, meson subset_trans)
      have "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>p)" using "13.prems"(3) wf\<^sub>p by (rule wf_cxt_add)
      from "13.IH"[OF \<sigma> mc refl refl b refl refl R[unfolded R\<^sub>2] "13.prems"(2) this] tv\<^sub>p tyvars_add[of \<Gamma> \<Delta>\<^sub>p]
      have wf\<^sub>2: "wf_cxt \<Sigma> \<Delta>\<^sub>2" and tv\<^sub>2: "tyvars \<Delta>\<^sub>2 \<subseteq> tyvars \<Gamma>" by auto
      from wf_cxt_add[OF wf\<^sub>p wf\<^sub>2] tyvars_add[of \<Delta>\<^sub>p \<Delta>\<^sub>2] tv\<^sub>p tv\<^sub>2 show ?thesis by (auto simp: \<Delta>'')
    next
      case False
      with mem have "\<Delta>' = fmempty" by (auto simp: match_branches_def split: if_splits)
      then show ?thesis by simp
    qed
  qed
next
  case (14 \<Sigma> \<Gamma> \<zeta> p s)
  from "14.prems"(1) obtain r' where "check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r')"
    by (cases "check_stmt \<Sigma> \<Gamma> \<zeta> s") (auto split: static_outcome.splits)
  from "14.IH"[OF this "14.prems"(2, 3)] show ?case .
qed (auto simp: bind_sum_Ok ensure_def Let_def split: option.splits if_splits)

end
