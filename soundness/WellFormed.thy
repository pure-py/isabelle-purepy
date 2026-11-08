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

end
