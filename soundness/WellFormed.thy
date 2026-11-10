(* Well-formedness and type variables of the types produced by operations on types and contexts *)
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
lemma ancestor_args_wf:
  assumes "wf_class_table \<Sigma>" and "wf_ty \<Sigma> (TyClass C \<tau>s)" and "D \<in> set (ancestors \<Sigma> C)"
  shows "wf_ty \<Sigma> (TyClass D (ancestor_args \<Sigma> C \<tau>s D))
    \<and> (\<forall>\<sigma> \<in> set (ancestor_args \<Sigma> C \<tau>s D). fv \<sigma> \<subseteq> \<Union> (fv ` set \<tau>s))"
proof -
  have "map_of (instantiated_ancestors \<Sigma> C \<tau>s) D \<noteq> None"
    using assms(3) by (simp add: map_of_eq_None_iff ancestors_instantiated[of \<Sigma> C \<tau>s])
  then obtain \<sigma>s where "map_of (instantiated_ancestors \<Sigma> C \<tau>s) D = Some \<sigma>s" by blast
  with instantiated_ancestors_wf[OF assms(1, 2) map_of_SomeD[OF this]] show ?thesis
    by (simp add: ancestor_args_def)
qed

subsection \<open>Joins and meets\<close>

lemma join_wf: "\<lbrakk> wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)"
  by (simp add: join_def)

lemma joins_wf: "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_ty \<Sigma> (joins \<Sigma> \<tau>s)"
  by (induction \<tau>s) (simp_all add: joins_def join_wf)

lemma base_type_lit_wf [simp]: "wf_ty \<Sigma> (base_type_lit l)"
  by (cases l) simp_all

lemma base_type_wf: "wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_ty \<Sigma> (base_type \<tau>)"
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

lemma meet_wf:
  "wf_ty \<Sigma> \<sigma> \<Longrightarrow> wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_ty \<Sigma> (meet \<Sigma> \<sigma> \<tau>)"
  "wf_ty \<Sigma> \<sigma>' \<Longrightarrow> wf_ty \<Sigma> \<tau>' \<Longrightarrow> wf_ty \<Sigma> (meet_incomparable \<Sigma> \<sigma>' \<tau>')"
proof (induction \<Sigma> \<sigma> \<tau> and \<Sigma> \<sigma>' \<tau>' rule: meet_meet_incomparable.induct)
  case (4 \<Sigma> \<sigma>s \<sigma> \<tau>s \<tau>)
  show ?case
  proof (cases "length \<sigma>s = length \<tau>s")
    case True
    have "wf_ty \<Sigma> (a \<squnion>\<^bsub>\<Sigma>\<^esub> b)" if "(a, b) \<in> set (zip \<sigma>s \<tau>s)" for a b
      using "4.prems" set_zip_leftD[OF that] set_zip_rightD[OF that] by (auto intro: join_wf)
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
qed (auto split: if_splits intro: join_wf)

subsection \<open>Elements, subscripts and attributes\<close>

lemma elem_type_wf: "\<lbrakk> wf_ty \<Sigma> \<sigma> ; elem_type \<Sigma> \<sigma> = Some \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
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
  then show ?case by (auto intro!: joins_wf base_type_wf)
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
        by (simp add: join_wf)
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
    unfolding \<tau> by (auto intro: join_wf dest!: fv_join_elem)
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
    with "4.prems"(1) show ?thesis by (auto intro!: joins_wf dest!: fv_joins[THEN subsetD])
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
    unfolding \<tau> by (auto intro: join_wf dest!: fv_join_elem)
next
  case (2 \<Sigma> C \<sigma>s x)
  then have "(x, \<tau>) \<in> set (instantiate (fields \<Sigma> C) \<sigma>s)"
    by (auto simp: or_else_def split: option.splits dest: map_of_SomeD)
  with fields_wf[OF "2.prems"(1, 2) this] fields_fv_inst[OF "2.prems"(1, 2) this] show ?case by auto
qed simp_all

subsection \<open>Instances and type arguments\<close>

lemma merge_match_Matched:
  "merge_match m m' = Matched \<gamma> \<Longrightarrow> \<exists>\<gamma>\<^sub>1 \<gamma>\<^sub>2. m = Matched \<gamma>\<^sub>1 \<and> m' = Matched \<gamma>\<^sub>2 \<and> \<gamma> = \<gamma>\<^sub>1 ++\<^sub>f \<gamma>\<^sub>2"
  by (cases m; cases m') auto

(* Types bound by matching a sequence of types against well-formed types, given the property for each of the
   types matched *)
lemma match_args_seq_bound_elems:
  assumes "\<And>\<rho> \<sigma> \<gamma>. \<lbrakk> \<rho> \<in> set \<rho>s ; match_args \<rho> \<sigma> = Matched \<gamma> ; fmlookup \<gamma> \<alpha> = Some \<tau> ; wf_ty \<Sigma> \<sigma> \<rbrakk>
            \<Longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma>"
    and "match_args_seq \<rho>s \<sigma>s = Matched \<gamma>'" and "fmlookup \<gamma>' \<alpha> = Some \<tau>" and "\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>"
  shows "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> \<Union> (fv ` set \<sigma>s)"
  using assms
proof (induction \<rho>s arbitrary: \<sigma>s \<gamma>')
  case Nil
  then show ?case by (cases \<sigma>s) auto
next
  case (Cons \<rho> \<rho>s)
  from Cons.prems(2) obtain \<sigma> \<sigma>s' where \<sigma>s: "\<sigma>s = \<sigma> # \<sigma>s'" by (cases \<sigma>s) auto
  with Cons.prems(2) have "merge_match (match_args \<rho> \<sigma>) (match_args_seq \<rho>s \<sigma>s') = Matched \<gamma>'" by simp
  from merge_match_Matched[OF this] obtain \<gamma>\<^sub>1 \<gamma>\<^sub>2
    where m: "match_args \<rho> \<sigma> = Matched \<gamma>\<^sub>1" "match_args_seq \<rho>s \<sigma>s' = Matched \<gamma>\<^sub>2" and "\<gamma>' = \<gamma>\<^sub>1 ++\<^sub>f \<gamma>\<^sub>2"
    by blast
  with Cons.prems(3) have "fmlookup \<gamma>\<^sub>1 \<alpha> = Some \<tau> \<or> fmlookup \<gamma>\<^sub>2 \<alpha> = Some \<tau>"
    by (auto simp: fmlookup_add split: if_splits option.splits)
  moreover have "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> \<Union> (fv ` set \<sigma>s')" if "fmlookup \<gamma>\<^sub>2 \<alpha> = Some \<tau>"
  proof (rule Cons.IH[OF _ m(2) that])
    fix \<rho>' \<sigma>' \<gamma>
    assume "\<rho>' \<in> set \<rho>s" and "match_args \<rho>' \<sigma>' = Matched \<gamma>" and "fmlookup \<gamma> \<alpha> = Some \<tau>" and "wf_ty \<Sigma> \<sigma>'"
    then show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma>'" by (intro Cons.prems(1)[of \<rho>' \<sigma>' \<gamma>]) simp_all
  next
    from Cons.prems(4) show "\<forall>\<sigma> \<in> set \<sigma>s'. wf_ty \<Sigma> \<sigma>" unfolding \<sigma>s by simp
  qed
  ultimately show ?case using Cons.prems(1)[OF _ m(1)] Cons.prems(4) unfolding \<sigma>s by auto
qed

(* Type bound by matching against a well-formed type: well-formed and over its type variables *)
lemma match_args_bound:
  "\<lbrakk> match_args \<rho> \<sigma> = Matched \<gamma> ; fmlookup \<gamma> \<alpha> = Some \<tau> ; wf_ty \<Sigma> \<sigma> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma>"
proof (induction \<rho> arbitrary: \<sigma> \<gamma>)
  case (TyList \<rho>)
  then show ?case by (cases \<sigma>) (auto split: if_splits)
next
  case (TyDict \<rho>)
  then show ?case by (cases \<sigma>) (auto split: if_splits)
next
  case (TyTuple \<rho>s)
  from TyTuple.prems(1) obtain \<sigma>s where \<sigma>: "\<sigma> = TyTuple \<sigma>s" by (cases \<sigma>) (auto split: if_splits)
  with TyTuple.prems(1) have "match_args_seq \<rho>s \<sigma>s = Matched \<gamma>" by simp
  from match_args_seq_bound_elems[OF TyTuple.IH this TyTuple.prems(2)] TyTuple.prems(3) show ?case
    unfolding \<sigma> by auto
next
  case (TyCallable \<rho>s \<rho>)
  from TyCallable.prems(1) obtain \<sigma>s \<sigma>' where \<sigma>: "\<sigma> = TyCallable \<sigma>s \<sigma>'" by (cases \<sigma>) (auto split: if_splits)
  with TyCallable.prems(1) have seq: "match_args_seq (\<rho> # \<rho>s) (\<sigma>' # \<sigma>s) = Matched \<gamma>" by simp
  have "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> \<Union> (fv ` set (\<sigma>' # \<sigma>s))"
  proof (rule match_args_seq_bound_elems[OF _ seq TyCallable.prems(2)])
    fix \<rho>' \<sigma>'' \<gamma>''
    assume "\<rho>' \<in> set (\<rho> # \<rho>s)" and "match_args \<rho>' \<sigma>'' = Matched \<gamma>''" and "fmlookup \<gamma>'' \<alpha> = Some \<tau>"
      and "wf_ty \<Sigma> \<sigma>''"
    then show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma>''"
      using TyCallable.IH(1)[of \<rho>' \<sigma>'' \<gamma>''] TyCallable.IH(2)[of \<sigma>'' \<gamma>''] by auto
  next
    from TyCallable.prems(3) show "\<forall>\<sigma> \<in> set (\<sigma>' # \<sigma>s). wf_ty \<Sigma> \<sigma>" unfolding \<sigma> by auto
  qed
  with TyCallable.prems(3) show ?case unfolding \<sigma> by auto
next
  case (TyClass C \<rho>s)
  from TyClass.prems(1) obtain \<sigma>s where \<sigma>: "\<sigma> = TyClass C \<sigma>s" by (cases \<sigma>) (auto split: if_splits)
  with TyClass.prems(1) have "match_args_seq \<rho>s \<sigma>s = Matched \<gamma>" by (simp split: if_splits)
  from match_args_seq_bound_elems[OF TyClass.IH this TyClass.prems(2)] TyClass.prems(3) show ?case
    unfolding \<sigma> by auto
qed (auto split: if_splits elim!: match_args.elims)

lemma match_args_seq_bound:
  assumes "match_args_seq \<rho>s \<sigma>s = Matched \<gamma>" and "fmlookup \<gamma> \<alpha> = Some \<tau>" and "\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>"
  shows "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> \<Union> (fv ` set \<sigma>s)"
proof (rule match_args_seq_bound_elems[OF _ assms])
  fix \<rho> \<sigma> \<gamma>
  assume "match_args \<rho> \<sigma> = Matched \<gamma>" and "fmlookup \<gamma> \<alpha> = Some \<tau>" and "wf_ty \<Sigma> \<sigma>"
  then show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> fv \<sigma>" by (rule match_args_bound)
qed

lemma type_args_of_elem:
  "\<lbrakk> type_args_of \<gamma> \<alpha>s = Ok \<tau>s ; \<tau> \<in> set \<tau>s \<rbrakk> \<Longrightarrow> \<exists>\<alpha>. fmlookup \<gamma> \<alpha> = Some \<tau>"
  by (auto simp: type_args_of_def or_else_def dest!: those_sum_map_Ok_elem split: option.splits)

lemma instance_above_wf:
  assumes "wf_class_table \<Sigma>" and "wf_ty \<Sigma> \<tau>" and "instance_above \<Sigma> C \<tau> = Instance \<tau>s"
  shows "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fv \<tau> \<and> wf_ty \<Sigma> \<tau>'"
proof (cases \<tau>)
  case (TyClass D \<sigma>s)
  with assms(3) have anc: "C \<in> set (ancestors \<Sigma> D)" and \<tau>s: "\<tau>s = ancestor_args \<Sigma> D \<sigma>s C"
    by (auto split: if_splits)
  from ancestor_args_wf[OF assms(1) assms(2)[unfolded TyClass] anc] show ?thesis
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
  with assms(2) obtain \<gamma>
    where "match_args_seq (ancestor_args \<Sigma> C (map TyVar (type_params \<Sigma> C)) D) \<sigma>s = Matched \<gamma>"
      and "type_args_of \<gamma> (type_params \<Sigma> C) = Ok \<tau>s"
    by (auto simp: Let_def split: if_splits arg_match.splits sum.splits)
  with assms(1) show ?thesis
    unfolding TyClass by (fastforce dest!: type_args_of_elem dest: match_args_seq_bound)
next
  case (TyPrim p)
  with assms(2) show ?thesis by (cases p) (auto split: if_splits)
qed (use assms(2) in auto)

lemma instance_below_length:
  assumes "instance_below \<Sigma> C \<tau> = Instance \<tau>s"
  shows "length \<tau>s = length (type_params \<Sigma> C)"
  using assms
proof (cases \<tau>)
  case (TyPrim p)
  with assms show ?thesis by (cases p) (auto split: if_splits)
qed (auto simp: Let_def split: if_splits arg_match.splits sum.splits dest: type_args_of_length)

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
      unfolding both(3) by (auto intro: join_wf dest!: fv_join_elem)
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
      unfolding both(3) by (auto intro: join_wf dest!: fv_join_elem)
  qed
qed

(* Induction over the clauses of type argument matching, with one case for a type other than a variable matched
   against a union, one for a class and one for a union matched against a type other than a union *)
lemma type_args_induct[case_names Var UnionRight List Dict Tuple Callable Class UnionLeft Other Seq]:
  assumes "\<And>\<Sigma> \<alpha>s \<alpha> \<tau>. P \<Sigma> \<alpha>s (TyVar \<alpha>) \<tau>"
    and "\<And>\<Sigma> \<alpha>s \<sigma> \<tau> \<tau>'. \<lbrakk> \<forall>\<alpha>. \<sigma> \<noteq> TyVar \<alpha> ; P \<Sigma> \<alpha>s \<sigma> \<tau> ; P \<Sigma> \<alpha>s \<sigma> \<tau>' \<rbrakk> \<Longrightarrow> P \<Sigma> \<alpha>s \<sigma> (TyUnion \<tau> \<tau>')"
    and "\<And>\<Sigma> \<alpha>s \<sigma> \<tau>. P \<Sigma> \<alpha>s \<sigma> \<tau> \<Longrightarrow> P \<Sigma> \<alpha>s (TyList \<sigma>) (TyList \<tau>)"
    and "\<And>\<Sigma> \<alpha>s \<sigma> \<tau>. P \<Sigma> \<alpha>s \<sigma> \<tau> \<Longrightarrow> P \<Sigma> \<alpha>s (TyDict \<sigma>) (TyDict \<tau>)"
    and "\<And>\<Sigma> \<alpha>s \<sigma>s \<tau>s. Q \<Sigma> \<alpha>s \<sigma>s \<tau>s \<Longrightarrow> P \<Sigma> \<alpha>s (TyTuple \<sigma>s) (TyTuple \<tau>s)"
    and "\<And>\<Sigma> \<alpha>s \<sigma>s \<sigma> \<tau>s \<tau>. Q \<Sigma> \<alpha>s (\<sigma> # \<sigma>s) (\<tau> # \<tau>s) \<Longrightarrow> P \<Sigma> \<alpha>s (TyCallable \<sigma>s \<sigma>) (TyCallable \<tau>s \<tau>)"
    and "\<And>\<Sigma> \<alpha>s C \<sigma>s \<tau>. \<lbrakk> \<forall>\<rho> \<rho>'. \<tau> \<noteq> TyUnion \<rho> \<rho>' ; \<And>\<tau>s. instance_at \<Sigma> C \<tau> = Instance \<tau>s \<Longrightarrow> Q \<Sigma> \<alpha>s \<sigma>s \<tau>s \<rbrakk>
          \<Longrightarrow> P \<Sigma> \<alpha>s (TyClass C \<sigma>s) \<tau>"
    and "\<And>\<Sigma> \<alpha>s \<sigma> \<sigma>' \<tau>. \<lbrakk> \<forall>\<rho> \<rho>'. \<tau> \<noteq> TyUnion \<rho> \<rho>'
          ; \<not> (\<Sigma> \<turnstile> \<tau> <: \<sigma> \<and> fv \<sigma> \<inter> set \<alpha>s = {} \<or> \<Sigma> \<turnstile> \<tau> <: \<sigma>' \<and> fv \<sigma>' \<inter> set \<alpha>s = {}) \<Longrightarrow> P \<Sigma> \<alpha>s \<sigma> \<tau>
          ; \<not> (\<Sigma> \<turnstile> \<tau> <: \<sigma> \<and> fv \<sigma> \<inter> set \<alpha>s = {} \<or> \<Sigma> \<turnstile> \<tau> <: \<sigma>' \<and> fv \<sigma>' \<inter> set \<alpha>s = {}) \<Longrightarrow> P \<Sigma> \<alpha>s \<sigma>' \<tau> \<rbrakk>
          \<Longrightarrow> P \<Sigma> \<alpha>s (TyUnion \<sigma> \<sigma>') \<tau>"
    and "\<And>\<Sigma> \<alpha>s \<sigma> \<tau>. type_args \<Sigma> \<alpha>s \<sigma> \<tau> = fmempty \<Longrightarrow> P \<Sigma> \<alpha>s \<sigma> \<tau>"
    and "\<And>\<Sigma> \<alpha>s \<sigma>s \<tau>s. (\<And>\<sigma> \<tau>. (\<sigma>, \<tau>) \<in> set (zip \<sigma>s \<tau>s) \<Longrightarrow> P \<Sigma> \<alpha>s \<sigma> \<tau>) \<Longrightarrow> Q \<Sigma> \<alpha>s \<sigma>s \<tau>s"
  shows "P \<Sigma> \<alpha>s \<sigma> \<tau>" and "Q \<Sigma> \<alpha>s \<sigma>s \<tau>s"
  by (induction \<Sigma> \<alpha>s \<sigma> \<tau> and \<Sigma> \<alpha>s \<sigma>s \<tau>s rule: type_args_type_args_seq.induct) (rule assms; simp)+

(* Type bound to a type variable by matching \<sigma> against well-formed \<tau>: over the type variables of \<tau> and
   well-formed *)
lemma type_args_range:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> \<tau> ; fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha> = Some \<tau>' \<rbrakk>
  \<Longrightarrow> (\<forall>x. x \<in> fv \<tau>' \<longrightarrow> x \<in> fv \<tau>) \<and> wf_ty \<Sigma> \<tau>'"
  "\<lbrakk> wf_class_table \<Sigma> ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> ; fmlookup (type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s) \<alpha> = Some \<tau>' \<rbrakk>
  \<Longrightarrow> (\<forall>x. x \<in> fv \<tau>' \<longrightarrow> (\<exists>\<tau> \<in> set \<tau>s. x \<in> fv \<tau>)) \<and> wf_ty \<Sigma> \<tau>'"
proof (induction \<Sigma> \<alpha>s \<sigma> \<tau> and \<Sigma> \<alpha>s \<sigma>s \<tau>s arbitrary: \<tau>' and \<tau>' rule: type_args_induct)
  case (Var \<Sigma> \<alpha>s \<alpha>' \<tau>)
  then show ?case by (auto simp: base_type_wf split: if_splits)
next
  case UnionRight
  from UnionRight.IH UnionRight.prems UnionRight.hyps show ?case by (rule type_args_union_range)
next
  case (List \<Sigma> \<alpha>s \<sigma> \<tau>)
  from List.prems have "wf_ty \<Sigma> \<tau>" and "fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha> = Some \<tau>'" by simp_all
  from List.IH[OF List.prems(1) this] show ?case by simp
next
  case (Dict \<Sigma> \<alpha>s \<sigma> \<tau>)
  from Dict.prems have "wf_ty \<Sigma> \<tau>" and "fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha> = Some \<tau>'" by simp_all
  from Dict.IH[OF Dict.prems(1) this] show ?case by simp
next
  case (Tuple \<Sigma> \<alpha>s \<sigma>s \<tau>s)
  from Tuple.prems have "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>" and "fmlookup (type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s) \<alpha> = Some \<tau>'"
    by simp_all
  from Tuple.IH[OF Tuple.prems(1) this] show ?case by auto
next
  case (Callable \<Sigma> \<alpha>s \<sigma>s \<sigma> \<tau>s \<tau>)
  from Callable.prems have "\<forall>\<tau>' \<in> set (\<tau> # \<tau>s). wf_ty \<Sigma> \<tau>'"
    and "fmlookup (type_args_seq \<Sigma> \<alpha>s (\<sigma> # \<sigma>s) (\<tau> # \<tau>s)) \<alpha> = Some \<tau>'"
    by simp_all
  from Callable.IH[OF Callable.prems(1) this] show ?case by auto
next
  case Class
  from Class.IH Class.prems Class.hyps show ?case by (rule type_args_class_range)
next
  case UnionLeft
  from UnionLeft.IH UnionLeft.prems UnionLeft.hyps show ?case by (rule type_args_union_left_range)
next
  case (Seq \<Sigma> \<alpha>s \<sigma>s \<tau>s)
  let ?P = "\<lambda>\<tau>'. (\<forall>x. x \<in> fv \<tau>' \<longrightarrow> (\<exists>\<tau> \<in> set \<tau>s. x \<in> fv \<tau>)) \<and> wf_ty \<Sigma> \<tau>'"
  have elem: "?P \<tau>'" if "\<gamma> \<in> set (map2 (type_args \<Sigma> \<alpha>s) \<sigma>s \<tau>s)" and "fmlookup \<gamma> \<alpha> = Some \<tau>'" for \<gamma> \<tau>'
  proof -
    from that(1) obtain \<sigma> \<tau> where mem: "(\<sigma>, \<tau>) \<in> set (zip \<sigma>s \<tau>s)" and \<gamma>: "\<gamma> = type_args \<Sigma> \<alpha>s \<sigma> \<tau>" by auto
    from Seq.prems(2) set_zip_rightD[OF mem] have wf: "wf_ty \<Sigma> \<tau>" by auto
    from Seq.IH[OF mem Seq.prems(1) wf that(2)[unfolded \<gamma>]] set_zip_rightD[OF mem] show ?thesis by auto
  qed
  show ?case
  proof (rule foldr_join_cxt_lookup[OF Seq.prems(3)[unfolded type_args_seq.simps]])
    show "\<forall>\<gamma> \<in> set (map2 (type_args \<Sigma> \<alpha>s) \<sigma>s \<tau>s). \<forall>\<tau>'. fmlookup \<gamma> \<alpha> = Some \<tau>' \<longrightarrow> ?P \<tau>'" using elem by blast
    show "?P (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>')" if "?P \<tau>" and "?P \<tau>'" for \<tau> \<tau>'
      using that by (blast intro: join_wf dest: fv_join_elem)
  qed
qed simp_all


subsection \<open>Operators\<close>

(* Result type of an operator overload at well-formed operand types *)
lemma binop_overload_result:
  "\<lbrakk> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega> ; wf_ty \<Sigma> \<sigma>\<^sub>1 ; wf_ty \<Sigma> \<sigma>\<^sub>2 \<rbrakk>
  \<Longrightarrow> wf_ty \<Sigma> (snd \<omega>) \<and> fv (snd \<omega>) \<subseteq> fv \<sigma>\<^sub>1 \<union> fv \<sigma>\<^sub>2"
  by (induction rule: binop_overload.induct) (auto simp: base_type_wf intro: join_wf dest!: fv_join_elem)

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
    show ?thesis by (auto intro: join_wf dest!: fv_join_elem)
  next
    case (right \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
    with less.prems(2) have "wf_ty \<Sigma> \<sigma>\<^sub>1" and "wf_ty \<Sigma> \<sigma>\<^sub>2" by simp_all
    from less.hyps[OF _ less.prems(1) this(1) right(2)] less.hyps[OF _ less.prems(1) this(2) right(3)]
      right(1, 4)
    show ?thesis by (auto intro: join_wf dest!: fv_join_elem)
  qed
qed

lemma binop_overload_operands:
  "\<lbrakk> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega> ; wf_ty \<Sigma> \<sigma>\<^sub>1 ; wf_ty \<Sigma> \<sigma>\<^sub>2 \<rbrakk>
  \<Longrightarrow> wf_ty \<Sigma> (fst (fst \<omega>)) \<and> wf_ty \<Sigma> (snd (fst \<omega>))"
  by (induction rule: binop_overload.induct) (auto simp: base_type_wf)

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

end
