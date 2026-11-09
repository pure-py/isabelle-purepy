(* Stability of pattern checking, shape matching and expression typing under extension of the class table *)
theory ExtensionExpressions
  imports Extension
begin

declare check_expr.simps [simp del] callee.simps [simp del] elements_join.simps [simp del]
  check_args.simps [simp del] resolve_binop_union.simps [simp del]

subsection \<open>Patterns\<close>

(* Type matched by a constructor pattern at a well-formed type other than a union, well-formed *)
lemma matched_as_constr_wf_ty:
  assumes "wf_class_table \<Sigma>" and "wf_cxt \<Sigma> \<Gamma>" and "wf_ty \<Sigma> \<tau>" and "\<forall>\<sigma> \<sigma>'. \<tau> \<noteq> TyUnion \<sigma> \<sigma>'"
  shows "wf_ty \<Sigma> (matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q a))"
proof -
  have eq: "matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q a) =
    (case resolve_name \<Gamma> q of
       Some (Type C) \<Rightarrow> (case instance_at \<Sigma> C \<tau> of Instance \<sigma>s \<Rightarrow> meet \<Sigma> \<tau> (TyClass C \<sigma>s) | _ \<Rightarrow> TyPrim Never)
     | _ \<Rightarrow> TyPrim Never)"
    using assms(4) by (cases \<tau>) auto
  show ?thesis
  proof (cases "resolve_name \<Gamma> q")
    case (Some \<theta>)
    show ?thesis
    proof (cases \<theta>)
      case (Type C)
      with resolve_name_wf[OF assms(2) Some] have C: "C |\<in>| fmdom \<Sigma>" by simp
      show ?thesis
      proof (cases "instance_at \<Sigma> C \<tau>")
        case (Instance \<sigma>s)
        from instance_at_class_wf[OF assms(1, 3) this C] assms(3) show ?thesis
          by (simp add: eq Some Type Instance meet_wf)
      qed (simp_all add: eq Some Type)
    qed (simp_all add: eq Some)
  qed (simp add: eq)
qed

(* Type matched by a pattern at a well-formed type, well-formed *)
lemma matched_as_wf_ty:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> (matched_as \<Sigma> \<Gamma> \<tau> p)"
proof (induction \<Sigma> \<Gamma> \<tau> p rule: matched_as.induct)
  case (8 \<Sigma> \<Gamma> \<tau>s ps)
  then show ?case by (fastforce dest: set_zip_leftD)
qed ((rule matched_as_constr_wf_ty; (assumption | simp)) | ((auto intro: join_wf meet_wf)[1]; fail))+

lemma matched_as_constr_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "wf_cxt \<Sigma> \<Gamma>" and "wf_ty \<Sigma> \<tau>" and "\<forall>\<sigma> \<sigma>'. \<tau> \<noteq> TyUnion \<sigma> \<sigma>'"
  shows "matched_as \<Sigma>' \<Gamma> \<tau> (PatConstr q a) = matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q a)"
proof -
  interpret extension \<Sigma> \<Sigma>' by fact
  have eq: "matched_as \<Sigma>'' \<Gamma> \<tau> (PatConstr q a) =
    (case resolve_name \<Gamma> q of
       Some (Type C) \<Rightarrow> (case instance_at \<Sigma>'' C \<tau> of Instance \<sigma>s \<Rightarrow> meet \<Sigma>'' \<tau> (TyClass C \<sigma>s) | _ \<Rightarrow> TyPrim Never)
     | _ \<Rightarrow> TyPrim Never)" for \<Sigma>''
    using assms(4) by (cases \<tau>) auto
  show ?thesis
  proof (cases "resolve_name \<Gamma> q")
    case (Some \<theta>)
    show ?thesis
    proof (cases \<theta>)
      case (Type C)
      with resolve_name_wf[OF assms(2) Some] have C: "C |\<in>| fmdom \<Sigma>" by simp
      show ?thesis
      proof (cases "instance_at \<Sigma> C \<tau>")
        case (Instance \<sigma>s)
        from instance_at_class_wf[OF wf_table assms(3) this C] assms(3) show ?thesis
          by (simp add: eq Some Type Instance instance_at_ext[OF assms(3) C] meet_ext)
      qed (simp_all add: eq Some Type instance_at_ext[OF assms(3) C])
    qed (simp_all add: eq Some)
  qed (simp add: eq)
qed

lemma matched_as_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> matched_as \<Sigma>' \<Gamma> \<tau> p = matched_as \<Sigma> \<Gamma> \<tau> p"
proof (induction \<Sigma> \<Gamma> \<tau> p rule: matched_as.induct)
  case (1 \<Sigma> \<Gamma> \<sigma> \<tau> p)
  interpret extension \<Sigma> \<Sigma>' by fact
  from "1.prems" show ?case by (simp add: 1 join_ext matched_as_wf_ty[OF wf_table])
next
  case (8 \<Sigma> \<Gamma> \<tau>s ps)
  show ?case
  proof (cases "length \<tau>s = length ps")
    case True
    have "map2 (\<lambda>\<tau> p. matched_as \<Sigma>' \<Gamma> \<tau> (node p)) \<tau>s ps = map2 (\<lambda>\<tau> p. matched_as \<Sigma> \<Gamma> \<tau> (node p)) \<tau>s ps"
      using "8.IH"[OF True _ refl] "8.prems" by (intro map_cong[OF refl]) (auto dest: set_zip_leftD)
    with True show ?thesis by (simp only: matched_as.simps if_True)
  qed simp
qed ((rule matched_as_constr_mono; (assumption | simp)) | ((auto simp: extension.meet_ext)[1]; fail))+

lemma field_patterns_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; C |\<in>| fmdom \<Sigma> \<rbrakk> \<Longrightarrow> field_patterns \<Sigma>' C a = field_patterns \<Sigma> C a"
  by (cases a) (simp add: extension.field_names_ext)

(* Type remaining after a constructor pattern at a well-formed type other than a union, given the stability of
   the sub-patterns at the field types *)
lemma remaining_constr_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "wf_cxt \<Sigma> \<Gamma>" and "wf_ty \<Sigma> \<tau>" and "\<forall>\<sigma> \<sigma>'. \<tau> \<noteq> TyUnion \<sigma> \<sigma>'"
    and IH: "\<And>C \<sigma>s p \<sigma>. \<lbrakk> resolve_name \<Gamma> q = Some (Type C) ; instance_at \<Sigma> C \<tau> = Instance \<sigma>s
                ; (p, \<sigma>) \<in> set (zip (field_patterns \<Sigma> C a) (field_types \<Sigma> C \<sigma>s)) ; wf_ty \<Sigma> \<sigma> \<rbrakk>
              \<Longrightarrow> remaining \<Sigma>' \<Gamma> \<sigma> (node p) = remaining \<Sigma> \<Gamma> \<sigma> (node p)"
  shows "remaining \<Sigma>' \<Gamma> \<tau> (PatConstr q a) = remaining \<Sigma> \<Gamma> \<tau> (PatConstr q a)"
proof -
  interpret extension \<Sigma> \<Sigma>' by fact
  have eq: "remaining \<Sigma>'' \<Gamma> \<tau> (PatConstr q a) =
    (case resolve_name \<Gamma> q of
       Some (Type C) \<Rightarrow>
         (case instance_at \<Sigma>'' C \<tau> of
            Instance \<sigma>s \<Rightarrow>
              if \<Sigma>'' \<turnstile> \<tau> <: TyClass C \<sigma>s
                 \<and> (\<forall>(p, \<sigma>) \<in> set (zip (field_patterns \<Sigma>'' C a) (field_types \<Sigma>'' C \<sigma>s)).
                      remaining \<Sigma>'' \<Gamma> \<sigma> (node p) = TyPrim Never)
              then TyPrim Never
              else \<tau>
          | _ \<Rightarrow> \<tau>)
     | _ \<Rightarrow> \<tau>)" for \<Sigma>''
    using assms(4) by (cases \<tau>) auto
  show ?thesis
  proof (cases "resolve_name \<Gamma> q")
    case (Some \<theta>)
    show ?thesis
    proof (cases \<theta>)
      case (Type C)
      with resolve_name_wf[OF assms(2) Some] have C: "C |\<in>| fmdom \<Sigma>" by simp
      show ?thesis
      proof (cases "instance_at \<Sigma> C \<tau>")
        case (Instance \<sigma>s)
        have wfC: "wf_ty \<Sigma> (TyClass C \<sigma>s)" by (rule instance_at_class_wf[OF wf_table assms(3) Instance C])
        have sub: "remaining \<Sigma>' \<Gamma> \<sigma> (node p) = remaining \<Sigma> \<Gamma> \<sigma> (node p)"
          if "(p, \<sigma>) \<in> set (zip (field_patterns \<Sigma> C a) (field_types \<Sigma> C \<sigma>s))" for p \<sigma>
          using IH[OF Some[unfolded Type] Instance that] field_types_wf[OF wf_table wfC] set_zip_rightD[OF that]
          by blast
        have eqb: "(\<forall>(p, \<sigma>) \<in> set (zip (field_patterns \<Sigma> C a) (field_types \<Sigma> C \<sigma>s)).
                      remaining \<Sigma>' \<Gamma> \<sigma> (node p) = TyPrim Never)
                 = (\<forall>(p, \<sigma>) \<in> set (zip (field_patterns \<Sigma> C a) (field_types \<Sigma> C \<sigma>s)).
                      remaining \<Sigma> \<Gamma> \<sigma> (node p) = TyPrim Never)"
          by (rule ball_cong[OF refl]) (auto simp: sub)
        show ?thesis
          by (simp add: eq Some Type Instance instance_at_ext[OF assms(3) C] subty_ext[OF assms(3) wfC]
              field_patterns_mono[OF assms(1) C] field_types_ext[OF C] eqb)
      qed (simp_all add: eq Some Type instance_at_ext[OF assms(3) C])
    qed (simp_all add: eq Some)
  qed (simp add: eq)
qed

lemma remaining_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> remaining \<Sigma>' \<Gamma> \<tau> p = remaining \<Sigma> \<Gamma> \<tau> p"
proof (induction \<Sigma> \<Gamma> \<tau> p rule: remaining.induct)
  case (1 \<Sigma> \<Gamma> \<sigma> \<tau> p)
  interpret extension \<Sigma> \<Sigma>' by fact
  from "1.prems" show ?case by (simp add: 1 join_ext remaining_wf)
next
  case (8 \<Sigma> \<Gamma> \<tau>s ps)
  show ?case
  proof (cases "length \<tau>s = length ps")
    case True
    have "map2 (\<lambda>\<tau> p. remaining \<Sigma>' \<Gamma> \<tau> (node p)) \<tau>s ps = map2 (\<lambda>\<tau> p. remaining \<Sigma> \<Gamma> \<tau> (node p)) \<tau>s ps"
      using "8.IH"[OF True _ refl] "8.prems" by (intro map_cong[OF refl]) (auto dest: set_zip_leftD)
    with True show ?thesis by (simp only: remaining.simps Let_def if_True)
  qed simp
qed ((rule remaining_constr_mono; (assumption | (simp; fail) | blast)) | ((auto)[1]; fail))+

(* Bindings at the disjuncts of a type, each binding the variables of the pattern at well-formed types *)
lemma bindings_at_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "ms \<noteq> []"
    and dom: "\<And>\<Delta>. Some (Ok \<Delta>) \<in> set ms \<Longrightarrow> fmdom' \<Delta> = binds p"
    and wf: "\<And>\<Delta> x \<sigma>. \<lbrakk> Some (Ok \<Delta>) \<in> set ms ; fmlookup \<Delta> x = Some \<sigma> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<sigma>"
  shows "bindings_at \<Sigma>' \<Gamma> p ms = bindings_at \<Sigma> \<Gamma> p ms"
proof -
  interpret extension \<Sigma> \<Sigma>' by fact
  let ?g = "\<lambda>m. case m of
                  Some m' \<Rightarrow> m'
                | None \<Rightarrow> do {
                    all_sum (map (check_unbound \<Gamma>) (sorted_list_of_set (binds p)));
                    Ok (fmconst (binds p) (TyPrim Never))
                  }"
  show ?thesis
  proof (cases "those_sum (map ?g ms)")
    case (Inr \<Delta>s)
    have each: "fmdom' \<Delta> = binds p \<and> (\<forall>x \<sigma>. fmlookup \<Delta> x = Some \<sigma> \<longrightarrow> wf_ty \<Sigma> \<sigma>)" if "\<Delta> \<in> set \<Delta>s" for \<Delta>
    proof -
      from those_sum_map_Ok_elem[OF Inr that] obtain m where m: "m \<in> set ms" and g: "?g m = Ok \<Delta>" by auto
      show ?thesis
      proof (cases m)
        case None
        with g have "\<Delta> = fmconst (binds p) (TyPrim Never)" by (auto simp: bind_sum_Ok)
        then show ?thesis
          by (auto simp: fmlookup_dom'_iff fmlookup_fmconst[OF finite_binds_pat] split: if_splits)
      next
        case (Some m')
        with g m have "Some (Ok \<Delta>) \<in> set ms" by simp
        with dom wf show ?thesis by blast
      qed
    qed
    have "\<Delta>s \<noteq> []" using those_sum_map_Ok[OF Inr] assms(2) by (auto dest: list_all2_lengthD)
    then have hd: "hd \<Delta>s \<in> set \<Delta>s" by simp
    have "joins \<Sigma>' (map (\<lambda>\<Delta>. the (fmlookup \<Delta> x)) \<Delta>s) = joins \<Sigma> (map (\<lambda>\<Delta>. the (fmlookup \<Delta> x)) \<Delta>s)"
      if x: "fmlookup (hd \<Delta>s) x = Some \<sigma>" for x \<sigma>
    proof (rule joins_ext, intro ballI)
      fix \<rho>
      assume "\<rho> \<in> set (map (\<lambda>\<Delta>. the (fmlookup \<Delta> x)) \<Delta>s)"
      then obtain \<Delta> where \<Delta>: "\<Delta> \<in> set \<Delta>s" and \<rho>: "\<rho> = the (fmlookup \<Delta> x)" by auto
      from each[OF \<Delta>] each[OF hd] x have "x \<in> fmdom' \<Delta>" by (auto simp: fmlookup_dom'_iff)
      then obtain \<sigma>' where "fmlookup \<Delta> x = Some \<sigma>'" by (auto simp: fmlookup_dom'_iff)
      with each[OF \<Delta>] \<rho> show "wf_ty \<Sigma> \<rho>" by simp
    qed
    then show ?thesis unfolding bindings_at_def Inr by (simp cong: fmmap_keys_cong)
  qed (simp add: bindings_at_def)
qed

lemma check_pat_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> check_pat \<Sigma>' \<Gamma> p \<tau> = check_pat \<Sigma> \<Gamma> p \<tau>"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau>' \<rbrakk> \<Longrightarrow> check_pat_at \<Sigma>' \<Gamma> p' \<tau>' = check_pat_at \<Sigma> \<Gamma> p' \<tau>'"
proof (induction \<Sigma> \<Gamma> p \<tau> and \<Sigma> \<Gamma> p' \<tau>' rule: check_pat_check_pat_at.induct)
  case (3 \<Sigma> \<Gamma> p x \<tau>)
  then show ?case by (simp add: matched_as_mono cong: bind_sum_cong)
next
  case (4 \<Sigma> \<Gamma> l \<tau>)
  then show ?case by (simp add: extension.has_float_values_ext)
next
  case (5 \<Sigma> \<Gamma> ps \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  let ?f = "\<lambda>\<Sigma> \<sigma>. case \<sigma> of
              TyTuple \<sigma>s \<Rightarrow>
                if length \<sigma>s = length ps then Some (pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s))
                else None
            | _ \<Rightarrow> None"
  let ?ens = "by_rule RuleCheckTupleNone (do {
      ensure (\<not> has_values \<Sigma> ListKind \<tau>) (SequenceKindMismatch TupleKind \<tau> ListKind);
      ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch TupleKind \<tau> RangeKind)
    })"
  have ens: "by_rule RuleCheckTupleNone (do {
      ensure (\<not> has_values \<Sigma>' ListKind \<tau>) (SequenceKindMismatch TupleKind \<tau> ListKind);
      ensure (\<not> has_values \<Sigma>' RangeKind \<tau>) (SequenceKindMismatch TupleKind \<tau> RangeKind)
    }) = ?ens"
    using "5.prems"(3) by (simp add: has_values_ext)
  have body: "bindings_at \<Sigma>' \<Gamma> (PatTuple ps) (map (?f \<Sigma>') (disjuncts \<tau>))
            = bindings_at \<Sigma> \<Gamma> (PatTuple ps) (map (?f \<Sigma>) (disjuncts \<tau>))"
    if ens': "?ens = Ok u" and cb: "check_bound_once ps = Ok u'" for u u'
  proof -
    have sub: "check_pat_at \<Sigma>' \<Gamma> p \<sigma>' = check_pat_at \<Sigma> \<Gamma> p \<sigma>'"
      if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and \<sigma>s: "\<sigma> = TyTuple \<sigma>s" and len: "length \<sigma>s = length ps"
        and mem: "(p, \<sigma>') \<in> set (zip ps \<sigma>s)" for \<sigma> \<sigma>s p \<sigma>'
      using "5.IH"[OF ens' cb \<sigma> \<sigma>s len mem refl "5.prems"(1, 2)] disjuncts_wf[OF "5.prems"(3) \<sigma>]
        set_zip_rightD[OF mem]
      by (auto simp: \<sigma>s)
    have f: "map (?f \<Sigma>') (disjuncts \<tau>) = map (?f \<Sigma>) (disjuncts \<tau>)"
      by (intro map_cong[OF refl]) (auto simp: sub split: ty.splits intro!: arg_cong[where f = pattern_bindings])
    have dom_wf: "fmdom' \<Delta> = binds (PatTuple ps) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta> x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>')"
      if "Some (Ok \<Delta>) \<in> set (map (?f \<Sigma>) (disjuncts \<tau>))" for \<Delta>
    proof -
      from that obtain \<sigma> \<sigma>s where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and \<sigma>s: "\<sigma> = TyTuple \<sigma>s"
        and len: "length \<sigma>s = length ps" and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) = Ok \<Delta>"
        by (auto split: ty.splits if_splits)
      from disjuncts_wf[OF "5.prems"(3) \<sigma>] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" by simp
      have "fmdom' \<Delta>' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> UNIV)"
        if mem: "(p, \<sigma>') \<in> set (zip ps \<sigma>s)" and chk: "check_pat_at \<Sigma> \<Gamma> p \<sigma>' = Ok \<Delta>'" for p \<sigma>' \<Delta>'
        using check_pat_wf(2)[OF wf_table "5.prems"(2) _ chk] wf\<sigma> set_zip_rightD[OF mem] by (auto simp: \<sigma>s)
      from pattern_bindings_wf[OF pb len[symmetric] this] show ?thesis by auto
    qed
    show ?thesis unfolding f by (rule bindings_at_mono[OF "5.prems"(1)]) (use dom_wf disjuncts_nonempty in auto)
  qed
  show ?case unfolding check_pat.simps ens by (rule bind_sum_cong[OF refl], rule bind_sum_cong[OF refl]) (rule body)
next
  case (6 \<Sigma> \<Gamma> ps \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  let ?f = "\<lambda>\<Sigma> \<sigma>. case \<sigma> of
              TyList \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p. check_pat_at \<Sigma> \<Gamma> p \<sigma>') ps))
            | _ \<Rightarrow> None"
  let ?ens = "by_rule RuleCheckListNone (do {
      ensure (\<not> has_values \<Sigma> TupleKind \<tau>) (SequenceKindMismatch ListKind \<tau> TupleKind);
      ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch ListKind \<tau> RangeKind)
    })"
  have ens: "by_rule RuleCheckListNone (do {
      ensure (\<not> has_values \<Sigma>' TupleKind \<tau>) (SequenceKindMismatch ListKind \<tau> TupleKind);
      ensure (\<not> has_values \<Sigma>' RangeKind \<tau>) (SequenceKindMismatch ListKind \<tau> RangeKind)
    }) = ?ens"
    using "6.prems"(3) by (simp add: has_values_ext)
  have body: "bindings_at \<Sigma>' \<Gamma> (PatList ps) (map (?f \<Sigma>') (disjuncts \<tau>))
            = bindings_at \<Sigma> \<Gamma> (PatList ps) (map (?f \<Sigma>) (disjuncts \<tau>))"
    if ens': "?ens = Ok u" and cb: "check_bound_once ps = Ok u'" for u u'
  proof -
    have sub: "check_pat_at \<Sigma>' \<Gamma> p \<sigma>' = check_pat_at \<Sigma> \<Gamma> p \<sigma>'"
      if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and \<sigma>': "\<sigma> = TyList \<sigma>'" and p: "p \<in> set ps" for \<sigma> \<sigma>' p
      using "6.IH"[OF ens' cb \<sigma> \<sigma>' p "6.prems"(1, 2)] disjuncts_wf[OF "6.prems"(3) \<sigma>] by (auto simp: \<sigma>')
    have f: "map (?f \<Sigma>') (disjuncts \<tau>) = map (?f \<Sigma>) (disjuncts \<tau>)"
      by (intro map_cong[OF refl]) (auto simp: sub split: ty.splits intro!: arg_cong[where f = pattern_bindings])
    have dom_wf: "fmdom' \<Delta> = binds (PatList ps) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta> x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>')"
      if "Some (Ok \<Delta>) \<in> set (map (?f \<Sigma>) (disjuncts \<tau>))" for \<Delta>
    proof -
      from that obtain \<sigma> \<sigma>' where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and \<sigma>': "\<sigma> = TyList \<sigma>'"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps (replicate (length ps) \<sigma>')) = Ok \<Delta>"
        by (auto simp: map2_replicate split: ty.splits)
      from disjuncts_wf[OF "6.prems"(3) \<sigma>] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>'" by (simp add: \<sigma>')
      have "fmdom' \<Delta>' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> UNIV)"
        if mem: "(p, \<sigma>'') \<in> set (zip ps (replicate (length ps) \<sigma>'))" and chk: "check_pat_at \<Sigma> \<Gamma> p \<sigma>'' = Ok \<Delta>'"
        for p \<sigma>'' \<Delta>'
        using check_pat_wf(2)[OF wf_table "6.prems"(2) _ chk] wf\<sigma> set_zip_rightD[OF mem] by auto
      from pattern_bindings_wf[OF pb _ this] show ?thesis by auto
    qed
    show ?thesis unfolding f by (rule bindings_at_mono[OF "6.prems"(1)]) (use dom_wf disjuncts_nonempty in auto)
  qed
  show ?case unfolding check_pat.simps ens by (rule bind_sum_cong[OF refl], rule bind_sum_cong[OF refl]) (rule body)
next
  case (7 \<Sigma> \<Gamma> kps \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  let ?f = "\<lambda>\<Sigma> \<sigma>. case \<sigma> of
              TyDict \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p. check_pat_at \<Sigma> \<Gamma> p \<sigma>') (map snd kps)))
            | _ \<Rightarrow>
                if has_dict_values \<Sigma> \<sigma> then Some (Fail (Violates RuleCheckDictNone (DictPatternDictValues \<sigma>)))
                else None"
  have body: "bindings_at \<Sigma>' \<Gamma> (PatDict kps) (map (?f \<Sigma>') (disjuncts \<tau>))
            = bindings_at \<Sigma> \<Gamma> (PatDict kps) (map (?f \<Sigma>) (disjuncts \<tau>))"
    if cb: "check_bound_once (map snd kps) = Ok u" for u
  proof -
    have sub: "check_pat_at \<Sigma>' \<Gamma> p \<sigma>' = check_pat_at \<Sigma> \<Gamma> p \<sigma>'"
      if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and \<sigma>': "\<sigma> = TyDict \<sigma>'" and p: "p \<in> set (map snd kps)" for \<sigma> \<sigma>' p
      using "7.IH"[OF cb \<sigma> \<sigma>' p "7.prems"(1, 2)] disjuncts_wf[OF "7.prems"(3) \<sigma>] by (auto simp: \<sigma>')
    have f: "map (?f \<Sigma>') (disjuncts \<tau>) = map (?f \<Sigma>) (disjuncts \<tau>)"
      using disjuncts_wf[OF "7.prems"(3)]
      by (intro map_cong[OF refl])
         (auto simp: sub has_dict_values_ext split: ty.splits intro!: arg_cong[where f = pattern_bindings])
    have dom_wf: "fmdom' \<Delta> = binds (PatDict kps) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta> x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>')"
      if "Some (Ok \<Delta>) \<in> set (map (?f \<Sigma>) (disjuncts \<tau>))" for \<Delta>
    proof -
      from that obtain \<sigma> \<sigma>' where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and \<sigma>': "\<sigma> = TyDict \<sigma>'"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) (map snd kps) (replicate (length kps) \<sigma>')) = Ok \<Delta>"
        by (auto simp: map2_replicate[of _ "map snd kps", simplified] split: ty.splits if_splits)
      from disjuncts_wf[OF "7.prems"(3) \<sigma>] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>'" by (simp add: \<sigma>')
      have "fmdom' \<Delta>' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> UNIV)"
        if mem: "(p, \<sigma>'') \<in> set (zip (map snd kps) (replicate (length kps) \<sigma>'))"
        and chk: "check_pat_at \<Sigma> \<Gamma> p \<sigma>'' = Ok \<Delta>'" for p \<sigma>'' \<Delta>'
        using check_pat_wf(2)[OF wf_table "7.prems"(2) _ chk] wf\<sigma> set_zip_rightD[OF mem] by auto
      from pattern_bindings_wf[OF pb _ this] show ?thesis by auto
    qed
    show ?thesis unfolding f by (rule bindings_at_mono[OF "7.prems"(1)]) (use dom_wf disjuncts_nonempty in auto)
  qed
  show ?case unfolding check_pat.simps by (rule bind_sum_cong[OF refl]) (rule body)
next
  case (8 \<Sigma> \<Gamma> q ps kps \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  let ?f = "\<lambda>\<Sigma> C \<sigma>. case instance_at \<Sigma> C \<sigma> of
              Instance \<sigma>s \<Rightarrow>
                Some (pattern_bindings
                  (map2 (check_pat_at \<Sigma> \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s)))
            | NoInstance \<Rightarrow> None
            | Undetermined \<Rightarrow>
                Some (Fail (Violates
                  (if instance_above \<Sigma> C \<sigma> = Undetermined then RuleInstanceAbove else RuleInstanceBelow)
                  (PatternClassUndetermined (short_name C) \<sigma>)))"
  have body: "do {
      check_field_map (PatternArityMismatch (short_name C)) (UnknownFieldInPattern (short_name C))
        (field_names \<Sigma>' C) (length ps) (map fst kps);
      check_bound_once (ps @ map snd kps);
      bindings_at \<Sigma>' \<Gamma> (PatConstr q (ps, kps)) (map (?f \<Sigma>' C) (disjuncts \<tau>))
    } = do {
      check_field_map (PatternArityMismatch (short_name C)) (UnknownFieldInPattern (short_name C))
        (field_names \<Sigma> C) (length ps) (map fst kps);
      check_bound_once (ps @ map snd kps);
      bindings_at \<Sigma> \<Gamma> (PatConstr q (ps, kps)) (map (?f \<Sigma> C) (disjuncts \<tau>))
    }"
    if cls: "check_pattern_class \<Gamma> q = Ok C" for C
  proof -
    from check_pattern_class_dom[OF "8.prems"(2) cls] have C: "C |\<in>| fmdom \<Sigma>" by simp
    have "bindings_at \<Sigma>' \<Gamma> (PatConstr q (ps, kps)) (map (?f \<Sigma>' C) (disjuncts \<tau>))
        = bindings_at \<Sigma> \<Gamma> (PatConstr q (ps, kps)) (map (?f \<Sigma> C) (disjuncts \<tau>))"
      if fm: "check_field_map (PatternArityMismatch (short_name C)) (UnknownFieldInPattern (short_name C))
                (field_names \<Sigma> C) (length ps) (map fst kps) = Ok u"
      and cb: "check_bound_once (ps @ map snd kps) = Ok u'" for u u'
    proof -
      have wfC: "wf_ty \<Sigma> (TyClass C \<sigma>s)" if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and inst: "instance_at \<Sigma> C \<sigma> = Instance \<sigma>s"
        for \<sigma> \<sigma>s
        using instance_at_class_wf[OF wf_table _ inst C] disjuncts_wf[OF "8.prems"(3) \<sigma>] by blast
      have sub: "check_pat_at \<Sigma>' \<Gamma> p \<sigma>' = check_pat_at \<Sigma> \<Gamma> p \<sigma>'"
        if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and inst: "instance_at \<Sigma> C \<sigma> = Instance \<sigma>s"
          and mem: "(p, \<sigma>') \<in> set (zip (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s))" for \<sigma> \<sigma>s p \<sigma>'
        using "8.IH"[OF cls fm cb \<sigma> inst mem refl "8.prems"(1, 2)] field_types_wf[OF wf_table wfC[OF \<sigma> inst]]
          set_zip_rightD[OF mem]
        by blast
      have f: "map (?f \<Sigma>' C) (disjuncts \<tau>) = map (?f \<Sigma> C) (disjuncts \<tau>)"
      proof (intro map_cong[OF refl])
        fix \<sigma>
        assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)"
        with disjuncts_wf[OF "8.prems"(3)] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" by blast
        show "?f \<Sigma>' C \<sigma> = ?f \<Sigma> C \<sigma>"
        proof (cases "instance_at \<Sigma> C \<sigma>")
          case (Instance \<sigma>s)
          have eqm: "map2 (check_pat_at \<Sigma>' \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s)
              = map2 (check_pat_at \<Sigma> \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s)"
            using sub[OF \<sigma> Instance] by (intro map_cong[OF refl]) auto
          show ?thesis
            unfolding instance_at_ext[OF wf\<sigma> C] Instance instances.case field_patterns_mono[OF "8.prems"(1) C]
              field_types_ext[OF C] eqm
            by (rule refl)
        qed (simp_all add: instance_at_ext[OF wf\<sigma> C] instance_above_ext[OF wf\<sigma> C])
      qed
      have dom_wf: "fmdom' \<Delta> = binds (PatConstr q (ps, kps)) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta> x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>')"
        if "Some (Ok \<Delta>) \<in> set (map (?f \<Sigma> C) (disjuncts \<tau>))" for \<Delta>
      proof -
        from that obtain \<sigma> \<sigma>s where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and inst: "instance_at \<Sigma> C \<sigma> = Instance \<sigma>s"
          and pb: "pattern_bindings
                     (map2 (check_pat_at \<Sigma> \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s)) = Ok \<Delta>"
          by (auto split: instances.splits)
        from fm have len_kps: "length ps + length kps = length (field_names \<Sigma> C)"
          and keys: "set (map fst kps) = set (drop (length ps) (field_names \<Sigma> C))"
          by (auto simp: check_field_map_def split: if_splits)
        from field_patterns_cover[OF wf_class_table_distinct[OF wf_table C] len_kps keys]
        have len_fp: "length (field_patterns \<Sigma> C (ps, kps)) = length (field_names \<Sigma> C)"
          and set_fp: "set (field_patterns \<Sigma> C (ps, kps)) = set ps \<union> set (map snd kps)"
          using len_kps by simp_all
        have "fmdom' \<Delta>' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> UNIV)"
          if mem: "(p, \<sigma>') \<in> set (zip (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s))"
          and chk: "check_pat_at \<Sigma> \<Gamma> p \<sigma>' = Ok \<Delta>'" for p \<sigma>' \<Delta>'
        proof -
          have wf\<sigma>': "wf_ty \<Sigma> \<sigma>'" using field_types_wf[OF wf_table wfC[OF \<sigma> inst]] set_zip_rightD[OF mem] by blast
          from check_pat_wf(2)[OF wf_table "8.prems"(2) wf\<sigma>' chk] show ?thesis by blast
        qed
        from pattern_bindings_wf[OF pb _ this] len_fp length_field_types[of \<Sigma> C \<sigma>s] set_fp show ?thesis
          by auto
      qed
      show ?thesis unfolding f by (rule bindings_at_mono[OF "8.prems"(1)]) (use dom_wf disjuncts_nonempty in auto)
    qed
    then show ?thesis
      unfolding field_names_ext[OF C] by (intro bind_sum_cong[OF refl]) simp
  qed
  show ?case
    unfolding check_pat.simps
    by (rule arg_cong[where f = "by_rule RuleCheckConstr"]) (rule bind_sum_cong[OF refl body])
qed (simp_all cong: bind_sum_cong)

subsection \<open>Shapes\<close>

(* Equations with a variable on the left in place of a constructor, applied explicitly *)
declare match_shape.simps [simp del] match_shape_upto.simps [simp del]

(* Head whose class is in the class table *)
fun wf_head :: "class_table \<Rightarrow> head \<Rightarrow> bool"
where
"wf_head \<Sigma> (HeadClass C) = (C |\<in>| fmdom \<Sigma>)" |
"wf_head \<Sigma> _ = True"

abbreviation wf_heads :: "class_table \<Rightarrow> head set \<Rightarrow> bool"
where "wf_heads \<Sigma> H \<equiv> \<forall>h \<in> H. wf_head \<Sigma> h"

(* Shape over well-formed types, its heads and classes in the class table *)
fun wf_shape :: "class_table \<Rightarrow> shape \<Rightarrow> bool"
where
"wf_shape \<Sigma> (ShapeRest \<tau> H) = (wf_ty \<Sigma> \<tau> \<and> wf_heads \<Sigma> H)" |
"wf_shape \<Sigma> (ShapeConstr C \<tau>s ks H) = (wf_ty \<Sigma> (TyClass C \<tau>s) \<and> list_all (wf_shape \<Sigma>) ks \<and> wf_heads \<Sigma> H)" |
"wf_shape \<Sigma> (ShapeTuple ks) = list_all (wf_shape \<Sigma>) ks" |
"wf_shape \<Sigma> (ShapeList \<tau> ks) = (wf_ty \<Sigma> \<tau> \<and> list_all (wf_shape \<Sigma>) ks)" |
"wf_shape \<Sigma> (ShapeDict \<tau> \<beta> W) = (wf_ty \<Sigma> \<tau> \<and> list_all (wf_shape \<Sigma> \<circ> snd) \<beta>)"

lemma head_typed_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_head \<Sigma> h ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> head_typed \<Sigma>' h \<tau> = head_typed \<Sigma> h \<tau>"
  by (induction \<Sigma> h \<tau> rule: head_typed.induct)
     (auto simp: extension.subty_ext extension.instance_below_ext simp del: instance_below.simps)

lemma typed_heads_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_heads \<Sigma> H ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> typed_heads \<Sigma>' H \<tau> = typed_heads \<Sigma> H \<tau>"
  by (auto simp: typed_heads_def head_typed_mono intro!: set_eqI)

lemma typed_heads_wf: "wf_heads \<Sigma> H \<Longrightarrow> wf_heads \<Sigma> (typed_heads \<Sigma> H \<tau>)"
  by (auto simp: typed_heads_def)

lemma below_excluded_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; C |\<in>| fmdom \<Sigma> \<rbrakk> \<Longrightarrow> below_excluded \<Sigma>' C H = below_excluded \<Sigma> C H"
  by (simp add: below_excluded_def extension.ancestors_ext)

lemma exhausts_mono: "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> exhausts \<Sigma>' H \<tau> = exhausts \<Sigma> H \<tau>"
  by (induction \<Sigma> H \<tau> rule: exhausts.induct) (auto simp: below_excluded_mono)

lemma shapes_mono: "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_heads \<Sigma> H ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> shapes \<Sigma>' \<tau> H = shapes \<Sigma> \<tau> H"
proof (induction \<Sigma> \<tau> H rule: shapes.induct)
  case (1 \<Sigma> \<sigma> \<tau> H)
  then show ?case by (simp add: Let_def typed_heads_mono typed_heads_wf)
qed (auto simp: exhausts_mono below_excluded_mono)

lemma shapes_wf: "\<lbrakk> wf_heads \<Sigma> H ; wf_ty \<Sigma> \<tau> ; k \<in> set (shapes \<Sigma> \<tau> H) \<rbrakk> \<Longrightarrow> wf_shape \<Sigma> k"
  by (induction \<Sigma> \<tau> H arbitrary: k rule: shapes.induct) (auto simp: Let_def typed_heads_wf split: if_splits)

lemma shapes_wfD: "\<lbrakk> k \<in> set (shapes \<Sigma> \<tau> H) ; wf_heads \<Sigma> H ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_shape \<Sigma> k"
  by (rule shapes_wf)

lemma shapes_seq_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> shapes_seq \<Sigma>' \<tau>s = shapes_seq \<Sigma> \<tau>s"
  by (simp add: shapes_seq_def shapes_mono cong: map_cong)

lemma shapes_seq_wf:
  "\<lbrakk> ks \<in> set (shapes_seq \<Sigma> \<tau>s) ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> list_all (wf_shape \<Sigma>) ks"
  unfolding shapes_seq_def product_lists_set
  by (fastforce simp: list_all2_conv_all_nth list_all_length intro: shapes_wf[where H = "{}"])

lemma with_keys_wf:
  "\<lbrakk> list_all (wf_shape \<Sigma> \<circ> snd) \<beta> ; list_all (wf_shape \<Sigma>) ks \<rbrakk> \<Longrightarrow> list_all (wf_shape \<Sigma> \<circ> snd) (with_keys \<beta> ws ks)"
  by (auto simp: with_keys_def list_all_iff dest: set_zip_rightD)

lemma split_rest_constr_mono:
  assumes ext: "extension \<Sigma> \<Sigma>'" and \<Gamma>: "wf_cxt \<Sigma> \<Gamma>" and \<tau>: "wf_ty \<Sigma> \<tau>" and H: "wf_heads \<Sigma> H"
  shows "split \<Sigma>' \<Gamma> (ShapeRest \<tau> H) (PatConstr q a) = split \<Sigma> \<Gamma> (ShapeRest \<tau> H) (PatConstr q a)"
proof -
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?thesis
  proof (cases "resolve_name \<Gamma> q")
    case (Some \<theta>)
    show ?thesis
    proof (cases \<theta>)
      case (Type C)
      with resolve_name_wf[OF \<Gamma> Some] have C: "C |\<in>| fmdom \<Sigma>" by simp
      show ?thesis
      proof (cases "instance_at \<Sigma> C \<tau>")
        case (Instance \<tau>s)
        have wfC: "wf_ty \<Sigma> (TyClass C \<tau>s)" by (rule instance_at_class_wf[OF wf_table \<tau> Instance C])
        have wfm: "wf_ty \<Sigma> (meet \<Sigma> \<tau> (TyClass C \<tau>s))" by (rule meet_wf(1)[OF \<tau> wfC])
        show ?thesis
        proof (cases "meet \<Sigma> \<tau> (TyClass C \<tau>s)")
          case (TyClass D \<sigma>s)
          with wfm have D: "D |\<in>| fmdom \<Sigma>" and wfD: "wf_ty \<Sigma> (TyClass D \<sigma>s)" by simp_all
          have "\<forall>\<sigma> \<in> set (field_types \<Sigma> D \<sigma>s). wf_ty \<Sigma> \<sigma>" using field_types_wf[OF wf_table wfD] by blast
          with Some Type Instance TyClass \<tau> H C show ?thesis
            by (simp add: instance_at_ext[OF \<tau> C] meet_ext[OF \<tau> wfC] below_excluded_mono[OF ext C]
                field_types_ext[OF D] shapes_seq_mono[OF ext] typed_heads_mono[OF ext H wfD]
                shapes_mono[OF ext _ \<tau>])
        qed (simp_all add: Some Type Instance instance_at_ext[OF \<tau> C] meet_ext[OF \<tau> wfC]
               below_excluded_mono[OF ext C])
      qed (simp_all add: Some Type instance_at_ext[OF \<tau> C] below_excluded_mono[OF ext C])
    qed (simp_all add: Some)
  qed simp
qed

lemma split_constr_constr_mono:
  assumes ext: "extension \<Sigma> \<Sigma>'" and \<Gamma>: "wf_cxt \<Sigma> \<Gamma>" and C: "wf_ty \<Sigma> (TyClass C \<tau>s)" and H: "wf_heads \<Sigma> H"
  shows "split \<Sigma>' \<Gamma> (ShapeConstr C \<tau>s ks H) (PatConstr q a) = split \<Sigma> \<Gamma> (ShapeConstr C \<tau>s ks H) (PatConstr q a)"
proof -
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?thesis
  proof (cases "resolve_name \<Gamma> q")
    case (Some \<theta>)
    show ?thesis
    proof (cases \<theta>)
      case (Type D)
      with resolve_name_wf[OF \<Gamma> Some] have D: "D |\<in>| fmdom \<Sigma>" by simp
      show ?thesis
      proof (cases "instance_at \<Sigma> D (TyClass C \<tau>s)")
        case (Instance \<sigma>s)
        have wfD: "wf_ty \<Sigma> (TyClass D \<sigma>s)" by (rule instance_at_class_wf[OF wf_table C Instance D])
        have "\<forall>\<sigma> \<in> set (drop (length ks) (field_types \<Sigma> D \<sigma>s)). wf_ty \<Sigma> \<sigma>"
          using field_types_wf[OF wf_table wfD] by (auto dest: in_set_dropD)
        with Some Type Instance C H show ?thesis
          by (simp add: instance_at_ext[OF C D] subty_ext[OF wfD C] below_excluded_mono[OF ext D]
              field_types_ext[OF D] shapes_seq_mono[OF ext] typed_heads_mono[OF ext H wfD])
      qed (simp_all add: Some Type instance_at_ext[OF C D])
    qed (simp_all add: Some)
  qed simp
qed

lemma split_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "wf_cxt \<Sigma> \<Gamma>" and "wf_shape \<Sigma> k"
  shows "split \<Sigma>' \<Gamma> k p = split \<Sigma> \<Gamma> k p"
  using assms
proof (cases "(\<Sigma>, \<Gamma>, k, p)" rule: split.cases)
  case (6 \<Sigma>'' \<Gamma>'' \<tau> H q a)
  then have k: "k = ShapeRest \<tau> H" and p: "p = PatConstr q a" by simp_all
  from assms(3) show ?thesis unfolding k p by (intro split_rest_constr_mono[OF assms(1, 2)]) simp_all
next
  case (7 \<Sigma>'' \<Gamma>'' C \<tau>s ks H q a)
  then have k: "k = ShapeConstr C \<tau>s ks H" and p: "p = PatConstr q a" by simp_all
  from assms(3) show ?thesis unfolding k p by (intro split_constr_constr_mono[OF assms(1, 2)]) simp_all
next
  case (5 \<Sigma>'' \<Gamma>'' \<tau> \<beta> W kps)
  then have k: "k = ShapeDict \<tau> \<beta> W" and p: "p = PatDict kps" by simp_all
  have sh: "shapes \<Sigma>' \<tau> {} = shapes \<Sigma> \<tau> {}" by (rule shapes_mono[OF assms(1)]) (use assms(3) in \<open>simp_all add: k\<close>)
  show ?thesis unfolding k p by (simp only: split.simps sh)
qed (auto simp: extension.subty_ext shapes_mono shapes_seq_mono)

(* Shapes matched and remaining after a split, well-formed *)
lemma split_rest_constr_wf:
  assumes "wf_class_table \<Sigma>" and "wf_cxt \<Sigma> \<Gamma>" and "wf_ty \<Sigma> \<tau>" and "wf_heads \<Sigma> H"
    and "split \<Sigma> \<Gamma> (ShapeRest \<tau> H) (PatConstr q a) = Some (K, L)"
  shows "list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L"
proof -
  from assms(5) obtain C \<tau>s D \<sigma>s where rn: "resolve_name \<Gamma> q = Some (Type C)"
    and inst: "instance_at \<Sigma> C \<tau> = Instance \<tau>s" and m: "meet \<Sigma> \<tau> (TyClass C \<tau>s) = TyClass D \<sigma>s"
    and K: "K = map (\<lambda>ks. ShapeConstr D \<sigma>s ks (typed_heads \<Sigma> H (TyClass D \<sigma>s))) (shapes_seq \<Sigma> (field_types \<Sigma> D \<sigma>s))"
    and L: "L = shapes \<Sigma> \<tau> (insert (HeadClass C) H)"
    by (auto split: option.splits cxt_entry.splits if_splits instances.splits ty.splits)
  from resolve_name_wf[OF assms(2) rn] have C: "C |\<in>| fmdom \<Sigma>" by simp
  have wfC: "wf_ty \<Sigma> (TyClass C \<tau>s)" by (rule instance_at_class_wf[OF assms(1, 3) inst C])
  from meet_wf(1)[OF assms(3) wfC] m have wfD: "wf_ty \<Sigma> (TyClass D \<sigma>s)" by simp
  have ft: "\<forall>\<sigma> \<in> set (field_types \<Sigma> D \<sigma>s). wf_ty \<Sigma> \<sigma>" using field_types_wf[OF assms(1) wfD] by blast
  have "list_all (wf_shape \<Sigma>) K"
    unfolding K list_all_iff using wfD typed_heads_wf[OF assms(4)] shapes_seq_wf[OF _ ft] by auto
  moreover have "wf_heads \<Sigma> (insert (HeadClass C) H)" using assms(4) C by simp
  then have "list_all (wf_shape \<Sigma>) L" unfolding L list_all_iff using shapes_wf[OF _ assms(3)] by blast
  ultimately show ?thesis ..
qed

lemma split_constr_constr_wf:
  assumes "wf_class_table \<Sigma>" and "wf_cxt \<Sigma> \<Gamma>" and "wf_ty \<Sigma> (TyClass C \<tau>s)" and "list_all (wf_shape \<Sigma>) ks"
    and "wf_heads \<Sigma> H" and "split \<Sigma> \<Gamma> (ShapeConstr C \<tau>s ks H) (PatConstr q a) = Some (K, L)"
  shows "list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L"
proof -
  from assms(6) obtain D \<sigma>s where rn: "resolve_name \<Gamma> q = Some (Type D)"
    and inst: "instance_at \<Sigma> D (TyClass C \<tau>s) = Instance \<sigma>s"
    and K: "K = map (\<lambda>ks'. ShapeConstr D \<sigma>s (ks @ ks') (typed_heads \<Sigma> H (TyClass D \<sigma>s)))
                  (shapes_seq \<Sigma> (drop (length ks) (field_types \<Sigma> D \<sigma>s)))"
    and L: "L = [ShapeConstr C \<tau>s ks (insert (HeadClass D) H)]"
    by (auto split: option.splits cxt_entry.splits if_splits instances.splits)
  from resolve_name_wf[OF assms(2) rn] have D: "D |\<in>| fmdom \<Sigma>" by simp
  have wfD: "wf_ty \<Sigma> (TyClass D \<sigma>s)" by (rule instance_at_class_wf[OF assms(1, 3) inst D])
  have ft: "\<forall>\<sigma> \<in> set (drop (length ks) (field_types \<Sigma> D \<sigma>s)). wf_ty \<Sigma> \<sigma>"
    using field_types_wf[OF assms(1) wfD] by (auto dest: in_set_dropD)
  have "list_all (wf_shape \<Sigma>) K"
    unfolding K list_all_iff using wfD typed_heads_wf[OF assms(5)] shapes_seq_wf[OF _ ft] assms(4) by auto
  moreover have "list_all (wf_shape \<Sigma>) L" unfolding L using assms(3-5) D by simp
  ultimately show ?thesis ..
qed

lemma split_wf:
  assumes "wf_class_table \<Sigma>" and "wf_cxt \<Sigma> \<Gamma>" and "wf_shape \<Sigma> k" and "split \<Sigma> \<Gamma> k p = Some (K, L)"
  shows "list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L"
  using assms
proof (cases "(\<Sigma>, \<Gamma>, k, p)" rule: split.cases)
  case (6 \<Sigma>'' \<Gamma>'' \<tau> H q a)
  then have k: "k = ShapeRest \<tau> H" and p: "p = PatConstr q a" by simp_all
  from assms(3, 4) show ?thesis unfolding k p by (intro split_rest_constr_wf[OF assms(1, 2)]) simp_all
next
  case (7 \<Sigma>'' \<Gamma>'' C \<tau>s ks H q a)
  then have k: "k = ShapeConstr C \<tau>s ks H" and p: "p = PatConstr q a" by simp_all
  from assms(3, 4) show ?thesis unfolding k p by (intro split_constr_constr_wf[OF assms(1, 2)]) simp_all
next
  case (5 \<Sigma>'' \<Gamma>'' \<tau> \<beta> W kps)
  then have k: "k = ShapeDict \<tau> \<beta> W" and p: "p = PatDict kps" by simp_all
  from assms(3) have \<tau>: "wf_ty \<Sigma> \<tau>" and \<beta>: "list_all (wf_shape \<Sigma> \<circ> snd) \<beta>" by (simp_all add: k)
  from assms(4) obtain w where K: "K = map (\<lambda>k. ShapeDict \<tau> (with_keys \<beta> [w] [k]) W) (shapes \<Sigma> \<tau> {})"
    and L: "L = [ShapeDict \<tau> \<beta> (insert w W)]"
    unfolding k p by (auto split: option.splits if_splits)
  have "wf_shape \<Sigma> (ShapeDict \<tau> (with_keys \<beta> [w] [k']) W)" if "k' \<in> set (shapes \<Sigma> \<tau> {})" for k'
    using shapes_wfD[OF that _ \<tau>] \<tau> \<beta> by (simp add: with_keys_wf)
  then show ?thesis unfolding K L using \<tau> \<beta> by (auto simp: list_all_iff)
qed (auto simp: list_all_iff typed_heads_wf dest!: shapes_wfD shapes_seq_wf[unfolded list_all_iff]
     split: if_splits option.splits)

lemma those_Some: "those ms = Some rs \<Longrightarrow> ms = map Some rs"
  by (induction ms arbitrary: rs) (auto simp: map_option_eq_Some split: option.splits)

(* Shapes of a sequence match, well-formed when those at each position are and the form f preserves
   well-formedness *)
lemma seq_result_wf:
  assumes "seq_result f ks ms = Some (K, L)" and ks: "list_all (wf_shape \<Sigma>) ks"
    and ms: "\<And>K' L'. Some (K', L') \<in> set ms \<Longrightarrow> list_all (wf_shape \<Sigma>) K' \<and> list_all (wf_shape \<Sigma>) L'"
    and f: "\<And>ks'. list_all (wf_shape \<Sigma>) ks' \<Longrightarrow> wf_shape \<Sigma> (f ks')"
  shows "list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L"
proof -
  from assms(1) obtain rs where rs: "those ms = Some rs"
    and K: "K = map f (product_lists (map fst rs))"
    and L: "L = map f (concat (map (\<lambda>i. [ks' @ [l] @ drop (Suc i) ks. ks' \<leftarrow> product_lists (take i (map fst rs)),
                                                l \<leftarrow> snd (rs ! i)]) [0..<length rs]))"
    by (auto simp: seq_result_def Let_def bind_eq_Some_conv)
  have each: "list_all (wf_shape \<Sigma>) (fst r) \<and> list_all (wf_shape \<Sigma>) (snd r)" if "r \<in> set rs" for r
    using ms[of "fst r" "snd r"] those_Some[OF rs] that by auto
  have prod: "list_all (wf_shape \<Sigma>) ks'"
    if ks': "ks' \<in> set (product_lists (map fst rs'))" and sub: "set rs' \<subseteq> set rs" for ks' rs'
  proof (unfold list_all_length, intro allI impI)
    fix i
    assume i: "i < length ks'"
    from ks' have "list_all2 (\<lambda>k Ks. k \<in> set Ks) ks' (map fst rs')" by (simp add: product_lists_set)
    with i have mem: "ks' ! i \<in> set (fst (rs' ! i))" and "i < length rs'" by (auto simp: list_all2_conv_all_nth)
    from this(2) sub have "rs' ! i \<in> set rs" by (auto dest: nth_mem)
    with each mem show "wf_shape \<Sigma> (ks' ! i)" by (auto simp: list_all_iff)
  qed
  have "list_all (wf_shape \<Sigma>) K"
    unfolding K list_all_iff by (auto intro!: f prod[OF _ subset_refl])
  moreover have "list_all (wf_shape \<Sigma>) L"
    unfolding L list_all_iff
  proof (intro ballI)
    fix k
    assume "k \<in> set (map f (concat (map (\<lambda>i. [ks' @ [l] @ drop (Suc i) ks.
                                                   ks' \<leftarrow> product_lists (take i (map fst rs)),
                                                   l \<leftarrow> snd (rs ! i)]) [0..<length rs])))"
    then obtain i ks' l where i: "i < length rs" and ks': "ks' \<in> set (product_lists (take i (map fst rs)))"
      and l: "l \<in> set (snd (rs ! i))" and k: "k = f (ks' @ [l] @ drop (Suc i) ks)"
      by auto
    have "list_all (wf_shape \<Sigma>) ks'" using prod[OF ks'[unfolded take_map] set_take_subset] .
    moreover have "wf_shape \<Sigma> l" using each[OF nth_mem[OF i]] l by (simp add: list_all_iff)
    moreover have "list_all (wf_shape \<Sigma>) (drop (Suc i) ks)" using ks by (auto simp: list_all_iff dest: in_set_dropD)
    ultimately show "wf_shape \<Sigma> k" unfolding k by (intro f) simp
  qed
  ultimately show ?thesis ..
qed

lemma shapes_result_wf:
  assumes "shapes_result L ms = Some (K, L')" and "list_all (wf_shape \<Sigma>) L"
    and ms: "\<And>K' L''. Some (K', L'') \<in> set ms \<Longrightarrow> list_all (wf_shape \<Sigma>) K' \<and> list_all (wf_shape \<Sigma>) L''"
  shows "list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L'"
proof -
  let ?rs = "[r. Some r \<leftarrow> ms]"
  from assms(1) have K: "K = concat (map fst ?rs)" and L': "L' = concat (map snd ?rs) @ [k. (k, None) \<leftarrow> zip L ms]"
    by (auto simp: shapes_result_def Let_def split: if_splits)
  have rs: "list_all (wf_shape \<Sigma>) (fst r) \<and> list_all (wf_shape \<Sigma>) (snd r)" if "r \<in> set ?rs" for r
    using ms[of "fst r" "snd r"] that by (auto split: option.splits)
  have rest: "wf_shape \<Sigma> k" if "k \<in> set [k. (k, None) \<leftarrow> zip L ms]" for k
    using that assms(2) by (auto simp: list_all_iff dest!: set_zip_leftD split: option.splits)
  show ?thesis unfolding K L' using rs rest by (auto simp: list_all_iff)
qed

lemma match_shape_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_shape \<Sigma> k \<rbrakk> \<Longrightarrow> match_shape \<Sigma>' \<Gamma> k p = match_shape \<Sigma> \<Gamma> k p"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_shape \<Sigma> k' \<rbrakk> \<Longrightarrow> match_shape_upto n \<Sigma>' \<Gamma> k' p' = match_shape_upto n \<Sigma> \<Gamma> k' p'"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_shape \<Sigma> k'' \<rbrakk> \<Longrightarrow> match_directly \<Sigma>' \<Gamma> k'' p'' = match_directly \<Sigma> \<Gamma> k'' p''"
proof (induction \<Sigma> \<Gamma> k p and n \<Sigma> \<Gamma> k' p' and \<Sigma> \<Gamma> k'' p'' rule: match_shape_match_shape_upto_match_directly.induct)
  case (1 \<Sigma> \<Gamma> k p)
  from "1.IH"[OF "1.prems"] show ?case by (simp add: match_shape.simps)
next
  case (2 n \<Sigma> \<Gamma> k p)
  interpret extension \<Sigma> \<Sigma>' by fact
  have IH1: "match_directly \<Sigma>' \<Gamma> k p = match_directly \<Sigma> \<Gamma> k p" using "2.IH"(1)[OF "2.prems"] .
  note eqs = match_shape_upto.simps[of n \<Sigma>' \<Gamma> k p] match_shape_upto.simps[of n \<Sigma> \<Gamma> k p] IH1 split_mono[OF "2.prems"]
  show ?case
  proof (cases "match_directly \<Sigma> \<Gamma> k p")
    case None
    show ?thesis
    proof (cases "split \<Sigma> \<Gamma> k p")
      case (Some KL)
      obtain K L where KL: "KL = (K, L)" by (cases KL)
      show ?thesis
      proof (cases n)
        case 0
        then show ?thesis
          by (simp add: match_shape_upto.simps[of 0 \<Sigma>' \<Gamma> k p] match_shape_upto.simps[of 0 \<Sigma> \<Gamma> k p] IH1
              split_mono[OF "2.prems"] None Some)
      next
        case (Suc n')
        have "map (\<lambda>k'. match_shape_upto n' \<Sigma>' \<Gamma> k' p) K = map (\<lambda>k'. match_shape_upto n' \<Sigma> \<Gamma> k' p) K"
          using "2.IH"(2)[OF None refl Some KL[symmetric] Suc _ "2.prems"(1, 2)]
            split_wf[OF wf_table "2.prems"(2, 3) Some[unfolded KL]]
          by (intro map_cong[OF refl]) (auto simp: list_all_iff)
        then show ?thesis
          unfolding Suc
          by (simp only: match_shape_upto.simps[of "Suc n'" \<Sigma>' \<Gamma> k p] match_shape_upto.simps[of "Suc n'" \<Sigma> \<Gamma> k p]
              IH1 split_mono[OF "2.prems"] None Some KL option.case prod.case nat.case)
      qed
    qed (simp add: eqs None)
  qed (simp add: eqs)
next
  case (6 \<Sigma> \<Gamma> \<tau> H r)
  then show ?case by (simp add: extension.subty_ext)
next
  case (8 \<Sigma> \<Gamma> ks ps)
  show ?case
  proof (cases "length ks = length ps")
    case True
    have "map2 (\<lambda>k p. match_shape \<Sigma>' \<Gamma> k (node p)) ks ps = map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) ks ps"
      using "8.IH"[OF True _ refl "8.prems"(1, 2)] "8.prems"(3)
      by (intro map_cong[OF refl]) (auto simp: list_all_iff dest: set_zip_leftD)
    with True show ?thesis by (simp only: match_directly.simps if_True)
  qed simp
next
  case (9 \<Sigma> \<Gamma> \<tau> ks ps)
  show ?case
  proof (cases "length ks = length ps")
    case True
    have "map2 (\<lambda>k p. match_shape \<Sigma>' \<Gamma> k (node p)) ks ps = map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) ks ps"
      using "9.IH"[OF True _ refl "9.prems"(1, 2)] "9.prems"(3)
      by (intro map_cong[OF refl]) (auto simp: list_all_iff dest: set_zip_leftD)
    with True show ?thesis by (simp only: match_directly.simps if_True)
  qed simp
next
  case (10 \<Sigma> \<Gamma> \<tau> \<beta> W kps)
  let ?ks = "map (the \<circ> map_of \<beta> \<circ> fst) kps"
  show ?case
  proof (cases "\<forall>w \<in> set (map fst kps). w \<in> fst ` set \<beta>")
    case True
    have "map2 (\<lambda>k p. match_shape \<Sigma>' \<Gamma> k (node p)) ?ks (map snd kps)
        = map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) ?ks (map snd kps)"
    proof (intro map_cong[OF refl])
      fix kp
      assume kp: "kp \<in> set (zip ?ks (map snd kps))"
      then obtain w p where wp: "(w, p) \<in> set kps" and kp': "kp = (the (map_of \<beta> w), p)"
        by (auto simp: in_set_zip) (metis nth_map nth_mem prod.collapse)
      from wp True obtain k where k: "map_of \<beta> w = Some k" by (force simp: map_of_eq_None_iff)
      have wf: "wf_shape \<Sigma> (the (map_of \<beta> w))"
        using map_of_SomeD[OF k] "10.prems"(3) by (fastforce simp: k list_all_iff)
      show "(case kp of (k, p) \<Rightarrow> match_shape \<Sigma>' \<Gamma> k (node p)) = (case kp of (k, p) \<Rightarrow> match_shape \<Sigma> \<Gamma> k (node p))"
        unfolding kp' prod.case by (rule "10.IH"[OF True refl kp[unfolded kp'] refl "10.prems"(1, 2) wf])
    qed
    with True show ?thesis by (simp only: match_directly.simps Let_def if_True)
  qed (simp only: match_directly.simps if_False)
next
  case (11 \<Sigma> \<Gamma> C \<tau>s ks H q a)
  interpret extension \<Sigma> \<Sigma>' by fact
  have Cdom: "C |\<in>| fmdom \<Sigma>" using "11.prems"(3) by simp
  show ?case
  proof (cases "resolve_name \<Gamma> q")
    case (Some \<theta>)
    show ?thesis
    proof (cases \<theta>)
      case (Type D)
      with resolve_name_wf[OF "11.prems"(2) Some] have D: "D |\<in>| fmdom \<Sigma>" by simp
      have fp: "field_patterns \<Sigma>' D a = field_patterns \<Sigma> D a" by (rule field_patterns_mono[OF "11.prems"(1) D])
      let ?m = "length (field_patterns \<Sigma> D a)"
      show ?thesis
      proof (cases "D \<in> set (ancestors \<Sigma> C)")
        case True
        have "map2 (\<lambda>k p. match_shape \<Sigma>' \<Gamma> k (node p)) (take ?m ks) (field_patterns \<Sigma> D a)
            = map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) (take ?m ks) (field_patterns \<Sigma> D a)"
        proof (intro map_cong[OF refl])
          fix kp
          assume kp: "kp \<in> set (zip (take ?m ks) (field_patterns \<Sigma> D a))"
          obtain k p where kp': "kp = (k, p)" by (cases kp)
          have "wf_shape \<Sigma> k"
            using "11.prems"(3) set_zip_leftD[OF kp[unfolded kp']] by (auto simp: list_all_iff dest: in_set_takeD)
          then show "(case kp of (k, p) \<Rightarrow> match_shape \<Sigma>' \<Gamma> k (node p))
            = (case kp of (k, p) \<Rightarrow> match_shape \<Sigma> \<Gamma> k (node p))"
            unfolding kp' prod.case
            by (rule "11.IH"[OF Some Type refl refl True kp[unfolded kp'] refl "11.prems"(1, 2)])
        qed
        with True show ?thesis
          by (simp only: match_directly.simps Some Type option.case cxt_entry.case Let_def fp ancestors_ext[OF Cdom]
                if_True)
      qed (simp add: Some Type fp ancestors_ext[OF Cdom] Let_def)
    qed (simp_all add: Some)
  qed simp
qed (simp_all add: split_mono)

lemma seq_result_match_wf:
  assumes "seq_result f ks (map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) ks ps) = Some (K, L)"
    and "list_all (wf_shape \<Sigma>) ks"
    and IH: "\<And>k p K' L'. \<lbrakk> (k, p) \<in> set (zip ks ps) ; match_shape \<Sigma> \<Gamma> k (node p) = Some (K', L') \<rbrakk>
                \<Longrightarrow> list_all (wf_shape \<Sigma>) K' \<and> list_all (wf_shape \<Sigma>) L'"
    and f: "\<And>ks'. list_all (wf_shape \<Sigma>) ks' \<Longrightarrow> wf_shape \<Sigma> (f ks')"
  shows "list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L"
proof (rule seq_result_wf[OF assms(1, 2)])
  fix K' L'
  assume "Some (K', L') \<in> set (map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) ks ps)"
  then obtain k p where "(k, p) \<in> set (zip ks ps)" and "match_shape \<Sigma> \<Gamma> k (node p) = Some (K', L')" by auto
  from IH[OF this] show "list_all (wf_shape \<Sigma>) K' \<and> list_all (wf_shape \<Sigma>) L'" .
qed (rule f)

lemma match_shape_wf:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; wf_shape \<Sigma> k ; match_shape \<Sigma> \<Gamma> k p = Some (K, L) \<rbrakk>
  \<Longrightarrow> list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L"
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; wf_shape \<Sigma> k' ; match_shape_upto n \<Sigma> \<Gamma> k' p' = Some (K, L) \<rbrakk>
  \<Longrightarrow> list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L"
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; wf_shape \<Sigma> k'' ; match_directly \<Sigma> \<Gamma> k'' p'' = Some (K, L) \<rbrakk>
  \<Longrightarrow> list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L"
proof (induction \<Sigma> \<Gamma> k p and n \<Sigma> \<Gamma> k' p' and \<Sigma> \<Gamma> k'' p'' arbitrary: K L and K L and K L
    rule: match_shape_match_shape_upto_match_directly.induct)
  case (1 \<Sigma> \<Gamma> k p)
  from "1.prems" show ?case by (intro "1.IH") (simp_all add: match_shape.simps)
next
  case (2 n \<Sigma> \<Gamma> k p)
  show ?case
  proof (cases "match_directly \<Sigma> \<Gamma> k p")
    case None
    with "2.prems"(4) obtain K' L' n' L'' where sp: "split \<Sigma> \<Gamma> k p = Some (K', L')" and n: "n = Suc n'"
      and sr: "shapes_result K' (map (\<lambda>k'. match_shape_upto n' \<Sigma> \<Gamma> k' p) K') = Some (K, L'')" and L: "L = L' @ L''"
      by (auto simp: match_shape_upto.simps[of n \<Sigma> \<Gamma> k p] map_option_eq_Some
          split: option.splits nat.splits prod.splits)
    from split_wf[OF "2.prems"(1-3) sp] have K': "list_all (wf_shape \<Sigma>) K'" and L': "list_all (wf_shape \<Sigma>) L'"
      by auto
    have "list_all (wf_shape \<Sigma>) K'' \<and> list_all (wf_shape \<Sigma>) L'''"
      if "Some (K'', L''') \<in> set (map (\<lambda>k'. match_shape_upto n' \<Sigma> \<Gamma> k' p) K')" for K'' L'''
    proof -
      from that obtain k' where k': "k' \<in> set K'" and m: "match_shape_upto n' \<Sigma> \<Gamma> k' p = Some (K'', L''')" by auto
      from K' k' have "wf_shape \<Sigma> k'" by (simp add: list_all_iff)
      from "2.IH"(2)[OF None refl sp refl n k' "2.prems"(1, 2) this m] show ?thesis .
    qed
    from shapes_result_wf[OF sr K' this] L' show ?thesis by (simp add: L)
  qed (use "2.prems" "2.IH"(1) in \<open>auto simp: match_shape_upto.simps[of n \<Sigma> \<Gamma> k p]\<close>)
next
  case (5 \<Sigma> \<Gamma> k p x)
  from "5.prems" show ?case by (intro "5.IH") simp_all
next
  case (8 \<Sigma> \<Gamma> ks ps)
  from "8.prems"(4) have len: "length ks = length ps"
    and sr: "seq_result ShapeTuple ks (map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) ks ps) = Some (K, L)"
    by (auto split: if_splits)
  from "8.prems"(3) have ks: "list_all (wf_shape \<Sigma>) ks" by simp
  show ?case
  proof (intro seq_result_match_wf[OF sr ks])
    fix k p K' L'
    assume mem: "(k, p) \<in> set (zip ks ps)" and m: "match_shape \<Sigma> \<Gamma> k (node p) = Some (K', L')"
    from "8.prems"(3) set_zip_leftD[OF mem] have "wf_shape \<Sigma> k" by (simp add: list_all_iff)
    from "8.IH"[OF len mem refl "8.prems"(1, 2) this m] show "list_all (wf_shape \<Sigma>) K' \<and> list_all (wf_shape \<Sigma>) L'" .
  qed simp
next
  case (9 \<Sigma> \<Gamma> \<tau> ks ps)
  from "9.prems"(4) have len: "length ks = length ps"
    and sr: "seq_result (ShapeList \<tau>) ks (map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) ks ps) = Some (K, L)"
    by (auto split: if_splits)
  from "9.prems"(3) have ks: "list_all (wf_shape \<Sigma>) ks" by simp
  show ?case
  proof (intro seq_result_match_wf[OF sr ks])
    fix k p K' L'
    assume mem: "(k, p) \<in> set (zip ks ps)" and m: "match_shape \<Sigma> \<Gamma> k (node p) = Some (K', L')"
    from ks set_zip_leftD[OF mem] have "wf_shape \<Sigma> k" by (simp add: list_all_iff)
    from "9.IH"[OF len mem refl "9.prems"(1, 2) this m] show "list_all (wf_shape \<Sigma>) K' \<and> list_all (wf_shape \<Sigma>) L'" .
  qed (use "9.prems"(3) in simp)
next
  case (10 \<Sigma> \<Gamma> \<tau> \<beta> W kps)
  let ?ks = "map (the \<circ> map_of \<beta> \<circ> fst) kps"
  from "10.prems"(4) have keys: "\<forall>w \<in> set (map fst kps). w \<in> fst ` set \<beta>"
    and sr: "seq_result (\<lambda>ks'. ShapeDict \<tau> (with_keys \<beta> (map fst kps) ks') W) ?ks
               (map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) ?ks (map snd kps)) = Some (K, L)"
    by (auto simp: Let_def split: if_splits)
  have ks: "list_all (wf_shape \<Sigma>) ?ks"
  proof (intro list_all_iff[THEN iffD2] ballI)
    fix k
    assume "k \<in> set ?ks"
    then obtain kp where kp: "kp \<in> set kps" and k: "k = the (map_of \<beta> (fst kp))" by auto
    from kp keys obtain k' where "map_of \<beta> (fst kp) = Some k'" by (force simp: map_of_eq_None_iff)
    with "10.prems"(3) map_of_SomeD[OF this] show "wf_shape \<Sigma> k" by (fastforce simp: list_all_iff k)
  qed
  show ?case
  proof (intro seq_result_match_wf[OF sr ks])
    fix k p K' L'
    assume mem: "(k, p) \<in> set (zip ?ks (map snd kps))" and m: "match_shape \<Sigma> \<Gamma> k (node p) = Some (K', L')"
    from ks set_zip_leftD[OF mem] have "wf_shape \<Sigma> k" by (auto simp: list_all_iff)
    from "10.IH"[OF keys refl mem refl "10.prems"(1, 2) this m]
    show "list_all (wf_shape \<Sigma>) K' \<and> list_all (wf_shape \<Sigma>) L'" .
  qed (use "10.prems"(3) in \<open>auto intro: with_keys_wf\<close>)
next
  case (11 \<Sigma> \<Gamma> C \<tau>s ks H q a)
  from "11.prems"(4) obtain D where rn: "resolve_name \<Gamma> q = Some (Type D)" and anc: "D \<in> set (ancestors \<Sigma> C)"
    and sr: "seq_result (\<lambda>ks'. ShapeConstr C \<tau>s (ks' @ drop (length (field_patterns \<Sigma> D a)) ks) H)
               (take (length (field_patterns \<Sigma> D a)) ks)
               (map2 (\<lambda>k p. match_shape \<Sigma> \<Gamma> k (node p)) (take (length (field_patterns \<Sigma> D a)) ks)
                  (field_patterns \<Sigma> D a)) = Some (K, L)"
    by (auto simp: Let_def split: option.splits cxt_entry.splits if_splits)
  let ?m = "length (field_patterns \<Sigma> D a)"
  from "11.prems"(3) have wfC: "wf_ty \<Sigma> (TyClass C \<tau>s)" and ks: "list_all (wf_shape \<Sigma>) ks" and H: "wf_heads \<Sigma> H"
    by simp_all
  have take: "list_all (wf_shape \<Sigma>) (take ?m ks)" using ks by (auto simp: list_all_iff dest: in_set_takeD)
  show ?case
  proof (intro seq_result_match_wf[OF sr take])
    fix k p K' L'
    assume mem: "(k, p) \<in> set (zip (take ?m ks) (field_patterns \<Sigma> D a))"
      and m: "match_shape \<Sigma> \<Gamma> k (node p) = Some (K', L')"
    from take set_zip_leftD[OF mem] have "wf_shape \<Sigma> k" by (simp add: list_all_iff)
    from "11.IH"[OF rn refl refl refl anc mem refl "11.prems"(1, 2) this m]
    show "list_all (wf_shape \<Sigma>) K' \<and> list_all (wf_shape \<Sigma>) L'" .
  qed (use wfC ks H in \<open>auto simp: list_all_iff dest: in_set_dropD\<close>)
qed (auto split: if_splits)

lemma match_shapes_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; list_all (wf_shape \<Sigma>) L \<rbrakk> \<Longrightarrow> match_shapes \<Sigma>' \<Gamma> L p = match_shapes \<Sigma> \<Gamma> L p"
  unfolding match_shapes_def
  by (intro arg_cong[where f = "shapes_result L"] map_cong[OF refl] match_shape_mono(1)) (auto simp: list_all_iff)

lemma match_shapes_wf:
  assumes "wf_class_table \<Sigma>" and "wf_cxt \<Sigma> \<Gamma>" and "list_all (wf_shape \<Sigma>) L"
    and "match_shapes \<Sigma> \<Gamma> L p = Some (K, L')"
  shows "list_all (wf_shape \<Sigma>) K \<and> list_all (wf_shape \<Sigma>) L'"
proof (rule shapes_result_wf[OF assms(4)[unfolded match_shapes_def] assms(3)])
  fix K' L''
  assume "Some (K', L'') \<in> set (map (\<lambda>k. match_shape \<Sigma> \<Gamma> k p) L)"
  then obtain k where "k \<in> set L" and "match_shape \<Sigma> \<Gamma> k p = Some (K', L'')" by auto
  with assms(3) show "list_all (wf_shape \<Sigma>) K' \<and> list_all (wf_shape \<Sigma>) L''"
    by (intro match_shape_wf(1)[OF assms(1, 2)]) (auto simp: list_all_iff)
qed

subsection \<open>Expressions\<close>

lemma synth_Ok_wf: "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  using synth_wf(1) by blast

lemma synth_at_Ok_wf: "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  using synth_wf(2) by blast

lemma elements_join_Ok_wf: "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; elements_join \<Sigma> \<Gamma> es = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  using synth_wf(3) by blast

lemma callee_Ok_wf: "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; callee \<Sigma> \<Gamma> e es = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  using synth_wf(4) by blast

lemma synth_call_Ok_wf: "\<lbrakk> wf_ty \<Sigma> \<sigma> ; synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  using synth_wf(5) by blast

lemma quals_Ok_wf: "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; quals \<Sigma> \<Gamma> gs = Ok \<Delta> \<rbrakk> \<Longrightarrow> wf_cxt \<Sigma> \<Delta>"
  using synth_wf(10) by blast

lemma params_cxt_Ok_wf: "\<lbrakk> params_cxt xs \<tau>s = Ok \<Delta> ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_cxt \<Sigma> \<Delta>"
  using params_cxt_wf[where V = UNIV] by blast

lemma lambda_args_Ok_wf:
  assumes "wf_class_table \<Sigma>" and "wf_cxt \<Sigma> \<Gamma>" and "lambda_args e xs kws es (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<Delta>"
  shows "wf_cxt \<Sigma> \<Delta>"
proof -
  from assms(3) obtain \<tau>s where \<tau>s: "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
    and \<Delta>: "params_cxt xs \<tau>s = Ok \<Delta>"
    by (auto simp: lambda_args_def bind_sum_Ok)
  have "wf_ty \<Sigma> \<tau>" if "\<tau> \<in> set \<tau>s" for \<tau>
    using those_sum_map_Ok_elem[OF \<tau>s that] synth_at_Ok_wf[OF assms(1, 2)] by blast
  then show ?thesis using params_cxt_Ok_wf[OF \<Delta>] by blast
qed

lemma inferred_type_args_Ok_wf:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; inferred_type_args \<Sigma> \<alpha>s \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s \<rbrakk>
  \<Longrightarrow> \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>"
  using inferred_type_args_wf[where V = UNIV] by (fastforce intro: synth_at_Ok_wf)

(* Type of the field supplied by a constructor argument, well-formed *)
lemma constructor_arg_wf:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "fields \<Sigma> C = FieldScheme \<alpha>s x\<sigma>s"
    and "constructor_args C (FieldScheme \<alpha>s x\<sigma>s) es kws = Ok \<sigma>es" and "(\<sigma>, e') \<in> set \<sigma>es"
  shows "wf_ty \<Sigma> \<sigma>"
proof -
  have \<alpha>s: "\<alpha>s = type_params \<Sigma> C" using assms(3) fields_ancestor_fields[of \<Sigma> C] by simp
  have wf: "wf_ty \<Sigma> (TyClass C (map TyVar \<alpha>s))" using assms(2) \<alpha>s by simp
  from constructor_args_field[OF assms(4, 5)] obtain x where "(x, \<sigma>) \<in> set x\<sigma>s" by auto
  then have "(x, \<sigma>) \<in> set (instantiate (fields \<Sigma> C) (map TyVar \<alpha>s))" by (simp add: assms(3) subst_TyVar)
  from fields_wf[OF assms(1) wf this] show ?thesis .
qed

lemma inferred_type_args_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>" and ms: "\<And>\<tau>. Ok \<tau> \<in> set ms \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  shows "inferred_type_args \<Sigma>' \<alpha>s \<sigma>s ms = inferred_type_args \<Sigma> \<alpha>s \<sigma>s ms"
proof -
  interpret extension \<Sigma> \<Sigma>' by fact
  let ?\<sigma>\<tau>s = "filter (Not \<circ> isl \<circ> snd) (zip \<sigma>s ms)"
  have "\<forall>\<sigma> \<in> set (map fst ?\<sigma>\<tau>s). wf_ty \<Sigma> \<sigma>" using assms(2) by (auto dest: set_zip_leftD)
  moreover have "\<forall>\<tau> \<in> set (map (projr \<circ> snd) ?\<sigma>\<tau>s). wf_ty \<Sigma> \<tau>"
  proof
    fix \<tau>
    assume "\<tau> \<in> set (map (projr \<circ> snd) ?\<sigma>\<tau>s)"
    then obtain m where "m \<in> set ms" and "\<not> isl m" and "\<tau> = projr m" by (auto dest: set_zip_rightD)
    then have "Ok \<tau> \<in> set ms" by (cases m) auto
    then show "wf_ty \<Sigma> \<tau>" by (rule ms)
  qed
  ultimately show ?thesis unfolding inferred_type_args_def Let_def by (simp only: type_args_seq_ext)
qed

lemma var_scheme_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "wf_cxt \<Sigma> \<Gamma>" and "wf_ty \<Sigma> \<tau>"
  shows "var_scheme \<Sigma>' \<Gamma> e \<tau> = var_scheme \<Sigma> \<Gamma> e \<tau>"
proof -
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?thesis
  proof (cases "scheme_of_name \<Gamma> e")
    case (Some \<pi>)
    obtain \<alpha>s \<sigma> where \<pi>: "\<pi> = TyScheme \<alpha>s \<sigma>" by (cases \<pi>)
    from scheme_of_name_wf[OF assms(2) Some[unfolded \<pi>]] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" by blast
    have wf_subst: "wf_ty \<Sigma> (subst \<tau>s \<alpha>s \<sigma>)" if "type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s" for \<tau>s
    proof (rule wf_ty_subst[OF wf\<sigma>], intro ballI)
      fix \<tau>'
      assume "\<tau>' \<in> set \<tau>s"
      from type_args_of_elem[OF that this] obtain \<alpha> where "fmlookup (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha> = Some \<tau>'" ..
      with type_args_bindings_wf[OF assms(3), of \<alpha>s \<sigma>] show "wf_ty \<Sigma> \<tau>'" by (simp add: wf_bindings_def)
    qed
    show ?thesis
      by (simp add: var_scheme_def Some \<pi> Let_def type_args_ext[OF wf\<sigma> assms(3)] subty_ext[OF wf_subst assms(3)]
          mismatch_ext[OF wf_subst] cong: bind_sum_cong)
  qed (simp add: var_scheme_def)
qed

lemma constructor_class_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "wf_cxt \<Sigma> \<Gamma>"
  shows "constructor_class \<Sigma>' \<Gamma> e = constructor_class \<Sigma> \<Gamma> e"
  unfolding constructor_class_def by (simp only: extension.resolve_type_ext[OF assms])

(* Class table lemmas as conditional rewrite rules for the stability proofs *)
lemmas ext_simps =
  extension.wf_table extension.subty_ext extension.join_ext extension.joins_ext extension.meet_ext
  extension.elem_type_ext extension.subscript_type_ext extension.attribute_type_ext extension.mismatch_ext
  extension.resolve_binop_union_ext extension.resolve_unop_ext extension.resolve_type_ext extension.fields_ext
  extension.wf_ty_ext synth_Ok_wf synth_at_Ok_wf elements_join_Ok_wf callee_Ok_wf synth_call_Ok_wf quals_Ok_wf
  wf_cxt_add var_scheme_mono constructor_class_mono joins_wf base_type_wf elem_type_wf

lemma synth_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> synth_expr \<Sigma>' \<Gamma> e = synth_expr \<Sigma> \<Gamma> e"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> synth_expr_at \<Sigma>' \<Gamma> e' = synth_expr_at \<Sigma> \<Gamma> e'"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> elements_join \<Sigma>' \<Gamma> es = elements_join \<Sigma> \<Gamma> es"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> callee \<Sigma>' \<Gamma> e' es = callee \<Sigma> \<Gamma> e' es"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<sigma> \<rbrakk> \<Longrightarrow> synth_call \<Sigma>' \<Gamma> e' \<sigma> kws es = synth_call \<Sigma> \<Gamma> e' \<sigma> kws es"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau>\<^sub>0 \<rbrakk> \<Longrightarrow> check_expr \<Sigma>' \<Gamma> e \<tau>\<^sub>0 = check_expr \<Sigma> \<Gamma> e \<tau>\<^sub>0"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau>\<^sub>0 \<rbrakk> \<Longrightarrow> check_expr_at \<Sigma>' \<Gamma> e' \<tau>\<^sub>0 = check_expr_at \<Sigma> \<Gamma> e' \<tau>\<^sub>0"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau>\<^sub>0 \<rbrakk> \<Longrightarrow> check_expr' \<Sigma>' \<Gamma> e \<tau>\<^sub>0 = check_expr' \<Sigma> \<Gamma> e \<tau>\<^sub>0"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; \<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma> \<rbrakk>
  \<Longrightarrow> check_args \<Sigma>' \<Gamma> e' kws es \<sigma>s = check_args \<Sigma> \<Gamma> e' kws es \<sigma>s"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> quals \<Sigma>' \<Gamma> gs = quals \<Sigma> \<Gamma> gs"
proof (induction \<Sigma> \<Gamma> e and \<Sigma> \<Gamma> e' and \<Sigma> \<Gamma> es and \<Sigma> \<Gamma> e' es and \<Sigma> \<Gamma> e' \<sigma> kws es and \<Sigma> \<Gamma> e \<tau>\<^sub>0
    and \<Sigma> \<Gamma> e' \<tau>\<^sub>0 and \<Sigma> \<Gamma> e \<tau>\<^sub>0 and \<Sigma> \<Gamma> e' kws es \<sigma>s and \<Sigma> \<Gamma> gs
    rule:
  synth_expr_synth_expr_at_elements_join_callee_synth_call_check_expr_check_expr_at_check_expr'_check_args_quals.induct)
  case (3 \<Sigma> \<Gamma> e es kws)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
  proof (cases "lambda_of (node e)")
    case (Some xe)
    then obtain xs e' where lam: "lambda_of (node e) = Some (xs, e')" by (cases xe) simp
    have args: "map (synth_expr_at \<Sigma>' \<Gamma>) es = map (synth_expr_at \<Sigma> \<Gamma>) es"
      using "3.IH"(6)[OF lam refl _ "3.prems"] by (intro map_cong[OF refl])
    have body: "synth_expr_at \<Sigma>' (\<Gamma> \<otimes> \<Delta>) e' = synth_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e'"
      if "lambda_args e xs kws es (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<Delta>" for \<Delta>
      using "3.IH"(7)[OF lam refl that "3.prems"(1)] lambda_args_Ok_wf[OF wf_table "3.prems"(2) that] "3.prems"(2)
      by (simp add: wf_cxt_add)
    show ?thesis by (simp add: lam args body cong: bind_sum_cong)
  next
    case None
    note lam = None
    show ?thesis
    proof (cases "constructor_class \<Sigma> \<Gamma> e")
      case (Some m)
      note Some_m = Some
      have cc: "constructor_class \<Sigma>' \<Gamma> e = Some m" using Some by (simp add: constructor_class_mono[OF "3.prems"])
      show ?thesis
      proof (cases m)
        case (Inr Ce)
        obtain C explicit where m: "m = Ok (C, explicit)" using Inr by (cases Ce) simp
        from constructor_class_Ok[OF Some_m[unfolded m]] "3.prems"(2) have C: "C |\<in>| fmdom \<Sigma>"
          by (auto dest: class_of_name_dom)
        obtain x\<sigma>s where fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
          by (simp add: fields_ancestor_fields)
        let ?\<alpha>s = "type_params \<Sigma> C"
        have arg_wf: "wf_ty \<Sigma> \<sigma>"
          if "constructor_args C (FieldScheme ?\<alpha>s x\<sigma>s) es kws = Ok \<sigma>es" and "(\<sigma>, e') \<in> set \<sigma>es"
          for \<sigma>es \<sigma> e'
          using constructor_arg_wf[OF wf_table C fields that] .
        have explicit_wf: "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>" if "explicit = Some \<tau>s" for \<tau>s
        proof -
          from constructor_class_Ok[OF Some_m[unfolded m]] that
          obtain \<psi> where "resolve_type \<Sigma> \<Gamma> \<psi> = Ok (TyClass C \<tau>s)"
            by auto
          from resolve_type_wf[OF "3.prems"(2) this] show ?thesis by simp
        qed
        have synth_args: "map (synth_expr_at \<Sigma>' \<Gamma> \<circ> snd) \<sigma>es = map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es"
          if cargs: "constructor_args C (FieldScheme ?\<alpha>s x\<sigma>s) es kws = Ok \<sigma>es" and "explicit = None" for \<sigma>es
          using "3.IH"(3)[OF lam Some_m m refl fields cargs that(2) _ "3.prems"] by (intro map_cong[OF refl]) simp
        have inferred: "inferred_type_args \<Sigma>' ?\<alpha>s (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es)
                      = inferred_type_args \<Sigma> ?\<alpha>s (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es)"
          if cargs: "constructor_args C (FieldScheme ?\<alpha>s x\<sigma>s) es kws = Ok \<sigma>es" for \<sigma>es
          using arg_wf[OF cargs]
          by (intro inferred_type_args_mono[OF "3.prems"(1)]) (auto intro: synth_at_Ok_wf[OF wf_table "3.prems"(2)])
        have checks: "map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma>' \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>)) \<sigma>es
                    = map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>)) \<sigma>es"
          if cargs: "constructor_args C (FieldScheme ?\<alpha>s x\<sigma>s) es kws = Ok \<sigma>es" and \<tau>s: "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>"
          and IH: "\<And>\<sigma> e'. (\<sigma>, e') \<in> set \<sigma>es \<Longrightarrow> extension \<Sigma> \<Sigma>' \<Longrightarrow> wf_cxt \<Sigma> \<Gamma> \<Longrightarrow> wf_ty \<Sigma> (subst \<tau>s ?\<alpha>s \<sigma>)
                  \<Longrightarrow> check_expr_at \<Sigma>' \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>) = check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>)"
          for \<sigma>es \<tau>s
        proof (intro map_cong[OF refl])
          fix \<sigma>e
          assume \<sigma>e: "\<sigma>e \<in> set \<sigma>es"
          obtain \<sigma> e' where \<sigma>e': "\<sigma>e = (\<sigma>, e')" by (cases \<sigma>e)
          have mem: "(\<sigma>, e') \<in> set \<sigma>es" using \<sigma>e by (simp add: \<sigma>e')
          have "wf_ty \<Sigma> (subst \<tau>s ?\<alpha>s \<sigma>)" using wf_ty_subst[OF arg_wf[OF cargs mem] \<tau>s] .
          then show "(case \<sigma>e of (\<sigma>, e') \<Rightarrow> check_expr_at \<Sigma>' \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>))
                   = (case \<sigma>e of (\<sigma>, e') \<Rightarrow> check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>))"
            unfolding \<sigma>e' prod.case by (rule IH[OF mem "3.prems"])
        qed
        show ?thesis
        proof (cases explicit)
          case (Some \<tau>s)
          have eq: "those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma>' \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>)) \<sigma>es)
                  = those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>)) \<sigma>es)"
            if cargs: "constructor_args C (FieldScheme ?\<alpha>s x\<sigma>s) es kws = Ok \<sigma>es" for \<sigma>es
            by (intro arg_cong[where f = those_sum]
                checks[OF cargs explicit_wf[OF Some] "3.IH"(5)[OF lam Some_m m refl fields cargs Some _ refl]])
          show ?thesis
            unfolding synth_expr.simps lam option.case cc Some_m m bind_sum_simps prod.case fields_ext[OF C] fields
              field_scheme.case Some
            by (intro arg_cong[where f = "by_rule RuleConstrExplicit"] bind_sum_cong[OF refl]) (simp add: eq)
        next
          case None
          have eq: "do {
              \<tau>s \<leftarrow> inferred_type_args \<Sigma> ?\<alpha>s (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es);
              those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma>' \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>)) \<sigma>es);
              Ok (TyClass C \<tau>s)
            } = do {
              \<tau>s \<leftarrow> inferred_type_args \<Sigma> ?\<alpha>s (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es);
              those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>)) \<sigma>es);
              Ok (TyClass C \<tau>s)
            }"
            if cargs: "constructor_args C (FieldScheme ?\<alpha>s x\<sigma>s) es kws = Ok \<sigma>es" for \<sigma>es
          proof (rule bind_sum_cong[OF refl])
            fix \<tau>s
            assume inf: "inferred_type_args \<Sigma> ?\<alpha>s (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
            have \<tau>s: "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>" using inferred_type_args_Ok_wf[OF wf_table "3.prems"(2) inf] .
            show "do { those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma>' \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>)) \<sigma>es); Ok (TyClass C \<tau>s) }
                = do { those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s ?\<alpha>s \<sigma>)) \<sigma>es); Ok (TyClass C \<tau>s) }"
              by (simp only: checks[OF cargs \<tau>s "3.IH"(4)[OF lam Some_m m refl fields cargs None inf _ refl]])
          qed
          show ?thesis
            unfolding synth_expr.simps lam option.case cc Some_m m bind_sum_simps prod.case fields_ext[OF C] fields
              field_scheme.case None
            by (intro arg_cong[where f = "by_rule RuleConstr"] bind_sum_cong[OF refl])
               (simp only: synth_args[OF _ None] inferred eq)
        qed
      qed (simp add: lam cc Some_m)
    next
      case cc: None
      have cc': "constructor_class \<Sigma>' \<Gamma> e = None" using cc by (simp add: constructor_class_mono[OF "3.prems"])
      show ?thesis
        using "3.IH"(1)[OF lam cc "3.prems"] "3.IH"(2)[OF lam cc _ "3.prems"] callee_Ok_wf[OF wf_table "3.prems"(2)]
        by (simp add: lam cc cc' cong: bind_sum_cong)
    qed
  qed
next
  case (8 \<Sigma> \<Gamma> e\<^sub>1 e e\<^sub>2)
  interpret extension \<Sigma> \<Sigma>' by fact
  have chk: "check_expr_at \<Sigma>' \<Gamma> e (TyPrim bool) = check_expr_at \<Sigma> \<Gamma> e (TyPrim bool)"
    using "8.IH"(1)[OF "8.prems"] by simp
  show ?case
  proof (cases "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool)")
    case (Inr u)
    note IH = "8.IH"(2)[OF Inr "8.prems"] "8.IH"(3)[OF Inr "8.prems"]
    show ?thesis
      using "8.IH"(4)[OF Inr refl _ _ "8.prems"(1, 2)] "8.IH"(5)[OF Inr refl _ _ "8.prems"(1, 2)]
        synth_at_Ok_wf[OF wf_table "8.prems"(2)]
      by (auto simp: chk IH join_ext split: sum.splits)
  qed (simp add: chk)
next
  case (22 \<Sigma> \<Gamma> es)
  interpret extension \<Sigma> \<Sigma>' by fact
  let ?\<sigma>s = "map (synth_expr_at \<Sigma> \<Gamma>) es"
  let ?\<tau> = "joins \<Sigma> (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s))"
  have \<sigma>s: "map (synth_expr_at \<Sigma>' \<Gamma>) es = ?\<sigma>s" using "22.IH"(1)[OF _ "22.prems"] by (intro map_cong[OF refl])
  have wf: "\<forall>\<rho> \<in> set (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s)). wf_ty \<Sigma> \<rho>"
  proof
    fix \<rho>
    assume "\<rho> \<in> set (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s))"
    then obtain e'' where "e'' \<in> set es" and nl: "\<not> isl (synth_expr_at \<Sigma> \<Gamma> e'')"
      and \<rho>: "\<rho> = base_type (projr (synth_expr_at \<Sigma> \<Gamma> e''))"
      by auto
    from nl obtain \<sigma> where "synth_expr_at \<Sigma> \<Gamma> e'' = Ok \<sigma>" by (cases "synth_expr_at \<Sigma> \<Gamma> e''") auto
    with synth_at_Ok_wf[OF wf_table "22.prems"(2) this] show "wf_ty \<Sigma> \<rho>" by (simp add: \<rho> base_type_wf)
  qed
  have \<tau>: "joins \<Sigma>' (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s)) = ?\<tau>" by (rule joins_ext[OF wf])
  have eq: "map (\<lambda>(e, _). check_expr_at \<Sigma>' \<Gamma> e ?\<tau>) (filter (isl \<circ> snd) (zip es ?\<sigma>s))
          = map (\<lambda>(e, _). check_expr_at \<Sigma> \<Gamma> e ?\<tau>) (filter (isl \<circ> snd) (zip es ?\<sigma>s))"
    if "\<not> list_all isl ?\<sigma>s"
  proof (intro map_cong[OF refl])
    fix em
    assume em: "em \<in> set (filter (isl \<circ> snd) (zip es ?\<sigma>s))"
    obtain e'' m where em': "em = (e'', m)" by (cases em)
    show "(case em of (e, _) \<Rightarrow> check_expr_at \<Sigma>' \<Gamma> e ?\<tau>) = (case em of (e, _) \<Rightarrow> check_expr_at \<Sigma> \<Gamma> e ?\<tau>)"
      unfolding em' prod.case
      by (rule "22.IH"(2)[OF refl refl that em[unfolded em'] refl "22.prems" joins_wf[OF wf]])
  qed
  show ?case unfolding elements_join.simps Let_def \<sigma>s \<tau> by (cases "list_all isl ?\<sigma>s") (simp_all add: eq)
next
  case (23 \<Sigma> \<Gamma> e \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
    using "23.IH"(1)[OF "23.prems"] "23.IH"(2)[OF _ "23.prems"(1, 2)] "23.IH"(3)[OF _ _ "23.prems"(1, 2)]
      synth_Ok_wf[OF wf_table "23.prems"(2)] "23.prems"(3)
    unfolding check_expr.simps
    by (auto simp: subty_ext mismatch_ext split: option.splits sum.splits cong: bind_sum_cong)
next
  case (34 \<Sigma> \<Gamma> e kws es \<sigma>s)
  show ?case
  proof (cases "kws = [] \<and> length \<sigma>s = length es")
    case True
    have eq: "map2 (check_expr_at \<Sigma>' \<Gamma>) es \<sigma>s = map2 (check_expr_at \<Sigma> \<Gamma>) es \<sigma>s"
      using "34.IH"[OF _ _ _ refl "34.prems"(1, 2)] "34.prems"(3) True
      by (intro map_cong[OF refl]) (auto dest: set_zip_rightD simp: ensure_def)
    show ?thesis unfolding check_args.simps eq by (simp add: ensure_def True)
  qed (auto simp: check_args.simps ensure_def)
next
  case (4 \<Sigma> \<Gamma> op e e')
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
    using "4.IH"(1)[OF "4.prems"] "4.IH"(2)[OF _ "4.prems"] synth_at_Ok_wf[OF wf_table "4.prems"(2)]
    by (simp add: resolve_binop_union_ext cong: bind_sum_cong)
next
  case (5 \<Sigma> \<Gamma> op e)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
    using "5.IH"[OF _ "5.prems"] synth_at_Ok_wf[OF wf_table "5.prems"(2)]
    by (simp add: resolve_unop_ext cong: bind_sum_cong)
next
  case (6 \<Sigma> \<Gamma> e e')
  then show ?case by (simp add: "6.IH"(1)[OF "6.prems"] "6.IH"(2)[OF _ "6.prems"(1, 2)] cong: bind_sum_cong)
next
  case (7 \<Sigma> \<Gamma> e e')
  then show ?case by (simp add: "7.IH"(1)[OF "7.prems"] "7.IH"(2)[OF _ "7.prems"(1, 2)] cong: bind_sum_cong)
next
  case (9 \<Sigma> \<Gamma> es)
  then show ?case by (simp add: "9.IH"[OF _ "9.prems"] cong: bind_sum_cong)
next
  case (10 \<Sigma> \<Gamma> es)
  then show ?case by (simp add: "10.IH"[OF _ "10.prems"] cong: map_cong)
next
  case (11 \<Sigma> \<Gamma> e x)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
    using "11.IH"[OF _ "11.prems"] synth_at_Ok_wf[OF wf_table "11.prems"(2)]
    by (simp add: attribute_type_ext split: option.splits cong: bind_sum_cong)
next
  case (12 \<Sigma> \<Gamma> e e')
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
    using "12.IH"(1)[OF "12.prems"] "12.IH"(2)[OF _ "12.prems"(1, 2)] "12.IH"(3)[OF _ "12.prems"(1, 2)]
      "12.IH"(4)[OF _ "12.prems"] synth_at_Ok_wf[OF wf_table "12.prems"(2)]
    by (simp add: subscript_type_ext cong: bind_sum_cong)
next
  case (13 \<Sigma> \<Gamma> kvs)
  then show ?case
    by (simp add: "13.IH"(1)[OF _ _ "13.prems"(1, 2)] "13.IH"(2)[OF _ _ "13.prems"] cong: bind_sum_cong map_cong)
next
  case (14 \<Sigma> \<Gamma> e gs)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
    using "14.IH"(1)[OF "14.prems"] "14.IH"(2)[OF _ _ "14.prems"(1)] quals_Ok_wf[OF wf_table "14.prems"(2)]
      "14.prems"(2)
    by (simp add: wf_cxt_add cong: bind_sum_cong)
next
  case (15 \<Sigma> \<Gamma> e e' gs)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
    using "15.IH"(1)[OF "15.prems"] "15.IH"(2)[OF _ _ "15.prems"(1)] "15.IH"(3)[OF _ _ _ "15.prems"(1)]
      quals_Ok_wf[OF wf_table "15.prems"(2)] "15.prems"(2)
    by (simp add: wf_cxt_add cong: bind_sum_cong)
next
  case (17 \<Sigma> \<Gamma> p e)
  then show ?case by (simp add: "17.IH")
next
  case (18 \<Sigma> \<Gamma> e es)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
  proof (cases "scheme_of_name \<Gamma> (node e)")
    case None
    then show ?thesis by (simp add: callee.simps "18.IH"(1)[OF None "18.prems"])
  next
    case (Some \<pi>)
    then obtain \<alpha>s \<sigma>\<^sub>0 where \<pi>: "\<pi> = TyScheme \<alpha>s \<sigma>\<^sub>0" by (cases \<pi>)
    from scheme_of_name_wf[OF "18.prems"(2) Some[unfolded \<pi>]] obtain \<sigma>s \<sigma>
      where \<sigma>\<^sub>0: "\<sigma>\<^sub>0 = TyCallable \<sigma>s \<sigma>" and wf: "wf_ty \<Sigma> (TyCallable \<sigma>s \<sigma>)"
      by auto
    have args: "map (synth_expr_at \<Sigma>' \<Gamma>) es = map (synth_expr_at \<Sigma> \<Gamma>) es"
      using "18.IH"(2)[OF Some[unfolded \<pi> \<sigma>\<^sub>0] refl refl _ "18.prems"] by (intro map_cong[OF refl])
    have "inferred_type_args \<Sigma>' \<alpha>s \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma>) es)
        = inferred_type_args \<Sigma> \<alpha>s \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma>) es)"
      using wf
      by (intro inferred_type_args_mono[OF "18.prems"(1)]) (auto intro: synth_at_Ok_wf[OF wf_table "18.prems"(2)])
    then show ?thesis by (simp add: callee.simps Some \<pi> \<sigma>\<^sub>0 args)
  qed
next
  case (19 \<Sigma> \<Gamma> e \<sigma> \<sigma>' kws es)
  interpret extension \<Sigma> \<Sigma>' by fact
  from "19.prems"(3) have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" and wf\<sigma>': "wf_ty \<Sigma> \<sigma>'" by simp_all
  show ?case
    using "19.IH"(1)[OF "19.prems"(1, 2) wf\<sigma>] "19.IH"(2)[OF _ "19.prems"(1, 2) wf\<sigma>'] synth_call_Ok_wf[OF wf\<sigma>]
      synth_call_Ok_wf[OF wf\<sigma>']
    by (simp add: join_ext cong: bind_sum_cong)
next
  case (20 \<Sigma> \<Gamma> e \<sigma>s \<tau> kws es)
  then show ?case by (simp add: "20.IH"[OF "20.prems"(1, 2)] cong: bind_sum_cong)
next
  case (24 \<Sigma> \<Gamma> p e \<tau>)
  then show ?case by (simp add: "24.IH")
next
  case (25 \<Sigma> \<Gamma> xs e \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
  proof (cases \<tau>)
    case (TyCallable \<tau>s \<tau>')
    with "25.prems"(3) have wf: "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>" and wf': "wf_ty \<Sigma> \<tau>'" by simp_all
    show ?thesis
      using "25.IH"[OF TyCallable _ _ "25.prems"(1)] params_cxt_Ok_wf[OF _ wf] "25.prems"(2) wf'
      by (simp add: TyCallable wf_cxt_add cong: bind_sum_cong)
  qed simp_all
next
  case (26 \<Sigma> \<Gamma> e es kws \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
  proof (cases "lambda_of (node e)")
    case (Some xe)
    then obtain xs e' where lam: "lambda_of (node e) = Some (xs, e')" by (cases xe) simp
    have args: "map (synth_expr_at \<Sigma>' \<Gamma>) es = map (synth_expr_at \<Sigma> \<Gamma>) es"
      using "26.IH"(1)[OF lam refl _ "26.prems"(1, 2)] by (intro map_cong[OF refl])
    have body: "check_expr_at \<Sigma>' (\<Gamma> \<otimes> \<Delta>) e' \<tau> = check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau>"
      if "lambda_args e xs kws es (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<Delta>" for \<Delta>
      using "26.IH"(2)[OF lam refl that "26.prems"(1) _ "26.prems"(3)]
        lambda_args_Ok_wf[OF wf_table "26.prems"(2) that]
        "26.prems"(2)
      by (simp add: wf_cxt_add)
    show ?thesis by (simp add: lam args body cong: bind_sum_cong)
  qed simp
next
  case (27 \<Sigma> \<Gamma> es \<tau>)
  then show ?case by (cases \<tau>) (simp_all add: "27.IH"[OF _ _ "27.prems"(1, 2)] cong: map_cong)
next
  case (28 \<Sigma> \<Gamma> es \<tau>)
  show ?case
  proof (cases \<tau>)
    case (TyTuple \<tau>s)
    show ?thesis
    proof (cases "length es = length \<tau>s")
      case True
      have eq: "map2 (check_expr_at \<Sigma>' \<Gamma>) es \<tau>s = map2 (check_expr_at \<Sigma> \<Gamma>) es \<tau>s"
        using "28.IH"[OF TyTuple True _ refl "28.prems"(1, 2)] "28.prems"(3)
        by (intro map_cong[OF refl]) (auto simp: TyTuple dest: set_zip_rightD)
      show ?thesis unfolding TyTuple check_expr'.simps ty.case eq by (rule refl)
    qed (simp add: TyTuple)
  qed simp_all
next
  case (29 \<Sigma> \<Gamma> e\<^sub>1 e e\<^sub>2 \<tau>)
  then show ?case
    by (simp add: "29.IH"(1)[OF "29.prems"(1, 2)] "29.IH"(2)[OF _ "29.prems"] "29.IH"(3)[OF _ _ "29.prems"]
        cong: bind_sum_cong)
next
  case (30 \<Sigma> \<Gamma> kvs \<tau>)
  then show ?case
    by (cases \<tau>)
       (simp_all add: "30.IH"(1)[OF _ _ "30.prems"(1, 2)] "30.IH"(2)[OF _ _ _ "30.prems"(1, 2)]
        cong: bind_sum_cong map_cong)
next
  case (31 \<Sigma> \<Gamma> e gs \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
  proof (cases \<tau>)
    case (TyList \<tau>')
    then show ?thesis
      using "31.IH"(1)[OF TyList "31.prems"(1, 2)] "31.IH"(2)[OF TyList _ _ "31.prems"(1)]
        quals_Ok_wf[OF wf_table "31.prems"(2)] "31.prems"(2, 3)
      by (simp add: wf_cxt_add cong: bind_sum_cong)
  qed simp_all
next
  case (32 \<Sigma> \<Gamma> e e' gs \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
  proof (cases \<tau>)
    case (TyDict \<tau>')
    then show ?thesis
      using "32.IH"(1)[OF TyDict "32.prems"(1, 2)] "32.IH"(2)[OF TyDict _ _ "32.prems"(1)]
        "32.IH"(3)[OF TyDict _ _ _ "32.prems"(1)] quals_Ok_wf[OF wf_table "32.prems"(2)] "32.prems"(2, 3)
      by (simp add: wf_cxt_add cong: bind_sum_cong)
  qed simp_all
next
  case (36 \<Sigma> \<Gamma> p e gs)
  then show ?case by (simp add: "36.IH"(1)[OF "36.prems"] "36.IH"(2)[OF _ "36.prems"] cong: bind_sum_cong)
next
  case (37 \<Sigma> \<Gamma> p x e gs)
  interpret extension \<Sigma> \<Sigma>' by fact
  let ?gen = "\<lambda>\<Sigma>. by_rule RuleQualGenerator (do {
      \<sigma> \<leftarrow> synth_expr_at \<Sigma> \<Gamma> e;
      \<tau> \<leftarrow> or_else (Located (pos_of e) (NotIterable \<sigma>)) (elem_type \<Sigma> \<sigma>);
      ensure (x \<notin> captures gs) (Located p (CapturedGeneratorVariable x));
      Ok \<tau>
    })"
  have gen: "?gen \<Sigma>' = ?gen \<Sigma>"
    using "37.IH"(1)[OF "37.prems"] synth_at_Ok_wf[OF wf_table "37.prems"(2)]
    by (simp add: elem_type_ext cong: bind_sum_cong)
  have wf: "wf_ty \<Sigma> \<tau>" if "?gen \<Sigma> = Ok \<tau>" for \<tau>
    using that synth_at_Ok_wf[OF wf_table "37.prems"(2)]
    by (auto simp: bind_sum_Ok or_else_def ensure_def split: option.splits if_splits intro: elem_type_wf)
  have "quals \<Sigma>' (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs" if "?gen \<Sigma> = Ok \<tau>" for \<tau>
    using "37.IH"(2)[OF that "37.prems"(1)] wf[OF that] "37.prems"(2) by (simp add: wf_cxt_add wf_cxt_upd)
  then show ?case unfolding quals.simps gen by (intro bind_sum_cong[OF refl]) simp
qed (simp_all add: var_scheme_mono)

end
