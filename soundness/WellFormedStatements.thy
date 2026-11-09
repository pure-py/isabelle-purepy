(* Well-formedness and type variables of pattern bindings and of the contexts produced by statements *)
theory WellFormedStatements
  imports WellFormedExpressions
begin

subsection \<open>Pattern bindings\<close>

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
    from joins_wf[OF wf] subset_trans[OF fv_joins fv] show ?thesis unfolding \<sigma> by blast
  qed
  ultimately show ?thesis by blast
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
  from "3.prems"(4) obtain \<Delta>\<^sub>p where unb: "check_unbound \<Gamma> x = Ok ()"
    and once: "ensure (x \<notin> binds (node p)) (SelectsNoRule JudgementCheckPattern (PatternBindsTwice x)) = Ok ()"
    and p: "check_pat_at \<Sigma> \<Gamma> p \<tau> = Ok \<Delta>\<^sub>p"
    and \<Delta>: "\<Delta> = \<Delta>\<^sub>p \<otimes> fmupd x (matched_as \<Sigma> \<Gamma> \<tau> (node p)) fmempty"
    by (auto simp: bind_sum_Ok)
  from matched_as_wf[OF "3.prems"(1-3) check_pat_at_node[OF p]] "3.IH"[OF unb once "3.prems"(1-3) p] show ?case
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
    and cb: "check_bound_once ps = Ok ()" and b: "bindings_at \<Sigma> \<Gamma> (PatTuple ps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
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
      from "5.IH"[OF ens cb \<sigma> \<sigma>s len mem refl "5.prems"(1, 2) wf\<sigma>' chk] fv\<sigma>' fv\<sigma> show ?thesis by blast
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
    and cb: "check_bound_once ps = Ok ()" and b: "bindings_at \<Sigma> \<Gamma> (PatList ps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
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
      from "6.IH"[OF ens cb \<sigma> \<sigma>' p "6.prems"(1, 2) wf\<sigma> chk[unfolded this(2)]] fv\<sigma> this(2) show ?thesis by blast
    qed
    from pattern_bindings_wf[OF pb _ this] show ?thesis by auto
  qed
  from bindings_at_wf[OF b] sub show ?case by blast
next
  case (7 \<Sigma> \<Gamma> kps \<tau>)
  let ?f = "\<lambda>\<sigma>. case \<sigma> of
              TyDict \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p. check_pat_at \<Sigma> \<Gamma> p \<sigma>') (map snd kps)))
            | _ \<Rightarrow>
                if has_dict_values \<Sigma> \<sigma> then Some (Fail (Violates RuleCheckDictNone (DictPatternDictValues \<sigma>)))
                else None"
  from "7.prems"(4) have cb: "check_bound_once (map snd kps) = Ok ()"
    and b: "bindings_at \<Sigma> \<Gamma> (PatDict kps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
    by (auto simp: bind_sum_Ok)
  have sub: "fmdom' \<Delta>' = binds (PatDict kps) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> fv \<tau>)"
    if \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')" for \<sigma> \<Delta>'
  proof -
    from f obtain \<sigma>' where \<sigma>': "\<sigma> = TyDict \<sigma>'"
      and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) (map snd kps) (replicate (length kps) \<sigma>')) = Ok \<Delta>'"
      by (auto simp: map2_replicate[of _ "map snd kps", simplified] split: ty.splits if_splits)
    from disjuncts_wf[OF "7.prems"(3) \<sigma>] have wf\<sigma>: "wf_ty \<Sigma> \<sigma>'" and fv\<sigma>: "fv \<sigma>' \<subseteq> fv \<tau>" by (auto simp: \<sigma>')
    have "fmdom' \<Delta>'' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>'' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> fv \<tau>)"
      if mem: "(p, \<sigma>'') \<in> set (zip (map snd kps) (replicate (length kps) \<sigma>'))"
      and chk: "check_pat_at \<Sigma> \<Gamma> p \<sigma>'' = Ok \<Delta>''" for p \<sigma>'' \<Delta>''
    proof -
      from mem have p: "p \<in> set (map snd kps)" and "\<sigma>'' = \<sigma>'" by (auto dest: set_zip_leftD set_zip_rightD)
      from "7.IH"[OF cb \<sigma> \<sigma>' p "7.prems"(1, 2) wf\<sigma> chk[unfolded this(2)]] fv\<sigma> this(2) show ?thesis by blast
    qed
    from pattern_bindings_wf[OF pb _ this] show ?thesis by auto
  qed
  from bindings_at_wf[OF b] sub show ?case by blast
next
  case (8 \<Sigma> \<Gamma> q ps kps \<tau>)
  from "8.prems"(4) obtain C where cls: "check_pattern_class \<Gamma> q = Ok C"
    and fm: "check_field_map (PatternArityMismatch (short_name C)) (UnknownFieldInPattern (short_name C))
               (field_names \<Sigma> C) (length ps) (map fst kps) = Ok ()"
    and cb: "check_bound_once (ps @ map snd kps) = Ok ()"
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
      from "8.IH"[OF cls fm cb \<sigma> inst mem refl "8.prems"(1, 2) wf\<sigma>' chk] fv\<sigma>' fv\<sigma>s fv\<sigma> show ?thesis by blast
    qed
    from pattern_bindings_wf[OF pb _ this] len_fp length_field_types[of \<Sigma> C \<sigma>s] set_fp show ?thesis
      by auto
  qed
  from bindings_at_wf[OF b] sub show ?case by blast
next
  case (9 \<Sigma> \<Gamma> p q \<tau>)
  then show ?case by simp
qed (auto simp: bind_sum_Ok)


subsection \<open>Statements\<close>

lemma tyvars_fmempty [simp]: "tyvars fmempty = {}"
  by (rule tyvars_empty) simp

lemma wf_entry_PUScheme: "wf_entry \<Sigma> (PUScheme \<pi> b) = wf_entry \<Sigma> (Scheme \<pi>)"
  by (cases \<pi>) simp_all

lemma var_ty_wf: "\<lbrakk> var_ty \<theta> = Some \<sigma> ; wf_entry \<Sigma> \<theta> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<sigma>"
  by (auto dest!: var_ty_Some)

lemma possibly_unassigned_wf: "\<lbrakk> possibly_unassigned b \<theta> = Some \<theta>' ; wf_entry \<Sigma> \<theta> \<rbrakk> \<Longrightarrow> wf_entry \<Sigma> \<theta>'"
  by (cases "(b, \<theta>)" rule: possibly_unassigned.cases) (auto simp: wf_entry_PUScheme)

(* Merge of well-formed entries, well-formed *)
lemma merge_entry_wf:
  "\<lbrakk> merge_cxt_entry \<Sigma> b e e' = Some \<theta>'' ; \<forall>\<theta> \<in> set_option e. wf_entry \<Sigma> \<theta> ; \<forall>\<theta> \<in> set_option e'. wf_entry \<Sigma> \<theta> \<rbrakk>
  \<Longrightarrow> wf_entry \<Sigma> \<theta>''"
proof (cases e)
  case (Some \<theta>)
  show "\<lbrakk> merge_cxt_entry \<Sigma> b e e' = Some \<theta>'' ; \<forall>\<theta> \<in> set_option e. wf_entry \<Sigma> \<theta>
         ; \<forall>\<theta> \<in> set_option e'. wf_entry \<Sigma> \<theta> \<rbrakk>
    \<Longrightarrow> wf_entry \<Sigma> \<theta>''"
  proof (cases e')
    case (Some \<theta>')
    assume "merge_cxt_entry \<Sigma> b e e' = Some \<theta>''" and "\<forall>\<theta> \<in> set_option e. wf_entry \<Sigma> \<theta>"
      and "\<forall>\<theta> \<in> set_option e'. wf_entry \<Sigma> \<theta>"
    with \<open>e = Some \<theta>\<close> Some merge_cxt_entry_cases[of \<Sigma> b \<theta> \<theta>' \<theta>''] show ?thesis
      by (auto intro!: join_wf simp: wf_entry_PUScheme dest!: scheme_of_Some var_ty_Some)
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
    by (rule merge_entry_wf)
       (auto dest: wf_cxt_lookup[OF assms(2)] wf_cxt_lookup[OF assms(3)] split: option.splits)
qed

(* Bindings of the merge of a list of static outcomes, well-formed when those of each outcome are *)
lemma merge_fold_wf:
  "\<lbrakk> foldr (\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }) Rs (Ok Returns\<^sub>R) = Ok (Assigns\<^sub>R \<Delta> r)
   ; \<And>\<Delta>' r'. Assigns\<^sub>R \<Delta>' r' \<in> set Rs \<Longrightarrow> wf_cxt \<Sigma> \<Delta>' \<rbrakk>
  \<Longrightarrow> wf_cxt \<Sigma> \<Delta>"
proof (induction Rs arbitrary: \<Delta> r)
  case (Cons R Rs)
  let ?f = "\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }"
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
  show "wf_cxt \<Sigma> \<Delta>"
  proof (rule merge_fold_wf[OF fold])
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
