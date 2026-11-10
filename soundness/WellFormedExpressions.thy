(* Well-formedness and type variables of the types synthesised for expressions and matched by patterns *)
theory WellFormedExpressions
  imports WellFormed
begin

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
      with IH show ?thesis by (auto intro: join_wf dest!: fv_join_elem)
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
    with tyvars_add[of \<Gamma> \<Delta>] \<Delta> show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" unfolding \<tau> by (auto simp: base_type_wf)
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
    with tyvars_add[of \<Gamma> \<Delta>] \<Delta> show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>" unfolding \<tau> by (auto simp: base_type_wf)
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
      unfolding \<tau> by (auto intro: join_wf dest!: fv_join_elem)
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
      then show ?thesis unfolding \<rho> \<sigma> by (simp add: base_type_wf)
    qed
    have wf: "\<forall>\<rho> \<in> set ?\<rho>s. wf_ty \<Sigma> \<rho>" using elems by blast
    have fv: "\<Union> (fv ` set ?\<rho>s) \<subseteq> tyvars \<Gamma>" unfolding UN_subset_iff using elems by blast
    from joins_wf[OF wf] subset_trans[OF fv_joins fv] show "wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> tyvars \<Gamma>"
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
    with elem_type_wf[OF _ elem] elem_type_fv[OF elem] have \<tau>: "wf_ty \<Sigma> \<tau>" "fv \<tau> \<subseteq> tyvars \<Gamma>" by auto
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
  from "3.prems" obtain \<Delta>\<^sub>p where "check_unbound \<Gamma> x = Ok ()"
    and "ensure (x \<notin> binds (node p)) (SelectsNoRule JudgementCheckPattern (PatternBindsTwice x)) = Ok ()"
    and "check_pat_at \<Sigma> \<Gamma> p \<tau> = Ok \<Delta>\<^sub>p"
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
  then show ?case by (auto simp: bind_sum_Ok dest!: bindings_at_append)
next
  case (8 \<Sigma> \<Gamma> q ps kps \<tau>)
  then show ?case by (auto simp: bind_sum_Ok dest!: bindings_at_append)
qed (auto simp: bind_sum_Ok ensure_def)

lemma check_pat_at_node:
  "check_pat_at \<Sigma> \<Gamma> p \<tau> = Ok \<Delta> \<Longrightarrow> check_pat \<Sigma> \<Gamma> (node p) \<tau> = Ok \<Delta>"
  by (cases p) simp

(* Class of a constructor pattern checked against a type, in the class table *)
lemma check_pattern_class_dom:
  "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; check_pattern_class \<Gamma> q = Ok C \<rbrakk> \<Longrightarrow> C |\<in>| fmdom \<Sigma> \<and> resolve_name \<Gamma> q = Some (Type C)"
  by (auto simp: check_pattern_class_def split: option.splits cxt_entry.splits if_splits dest!: resolve_name_wf)

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
      with Instance have anc: "C \<in> set (ancestors \<Sigma> D)" and "\<tau>s' = ancestor_args \<Sigma> D \<sigma>s C"
        by (auto split: if_splits)
      with ancestor_args_wf[OF assms(1) assms(2)[unfolded TyClass] anc] \<tau>s' show ?thesis by simp
    next
      case (TyPrim p)
      with Instance \<tau>s' show ?thesis by (cases p) (auto split: if_splits)
    qed (use Instance in auto)
  next
    case Incomparable
    with assms(3) have below: "instance_below \<Sigma> C \<tau> = Instance \<tau>s" by (simp add: instance_at_def)
    from instance_below_length[OF below] show ?thesis .
  next
    case Undefined
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
  from check_pattern_class_dom[OF assms(2) cls] have C: "C |\<in>| fmdom \<Sigma>" and rn: "resolve_name \<Gamma> q = Some (Type C)"
    by auto
  have eq: "matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q a) =
    (case instance_at \<Sigma> C \<tau> of Instance \<sigma>s \<Rightarrow> meet \<Sigma> \<tau> (TyClass C \<sigma>s) | _ \<Rightarrow> TyPrim Never)"
    using assms(5) by (cases \<tau>) (auto simp: rn)
  show ?thesis
  proof (cases "instance_at \<Sigma> C \<tau>")
    case (Instance \<sigma>s)
    from instance_at_class_wf[OF assms(1, 3) Instance C] have "wf_ty \<Sigma> (TyClass C \<sigma>s)" .
    from meet_wf(1)[OF assms(3) this] have wf: "wf_ty \<Sigma> (meet \<Sigma> \<tau> (TyClass C \<sigma>s))" .
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
  show ?case by (auto intro: join_wf dest!: fv_join_elem)
next
  case (8 \<Sigma> \<Gamma> \<tau>s ps)
  show ?case
  proof (cases "length \<tau>s = length ps")
    case True
    from "8.prems"(4) obtain \<Delta>' where "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<tau>s) = Ok \<Delta>'"
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
      moreover have "wf_ty \<Sigma> \<sigma>" using "8.prems"(3) set_zip_leftD[OF that] by auto
      ultimately show ?thesis using "8.IH"[OF True that refl "8.prems"(1, 2)] by blast
    qed
    then have elems: "wf_ty \<Sigma> (matched_as \<Sigma> \<Gamma> a (node b))
        \<and> fv (matched_as \<Sigma> \<Gamma> a (node b)) \<subseteq> \<Union> (fv ` set \<tau>s)"
      if "(a, b) \<in> set (zip \<tau>s ps)" for a b
      using that set_zip_leftD[OF that] by blast
    have wf: "\<forall>\<rho> \<in> set (map2 (\<lambda>\<tau> p. matched_as \<Sigma> \<Gamma> \<tau> (node p)) \<tau>s ps). wf_ty \<Sigma> \<rho>" using elems by auto
    have fv: "\<Union> (fv ` set (map2 (\<lambda>\<tau> p. matched_as \<Sigma> \<Gamma> \<tau> (node p)) \<tau>s ps)) \<subseteq> \<Union> (fv ` set \<tau>s)"
      unfolding UN_subset_iff using elems by auto
    from wf fv True show ?thesis by simp
  qed (use "8.prems"(3) in simp)
qed ((rule matched_as_constr_wf; (assumption | simp))
     | (auto simp: bind_sum_Ok intro: meet_wf(1) dest!: fv_meet[THEN subsetD] check_pat_at_node)[1])+


(* Type remaining after a pattern at a well-formed type: well-formed and over the type variables of the type *)
lemma remaining_wf:
  "wf_ty \<Sigma> \<tau> \<Longrightarrow> wf_ty \<Sigma> (remaining \<Sigma> \<Gamma> \<tau> p) \<and> fv (remaining \<Sigma> \<Gamma> \<tau> p) \<subseteq> fv \<tau>"
proof (induction \<Sigma> \<Gamma> \<tau> p rule: remaining.induct)
  case (1 \<Sigma> \<Gamma> \<sigma> \<tau> p)
  then show ?case by (auto intro: join_wf dest!: fv_join_elem)
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
qed (auto simp: Let_def split: instances.splits if_splits option.splits cxt_entry.splits)

end
