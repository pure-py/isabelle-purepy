(* Stability of statement, definition and type definition checking under extension of the class table *)
theory ExtensionStatements
  imports ExtensionExpressions
begin

subsection \<open>Merging of contexts\<close>

lemma merge_entry_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; \<forall>\<theta> \<in> set_option e. wf_entry \<Sigma> \<theta> ; \<forall>\<theta> \<in> set_option e'. wf_entry \<Sigma> \<theta> \<rbrakk>
  \<Longrightarrow> merge_cxt_entry \<Sigma>' b e e' = merge_cxt_entry \<Sigma> b e e'"
  by (cases "(\<Sigma>, b, e, e')" rule: merge_cxt_entry.cases)
     (auto simp: extension.join_ext dest: var_ty_wf split: option.splits)

lemma merge_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "wf_cxt \<Sigma> \<Gamma>" and "wf_cxt \<Sigma> \<Gamma>'"
  shows "merge \<Sigma>' X \<Gamma> \<Gamma>' = merge \<Sigma> X \<Gamma> \<Gamma>'"
proof -
  have "merge_cxt_entry \<Sigma>' (x \<in> X) (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x)
    = merge_cxt_entry \<Sigma> (x \<in> X) (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x)"
    for x
    by (rule merge_entry_mono[OF assms(1)]) (auto dest: wf_cxt_lookup[OF assms(2)] wf_cxt_lookup[OF assms(3)])
  then show ?thesis unfolding merge_def Let_def by simp
qed

(* Static outcome whose bindings are well-formed *)
fun wf_static_outcome :: "class_table \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_static_outcome \<Sigma> (Assigns\<^sub>R \<Delta> r) = wf_cxt \<Sigma> \<Delta>" |
"wf_static_outcome \<Sigma> Returns\<^sub>R = True"

lemma merge_outcome_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_static_outcome \<Sigma> R ; wf_static_outcome \<Sigma> R' \<rbrakk>
  \<Longrightarrow> merge_outcome \<Sigma>' X R R' = merge_outcome \<Sigma> X R R'"
  by (cases "(\<Sigma>, X, R, R')" rule: merge_outcome.cases) (auto simp: merge_mono)

lemma merge_outcome_wf:
  "\<lbrakk> merge_outcome \<Sigma> X R R' = Ok R'' ; wf_static_outcome \<Sigma> R ; wf_static_outcome \<Sigma> R' \<rbrakk> \<Longrightarrow> wf_static_outcome \<Sigma> R''"
  by (cases "(\<Sigma>, X, R, R')" rule: merge_outcome.cases) (auto simp: bind_sum_Ok merge_wf)

lemma merge_fold_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "\<forall>R \<in> set Rs. wf_static_outcome \<Sigma> R"
  shows "foldr (\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma>' X R R' }) Rs (Ok Returns\<^sub>R)
       = foldr (\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }) Rs (Ok Returns\<^sub>R)
     \<and> (\<forall>R'. foldr (\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }) Rs (Ok Returns\<^sub>R) = Ok R' \<longrightarrow> wf_static_outcome \<Sigma> R')"
  using assms(2)
proof (induction Rs)
  case (Cons R Rs)
  then show ?case
    by (auto simp: bind_sum_Ok merge_outcome_mono[OF assms(1)] intro: merge_outcome_wf cong: bind_sum_cong)
qed simp

lemma merges_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "\<And>R. Ok R \<in> set ms \<Longrightarrow> wf_static_outcome \<Sigma> R"
  shows "merges \<Sigma>' X ms = merges \<Sigma> X ms"
proof -
  have "\<forall>R \<in> set Rs. wf_static_outcome \<Sigma> R" if "those_sum ms = Ok Rs" for Rs
    using assms(2) those_sum_eq[OF that] by simp
  then show ?thesis unfolding merges_def by (simp add: merge_fold_mono[OF assms(1)] cong: bind_sum_cong)
qed

subsection \<open>Definitions and calls\<close>

(* Type resolution in a well-formed context, as a function of the type expression *)
lemma resolve_type_fun_mono: "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> resolve_type \<Sigma>' \<Gamma> = resolve_type \<Sigma> \<Gamma>"
  by (rule ext) (rule extension.resolve_type_ext)

lemma def_signature_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> \<rbrakk> \<Longrightarrow> def_signature \<Sigma>' \<Gamma> d = def_signature \<Sigma> \<Gamma> d"
  by (cases d) (simp add: Let_def resolve_type_fun_mono wf_cxt_add wf_cxt_fmconst cong: bind_sum_cong)

lemma check_call_stmt_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<sigma> \<rbrakk> \<Longrightarrow> check_call_stmt \<Sigma>' \<Gamma> e \<sigma> kws es = check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es"
  by (induction \<Sigma> \<Gamma> e \<sigma> kws es rule: check_call_stmt.induct)
     (auto simp: synth_mono(5, 9) cong: bind_sum_cong)

lemma bind_sum_assoc: "bind_sum (bind_sum m g) f = bind_sum m (\<lambda>x. bind_sum (g x) f)"
  by (cases m) simp_all

lemma bind_sum_if: "bind_sum (if c then a else b) f = (if c then bind_sum a f else bind_sum b f)"
  by simp

lemma check_type_def_mono:
  assumes "extension \<Sigma> \<Sigma>'" and "wf_cxt \<Sigma> \<Gamma>"
  shows "check_type_def \<Sigma>' \<Gamma> \<chi> = check_type_def \<Sigma> \<Gamma> \<chi>"
proof -
  interpret extension \<Sigma> \<Sigma>' by fact
  have fields: "field_names \<Sigma>' D = field_names \<Sigma> D" if "resolve_name \<Gamma> q' = Some (Type D)" for q' D
    using resolve_name_wf[OF assms(2) that] by (simp add: field_names_ext)
  have rt: "resolve_type \<Sigma>' \<Gamma> = resolve_type \<Sigma> \<Gamma>" by (rule resolve_type_fun_mono[OF assms])
  show ?thesis
    by (cases \<chi>; cases "node \<chi>")
       (simp_all add: rt fields bind_sum_assoc bind_sum_if split: option.splits cxt_entry.splits)
qed

subsection \<open>Match cases\<close>

lemma match_cases_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> ; list_all (wf_shape \<Sigma>) L \<rbrakk>
  \<Longrightarrow> match_cases \<Sigma>' \<Gamma> \<tau> L ps = match_cases \<Sigma> \<Gamma> \<tau> L ps"
proof (induction ps arbitrary: \<tau> L)
  case (Cons p ps)
  interpret extension \<Sigma> \<Sigma>' by fact
  have "match_cases \<Sigma>' \<Gamma> (remaining \<Sigma> \<Gamma> \<tau> (node p)) L' ps = match_cases \<Sigma> \<Gamma> (remaining \<Sigma> \<Gamma> \<tau> (node p)) L' ps"
    if "match_shapes \<Sigma> \<Gamma> L (node p) = Some (K, L')" for K L'
    using Cons.IH[OF Cons.prems(1, 2) remaining_wf[OF Cons.prems(3), THEN conjunct1]]
      match_shapes_wf[OF wf_table Cons.prems(2, 4) that]
    by simp
  then show ?case
    by (simp add: check_pat_mono(2)[OF Cons.prems(1-3)] match_shapes_mono[OF Cons.prems(1, 2, 4)]
        remaining_mono[OF Cons.prems(1-3)] or_else_def cong: bind_sum_cong split: option.splits prod.splits)
qed simp

(* Bindings of the cases of a match at a well-formed scrutinee type, well-formed *)
lemma match_cases_wf_cxt:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> ; match_cases \<Sigma> \<Gamma> \<tau> L ps = Ok (\<Delta>s, \<tau>', L') ; \<Delta> \<in> set \<Delta>s \<rbrakk>
  \<Longrightarrow> wf_cxt \<Sigma> \<Delta>"
  using match_cases_wf by blast

subsection \<open>Statements\<close>

lemma check_stmt_at_wf_outcome:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R \<rbrakk> \<Longrightarrow> wf_static_outcome \<Sigma> R"
  by (cases R) (auto dest: check_stmt_wf(2))

lemma check_stmt_wf_outcome:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_cxt \<Sigma> \<Gamma> ; check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R \<rbrakk> \<Longrightarrow> wf_static_outcome \<Sigma> R"
  by (cases R) (auto dest: check_stmt_wf(1))

lemma check_stmt_mono:
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; pred_option (wf_ty \<Sigma>) \<zeta> \<rbrakk> \<Longrightarrow> check_stmt \<Sigma>' \<Gamma> \<zeta> s = check_stmt \<Sigma> \<Gamma> \<zeta> s"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; pred_option (wf_ty \<Sigma>) \<zeta> \<rbrakk> \<Longrightarrow> check_stmt_at \<Sigma>' \<Gamma> \<zeta> s' = check_stmt_at \<Sigma> \<Gamma> \<zeta> s'"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; \<forall>\<alpha>s \<sigma>. \<pi> = TyScheme \<alpha>s \<sigma> \<longrightarrow> wf_ty \<Sigma> \<sigma> \<rbrakk> \<Longrightarrow> check_def \<Sigma>' \<Gamma> d \<pi> = check_def \<Sigma> \<Gamma> d \<pi>"
  "\<lbrakk> extension \<Sigma> \<Sigma>' ; wf_cxt \<Sigma> \<Gamma> ; \<forall>\<alpha>s \<sigma>. \<pi> = TyScheme \<alpha>s \<sigma> \<longrightarrow> wf_ty \<Sigma> \<sigma> \<rbrakk>
    \<Longrightarrow> check_def_at \<Sigma>' \<Gamma> d' \<pi> = check_def_at \<Sigma> \<Gamma> d' \<pi>"
proof (induction \<Sigma> \<Gamma> \<zeta> s and \<Sigma> \<Gamma> \<zeta> s' and \<Sigma> \<Gamma> d \<pi> and \<Sigma> \<Gamma> d' \<pi>
    rule: check_stmt_check_stmt_at_check_def_check_def_at.induct)
  case (3 \<Sigma> \<Gamma> \<zeta> x e)
  show ?case
  proof (cases "fmlookup \<Gamma> x")
    case (Some \<theta>)
    show ?thesis
    proof (cases \<theta>)
      case (DU \<tau>)
      with Some wf_cxt_lookup[OF "3.prems"(2) Some] show ?thesis
        by (simp add: synth_mono(7)[OF "3.prems"(1, 2)] cong: bind_sum_cong)
    qed (simp_all add: Some)
  qed simp
next
  case (4 \<Sigma> \<Gamma> \<zeta> x \<psi> e)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
    using resolve_type_wf[OF "4.prems"(2)]
    by (simp add: resolve_type_ext[OF "4.prems"(2)] synth_mono(7)[OF "4.prems"(1, 2)] cong: bind_sum_cong)
next
  case (5 \<Sigma> \<Gamma> \<zeta> e)
  interpret extension \<Sigma> \<Sigma>' by fact
  show ?case
    using callee_Ok_wf[OF wf_table "5.prems"(2)]
    by (auto simp: synth_mono(2, 4)[OF "5.prems"(1, 2)] check_call_stmt_mono[OF "5.prems"(1, 2)]
        split: expr.splits cong: bind_sum_cong)
next
  case (10 \<Sigma> \<Gamma> \<zeta> e s elifs else')
  interpret extension \<Sigma> \<Sigma>' by fact
  have chk: "check_expr_at \<Sigma>' \<Gamma> e (TyPrim bool) = check_expr_at \<Sigma> \<Gamma> e (TyPrim bool)"
    using synth_mono(7)[OF "10.prems"(1, 2)] by simp
  show ?case
  proof (cases "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool)")
    case (Inr u)
    have elif: "check_elif \<Sigma>' \<Gamma> \<zeta> (elifs, else') = check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')"
      using "10.IH"(2)[OF Inr _ refl _ "10.prems"] "10.IH"(3)[OF Inr _ "10.prems"]
        synth_mono(7)[OF "10.prems"(1, 2)]
      by (auto split: option.splits cong: bind_sum_cong map_cong)
    have branches: "wf_static_outcome \<Sigma> R"
      if "Ok R \<in> set (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))" for R
      using check_elif_branch[OF that] check_stmt_at_wf_outcome[OF wf_table "10.prems"(2)] by auto
    show ?thesis
      unfolding check_stmt_if chk Inr
      by (simp only: bind_sum_simps "10.IH"(1)[OF Inr "10.prems"] elif merges_mono[OF "10.prems"(1) branches])
  qed (simp add: check_stmt_if chk)
next
  case (11 \<Sigma> \<Gamma> \<zeta> s s')
  interpret extension \<Sigma> \<Sigma>' by fact
  have "check_stmt_at \<Sigma>' (\<Gamma> \<otimes> \<Delta>) \<zeta> s' = check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s'"
    if "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)" for \<Delta> r
    using "11.IH"(2)[OF that refl "11.prems"(1) _ "11.prems"(3)] check_stmt_wf(2)[OF that wf_table "11.prems"(2)]
      "11.prems"(2)
    by (simp add: wf_cxt_add)
  then show ?case
    by (simp add: "11.IH"(1)[OF "11.prems"] cong: bind_sum_cong static_outcome.case_cong)
next
  case (12 \<Sigma> \<Gamma> \<zeta> ds)
  interpret extension \<Sigma> \<Sigma>' by fact
  let ?sigs = "\<lambda>\<Sigma>. map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds"
  have sigs: "?sigs \<Sigma>' = ?sigs \<Sigma>" by (simp add: def_signature_mono[OF "12.prems"(1, 2)])
  have defs: "map2 (check_def_at \<Sigma>' (\<Gamma> \<otimes> \<Delta>)) ds \<pi>s = map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> \<Delta>)) ds \<pi>s"
    if u: "(case redeclared node {} (map (\<lambda>d. At (pos_of d) (def_name (node d))) ds) of
             Some f \<Rightarrow> Fail (Located (pos_of f) (Redeclaration (node f))) | None \<Rightarrow> Ok ()) = Ok u"
    and unb: "all_sum (map (\<lambda>d. locate (pos_of d) (check_unbound \<Gamma> (def_name (node d)))) ds) = Ok u'"
    and \<pi>s: "those_sum (?sigs \<Sigma>) = Ok \<pi>s"
    and \<Delta>: "\<Delta> = fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))"
    for u u' \<pi>s \<Delta>
  proof (intro map_cong[OF refl])
    fix d\<pi>
    assume mem: "d\<pi> \<in> set (zip ds \<pi>s)"
    obtain d \<pi> where d\<pi>: "d\<pi> = (d, \<pi>)" by (cases d\<pi>)
    have cxt: "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>)" using "12.prems"(2) defs_wf[OF "12.prems"(2) \<pi>s] by (auto simp: \<Delta> wf_cxt_add)
    have "wf_ty \<Sigma> \<sigma>" if "\<pi> = TyScheme \<alpha>s \<sigma>" for \<alpha>s \<sigma>
    proof -
      from mem have "\<pi> \<in> set \<pi>s" by (auto simp: d\<pi> dest: set_zip_rightD)
      from those_sum_map_Ok_elem[OF \<pi>s this] obtain d' where "def_signature \<Sigma> \<Gamma> (node d') = Ok \<pi>" by auto
      from def_signature_wf[OF "12.prems"(2) this] show ?thesis by (cases \<alpha>s) (auto simp: that)
    qed
    then show "(case d\<pi> of (d, \<pi>) \<Rightarrow> check_def_at \<Sigma>' (\<Gamma> \<otimes> \<Delta>) d \<pi>) = (case d\<pi> of (d, \<pi>) \<Rightarrow> check_def_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) d \<pi>)"
      unfolding d\<pi> prod.case
      by (intro "12.IH"[OF u unb \<pi>s \<Delta> mem[unfolded d\<pi>] refl "12.prems"(1) cxt]) simp
  qed
  show ?case
    unfolding check_stmt.simps sigs Let_def
    by (intro bind_sum_cong[OF refl] arg_cong2[where f = bind_sum] refl) (simp add: defs)
next
  case (13 \<Sigma> \<Gamma> \<zeta> e bs)
  interpret extension \<Sigma> \<Sigma>' by fact
  have e: "synth_expr_at \<Sigma>' \<Gamma> e = synth_expr_at \<Sigma> \<Gamma> e" by (rule synth_mono(2)[OF "13.prems"(1, 2)])
  show ?case
  proof (cases "synth_expr_at \<Sigma> \<Gamma> e")
    case (Inr \<sigma>)
    have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" by (rule synth_at_Ok_wf[OF wf_table "13.prems"(2) Inr])
    have shapes: "shapes \<Sigma>' \<sigma> {} = shapes \<Sigma> \<sigma> {}" by (rule shapes_mono[OF "13.prems"(1) _ wf\<sigma>]) simp
    have cases: "match_cases \<Sigma>' \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst bs) = match_cases \<Sigma> \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst bs)"
      by (rule match_cases_mono[OF "13.prems"(1, 2) wf\<sigma>]) (auto simp: list_all_iff intro: shapes_wf[OF _ wf\<sigma>])
    have branches: "match_branches \<Sigma>' \<Gamma> \<zeta> \<Delta>s bs \<tau> L = match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L
        \<and> (\<forall>R. Ok R \<in> set (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L) \<longrightarrow> wf_static_outcome \<Sigma> R)"
      if mc: "match_cases \<Sigma> \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst bs) = Ok (\<Delta>s, \<tau>, L)" for \<Delta>s \<tau> L
    proof -
      have cxt: "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>)" if "\<Delta> \<in> set \<Delta>s" for \<Delta>
        using match_cases_wf_cxt[OF wf_table "13.prems"(2) wf\<sigma> mc that] "13.prems"(2) by (rule wf_cxt_add[rotated])
      have each: "check_stmt_at \<Sigma>' (\<Gamma> \<otimes> \<Delta>) \<zeta> s = check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s"
        if "(\<Delta>, (p, s)) \<in> set (zip \<Delta>s bs)" for \<Delta> p s
        using "13.IH"[OF Inr mc refl refl that refl refl "13.prems"(1) cxt[OF set_zip_leftD[OF that]] "13.prems"(3)]
        .
      have "map2 (\<lambda>\<Delta> (_, s). do { R \<leftarrow> check_stmt_at \<Sigma>' (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) }) \<Delta>s bs
          = map2 (\<lambda>\<Delta> (_, s). do { R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) }) \<Delta>s bs"
        using each by (intro map_cong[OF refl]) (auto split: prod.splits)
      moreover have "wf_static_outcome \<Sigma> R" if "Ok R \<in> set (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L)" for R
      proof (cases "Ok R \<in> set (map2 (\<lambda>\<Delta> (_, s). do { R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) })
                          \<Delta>s bs)")
        case True
        from Ok_in_set_map2[OF True] obtain \<Delta> p s R' where b: "(\<Delta>, (p, s)) \<in> set (zip \<Delta>s bs)"
          and R': "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s = Ok R'" and R: "R = Assigns\<^sub>R \<Delta> None \<otimes> R'"
          by (auto simp: bind_sum_Ok split: prod.splits)
        from check_stmt_at_wf_outcome[OF wf_table cxt[OF set_zip_leftD[OF b]] R']
          match_cases_wf_cxt[OF wf_table "13.prems"(2) wf\<sigma> mc set_zip_leftD[OF b]]
        show ?thesis by (cases R') (auto simp: R wf_cxt_add)
      next
        case False
        with that show ?thesis by (auto simp: match_branches_def split: if_splits)
      qed
      ultimately show ?thesis by (simp add: match_branches_def)
    qed
    show ?thesis
      unfolding check_stmt.simps e Inr bind_sum_simps shapes cases match_branches_def[symmetric]
      by (intro bind_sum_cong[OF refl]) (auto simp: branches merges_mono[OF "13.prems"(1)] split: prod.splits)
  qed (simp add: e)
next
  case (15 \<Sigma> \<Gamma> f \<alpha>s xps \<psi> s \<alpha>s' \<sigma>s \<tau>)
  interpret extension \<Sigma> \<Sigma>' by fact
  from "15.prems"(3) have wf\<sigma>s: "\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>" and wf\<tau>: "wf_ty \<Sigma> \<tau>" by auto
  let ?xs = "map fst xps"
  have body: "check_stmt_at \<Sigma>' (\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> \<Delta>' \<otimes> \<Delta>) (Some \<tau>) s
            = check_stmt_at \<Sigma> (\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> \<Delta>' \<otimes> \<Delta>) (Some \<tau>) s"
    if cad: "check_assignments_declared (set ?xs) (assign_targets s) (declares (node s)) (binds s) = Ok u"
    and sc: "(case scope Unbound ?xs s of None \<Rightarrow> Fail (redeclaration ?xs (declarations s) (pat_bound s))
              | Some x \<Rightarrow> Ok x) = Ok \<Delta>"
    and len: "length ?xs = length \<sigma>s" and \<Delta>': "params_cxt ?xs \<sigma>s = Ok \<Delta>'" for u \<Delta> \<Delta>'
  proof -
    have "wf_cxt \<Sigma> \<Delta>" using sc by (auto split: option.splits dest!: scope_stmt_Some simp: wf_cxt_fmconst)
    with "15.prems"(2) params_cxt_Ok_wf[OF \<Delta>' wf\<sigma>s]
    have "wf_cxt \<Sigma> (\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> \<Delta>' \<otimes> \<Delta>)" by (intro wf_cxt_add wf_cxt_fmconst) simp_all
    from "15.IH"[OF refl cad sc len \<Delta>' "15.prems"(1) this] wf\<tau> show ?thesis by simp
  qed
  show ?case
    unfolding check_def.simps Let_def
  proof (intro arg_cong[where f = "by_rule RuleDefBody"] bind_sum_cong[OF refl] if_cong[OF refl] refl, goal_cases)
    case (1 u \<Delta> \<Delta>')
    show ?case
      unfolding body[OF 1]
    proof (intro bind_sum_cong[OF refl], goal_cases)
      case (1 R)
      show ?case
      proof (cases R)
        case (Assigns\<^sub>R \<Delta>'' r)
        then show ?thesis by (cases r) (simp_all add: subty_ext[OF wf\<tau>] subty_ext[OF _ wf\<tau>] cong: if_cong)
      qed simp
    qed
  qed
next
  case (1 \<Sigma> \<Gamma> \<zeta>)
  then show ?case by simp
next
  case (2 \<Sigma> \<Gamma> \<zeta> x \<psi>)
  then show ?case by (simp add: extension.resolve_type_ext cong: bind_sum_cong)
next
  case (6 \<Sigma> \<Gamma> \<zeta> e)
  then show ?case by (simp add: synth_mono(2)[OF "6.prems"(1, 2)] cong: bind_sum_cong)
next
  case (7 \<Sigma> \<Gamma> \<zeta> e e')
  then show ?case
    by (cases e') (simp_all add: Let_def synth_mono(2, 7)[OF "7.prems"(1, 2)] cong: bind_sum_cong)
next
  case (8 \<Sigma> \<Gamma> \<zeta>)
  then show ?case by (cases \<zeta>) (simp_all add: extension.subty_ext)
next
  case (9 \<Sigma> \<Gamma> \<zeta> e)
  then show ?case by (cases \<zeta>) (simp_all add: synth_mono(7)[OF "9.prems"(1, 2)] cong: bind_sum_cong)
next
  case (14 \<Sigma> \<Gamma> \<zeta> p s)
  then show ?case by (simp add: "14.IH")
next
  case (17 \<Sigma> \<Gamma> p d \<pi>)
  then show ?case by (simp add: "17.IH")
qed simp_all

end
