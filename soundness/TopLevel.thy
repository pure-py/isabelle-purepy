(* Soundness of top-level statement, module and program evaluation *)
theory TopLevel
  imports Attributes Comprehensions Calls Statements ExtensionTopLevel
begin

context wf_evaluation
begin

subsection \<open>Statements\<close>

(* Soundness of each evaluation rule *)
lemmas rule_sound =
  var_sound var_unknown_sound var_unbound_sound literal_sound lambda_sound unop_sound binop_sound
  binop_fail_sound and_false_sound and_true_sound and_fail_sound and_nonbool_sound or_true_sound
  or_false_sound or_fail_sound or_nonbool_sound cond_true_sound cond_false_sound cond_fail_sound
  cond_nonbool_sound list_sound list_fail_sound tuple_sound tuple_fail_sound dict_sound dict_fail_sound
  dict_nonstr_sound subscript_sound class_type_args_sound subscript_fail_sound list_comp_sound
  list_comp_fail_quals_sound list_comp_fail_sound dict_comp_sound dict_comp_fail_quals_sound
  dict_comp_fail_sound attr_object_sound attr_object_missing_sound attr_module_sound
  attr_module_missing_sound attr_nonobject_sound attr_fail_sound call_lambda_sound call_lambda_arity_sound
  call_def_sound call_def_arity_sound call_prim_sound call_nonfun_sound call_fail_sound call_fail_args_sound
  constr_sound constr_arity_sound constr_fail_sound exprs_nil_sound exprs_cons_sound exprs_fail_sound
  pass_sound declare_sound assign_sound expr_stmt_sound print_sound return_sound return_none_sound defs_sound
  assert_sound assert_false_sound assert_fail_sound assert_nonbool_sound assert_msg_false_fail_sound
  assert_msg_nonstr_sound if_true_sound if_false_sound if_fail_sound if_nonbool_sound match_sound
  match_fail_sound match_abort_sound seq_sound seq_exit_sound if_none_sound else_sound elif_true_sound
  elif_false_sound elif_fail_sound elif_nonbool_sound quals_nil_sound qual_guard_true_sound
  qual_guard_false_sound qual_guard_fail_sound qual_guard_nonbool_sound qual_generator_sound
  qual_generator_fail_sound qual_generator_nonseq_sound gen_nil_sound gen_cons_sound gen_fail_sound
  comp_nil_sound comp_cons_sound comp_fail_sound entries_nil_sound entries_cons_sound entries_fail_key_sound
  entries_nonstr_sound entries_fail_value_sound

theorem soundness:
  shows
      expr_sound: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> sound_expr \<rho> e r"
  and exprs_sound: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> sound_exprs \<rho> es rs"
  and stmt_sound: "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> sound_stmt \<rho> s o"
  and elif_sound: "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o' \<Longrightarrow> sound_elif \<rho> eb o'"
  and quals_sound: "\<rho>, gs \<Rightarrow>\<^sub>q q \<Longrightarrow> sound_quals \<rho> gs q"
  and gen_sound: "\<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q \<Longrightarrow> sound_gen \<rho> x us gs q"
  and comp_sound: "\<rho>s, ec \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr \<Longrightarrow> sound_comp \<rho>s ec vr"
  and entries_sound: "\<rho>s, ec, ec' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr \<Longrightarrow> sound_entries \<rho>s ec ec' dr"
  by (induction
      rule: eval_expr_eval_exprs_eval_stmt_eval_elif_eval_quals_eval_gen_eval_comp_eval_entries.inducts)
     (auto intro: rule_sound)

subsection \<open>Top-level statements\<close>

(* Sequence of top-level statements checked from the class table and leaving it fixed: each statement checked
   from the table and leaving it fixed *)
lemma check_top_seq_fixed:
  assumes "check_top_stmt \<Sigma> q \<Gamma> (TopSeq t t') = Ok (R, \<Sigma>)" and "distinct (declares (TopSeq t t'))"
  obtains \<Delta> r R' where "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>)"
    and "check_top_stmt \<Sigma> q (\<Gamma> \<otimes> \<Delta>) t' = Ok (R', \<Sigma>)" and "R = Assigns\<^sub>R \<Delta> r \<otimes> R'"
proof -
  from assms(1) obtain \<Delta> r \<Sigma>\<^sub>1 R' where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>\<^sub>1)"
    and t': "check_top_stmt \<Sigma>\<^sub>1 q (\<Gamma> \<otimes> \<Delta>) t' = Ok (R', \<Sigma>)" and R: "R = Assigns\<^sub>R \<Delta> r \<otimes> R'"
    by (auto simp: bind_sum_Ok split: static_outcome.splits dest!: not_Returns)
  from check_top_stmt_adds[OF t] obtain E\<^sub>1 where \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma> \<otimes> E\<^sub>1"
    and E\<^sub>1: "\<forall>C. C |\<in>| fmdom E\<^sub>1 \<longrightarrow> (\<exists>c \<in> set (declares t). C = Qualified q c)" by blast
  from check_top_stmt_adds[OF t'] obtain E\<^sub>2 where \<Sigma>: "\<Sigma> = \<Sigma>\<^sub>1 \<otimes> E\<^sub>2"
    and E\<^sub>2: "\<forall>C. C |\<in>| fmdom E\<^sub>2 \<longrightarrow> (\<exists>c \<in> set (declares t'). C = Qualified q c)" by blast
  have "\<Sigma>\<^sub>1 = \<Sigma>"
  proof (rule fmap_ext)
    fix C
    show "fmlookup \<Sigma>\<^sub>1 C = fmlookup \<Sigma> C"
    proof (cases "C |\<in>| fmdom E\<^sub>2")
      case True
      with E\<^sub>2 assms(2) E\<^sub>1 have "C |\<notin>| fmdom E\<^sub>1" by auto
      with True show ?thesis using \<Sigma>\<^sub>1 \<Sigma> by (metis fmlookup_add_in fmlookup_add_notin)
    next
      case False
      with \<Sigma> show ?thesis by (metis fmlookup_add_notin)
    qed
  qed
  with t t' R have "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>)"
    and "check_top_stmt \<Sigma> q (\<Gamma> \<otimes> \<Delta>) t' = Ok (R', \<Sigma>)" and "R = Assigns\<^sub>R \<Delta> r \<otimes> R'"
    by simp_all
  then show thesis by (rule that)
qed

(* Bindings of a top-level statement checked from the class table in a well-formed closed context, leaving the
   table fixed: well-formed and closed *)
lemma check_top_stmt_fixed_closed:
  "\<lbrakk> check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>) ; distinct (declares t) ; wf_cxt \<Sigma> \<Gamma> ; tyvars \<Gamma> = {} \<rbrakk>
  \<Longrightarrow> wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> = {}"
proof (induction t arbitrary: \<Gamma> \<Delta> r)
  case (Stmt s)
  from Stmt.prems(1) have "check_stmt_at \<Sigma> \<Gamma> None s = Ok (Assigns\<^sub>R \<Delta> r)" by (auto simp: bind_sum_Ok)
  from check_stmt_wf(2)[OF this wf_class_table Stmt.prems(3)] Stmt.prems(4) show ?case by auto
next
  case (TopSeq t t')
  from check_top_seq_fixed[OF TopSeq.prems(1, 2)] obtain \<Delta>\<^sub>1 r\<^sub>1 R'
    where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1, \<Sigma>)"
    and t': "check_top_stmt \<Sigma> q (\<Gamma> \<otimes> \<Delta>\<^sub>1) t' = Ok (R', \<Sigma>)" and R: "Assigns\<^sub>R \<Delta> r = Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1 \<otimes> R'" .
  from R obtain \<Delta>\<^sub>2 r\<^sub>2 where R': "R' = Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2" and \<Delta>: "\<Delta> = \<Delta>\<^sub>1 \<otimes> \<Delta>\<^sub>2" by (cases R') auto
  from TopSeq.IH(1)[OF t _ TopSeq.prems(3, 4)] TopSeq.prems(2) have \<Delta>\<^sub>1: "wf_cxt \<Sigma> \<Delta>\<^sub>1 \<and> tyvars \<Delta>\<^sub>1 = {}" by auto
  with TopSeq.prems(3, 4) have "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>1)" and "tyvars (\<Gamma> \<otimes> \<Delta>\<^sub>1) = {}"
    using tyvars_add[of \<Gamma> \<Delta>\<^sub>1] by (auto intro: wf_cxt_add)
  from TopSeq.IH(2)[OF t'[unfolded R'] _ this] TopSeq.prems(2) have "wf_cxt \<Sigma> \<Delta>\<^sub>2 \<and> tyvars \<Delta>\<^sub>2 = {}" by auto
  with \<Delta>\<^sub>1 show ?case using tyvars_add[of \<Delta>\<^sub>1 \<Delta>\<^sub>2] by (auto simp: \<Delta> intro: wf_cxt_add)
next
  case (TypeDefs \<chi>s)
  let ?\<Delta> = "fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_entry \<Gamma> q \<chi>s j)) [0..<length \<chi>s])"
  from TypeDefs.prems(1) have \<Sigma>: "region_table \<Gamma> q \<chi>s \<Sigma> = \<Sigma>" and \<Delta>: "\<Delta> = ?\<Delta>"
    by (auto simp: Let_def bind_sum_Ok)
  have region: "\<forall>\<chi> \<in> set \<chi>s. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q c |\<in>| fmdom \<Sigma>"
  proof (intro ballI allI impI)
    fix \<chi> c \<alpha>s b \<phi>
    assume "\<chi> \<in> set \<chi>s" and "node \<chi> = Dataclass c \<alpha>s b \<phi>"
    then obtain j where "j < length \<chi>s" and "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" by (auto simp: in_set_conv_nth)
    then have "\<exists>j \<in> set [0..<length \<chi>s]. \<exists>c'. defines_class \<chi>s j c' \<and> Qualified q c = Qualified q c'"
      by (auto intro!: bexI[of _ j])
    then show "Qualified q c |\<in>| fmdom \<Sigma>"
      using fold_class_table_dom[of "Qualified q c" \<Gamma> q \<chi>s "[0..<length \<chi>s]" \<Sigma>] unfolding \<Sigma> by blast
  qed
  have "wf_cxt \<Sigma> ?\<Delta>"
    using type_entry_wf[OF TypeDefs.prems(4, 3) _ region] by (auto intro!: wf_cxt_of_list)
  moreover have "tyvars ?\<Delta> = {}" by (rule tyvars_empty) (auto simp: fmlookup_of_list dest!: map_of_SomeD)
  ultimately show ?case by (simp add: \<Delta>)
qed

(* Soundness of top-level statement evaluation, for a statement checked from the class table in a closed
   context, leaving the table fixed *)
lemma top_sound:
  "\<lbrakk> q, \<rho>, t \<Rightarrow>\<^sub>t o ; \<eta> \<turnstile> \<rho> : \<Gamma> ; tyvars \<Gamma> = {} ; check_top_stmt \<Sigma> q \<Gamma> t = Ok (R, \<Sigma>) ; distinct (declares t) \<rbrakk>
  \<Longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> None o R"
proof (induction arbitrary: \<Gamma> R rule: eval_top.induct)
  case (EvalTopStmt \<rho> s o q)
  from EvalTopStmt.prems(3) have "check_stmt_at \<Sigma> \<Gamma> None s = Ok R" by (auto simp: bind_sum_Ok)
  with stmt_sound[OF EvalTopStmt.hyps] EvalTopStmt.prems(1) show ?case by (intro sound_stmt_at) simp_all
next
  case (EvalTopSeq q \<rho> t us \<rho>' t' o)
  from check_top_seq_fixed[OF EvalTopSeq.prems(3, 4)] obtain \<Delta> r R'
    where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>)"
    and t': "check_top_stmt \<Sigma> q (\<Gamma> \<otimes> \<Delta>) t' = Ok (R', \<Sigma>)" and R: "R = Assigns\<^sub>R \<Delta> r \<otimes> R'" .
  from EvalTopSeq.prems(4) have distinct: "distinct (declares t)" "distinct (declares t')" by auto
  have o1: "wf_outcome \<eta> \<rho> \<Gamma> None (us, Assigns \<rho>') (Assigns\<^sub>R \<Delta> r)"
    by (rule EvalTopSeq.IH(1)[OF EvalTopSeq.prems(1, 2) t distinct(1)])
  then have env': "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>" and dom: "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>" by simp_all
  have "tyvars (\<Gamma> \<otimes> \<Delta>) = {}"
    using check_top_stmt_fixed_closed[OF t distinct(1) wf_env_wf_cxt[OF EvalTopSeq.prems(1)] EvalTopSeq.prems(2)]
      EvalTopSeq.prems(2) tyvars_add[of \<Gamma> \<Delta>]
    by blast
  from EvalTopSeq.IH(2)[OF env' this t' distinct(2)] have o2: "wf_outcome \<eta> (\<rho> \<otimes> \<rho>') (\<Gamma> \<otimes> \<Delta>) None o R'" .
  obtain vs' \<omega>' where o: "o = (vs', \<omega>')" by (cases o)
  show ?case
  proof (cases \<omega>')
    case (Assigns \<rho>'')
    with o2 o obtain \<Delta>' where "bindings_of R' = Some \<Delta>'" and "fmdom \<rho>'' |\<subseteq>| fmdom \<Delta>'"
      and "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' \<otimes> \<rho>'' : \<Gamma> \<otimes> \<Delta> \<otimes> \<Delta>'" by auto
    moreover from this(1) obtain r' where "R' = Assigns\<^sub>R \<Delta>' r'" by (cases R') auto
    ultimately show ?thesis using dom by (auto simp: o Assigns R intro: le_supI1 le_supI2)
  qed (use o2 in \<open>simp_all add: o\<close>)
next
  case (EvalTopSeqFail q \<rho> t us \<kappa> t')
  from check_top_seq_fixed[OF EvalTopSeqFail.prems(3, 4)] obtain \<Delta> r R'
    where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>)" .
  from EvalTopSeqFail.IH[OF EvalTopSeqFail.prems(1, 2) t] EvalTopSeqFail.prems(4) show ?case by auto
next
  case (EvalTypes q \<rho> \<chi>s)
  let ?names = "map (\<lambda>j. type_def_name (node (\<chi>s ! j))) [0..<length \<chi>s]"
  let ?\<Delta> = "fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_entry \<Gamma> q \<chi>s j)) [0..<length \<chi>s])"
  let ?\<rho>' = "fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_value q \<chi>s j)) [0..<length \<chi>s])"
  from EvalTypes.prems(3) have \<Sigma>: "region_table \<Gamma> q \<chi>s \<Sigma> = \<Sigma>" and R: "R = Assigns\<^sub>R ?\<Delta> None"
    by (auto simp: Let_def bind_sum_Ok)
  have "?names = map (type_def_name \<circ> node) \<chi>s" by (rule nth_equalityI) simp_all
  with EvalTypes.prems(4) have distinct: "distinct ?names" by simp
  have region: "\<forall>\<chi> \<in> set \<chi>s. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q c |\<in>| fmdom \<Sigma>"
  proof (intro ballI allI impI)
    fix \<chi> c \<alpha>s b \<phi>
    assume "\<chi> \<in> set \<chi>s" and "node \<chi> = Dataclass c \<alpha>s b \<phi>"
    then obtain j where "j < length \<chi>s" and "node (\<chi>s ! j) = Dataclass c \<alpha>s b \<phi>" by (auto simp: in_set_conv_nth)
    then have "\<exists>j \<in> set [0..<length \<chi>s]. \<exists>c'. defines_class \<chi>s j c' \<and> Qualified q c = Qualified q c'"
      by (auto intro!: bexI[of _ j])
    then show "Qualified q c |\<in>| fmdom \<Sigma>"
      using fold_class_table_dom[of "Qualified q c" \<Gamma> q \<chi>s "[0..<length \<chi>s]" \<Sigma>] unfolding \<Sigma> by blast
  qed
  have "\<eta> \<turnstile> \<rho> \<otimes> ?\<rho>' : \<Gamma> \<otimes> ?\<Delta>"
  proof (rule wf_env_add[OF EvalTypes.prems(1)])
    show "fmdom ?\<rho>' |\<subseteq>| fmdom ?\<Delta>" by (simp add: comp_def)
    show "wf_cxt \<Sigma> ?\<Delta>"
      using type_entry_wf[OF EvalTypes.prems(2) wf_env_wf_cxt[OF EvalTypes.prems(1)] _ region]
      by (auto intro!: wf_cxt_of_list)
    fix x \<theta>
    assume "fmlookup ?\<Delta> x = Some \<theta>"
    then obtain j where j: "j < length \<chi>s" and x: "x = type_def_name (node (\<chi>s ! j))"
      and \<theta>: "\<theta> = type_entry \<Gamma> q \<chi>s j"
      by (auto simp: fmlookup_of_list dest!: map_of_SomeD)
    have look': "fmlookup ?\<rho>' x = Some (type_value q \<chi>s j)"
      using distinct j x by (auto simp: fmlookup_of_list comp_def intro!: map_of_is_SomeI)
    moreover have "\<turnstile> type_value q \<chi>s j : inst_entry \<eta> \<theta>"
      using region nth_mem[OF j] by (auto simp: \<theta> type_value_def type_entry_def intro: ValClass ValTypeAlias split: type_def.splits)
    ultimately show "\<exists>v. fmlookup (\<rho> \<otimes> ?\<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
      using fmlookup_add_in[OF fmdomI[OF look']] by auto
  qed
  then show ?case by (simp add: R comp_def)
qed

subsection \<open>Environments of modules\<close>

lemma wf_env_add_env:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<eta> \<turnstile> \<rho>' : \<Gamma>'" and "fmdom \<rho>' |\<subseteq>| fmdom \<Gamma>'"
  shows "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Gamma>'"
proof (rule wf_env_add[OF assms(1, 3) _ wf_env_wf_cxt[OF assms(2)]])
  fix x \<theta>
  assume "fmlookup \<Gamma>' x = Some \<theta>" and "\<theta> \<noteq> TypeVar"
  from wf_env_lookup[OF assms(2) this] obtain v where "fmlookup \<rho>' x = Some v" and "\<turnstile> v : inst_entry \<eta> \<theta>"
    by blast
  then show "\<exists>v. fmlookup (\<rho> \<otimes> \<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>" by (auto simp: fmlookup_dom_iff)
qed

(* Environment of a module with the members absent from it unbound, typed by the signature of the module *)
abbreviation module_env :: "(var \<Rightarrow> ty) \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> bool"
where "module_env \<eta> \<rho> \<Gamma> \<equiv> \<eta> \<turnstile> \<rho> \<otimes> fmconst (fmdom' \<Gamma> - fmdom' \<rho>) VUnbound : \<Gamma> \<and> fmdom \<rho> |\<subseteq>| fmdom \<Gamma>"

lemma module_env_full: "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; fmdom \<rho> |\<subseteq>| fmdom \<Gamma> ; tyvars \<Gamma> = {} \<rbrakk> \<Longrightarrow> module_env \<eta> \<rho> \<Gamma>"
proof -
  assume *: "\<eta> \<turnstile> \<rho> : \<Gamma>" "fmdom \<rho> |\<subseteq>| fmdom \<Gamma>" "tyvars \<Gamma> = {}"
  have "fmdom' \<Gamma> - fmdom' \<rho> = {}"
  proof -
    have "x \<in> fmdom' \<rho>" if "x \<in> fmdom' \<Gamma>" for x
    proof -
      from that obtain \<theta> where \<theta>: "fmlookup \<Gamma> x = Some \<theta>" by (auto simp: fmlookup_dom'_iff)
      with *(3) have "\<theta> \<noteq> TypeVar" by (auto dest: tyvars_empty_entries)
      from wf_env_lookup[OF *(1) \<theta> this] show ?thesis by (auto simp: fmlookup_dom'_iff)
    qed
    then show ?thesis by auto
  qed
  then have "fmconst (fmdom' \<Gamma> - fmdom' \<rho>) VUnbound = fmempty"
    by (simp only: fmconst_def Finite_Set.fold_empty)
  with * show ?thesis by simp
qed

lemma module_env_inst:
  "\<lbrakk> module_env \<eta> \<rho> \<Gamma> ; wf_inst \<Sigma> \<eta>' ; tyvars \<Gamma> = {} \<rbrakk> \<Longrightarrow> module_env \<eta>' \<rho> \<Gamma>"
  by (auto intro: wf_env_inst)

lemma wf_mod_env: "\<turnstile> VModLoaded q \<rho> : ModChecked q \<Gamma> \<Longrightarrow> \<exists>\<eta>. module_env \<eta> \<rho> \<Gamma>"
  by (auto dest: wf_mod_checked)

lemma wf_stub: "\<turnstile> v : ModStub p \<Longrightarrow> v = VModStub p"
  by (erule wf_val.cases) auto

lemma wf_val_stub: "\<turnstile> VModStub p : \<theta> \<Longrightarrow> \<theta> = ModStub p"
  by (erule wf_val.cases) (auto elim: WfTyE WfSchemeE)

lemma unbound_entry_inst: "unbound_entry (inst_entry \<eta> \<theta>) \<longleftrightarrow> unbound_entry \<theta>"
  by (cases \<theta>) simp_all

lemma predefined_not_unbound: "\<lbrakk> fmlookup \<P> q = Some \<Gamma> ; fmlookup \<Gamma> x = Some \<theta> \<rbrakk> \<Longrightarrow> \<not> unbound_entry \<theta>"
  by (auto simp: \<P>_def fmlookup_of_list split: if_splits dest!: map_of_SomeD)

(* Lookup of a member of a module environment with the absent members unbound *)
lemma module_env_lookup:
  assumes "module_env \<eta> \<rho> \<Gamma>" and "fmlookup \<Gamma> x = Some \<theta>" and "\<theta> \<noteq> TypeVar"
  shows "(\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>) \<or> (fmlookup \<rho> x = None \<and> unbound_entry \<theta>)"
proof -
  from wf_env_lookup[OF assms(1)[THEN conjunct1] assms(2, 3)] obtain v
    where look: "fmlookup (\<rho> \<otimes> fmconst (fmdom' \<Gamma> - fmdom' \<rho>) VUnbound) x = Some v" and v: "\<turnstile> v : inst_entry \<eta> \<theta>"
    by blast
  show ?thesis
  proof (cases "fmlookup \<rho> x")
    case None
    with assms(2) have "x \<in> fmdom' \<Gamma> - fmdom' \<rho>" by (auto simp: fmlookup_dom'_iff)
    with look have "v = VUnbound" by (auto simp: fmlookup_fmconst fmlookup_dom_iff)
    with v None show ?thesis by (simp add: unbound_entry_iff[symmetric] unbound_entry_inst)
  next
    case (Some v')
    with look v show ?thesis by (auto simp: fmlookup_fmconst fmlookup_dom_iff fmlookup_dom'_iff)
  qed
qed

end

context wf_loading
begin

subsection \<open>Loaded modules\<close>

(* Environments of the loaded modules: those of the predefined modules among them, and each the environment of
   its module at the signature given by checking the module from the class table, which it leaves fixed *)
definition loaded :: "(var \<Rightarrow> ty) \<Rightarrow> (name, env) fmap \<Rightarrow> bool"
where
"loaded \<eta> \<L> =
  (fmdom \<P> |\<subseteq>| fmdom \<L>
   \<and> (\<forall>q \<rho>. fmlookup \<L> q = Some \<rho>
        \<longrightarrow> (\<exists>\<Gamma> V q'. check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>) \<and> module_env \<eta> \<rho> \<Gamma>)))"

lemma loaded_wf_inst: "loaded \<eta> \<L> \<Longrightarrow> wf_inst \<Sigma> \<eta>"
proof -
  assume L: "loaded \<eta> \<L>"
  have "builtins |\<in>| fmdom \<P>" by (simp add: \<P>_def)
  with L have "builtins |\<in>| fmdom \<L>" unfolding loaded_def by blast
  then obtain \<rho> where "fmlookup \<L> builtins = Some \<rho>" unfolding fmlookup_dom_iff by blast
  with L obtain \<Gamma> where "module_env \<eta> \<rho> \<Gamma>" unfolding loaded_def by blast
  then show ?thesis by (auto dest: wf_env_wf_inst)
qed

(* Module checked from the class table, leaving it fixed: the same signature from any check *)
lemma check_module_unique:
  assumes "settled \<M> \<Sigma>" and "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>)"
    and "check_module \<M> V' \<Sigma> q'' q = Ok (\<Gamma>', \<Sigma>')"
  shows "\<Gamma>' = \<Gamma>" and "\<Sigma>' = \<Sigma>"
proof -
  have st: "stable \<M> (\<lambda>(V, q') \<Sigma>. check_module \<M> V \<Sigma> q' q) (V, q') \<Sigma> \<Gamma> \<Sigma>"
    using check_module_stable(1)[OF assms(2) wf_class_table predefined assms(1)] by blast
  from stableD(4)[OF st fmsubset_refl fmsubset_refl wf_class_table wf_class_table, of "(V', q'')" "(\<Gamma>', \<Sigma>')"]
    assms(3)
  show "\<Gamma>' = \<Gamma>" and "\<Sigma>' = \<Sigma>" by auto
qed

lemma loaded_module:
  assumes "loaded \<eta> \<L>" and "settled \<M> \<Sigma>" and "fmlookup \<L> q = Some \<rho>" and "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>)"
  shows "module_env \<eta> \<rho> \<Gamma>"
proof -
  from assms(1, 3) obtain \<Gamma>' V' q'' where "check_module \<M> V' \<Sigma> q'' q = Ok (\<Gamma>', \<Sigma>)" and "module_env \<eta> \<rho> \<Gamma>'"
    unfolding loaded_def by blast
  with check_module_unique(1)[OF assms(2) assms(4) this(1)] show ?thesis by simp
qed

(* Signature of a module checked from the class table, leaving it fixed: well-formed and closed *)
lemma check_module_closed:
  assumes "settled \<M> \<Sigma>" and "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>)"
  shows "closed_cxt \<Sigma> \<Gamma>"
  using check_module_stable(1)[OF assms(2) wf_class_table predefined assms(1)] by blast

(* Check of a module from the class table whose table is contained in the class table: leaves it fixed *)
lemma fixed_table:
  assumes "settled \<M> \<Sigma>" and "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>\<^sub>1)" and "\<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>"
  shows "\<Sigma>\<^sub>1 = \<Sigma>"
  using stableD(1)[OF check_module_stable(1)[OF assms(2) wf_class_table predefined assms(1), THEN conjunct1]] assms(3)
  by (rule fmsubset_antisym[rotated])

(* Entries of the signature of a checked module: stubs of its submodules and entries of its body, none a
   checked module *)
lemma check_module_entries:
  assumes "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>')" and "fmlookup \<Gamma> x = Some \<theta>"
  shows "\<nexists>p \<Gamma>'. \<theta> = ModChecked p \<Gamma>'"
proof (cases "fmlookup \<P> q")
  case (Some \<Gamma>\<^sub>0)
  with assms have "fmlookup \<Gamma>\<^sub>0 x = Some \<theta>" by (simp add: check_module.simps[of \<M> V \<Sigma> q' q])
  with Some show ?thesis by (auto simp: \<P>_def fmlookup_of_list split: if_splits dest!: map_of_SomeD)
next
  case None
  from check_module_body[OF assms(1) None] obtain \<iota>s t \<Gamma>' \<Sigma>\<^sub>1 \<Gamma>\<^sub>s \<Delta> r
    where top: "check_top_stmt \<Sigma>\<^sub>1 q (the (fmlookup \<P> builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>')"
    and \<Gamma>: "\<Gamma> = submods \<M> q \<otimes> \<Delta>" .
  show ?thesis
  proof (cases "fmlookup \<Delta> x")
    case None
    with assms(2) \<Gamma> have "fmlookup (submods \<M> q) x = Some \<theta>" by (simp add: fmlookup_dom_iff)
    then show ?thesis by (auto simp: submods_lookup split: if_splits)
  next
    case (Some \<theta>')
    with assms(2) \<Gamma> have "\<theta>' = \<theta>" by (simp add: fmlookup_dom_iff)
    with check_top_stmt_entries[OF top Some] show ?thesis by auto
  qed
qed

(* Stub in the signature of a checked module: of a submodule named by the stub's variable *)
lemma check_module_stub_name:
  assumes "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>')" and "fmlookup \<Gamma> x = Some (ModStub p)"
  shows "p = Qualified q x" and "Qualified q x |\<in>| fmdom \<M>" and "fmlookup \<P> q = None"
proof -
  have "fmlookup \<P> q = None"
  proof (cases "fmlookup \<P> q")
    case (Some \<Gamma>\<^sub>0)
    with assms have "fmlookup \<Gamma>\<^sub>0 x = Some (ModStub p)" by (simp add: check_module.simps[of \<M> V \<Sigma> q' q])
    with Some show ?thesis by (auto simp: \<P>_def fmlookup_of_list split: if_splits dest!: map_of_SomeD)
  qed simp
  then show "fmlookup \<P> q = None" .
  from check_module_body[OF assms(1) this] obtain \<iota>s t \<Gamma>' \<Sigma>\<^sub>1 \<Gamma>\<^sub>s \<Delta> r
    where top: "check_top_stmt \<Sigma>\<^sub>1 q (the (fmlookup \<P> builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>')"
    and \<Gamma>: "\<Gamma> = submods \<M> q \<otimes> \<Delta>" .
  have "fmlookup \<Delta> x = None"
  proof (rule ccontr)
    assume "fmlookup \<Delta> x \<noteq> None"
    then obtain \<theta> where \<theta>: "fmlookup \<Delta> x = Some \<theta>" by auto
    with assms(2) \<Gamma> have "\<theta> = ModStub p" by (simp add: fmlookup_dom_iff)
    with check_top_stmt_entries[OF top \<theta>] show False by simp
  qed
  with assms(2) \<Gamma> have "fmlookup (submods \<M> q) x = Some (ModStub p)" by (simp add: fmlookup_dom_iff)
  then show "p = Qualified q x" and "Qualified q x |\<in>| fmdom \<M>" by (auto simp: submods_lookup split: if_splits)
qed

subsection \<open>Import environments\<close>

(* Environment and context of a loaded module extended at submodules: the environment and signature of the
   module, with some stubs of submodules replaced by loaded submodules, extended in the same way *)
inductive tree :: "(name, env) fmap \<Rightarrow> name \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> bool"
  for \<L> :: "(name, env) fmap"
where
Tree:
  "\<lbrakk> fmlookup \<L> p = Some \<rho>\<^sub>p ; check_module \<M> V \<Sigma> q' p = Ok (\<Gamma>\<^sub>p, \<Sigma>)
   ; \<forall>x. fmlookup \<rho> x = fmlookup \<rho>\<^sub>p x \<and> fmlookup G x = fmlookup \<Gamma>\<^sub>p x
        \<or> (\<exists>\<rho>\<^sub>1 G\<^sub>1. fmlookup \<rho> x = Some (VModLoaded (Qualified p x) \<rho>\<^sub>1)
             \<and> fmlookup G x = Some (ModChecked (Qualified p x) G\<^sub>1)
             \<and> (fmlookup \<rho>\<^sub>p x = None \<longrightarrow> fmlookup \<Gamma>\<^sub>p x = None)
             \<and> tree \<L> (Qualified p x) \<rho>\<^sub>1 G\<^sub>1) \<rbrakk>
  \<Longrightarrow> tree \<L> p \<rho> G"

(* The environment of a loaded module *)
lemma tree_module:
  "\<lbrakk> fmlookup \<L> p = Some \<rho>\<^sub>p ; check_module \<M> V \<Sigma> q' p = Ok (\<Gamma>\<^sub>p, \<Sigma>) \<rbrakk> \<Longrightarrow> tree \<L> p \<rho>\<^sub>p \<Gamma>\<^sub>p"
  by (rule Tree) auto

(* Replacement of the binding of a submodule's name by a loaded submodule *)
lemma tree_upd:
  assumes "tree \<L> p \<rho> G" and "tree \<L> (Qualified p x) \<rho>\<^sub>1 G\<^sub>1"
    and "fmlookup \<rho> x = None \<longrightarrow> fmlookup G x = None"
  shows "tree \<L> p (fmupd x (VModLoaded (Qualified p x) \<rho>\<^sub>1) \<rho>) (fmupd x (ModChecked (Qualified p x) G\<^sub>1) G)"
  using assms(1)
proof cases
  case (Tree \<rho>\<^sub>p V q' \<Gamma>\<^sub>p)
  have slot: "fmlookup \<rho>\<^sub>p x = None \<longrightarrow> fmlookup \<Gamma>\<^sub>p x = None" using Tree(3)[rule_format, of x] assms(3) by auto
  show ?thesis
    by (rule tree.Tree[OF Tree(1, 2)]) (use Tree(3) assms(2) slot in auto)
qed

(* Environment of a module extended at submodules, typed by the extended signature *)
lemma tree_wf:
  assumes "loaded \<eta> \<L>" and "settled \<M> \<Sigma>"
  shows "tree \<L> p \<rho> G \<Longrightarrow> module_env \<eta> \<rho> G \<and> closed_cxt \<Sigma> G"
proof (induction rule: tree.induct)
  case (Tree p \<rho>\<^sub>p V q' \<Gamma>\<^sub>p \<rho> G)
  note env\<^sub>p = loaded_module[OF assms Tree(1, 2)] and cl\<^sub>p = check_module_closed[OF assms(2) Tree(2)]
  have entry: "\<exists>\<theta>'. fmlookup G x = Some \<theta>' \<and> closed_entry \<Sigma> \<theta>'" if "x |\<in>| fmdom G" for x
    using Tree(3)[rule_format, of x] that wf_cxt_lookup[OF cl\<^sub>p[THEN conjunct1]] tyvars_empty_entries[OF cl\<^sub>p[THEN conjunct2]]
    by (auto simp: fmlookup_dom_iff)
  have cl: "closed_cxt \<Sigma> G"
  proof -
    have "closed_entry \<Sigma> \<theta>" if "fmlookup G x = Some \<theta>" for x \<theta>
      using entry[of x] that by (auto simp: fmlookup_dom_iff)
    then show ?thesis by (auto simp: wf_cxt_iff intro!: tyvars_empty)
  qed
  have dom: "fmdom \<rho> |\<subseteq>| fmdom G"
    using Tree(3) env\<^sub>p by (auto simp: fmlookup_dom_iff) (metis fmdom_notD fmlookup_dom_iff fsubsetD option.distinct(1))
  have "\<eta> \<turnstile> \<rho> \<otimes> fmconst (fmdom' G - fmdom' \<rho>) VUnbound : G"
  proof (rule WfEnv[OF wf_env_wf_inst[OF env\<^sub>p[THEN conjunct1]] cl[THEN conjunct1]], intro allI impI)
    fix x \<theta>
    assume look: "fmlookup G x = Some \<theta>" and tv: "\<theta> \<noteq> TypeVar"
    let ?pad = "fmlookup (\<rho> \<otimes> fmconst (fmdom' G - fmdom' \<rho>) VUnbound) x"
    have pad: "?pad = (case fmlookup \<rho> x of Some v \<Rightarrow> Some v | None \<Rightarrow> Some VUnbound)"
      using look by (auto simp: fmlookup_fmconst fmlookup_dom_iff fmlookup_dom'_iff split: option.splits)
    from Tree(3)[rule_format, of x] show "\<exists>v. ?pad = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
    proof
      assume base: "fmlookup \<rho> x = fmlookup \<rho>\<^sub>p x \<and> fmlookup G x = fmlookup \<Gamma>\<^sub>p x"
      with look have \<theta>: "fmlookup \<Gamma>\<^sub>p x = Some \<theta>" by simp
      from module_env_lookup[OF env\<^sub>p \<theta> tv] base pad show ?thesis
        by (auto simp: unbound_entry_iff[symmetric] unbound_entry_inst inst_entry_closed)
    next
      assume "\<exists>\<rho>\<^sub>1 G\<^sub>1. fmlookup \<rho> x = Some (VModLoaded (Qualified p x) \<rho>\<^sub>1)
             \<and> fmlookup G x = Some (ModChecked (Qualified p x) G\<^sub>1)
             \<and> (fmlookup \<rho>\<^sub>p x = None \<longrightarrow> fmlookup \<Gamma>\<^sub>p x = None)
             \<and> (tree \<L> (Qualified p x) \<rho>\<^sub>1 G\<^sub>1 \<and> module_env \<eta> \<rho>\<^sub>1 G\<^sub>1 \<and> closed_cxt \<Sigma> G\<^sub>1)"
      then obtain \<rho>\<^sub>1 G\<^sub>1 where "fmlookup \<rho> x = Some (VModLoaded (Qualified p x) \<rho>\<^sub>1)"
        and "fmlookup G x = Some (ModChecked (Qualified p x) G\<^sub>1)" and env\<^sub>1: "module_env \<eta> \<rho>\<^sub>1 G\<^sub>1" by blast
      moreover from env\<^sub>1 have "\<turnstile> VModLoaded (Qualified p x) \<rho>\<^sub>1 : ModChecked (Qualified p x) G\<^sub>1"
        by (auto intro: ValModLoaded[of \<eta>])
      ultimately show ?thesis using look pad by auto
    qed
  qed
  with dom cl show ?case by simp
qed

(* Entry of a module signature at a submodule's name: not a checked module, and its value not a loaded module *)
lemma signature_not_module:
  assumes "loaded \<eta> \<L>" and "settled \<M> \<Sigma>" and "fmlookup \<L> p = Some \<rho>\<^sub>p" and "check_module \<M> V \<Sigma> q' p = Ok (\<Gamma>\<^sub>p, \<Sigma>)"
  shows "\<forall>\<theta>. fmlookup \<Gamma>\<^sub>p x = Some \<theta> \<longrightarrow> (\<nexists>q \<Gamma>'. \<theta> = ModChecked q \<Gamma>')"
    and "\<forall>v. fmlookup \<rho>\<^sub>p x = Some v \<longrightarrow> (\<nexists>q \<rho>'. v = VModLoaded q \<rho>')"
proof -
  show entries: "\<forall>\<theta>. fmlookup \<Gamma>\<^sub>p x = Some \<theta> \<longrightarrow> (\<nexists>q \<Gamma>'. \<theta> = ModChecked q \<Gamma>')"
    using check_module_entries[OF assms(4)] by blast
  note env\<^sub>p = loaded_module[OF assms] and cl\<^sub>p = check_module_closed[OF assms(2, 4)]
  show "\<forall>v. fmlookup \<rho>\<^sub>p x = Some v \<longrightarrow> (\<nexists>q \<rho>'. v = VModLoaded q \<rho>')"
  proof (intro allI impI notI)
    fix v
    assume v: "fmlookup \<rho>\<^sub>p x = Some v" and "\<exists>q \<rho>'. v = VModLoaded q \<rho>'"
    from v have "x |\<in>| fmdom \<rho>\<^sub>p" by (simp add: fmlookup_dom_iff)
    from fsubsetD[OF env\<^sub>p[THEN conjunct2] this] obtain \<theta> where \<theta>: "fmlookup \<Gamma>\<^sub>p x = Some \<theta>"
      by (auto simp: fmlookup_dom_iff)
    have "\<theta> \<noteq> TypeVar" using cl\<^sub>p \<theta> by (auto dest: tyvars_empty_entries)
    from module_env_lookup[OF env\<^sub>p \<theta> this] v have "\<turnstile> v : inst_entry \<eta> \<theta>" by auto
    with \<open>\<exists>q \<rho>'. v = VModLoaded q \<rho>'\<close> entries \<theta> show False
      by (auto dest!: wf_mod_loaded) (cases \<theta>, auto)
  qed
qed

(* Extension of two extensions of a loaded module at submodules *)
lemma tree_extend:
  assumes "loaded \<eta> \<L>" and "settled \<M> \<Sigma>"
  shows "tree \<L> p \<rho> G \<Longrightarrow> tree \<L> p \<rho>' G' \<Longrightarrow> tree \<L> p (\<rho> \<uplus> \<rho>') (G \<uplus> G')"
proof (induction arbitrary: \<rho>' G' rule: tree.induct)
  case (Tree p \<rho>\<^sub>p V q' \<Gamma>\<^sub>p \<rho> G)
  note hyps = Tree(1-3)
  note not_module = signature_not_module[OF assms hyps(1, 2)]
  note env\<^sub>p = loaded_module[OF assms hyps(1, 2)] and cl\<^sub>p = check_module_closed[OF assms(2) hyps(2)]
  from Tree.prems show ?case
  proof cases
    case (Tree \<rho>\<^sub>p' V' q'' \<Gamma>\<^sub>p')
    with hyps(1) check_module_unique(1)[OF assms(2) hyps(2) Tree(2)]
    have \<rho>\<^sub>p': "\<rho>\<^sub>p' = \<rho>\<^sub>p" and \<Gamma>\<^sub>p': "\<Gamma>\<^sub>p' = \<Gamma>\<^sub>p" by simp_all
    show ?thesis
    proof (rule tree.Tree[OF hyps(1, 2)], intro allI)
      fix x
      have val: "extend_val v (VModLoaded (Qualified p x) \<rho>\<^sub>1) = VModLoaded (Qualified p x) \<rho>\<^sub>1"
        if "fmlookup \<rho>\<^sub>p x = Some v" for v \<rho>\<^sub>1
        using not_module(2) that by (cases v) auto
      have ent: "extend_entry \<theta> (ModChecked (Qualified p x) G\<^sub>1) = ModChecked (Qualified p x) G\<^sub>1"
        if "fmlookup \<Gamma>\<^sub>p x = Some \<theta>" for \<theta> G\<^sub>1
        using not_module(1) that by (cases \<theta>) auto
      have idem: "extend_val v v = v" if "fmlookup \<rho>\<^sub>p x = Some v" for v
        using not_module(2)[rule_format, OF that] by (cases v) auto
      have idem': "extend_entry \<theta> \<theta> = \<theta>" if "fmlookup \<Gamma>\<^sub>p x = Some \<theta>" for \<theta>
        using not_module(1)[rule_format, OF that] by (cases \<theta>) auto
      from hyps(3)[rule_format, of x] Tree(3)[rule_format, of x]
      show "fmlookup (\<rho> \<uplus> \<rho>') x = fmlookup \<rho>\<^sub>p x \<and> fmlookup (G \<uplus> G') x = fmlookup \<Gamma>\<^sub>p x
          \<or> (\<exists>\<rho>\<^sub>1 G\<^sub>1. fmlookup (\<rho> \<uplus> \<rho>') x = Some (VModLoaded (Qualified p x) \<rho>\<^sub>1)
               \<and> fmlookup (G \<uplus> G') x = Some (ModChecked (Qualified p x) G\<^sub>1)
               \<and> (fmlookup \<rho>\<^sub>p x = None \<longrightarrow> fmlookup \<Gamma>\<^sub>p x = None) \<and> tree \<L> (Qualified p x) \<rho>\<^sub>1 G\<^sub>1)"
        unfolding \<rho>\<^sub>p' \<Gamma>\<^sub>p'
      proof (elim disjE exE conjE)
        assume *: "fmlookup \<rho> x = fmlookup \<rho>\<^sub>p x" "fmlookup G x = fmlookup \<Gamma>\<^sub>p x"
          "fmlookup \<rho>' x = fmlookup \<rho>\<^sub>p x" "fmlookup G' x = fmlookup \<Gamma>\<^sub>p x"
        then have "fmlookup (\<rho> \<uplus> \<rho>') x = fmlookup \<rho>\<^sub>p x" and "fmlookup (G \<uplus> G') x = fmlookup \<Gamma>\<^sub>p x"
          by (auto simp: extend_env.simps extend_cxt.simps fmlookup_dom_iff idem idem'
              split: option.splits)
        then show ?thesis by simp
      next
        fix \<rho>\<^sub>1 G\<^sub>1
        assume *: "fmlookup \<rho> x = fmlookup \<rho>\<^sub>p x" "fmlookup G x = fmlookup \<Gamma>\<^sub>p x"
          "fmlookup \<rho>' x = Some (VModLoaded (Qualified p x) \<rho>\<^sub>1)" "fmlookup G' x = Some (ModChecked (Qualified p x) G\<^sub>1)"
          "fmlookup \<rho>\<^sub>p x = None \<longrightarrow> fmlookup \<Gamma>\<^sub>p x = None" "tree \<L> (Qualified p x) \<rho>\<^sub>1 G\<^sub>1"
        then show ?thesis
          by (auto simp: extend_env.simps extend_cxt.simps fmlookup_dom_iff val ent split: option.splits)
      next
        fix \<rho>\<^sub>1 G\<^sub>1
        assume *: "fmlookup \<rho> x = Some (VModLoaded (Qualified p x) \<rho>\<^sub>1)" "fmlookup G x = Some (ModChecked (Qualified p x) G\<^sub>1)"
          "fmlookup \<rho>\<^sub>p x = None \<longrightarrow> fmlookup \<Gamma>\<^sub>p x = None"
          "tree \<L> (Qualified p x) \<rho>\<^sub>1 G\<^sub>1"
          "\<forall>\<rho>' G'. tree \<L> (Qualified p x) \<rho>' G' \<longrightarrow> tree \<L> (Qualified p x) (\<rho>\<^sub>1 \<uplus> \<rho>') (G\<^sub>1 \<uplus> G')"
          "fmlookup \<rho>' x = fmlookup \<rho>\<^sub>p x" "fmlookup G' x = fmlookup \<Gamma>\<^sub>p x"
        show ?thesis
        proof (cases "fmlookup \<rho>\<^sub>p x")
          case None
          with *(3) have "fmlookup \<Gamma>\<^sub>p x = None" by simp
          with * None show ?thesis by (auto simp: extend_env.simps extend_cxt.simps fmlookup_dom_iff)
        next
          case (Some v)
          then have "x |\<in>| fmdom \<rho>\<^sub>p" by (simp add: fmlookup_dom_iff)
          from fsubsetD[OF env\<^sub>p[THEN conjunct2] this] obtain \<theta> where \<theta>: "fmlookup \<Gamma>\<^sub>p x = Some \<theta>"
            by (auto simp: fmlookup_dom_iff)
          have "\<theta> \<noteq> TypeVar" using cl\<^sub>p \<theta> by (auto dest: tyvars_empty_entries)
          from module_env_lookup[OF env\<^sub>p \<theta> this] Some have v: "\<turnstile> v : inst_entry \<eta> \<theta>" by auto
          show ?thesis
          proof (cases "\<theta> = ModStub (Qualified p x)")
            case True
            with v have "v = VModStub (Qualified p x)" by (auto dest: wf_stub)
            with * Some \<theta> True show ?thesis by (auto simp: extend_env.simps extend_cxt.simps fmlookup_dom_iff)
          next
            case False
            have "v \<noteq> VModStub (Qualified p x)"
            proof
              assume "v = VModStub (Qualified p x)"
              with v have "inst_entry \<eta> \<theta> = ModStub (Qualified p x)" by (auto dest: wf_val_stub)
              with False show False by (cases \<theta>) auto
            qed
            moreover have "\<nexists>q \<rho>''. v = VModLoaded q \<rho>''" using not_module(2) Some by auto
            moreover have "\<nexists>q G''. \<theta> = ModChecked q G''" using not_module(1) \<theta> by auto
            moreover from this False have "extend_entry (ModChecked (Qualified p x) G\<^sub>1) \<theta> = \<theta>" by (cases \<theta>) auto
            ultimately show ?thesis using * Some \<theta> False
              by (auto simp: extend_env.simps extend_cxt.simps fmlookup_dom_iff split: val.splits)
          qed
        qed
      next
        fix \<rho>\<^sub>1 G\<^sub>1 \<rho>\<^sub>1' G\<^sub>1'
        assume *: "fmlookup \<rho> x = Some (VModLoaded (Qualified p x) \<rho>\<^sub>1)" "fmlookup G x = Some (ModChecked (Qualified p x) G\<^sub>1)"
          "fmlookup \<rho>\<^sub>p x = None \<longrightarrow> fmlookup \<Gamma>\<^sub>p x = None"
          "tree \<L> (Qualified p x) \<rho>\<^sub>1 G\<^sub>1"
          "\<forall>\<rho>' G'. tree \<L> (Qualified p x) \<rho>' G' \<longrightarrow> tree \<L> (Qualified p x) (\<rho>\<^sub>1 \<uplus> \<rho>') (G\<^sub>1 \<uplus> G')"
          "fmlookup \<rho>' x = Some (VModLoaded (Qualified p x) \<rho>\<^sub>1')" "fmlookup G' x = Some (ModChecked (Qualified p x) G\<^sub>1')"
          "fmlookup \<rho>\<^sub>p x = None \<longrightarrow> fmlookup \<Gamma>\<^sub>p x = None" "tree \<L> (Qualified p x) \<rho>\<^sub>1' G\<^sub>1'"
        then show ?thesis by (auto simp: extend_env.simps extend_cxt.simps fmlookup_dom_iff)
      qed
    qed
  qed
qed

lemma extend_env_single:
  "(\<And>v. fmlookup \<rho> x = Some v \<Longrightarrow> extend_val v v' = v') \<Longrightarrow> \<rho> \<uplus> fmupd x v' fmempty = fmupd x v' \<rho>"
  by (auto simp: extend_env.simps intro!: fmap_ext split: option.splits)

lemma extend_cxt_single:
  "(\<And>\<theta>. fmlookup \<Gamma> x = Some \<theta> \<Longrightarrow> extend_entry \<theta> \<theta>' = \<theta>') \<Longrightarrow> \<Gamma> \<uplus> fmupd x \<theta>' fmempty = fmupd x \<theta>' \<Gamma>"
  by (auto simp: extend_cxt.simps intro!: fmap_ext split: option.splits)

(* Submodules of p named by successive variables *)
fun chain :: "name \<Rightarrow> var list \<Rightarrow> name list"
where
"chain p [] = []" |
"chain p (x # xs) = Qualified p x # chain (Qualified p x) xs"

lemma chain_snoc: "chain p (xs @ [x]) = chain p xs @ [Qualified (last (p # chain p xs)) x]"
  by (induction xs arbitrary: p) simp_all

lemma root_variables: "variables q = y # ys \<Longrightarrow> root q = y"
proof (induction q arbitrary: ys)
  case (Qualified q x)
  then show ?case using variables_nonempty[of q] by (cases "variables q") auto
qed simp

lemma proper_prefixes_chain: "variables q = y # ys \<Longrightarrow> proper_prefixes q @ [q] = Simple y # chain (Simple y) ys"
proof (induction q arbitrary: ys)
  case (Qualified q x)
  obtain ys' where ys': "variables q = y # ys'" and ys: "ys = ys' @ [x]"
    using Qualified.prems variables_nonempty[of q] by (cases "variables q") auto
  have "last (Simple y # chain (Simple y) ys') = q" unfolding Qualified.IH[OF ys', symmetric] by simp
  then show ?case using Qualified.IH[OF ys'] by (simp add: ys chain_snoc)
qed simp

(* Environment of a loaded module extended along a chain of its submodules, each loaded, at the signature
   extended by checking the chain *)
lemma chain_tree:
  assumes "loaded \<eta> \<L>" and "settled \<M> \<Sigma>"
  shows "\<lbrakk> submodules \<M> V \<Sigma> q p \<Gamma>\<^sub>p xs = Ok (\<Gamma>', \<Sigma>) ; check_module \<M> V' \<Sigma> q' p = Ok (\<Gamma>\<^sub>p, \<Sigma>)
          ; fmlookup \<L> p = Some \<rho>\<^sub>p ; \<forall>p' \<in> set (chain p xs). p' |\<in>| fmdom \<L> \<rbrakk>
    \<Longrightarrow> tree \<L> p (submod_env \<L> p xs) \<Gamma>'"
proof (induction xs arbitrary: p \<Gamma>\<^sub>p \<Gamma>' \<rho>\<^sub>p V' q')
  case Nil
  then show ?case by (auto simp: submodules.simps intro: tree_module)
next
  case (Cons x xs)
  let ?p = "Qualified p x"
  from Cons.prems(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Delta>' where m: "check_module \<M> V \<Sigma> q ?p = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and sub: "submodules \<M> V \<Sigma>\<^sub>1 q ?p \<Delta> xs = Ok (\<Delta>', \<Sigma>)"
    and \<Gamma>': "\<Gamma>' = \<Gamma>\<^sub>p \<uplus> fmupd x (ModChecked ?p \<Delta>') fmempty"
    by (auto simp: submodules.simps bind_sum_Ok)
  note st = check_module_stable(1)[OF m wf_class_table predefined assms(2)]
  note st\<^sub>1 = st[THEN conjunct1]
  have "\<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>"
    using check_module_stable(3)[OF sub stableD(2)[OF st\<^sub>1] fmsubset_trans[OF predefined stableD(1)[OF st\<^sub>1]]
        stableD(3)[OF st\<^sub>1] st[THEN conjunct2]]
    by (auto dest: stableD(1))
  with fixed_table[OF assms(2) m] have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>" by simp
  have "?p |\<in>| fmdom \<L>" using Cons.prems(4) by simp
  then obtain \<rho>\<^sub>1 where \<rho>\<^sub>1: "fmlookup \<L> ?p = Some \<rho>\<^sub>1" by (auto simp: fmlookup_dom_iff)
  have inner: "tree \<L> ?p (submod_env \<L> ?p xs) \<Delta>'"
    using Cons.IH[OF sub[unfolded \<Sigma>\<^sub>1] m[unfolded \<Sigma>\<^sub>1] \<rho>\<^sub>1] Cons.prems(4) by simp
  note not_module = signature_not_module[OF assms Cons.prems(3, 2)]
  have val: "extend_val v (VModLoaded ?p (submod_env \<L> ?p xs)) = VModLoaded ?p (submod_env \<L> ?p xs)"
    if "fmlookup \<rho>\<^sub>p x = Some v" for v
    using not_module(2)[rule_format, OF that] by (cases v) auto
  have env: "submod_env \<L> p (x # xs) = fmupd x (VModLoaded ?p (submod_env \<L> ?p xs)) \<rho>\<^sub>p"
    using Cons.prems(3) extend_env_single[OF val] by simp
  have ent: "extend_entry \<theta> (ModChecked ?p \<Delta>') = ModChecked ?p \<Delta>'" if "fmlookup \<Gamma>\<^sub>p x = Some \<theta>" for \<theta>
    using not_module(1)[rule_format, OF that] by (cases \<theta>) auto
  have cxt: "\<Gamma>' = fmupd x (ModChecked ?p \<Delta>') \<Gamma>\<^sub>p" unfolding \<Gamma>' by (rule extend_cxt_single[OF ent])
  have slot: "fmlookup \<rho>\<^sub>p x = None \<longrightarrow> fmlookup \<Gamma>\<^sub>p x = None"
  proof
    assume none: "fmlookup \<rho>\<^sub>p x = None"
    show "fmlookup \<Gamma>\<^sub>p x = None"
    proof (rule ccontr)
      assume "fmlookup \<Gamma>\<^sub>p x \<noteq> None"
      then obtain \<theta> where \<theta>: "fmlookup \<Gamma>\<^sub>p x = Some \<theta>" by auto
      have tv: "\<theta> \<noteq> TypeVar" using check_module_closed[OF assms(2) Cons.prems(2)] \<theta> by (auto dest: tyvars_empty_entries)
      from module_env_lookup[OF loaded_module[OF assms Cons.prems(3, 2)] \<theta> tv] none have unb: "unbound_entry \<theta>"
        by auto
      show False
      proof (cases "fmlookup \<P> p")
        case (Some \<Gamma>\<^sub>0)
        with Cons.prems(2) have "\<Gamma>\<^sub>p = \<Gamma>\<^sub>0" by (simp add: check_module.simps[of \<M> V' \<Sigma> q' p])
        with Some \<theta> unb show False by (auto dest: predefined_not_unbound)
      next
        case None
        have "fmlookup \<P> ?p = None" by (simp add: \<P>_def fmlookup_of_list builtins_def name_of_def)
        have pM: "?p |\<in>| fmdom \<M>"
        proof (rule ccontr)
          assume "?p |\<notin>| fmdom \<M>"
          then have "fmlookup \<M> ?p = None" by (simp add: fmlookup_dom_iff)
          with m \<open>fmlookup \<P> ?p = None\<close> show False by (simp add: check_module.simps[of \<M> V \<Sigma> q ?p] split: if_splits)
        qed
        have "fmlookup \<Gamma>\<^sub>p x = Some (ModStub ?p)" by (rule check_module_stub[OF Cons.prems(2) None pM]) simp
        with \<theta> unb show False by auto
      qed
    qed
  qed
  show ?case
    unfolding env cxt by (rule tree_upd[OF tree_module[OF Cons.prems(3, 2)] inner slot])
qed

(* Member of a module imported from it: the loaded submodule for a stub, the member's value otherwise *)
lemma member_wf:
  assumes "loaded \<eta> \<L>" and "settled \<M> \<Sigma>"
    and "imports_entry \<M> V \<Sigma> q p \<Gamma>\<^sub>p x = Ok (\<theta>, \<Sigma>)"
    and "check_module \<M> V' \<Sigma> q' p = Ok (\<Gamma>\<^sub>p, \<Sigma>)" and "fmlookup \<L> p = Some \<rho>\<^sub>p"
    and "\<forall>q''. fmlookup \<Gamma>\<^sub>p x = Some (ModStub q'') \<longrightarrow> q'' |\<in>| fmdom \<L>"
  shows "\<turnstile> member \<L> \<rho>\<^sub>p x : \<theta> \<and> closed_entry \<Sigma> \<theta> \<and> \<not> unbound_entry \<theta>"
proof -
  have env\<^sub>p: "module_env \<eta> \<rho>\<^sub>p \<Gamma>\<^sub>p" using loaded_module[OF assms(1, 2, 5, 4)] .
  have cl\<^sub>p: "closed_cxt \<Sigma> \<Gamma>\<^sub>p" using check_module_closed[OF assms(2, 4)] .
  show ?thesis
  proof (cases "\<exists>q''. fmlookup \<Gamma>\<^sub>p x = Some (ModStub q'')")
    case True
    then obtain q'' where stub: "fmlookup \<Gamma>\<^sub>p x = Some (ModStub q'')" by blast
    with assms(3) obtain \<Gamma>'' where m: "check_module \<M> V \<Sigma> q q'' = Ok (\<Gamma>'', \<Sigma>)" and \<theta>: "\<theta> = ModChecked q'' \<Gamma>''"
      by (auto simp: imports_entry.simps bind_sum_Ok)
    from module_env_lookup[OF env\<^sub>p stub] have "fmlookup \<rho>\<^sub>p x = Some (VModStub q'')"
      by (auto dest: wf_stub simp: inst_entry_closed)
    moreover from assms(6) stub obtain \<rho>'' where \<rho>'': "fmlookup \<L> q'' = Some \<rho>''" by (auto simp: fmlookup_dom_iff)
    moreover have "module_env \<eta> \<rho>'' \<Gamma>''" using loaded_module[OF assms(1, 2) \<rho>'' m] .
    ultimately show ?thesis
      using check_module_closed[OF assms(2) m] by (auto simp: \<theta> \<rho>'' intro: ValModLoaded)
  next
    case False
    with assms(3) have res: "resolve_name \<Gamma>\<^sub>p (Simple x) = Some \<theta>"
      by (auto simp: imports_entry.simps split: option.splits cxt_entry.splits)
    then have look: "fmlookup \<Gamma>\<^sub>p x = Some \<theta>" and bound: "\<not> unbound_entry \<theta>" and tv: "\<theta> \<noteq> TypeVar"
      by (auto simp: resolve_name_def split: option.splits cxt_entry.splits)
    have closed: "closed_entry \<Sigma> \<theta>"
      using wf_cxt_lookup[OF cl\<^sub>p[THEN conjunct1] look] tyvars_empty_entries[OF cl\<^sub>p[THEN conjunct2] look] by simp
    from module_env_lookup[OF env\<^sub>p look tv] bound closed obtain v where v: "fmlookup \<rho>\<^sub>p x = Some v"
      and vt: "\<turnstile> v : \<theta>"
      by (auto simp: inst_entry_closed)
    moreover have "member \<L> \<rho>\<^sub>p x = v" using v vt False look by (cases v) (auto dest!: wf_val_stub)
    ultimately show ?thesis using closed bound by simp
  qed
qed

(* Names imported from a module, each checked from the class table, leaving it fixed *)
lemma imports_entries_fixed:
  assumes "settled \<M> \<Sigma>" and "closed_cxt \<Sigma> \<Gamma>\<^sub>p" and "imports_entries \<M> V \<Sigma> q p \<Gamma>\<^sub>p xs = Ok (\<theta>s, \<Sigma>)"
  shows "list_all2 (\<lambda>x \<theta>. imports_entry \<M> V \<Sigma> q p \<Gamma>\<^sub>p x = Ok (\<theta>, \<Sigma>)) xs \<theta>s"
  using assms(3)
proof (induction xs arbitrary: \<theta>s)
  case (Cons x xs)
  from Cons.prems obtain \<theta> \<Sigma>\<^sub>1 \<theta>s' where e: "imports_entry \<M> V \<Sigma> q p \<Gamma>\<^sub>p x = Ok (\<theta>, \<Sigma>\<^sub>1)"
    and rest: "imports_entries \<M> V \<Sigma>\<^sub>1 q p \<Gamma>\<^sub>p xs = Ok (\<theta>s', \<Sigma>)" and \<theta>s: "\<theta>s = \<theta> # \<theta>s'"
    by (auto simp: imports_entries.simps bind_sum_Ok)
  note st = check_module_stable(4)[OF e wf_class_table predefined assms(1, 2), THEN conjunct1]
  have "\<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>"
    using check_module_stable(5)[OF rest stableD(2)[OF st] fmsubset_trans[OF predefined stableD(1)[OF st]]
        stableD(3)[OF st] closed_cxt_mono[OF assms(2) stableD(1)[OF st]]]
    by (auto dest: stableD(1))
  with stableD(1)[OF st] have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>" by (rule fmsubset_antisym[rotated])
  from Cons.IH[OF rest[unfolded \<Sigma>\<^sub>1]] e show ?case by (simp add: \<theta>s \<Sigma>\<^sub>1)
qed (simp add: imports_entries.simps)

(* Roots of the plain imports, and names of the from-imports *)
fun roots :: "import located list \<Rightarrow> var set"
where
"roots [] = {}" |
"roots (At _ (Import q) # \<iota>s) = insert (root q) (roots \<iota>s)" |
"roots (At _ (FromImport _ _) # \<iota>s) = roots \<iota>s"

fun from_names :: "import located list \<Rightarrow> var set"
where
"from_names [] = {}" |
"from_names (At _ (Import _) # \<iota>s) = from_names \<iota>s" |
"from_names (At _ (FromImport _ xs) # \<iota>s) = set xs \<union> from_names \<iota>s"

lemma declarations_imports_names: "node ` set (declarations_imports \<iota>s) = roots \<iota>s \<union> from_names \<iota>s"
proof (induction \<iota>s rule: declarations_imports.induct)
  case (2 p q \<iota>s)
  have "root q \<in> roots \<iota>s" if "list_ex (\<lambda>\<iota>. case node \<iota> of Import q' \<Rightarrow> root q' = root q | _ \<Rightarrow> False) \<iota>s"
    using that by (induction \<iota>s rule: roots.induct) auto
  with 2 show ?case by auto
qed (auto simp: image_Un image_image)

lemma roots_from_names_disjoint:
  "distinct (map node (declarations_imports \<iota>s)) \<Longrightarrow> roots \<iota>s \<inter> from_names \<iota>s = {}"
proof (induction \<iota>s rule: declarations_imports.induct)
  case (2 p q \<iota>s)
  have "root q \<in> roots \<iota>s" if "list_ex (\<lambda>\<iota>. case node \<iota> of Import q' \<Rightarrow> root q' = root q | _ \<Rightarrow> False) \<iota>s"
    using that by (induction \<iota>s rule: roots.induct) auto
  with 2 show ?case by (auto simp: declarations_imports_names split: if_splits)
qed (auto simp: declarations_imports_names)

(* Names bound by the context of imports, declared by them *)
lemma check_imports_dom:
  "\<lbrakk> check_imports \<M> V \<Sigma> q \<iota>s = Ok (\<Gamma>, \<Sigma>') ; x |\<in>| fmdom \<Gamma> \<rbrakk> \<Longrightarrow> x \<in> roots \<iota>s \<union> from_names \<iota>s"
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
    from Cons.prems(2) Cons.IH[OF rest] root_variables[OF vars] show ?thesis by (auto simp: \<iota> Import \<Gamma>)
  next
    case (FromImport q' xs)
    from Cons.prems(1) obtain \<Sigma>\<^sub>2 \<Delta> \<Sigma>\<^sub>3 \<theta>s \<Gamma>'' where ent: "imports_entries \<M> V \<Sigma>\<^sub>2 q q' \<Delta> xs = Ok (\<theta>s, \<Sigma>\<^sub>3)"
      and rest: "check_imports \<M> V \<Sigma>\<^sub>3 q \<iota>s = Ok (\<Gamma>'', \<Sigma>')" and \<Gamma>: "\<Gamma> = fmap_of_list (zip xs \<theta>s) \<uplus> \<Gamma>''"
      by (auto simp: \<iota> FromImport check_imports.simps bind_sum_Ok split: option.splits simp del: check_module.simps)
    from Cons.prems(2) Cons.IH[OF rest] show ?thesis
      by (auto simp: \<iota> FromImport \<Gamma> fset_of_list_elem dest: set_zip_leftD)
  qed
qed (simp add: check_imports.simps)

(* Modules whose environments the evaluation of an import looks up *)
fun needs :: "import \<Rightarrow> name set"
where
"needs (Import q') = set (proper_prefixes q') \<union> {q'}" |
"needs (FromImport q' xs) =
   insert q' {Qualified q' x | x. x \<in> set xs \<and> Qualified q' x |\<in>| fmdom \<M>
                \<and> (case fmlookup \<M> q' of Some b \<Rightarrow> x \<notin> set (declares b) | None \<Rightarrow> False)}"

(* Stub in the signature of a module: the submodule it names is loaded by an import of the name *)
lemma stub_needed:
  assumes "check_module \<M> V \<Sigma> q' p = Ok (\<Gamma>\<^sub>p, \<Sigma>')" and "fmlookup \<Gamma>\<^sub>p x = Some (ModStub q'')" and "x \<in> set xs"
  shows "q'' \<in> needs (FromImport p xs)"
proof -
  from check_module_stub_name[OF assms(1, 2)] have q'': "q'' = Qualified p x" and dom: "Qualified p x |\<in>| fmdom \<M>"
    and "fmlookup \<P> p = None"
    by simp_all
  from check_module_stub[OF assms(1) this(3) dom] obtain \<iota>s t where "fmlookup \<M> p = Some (ModuleBody \<iota>s t)"
    and "x \<notin> set (declares \<iota>s)" and "x \<notin> set (declares t)" .
  with dom assms(3) show ?thesis by (auto simp: q'')
qed

(* Bindings of the environment of imports at their context: each root of a plain import bound to the root
   module extended at submodules, and each name of a from-import to a value typed by its entry *)
definition import_bindings :: "import located list \<Rightarrow> (name, env) fmap \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> bool"
where
"import_bindings \<iota>s \<L> \<rho> \<Gamma> =
  (fmdom \<rho> = fmdom \<Gamma>
   \<and> (\<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta>
        \<longrightarrow> x \<in> roots \<iota>s \<and> (\<exists>G \<rho>'. \<theta> = ModChecked (Simple x) G \<and> fmlookup \<rho> x = Some (VModLoaded (Simple x) \<rho>')
                                 \<and> tree \<L> (Simple x) \<rho>' G)
          \<or> x \<in> from_names \<iota>s \<and> (\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : \<theta> \<and> closed_entry \<Sigma> \<theta> \<and> \<not> unbound_entry \<theta>)))"

lemma import_bindings_env:
  assumes "loaded \<eta> \<L>" and "settled \<M> \<Sigma>" and "import_bindings \<iota>s \<L> \<rho> \<Gamma>"
  shows "module_env \<eta> \<rho> \<Gamma>" and "closed_cxt \<Sigma> \<Gamma>" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and "\<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> \<not> unbound_entry \<theta>"
proof -
  have entry: "\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : \<theta> \<and> closed_entry \<Sigma> \<theta>" if "fmlookup \<Gamma> x = Some \<theta>" for x \<theta>
    using assms(3)[unfolded import_bindings_def, THEN conjunct2, rule_format, OF that]
  proof
    assume "x \<in> roots \<iota>s \<and> (\<exists>G \<rho>'. \<theta> = ModChecked (Simple x) G \<and> fmlookup \<rho> x = Some (VModLoaded (Simple x) \<rho>')
                                 \<and> tree \<L> (Simple x) \<rho>' G)"
    then obtain G \<rho>' where \<theta>: "\<theta> = ModChecked (Simple x) G" and v: "fmlookup \<rho> x = Some (VModLoaded (Simple x) \<rho>')"
      and tr: "tree \<L> (Simple x) \<rho>' G" by blast
    from tree_wf[OF assms(1, 2) tr] have env: "module_env \<eta> \<rho>' G" and cl: "closed_cxt \<Sigma> G" by auto
    from env have "\<turnstile> VModLoaded (Simple x) \<rho>' : ModChecked (Simple x) G" by (auto intro: ValModLoaded[of \<eta>])
    with v cl show ?thesis unfolding \<theta> by simp
  qed blast
  then show cl: "closed_cxt \<Sigma> \<Gamma>" by (auto simp: wf_cxt_iff intro!: tyvars_empty)
  have "fmdom' \<Gamma> - fmdom' \<rho> = {}" using assms(3) by (simp add: import_bindings_def fmdom'_alt_def)
  then have "fmconst (fmdom' \<Gamma> - fmdom' \<rho>) VUnbound = fmempty" by (simp only: fmconst_def Finite_Set.fold_empty)
  then have "\<rho> \<otimes> fmconst (fmdom' \<Gamma> - fmdom' \<rho>) VUnbound = \<rho>" by simp
  moreover show "\<eta> \<turnstile> \<rho> : \<Gamma>"
  proof (rule WfEnv[OF loaded_wf_inst[OF assms(1)] cl[THEN conjunct1]], intro allI impI)
    fix x \<theta>
    assume "fmlookup \<Gamma> x = Some \<theta>" and "\<theta> \<noteq> TypeVar"
    from entry[OF this(1)] show "\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>" by (auto simp: inst_entry_closed)
  qed
  ultimately show "module_env \<eta> \<rho> \<Gamma>" using assms(3) by (simp add: import_bindings_def)
  show "\<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> \<not> unbound_entry \<theta>"
  proof (intro allI impI)
    fix x \<theta>
    assume "fmlookup \<Gamma> x = Some \<theta>"
    from assms(3)[unfolded import_bindings_def, THEN conjunct2, rule_format, OF this] show "\<not> unbound_entry \<theta>" by auto
  qed
qed

(* Environment of the imports of a module, at their context *)
lemma imports_env_wf:
  assumes "loaded \<eta> \<L>" and "settled \<M> \<Sigma>" and "check_imports \<M> V \<Sigma> q \<iota>s = Ok (\<Gamma>, \<Sigma>)"
    and "distinct (map node (declarations \<iota>s))" and "\<forall>\<iota> \<in> set \<iota>s. \<forall>p \<in> needs (node \<iota>). p |\<in>| fmdom \<L>"
  shows "import_bindings \<iota>s \<L> (imports_env \<L> \<iota>s) \<Gamma>"
  using assms(3-5)
proof (induction \<iota>s arbitrary: \<Gamma>)
  case Nil
  then show ?case by (simp add: check_imports.simps import_bindings_def)
next
  case (Cons \<iota> \<iota>s)
  obtain p i where \<iota>: "\<iota> = At p i" by (cases \<iota>)
  show ?case
  proof (cases i)
    case (Import q')
    obtain y ys where vars: "variables q' = y # ys" using variables_nonempty by (cases "variables q'") auto
    from Cons.prems(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Delta>' \<Sigma>\<^sub>2 \<Gamma>'' where m: "check_module \<M> V \<Sigma> q (Simple y) = Ok (\<Delta>, \<Sigma>\<^sub>1)"
      and sub: "submodules \<M> V \<Sigma>\<^sub>1 q (Simple y) \<Delta> ys = Ok (\<Delta>', \<Sigma>\<^sub>2)"
      and rest: "check_imports \<M> V \<Sigma>\<^sub>2 q \<iota>s = Ok (\<Gamma>'', \<Sigma>)"
      and \<Gamma>: "\<Gamma> = fmupd y (ModChecked (Simple y) \<Delta>') fmempty \<uplus> \<Gamma>''"
      by (auto simp: \<iota> Import check_imports.simps vars bind_sum_Ok)
    note st\<^sub>1 = check_module_stable(1)[OF m wf_class_table predefined assms(2), THEN conjunct1]
    note sub1 = stableD(1)[OF st\<^sub>1] and wf1 = stableD(2)[OF st\<^sub>1] and set1 = stableD(3)[OF st\<^sub>1]
    have pre1: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using predefined sub1 by (rule fmsubset_trans)
    have cl\<Delta>: "closed_cxt \<Sigma>\<^sub>1 \<Delta>" using check_module_stable(1)[OF m wf_class_table predefined assms(2)] by blast
    note st\<^sub>2 = check_module_stable(3)[OF sub wf1 pre1 set1 cl\<Delta>, THEN conjunct1]
    note sub2 = stableD(1)[OF st\<^sub>2] and wf2 = stableD(2)[OF st\<^sub>2] and set2 = stableD(3)[OF st\<^sub>2]
    have pre2: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>2" using pre1 sub2 by (rule fmsubset_trans)
    note st\<^sub>3 = check_module_stable(2)[OF rest wf2 pre2 set2, THEN conjunct1]
    have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>" using sub1 fmsubset_trans[OF sub2 stableD(1)[OF st\<^sub>3]] by (rule fmsubset_antisym[rotated])
    have \<Sigma>\<^sub>2: "\<Sigma>\<^sub>2 = \<Sigma>" using sub2[unfolded \<Sigma>\<^sub>1] stableD(1)[OF st\<^sub>3] by (rule fmsubset_antisym[rotated])
    have needs: "\<forall>p' \<in> set (Simple y # chain (Simple y) ys). p' |\<in>| fmdom \<L>"
      using Cons.prems(3) unfolding proper_prefixes_chain[OF vars, symmetric] by (auto simp: \<iota> Import)
    then obtain \<rho>\<^sub>y where \<rho>\<^sub>y: "fmlookup \<L> (Simple y) = Some \<rho>\<^sub>y" by (auto simp: fmlookup_dom_iff)
    have chain: "tree \<L> (Simple y) (submod_env \<L> (Simple y) ys) \<Delta>'"
      by (rule chain_tree[OF assms(1, 2) sub[unfolded \<Sigma>\<^sub>1 \<Sigma>\<^sub>2] m[unfolded \<Sigma>\<^sub>1] \<rho>\<^sub>y]) (use needs in simp)
    have distinct: "distinct (map node (declarations \<iota>s))" and "y \<notin> from_names \<iota>s"
      using Cons.prems(2) roots_from_names_disjoint[of "\<iota> # \<iota>s"] root_variables[OF vars]
      by (auto simp: \<iota> Import declares_imports_def declarations_imports_names split: if_splits)
    note IH = Cons.IH[OF rest[unfolded \<Sigma>\<^sub>2] distinct]
    have IH: "import_bindings \<iota>s \<L> (imports_env \<L> \<iota>s) \<Gamma>''" using IH Cons.prems(3) by (simp add: \<iota>)
    let ?\<rho>\<^sub>y = "fmupd y (VModLoaded (Simple y) (submod_env \<L> (Simple y) ys)) \<epsilon>"
    show ?thesis
      unfolding import_bindings_def
    proof (intro conjI allI impI)
      show "fmdom (imports_env \<L> (\<iota> # \<iota>s)) = fmdom \<Gamma>"
        using IH by (simp add: \<iota> Import vars \<Gamma> import_bindings_def extend_env.simps)
      fix x \<theta>
      assume look: "fmlookup \<Gamma> x = Some \<theta>"
      show "x \<in> roots (\<iota> # \<iota>s) \<and> (\<exists>G \<rho>'. \<theta> = ModChecked (Simple x) G
                \<and> fmlookup (imports_env \<L> (\<iota> # \<iota>s)) x = Some (VModLoaded (Simple x) \<rho>') \<and> tree \<L> (Simple x) \<rho>' G)
            \<or> x \<in> from_names (\<iota> # \<iota>s) \<and> (\<exists>v. fmlookup (imports_env \<L> (\<iota> # \<iota>s)) x = Some v \<and> \<turnstile> v : \<theta> \<and> closed_entry \<Sigma> \<theta>
                 \<and> \<not> unbound_entry \<theta>)"
      proof (cases "x = y")
        case False
        with look have "fmlookup \<Gamma>'' x = Some \<theta>"
          by (auto simp: \<Gamma> extend_cxt.simps fmlookup_dom_iff split: if_splits option.splits)
        from IH[unfolded import_bindings_def, THEN conjunct2, rule_format, OF this] False
        show ?thesis by (auto simp: \<iota> Import vars extend_env.simps fmlookup_dom_iff)
      next
        case True
        show ?thesis
        proof (cases "fmlookup \<Gamma>'' y")
          case None
          with look True have "\<theta> = ModChecked (Simple y) \<Delta>'" by (simp add: \<Gamma> extend_cxt.simps fmlookup_dom_iff)
          moreover have "fmlookup (imports_env \<L> \<iota>s) y = None"
            using IH None unfolding import_bindings_def by (metis fmdom_notD fmdom_notI)
          ultimately show ?thesis using chain root_variables[OF vars] True
            by (auto simp: \<iota> Import vars extend_env.simps fmlookup_dom_iff)
        next
          case (Some \<theta>'')
          from IH[unfolded import_bindings_def, THEN conjunct2, rule_format, OF Some] \<open>y \<notin> from_names \<iota>s\<close>
          obtain G \<rho>' where \<theta>'': "\<theta>'' = ModChecked (Simple y) G"
            and \<rho>': "fmlookup (imports_env \<L> \<iota>s) y = Some (VModLoaded (Simple y) \<rho>')" and tr: "tree \<L> (Simple y) \<rho>' G"
            by blast
          with look Some True have "\<theta> = ModChecked (Simple y) (\<Delta>' \<uplus> G)" by (simp add: \<Gamma> extend_cxt.simps fmlookup_dom_iff)
          moreover have "fmlookup (imports_env \<L> (\<iota> # \<iota>s)) y = Some (VModLoaded (Simple y) (submod_env \<L> (Simple y) ys \<uplus> \<rho>'))"
            using \<rho>' by (simp add: \<iota> Import vars extend_env.simps fmlookup_dom_iff)
          moreover have "y \<in> roots (\<iota> # \<iota>s)" using root_variables[OF vars] by (simp add: \<iota> Import)
          ultimately show ?thesis unfolding True using tree_extend[OF assms(1, 2) chain tr] by blast
        qed
      qed
    qed
  next
    case (FromImport q' xs)
    from Cons.prems(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 \<theta>s \<Sigma>\<^sub>3 \<Gamma>'' where m: "check_module \<M> V \<Sigma> q q' = Ok (\<Delta>, \<Sigma>\<^sub>1)"
      and ms: "check_modules \<M> V \<Sigma>\<^sub>1 q (unique_to q' q) = Ok \<Sigma>\<^sub>2" and red: "redeclared id {} xs = None"
      and ent: "imports_entries \<M> V \<Sigma>\<^sub>2 q q' \<Delta> xs = Ok (\<theta>s, \<Sigma>\<^sub>3)"
      and rest: "check_imports \<M> V \<Sigma>\<^sub>3 q \<iota>s = Ok (\<Gamma>'', \<Sigma>)" and \<Gamma>: "\<Gamma> = fmap_of_list (zip xs \<theta>s) \<uplus> \<Gamma>''"
      by (auto simp: \<iota> FromImport check_imports.simps bind_sum_Ok split: option.splits simp del: check_module.simps)
    note st\<^sub>1 = check_module_stable(1)[OF m wf_class_table predefined assms(2), THEN conjunct1]
    note sub1 = stableD(1)[OF st\<^sub>1] and wf1 = stableD(2)[OF st\<^sub>1] and set1 = stableD(3)[OF st\<^sub>1]
    have pre1: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using predefined sub1 by (rule fmsubset_trans)
    have cl\<Delta>: "closed_cxt \<Sigma>\<^sub>1 \<Delta>" using check_module_stable(1)[OF m wf_class_table predefined assms(2)] by blast
    note st\<^sub>2 = check_module_stable(6)[OF ms wf1 pre1 set1]
    note sub2 = stableD(1)[OF st\<^sub>2] and wf2 = stableD(2)[OF st\<^sub>2] and set2 = stableD(3)[OF st\<^sub>2]
    have pre2: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>2" using pre1 sub2 by (rule fmsubset_trans)
    note st\<^sub>3 = check_module_stable(5)[OF ent wf2 pre2 set2 closed_cxt_mono[OF cl\<Delta> sub2], THEN conjunct1]
    note sub3 = stableD(1)[OF st\<^sub>3] and wf3 = stableD(2)[OF st\<^sub>3] and set3 = stableD(3)[OF st\<^sub>3]
    have pre3: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>3" using pre2 sub3 by (rule fmsubset_trans)
    note st\<^sub>4 = check_module_stable(2)[OF rest wf3 pre3 set3, THEN conjunct1]
    have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>" using sub1 fmsubset_trans[OF sub2 fmsubset_trans[OF sub3 stableD(1)[OF st\<^sub>4]]] by (rule fmsubset_antisym[rotated])
    have \<Sigma>\<^sub>2: "\<Sigma>\<^sub>2 = \<Sigma>" using sub2[unfolded \<Sigma>\<^sub>1] fmsubset_trans[OF sub3 stableD(1)[OF st\<^sub>4]] by (rule fmsubset_antisym[rotated])
    have \<Sigma>\<^sub>3: "\<Sigma>\<^sub>3 = \<Sigma>" using sub3[unfolded \<Sigma>\<^sub>2] stableD(1)[OF st\<^sub>4] by (rule fmsubset_antisym[rotated])
    have distinct: "distinct (map node (declarations \<iota>s))" and fresh: "set xs \<inter> (roots \<iota>s \<union> from_names \<iota>s) = {}"
      and distinct_xs: "distinct xs"
      using Cons.prems(2) by (auto simp: \<iota> FromImport declares_imports_def declarations_imports_names comp_def)
    have IH: "import_bindings \<iota>s \<L> (imports_env \<L> \<iota>s) \<Gamma>''"
      using Cons.IH[OF rest[unfolded \<Sigma>\<^sub>3] distinct] Cons.prems(3) by (simp add: \<iota>)
    have "q' |\<in>| fmdom \<L>" using Cons.prems(3) by (simp add: \<iota> FromImport)
    then obtain \<rho>\<^sub>q where \<rho>\<^sub>q: "fmlookup \<L> q' = Some \<rho>\<^sub>q" by (auto simp: fmlookup_dom_iff)
    note entries = imports_entries_fixed[OF assms(2) cl\<Delta>[unfolded \<Sigma>\<^sub>1] ent[unfolded \<Sigma>\<^sub>2 \<Sigma>\<^sub>3]]
    have member: "\<turnstile> member \<L> \<rho>\<^sub>q x : \<theta> \<and> closed_entry \<Sigma> \<theta> \<and> \<not> unbound_entry \<theta>"
      if "imports_entry \<M> V \<Sigma> q q' \<Delta> x = Ok (\<theta>, \<Sigma>)" and "x \<in> set xs"
      for x \<theta>
    proof (rule member_wf[OF assms(1, 2) that(1) m[unfolded \<Sigma>\<^sub>1] \<rho>\<^sub>q], intro allI impI)
      fix q''
      assume "fmlookup \<Delta> x = Some (ModStub q'')"
      from stub_needed[OF m this that(2)] Cons.prems(3) show "q'' |\<in>| fmdom \<L>" by (auto simp: \<iota> FromImport)
    qed
    have len: "length \<theta>s = length xs" using entries by (simp add: list_all2_lengthD)
    show ?thesis
      unfolding import_bindings_def
    proof (intro conjI allI impI)
      show "fmdom (imports_env \<L> (\<iota> # \<iota>s)) = fmdom \<Gamma>"
        using IH len by (simp add: \<iota> FromImport \<Gamma> import_bindings_def extend_env.simps comp_def)
      fix x \<theta>
      assume look: "fmlookup \<Gamma> x = Some \<theta>"
      show "x \<in> roots (\<iota> # \<iota>s) \<and> (\<exists>G \<rho>'. \<theta> = ModChecked (Simple x) G
                \<and> fmlookup (imports_env \<L> (\<iota> # \<iota>s)) x = Some (VModLoaded (Simple x) \<rho>') \<and> tree \<L> (Simple x) \<rho>' G)
            \<or> x \<in> from_names (\<iota> # \<iota>s) \<and> (\<exists>v. fmlookup (imports_env \<L> (\<iota> # \<iota>s)) x = Some v \<and> \<turnstile> v : \<theta> \<and> closed_entry \<Sigma> \<theta>
                 \<and> \<not> unbound_entry \<theta>)"
      proof (cases "x \<in> set xs")
        case False
        with look have look'': "fmlookup \<Gamma>'' x = Some \<theta>"
          by (auto simp: \<Gamma> extend_cxt.simps fmlookup_dom_iff fset_of_list_elem len fmlookup_of_list map_of_eq_None_iff
              split: if_splits option.splits dest!: map_of_SomeD dest: set_zip_leftD)
        have none: "map_of (map (\<lambda>x. (x, g x)) xs) x = None" for g :: "var \<Rightarrow> val"
          using False by (simp add: map_of_eq_None_iff image_image)
        from IH[unfolded import_bindings_def, THEN conjunct2, rule_format, OF look''] False
        show ?thesis by (auto simp: \<iota> FromImport extend_env.simps fmlookup_dom_iff fmlookup_of_list none)
      next
        case True
        then obtain i where i: "i < length xs" and x: "x = xs ! i" by (auto simp: in_set_conv_nth)
        have "x |\<notin>| fmdom \<Gamma>''" using check_imports_dom[OF rest[unfolded \<Sigma>\<^sub>3]] fresh True by blast
        then have \<Gamma>''x: "fmlookup \<Gamma>'' x = None" by (rule fmdom_notD)
        with look have \<theta>: "fmlookup (fmap_of_list (zip xs \<theta>s)) x = Some \<theta>" by (simp add: \<Gamma> extend_cxt.simps fmlookup_dom_iff)
        then have \<theta>i: "\<theta> = \<theta>s ! i"
          using map_of_zip_nth[of xs \<theta>s i] distinct_xs i x len by (simp add: fmlookup_of_list)
        have "imports_entry \<M> V \<Sigma> q q' \<Delta> x = Ok (\<theta>, \<Sigma>)" using entries i x \<theta>i by (auto simp: list_all2_conv_all_nth)
        from member[OF this True] have "\<turnstile> member \<L> \<rho>\<^sub>q x : \<theta>" and "closed_entry \<Sigma> \<theta>" and "\<not> unbound_entry \<theta>"
          by simp_all
        moreover have "fmlookup (imports_env \<L> (\<iota> # \<iota>s)) x = Some (member \<L> \<rho>\<^sub>q x)"
        proof -
          have notB: "fmlookup (imports_env \<L> \<iota>s) x = None"
            using IH \<Gamma>''x unfolding import_bindings_def by (metis fmdom_notD fmdom_notI)
          have inA: "map_of (map (\<lambda>x. (x, member \<L> \<rho>\<^sub>q x)) xs) x = Some (member \<L> \<rho>\<^sub>q x)"
            using True by (induction xs) (auto simp del: member.simps)
          show ?thesis
            by (simp add: \<iota> FromImport extend_env.simps fmlookup_dom_iff fmlookup_of_list notB \<rho>\<^sub>q inA
                del: member.simps)
        qed
        ultimately show ?thesis using True by (auto simp: \<iota> FromImport)
      qed
    qed
  qed
qed

subsection \<open>Modules\<close>

lemma scope_top_Some: "scope_top u ys t = Some m \<Longrightarrow> m = fmconst (assigns t - set ys) u"
  by (simp add: scope_top_def split: if_splits)

(* Module environment at a signature none of whose entries is that of a possibly unbound variable: typed by the
   signature *)
lemma module_env_definite:
  assumes "module_env \<eta> \<rho> \<Gamma>" and "\<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> \<not> unbound_entry \<theta>" and "tyvars \<Gamma> = {}"
  shows "\<eta> \<turnstile> \<rho> : \<Gamma>"
proof -
  have "x \<in> fmdom' \<rho>" if "x \<in> fmdom' \<Gamma>" for x
  proof -
    from that obtain \<theta> where \<theta>: "fmlookup \<Gamma> x = Some \<theta>" by (auto simp: fmlookup_dom'_iff)
    with assms(3) have "\<theta> \<noteq> TypeVar" by (auto dest: tyvars_empty_entries)
    from module_env_lookup[OF assms(1) \<theta> this] assms(2) \<theta> show ?thesis by (auto simp: fmlookup_dom'_iff)
  qed
  then have "fmdom' \<Gamma> - fmdom' \<rho> = {}" by auto
  with assms(1) show ?thesis by (simp add: fmconst_def)
qed

(* Class table containing a table from which a top-level statement is checked to the class table: that table *)
lemma adds_fixed: "\<lbrakk> \<Sigma> \<subseteq>\<^sub>f \<Sigma>\<^sub>1 ; \<Sigma> = \<Sigma>\<^sub>1 \<otimes> E \<rbrakk> \<Longrightarrow> \<Sigma>\<^sub>1 = \<Sigma>"
proof (rule fmsubset_antisym[rotated])
  assume sub: "\<Sigma> \<subseteq>\<^sub>f \<Sigma>\<^sub>1" and E: "\<Sigma> = \<Sigma>\<^sub>1 \<otimes> E"
  show "\<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>"
  proof (auto simp: fmsubset_alt_def fmpred_iff)
    fix C ce
    assume C: "fmlookup \<Sigma>\<^sub>1 C = Some ce"
    show "fmlookup \<Sigma> C = Some ce"
    proof (cases "fmlookup E C")
      case None
      with E C show ?thesis by (simp add: fmlookup_dom_iff)
    next
      case (Some ce')
      with E have "fmlookup \<Sigma> C = Some ce'" by (simp add: fmlookup_dom_iff)
      with fmsubset_lookup[OF sub this] C show ?thesis by simp
    qed
  qed
qed

(* Soundness of module evaluation, for a module checked from the class table, leaving it fixed, whose imports
   are loaded: the module does not abort with a prevented error, and its environment is typed by its signature *)
lemma mod_sound:
  assumes "q, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d o" and "loaded \<eta> \<L>" and "settled \<M> \<Sigma>"
    and chk: "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>)" and "fmlookup \<P> q = None"
    and needs: "\<forall>\<iota>s t. fmlookup \<M> q = Some (ModuleBody \<iota>s t) \<longrightarrow> (\<forall>\<iota> \<in> set \<iota>s. \<forall>p \<in> needs (node \<iota>). p |\<in>| fmdom \<L>)"
  shows "(\<forall>vs \<kappa>. o = (vs, Aborts\<^sub>\<omega> \<kappa>) \<longrightarrow> \<not> prevented \<kappa>)
    \<and> (\<forall>vs \<rho>. o = (vs, Assigns \<rho>) \<longrightarrow> module_env \<eta> (submods_env q \<otimes> \<rho>) \<Gamma>)"
proof -
  from assms(1) obtain \<iota>s t \<rho>\<^sub>s where M: "fmlookup \<M> q = Some (ModuleBody \<iota>s t)"
    and sc: "scope VUnbound (declares \<iota>s) t = Some \<rho>\<^sub>s"
    and ev: "q, the (fmlookup \<L> builtins) \<otimes> imports_env \<L> \<iota>s \<otimes> \<rho>\<^sub>s, t \<Rightarrow>\<^sub>t o"
    by (rule ModE)
  from check_module_body[OF chk assms(5)] obtain \<iota>s' t' \<Gamma>' \<Sigma>\<^sub>1 \<Gamma>\<^sub>s \<Delta> r
    where "fmlookup \<M> q = Some (ModuleBody \<iota>s' t')"
    and imp: "check_imports \<M> (V @ [q]) \<Sigma> q \<iota>s' = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
    and red: "redeclared node {} (declarations \<iota>s') = None"
    and sc': "scope Unbound (declares \<iota>s') t' = Some \<Gamma>\<^sub>s"
    and cad: "check_assignments_declared {} (assign_targets t') (declares t') (binds t') = Ok ()"
    and top: "check_top_stmt \<Sigma>\<^sub>1 q (the (fmlookup \<P> builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t' = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>)"
    and X: "(fmdom \<Gamma>' |\<union>| fmdom \<Gamma>\<^sub>s) |\<inter>| fmdom (submods \<M> q) = {||}" and \<Gamma>: "\<Gamma> = submods \<M> q \<otimes> \<Delta>" .
  with M have \<iota>s': "\<iota>s' = \<iota>s" and t': "t' = t" by simp_all
  note imp = imp[unfolded \<iota>s'] and sc' = sc'[unfolded \<iota>s' t'] and top = top[unfolded t'] and red = red[unfolded \<iota>s']
    and cad = cad[unfolded t']
  note st = check_module_stable(2)[OF imp wf_class_table predefined assms(3)]
  have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>"
  proof -
    from check_top_stmt_adds[OF top] obtain E where "\<Sigma> = \<Sigma>\<^sub>1 \<otimes> E" by blast
    then show ?thesis by (rule adds_fixed[OF stableD(1)[OF st[THEN conjunct1]]])
  qed
  note imp = imp[unfolded \<Sigma>\<^sub>1] and top = top[unfolded \<Sigma>\<^sub>1]
  let ?\<rho>\<^sub>b = "the (fmlookup \<L> builtins)" and ?\<Gamma>\<^sub>b = "the (fmlookup \<P> builtins)"
  let ?\<rho>\<^sub>0 = "?\<rho>\<^sub>b \<otimes> imports_env \<L> \<iota>s \<otimes> \<rho>\<^sub>s" and ?\<Gamma>\<^sub>0 = "?\<Gamma>\<^sub>b \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s"
  (* The environment of the body, typed by its context *)
  have "builtins |\<in>| fmdom \<P>" by (simp add: \<P>_def)
  with assms(2) have "builtins |\<in>| fmdom \<L>" unfolding loaded_def by blast
  then obtain \<rho>\<^sub>b where \<rho>\<^sub>b: "fmlookup \<L> builtins = Some \<rho>\<^sub>b" unfolding fmlookup_dom_iff by blast
  have "check_module \<M> V \<Sigma> q' builtins = Ok (?\<Gamma>\<^sub>b, \<Sigma>)"
    by (simp add: check_module.simps[of \<M> V \<Sigma> q' builtins] \<P>_def fmlookup_of_list builtins_def name_of_def)
  from loaded_module[OF assms(2, 3) \<rho>\<^sub>b this] have "module_env \<eta> \<rho>\<^sub>b ?\<Gamma>\<^sub>b" .
  then have env\<^sub>b: "\<eta> \<turnstile> ?\<rho>\<^sub>b : ?\<Gamma>\<^sub>b"
  proof -
    assume me: "module_env \<eta> \<rho>\<^sub>b ?\<Gamma>\<^sub>b"
    have "\<forall>x \<theta>. fmlookup ?\<Gamma>\<^sub>b x = Some \<theta> \<longrightarrow> \<not> unbound_entry \<theta>"
      using predefined_not_unbound[of builtins ?\<Gamma>\<^sub>b] by (simp add: \<P>_def)
    from module_env_definite[OF me this builtins_closed[OF predefined, THEN conjunct2]] \<rho>\<^sub>b show ?thesis by simp
  qed
  have distinct: "distinct (map node (declarations \<iota>s))" using redeclared_None[OF red] by simp
  have needs': "\<forall>\<iota> \<in> set \<iota>s. \<forall>p \<in> needs (node \<iota>). p |\<in>| fmdom \<L>" using needs M by blast
  note bindings = imports_env_wf[OF assms(2, 3) imp distinct needs']
  note env\<^sub>i = import_bindings_env[OF assms(2, 3) bindings]
  have dom\<^sub>i: "fmdom (imports_env \<L> \<iota>s) = fmdom \<Gamma>'" using bindings by (simp add: import_bindings_def)
  have \<rho>\<^sub>s: "\<rho>\<^sub>s = fmconst (assigns t - set (declares \<iota>s)) VUnbound" and \<Gamma>\<^sub>s: "\<Gamma>\<^sub>s = fmconst (assigns t - set (declares \<iota>s)) Unbound"
    using scope_top_Some[OF sc] scope_top_Some[OF sc'] by simp_all
  have env\<^sub>0: "\<eta> \<turnstile> ?\<rho>\<^sub>0 : ?\<Gamma>\<^sub>0"
    using wf_env_add_env[OF env\<^sub>b env\<^sub>i(3)] dom\<^sub>i unfolding \<rho>\<^sub>s \<Gamma>\<^sub>s by (intro wf_env_unbound) simp
  have closed\<^sub>0: "tyvars ?\<Gamma>\<^sub>0 = {}"
    using closed_cxt_add[OF closed_cxt_add[OF builtins_closed[OF predefined] env\<^sub>i(2)] closed_cxt_scope[OF sc']] by simp
  have distinct_t: "distinct (declares t)" using sc' by (simp add: scope_top_def split: if_splits)
  note outcome = top_sound[OF ev env\<^sub>0 closed\<^sub>0 top distinct_t]
  (* A variable bound by the body: assigned by it, so unbound in the scope of the body *)
  have unbound: "fmlookup \<rho>\<^sub>s x = Some VUnbound" if "x |\<in>| fmdom \<Delta>" for x
  proof -
    have fin: "finite (assigns t - set (declares \<iota>s))" using finite_assigns_top by blast
    have "x \<in> assigns t - set (declares \<iota>s)"
    proof -
      from check_top_stmt_bound[OF top that]
      consider "x \<in> assigns t" | "fmlookup ?\<Gamma>\<^sub>0 x = Some Unbound \<or> (\<exists>\<tau>. fmlookup ?\<Gamma>\<^sub>0 x = Some (DU \<tau>))" by blast
      then show ?thesis
      proof cases
        case 1
        from assigns_top_binders[THEN subsetD, OF 1] check_assignments_declared_top[OF cad]
        have "x \<in> set (declares t) \<or> x \<in> binds t" by blast
        with sc' show ?thesis using 1 by (auto simp: scope_top_def split: if_splits)
      next
        case 2
        then have "x |\<in>| fmdom \<Gamma>\<^sub>s \<or> x |\<in>| fmdom \<Gamma>'"
          using builtins_entry by (auto simp: fmlookup_dom_iff split: if_splits)
        with env\<^sub>i(4) 2 show ?thesis
          by (auto simp: \<Gamma>\<^sub>s fmlookup_fmconst[OF fin] fmlookup_dom_iff split: if_splits) (metis option.inject unbound_entry.simps(1, 2))+
      qed
    qed
    then show ?thesis by (simp add: \<rho>\<^sub>s fmlookup_fmconst[OF fin])
  qed
  have S: "fmlookup (submods \<M> q) x = Some (ModStub (Qualified q x)) \<and> fmlookup \<Delta> x = None"
    if "x |\<in>| fmdom (submods \<M> q)" for x
  proof -
    from that have "Qualified q x |\<in>| fmdom \<M>" by (auto simp: submods_lookup fmlookup_dom_iff split: if_splits)
    from check_module_stub[OF chk assms(5) this] have "fmlookup \<Gamma> x = Some (ModStub (Qualified q x))" by auto
    with \<Gamma> that show ?thesis
      using check_top_stmt_entries[OF top] by (auto simp: submods_lookup fmlookup_dom_iff split: if_splits option.splits) fastforce
  qed
  show ?thesis
  proof (rule conjI; intro allI impI)
    fix vs \<kappa>
    assume "o = (vs, Aborts\<^sub>\<omega> \<kappa>)"
    with outcome show "\<not> prevented \<kappa>" by simp
  next
    fix vs \<rho>
    assume o: "o = (vs, Assigns \<rho>)"
    with outcome have env: "\<eta> \<turnstile> ?\<rho>\<^sub>0 \<otimes> \<rho> : ?\<Gamma>\<^sub>0 \<otimes> \<Delta>" and dom: "fmdom \<rho> |\<subseteq>| fmdom \<Delta>" by simp_all
    have cl\<Delta>: "closed_cxt \<Sigma> \<Delta>"
      using check_top_stmt_fixed_closed[OF top distinct_t wf_env_wf_cxt[OF env\<^sub>0] closed\<^sub>0] .
    let ?\<rho> = "submods_env q \<otimes> \<rho>"
    have dom': "fmdom ?\<rho> |\<subseteq>| fmdom \<Gamma>" using dom by (auto simp: \<Gamma> submods_env_def)
    have wf\<Gamma>: "wf_cxt \<Sigma> \<Gamma>" using closed_cxt_submods cl\<Delta> unfolding \<Gamma> by (auto intro: wf_cxt_add)
    have "\<eta> \<turnstile> ?\<rho> \<otimes> fmconst (fmdom' \<Gamma> - fmdom' ?\<rho>) VUnbound : \<Gamma>"
    proof (rule WfEnv[OF wf_env_wf_inst[OF env\<^sub>0] wf\<Gamma>], intro allI impI)
      fix x \<theta>
      assume look: "fmlookup \<Gamma> x = Some \<theta>" and tv: "\<theta> \<noteq> TypeVar"
      let ?pad = "fmlookup (?\<rho> \<otimes> fmconst (fmdom' \<Gamma> - fmdom' ?\<rho>) VUnbound) x"
      have pad: "?pad = (case fmlookup ?\<rho> x of Some v \<Rightarrow> Some v | None \<Rightarrow> Some VUnbound)"
        using look by (auto simp: fmlookup_fmconst fmlookup_dom_iff fmlookup_dom'_iff split: option.splits)
      show "\<exists>v. ?pad = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
      proof (cases "fmlookup \<Delta> x")
        case None
        with look \<Gamma> have "fmlookup (submods \<M> q) x = Some \<theta>" by (simp add: fmlookup_dom_iff)
        then have \<theta>: "\<theta> = ModStub (Qualified q x)" and "Qualified q x |\<in>| fmdom \<M>"
          by (auto simp: submods_lookup split: if_splits)
        moreover have "fmlookup \<rho> x = None" using None dom by (auto simp: fmlookup_dom_iff)
        ultimately show ?thesis using pad by (auto simp: submods_env_def submods_lookup fmlookup_dom_iff intro: ValMod)
      next
        case (Some \<theta>')
        with look \<Gamma> have \<theta>': "\<theta>' = \<theta>" by (simp add: fmlookup_dom_iff)
        have "fmlookup (?\<Gamma>\<^sub>0 \<otimes> \<Delta>) x = Some \<theta>" using Some \<theta>' by (simp add: fmlookup_dom_iff)
        from wf_env_lookup[OF env this tv] obtain v where v: "fmlookup (?\<rho>\<^sub>0 \<otimes> \<rho>) x = Some v" and "\<turnstile> v : inst_entry \<eta> \<theta>"
          by blast
        show ?thesis
        proof (cases "fmlookup \<rho> x")
          case None
          with v have "v = VUnbound" using unbound[OF fmdomI[OF Some]] by (simp add: fmlookup_dom_iff)
          moreover have "fmlookup (submods_env q) x = None"
            using S[of x] Some by (cases "fmlookup (submods \<M> q) x") (auto simp: submods_env_def fmlookup_dom_iff)
          ultimately show ?thesis using None pad \<open>\<turnstile> v : inst_entry \<eta> \<theta>\<close> by (auto simp: fmlookup_dom_iff)
        next
          case (Some v')
          with v have "v' = v" by (simp add: fmlookup_dom_iff)
          with Some pad \<open>\<turnstile> v : inst_entry \<eta> \<theta>\<close> show ?thesis by (auto simp: fmlookup_dom_iff)
        qed
      qed
    qed
    with dom' show "module_env \<eta> ?\<rho> \<Gamma>" by simp
  qed
qed

subsection \<open>Loading\<close>

abbreviation loads_dom :: "name list \<Rightarrow> name list \<Rightarrow> bool"
where "loads_dom qs qs' \<equiv> loads_submod_loads_imports_loads_import_loads_dom (Inl (Inl (qs, qs')))"

abbreviation submod_loads_dom :: "name list \<Rightarrow> name \<Rightarrow> var list \<Rightarrow> bool"
where "submod_loads_dom qs q xs \<equiv> loads_submod_loads_imports_loads_import_loads_dom (Inl (Inr (qs, q, xs)))"

abbreviation imports_loads_dom :: "name list \<Rightarrow> name \<Rightarrow> import located list \<Rightarrow> bool"
where "imports_loads_dom qs q \<iota>s \<equiv> loads_submod_loads_imports_loads_import_loads_dom (Inr (Inl (qs, q, \<iota>s)))"

abbreviation import_loads_dom :: "name list \<Rightarrow> name \<Rightarrow> import \<Rightarrow> bool"
where "import_loads_dom qs q \<iota> \<equiv> loads_submod_loads_imports_loads_import_loads_dom (Inr (Inr (qs, q, \<iota>)))"

(* Submodule of q loaded by an import of members of q: a module of the program not declared by q *)
abbreviation submod :: "name \<Rightarrow> var \<Rightarrow> bool"
where
"submod q x \<equiv> Qualified q x |\<in>| fmdom \<M> \<and> (case fmlookup \<M> q of Some b \<Rightarrow> x \<notin> set (declares b) | None \<Rightarrow> False)"

lemmas loads_psimps = loads.psimps submod_loads.psimps imports_loads.psimps import_loads.psimps
lemmas loads_domintros = loads_submod_loads_imports_loads_import_loads.domintros

(* Modules loaded before those loaded by a call: a prefix of the result *)
lemma loads_prefix:
  "loads_dom qs qs' \<Longrightarrow> \<exists>r. loads qs qs' = qs @ r"
  "submod_loads_dom qs q xs \<Longrightarrow> \<exists>r. submod_loads qs q xs = qs @ r"
  "imports_loads_dom qs q \<iota>s \<Longrightarrow> \<exists>r. imports_loads qs q \<iota>s = qs @ r"
  "import_loads_dom qs q \<iota> \<Longrightarrow> \<exists>r. import_loads qs q \<iota> = qs @ r"
proof (induction qs qs' and qs q xs and qs q \<iota>s and qs q \<iota>
    rule: loads_submod_loads_imports_loads_import_loads.pinduct)
  case (2 qs q qs')
  show ?case
  proof (cases "q \<in> set qs \<or> q |\<in>| fmdom \<P>")
    case True
    with 2 show ?thesis by (simp add: loads_psimps)
  next
    case False
    obtain \<iota>s t where b: "the (fmlookup \<M> q) = ModuleBody \<iota>s t" by (cases "the (fmlookup \<M> q)")
    from 2(3)[OF False b] 2(4)[OF False b] show ?thesis using False 2(1) by (auto simp: loads_psimps b)
  qed
next
  case (4 qs q x xs)
  show ?case
  proof (cases "submod q x")
    case True
    with 4 show ?thesis by (auto simp: loads_psimps)
  next
    case False
    with 4 show ?thesis by (auto simp: loads_psimps)
  qed
qed (auto simp: loads_psimps)

lemma loads_set: "loads_dom qs qs' \<Longrightarrow> set qs \<subseteq> set (loads qs qs')"
  and submod_loads_set: "submod_loads_dom qs q xs \<Longrightarrow> set qs \<subseteq> set (submod_loads qs q xs)"
  and imports_loads_set: "imports_loads_dom qs q \<iota>s \<Longrightarrow> set qs \<subseteq> set (imports_loads qs q \<iota>s)"
  and import_loads_set: "import_loads_dom qs q \<iota> \<Longrightarrow> set qs \<subseteq> set (import_loads qs q \<iota>)"
  by (auto dest!: loads_prefix)

(* Imports of a module loaded by a call, the module neither loaded before nor predefined: in the domain *)
lemma loads_imports_dom:
  "\<lbrakk> loads_dom qs (q # qs') ; \<not> (q \<in> set qs \<or> q |\<in>| fmdom \<P>) ; the (fmlookup \<M> q) = ModuleBody \<iota>s t \<rbrakk>
  \<Longrightarrow> imports_loads_dom qs q \<iota>s"
  by (erule accp_downward) (rule loads_submod_loads_imports_loads_import_loads_rel.intros(2), assumption+)

(* Modules loaded by a call: those loaded before, and the modules named, other than the predefined ones *)
lemma loads_member:
  "\<lbrakk> loads_dom qs qs' ; p \<in> set qs \<or> p \<in> set qs' \<and> p |\<notin>| fmdom \<P> \<rbrakk> \<Longrightarrow> p \<in> set (loads qs qs')"
  "\<lbrakk> submod_loads_dom qs q xs ; p \<in> set qs \<or> (\<exists>y \<in> set xs. p = Qualified q y \<and> submod q y \<and> p |\<notin>| fmdom \<P>) \<rbrakk>
  \<Longrightarrow> p \<in> set (submod_loads qs q xs)"
  "\<lbrakk> imports_loads_dom qs q \<iota>s ; p \<in> set qs \<or> (\<exists>\<iota>' \<in> set \<iota>s. p \<in> needs (node \<iota>')) \<and> p |\<notin>| fmdom \<P> \<rbrakk>
  \<Longrightarrow> p \<in> set (imports_loads qs q \<iota>s)"
  "\<lbrakk> import_loads_dom qs q \<iota> ; p \<in> set qs \<or> p \<in> needs \<iota> \<and> p |\<notin>| fmdom \<P> \<rbrakk> \<Longrightarrow> p \<in> set (import_loads qs q \<iota>)"
proof (induction qs qs' and qs q xs and qs q \<iota>s and qs q \<iota> arbitrary: p and p and p and p
    rule: loads_submod_loads_imports_loads_import_loads.pinduct)
  case (2 qs q qs')
  show ?case
  proof (cases "q \<in> set qs \<or> q |\<in>| fmdom \<P>")
    case True
    have "p \<in> set qs \<or> p \<in> set qs' \<and> p |\<notin>| fmdom \<P>" using 2(5) True by auto
    from 2(2)[OF True this] True 2(1) show ?thesis by (simp add: loads_psimps)
  next
    case False
    obtain \<iota>s t where b: "the (fmlookup \<M> q) = ModuleBody \<iota>s t" by (cases "the (fmlookup \<M> q)")
    have "p \<in> set (imports_loads qs q \<iota>s @ [q]) \<or> p \<in> set qs' \<and> p |\<notin>| fmdom \<P>"
      using 2(5) 2(3)[OF False b] by auto
    from 2(4)[OF False b this] False b 2(1) show ?thesis by (simp add: loads_psimps)
  qed
next
  case (4 qs q x xs)
  show ?case
  proof (cases "submod q x")
    case True
    have "p \<in> set (loads qs [Qualified q x]) \<or> (\<exists>y \<in> set xs. p = Qualified q y \<and> submod q y \<and> p |\<notin>| fmdom \<P>)"
      using 4(5) 4(2)[OF True] by auto
    from 4(3)[OF True this] show ?thesis unfolding submod_loads.psimps(2)[OF 4(1)] if_P[OF True] .
  next
    case False
    have "p \<in> set qs \<or> (\<exists>y \<in> set xs. p = Qualified q y \<and> submod q y \<and> p |\<notin>| fmdom \<P>)"
      using 4(5) False by auto
    from 4(4)[OF False this] show ?thesis unfolding submod_loads.psimps(2)[OF 4(1)] if_not_P[OF False] .
  qed
next
  case (6 qs q \<iota> \<iota>s)
  have "p \<in> set (import_loads qs q (node \<iota>)) \<or> (\<exists>\<iota>' \<in> set \<iota>s. p \<in> needs (node \<iota>')) \<and> p |\<notin>| fmdom \<P>"
    using 6(4) 6(2) by auto
  from 6(3)[OF this] 6(1) show ?case by (simp add: loads_psimps)
next
  case (7 qs q q')
  from 7(3) have "p \<in> set qs \<or> p \<in> set (proper_prefixes q' @ [q']) \<and> p |\<notin>| fmdom \<P>" by auto
  from 7(2)[OF this] 7(1) show ?case by (simp add: loads_psimps)
next
  case (8 qs q q' xs)
  have "p \<in> set (loads qs (unique_to q' q @ [q'])) \<or> (\<exists>y \<in> set xs. p = Qualified q' y \<and> submod q' y \<and> p |\<notin>| fmdom \<P>)"
    using 8(4) 8(2) by auto
  from 8(3)[OF this] 8(1) show ?case by (simp add: loads_psimps)
qed (auto simp: loads_psimps)

(* Modules not loaded before a call but loaded by it: not predefined *)
lemma loads_fresh:
  "\<lbrakk> loads_dom qs qs' ; p \<in> set (loads qs qs') ; p \<notin> set qs \<rbrakk> \<Longrightarrow> p |\<notin>| fmdom \<P>"
  "\<lbrakk> submod_loads_dom qs q xs ; p \<in> set (submod_loads qs q xs) ; p \<notin> set qs \<rbrakk> \<Longrightarrow> p |\<notin>| fmdom \<P>"
  "\<lbrakk> imports_loads_dom qs q \<iota>s ; p \<in> set (imports_loads qs q \<iota>s) ; p \<notin> set qs \<rbrakk> \<Longrightarrow> p |\<notin>| fmdom \<P>"
  "\<lbrakk> import_loads_dom qs q \<iota> ; p \<in> set (import_loads qs q \<iota>) ; p \<notin> set qs \<rbrakk> \<Longrightarrow> p |\<notin>| fmdom \<P>"
proof (induction qs qs' and qs q xs and qs q \<iota>s and qs q \<iota> arbitrary: p and p and p and p
    rule: loads_submod_loads_imports_loads_import_loads.pinduct)
  case (2 qs q qs')
  show ?case
  proof (cases "q \<in> set qs \<or> q |\<in>| fmdom \<P>")
    case True
    from 2(5) True 2(1) have "p \<in> set (loads qs qs')" by (simp add: loads_psimps)
    from 2(2)[OF True this 2(6)] show ?thesis .
  next
    case False
    obtain \<iota>s t where b: "the (fmlookup \<M> q) = ModuleBody \<iota>s t" by (cases "the (fmlookup \<M> q)")
    from 2(5) False b 2(1) have "p \<in> set (loads (imports_loads qs q \<iota>s @ [q]) qs')" by (simp add: loads_psimps)
    with 2(3)[OF False b] 2(4)[OF False b] 2(6) False show ?thesis by auto
  qed
next
  case (4 qs q x xs)
  show ?case
  proof (cases "submod q x")
    case True
    from 4(5) have "p \<in> set (submod_loads (loads qs [Qualified q x]) q xs)" unfolding submod_loads.psimps(2)[OF 4(1)] if_P[OF True] .
    with 4(2)[OF True] 4(3)[OF True] 4(6) show ?thesis by auto
  next
    case False
    from 4(5) have "p \<in> set (submod_loads qs q xs)" unfolding submod_loads.psimps(2)[OF 4(1)] if_not_P[OF False] .
    from 4(4)[OF False this 4(6)] show ?thesis .
  qed
next
  case (6 qs q \<iota> \<iota>s)
  from 6(4) 6(1) have "p \<in> set (imports_loads (import_loads qs q (node \<iota>)) q \<iota>s)" by (simp add: loads_psimps)
  with 6(2) 6(3) 6(5) show ?case by auto
next
  case (8 qs q q' xs)
  from 8(4) 8(1) have "p \<in> set (submod_loads (loads qs (unique_to q' q @ [q'])) q' xs)" by (simp add: loads_psimps)
  with 8(2) 8(3) 8(5) show ?case by auto
qed (auto simp: loads_psimps)

(* Modules in dependency order: the imports of each need only modules loaded before it, or those of D *)
fun ordered :: "name set \<Rightarrow> name list \<Rightarrow> bool"
where
"ordered D [] = True" |
"ordered D (q # qs) =
  ((\<forall>\<iota>s t. fmlookup \<M> q = Some (ModuleBody \<iota>s t) \<longrightarrow> (\<forall>\<iota> \<in> set \<iota>s. needs (node \<iota>) \<subseteq> D)) \<and> ordered (insert q D) qs)"

lemma ordered_mono: "\<lbrakk> ordered D qs ; D \<subseteq> D' \<rbrakk> \<Longrightarrow> ordered D' qs"
proof (induction qs arbitrary: D D')
  case (Cons q qs)
  have "ordered (insert q D) qs" using Cons.prems(1) by simp
  moreover have "insert q D \<subseteq> insert q D'" using Cons.prems(2) by blast
  ultimately have "ordered (insert q D') qs" by (rule Cons.IH)
  with Cons.prems show ?case by (auto simp: subset_iff)
qed simp

lemma ordered_append: "ordered D (qs @ qs') \<longleftrightarrow> ordered D qs \<and> ordered (D \<union> set qs) qs'"
proof (induction qs arbitrary: D)
  case (Cons q qs)
  then show ?case by (simp add: insert_commute Un_insert_right[symmetric] del: Un_insert_right)
qed simp

(* Modules loaded by a call from modules in dependency order: in dependency order *)
lemma loads_ordered:
  "\<lbrakk> loads_dom qs qs' ; ordered (fset (fmdom \<P>)) qs \<rbrakk> \<Longrightarrow> ordered (fset (fmdom \<P>)) (loads qs qs')"
  "\<lbrakk> submod_loads_dom qs q xs ; ordered (fset (fmdom \<P>)) qs \<rbrakk> \<Longrightarrow> ordered (fset (fmdom \<P>)) (submod_loads qs q xs)"
  "\<lbrakk> imports_loads_dom qs q \<iota>s ; ordered (fset (fmdom \<P>)) qs \<rbrakk> \<Longrightarrow> ordered (fset (fmdom \<P>)) (imports_loads qs q \<iota>s)"
  "\<lbrakk> import_loads_dom qs q \<iota> ; ordered (fset (fmdom \<P>)) qs \<rbrakk> \<Longrightarrow> ordered (fset (fmdom \<P>)) (import_loads qs q \<iota>)"
proof (induction qs qs' and qs q xs and qs q \<iota>s and qs q \<iota>
    rule: loads_submod_loads_imports_loads_import_loads.pinduct)
  case (2 qs q qs')
  show ?case
  proof (cases "q \<in> set qs \<or> q |\<in>| fmdom \<P>")
    case True
    from 2(2)[OF True 2(5)] True 2(1) show ?thesis by (simp add: loads_psimps)
  next
    case False
    obtain \<iota>s t where b: "the (fmlookup \<M> q) = ModuleBody \<iota>s t" by (cases "the (fmlookup \<M> q)")
    have dom: "imports_loads_dom qs q \<iota>s" using 2(1) False b by (rule loads_imports_dom)
    have "ordered (fset (fmdom \<P>)) (imports_loads qs q \<iota>s @ [q])"
    proof -
      have "needs (node \<iota>) \<subseteq> fset (fmdom \<P>) \<union> set (imports_loads qs q \<iota>s)"
        if "fmlookup \<M> q = Some (ModuleBody \<iota>s' t')" and "\<iota> \<in> set \<iota>s'" for \<iota>s' t' \<iota>
      proof
        fix p
        assume p: "p \<in> needs (node \<iota>)"
        from that b have \<iota>: "\<iota> \<in> set \<iota>s" by simp
        show "p \<in> fset (fmdom \<P>) \<union> set (imports_loads qs q \<iota>s)"
        proof (cases "p |\<in>| fmdom \<P>")
          case False
          with p \<iota> show ?thesis using loads_member(3)[OF dom, of p] by blast
        qed simp
      qed
      with 2(3)[OF False b 2(5)] show ?thesis by (simp add: ordered_append)
    qed
    from 2(4)[OF False b this] False b 2(1) show ?thesis by (simp add: loads_psimps)
  qed
next
  case (4 qs q x xs)
  show ?case
  proof (cases "submod q x")
    case True
    from 4(3)[OF True 4(2)[OF True 4(5)]] show ?thesis unfolding submod_loads.psimps(2)[OF 4(1)] if_P[OF True] .
  next
    case False
    from 4(4)[OF False 4(5)] show ?thesis unfolding submod_loads.psimps(2)[OF 4(1)] if_not_P[OF False] .
  qed
next
  case (6 qs q \<iota> \<iota>s)
  from 6(3)[OF 6(2)[OF 6(4)]] 6(1) show ?case by (simp add: loads_psimps)
next
  case (7 qs q q')
  from 7(2)[OF 7(3)] 7(1) show ?case by (simp add: loads_psimps)
next
  case (8 qs q q' xs)
  from 8(3)[OF 8(2)[OF 8(4)]] 8(1) show ?case by (simp add: loads_psimps)
qed (auto simp: loads_psimps)

(* Module checked from the class table, leaving it fixed *)
definition checked :: "name \<Rightarrow> bool"
where "checked q = (\<exists>V q' \<Gamma>. check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>))"

(* Modules loaded by a call from the modules qs: those modules, and checked modules not predefined *)
abbreviation fresh :: "name list \<Rightarrow> name list \<Rightarrow> bool"
where "fresh qs r \<equiv> \<forall>p \<in> set r. p \<in> set qs \<or> checked p \<and> p |\<notin>| fmdom \<P>"

(* Module whose imports load, from any modules, only checked modules; predefined, or checked itself *)
definition loadable :: "name \<Rightarrow> bool"
where
"loadable q =
  (q |\<in>| fmdom \<P>
   \<or> checked q \<and> (\<exists>\<iota>s t. fmlookup \<M> q = Some (ModuleBody \<iota>s t)
                     \<and> (\<forall>qs. imports_loads_dom qs q \<iota>s \<and> fresh qs (imports_loads qs q \<iota>s))))"

lemma loads_list: "\<forall>p \<in> set qs'. loadable p \<Longrightarrow> loads_dom qs qs' \<and> fresh qs (loads qs qs')"
proof (induction qs' arbitrary: qs)
  case Nil
  have "loads_dom qs []" by (rule loads_domintros)
  then show ?case by (simp add: loads_psimps)
next
  case (Cons p qs')
  show ?case
  proof (cases "p \<in> set qs \<or> p |\<in>| fmdom \<P>")
    case True
    have dom: "loads_dom qs (p # qs')" using Cons.IH[of qs] Cons.prems True by (auto intro: loads_domintros)
    with Cons.IH[of qs] Cons.prems True show ?thesis by (auto simp: loads_psimps)
  next
    case False
    with Cons.prems obtain \<iota>s t where b: "fmlookup \<M> p = Some (ModuleBody \<iota>s t)" and ch: "checked p"
      and imp: "\<forall>qs. imports_loads_dom qs p \<iota>s \<and> fresh qs (imports_loads qs p \<iota>s)"
      by (auto simp: loadable_def)
    let ?qs = "imports_loads qs p \<iota>s @ [p]"
    have dom: "loads_dom qs (p # qs')"
      using imp Cons.IH[of ?qs] Cons.prems False b by (auto intro: loads_domintros)
    have "fresh qs (loads ?qs qs')" using Cons.IH[of ?qs] Cons.prems imp[rule_format, of qs] ch False by auto
    with dom show ?thesis using False by (simp add: loads_psimps b)
  qed
qed

lemma submod_loads_list:
  "\<forall>x \<in> set xs. submod q x \<longrightarrow> loadable (Qualified q x)
  \<Longrightarrow> submod_loads_dom qs q xs \<and> fresh qs (submod_loads qs q xs)"
proof (induction xs arbitrary: qs)
  case Nil
  have "submod_loads_dom qs q []" by (rule loads_domintros)
  then show ?case by (simp add: loads_psimps)
next
  case (Cons x xs)
  show ?case
  proof (cases "submod q x")
    case True
    have l: "loads_dom qs [Qualified q x] \<and> fresh qs (loads qs [Qualified q x])"
      using loads_list[of "[Qualified q x]" qs] Cons.prems True by simp
    let ?qs = "loads qs [Qualified q x]"
    have rest: "submod_loads_dom ?qs q xs \<and> fresh ?qs (submod_loads ?qs q xs)" using Cons.IH[of ?qs] Cons.prems by simp
    have dom: "submod_loads_dom qs q (x # xs)" using l rest True by (auto intro: loads_domintros)
    have eq: "submod_loads qs q (x # xs) = submod_loads ?qs q xs"
      unfolding submod_loads.psimps(2)[OF dom] if_P[OF True] ..
    have "fresh qs (submod_loads ?qs q xs)" using rest l by auto
    with dom show ?thesis unfolding eq by simp
  next
    case False
    have rest: "submod_loads_dom qs q xs \<and> fresh qs (submod_loads qs q xs)" using Cons.IH[of qs] Cons.prems by simp
    have dom: "submod_loads_dom qs q (x # xs)" using rest False by (auto intro: loads_domintros)
    have eq: "submod_loads qs q (x # xs) = submod_loads qs q xs"
      unfolding submod_loads.psimps(2)[OF dom] if_not_P[OF False] ..
    with dom rest show ?thesis by simp
  qed
qed

lemma imports_loads_list:
  "\<forall>\<iota> \<in> set \<iota>s. \<forall>qs. import_loads_dom qs q (node \<iota>) \<and> fresh qs (import_loads qs q (node \<iota>))
  \<Longrightarrow> imports_loads_dom qs q \<iota>s \<and> fresh qs (imports_loads qs q \<iota>s)"
proof (induction \<iota>s arbitrary: qs)
  case Nil
  have "imports_loads_dom qs q []" by (rule loads_domintros)
  then show ?case by (simp add: loads_psimps)
next
  case (Cons \<iota> \<iota>s)
  let ?qs = "import_loads qs q (node \<iota>)"
  have hd: "import_loads_dom qs q (node \<iota>) \<and> fresh qs ?qs" using Cons.prems by simp
  have rest: "imports_loads_dom ?qs q \<iota>s \<and> fresh ?qs (imports_loads ?qs q \<iota>s)" using Cons.IH[of ?qs] Cons.prems by simp
  have dom: "imports_loads_dom qs q (\<iota> # \<iota>s)" using hd rest by (auto intro: loads_domintros)
  have eq: "imports_loads qs q (\<iota> # \<iota>s) = imports_loads ?qs q \<iota>s" by (rule imports_loads.psimps(2)[OF dom])
  from dom hd rest show ?case unfolding eq by auto
qed

(* Class table from which checking proceeds: well-formed, containing the predefined classes and settled *)
abbreviation good :: "class_table \<Rightarrow> bool"
where "good \<Sigma>' \<equiv> wf_class_table \<Sigma>' \<and> predefined_classes \<subseteq>\<^sub>f \<Sigma>' \<and> settled \<M> \<Sigma>'"

lemma check_module_good:
  "\<lbrakk> check_module \<M> V \<Sigma>\<^sub>0 q' q = Ok (\<Gamma>, \<Sigma>') ; good \<Sigma>\<^sub>0 \<rbrakk> \<Longrightarrow> \<Sigma>\<^sub>0 \<subseteq>\<^sub>f \<Sigma>' \<and> good \<Sigma>' \<and> closed_cxt \<Sigma>' \<Gamma>"
  "\<lbrakk> check_imports \<M> V \<Sigma>\<^sub>0 q \<iota>s = Ok (\<Gamma>, \<Sigma>') ; good \<Sigma>\<^sub>0 \<rbrakk> \<Longrightarrow> \<Sigma>\<^sub>0 \<subseteq>\<^sub>f \<Sigma>' \<and> good \<Sigma>' \<and> closed_cxt \<Sigma>' \<Gamma>"
  "\<lbrakk> submodules \<M> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 xs = Ok (\<Gamma>, \<Sigma>') ; good \<Sigma>\<^sub>0 ; closed_cxt \<Sigma>\<^sub>0 \<Gamma>\<^sub>0 \<rbrakk>
  \<Longrightarrow> \<Sigma>\<^sub>0 \<subseteq>\<^sub>f \<Sigma>' \<and> good \<Sigma>' \<and> closed_cxt \<Sigma>' \<Gamma>"
  "\<lbrakk> imports_entry \<M> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 x = Ok (\<theta>, \<Sigma>') ; good \<Sigma>\<^sub>0 ; closed_cxt \<Sigma>\<^sub>0 \<Gamma>\<^sub>0 \<rbrakk> \<Longrightarrow> \<Sigma>\<^sub>0 \<subseteq>\<^sub>f \<Sigma>' \<and> good \<Sigma>'"
  "\<lbrakk> imports_entries \<M> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 xs = Ok (\<theta>s, \<Sigma>') ; good \<Sigma>\<^sub>0 ; closed_cxt \<Sigma>\<^sub>0 \<Gamma>\<^sub>0 \<rbrakk> \<Longrightarrow> \<Sigma>\<^sub>0 \<subseteq>\<^sub>f \<Sigma>' \<and> good \<Sigma>'"
  "\<lbrakk> check_modules \<M> V \<Sigma>\<^sub>0 q qs = Ok \<Sigma>' ; good \<Sigma>\<^sub>0 \<rbrakk> \<Longrightarrow> \<Sigma>\<^sub>0 \<subseteq>\<^sub>f \<Sigma>' \<and> good \<Sigma>'"
  using check_module_stable(1)[of \<M> V \<Sigma>\<^sub>0 q' q \<Gamma> \<Sigma>'] check_module_stable(2)[of \<M> V \<Sigma>\<^sub>0 q \<iota>s \<Gamma> \<Sigma>']
    check_module_stable(3)[of \<M> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 xs \<Gamma> \<Sigma>'] check_module_stable(4)[of \<M> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 x \<theta> \<Sigma>']
    check_module_stable(5)[of \<M> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 xs \<theta>s \<Sigma>'] check_module_stable(6)[of \<M> V \<Sigma>\<^sub>0 q qs \<Sigma>']
  by (meson stableD(1-3) fmsubset_trans)+

lemma settled_good: "settled \<M> \<Sigma> \<Longrightarrow> good \<Sigma>"
  using wf_class_table predefined by simp

(* Table fixed by a call from a good table whose result is contained in the class table: the class table *)
lemma fixed_call: "\<lbrakk> \<Sigma> \<subseteq>\<^sub>f \<Sigma>\<^sub>1 ; \<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>\<^sub>2 ; \<Sigma>\<^sub>2 \<subseteq>\<^sub>f \<Sigma> \<rbrakk> \<Longrightarrow> \<Sigma>\<^sub>1 = \<Sigma> \<and> \<Sigma>\<^sub>2 = \<Sigma>"
  by (meson fmsubset_antisym fmsubset_trans)

(* Modules checked from the class table, leaving it fixed: loadable, and those their imports load, checked *)
lemma check_module_loadable:
  assumes settled: "settled \<M> \<Sigma>"
  shows
  "\<lbrakk> check_module \<N> V \<Sigma>\<^sub>0 q' q = Ok (\<Gamma>, \<Sigma>') ; \<N> = \<M> ; \<Sigma>\<^sub>0 = \<Sigma> ; \<Sigma>' = \<Sigma> \<rbrakk> \<Longrightarrow> loadable q"
  "\<lbrakk> check_imports \<N> V \<Sigma>\<^sub>0 q \<iota>s = Ok (\<Gamma>, \<Sigma>') ; \<N> = \<M> ; \<Sigma>\<^sub>0 = \<Sigma> ; \<Sigma>' = \<Sigma> \<rbrakk>
  \<Longrightarrow> \<forall>\<iota> \<in> set \<iota>s. \<forall>qs. import_loads_dom qs q (node \<iota>) \<and> fresh qs (import_loads qs q (node \<iota>))"
  "\<lbrakk> submodules \<N> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 xs = Ok (\<Gamma>, \<Sigma>') ; \<N> = \<M> ; \<Sigma>\<^sub>0 = \<Sigma> ; \<Sigma>' = \<Sigma> ; closed_cxt \<Sigma> \<Gamma>\<^sub>0 \<rbrakk>
  \<Longrightarrow> \<forall>p \<in> set (chain p' xs). loadable p"
  "\<lbrakk> imports_entry \<N> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 x = Ok (\<theta>, \<Sigma>') ; \<N> = \<M> ; \<Sigma>\<^sub>0 = \<Sigma> ; \<Sigma>' = \<Sigma> ; closed_cxt \<Sigma> \<Gamma>\<^sub>0 \<rbrakk>
  \<Longrightarrow> \<forall>q''. fmlookup \<Gamma>\<^sub>0 x = Some (ModStub q'') \<longrightarrow> loadable q''"
  "\<lbrakk> imports_entries \<N> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 xs = Ok (\<theta>s, \<Sigma>') ; \<N> = \<M> ; \<Sigma>\<^sub>0 = \<Sigma> ; \<Sigma>' = \<Sigma> ; closed_cxt \<Sigma> \<Gamma>\<^sub>0 \<rbrakk>
  \<Longrightarrow> \<forall>x \<in> set xs. \<forall>q''. fmlookup \<Gamma>\<^sub>0 x = Some (ModStub q'') \<longrightarrow> loadable q''"
  "\<lbrakk> check_modules \<N> V \<Sigma>\<^sub>0 q qs = Ok \<Sigma>' ; \<N> = \<M> ; \<Sigma>\<^sub>0 = \<Sigma> ; \<Sigma>' = \<Sigma> \<rbrakk> \<Longrightarrow> \<forall>p \<in> set qs. loadable p"
proof (induction \<N> V \<Sigma>\<^sub>0 q' q and \<N> V \<Sigma>\<^sub>0 q \<iota>s and \<N> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 xs and \<N> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 x
    and \<N> V \<Sigma>\<^sub>0 q p' \<Gamma>\<^sub>0 xs and \<N> V \<Sigma>\<^sub>0 q qs
    arbitrary: \<Gamma> \<Sigma>' and \<Gamma> \<Sigma>' and \<Gamma> \<Sigma>' and \<theta> \<Sigma>' and \<theta>s \<Sigma>' and \<Sigma>'
    rule: check_module_check_imports_submodules_imports_entry_imports_entries_check_modules.induct)
  case (1 \<N> V \<Sigma>\<^sub>0 q' q)
  note prems = "1.prems"
  note eq = prems(2-4)
  show ?case
  proof (cases "fmlookup \<P> q")
    case (Some \<Gamma>\<^sub>0)
    then show ?thesis by (auto simp: loadable_def fmlookup_dom_iff)
  next
    case None
    from check_module_body[OF prems(1) None] obtain \<iota>s t \<Gamma>' \<Sigma>\<^sub>1 \<Gamma>\<^sub>s \<Delta> r
      where M: "fmlookup \<N> q = Some (ModuleBody \<iota>s t)" and V: "q \<notin> set V"
      and imp: "check_imports \<N> (V @ [q]) \<Sigma>\<^sub>0 q \<iota>s = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
      and "redeclared node {} (declarations \<iota>s) = None" and "scope Unbound (declares \<iota>s) t = Some \<Gamma>\<^sub>s"
      and "check_assignments_declared {} (assign_targets t) (declares t) (binds t) = Ok ()"
      and top: "check_top_stmt \<Sigma>\<^sub>1 q (the (fmlookup \<P> builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>')"
      and "(fmdom \<Gamma>' |\<union>| fmdom \<Gamma>\<^sub>s) |\<inter>| fmdom (submods \<N> q) = {||}" and "\<Gamma> = submods \<N> q \<otimes> \<Delta>" .
    have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>"
    proof -
      from check_top_stmt_adds[OF top[unfolded eq(3)]] obtain E where "\<Sigma> = \<Sigma>\<^sub>1 \<otimes> E" by blast
      then show ?thesis
        by (rule adds_fixed[OF check_module_good(2)[OF imp[unfolded eq] settled_good[OF settled], THEN conjunct1]])
    qed
    from imports_loads_list[OF "1.IH"[OF None V M refl imp eq(1, 2) \<Sigma>\<^sub>1]]
    have "\<forall>qs. imports_loads_dom qs q \<iota>s \<and> fresh qs (imports_loads qs q \<iota>s)" by blast
    moreover have "checked q" using prems(1)[unfolded eq] unfolding checked_def by blast
    ultimately show ?thesis using M unfolding loadable_def eq by blast
  qed
next
  case (3 \<N> V \<Sigma>\<^sub>0 q p q' \<iota>s)
  note prems = "3.prems"
  note eq = prems(2-4)
  obtain y ys where vars: "variables q' = y # ys" using variables_nonempty by (cases "variables q'") auto
  from prems(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Delta>' \<Sigma>\<^sub>2 \<Gamma>'' where ens: "\<not> q \<prec> q'"
    and m: "check_module \<N> V \<Sigma>\<^sub>0 q (Simple y) = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and sub: "submodules \<N> V \<Sigma>\<^sub>1 q (Simple y) \<Delta> ys = Ok (\<Delta>', \<Sigma>\<^sub>2)"
    and rest: "check_imports \<N> V \<Sigma>\<^sub>2 q \<iota>s = Ok (\<Gamma>'', \<Sigma>')"
    by (auto simp: check_imports.simps vars bind_sum_Ok ensure_def split: if_splits)
  have ens': "ensure (\<not> q \<prec> q') (q, ImportOfContainedModule q' q) = Ok ()" by (simp add: ensure_def ens)
  note g1 = check_module_good(1)[OF m[unfolded eq] settled_good[OF settled]]
  note g2 = check_module_good(3)[OF sub[unfolded eq(1)] g1[THEN conjunct2, THEN conjunct1] g1[THEN conjunct2, THEN conjunct2]]
  note g3 = check_module_good(2)[OF rest[unfolded eq] g2[THEN conjunct2, THEN conjunct1]]
  have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>" and \<Sigma>\<^sub>2: "\<Sigma>\<^sub>2 = \<Sigma>" using fixed_call[OF g1[THEN conjunct1] g2[THEN conjunct1] g3[THEN conjunct1]] by auto
  have l: "loadable (Simple y)" using "3.IH"(1)[OF vars ens' m eq(1, 2) \<Sigma>\<^sub>1] .
  have cl\<Delta>: "closed_cxt \<Sigma> \<Delta>" using g1 unfolding \<Sigma>\<^sub>1 by blast
  have ls: "\<forall>p \<in> set (chain (Simple y) ys). loadable p" using "3.IH"(2)[OF vars ens' m refl sub eq(1) \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 cl\<Delta>] .
  have rest': "\<forall>\<iota> \<in> set \<iota>s. \<forall>qs. import_loads_dom qs q (node \<iota>) \<and> fresh qs (import_loads qs q (node \<iota>))"
    using "3.IH"(3)[OF vars ens' m refl sub refl rest eq(1) \<Sigma>\<^sub>2 eq(3)] .
  have ll: "loads_dom qs (proper_prefixes q' @ [q']) \<and> fresh qs (loads qs (proper_prefixes q' @ [q']))" for qs
    using l ls by (intro loads_list) (simp add: proper_prefixes_chain[OF vars])
  have "import_loads_dom qs q (Import q') \<and> fresh qs (import_loads qs q (Import q'))" for qs
  proof -
    have dom: "import_loads_dom qs q (Import q')" using ll[of qs] by (auto intro: loads_domintros)
    have "import_loads qs q (Import q') = loads qs (proper_prefixes q' @ [q'])" by (rule import_loads.psimps(1)[OF dom])
    with dom ll[of qs] show ?thesis by simp
  qed
  with rest' show ?case by simp
next
  case (4 \<N> V \<Sigma>\<^sub>0 q p q' xs \<iota>s)
  note prems = "4.prems"
  note eq = prems(2-4)
  from prems(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 \<theta>s \<Sigma>\<^sub>3 \<Gamma>'' where m: "check_module \<N> V \<Sigma>\<^sub>0 q q' = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and ms: "check_modules \<N> V \<Sigma>\<^sub>1 q (unique_to q' q) = Ok \<Sigma>\<^sub>2" and red: "redeclared id {} xs = None"
    and ent: "imports_entries \<N> V \<Sigma>\<^sub>2 q q' \<Delta> xs = Ok (\<theta>s, \<Sigma>\<^sub>3)"
    and rest: "check_imports \<N> V \<Sigma>\<^sub>3 q \<iota>s = Ok (\<Gamma>'', \<Sigma>')"
    by (auto simp: check_imports.simps bind_sum_Ok split: option.splits simp del: check_module.simps)
  have red': "(case redeclared id {} xs of None \<Rightarrow> Ok () | Some x \<Rightarrow> Fail (q, DuplicateImportedName x)) = Ok ()"
    by (simp add: red)
  note g1 = check_module_good(1)[OF m[unfolded eq] settled_good[OF settled]]
  note g2 = check_module_good(6)[OF ms[unfolded eq(1)] g1[THEN conjunct2, THEN conjunct1]]
  note g3 = check_module_good(5)[OF ent[unfolded eq(1)] g2[THEN conjunct2]
      closed_cxt_mono[OF g1[THEN conjunct2, THEN conjunct2] g2[THEN conjunct1]]]
  note g4 = check_module_good(2)[OF rest[unfolded eq] g3[THEN conjunct2]]
  have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>" and \<Sigma>\<^sub>3: "\<Sigma>\<^sub>3 = \<Sigma>"
    using fixed_call[OF g1[THEN conjunct1] fmsubset_trans[OF g2[THEN conjunct1] g3[THEN conjunct1]] g4[THEN conjunct1]]
    by auto
  have \<Sigma>\<^sub>2: "\<Sigma>\<^sub>2 = \<Sigma>" using fixed_call[OF g2[THEN conjunct1, unfolded \<Sigma>\<^sub>1] g3[THEN conjunct1, unfolded \<Sigma>\<^sub>3] fmsubset_refl] by simp
  have l: "loadable q'" using "4.IH"(1)[OF m eq(1, 2) \<Sigma>\<^sub>1] .
  have ls: "\<forall>p \<in> set (unique_to q' q). loadable p" using "4.IH"(2)[OF m refl ms eq(1) \<Sigma>\<^sub>1 \<Sigma>\<^sub>2] .
  have cl\<Delta>: "closed_cxt \<Sigma> \<Delta>" using g1 unfolding \<Sigma>\<^sub>1 by blast
  have stubs: "\<forall>x \<in> set xs. \<forall>q''. fmlookup \<Delta> x = Some (ModStub q'') \<longrightarrow> loadable q''"
    using "4.IH"(3)[OF m refl ms red' ent eq(1) \<Sigma>\<^sub>2 \<Sigma>\<^sub>3 cl\<Delta>] .
  have rest': "\<forall>\<iota> \<in> set \<iota>s. \<forall>qs. import_loads_dom qs q (node \<iota>) \<and> fresh qs (import_loads qs q (node \<iota>))"
    using "4.IH"(4)[OF m refl ms red' ent refl rest eq(1) \<Sigma>\<^sub>3 eq(3)] .
  have subs: "loadable (Qualified q' x)" if "x \<in> set xs" and "submod q' x" for x
  proof -
    from that(2) have "q' |\<in>| fmdom \<M>" by (auto simp: fmlookup_dom_iff split: option.splits)
    then have "q' |\<notin>| fmdom \<P>" using disjoint by (auto simp: fset_eq_iff)
    then have "fmlookup \<P> q' = None" by (rule fmdom_notD)
    moreover have Q: "Qualified q' x |\<in>| fmdom \<M>" using that(2) by simp
    ultimately have "fmlookup \<Delta> x = Some (ModStub (Qualified q' x))"
      by (rule check_module_stub[OF m[unfolded eq(1)]]) blast
    with stubs that(1) show ?thesis by blast
  qed
  have l\<^sub>1: "loads_dom qs (unique_to q' q @ [q']) \<and> fresh qs (loads qs (unique_to q' q @ [q']))" for qs
    using l ls by (intro loads_list) simp
  have l\<^sub>2: "submod_loads_dom qs q' xs \<and> fresh qs (submod_loads qs q' xs)" for qs
    using subs by (intro submod_loads_list) blast
  have "import_loads_dom qs q (FromImport q' xs) \<and> fresh qs (import_loads qs q (FromImport q' xs))" for qs
  proof -
    let ?qs = "loads qs (unique_to q' q @ [q'])"
    have dom: "import_loads_dom qs q (FromImport q' xs)" using l\<^sub>1[of qs] l\<^sub>2[of ?qs] by (auto intro: loads_domintros)
    have "import_loads qs q (FromImport q' xs) = submod_loads ?qs q' xs" by (rule import_loads.psimps(2)[OF dom])
    with dom l\<^sub>1[of qs] l\<^sub>2[of ?qs] show ?thesis by auto
  qed
  with rest' show ?case by simp
next
  case (6 \<N> V \<Sigma>\<^sub>0 q q' \<Gamma>\<^sub>0 x xs)
  note prems = "6.prems"
  note eq = prems(2-4)
  from prems(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Delta>' where m: "check_module \<N> V \<Sigma>\<^sub>0 q (Qualified q' x) = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and sub: "submodules \<N> V \<Sigma>\<^sub>1 q (Qualified q' x) \<Delta> xs = Ok (\<Delta>', \<Sigma>')"
    by (auto simp: submodules.simps bind_sum_Ok)
  note g1 = check_module_good(1)[OF m[unfolded eq] settled_good[OF settled]]
  note g2 = check_module_good(3)[OF sub[unfolded eq(1)] g1[THEN conjunct2, THEN conjunct1] g1[THEN conjunct2, THEN conjunct2]]
  have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>" using fixed_call[OF g1[THEN conjunct1] g2[THEN conjunct1, unfolded eq(3)] fmsubset_refl] by simp
  have cl\<Delta>: "closed_cxt \<Sigma> \<Delta>" using g1 unfolding \<Sigma>\<^sub>1 by blast
  from "6.IH"(1)[OF m eq(1, 2) \<Sigma>\<^sub>1] "6.IH"(2)[OF m refl sub eq(1) \<Sigma>\<^sub>1 eq(3) cl\<Delta>] show ?case by simp
next
  case (7 \<N> V \<Sigma>\<^sub>0 q q' \<Gamma>\<^sub>0 x)
  note prems = "7.prems"
  note eq = prems(2-4)
  show ?case
  proof (intro allI impI)
    fix q''
    assume look: "fmlookup \<Gamma>\<^sub>0 x = Some (ModStub q'')"
    with prems(1) obtain \<Gamma>' where m: "check_module \<N> V \<Sigma>\<^sub>0 q q'' = Ok (\<Gamma>', \<Sigma>')"
      by (auto simp: imports_entry.simps bind_sum_Ok)
    show "loadable q''" using "7.IH"[OF look refl m eq] .
  qed
next
  case (9 \<N> V \<Sigma>\<^sub>0 q q' \<Gamma>\<^sub>0 x xs)
  note prems = "9.prems"
  note eq = prems(2-4)
  from prems(1) obtain \<theta>' \<Sigma>\<^sub>1 \<theta>s' where e: "imports_entry \<N> V \<Sigma>\<^sub>0 q q' \<Gamma>\<^sub>0 x = Ok (\<theta>', \<Sigma>\<^sub>1)"
    and rest: "imports_entries \<N> V \<Sigma>\<^sub>1 q q' \<Gamma>\<^sub>0 xs = Ok (\<theta>s', \<Sigma>')"
    by (auto simp: imports_entries.simps bind_sum_Ok)
  have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>"
  proof (cases "fmlookup \<Gamma>\<^sub>0 x")
    case (Some \<theta>'')
    show ?thesis
    proof (cases \<theta>'')
      case (ModStub q'')
      with Some e obtain \<Gamma>' where m: "check_module \<N> V \<Sigma>\<^sub>0 q q'' = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
        by (auto simp: imports_entry.simps bind_sum_Ok)
      note g1 = check_module_good(1)[OF m[unfolded eq] settled_good[OF settled]]
      have "closed_cxt \<Sigma>\<^sub>1 \<Gamma>\<^sub>0" using closed_cxt_mono[OF prems(5) g1[THEN conjunct1]] .
      note g2 = check_module_good(5)[OF rest[unfolded eq(1)] g1[THEN conjunct2, THEN conjunct1] this]
      show ?thesis using fixed_call[OF g1[THEN conjunct1] g2[THEN conjunct1, unfolded eq(3)] fmsubset_refl] by simp
    qed (use Some e in \<open>auto simp: imports_entry.simps eq split: option.splits\<close>)
  qed (use e in \<open>auto simp: imports_entry.simps eq split: option.splits\<close>)
  from "9.IH"(1)[OF e eq(1, 2) \<Sigma>\<^sub>1 prems(5)] "9.IH"(2)[OF e refl rest eq(1) \<Sigma>\<^sub>1 eq(3) prems(5)] show ?case by simp
next
  case (11 \<N> V \<Sigma>\<^sub>0 q q' qs)
  note prems = "11.prems"
  note eq = prems(2-4)
  from prems(1) obtain \<Gamma>' \<Sigma>\<^sub>1 where m: "check_module \<N> V \<Sigma>\<^sub>0 q q' = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
    and rest: "check_modules \<N> V \<Sigma>\<^sub>1 q qs = Ok \<Sigma>'"
    by (auto simp: check_modules.simps bind_sum_Ok)
  note g1 = check_module_good(1)[OF m[unfolded eq] settled_good[OF settled]]
  note g2 = check_module_good(6)[OF rest[unfolded eq(1)] g1[THEN conjunct2, THEN conjunct1]]
  have \<Sigma>\<^sub>1: "\<Sigma>\<^sub>1 = \<Sigma>" using fixed_call[OF g1[THEN conjunct1] g2[THEN conjunct1, unfolded eq(3)] fmsubset_refl] by simp
  from "11.IH"(1)[OF m eq(1, 2) \<Sigma>\<^sub>1] "11.IH"(2)[OF m refl rest eq(1) \<Sigma>\<^sub>1 eq(3)] show ?case by simp
qed simp_all

subsection \<open>Programs\<close>

lemma loaded_upd:
  assumes "loaded \<eta> \<L>" and "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>)" and "module_env \<eta> \<rho> \<Gamma>"
  shows "loaded \<eta> (fmupd q \<rho> \<L>)"
  using assms unfolding loaded_def by (auto split: if_splits)

(* Soundness of the evaluation of modules in dependency order, each checked from the class table and not
   predefined, from loaded modules: no prevented error *)
lemma mods_sound:
  assumes "qs, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s o" and "loaded \<eta> \<L>" and "settled \<M> \<Sigma>" and "ordered (fset (fmdom \<L>)) qs"
    and "\<forall>q \<in> set qs. q |\<notin>| fmdom \<P> \<and> checked q"
  shows "\<forall>vs \<kappa>. o = (vs, Aborts\<^sub>\<omega> \<kappa>) \<longrightarrow> \<not> prevented \<kappa>"
  using assms
proof (induction qs \<L> o rule: eval_mods.induct)
  case (EvalModsNil \<L>)
  then show ?case by simp
next
  case (EvalModsCons q \<L> vs \<rho> qs o)
  from EvalModsCons.prems(4) obtain V q' \<Gamma> where chk: "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>)"
    by (auto simp: checked_def)
  have P: "fmlookup \<P> q = None" using EvalModsCons.prems(4) by (auto simp: fmlookup_dom_iff)
  have needs: "\<forall>\<iota>s t. fmlookup \<M> q = Some (ModuleBody \<iota>s t) \<longrightarrow> (\<forall>\<iota> \<in> set \<iota>s. \<forall>p \<in> needs (node \<iota>). p |\<in>| fmdom \<L>)"
    using EvalModsCons.prems(3) by auto
  from mod_sound[OF EvalModsCons.hyps(1) EvalModsCons.prems(1, 2) chk P needs]
  have env: "module_env \<eta> (submods_env q \<otimes> \<rho>) \<Gamma>" by simp
  have "loaded \<eta> (fmupd q (submods_env q \<otimes> \<rho>) \<L>)" using loaded_upd[OF EvalModsCons.prems(1) chk env] .
  moreover have "ordered (fset (fmdom (fmupd q (submods_env q \<otimes> \<rho>) \<L>))) qs" using EvalModsCons.prems(3) by simp
  ultimately have "\<forall>vs \<kappa>. o = (vs, Aborts\<^sub>\<omega> \<kappa>) \<longrightarrow> \<not> prevented \<kappa>"
    using EvalModsCons.IH EvalModsCons.prems(2, 4) by simp
  moreover obtain vs' \<omega> where "o = (vs', \<omega>)" by (cases o)
  ultimately show ?case by (cases \<omega>) auto
next
  case (EvalModsFail q \<L> vs \<kappa> qs)
  from EvalModsFail.prems(4) obtain V q' \<Gamma> where chk: "check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>)"
    by (auto simp: checked_def)
  have P: "fmlookup \<P> q = None" using EvalModsFail.prems(4) by (auto simp: fmlookup_dom_iff)
  have needs: "\<forall>\<iota>s t. fmlookup \<M> q = Some (ModuleBody \<iota>s t) \<longrightarrow> (\<forall>\<iota> \<in> set \<iota>s. \<forall>p \<in> needs (node \<iota>). p |\<in>| fmdom \<L>)"
    using EvalModsFail.prems(3) by auto
  from mod_sound[OF EvalModsFail.hyps EvalModsFail.prems(1, 2) chk P needs] show ?case by simp
qed

lemma map_of_list_all2:
  "\<lbrakk> list_all2 (\<lambda>(x, v) (y, \<theta>). x = y \<and> P v \<theta>) ls gs ; map_of gs x = Some \<theta> \<rbrakk> \<Longrightarrow> \<exists>v. map_of ls x = Some v \<and> P v \<theta>"
  by (induction ls gs rule: list_all2_induct) (auto split: if_splits)

lemma wf_env_of_list:
  assumes "wf_inst \<Sigma> \<eta>" and "wf_cxt \<Sigma> (fmap_of_list gs)"
    and "list_all2 (\<lambda>(x, v) (y, \<theta>). x = y \<and> \<turnstile> v : inst_entry \<eta> \<theta>) ls gs"
  shows "\<eta> \<turnstile> fmap_of_list ls : fmap_of_list gs"
  using assms(1, 2) map_of_list_all2[OF assms(3)] by (intro WfEnv) (auto simp: fmlookup_of_list)

lemma list_all2_keys:
  "list_all2 (\<lambda>(x, v) (y, \<theta>). x = y \<and> P v \<theta>) ls gs \<Longrightarrow> map fst ls = map fst gs"
  by (induction ls gs rule: list_all2_induct) auto

lemma prim_len_typed: "\<turnstile> VPrim PrimLen : Ty (TyCallable [TyPrim Sized] (TyPrim int))"
  by (rule ValPrim[where \<A> = "[]" and q = builtins and \<rho> = "the (fmlookup (\<E> []) builtins)" and x = "var ''len''"
        and \<Gamma> = "the (fmlookup \<P> builtins)", OF _ _ _ _ SubtyRefl])
     (simp_all add: \<E>_def \<P>_def fmlookup_of_list)

lemma prim_round_typed: "\<turnstile> VPrim PrimRound : Ty (TyCallable [TyPrim float] (TyPrim int))"
  by (rule ValPrim[where \<A> = "[]" and q = builtins and \<rho> = "the (fmlookup (\<E> []) builtins)" and x = "var ''round''"
        and \<Gamma> = "the (fmlookup \<P> builtins)", OF _ _ _ _ SubtyRefl])
     (simp_all add: \<E>_def \<P>_def fmlookup_of_list)

lemma prim_exit_typed: "\<turnstile> VPrim PrimExit : Ty (TyCallable [TyPrim int] (TyPrim Never))"
  by (rule ValPrim[where \<A> = "[]" and q = "name_of [''sys'']" and \<rho> = "the (fmlookup (\<E> []) (name_of [''sys'']))"
        and x = "var ''exit''" and \<Gamma> = "the (fmlookup \<P> (name_of [''sys'']))", OF _ _ _ _ SubtyRefl])
     (simp_all add: \<E>_def \<P>_def fmlookup_of_list builtins_def name_of_def)

lemmas prim_typed = prim_len_typed prim_round_typed prim_exit_typed

lemma predefined_typings:
  "\<turnstile> VClass range_class : Type range_class"
  "\<turnstile> VList (map (VLit \<circ> LitString) \<A>) : Ty (TyList (TyPrim str))"
proof -
  have "range_class |\<in>| fmdom \<Sigma>" using range_lookup by (simp add: predefined_classes_def fmlookup_dom_iff)
  then show "\<turnstile> VClass range_class : Type range_class" by (rule ValClass)
  show "\<turnstile> VList (map (VLit \<circ> LitString) \<A>) : Ty (TyList (TyPrim str))" by (rule wf_val_list) (auto simp: wf_str_char)
qed

lemma predefined_lists:
  "fmlookup (\<E> \<A>) q = Some \<rho> \<Longrightarrow> \<exists>ls gs. \<rho> = fmap_of_list ls \<and> fmlookup \<P> q = Some (fmap_of_list gs)
     \<and> list_all2 (\<lambda>(x, v) (y, \<theta>). x = y \<and> \<turnstile> v : inst_entry \<eta> \<theta>) ls gs"
  by (auto simp: \<E>_def \<P>_def fmlookup_of_list wf_str_char prim_typed predefined_typings ValPredef split: if_splits
      simp del: fmap_of_list_simps intro!: exI conjI)

(* Environments of the predefined modules, typed by their contexts *)
lemma predefined_env:
  assumes "fmlookup (\<E> \<A>) q = Some \<rho>" and "wf_inst \<Sigma> \<eta>"
  shows "\<exists>\<Gamma>. fmlookup \<P> q = Some \<Gamma> \<and> \<eta> \<turnstile> \<rho> : \<Gamma> \<and> fmdom \<rho> = fmdom \<Gamma>"
proof -
  from predefined_lists[OF assms(1), of \<eta>] obtain ls gs where \<rho>: "\<rho> = fmap_of_list ls"
    and P: "fmlookup \<P> q = Some (fmap_of_list gs)"
    and typed: "list_all2 (\<lambda>(x, v) (y, \<theta>). x = y \<and> \<turnstile> v : inst_entry \<eta> \<theta>) ls gs"
    by blast
  have "\<eta> \<turnstile> \<rho> : fmap_of_list gs" unfolding \<rho> by (rule wf_env_of_list[OF assms(2) predefined_cxt_wf[OF P] typed])
  moreover have "fmdom \<rho> = fmdom (fmap_of_list gs)" unfolding \<rho> using list_all2_keys[OF typed] by simp
  ultimately show ?thesis using P by blast
qed

lemma wf_class_table_predefined: "wf_class_table predefined_classes"
proof -
  have cxt: "wf_cxt predefined_classes (the (fmlookup \<P> builtins))"
    by (auto simp: \<P>_def fmlookup_of_list wf_cxt_iff builtins_def name_of_def predefined_classes_def range_class_def
        type_params_def dest!: map_of_SomeD)
  have tv: "tyvars (the (fmlookup \<P> builtins)) = {}"
    by (rule tyvars_empty) (auto simp: \<P>_def fmlookup_of_list builtins_def name_of_def split: if_splits dest!: map_of_SomeD)
  have dom: "fmdom predefined_classes = {|range_class|}" by (simp add: predefined_classes_def)
  have card: "fcard (fmdom predefined_classes) = Suc 0" by (simp add: dom fcard_finsert_disjoint)
  have look: "fmlookup predefined_classes range_class
    = Some (ClassDef (the (fmlookup \<P> builtins)) builtins
        [At no_pos (Dataclass (var ''range'') [] None [(var ''start'', TyExprPrim int), (var ''stop'', TyExprPrim int)])] 0)"
    by (simp add: predefined_classes_def)
  have range: "Qualified builtins (var ''range'') = range_class" by (simp add: range_class_def builtins_def name_of_def)
  have base: "base predefined_classes range_class = None" using look by (simp add: base_def)
  have params: "type_params predefined_classes range_class = []" using look by (simp add: type_params_def)
  have decl: "declared_fields predefined_classes range_class [] = [(var ''start'', TyPrim int), (var ''stop'', TyPrim int)]"
    using look
    by (simp add: declared_fields_def resolve_type_def check_type_head_def check_predefined_def ensure_def
        type_context_def \<P>_def fmlookup_of_list fmconst_def)
  have fields: "fields predefined_classes range_class = FieldScheme [] [(var ''start'', TyPrim int), (var ''stop'', TyPrim int)]"
    using look decl
    by (simp add: fields_def instantiated_ancestors_def Let_def params base card)
  show ?thesis
    unfolding wf_class_table_def dom
    using cxt tv look base params decl fields range by (auto simp: field_names_def card[unfolded dom])
qed

end

end
