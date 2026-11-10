(* Soundness of evaluation of comprehensions *)
theory Comprehensions
  imports Expressions
begin

context wf_evaluation
begin

(* Element of a list comprehension typed under its qualifiers at a subtype of the element type *)
lemma list_comp_typed:
  assumes "typed_by_rule \<Sigma> \<Gamma> (ExprListComp e gs) \<tau>"
  shows "\<exists>\<Delta> \<tau>' \<sigma>. \<tau> = TyList \<tau>' \<and> quals \<Sigma> \<Gamma> gs = Ok \<Delta> \<and> has_type_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  using assms unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprListComp e gs) = Ok \<tau>"
  then show ?thesis by (auto simp: bind_sum_def intro: has_type_synth_at base_type_upper split: sum.splits)
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprListComp e gs) \<tau> = Some (Ok ()) \<and> wf_ty \<Sigma> \<tau>"
  then show ?thesis
    by (auto simp: bind_sum_def intro: has_type_check_at SubtyRefl split: ty.splits sum.splits)
qed

lemma list_comp_sound:
  assumes "sound_quals \<rho> gs (Val \<rho>s)" and "sound_comp \<rho>s e (Val vs)"
  shows "sound_expr \<rho> (ExprListComp e gs) (Val (VList vs))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprListComp e gs) \<tau>"
  from list_comp_typed[OF this(2)] obtain \<Delta> \<tau>' \<sigma> where \<tau>: "\<tau> = TyList \<tau>'" and "quals \<Sigma> \<Gamma> gs = Ok \<Delta>"
    and e: "has_type_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    by blast
  with assms(1) env have envs: "\<forall>\<rho>' \<in> set \<rho>s. \<eta> \<turnstile> \<rho>' : \<Gamma> \<otimes> \<Delta>" by (simp add: sound_quals_def)
  have wf: "wf_ty \<Sigma> \<tau>'"
    using typed_by_rule_wf[OF wf_env_wf_cxt[OF env] \<open>typed_by_rule _ _ _ _\<close>] by (simp add: \<tau>)
  from sound_compD[OF assms(2) envs e] sub wf wf_env_wf_inst[OF env]
  show "result_typed (Val (VList vs)) (inst \<eta> \<tau>)" by (auto simp: \<tau> intro: wf_val_list wf_val_inst_sub inst_wf)
qed simp_all

lemma list_comp_fail_quals_sound:
  assumes "sound_quals \<rho> gs (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprListComp e gs) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprListComp e gs) \<tau>"
  from list_comp_typed[OF this(2)] assms env show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)"
    by (auto simp: sound_quals_def)
qed simp_all

lemma list_comp_fail_sound:
  assumes "sound_quals \<rho> gs (Val \<rho>s)" and "sound_comp \<rho>s e (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprListComp e gs) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprListComp e gs) \<tau>"
  from list_comp_typed[OF this(2)] obtain \<Delta> \<sigma> where "quals \<Sigma> \<Gamma> gs = Ok \<Delta>"
    and e: "has_type_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<sigma>"
    by blast
  with assms(1) env have "\<forall>\<rho>' \<in> set \<rho>s. \<eta> \<turnstile> \<rho>' : \<Gamma> \<otimes> \<Delta>" by (simp add: sound_quals_def)
  from sound_compD[OF assms(2) this e] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by simp
qed simp_all

(* Key of a dictionary comprehension checked against str, and its value typed at a subtype of the value type,
   under its qualifiers *)
lemma dict_comp_typed:
  assumes "typed_by_rule \<Sigma> \<Gamma> (ExprDictComp e e' gs) \<tau>"
  shows "\<exists>\<Delta> \<tau>' \<sigma>. \<tau> = TyDict \<tau>' \<and> quals \<Sigma> \<Gamma> gs = Ok \<Delta> \<and> check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str) = Ok ()
           \<and> has_type_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  using assms unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprDictComp e e' gs) = Ok \<tau>"
  then show ?thesis by (auto simp: bind_sum_def intro: has_type_synth_at base_type_upper split: sum.splits)
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprDictComp e e' gs) \<tau> = Some (Ok ()) \<and> wf_ty \<Sigma> \<tau>"
  then show ?thesis
    by (auto simp: bind_sum_def intro: has_type_check_at SubtyRefl split: ty.splits sum.splits)
qed

lemma dict_comp_sound:
  assumes "sound_quals \<rho> gs (Val \<rho>s)" and "sound_entries \<rho>s e e' (Val \<delta>)"
  shows "sound_expr \<rho> (ExprDictComp e e' gs) (Val (VDict (update [] \<delta>)))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprDictComp e e' gs) \<tau>"
  from dict_comp_typed[OF this(2)] obtain \<Delta> \<tau>' \<sigma> where \<tau>: "\<tau> = TyDict \<tau>'" and "quals \<Sigma> \<Gamma> gs = Ok \<Delta>"
    and key: "check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str) = Ok ()" and e': "has_type_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<sigma>"
    and sub: "\<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    by blast
  with assms(1) env have envs: "\<forall>\<rho>' \<in> set \<rho>s. \<eta> \<turnstile> \<rho>' : \<Gamma> \<otimes> \<Delta>" by (simp add: sound_quals_def)
  have wf: "wf_ty \<Sigma> \<tau>'"
    using typed_by_rule_wf[OF wf_env_wf_cxt[OF env] \<open>typed_by_rule _ _ _ _\<close>] by (simp add: \<tau>)
  from sound_entriesD[OF assms(2) envs key e'] sub wf wf_env_wf_inst[OF env]
  have "\<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>')" by (auto intro: wf_val_inst_sub)
  then show "result_typed (Val (VDict (update [] \<delta>))) (inst \<eta> \<tau>)"
    by (simp add: \<tau> wf_dict_update inst_wf[OF wf_env_wf_inst[OF env] wf])
qed simp_all

lemma dict_comp_fail_quals_sound:
  assumes "sound_quals \<rho> gs (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprDictComp e e' gs) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprDictComp e e' gs) \<tau>"
  from dict_comp_typed[OF this(2)] assms env show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)"
    by (auto simp: sound_quals_def)
qed simp_all

lemma dict_comp_fail_sound:
  assumes "sound_quals \<rho> gs (Val \<rho>s)" and "sound_entries \<rho>s e e' (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprDictComp e e' gs) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprDictComp e e' gs) \<tau>"
  from dict_comp_typed[OF this(2)] obtain \<Delta> \<sigma> where "quals \<Sigma> \<Gamma> gs = Ok \<Delta>"
    and key: "check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str) = Ok ()" and e': "has_type_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<sigma>"
    by blast
  with assms(1) env have "\<forall>\<rho>' \<in> set \<rho>s. \<eta> \<turnstile> \<rho>' : \<Gamma> \<otimes> \<Delta>" by (simp add: sound_quals_def)
  from sound_entriesD[OF assms(2) this key e'] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by simp
qed simp_all

lemma quals_nil_sound: "sound_quals \<rho> [] (Val [\<rho>])"
  by (simp add: sound_quals_def)

lemma qual_guard_true_sound: "sound_quals \<rho> gs r \<Longrightarrow> sound_quals \<rho> (At p (Guard e) # gs) r"
  by (auto simp: sound_quals_def bind_sum_def split: sum.splits)

lemma qual_guard_false_sound: "sound_expr \<rho> (node e) (Val false) \<Longrightarrow> sound_quals \<rho> (At p (Guard e) # gs) (Val [])"
  by (simp add: sound_quals_def)

lemma qual_guard_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_quals \<rho> (At p (Guard e) # gs) (Aborts \<kappa>)"
  by (auto simp: sound_quals_def bind_sum_def dest: prim_operand split: sum.splits)

lemma qual_guard_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_quals \<rho> (At p (Guard e) # gs) (Aborts Excluded)"
  by (auto simp: sound_quals_def bind_sum_def dest!: bool_operand split: sum.splits)

(* Elements drawn by a generator from a value, typed by the element type of a type of the value *)
lemma iter_typed:
  "\<lbrakk> \<turnstile> v : Ty (inst \<eta> \<sigma>) ; elem_type \<Sigma> \<sigma> = Some \<tau> ; iter v = Some us ; wf_inst \<Sigma> \<eta> \<rbrakk>
  \<Longrightarrow> \<forall>u \<in> set us. \<turnstile> u : Ty (inst \<eta> \<tau>)"
proof (induction \<sigma> arbitrary: v \<tau> us)
  case (TyList \<sigma>)
  from TyList(2) obtain vs where "v = VList vs" and "\<forall>u \<in> set vs. \<turnstile> u : Ty (inst \<eta> \<sigma>)"
    by (auto elim: wf_list)
  with TyList(3, 4) show ?case by simp
next
  case (TyPrim p)
  then have "p = str" and \<tau>: "\<tau> = TyPrim str" by (cases p; simp)+
  with TyPrim(1) obtain w where "v = VLit (LitString w)" by (auto dest: wf_str intro: SubtyRefl)
  with TyPrim(3) \<tau> show ?case by (auto intro: wf_str_char)
next
  case (TyLiteral l)
  then obtain w where l: "l = LitString w" and \<tau>: "\<tau> = TyPrim str" by (cases l) simp_all
  have "\<Sigma> \<turnstile> TyLiteral l <: TyPrim str" unfolding l by (rule SubtyLiteral) (simp add: SubtyRefl)
  with TyLiteral(1) obtain w' where "v = VLit (LitString w')" by (auto dest: wf_str)
  with TyLiteral(3) \<tau> show ?case by (auto intro: wf_str_char)
next
  case (TyDict \<sigma>)
  then have \<tau>: "\<tau> = TyPrim str" by simp
  from TyDict(2) obtain \<delta> where "v = VDict \<delta>" by (auto elim: wf_dict)
  with TyDict(4) \<tau> show ?case by (auto intro: wf_str_char)
next
  case (TyClass C \<sigma>s)
  then have C: "C = range_class" and "\<sigma>s = []" and \<tau>: "\<tau> = TyPrim int"
    by (auto split: if_splits elim: elem_type.elims)
  from wf_object_type[OF TyClass(2)] obtain D xvs where "v = VObject D xvs" by (cases v) auto
  with TyClass(4) \<tau> show ?case
    by (auto intro: wf_int_lit split: if_splits option.splits val.splits lit.splits)
next
  case (TyTuple \<sigma>s)
  then have \<tau>: "\<tau> = joins \<Sigma> (map base_type \<sigma>s)" by simp
  from TyTuple(2) obtain vs where v: "v = VTuple vs" and vs: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs (map (inst \<eta>) \<sigma>s)"
    by (auto elim: wf_tuple)
  show ?case
  proof
    fix u
    assume "u \<in> set us"
    with TyTuple(4) v obtain i where i: "i < length vs" and u: "u = vs ! i" by (auto simp: in_set_conv_nth)
    with vs have "\<turnstile> u : Ty (inst \<eta> (\<sigma>s ! i))" and "i < length \<sigma>s" by (auto simp: list_all2_conv_all_nth)
    have wfs: "\<forall>\<sigma> \<in> set (map base_type \<sigma>s). wf_ty \<Sigma> \<sigma>"
      using wf_ty_inst_inv[OF wf_val_ty[OF TyTuple(2)]] by (auto intro: base_type_wf)
    have wf\<tau>: "wf_ty \<Sigma> \<tau>" unfolding \<tau> by (rule joins_wf[OF wfs])
    have wf\<sigma>: "wf_ty \<Sigma> (\<sigma>s ! i)" using wf_ty_inst_inv[OF wf_val_ty[OF TyTuple(2)]] \<open>i < length \<sigma>s\<close> by simp
    from \<open>i < length \<sigma>s\<close> have "\<Sigma> \<turnstile> base_type (\<sigma>s ! i) <: \<tau>" unfolding \<tau> by (auto intro: joins_upper[OF wfs])
    with base_type_upper have "\<Sigma> \<turnstile> \<sigma>s ! i <: \<tau>"
      by (rule subty_trans[OF wf_class_table wf\<sigma> base_type_wf[OF wf\<sigma>]])
    with \<open>\<turnstile> u : Ty (inst \<eta> (\<sigma>s ! i))\<close> wf\<tau> TyTuple(5) show "\<turnstile> u : Ty (inst \<eta> \<tau>)"
      by (blast intro: wf_val_inst_sub)
  qed
next
  case (TyUnion \<sigma> \<sigma>')
  from TyUnion(4) obtain \<tau>' \<tau>'' where \<tau>': "elem_type \<Sigma> \<sigma> = Some \<tau>'" and \<tau>'': "elem_type \<Sigma> \<sigma>' = Some \<tau>''"
    and \<tau>: "\<tau> = \<tau>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>''"
    by (auto split: option.splits)
  have wf: "wf_ty \<Sigma> (\<tau>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>'')"
    using wf_ty_inst_inv[OF wf_val_ty[OF TyUnion(3)]] elem_type_wf[OF _ \<tau>'] elem_type_wf[OF _ \<tau>'']
    by (auto intro: join_wf)
  from wf_val_union[of v "inst \<eta> \<sigma>" "inst \<eta> \<sigma>'"] TyUnion(3) have "\<turnstile> v : Ty (inst \<eta> \<sigma>) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>')"
    by simp
  then show ?case
  proof
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    from TyUnion(1)[OF this \<tau>' TyUnion(5, 6)] show ?thesis
      unfolding \<tau> by (blast intro: wf_val_inst_sub[OF _ _ wf TyUnion(6)] join_upper)
  next
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>')"
    from TyUnion(2)[OF this \<tau>'' TyUnion(5, 6)] show ?thesis
      unfolding \<tau> by (blast intro: wf_val_inst_sub[OF _ _ wf TyUnion(6)] join_upper)
  qed
qed simp_all

lemma qual_generator_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and "iter v = Some us" and "sound_gen \<rho> x us gs r"
  shows "sound_quals \<rho> (At p (Generator x e) # gs) r"
  unfolding sound_quals_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<Delta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "quals \<Sigma> \<Gamma> (At p (Generator x e) # gs) = Ok \<Delta>"
  then obtain \<sigma> \<tau> \<Delta>' where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and elem: "elem_type \<Sigma> \<sigma> = Some \<tau>"
    and \<Delta>': "quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>'" and \<Delta>: "\<Delta> = fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>'"
    by (auto simp: bind_sum_def or_else_def ensure_def split: sum.splits option.splits if_splits)
  from sound_expr_synth_at[OF assms(1) env synth] have "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by simp
  from iter_typed[OF this elem assms(2) wf_env_wf_inst[OF env]] have us: "\<forall>u \<in> set us. \<turnstile> u : Ty (inst \<eta> \<tau>)" .
  have "wf_ty \<Sigma> \<tau>" using elem_type_wf[OF synth_at_wf_ty[OF wf_env_wf_cxt[OF env] synth] elem] .
  then have "wf_envs \<eta> r (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>')"
    using assms(3) env us \<Delta>' by (simp add: sound_gen_def)
  with \<Delta> show "wf_envs \<eta> r (\<Gamma> \<otimes> \<Delta>)" by simp
qed

lemma qual_generator_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_quals \<rho> (At p (Generator x e) # gs) (Aborts \<kappa>)"
  by (auto simp: sound_quals_def bind_sum_def dest: sound_expr_synth_at split: sum.splits)

(* Value of a type with an element type, from which a generator draws elements *)
lemma iter_defined: "\<lbrakk> \<turnstile> v : Ty (inst \<eta> \<sigma>) ; elem_type \<Sigma> \<sigma> = Some \<tau> \<rbrakk> \<Longrightarrow> iter v \<noteq> None"
proof (induction \<sigma> arbitrary: v \<tau>)
  case (TyList \<sigma>)
  from TyList(2) show ?case by (auto elim: wf_list)
next
  case (TyPrim p)
  then have "p = str" by (cases p) simp_all
  with TyPrim(1) show ?case by (auto dest: wf_str intro: SubtyRefl)
next
  case (TyLiteral l)
  then obtain w where l: "l = LitString w" by (cases l) simp_all
  have "\<Sigma> \<turnstile> TyLiteral l <: TyPrim str" unfolding l by (rule SubtyLiteral) (simp add: SubtyRefl)
  with TyLiteral(1) show ?case by (auto dest: wf_str)
next
  case (TyDict \<sigma>)
  from TyDict(2) show ?case by (auto elim: wf_dict)
next
  case (TyClass C \<sigma>s)
  then have C: "C = range_class" and "\<sigma>s = []" by (auto split: if_splits elim: elem_type.elims)
  with TyClass(2) have v: "\<turnstile> v : Ty (TyClass range_class [])" by simp
  from wf_object_type[OF v] obtain D xvs where v': "v = VObject D xvs" by (cases v) auto
  with v have "\<turnstile> VObject D xvs : Ty (TyClass range_class [])" by simp
  from iter_range[OF this] v' show ?case by simp
next
  case (TyTuple \<sigma>s)
  from TyTuple(2) show ?case by (auto elim: wf_tuple)
next
  case (TyUnion \<sigma> \<sigma>')
  from TyUnion(4) obtain \<tau>' \<tau>'' where "elem_type \<Sigma> \<sigma> = Some \<tau>'" and "elem_type \<Sigma> \<sigma>' = Some \<tau>''"
    by (auto split: option.splits)
  with TyUnion(1, 2) wf_val_union[of v "inst \<eta> \<sigma>" "inst \<eta> \<sigma>'"] TyUnion(3) show ?case by auto
qed simp_all

lemma qual_generator_nonseq_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and "iter v = None"
  shows "sound_quals \<rho> (At p (Generator x e) # gs) (Aborts TypeError)"
  unfolding sound_quals_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<Delta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "quals \<Sigma> \<Gamma> (At p (Generator x e) # gs) = Ok \<Delta>"
  then obtain \<sigma> \<tau> where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and elem: "elem_type \<Sigma> \<sigma> = Some \<tau>"
    by (auto simp: bind_sum_def or_else_def ensure_def split: sum.splits option.splits if_splits)
  from sound_expr_synth_at[OF assms(1) env synth] have "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by simp
  from iter_defined[OF this elem] assms(2) show "wf_envs \<eta> (Aborts TypeError) (\<Gamma> \<otimes> \<Delta>)" by simp
qed

lemma gen_nil_sound: "sound_gen \<rho> x [] gs (Val [])"
  by (simp add: sound_gen_def)

lemma gen_cons_sound:
  assumes "sound_quals (fmupd x u \<rho>) gs (Val \<rho>s)" and "sound_gen \<rho> x us gs r"
  shows "sound_gen \<rho> x (u # us) gs (mlet r (\<lambda>\<rho>ss. Val (\<rho>s @ \<rho>ss)))"
  unfolding sound_gen_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<tau> \<Delta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and wf: "wf_ty \<Sigma> \<tau>" and us: "\<forall>u' \<in> set (u # us). \<turnstile> u' : Ty (inst \<eta> \<tau>)"
    and quals: "quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>"
  have "\<eta> \<turnstile> fmupd x u \<rho> : fmupd x (Ty \<tau>) \<Gamma>" using env wf us by (intro wf_env_upd) auto
  with assms(1) quals have "wf_envs \<eta> (Val \<rho>s) (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)" by (simp add: sound_quals_def)
  moreover from assms(2) env wf us quals have "wf_envs \<eta> r (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)"
    by (simp add: sound_gen_def)
  ultimately show "wf_envs \<eta> (mlet r (\<lambda>\<rho>ss. Val (\<rho>s @ \<rho>ss))) (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)"
    by (cases r) auto
qed

lemma gen_fail_sound:
  assumes "sound_quals (fmupd x u \<rho>) gs (Aborts \<kappa>)"
  shows "sound_gen \<rho> x (u # us) gs (Aborts \<kappa>)"
  unfolding sound_gen_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<tau> \<Delta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and wf: "wf_ty \<Sigma> \<tau>" and us: "\<forall>u' \<in> set (u # us). \<turnstile> u' : Ty (inst \<eta> \<tau>)"
    and quals: "quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>"
  have "\<eta> \<turnstile> fmupd x u \<rho> : fmupd x (Ty \<tau>) \<Gamma>" using env wf us by (intro wf_env_upd) auto
  with assms quals show "wf_envs \<eta> (Aborts \<kappa>) (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)" by (simp add: sound_quals_def)
qed

lemma comp_nil_sound: "sound_comp [] e (Val [])"
  by (simp add: sound_comp_def)

lemma comp_cons_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and "sound_comp \<rho>s e r"
  shows "sound_comp (\<rho> # \<rho>s) e (mlet r (\<lambda>vs. Val (v # vs)))"
  unfolding sound_comp_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume envs: "\<forall>\<rho> \<in> set (\<rho> # \<rho>s). \<eta> \<turnstile> \<rho> : \<Gamma>" and e: "has_type_at \<Sigma> \<Gamma> e \<tau>"
  from assms(1) envs e have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_has_type_at)
  moreover from envs have "\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>" by simp
  with assms(2) e have "wf_elems r (inst \<eta> \<tau>)" by (blast intro: sound_compD)
  ultimately show "wf_elems (mlet r (\<lambda>vs. Val (v # vs))) (inst \<eta> \<tau>)" by (cases r) simp_all
qed

lemma comp_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_comp (\<rho> # \<rho>s) e (Aborts \<kappa>)"
  unfolding sound_comp_def by (auto dest: sound_expr_has_type_at)

lemma entries_nil_sound: "sound_entries [] e e' (Val [])"
  by (simp add: sound_entries_def)

lemma entries_cons_sound:
  assumes "sound_expr \<rho> (node e') (Val v)" and "sound_entries \<rho>s e e' r"
  shows "sound_entries (\<rho> # \<rho>s) e e' (mlet r (\<lambda>\<delta>. Val ((w, v) # \<delta>)))"
  unfolding sound_entries_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume envs: "\<forall>\<rho> \<in> set (\<rho> # \<rho>s). \<eta> \<turnstile> \<rho> : \<Gamma>" and key: "check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()"
    and e': "has_type_at \<Sigma> \<Gamma> e' \<tau>"
  from assms(1) envs e' have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_has_type_at)
  moreover from envs have "\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>" by simp
  with assms(2) key e' have "wf_entries r (inst \<eta> \<tau>)" by (blast intro: sound_entriesD)
  ultimately show "wf_entries (mlet r (\<lambda>\<delta>. Val ((w, v) # \<delta>))) (inst \<eta> \<tau>)" by (cases r) auto
qed

lemma entries_fail_key_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_entries (\<rho> # \<rho>s) e e' (Aborts \<kappa>)"
  unfolding sound_entries_def by (auto dest: prim_operand)

lemma entries_nonstr_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; \<forall>w. v \<noteq> VLit (LitString w) \<rbrakk>
  \<Longrightarrow> sound_entries (\<rho> # \<rho>s) e e' (Aborts Excluded)"
  unfolding sound_entries_def by (auto dest!: str_operand)

lemma entries_fail_value_sound:
  "sound_expr \<rho> (node e') (Aborts \<kappa>) \<Longrightarrow> sound_entries (\<rho> # \<rho>s) e e' (Aborts \<kappa>)"
  unfolding sound_entries_def by (auto dest: sound_expr_has_type_at)

end

end
