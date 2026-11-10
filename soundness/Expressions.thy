(* Soundness of evaluation of expressions other than calls, subscripts, attributes and comprehensions *)
theory Expressions
  imports ResultTyping
begin

context evaluation
begin

(* Value at the instance by \<eta> of a scheme bound to a name checked against \<tau>, typed at the instance of \<tau> *)
lemma scheme_instance_typed:
  assumes v: "\<turnstile> v : inst_entry \<eta> (Scheme (TyScheme \<alpha>s \<sigma>))" and \<eta>: "wf_inst \<Sigma> \<eta>" and wf: "wf_ty \<Sigma> \<tau>"
    and \<tau>s: "Subtyping.type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s" and sub: "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: \<tau>"
  shows "\<turnstile> v : Ty (inst \<eta> \<tau>)"
proof -
  have len: "length \<tau>s = length \<alpha>s" using \<tau>s by (rule type_args_of_length)
  have closed: "\<forall>\<tau>' \<in> set (map (inst \<eta>) \<tau>s). fv \<tau>' = {}" by (simp add: inst_closed[OF \<eta>])
  have wfs: "\<forall>\<tau>' \<in> set (map (inst \<eta>) \<tau>s). wf_ty \<Sigma> \<tau>'" using type_args_wf[OF wf \<tau>s] \<eta> by (auto intro: inst_wf)
  from wf_val_inst[OF v[simplified] _ closed wfs] len
  have "\<turnstile> v : Ty (subst (map (inst \<eta>) \<tau>s) \<alpha>s (inst (shadow \<alpha>s \<eta>) \<sigma>))" by simp
  then have "\<turnstile> v : Ty (inst \<eta> (subst \<tau>s \<alpha>s \<sigma>))" by (simp only: inst_subst[OF \<eta> len])
  then show ?thesis using sub wf \<eta> by (rule wf_val_inst_sub)
qed

lemma var_sound:
  assumes "fmlookup \<rho> x = Some v" and "v \<noteq> VUnbound"
  shows "sound_expr \<rho> (ExprVar x) (Val v)"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprVar x) = Ok \<tau>"
  then have "fmlookup \<Gamma> x = Some (Ty \<tau>)" by (auto split: option.splits cxt_entry.splits)
  with env assms(1) show "result_typed (Val v) (inst \<eta> \<tau>)" by (auto dest!: wf_env_lookup)
next
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr' \<Sigma> \<Gamma> (ExprVar x) \<tau> = Some (Ok ())" and wf: "wf_ty \<Sigma> \<tau>"
  then obtain \<alpha>s \<sigma> \<tau>s where \<Gamma>x: "fmlookup \<Gamma> x = Some (Scheme (TyScheme \<alpha>s \<sigma>))"
    and \<tau>s: "Subtyping.type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s"
    and sub: "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: \<tau>"
    by (auto simp: var_scheme_def scheme_of_name_def entry_of_def resolve_name_def bind_sum_def ensure_def
        Let_def split: option.splits cxt_entry.splits ty_scheme.splits if_splits sum.splits)
  from env \<Gamma>x assms(1) have "\<turnstile> v : inst_entry \<eta> (Scheme (TyScheme \<alpha>s \<sigma>))" by (auto dest!: wf_env_lookup)
  from scheme_instance_typed[OF this wf_env_wf_inst[OF env] wf \<tau>s sub]
  show "result_typed (Val v) (inst \<eta> \<tau>)" by simp
next
  show "sound_name \<rho> (ExprVar x) (Val v)"
    using assms(1)
    by (auto simp: sound_name_def entry_of_def resolve_name_def split: option.splits cxt_entry.splits
        dest!: wf_env_lookup)
qed simp_all

lemma var_unknown_sound: "fmlookup \<rho> x = None \<Longrightarrow> sound_expr \<rho> (ExprVar x) (Aborts NameError)"
  by (rule sound_exprI)
     (auto simp: var_scheme_def scheme_of_name_def entry_of_def resolve_name_def sound_name_def
      split: option.splits cxt_entry.splits dest!: wf_env_lookup)

lemma var_unbound_sound: "fmlookup \<rho> x = Some VUnbound \<Longrightarrow> sound_expr \<rho> (ExprVar x) (Aborts NameError)"
  by (rule sound_exprI)
     (auto simp: var_scheme_def scheme_of_name_def entry_of_def resolve_name_def sound_name_def
      split: option.splits cxt_entry.splits dest!: wf_env_lookup wf_unbound_ty wf_unbound_scheme wf_unbound)

lemma literal_sound: "sound_expr \<rho> (ExprLiteral l) (Val (VLit l))"
  by (rule sound_expr_synthI)
     (auto simp: var_scheme_None wf_val_lit wf_val_float split: lit.splits)

lemma lambda_sound: "sound_expr \<rho> (ExprLambda xs e) (Val Lam(\<rho>, xs, e))"
  by (rule sound_exprI)
     (auto simp: bind_sum_def intro!: ValLambda SubtyRefl inst_wf[OF wf_env_wf_inst]
      split: ty.splits if_splits sum.splits)

lemma unop_overload_sub: "unop_overload \<Sigma> op \<sigma> \<omega> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: fst \<omega>"
proof (induction rule: unop_overload.induct)
  case (UnopOverloadBase \<sigma> op \<tau> \<tau>')
  then obtain l where \<sigma>: "\<sigma> = TyLiteral l" by (cases \<sigma>) simp_all
  have "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    by (rule subty_trans[OF wf_class_table _ _ base_type_upper UnopOverloadBase(3)[simplified]])
       (simp_all add: \<sigma>)
  then show ?case by simp
qed simp_all

(* Meaning of a unary operator at an operand typed by the operand type of an overload *)
lemma unop_meaning_typed:
  assumes "\<turnstile> v : Ty \<tau>" and "unop_overload \<Sigma> op \<sigma> (\<tau>, \<tau>')"
  shows "result_typed (unop_meaning op v) \<tau>'"
proof -
  from unop_overload_types[OF assms(2)] consider (not) "op = UOpNot" "\<tau> = TyPrim bool" "\<tau>' = TyPrim bool"
    | (num) "op \<in> {UOpPos, UOpNeg}" "\<tau> = TyPrim int \<and> \<tau>' = TyPrim int \<or> \<tau> = TyPrim float \<and> \<tau>' = TyPrim float"
    by auto
  then show ?thesis
  proof cases
    case not
    with assms(1) have "\<turnstile> v : Ty (TyPrim bool)" by simp
    then have "v = true \<or> v = false" by (rule wf_bool) (rule SubtyRefl)
    with not lit_subty_base[where l = "LitBool True"] lit_subty_base[where l = "LitBool False"] show ?thesis
      by (auto intro: wf_lit_bool)
  next
    case num
    then have p: "\<Sigma> \<turnstile> \<tau> <: TyPrim float" and "\<tau> = \<tau>'" by (auto intro: SubtyRefl SubtyIntFloat)
    from assms(1) num obtain l where v: "v = VLit l"
      and l: "prim_subtype (case \<tau> of TyPrim p \<Rightarrow> p) (TyLiteral l)"
      by (auto elim!: wf_prim_lit[OF _ SubtyRefl])
    from l num obtain n x where "l = LitInt n \<or> \<tau> = TyPrim float \<and> l = LitFloat x"
      by (cases l) auto
    then show ?thesis
    proof
      assume "l = LitInt n"
      moreover have "\<Sigma> \<turnstile> TyLiteral (LitInt n) <: TyPrim float"
        by (rule SubtyLiteral) (simp add: SubtyIntFloat)
      moreover have "\<turnstile> VLit (LitInt (- n)) : Ty \<tau>'" using num by (auto intro: wf_int_lit wf_int_float)
      ultimately show ?thesis using num assms(1) v \<open>\<tau> = \<tau>'\<close> by auto
    next
      assume "\<tau> = TyPrim float \<and> l = LitFloat x"
      with num assms(1) v \<open>\<tau> = \<tau>'\<close> show ?thesis by (auto simp: wf_val_float SubtyRefl)
    qed
  qed
qed

lemma unop_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_expr \<rho> (ExprUnOp op e) (mlet r (unop_meaning op))"
proof (rule sound_expr_synthI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprUnOp op e) = Ok \<tau>"
  then obtain \<sigma> where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and res: "resolve_unop \<Sigma> op \<sigma> = Some \<tau>"
    by (auto simp: bind_sum_def or_else_def split: if_splits sum.splits option.splits)
  from res obtain \<tau>'' where ov: "unop_overload \<Sigma> op \<sigma> (\<tau>'', \<tau>)" by (rule resolve_unop_overload)
  from unop_overload_types[OF ov] have closed: "fv \<tau>'' = {}" "fv \<tau> = {}" by auto
  from sound_expr_synth_at[OF assms env \<sigma>] have r: "result_typed r (inst \<eta> \<sigma>)" .
  show "result_typed (mlet r (unop_meaning op)) (inst \<eta> \<tau>)"
  proof (cases r)
    case (Val v)
    with r have "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by simp
    moreover have "wf_ty \<Sigma> \<tau>''" using unop_overload_types[OF ov] by auto
    ultimately have "\<turnstile> v : Ty \<tau>''"
      using wf_val_inst_sub[OF _ unop_overload_sub[OF ov] _ wf_env_wf_inst[OF env]] closed
      by (simp add: inst_closed_ty)
    from unop_meaning_typed[OF this ov] Val closed show ?thesis by (simp add: inst_closed_ty)
  next
    case (Aborts \<kappa>)
    with r show ?thesis by simp
  qed
qed (simp_all add: var_scheme_None)

lemma binop_overload_sub: "binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: fst (fst \<omega>) \<and> \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: snd (fst \<omega>)"
proof (induction rule: binop_overload.induct)
  case (OverloadBase \<sigma>\<^sub>1 \<sigma>\<^sub>2 op \<tau>\<^sub>1 \<tau>\<^sub>2 \<tau>)
  have "\<Sigma> \<turnstile> \<sigma> <: \<tau>'" if "\<Sigma> \<turnstile> base_type \<sigma> <: \<tau>'" for \<sigma> \<tau>'
  proof (cases \<sigma>)
    case (TyLiteral l)
    show ?thesis by (rule subty_trans[OF wf_class_table _ _ base_type_upper that]) (simp_all add: TyLiteral)
  qed (use that in simp_all)
  with OverloadBase show ?case by auto
qed (auto intro: SubtyRefl)

lemmas binop_simps = binop_meaning_def overload_def tuple_overload_def subty_prim_iff subty_list_iff SubtyRefl
  SubtyObject compare_numbers_def compare_strings_def int_arith_def int_division_def int_quotient_def
  float_arith_def float_division_def float_operands_def float_of_def float_power_def int_power_def
  concat_str_def concat_list_def concat_tuple_def repeat_str_def repeat_list_def Let_def wf_int_lit wf_int_float
  ValLitFloat wf_lit_bool wf_str_char

(* Meaning of a binary operator at operands typed by the operand types of an overload *)
lemma binop_meaning_typed:
  "\<lbrakk> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega> ; \<turnstile> v : Ty (inst \<eta> (fst (fst \<omega>))) ; \<turnstile> u : Ty (inst \<eta> (snd (fst \<omega>)))
   ; wf_inst \<Sigma> \<eta> \<rbrakk>
  \<Longrightarrow> result_typed (binop_meaning op v u) (inst \<eta> (snd \<omega>))"
proof (induction rule: binop_overload.induct)
  case OverloadEq
  then show ?case using eq_abort(1)[of v u] by (cases "eq v u") (auto simp: binop_simps)
next
  case (OverloadInList op \<sigma>\<^sub>1 \<tau>)
  from OverloadInList.prems(2) obtain us where "u = VList us" by (auto elim: wf_list)
  with OverloadInList.hyps(1) show ?case
    using in_elems_abort[of v us] by (cases "in_elems v us") (auto simp: binop_simps)
next
  case (OverloadInTuple op \<sigma>\<^sub>1 \<tau>s)
  from OverloadInTuple.prems(2) obtain us where "u = VTuple us" by (auto elim: wf_tuple)
  with OverloadInTuple.hyps(1) show ?case
    using in_elems_abort[of v us] by (cases "in_elems v us") (auto simp: binop_simps)
next
  case OverloadInStr
  then obtain w w' where "v = VLit (LitString w)" and "u = VLit (LitString w')"
    by (auto dest!: wf_str[OF _ SubtyRefl])
  with OverloadInStr.hyps(1) show ?case by (auto simp: binop_simps)
next
  case (OverloadInDict op \<sigma>\<^sub>1 \<tau>)
  then obtain w where "v = VLit (LitString w)" by (auto dest!: wf_str[OF _ SubtyRefl])
  moreover from OverloadInDict.prems(2) obtain \<delta> where "u = VDict \<delta>" by (auto elim: wf_dict)
  ultimately show ?case using OverloadInDict.hyps(1) by (auto simp: binop_simps)
next
  case OverloadOrderFloat
  then show ?case by (auto simp: binop_simps dest!: wf_float[OF _ SubtyRefl])
next
  case OverloadOrderStr
  then show ?case by (auto simp: binop_simps dest!: wf_str[OF _ SubtyRefl])
next
  case OverloadArithInt
  then show ?case by (auto simp: binop_simps dest!: wf_int[OF _ SubtyRefl])
next
  case OverloadArithFloat
  then show ?case by (auto simp: binop_simps dest!: wf_float[OF _ SubtyRefl])
next
  case OverloadPowFloat
  then show ?case by (auto simp: binop_simps dest!: wf_float[OF _ SubtyRefl] wf_int[OF _ SubtyRefl])
next
  case OverloadAddStr
  then show ?case by (auto simp: binop_simps dest!: wf_str[OF _ SubtyRefl])
next
  case (OverloadAddList \<sigma> \<tau>)
  from OverloadAddList.prems(1) obtain vs where v: "v = VList vs" and vs: "\<forall>v' \<in> set vs. \<turnstile> v' : Ty (inst \<eta> \<sigma>)"
    by (auto elim: wf_list)
  from OverloadAddList.prems(2) obtain us where u: "u = VList us" and us: "\<forall>u' \<in> set us. \<turnstile> u' : Ty (inst \<eta> \<tau>)"
    by (auto elim: wf_list)
  have wf: "wf_ty \<Sigma> (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)"
    using wf_val_ty[OF OverloadAddList.prems(1)] wf_val_ty[OF OverloadAddList.prems(2)]
    by (auto intro: join_wf wf_ty_inst_inv)
  have "\<forall>v' \<in> set (vs @ us). \<turnstile> v' : Ty (inst \<eta> (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>))"
    using vs us OverloadAddList.prems(3)
    by (auto intro: wf_val_inst_sub[OF _ join_upper(1) wf] wf_val_inst_sub[OF _ join_upper(2) wf])
  then have "\<turnstile> VList (vs @ us) : Ty (TyList (inst \<eta> (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)))"
    by (rule wf_val_list) (rule inst_wf[OF OverloadAddList.prems(3) wf])
  with v u show ?case by (simp add: binop_simps)
next
  case (OverloadAddTuple \<sigma>s \<tau>s)
  from OverloadAddTuple.prems(1) obtain vs where v: "v = VTuple vs"
    and vs: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs (map (inst \<eta>) \<sigma>s)"
    by (auto elim: wf_tuple)
  from OverloadAddTuple.prems(2) obtain us where u: "u = VTuple us"
    and us: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) us (map (inst \<eta>) \<tau>s)"
    by (auto elim: wf_tuple)
  have "\<turnstile> VTuple (vs @ us) : Ty (TyTuple (map (inst \<eta>) \<sigma>s @ map (inst \<eta>) \<tau>s))"
    by (rule wf_val_tuple[OF list_all2_appendI[OF vs us]])
  with v u show ?case by (simp add: binop_simps)
next
  case OverloadMulStrInt
  then show ?case by (auto simp: binop_simps dest!: wf_str[OF _ SubtyRefl] wf_int[OF _ SubtyRefl])
next
  case OverloadMulIntStr
  then show ?case by (auto simp: binop_simps dest!: wf_str[OF _ SubtyRefl] wf_int[OF _ SubtyRefl])
next
  case (OverloadMulListInt \<sigma>\<^sub>2 \<tau>)
  from OverloadMulListInt.prems(1) obtain vs where v: "v = VList vs"
    and vs: "\<forall>v' \<in> set vs. \<turnstile> v' : Ty (inst \<eta> \<tau>)"
    by (auto elim: wf_list)
  from OverloadMulListInt.prems(2) obtain n where u: "u = VLit (LitInt n)"
    by (auto dest!: wf_int[OF _ SubtyRefl])
  from vs wf_val_ty[OF OverloadMulListInt.prems(1)]
  have "\<turnstile> VList (concat (replicate (nat n) vs)) : Ty (TyList (inst \<eta> \<tau>))" by (auto intro!: wf_val_list)
  with v u show ?case by (simp add: binop_simps)
next
  case (OverloadMulIntList \<sigma>\<^sub>1 \<tau>)
  from OverloadMulIntList.prems(2) obtain us where u: "u = VList us"
    and us: "\<forall>u' \<in> set us. \<turnstile> u' : Ty (inst \<eta> \<tau>)"
    by (auto elim: wf_list)
  from OverloadMulIntList.prems(1) obtain n where v: "v = VLit (LitInt n)"
    by (auto dest!: wf_int[OF _ SubtyRefl])
  from us wf_val_ty[OF OverloadMulIntList.prems(2)]
  have "\<turnstile> VList (concat (replicate (nat n) us)) : Ty (TyList (inst \<eta> \<tau>))" by (auto intro!: wf_val_list)
  with v u show ?case by (simp add: binop_simps)
next
  case OverloadPowNat
  then show ?case by (auto simp: binop_simps dest!: wf_int[OF _ SubtyRefl] wf_lit)
next
  case OverloadPowNeg
  then show ?case by (auto simp: binop_simps dest!: wf_int[OF _ SubtyRefl] wf_lit)
next
  case OverloadBase
  then show ?case by simp
qed

(* Meaning of a binary operator at operands typed by the operand types, at the type given by operator resolution
   with elimination of unions *)
lemma binop_union_typed:
  "\<lbrakk> resolve_binop_union \<Sigma> op \<sigma> \<sigma>' = Some \<tau> ; \<turnstile> v : Ty (inst \<eta> \<sigma>) ; \<turnstile> u : Ty (inst \<eta> \<sigma>') ; wf_inst \<Sigma> \<eta> \<rbrakk>
  \<Longrightarrow> result_typed (binop_meaning op v u) (inst \<eta> \<tau>)"
proof (induction "size \<sigma> + size \<sigma>'" arbitrary: \<sigma> \<sigma>' \<tau> v u rule: less_induct)
  case less
  have wf: "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> \<sigma>'"
    using wf_val_ty[OF less.prems(2)] wf_val_ty[OF less.prems(3)] by (auto intro: wf_ty_inst_inv)
  from less.prems(1) show ?case
  proof (cases rule: resolve_binop_union_cases)
    case overload
    then obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where ov: "binop_overload \<Sigma> op \<sigma> \<sigma>' ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>)" by (rule resolve_binop_overload)
    from binop_overload_sub[OF ov] binop_overload_operands[OF ov wf] less.prems(2-4)
    have "\<turnstile> v : Ty (inst \<eta> \<tau>\<^sub>1)" and "\<turnstile> u : Ty (inst \<eta> \<tau>\<^sub>2)" by (auto intro: wf_val_inst_sub)
    with binop_meaning_typed[OF ov _ _ less.prems(4)] show ?thesis by simp
  next
    case (left \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
    have wf\<tau>: "wf_ty \<Sigma> (\<tau>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>2)" using resolve_binop_union_wf[OF wf less.prems(1)] left(4) by simp
    from less.prems(2) left(1) have "\<turnstile> v : Ty (inst \<eta> \<sigma>\<^sub>1) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>\<^sub>2)" by (auto dest: wf_val_union)
    then show ?thesis
    proof
      assume "\<turnstile> v : Ty (inst \<eta> \<sigma>\<^sub>1)"
      from less.hyps[OF _ left(2) this less.prems(3, 4)] left(1)
      have "result_typed (binop_meaning op v u) (inst \<eta> \<tau>\<^sub>1)" by simp
      from result_typed_sub[OF this join_upper(1) wf\<tau> less.prems(4)] left(4) show ?thesis by simp
    next
      assume "\<turnstile> v : Ty (inst \<eta> \<sigma>\<^sub>2)"
      from less.hyps[OF _ left(3) this less.prems(3, 4)] left(1)
      have "result_typed (binop_meaning op v u) (inst \<eta> \<tau>\<^sub>2)" by simp
      from result_typed_sub[OF this join_upper(2) wf\<tau> less.prems(4)] left(4) show ?thesis by simp
    qed
  next
    case (right \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
    have wf\<tau>: "wf_ty \<Sigma> (\<tau>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>2)" using resolve_binop_union_wf[OF wf less.prems(1)] right(4) by simp
    from less.prems(3) right(1) have "\<turnstile> u : Ty (inst \<eta> \<sigma>\<^sub>1) \<or> \<turnstile> u : Ty (inst \<eta> \<sigma>\<^sub>2)" by (auto dest: wf_val_union)
    then show ?thesis
    proof
      assume "\<turnstile> u : Ty (inst \<eta> \<sigma>\<^sub>1)"
      from less.hyps[OF _ right(2) less.prems(2) this less.prems(4)] right(1)
      have "result_typed (binop_meaning op v u) (inst \<eta> \<tau>\<^sub>1)" by simp
      from result_typed_sub[OF this join_upper(1) wf\<tau> less.prems(4)] right(4) show ?thesis by simp
    next
      assume "\<turnstile> u : Ty (inst \<eta> \<sigma>\<^sub>2)"
      from less.hyps[OF _ right(3) less.prems(2) this less.prems(4)] right(1)
      have "result_typed (binop_meaning op v u) (inst \<eta> \<tau>\<^sub>2)" by simp
      from result_typed_sub[OF this join_upper(2) wf\<tau> less.prems(4)] right(4) show ?thesis by simp
    qed
  qed
qed

lemma binop_sound:
  assumes e: "sound_expr \<rho> (node e) (Val v)" and e': "sound_expr \<rho> (node e') r"
  shows "sound_expr \<rho> (ExprBinOp op e e') (mlet r (binop_meaning op v))"
proof (rule sound_expr_synthI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprBinOp op e e') = Ok \<tau>"
  then obtain \<sigma> \<sigma>' where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and \<sigma>': "synth_expr_at \<Sigma> \<Gamma> e' = Ok \<sigma>'"
    and res: "resolve_binop_union \<Sigma> op \<sigma> \<sigma>' = Some \<tau>"
    by (auto simp: bind_sum_def or_else_def split: if_splits sum.splits option.splits)
  from sound_expr_synth_at[OF e env \<sigma>] have v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by simp
  from sound_expr_synth_at[OF e' env \<sigma>'] have r: "result_typed r (inst \<eta> \<sigma>')" .
  show "result_typed (mlet r (binop_meaning op v)) (inst \<eta> \<tau>)"
  proof (cases r)
    case (Val u)
    with r have "\<turnstile> u : Ty (inst \<eta> \<sigma>')" by simp
    from binop_union_typed[OF res v this wf_env_wf_inst[OF env]] Val show ?thesis by simp
  next
    case (Aborts \<kappa>)
    with r show ?thesis by simp
  qed
qed (simp_all add: var_scheme_None)

lemma binop_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprBinOp op e e') (Aborts \<kappa>)"
  by (rule sound_expr_synthI)
     (auto simp: bind_sum_def var_scheme_None dest: sound_expr_synth_at split: sum.splits)

lemma and_false_sound: "sound_expr \<rho> (node e) (Val false) \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Val false)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None intro: wf_lit_bool split: sum.splits)

lemma and_true_sound: "sound_expr \<rho> (node e') r \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') r"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest: prim_operand split: sum.splits)

lemma and_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Aborts \<kappa>)"
  by (rule sound_expr_synthI)
     (auto simp: bind_sum_def var_scheme_None dest: prim_operand split: sum.splits)

lemma and_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Aborts Excluded)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest!: bool_operand split: sum.splits)

lemma or_true_sound: "sound_expr \<rho> (node e) (Val true) \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Val true)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None intro: wf_lit_bool split: sum.splits)

lemma or_false_sound: "sound_expr \<rho> (node e') r \<Longrightarrow> sound_expr \<rho> (ExprOr e e') r"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest: prim_operand split: sum.splits)

lemma or_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Aborts \<kappa>)"
  by (rule sound_expr_synthI)
     (auto simp: bind_sum_def var_scheme_None dest: prim_operand split: sum.splits)

lemma or_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Aborts Excluded)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest!: bool_operand split: sum.splits)

(* Branches of a conditional typed at subtypes of its type *)
lemma cond_typed:
  assumes "typed_by_rule \<Sigma> \<Gamma> (ExprCond e1 e e2) \<tau>" and "wf_cxt \<Sigma> \<Gamma>"
  shows "\<exists>\<sigma>1 \<sigma>2. has_type_at \<Sigma> \<Gamma> e1 \<sigma>1 \<and> \<Sigma> \<turnstile> \<sigma>1 <: \<tau> \<and> has_type_at \<Sigma> \<Gamma> e2 \<sigma>2 \<and> \<Sigma> \<turnstile> \<sigma>2 <: \<tau>"
  using assms(1) unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprCond e1 e e2) = Ok \<tau>"
  then show ?thesis
  proof (cases rule: synth_cond)
    case (1 \<sigma>1 \<sigma>2)
    then show ?thesis by (blast intro: has_type_synth_at join_upper)
  next
    case 2
    with synth_at_wf_ty[OF assms(2) 2(1)] show ?thesis
      by (blast intro: has_type_synth_at has_type_check_at SubtyRefl)
  next
    case 3
    with synth_at_wf_ty[OF assms(2) 3(2)] show ?thesis
      by (blast intro: has_type_synth_at has_type_check_at SubtyRefl)
  qed
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprCond e1 e e2) \<tau> = Some (Ok ()) \<and> wf_ty \<Sigma> \<tau>"
  then show ?thesis by (auto simp: bind_sum_def intro: has_type_check_at SubtyRefl split: sum.splits)
qed

lemma cond_true_sound:
  assumes "sound_expr \<rho> (node e1) r"
  shows "sound_expr \<rho> (ExprCond e1 e e2) r"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprCond e1 e e2) \<tau>"
  from cond_typed[OF this(2) wf_env_wf_cxt[OF env]]
    typed_by_rule_wf[OF wf_env_wf_cxt[OF env] this(2)] wf_env_wf_inst[OF env]
  show "result_typed r (inst \<eta> \<tau>)" by (blast intro: result_typed_sub sound_expr_has_type_at[OF assms env])
qed simp_all

lemma cond_false_sound:
  assumes "sound_expr \<rho> (node e2) r"
  shows "sound_expr \<rho> (ExprCond e1 e e2) r"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprCond e1 e e2) \<tau>"
  from cond_typed[OF this(2) wf_env_wf_cxt[OF env]]
    typed_by_rule_wf[OF wf_env_wf_cxt[OF env] this(2)] wf_env_wf_inst[OF env]
  show "result_typed r (inst \<eta> \<tau>)" by (blast intro: result_typed_sub sound_expr_has_type_at[OF assms env])
qed simp_all

lemma cond_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) (Aborts \<kappa>)"
  by (rule sound_exprI) (auto simp: bind_sum_def dest: prim_operand split: sum.splits)

lemma cond_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) (Aborts Excluded)"
  by (rule sound_exprI) (auto simp: bind_sum_def dest!: bool_operand split: sum.splits)

(* Elements of a list synthesise subtypes of the join, or check against it *)
lemma elements_join_Ok:
  assumes "elements_join \<Sigma> \<Gamma> es = Ok \<tau>" and "wf_cxt \<Sigma> \<Gamma>"
  shows "\<exists>\<tau>s. list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>) es \<tau>s"
proof -
  let ?\<sigma>s = "map (synth_expr_at \<Sigma> \<Gamma>) es"
  from assms(1) have \<tau>: "\<tau> = joins \<Sigma> (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s))"
    and chk: "all_sum (map (\<lambda>(e, _). check_expr_at \<Sigma> \<Gamma> e \<tau>) (filter (isl \<circ> snd) (zip es ?\<sigma>s))) = Ok ()"
    by (auto simp: elements_join.simps Let_def bind_sum_def split: if_splits sum.splits)
  have synth: "wf_ty \<Sigma> (base_type (projr m))" if "m \<in> set ?\<sigma>s" and "\<not> isl m" for m
  proof -
    from that(1) obtain e where e: "e \<in> set es" and m: "m = synth_expr_at \<Sigma> \<Gamma> e" by auto
    with that(2) obtain \<sigma> where "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" by (cases "synth_expr_at \<Sigma> \<Gamma> e") auto
    with m synth_at_wf_ty[OF assms(2)] show ?thesis by (fastforce intro: base_type_wf)
  qed
  have wfs: "\<forall>\<tau>' \<in> set (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s)). wf_ty \<Sigma> \<tau>'" using synth by auto
  have wf: "wf_ty \<Sigma> \<tau>" unfolding \<tau> by (rule joins_wf[OF wfs])
  let ?\<tau> = "\<lambda>e. case synth_expr_at \<Sigma> \<Gamma> e of Ok \<sigma> \<Rightarrow> \<sigma> | Fail _ \<Rightarrow> \<tau>"
  have "has_type_at \<Sigma> \<Gamma> e (?\<tau> e) \<and> \<Sigma> \<turnstile> ?\<tau> e <: \<tau>" if "e \<in> set es" for e
  proof (cases "synth_expr_at \<Sigma> \<Gamma> e")
    case (Inl r)
    have "(e, Fail r) \<in> set (filter (isl \<circ> snd) (zip es ?\<sigma>s))"
      using that Inl by (auto simp: zip_map2 zip_same_conv_map)
    with chk have "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()" by (fastforce dest: all_sum_map_Ok)
    with Inl wf show ?thesis by (auto intro: has_type_check_at SubtyRefl)
  next
    case (Inr \<sigma>)
    then have "base_type \<sigma> \<in> set (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s))" using that by force
    then have bsub: "\<Sigma> \<turnstile> base_type \<sigma> <: \<tau>" unfolding \<tau> by (rule joins_upper[OF wfs])
    have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" by (rule synth_at_wf_ty[OF assms(2) Inr])
    have "\<Sigma> \<turnstile> \<sigma> <: \<tau>" by (rule subty_trans[OF wf_class_table wf\<sigma> base_type_wf[OF wf\<sigma>] base_type_upper bsub])
    with Inr show ?thesis by (auto intro: has_type_synth_at)
  qed
  then have "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>) es (map ?\<tau> es)"
    by (auto simp: list_all2_map2 intro: list.rel_refl_strong)
  then show ?thesis by blast
qed

(* Elements of a list synthesise subtypes of the element type, or check against it *)
lemma list_typed:
  assumes "typed_by_rule \<Sigma> \<Gamma> (ExprList es) \<tau>" and "wf_cxt \<Sigma> \<Gamma>"
  shows "\<exists>\<tau>' \<tau>s. \<tau> = TyList \<tau>' \<and> list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s"
  using assms(1) unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprList es) = Ok \<tau>"
  then obtain \<tau>' where "elements_join \<Sigma> \<Gamma> es = Ok \<tau>'" and "\<tau> = TyList \<tau>'"
    by (auto simp: bind_sum_def split: sum.splits if_splits)
  with elements_join_Ok[OF this(1) assms(2)] show ?thesis by blast
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprList es) \<tau> = Some (Ok ()) \<and> wf_ty \<Sigma> \<tau>"
  then obtain \<tau>' where \<tau>: "\<tau> = TyList \<tau>'" and "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e \<tau>') es) = Ok ()"
    and wf: "wf_ty \<Sigma> \<tau>'"
    by (auto split: ty.splits)
  then have "\<forall>e \<in> set es. check_expr_at \<Sigma> \<Gamma> e \<tau>' = Ok ()" by (auto dest: all_sum_map_Ok)
  with wf have "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es (replicate (length es) \<tau>')"
    by (auto simp: list_all2_conv_all_nth intro: has_type_check_at SubtyRefl)
  with \<tau> show ?thesis by blast
qed

lemma list_elems:
  assumes "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s" and "sound_exprs \<rho> es (Val vs)"
    and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "wf_ty \<Sigma> \<tau>'"
  shows "\<turnstile> VList vs : Ty (TyList (inst \<eta> \<tau>'))"
proof -
  from assms(1) have "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s" and sub: "\<forall>\<sigma> \<in> set \<tau>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    by (auto simp: list_all2_conv_all_nth in_set_conv_nth)
  with assms(2, 3) have vs: "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty (inst \<eta> \<sigma>)) vs \<tau>s"
    by (simp add: sound_exprs_def list_all2_map2)
  have "\<turnstile> v : Ty (inst \<eta> \<tau>')" if "v \<in> set vs" for v
  proof -
    from that obtain i where "i < length vs" and "v = vs ! i" by (auto simp: in_set_conv_nth)
    with vs have "\<turnstile> v : Ty (inst \<eta> (\<tau>s ! i))" and "\<tau>s ! i \<in> set \<tau>s" by (auto simp: list_all2_conv_all_nth)
    with sub assms(4) wf_env_wf_inst[OF assms(3)] show ?thesis by (blast intro: wf_val_inst_sub)
  qed
  then show ?thesis by (auto intro!: wf_val_list inst_wf[OF wf_env_wf_inst[OF assms(3)] assms(4)])
qed

lemma list_sound:
  assumes "sound_exprs \<rho> es (Val vs)"
  shows "sound_expr \<rho> (ExprList es) (Val (VList vs))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprList es) \<tau>"
  with list_typed[OF this(2) wf_env_wf_cxt[OF env]]
    typed_by_rule_wf[OF wf_env_wf_cxt[OF env] this(2)] assms
  show "result_typed (Val (VList vs)) (inst \<eta> \<tau>)" by (auto intro: list_elems)
qed simp_all

lemma list_fail_sound:
  assumes "sound_exprs \<rho> es (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprList es) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprList es) \<tau>"
  from list_typed[OF this(2) wf_env_wf_cxt[OF env]] obtain \<tau>' \<tau>s
    where "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s" by blast
  then have "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s" by (auto simp: list_all2_conv_all_nth)
  with assms env show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by (auto dest: sound_exprs_abort)
qed simp_all

(* Elements of a tuple synthesise or check against the components of its type *)
lemma tuple_typed:
  assumes "typed_by_rule \<Sigma> \<Gamma> (ExprTuple es) \<tau>"
  shows "\<exists>\<tau>s. \<tau> = TyTuple \<tau>s \<and> list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s"
  using assms unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprTuple es) = Ok \<tau>"
  then obtain \<tau>s where "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s" and "\<tau> = TyTuple \<tau>s"
    by (auto simp: bind_sum_def split: sum.splits)
  then show ?thesis by (auto dest!: those_sum_map_Ok intro: list_all2_mono has_type_synth_at)
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprTuple es) \<tau> = Some (Ok ()) \<and> wf_ty \<Sigma> \<tau>"
  then obtain \<tau>s where \<tau>: "\<tau> = TyTuple \<tau>s" and "length es = length \<tau>s"
    and "all_sum (map2 (check_expr_at \<Sigma> \<Gamma>) es \<tau>s) = Ok ()" and "\<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>'"
    by (auto split: ty.splits if_splits)
  then show ?thesis
    by (auto simp: list_all2_conv_all_nth dest!: all_sum_map2_Ok intro!: has_type_check_at)
qed

lemma tuple_sound:
  assumes "sound_exprs \<rho> es (Val vs)"
  shows "sound_expr \<rho> (ExprTuple es) (Val (VTuple vs))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprTuple es) \<tau>"
  with tuple_typed[OF this(2)] assms show "result_typed (Val (VTuple vs)) (inst \<eta> \<tau>)"
    by (auto simp: sound_exprs_def wf_val_tuple)
qed simp_all

lemma tuple_fail_sound:
  assumes "sound_exprs \<rho> es (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprTuple es) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprTuple es) \<tau>"
  with tuple_typed[OF this(2)] assms show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by (auto dest: sound_exprs_abort)
qed simp_all

(* Keys of a dictionary display check against str, and values synthesise subtypes of the value type, or check
   against it *)
lemma dict_typed:
  assumes "typed_by_rule \<Sigma> \<Gamma> (ExprDict kes) \<tau>" and "wf_cxt \<Sigma> \<Gamma>"
  shows "\<exists>\<tau>' \<sigma>s. \<tau> = TyDict \<tau>'
           \<and> list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
               kes \<sigma>s"
  using assms(1) unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprDict kes) = Ok \<tau>"
  then obtain \<tau>' where keys: "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e (TyPrim str)) (map fst kes)) = Ok ()"
    and "elements_join \<Sigma> \<Gamma> (map snd kes) = Ok \<tau>'" and \<tau>: "\<tau> = TyDict \<tau>'"
    by (auto simp: bind_sum_def split: sum.splits if_splits)
  from elements_join_Ok[OF this(2) assms(2)] obtain \<sigma>s
    where "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') (map snd kes) \<sigma>s" by blast
  then have "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') kes \<sigma>s"
    by (simp add: list_all2_map1 split_def)
  moreover from keys have "\<forall>(e, e') \<in> set kes. has_type_at \<Sigma> \<Gamma> e (TyPrim str)"
    by (fastforce dest: all_sum_map_Ok intro: has_type_check_at)
  ultimately have "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<Gamma> e' \<sigma>
                     \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') kes \<sigma>s"
    by (auto elim!: list.rel_mono_strong)
  with \<tau> show ?thesis by blast
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprDict kes) \<tau> = Some (Ok ()) \<and> wf_ty \<Sigma> \<tau>"
  then obtain \<tau>' where \<tau>: "\<tau> = TyDict \<tau>'" and wf: "wf_ty \<Sigma> \<tau>'"
    and keys: "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e (TyPrim str)) (map fst kes)) = Ok ()"
    and vals: "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e \<tau>') (map snd kes)) = Ok ()"
    by (auto simp: bind_sum_def split: ty.splits sum.splits)
  have "has_type_at \<Sigma> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<Gamma> e' \<tau>'" if "(e, e') \<in> set kes" for e e'
    using that keys vals wf by (fastforce dest: all_sum_map_Ok intro: has_type_check_at)
  then have "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
               kes (map (\<lambda>_. \<tau>') kes)"
    by (auto simp: list_all2_map2 intro!: list.rel_refl_strong intro: SubtyRefl)
  with \<tau> show ?thesis by blast
qed

(* Values of a typed dictionary display: string keys interleaved with values at subtypes of the value type *)
lemma dict_values_typed:
  assumes "typed_by_rule \<Sigma> \<Gamma> (ExprDict kes) \<tau>" and "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) r"
    and "\<eta> \<turnstile> \<rho> : \<Gamma>"
  obtains \<tau>' \<sigma>s where "\<tau> = TyDict \<tau>'" and "\<forall>\<sigma> \<in> set \<sigma>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and "results_typed r (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) (map (inst \<eta>) \<sigma>s)))"
proof -
  from dict_typed[OF assms(1) wf_env_wf_cxt[OF assms(3)]] obtain \<tau>' \<sigma>s
    where \<tau>: "\<tau> = TyDict \<tau>'"
    and kes: "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
                kes \<sigma>s"
    by blast
  from kes have "\<forall>\<sigma> \<in> set \<sigma>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'" by (induction rule: list_all2_induct) auto
  moreover from kes have "list_all2 (has_type_at \<Sigma> \<Gamma>) (concat (map (\<lambda>(e, e'). [e, e']) kes))
                            (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) \<sigma>s))"
    by (intro list_all2_interleave) (auto elim: list_all2_mono)
  with assms(2, 3) have "results_typed r (map (inst \<eta>) (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) \<sigma>s)))"
    by (simp add: sound_exprs_def)
  moreover have "map (inst \<eta>) (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) \<sigma>s))
                  = concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) (map (inst \<eta>) \<sigma>s))"
    by (induction \<sigma>s) simp_all
  ultimately show ?thesis using that \<tau> by metis
qed

(* Entries of the values of a dictionary display, from values at str for the keys *)
lemma dict_entries_typed:
  "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) vs (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) \<sigma>s))
  \<Longrightarrow> \<exists>\<delta>. dict_entries vs = Some \<delta> \<and> (\<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> (\<exists>\<sigma> \<in> set \<sigma>s. \<turnstile> v : Ty \<sigma>))"
proof (induction \<sigma>s arbitrary: vs)
  case (Cons \<sigma> \<sigma>s)
  then obtain u v vs' where vs: "vs = u # v # vs'" and "\<turnstile> u : Ty (TyPrim str)" and "\<turnstile> v : Ty \<sigma>"
    and "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) vs' (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) \<sigma>s))"
    by (auto simp: list_all2_Cons2)
  moreover from this(2) obtain w where "u = VLit (LitString w)" using wf_str[OF _ SubtyRefl] by blast
  ultimately show ?case using Cons.IH by fastforce
qed simp_all

lemma dict_sound:
  assumes "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Val vs)" and "dict_entries vs = Some \<delta>"
  shows "sound_expr \<rho> (ExprDict kes) (Val (VDict (update [] \<delta>)))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<Gamma> (ExprDict kes) \<tau>"
  then obtain \<tau>' \<sigma>s where \<tau>: "\<tau> = TyDict \<tau>'" and sub: "\<forall>\<sigma> \<in> set \<sigma>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and typed: "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) vs (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) (map (inst \<eta>) \<sigma>s)))"
    using assms(1) by (auto elim: dict_values_typed)
  have wf: "wf_ty \<Sigma> \<tau>'"
    using typed_by_rule_wf[OF wf_env_wf_cxt[OF env] \<open>typed_by_rule _ _ _ _\<close>] by (simp add: \<tau>)
  from dict_entries_typed[OF typed] assms(2) sub wf wf_env_wf_inst[OF env]
  have "\<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>')" by (fastforce intro: wf_val_inst_sub)
  then show "result_typed (Val (VDict (update [] \<delta>))) (inst \<eta> \<tau>)"
    by (simp add: \<tau> wf_dict_update inst_wf[OF wf_env_wf_inst[OF env] wf])
qed simp_all

lemma dict_fail_sound:
  "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprDict kes) (Aborts \<kappa>)"
  by (rule sound_expr_typedI) (auto elim: dict_values_typed)

lemma dict_nonstr_sound:
  assumes "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Val vs)" and "dict_entries vs = None"
  shows "sound_expr \<rho> (ExprDict kes) (Aborts Excluded)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "typed_by_rule \<Sigma> \<Gamma> (ExprDict kes) \<tau>"
  show "result_typed (Aborts Excluded) (inst \<eta> \<tau>)"
  proof (rule dict_values_typed[OF typed assms(1) env])
    fix \<tau>' \<sigma>s
    assume "\<tau> = TyDict \<tau>'" and "\<forall>\<sigma> \<in> set \<sigma>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
      and "results_typed (Val vs) (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) (map (inst \<eta>) \<sigma>s)))"
    from dict_entries_typed[OF this(3)[unfolded wf_result.simps(1)]] assms(2) show ?thesis by simp
  qed
qed simp_all

lemma exprs_nil_sound: "sound_exprs \<rho> [] (Val [])"
  by (simp add: sound_exprs_def)

lemma exprs_cons_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and "sound_exprs \<rho> es r"
  shows "sound_exprs \<rho> (e # es) (mlet r (\<lambda>vs. Val (v # vs)))"
  unfolding sound_exprs_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<tau>s
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "list_all2 (has_type_at \<Sigma> \<Gamma>) (e # es) \<tau>s"
  then obtain \<tau> \<tau>s' where \<tau>s: "\<tau>s = \<tau> # \<tau>s'" and e: "has_type_at \<Sigma> \<Gamma> e \<tau>"
    and es: "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s'"
    by (auto simp: list_all2_Cons1)
  from assms(1) env e have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_has_type_at)
  moreover from assms(2) env es have "results_typed r (map (inst \<eta>) \<tau>s')" by (simp add: sound_exprs_def)
  ultimately show "results_typed (mlet r (\<lambda>vs. Val (v # vs))) (map (inst \<eta>) \<tau>s)" by (cases r) (simp_all add: \<tau>s)
qed

lemma exprs_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_exprs \<rho> (e # es) (Aborts \<kappa>)"
  unfolding sound_exprs_def by (auto simp: list_all2_Cons1 dest: sound_expr_has_type_at)

end

end
