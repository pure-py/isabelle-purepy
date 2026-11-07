(* Soundness of evaluation of expressions other than calls *)
theory Expressions
  imports SoundExpr
begin

context evaluation
begin

subsection \<open>Expressions\<close>

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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr' \<Sigma> \<Gamma> (ExprVar x) \<tau> = Some (Ok ())" and fv: "fv \<tau> \<subseteq> fst ` set \<eta>"
  then obtain \<alpha>s \<sigma> \<tau>s where \<Gamma>x: "fmlookup \<Gamma> x = Some (Scheme (TyScheme \<alpha>s \<sigma>))"
    and \<tau>s: "Subtyping.type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s"
    and sub: "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: \<tau>"
    by (auto simp: var_scheme_def scheme_of_name_def entry_of_def resolve_name_def bind_sum_def ensure_def
        Let_def split: option.splits cxt_entry.splits ty_scheme.splits if_splits sum.splits)
  let ?\<eta>' = "filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>"
  from env \<Gamma>x assms(1) have v: "\<turnstile> v : Scheme (TyScheme \<alpha>s (inst ?\<eta>' \<sigma>))" by (auto dest!: wf_env_lookup)
  have len: "length \<tau>s = length \<alpha>s" using \<tau>s by (rule type_args_of_length)
  have closed: "\<forall>\<tau>' \<in> set (map (inst \<eta>) \<tau>s). fv \<tau>' = {}"
    using type_args_fv[OF \<tau>s] fv wf_env_closed[OF env] by (auto intro!: inst_closed)
  have "length (map (inst \<eta>) \<tau>s) = length \<alpha>s" by (simp add: len)
  from v this closed have "\<turnstile> v : Ty (subst (map (inst \<eta>) \<tau>s) \<alpha>s (inst ?\<eta>' \<sigma>))" by (rule ValInst)
  then have "\<turnstile> v : Ty (inst \<eta> (subst \<tau>s \<alpha>s \<sigma>))" by (simp only: inst_subst[OF wf_env_closed[OF env] len])
  then show "result_typed (Val v) (inst \<eta> \<tau>)" using sub by (auto intro: wf_val_inst_sub)
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
      split: option.splits cxt_entry.splits dest!: wf_env_lookup wf_unbound_ty wf_unbound_scheme wf_unbound(1))

lemma literal_sound: "sound_expr \<rho> (ExprLiteral l) (Val (VLit l))"
  by (rule sound_expr_synthI) (auto simp: var_scheme_None intro: ValLit ValLitFloat split: lit.splits)

lemma lambda_sound: "sound_expr \<rho> (ExprLambda xs e) (Val Lam(\<rho>, xs, e))"
  by (rule sound_exprI)
     (auto simp: bind_sum_def intro!: ValLambda[simplified] split: ty.splits if_splits sum.splits)

lemma unop_overload_sub: "unop_overload \<Sigma> op \<sigma> \<omega> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: fst \<omega>"
proof (induction rule: unop_overload.induct)
  case (UnopOverloadBase \<sigma> op \<tau> \<tau>')
  then show ?case using subty_trans'[OF base_type_upper] by simp
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
    from assms(1) num obtain l where v: "v = VLit l" and l: "prim_subtype (case \<tau> of TyPrim p \<Rightarrow> p) (TyLiteral l)"
      by (auto elim!: wf_prim_lit[OF _ SubtyRefl])
    from l num obtain n x where "l = LitInt n \<or> \<tau> = TyPrim float \<and> l = LitFloat x"
      by (cases l) auto
    then show ?thesis
    proof
      assume "l = LitInt n"
      moreover have "\<Sigma> \<turnstile> TyLiteral (LitInt n) <: TyPrim float"
        by (rule SubtyLiteral) (simp add: SubtyIntFloat)
      moreover have "\<turnstile> VLit (LitInt (- n)) : Ty \<tau>'" using num wf_int_lit by (auto intro: ValSub SubtyIntFloat)
      ultimately show ?thesis using num assms(1) v \<open>\<tau> = \<tau>'\<close> by auto
    next
      assume "\<tau> = TyPrim float \<and> l = LitFloat x"
      with num assms(1) v \<open>\<tau> = \<tau>'\<close> show ?thesis by (auto intro: ValLitFloat SubtyRefl)
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
    from wf_val_inst_sub[OF this unop_overload_sub[OF ov]] closed have "\<turnstile> v : Ty \<tau>''" by (simp add: subst_closed)
    from unop_meaning_typed[OF this ov] Val closed show ?thesis by (simp add: subst_closed)
  next
    case (Aborts \<kappa>)
    with r show ?thesis by simp
  qed
qed (simp_all add: var_scheme_None)

lemma binop_overload_sub: "binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: fst (fst \<omega>) \<and> \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: snd (fst \<omega>)"
proof (induction rule: binop_overload.induct)
  case OverloadBase
  then show ?case using subty_trans'[OF base_type_upper] by simp
qed (auto intro: SubtyRefl)

lemmas binop_simps = binop_meaning_def overload_def tuple_overload_def subty_prim_iff subty_list_iff SubtyRefl
  SubtyObject compare_numbers_def compare_strings_def int_arith_def int_division_def int_quotient_def
  float_arith_def float_division_def float_operands_def float_of_def float_power_def int_power_def concat_str_def
  concat_list_def concat_tuple_def repeat_str_def repeat_list_def Let_def wf_int_lit wf_int_float ValLitFloat
  wf_lit_bool wf_str_char

(* Meaning of a binary operator at operands typed by the operand types of an overload *)
lemma binop_meaning_typed:
  "\<lbrakk> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega> ; \<turnstile> v : Ty (inst \<eta> (fst (fst \<omega>))) ; \<turnstile> u : Ty (inst \<eta> (snd (fst \<omega>))) \<rbrakk>
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
  have "\<forall>v' \<in> set (vs @ us). \<turnstile> v' : Ty (inst \<eta> (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>))"
    using vs us by (auto intro: wf_val_inst_sub[OF _ join_upper(1)] wf_val_inst_sub[OF _ join_upper(2)])
  then have "\<turnstile> VList (vs @ us) : Ty (TyList (inst \<eta> (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)))" by (rule ValList)
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
    by (rule ValTuple[OF list_all2_appendI[OF vs us]])
  with v u show ?case by (simp add: binop_simps)
next
  case OverloadMulStrInt
  then show ?case by (auto simp: binop_simps dest!: wf_str[OF _ SubtyRefl] wf_int[OF _ SubtyRefl])
next
  case OverloadMulIntStr
  then show ?case by (auto simp: binop_simps dest!: wf_str[OF _ SubtyRefl] wf_int[OF _ SubtyRefl])
next
  case (OverloadMulListInt \<sigma>\<^sub>2 \<tau>)
  from OverloadMulListInt.prems(1) obtain vs where v: "v = VList vs" and vs: "\<forall>v' \<in> set vs. \<turnstile> v' : Ty (inst \<eta> \<tau>)"
    by (auto elim: wf_list)
  from OverloadMulListInt.prems(2) obtain n where u: "u = VLit (LitInt n)" by (auto dest!: wf_int[OF _ SubtyRefl])
  from vs have "\<turnstile> VList (concat (replicate (nat n) vs)) : Ty (TyList (inst \<eta> \<tau>))" by (auto intro!: ValList)
  with v u show ?case by (simp add: binop_simps)
next
  case (OverloadMulIntList \<sigma>\<^sub>1 \<tau>)
  from OverloadMulIntList.prems(2) obtain us where u: "u = VList us" and us: "\<forall>u' \<in> set us. \<turnstile> u' : Ty (inst \<eta> \<tau>)"
    by (auto elim: wf_list)
  from OverloadMulIntList.prems(1) obtain n where v: "v = VLit (LitInt n)" by (auto dest!: wf_int[OF _ SubtyRefl])
  from us have "\<turnstile> VList (concat (replicate (nat n) us)) : Ty (TyList (inst \<eta> \<tau>))" by (auto intro!: ValList)
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
  "\<lbrakk> resolve_binop_union \<Sigma> op \<sigma> \<sigma>' = Some \<tau> ; \<turnstile> v : Ty (inst \<eta> \<sigma>) ; \<turnstile> u : Ty (inst \<eta> \<sigma>') \<rbrakk>
  \<Longrightarrow> result_typed (binop_meaning op v u) (inst \<eta> \<tau>)"
proof (induction "size \<sigma> + size \<sigma>'" arbitrary: \<sigma> \<sigma>' \<tau> v u rule: less_induct)
  case less
  from less.prems(1) show ?case
  proof (cases rule: resolve_binop_union_cases)
    case overload
    then obtain \<tau>\<^sub>1 \<tau>\<^sub>2 where ov: "binop_overload \<Sigma> op \<sigma> \<sigma>' ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>)" by (rule resolve_binop_overload)
    from binop_overload_sub[OF ov] less.prems(2, 3) have "\<turnstile> v : Ty (inst \<eta> \<tau>\<^sub>1)" and "\<turnstile> u : Ty (inst \<eta> \<tau>\<^sub>2)"
      by (auto intro: wf_val_inst_sub)
    with binop_meaning_typed[OF ov] show ?thesis by simp
  next
    case (left \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
    from less.prems(2) left(1) have "\<turnstile> v : Ty (inst \<eta> \<sigma>\<^sub>1) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>\<^sub>2)" by (auto dest: wf_val_union)
    then show ?thesis
    proof
      assume "\<turnstile> v : Ty (inst \<eta> \<sigma>\<^sub>1)"
      from less.hyps[OF _ left(2) this less.prems(3)] left(1)
      have "result_typed (binop_meaning op v u) (inst \<eta> \<tau>\<^sub>1)" by simp
      from result_typed_sub[OF this join_upper(1)] left(4) show ?thesis by simp
    next
      assume "\<turnstile> v : Ty (inst \<eta> \<sigma>\<^sub>2)"
      from less.hyps[OF _ left(3) this less.prems(3)] left(1)
      have "result_typed (binop_meaning op v u) (inst \<eta> \<tau>\<^sub>2)" by simp
      from result_typed_sub[OF this join_upper(2)] left(4) show ?thesis by simp
    qed
  next
    case (right \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2)
    from less.prems(3) right(1) have "\<turnstile> u : Ty (inst \<eta> \<sigma>\<^sub>1) \<or> \<turnstile> u : Ty (inst \<eta> \<sigma>\<^sub>2)" by (auto dest: wf_val_union)
    then show ?thesis
    proof
      assume "\<turnstile> u : Ty (inst \<eta> \<sigma>\<^sub>1)"
      from less.hyps[OF _ right(2) less.prems(2) this] right(1)
      have "result_typed (binop_meaning op v u) (inst \<eta> \<tau>\<^sub>1)" by simp
      from result_typed_sub[OF this join_upper(1)] right(4) show ?thesis by simp
    next
      assume "\<turnstile> u : Ty (inst \<eta> \<sigma>\<^sub>2)"
      from less.hyps[OF _ right(3) less.prems(2) this] right(1)
      have "result_typed (binop_meaning op v u) (inst \<eta> \<tau>\<^sub>2)" by simp
      from result_typed_sub[OF this join_upper(2)] right(4) show ?thesis by simp
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
    from binop_union_typed[OF res v this] Val show ?thesis by simp
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

lemma and_true_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val true) ; sound_expr \<rho> (node e') r \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') r"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest: prim_operand split: sum.splits)

lemma and_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Aborts \<kappa>)"
  by (rule sound_expr_synthI)
     (auto simp: bind_sum_def var_scheme_None dest: prim_operand split: sum.splits)

lemma and_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Aborts Excluded)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest!: bool_operand split: sum.splits)

lemma or_true_sound: "sound_expr \<rho> (node e) (Val true) \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Val true)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None intro: wf_lit_bool split: sum.splits)

lemma or_false_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val false) ; sound_expr \<rho> (node e') r \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprOr e e') r"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest: prim_operand split: sum.splits)

lemma or_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Aborts \<kappa>)"
  by (rule sound_expr_synthI)
     (auto simp: bind_sum_def var_scheme_None dest: prim_operand split: sum.splits)

lemma or_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Aborts Excluded)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest!: bool_operand split: sum.splits)

(* Branches of a conditional typed at subtypes of its type *)
lemma cond_typed:
  assumes "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprCond e1 e e2) \<tau>" and "tyvars \<Gamma> \<subseteq> fst ` set \<eta>"
  shows "\<exists>\<sigma>1 \<sigma>2. has_type_at \<Sigma> \<eta> \<Gamma> e1 \<sigma>1 \<and> \<Sigma> \<turnstile> \<sigma>1 <: \<tau> \<and> has_type_at \<Sigma> \<eta> \<Gamma> e2 \<sigma>2 \<and> \<Sigma> \<turnstile> \<sigma>2 <: \<tau>"
  using assms(1) unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprCond e1 e e2) = Ok \<tau>"
  then show ?thesis
  proof (cases rule: synth_cond)
    case (1 \<sigma>1 \<sigma>2)
    then show ?thesis by (blast intro: has_type_synth_at join_upper)
  next
    case 2
    with synth_at_tyvars[OF 2(1)] assms(2) show ?thesis
      by (blast intro: has_type_synth_at has_type_check_at SubtyRefl subset_trans)
  next
    case 3
    with synth_at_tyvars[OF 3(2)] assms(2) show ?thesis
      by (blast intro: has_type_synth_at has_type_check_at SubtyRefl subset_trans)
  qed
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprCond e1 e e2) \<tau> = Some (Ok ()) \<and> fv \<tau> \<subseteq> fst ` set \<eta>"
  then show ?thesis by (auto simp: bind_sum_def intro: has_type_check_at SubtyRefl split: sum.splits)
qed

lemma cond_true_sound:
  assumes "sound_expr \<rho> (node e) (Val true)" and "sound_expr \<rho> (node e1) r"
  shows "sound_expr \<rho> (ExprCond e1 e e2) r"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprCond e1 e e2) \<tau>"
  from cond_typed[OF this(2) wf_env_tyvars[OF env]] show "result_typed r (inst \<eta> \<tau>)"
    by (blast intro: result_typed_sub sound_expr_has_type_at[OF assms(2) env])
qed simp_all

lemma cond_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_expr \<rho> (node e2) r"
  shows "sound_expr \<rho> (ExprCond e1 e e2) r"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprCond e1 e e2) \<tau>"
  from cond_typed[OF this(2) wf_env_tyvars[OF env]] show "result_typed r (inst \<eta> \<tau>)"
    by (blast intro: result_typed_sub sound_expr_has_type_at[OF assms(2) env])
qed simp_all

lemma cond_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) (Aborts \<kappa>)"
  by (rule sound_exprI) (auto simp: bind_sum_def dest: prim_operand split: sum.splits)

lemma cond_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) (Aborts Excluded)"
  by (rule sound_exprI) (auto simp: bind_sum_def dest!: bool_operand split: sum.splits)

(* Elements of a list synthesise subtypes of the join, or check against it *)
lemma elements_join_Ok:
  assumes "elements_join \<Sigma> \<Gamma> es = Ok \<tau>" and "tyvars \<Gamma> \<subseteq> fst ` set \<eta>"
  shows "\<exists>\<tau>s. list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>) es \<tau>s"
proof -
  let ?\<sigma>s = "map (synth_expr_at \<Sigma> \<Gamma>) es"
  from assms(1) have \<tau>: "\<tau> = joins \<Sigma> (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s))"
    and chk: "all_sum (map (\<lambda>(e, _). check_expr_at \<Sigma> \<Gamma> e \<tau>) (filter (isl \<circ> snd) (zip es ?\<sigma>s))) = Ok ()"
    by (auto simp: elements_join.simps Let_def bind_sum_def split: if_splits sum.splits)
  have fv: "fv \<tau> \<subseteq> fst ` set \<eta>"
  proof -
    have "fv (base_type (projr m)) \<subseteq> fst ` set \<eta>" if "m \<in> set ?\<sigma>s" and "\<not> isl m" for m
    proof -
      from that(1) obtain e where e: "e \<in> set es" and m: "m = synth_expr_at \<Sigma> \<Gamma> e" by auto
      with that(2) obtain \<sigma> where "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" by (cases "synth_expr_at \<Sigma> \<Gamma> e") auto
      with m synth_at_tyvars assms(2) show ?thesis by fastforce
    qed
    then have "\<Union> (fv ` set (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s))) \<subseteq> fst ` set \<eta>" by auto
    then show ?thesis unfolding \<tau> by (rule subset_trans[OF fv_joins])
  qed
  let ?\<tau> = "\<lambda>e. case synth_expr_at \<Sigma> \<Gamma> e of Ok \<sigma> \<Rightarrow> \<sigma> | Fail _ \<Rightarrow> \<tau>"
  have "has_type_at \<Sigma> \<eta> \<Gamma> e (?\<tau> e) \<and> \<Sigma> \<turnstile> ?\<tau> e <: \<tau>" if "e \<in> set es" for e
  proof (cases "synth_expr_at \<Sigma> \<Gamma> e")
    case (Inl r)
    have "(e, Fail r) \<in> set (filter (isl \<circ> snd) (zip es ?\<sigma>s))"
      using that Inl by (auto simp: zip_map2 zip_same_conv_map)
    with chk have "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()" by (fastforce dest: all_sum_map_Ok)
    with Inl fv show ?thesis by (auto intro: has_type_check_at SubtyRefl)
  next
    case (Inr \<sigma>)
    then have "base_type \<sigma> \<in> set (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s))" using that by force
    then have "\<Sigma> \<turnstile> \<sigma> <: \<tau>" unfolding \<tau> by (blast intro: base_type_upper joins_upper subty_trans')
    with Inr show ?thesis by (auto intro: has_type_synth_at)
  qed
  then have "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>) es (map ?\<tau> es)"
    by (auto simp: list_all2_map2 intro: list.rel_refl_strong)
  then show ?thesis by blast
qed

(* Elements of a list synthesise subtypes of the element type, or check against it *)
lemma list_typed:
  assumes "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprList es) \<tau>" and "tyvars \<Gamma> \<subseteq> fst ` set \<eta>"
  shows "\<exists>\<tau>' \<tau>s. \<tau> = TyList \<tau>' \<and> list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s"
  using assms(1) unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprList es) = Ok \<tau>"
  then obtain \<tau>' where "elements_join \<Sigma> \<Gamma> es = Ok \<tau>'" and "\<tau> = TyList \<tau>'"
    by (auto simp: bind_sum_def split: sum.splits if_splits)
  with elements_join_Ok[OF this(1) assms(2)] show ?thesis by blast
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprList es) \<tau> = Some (Ok ()) \<and> fv \<tau> \<subseteq> fst ` set \<eta>"
  then obtain \<tau>' where \<tau>: "\<tau> = TyList \<tau>'" and "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e \<tau>') es) = Ok ()"
    and fv: "fv \<tau>' \<subseteq> fst ` set \<eta>"
    by (auto split: ty.splits)
  then have "\<forall>e \<in> set es. check_expr_at \<Sigma> \<Gamma> e \<tau>' = Ok ()" by (auto dest: all_sum_map_Ok)
  with fv have "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es (replicate (length es) \<tau>')"
    by (auto simp: list_all2_conv_all_nth intro: has_type_check_at SubtyRefl)
  with \<tau> show ?thesis by blast
qed

lemma list_elems:
  assumes "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s" and "sound_exprs \<rho> es (Val vs)"
    and "\<eta> \<turnstile> \<rho> : \<Gamma>"
  shows "\<turnstile> VList vs : Ty (TyList (inst \<eta> \<tau>'))"
proof -
  from assms(1) have "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s" and sub: "\<forall>\<sigma> \<in> set \<tau>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    by (auto simp: list_all2_conv_all_nth in_set_conv_nth)
  with assms(2, 3) have vs: "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty (inst \<eta> \<sigma>)) vs \<tau>s"
    by (simp add: sound_exprs_def list_all2_map2)
  have "\<turnstile> v : Ty (inst \<eta> \<tau>')" if "v \<in> set vs" for v
  proof -
    from that obtain i where "i < length vs" and "v = vs ! i" by (auto simp: in_set_conv_nth)
    with vs have "\<turnstile> v : Ty (inst \<eta> (\<tau>s ! i))" and "\<tau>s ! i \<in> set \<tau>s" by (auto simp: list_all2_conv_all_nth)
    with sub show ?thesis by (blast intro: wf_val_inst_sub)
  qed
  then show ?thesis by (auto intro!: ValList)
qed

lemma list_sound:
  assumes "sound_exprs \<rho> es (Val vs)"
  shows "sound_expr \<rho> (ExprList es) (Val (VList vs))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprList es) \<tau>"
  with list_typed[OF this(2) wf_env_tyvars[OF env]] assms show "result_typed (Val (VList vs)) (inst \<eta> \<tau>)"
    by (auto intro: list_elems)
qed simp_all

lemma list_fail_sound:
  assumes "sound_exprs \<rho> es (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprList es) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprList es) \<tau>"
  from list_typed[OF this(2) wf_env_tyvars[OF env]] obtain \<tau>' \<tau>s
    where "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s" by blast
  then have "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s" by (auto simp: list_all2_conv_all_nth)
  with assms env show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by (auto dest: sound_exprs_abort)
qed simp_all

(* Elements of a tuple synthesise or check against the components of its type *)
lemma tuple_typed:
  assumes "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprTuple es) \<tau>"
  shows "\<exists>\<tau>s. \<tau> = TyTuple \<tau>s \<and> list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s"
  using assms unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprTuple es) = Ok \<tau>"
  then obtain \<tau>s where "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s" and "\<tau> = TyTuple \<tau>s"
    by (auto simp: bind_sum_def split: sum.splits)
  then show ?thesis by (auto dest!: those_sum_map_Ok intro: list_all2_mono has_type_synth_at)
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprTuple es) \<tau> = Some (Ok ()) \<and> fv \<tau> \<subseteq> fst ` set \<eta>"
  then obtain \<tau>s where \<tau>: "\<tau> = TyTuple \<tau>s" and "length es = length \<tau>s"
    and "all_sum (map2 (check_expr_at \<Sigma> \<Gamma>) es \<tau>s) = Ok ()" and "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fst ` set \<eta>"
    by (auto split: ty.splits if_splits)
  then show ?thesis
    by (auto simp: list_all2_conv_all_nth dest!: all_sum_map2_Ok intro!: has_type_check_at)
qed

lemma tuple_sound:
  assumes "sound_exprs \<rho> es (Val vs)"
  shows "sound_expr \<rho> (ExprTuple es) (Val (VTuple vs))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprTuple es) \<tau>"
  with tuple_typed[OF this(2)] assms show "result_typed (Val (VTuple vs)) (inst \<eta> \<tau>)"
    by (auto simp: sound_exprs_def ValTuple)
qed simp_all

lemma tuple_fail_sound:
  assumes "sound_exprs \<rho> es (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprTuple es) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprTuple es) \<tau>"
  with tuple_typed[OF this(2)] assms show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by (auto dest: sound_exprs_abort)
qed simp_all

(* Keys of a dictionary display check against str, and values synthesise subtypes of the value type, or check
   against it *)
lemma dict_typed:
  assumes "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDict kes) \<tau>" and "tyvars \<Gamma> \<subseteq> fst ` set \<eta>"
  shows "\<exists>\<tau>' \<sigma>s. \<tau> = TyDict \<tau>'
           \<and> list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<eta> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
               kes \<sigma>s"
  using assms(1) unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprDict kes) = Ok \<tau>"
  then obtain \<tau>' where keys: "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e (TyPrim str)) (map fst kes)) = Ok ()"
    and "elements_join \<Sigma> \<Gamma> (map snd kes) = Ok \<tau>'" and \<tau>: "\<tau> = TyDict \<tau>'"
    by (auto simp: bind_sum_def split: sum.splits if_splits)
  from elements_join_Ok[OF this(2) assms(2)] obtain \<sigma>s
    where "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') (map snd kes) \<sigma>s" by blast
  then have "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') kes \<sigma>s"
    by (simp add: list_all2_map1 split_def)
  moreover from keys have "\<forall>(e, e') \<in> set kes. has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str)"
    by (fastforce dest: all_sum_map_Ok intro: has_type_check_at)
  ultimately have "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<eta> \<Gamma> e' \<sigma>
                     \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') kes \<sigma>s"
    by (auto elim!: list.rel_mono_strong)
  with \<tau> show ?thesis by blast
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprDict kes) \<tau> = Some (Ok ()) \<and> fv \<tau> \<subseteq> fst ` set \<eta>"
  then obtain \<tau>' where \<tau>: "\<tau> = TyDict \<tau>'" and fv: "fv \<tau>' \<subseteq> fst ` set \<eta>"
    and keys: "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e (TyPrim str)) (map fst kes)) = Ok ()"
    and vals: "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e \<tau>') (map snd kes)) = Ok ()"
    by (auto simp: bind_sum_def split: ty.splits sum.splits)
  have "has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<eta> \<Gamma> e' \<tau>'" if "(e, e') \<in> set kes" for e e'
    using that keys vals fv by (fastforce dest: all_sum_map_Ok intro: has_type_check_at)
  then have "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<eta> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
               kes (map (\<lambda>_. \<tau>') kes)"
    by (auto simp: list_all2_map2 intro!: list.rel_refl_strong intro: SubtyRefl)
  with \<tau> show ?thesis by blast
qed

(* Values of a typed dictionary display: string keys interleaved with values at subtypes of the value type *)
lemma dict_values_typed:
  assumes "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDict kes) \<tau>" and "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) r"
    and "\<eta> \<turnstile> \<rho> : \<Gamma>"
  obtains \<tau>' \<sigma>s where "\<tau> = TyDict \<tau>'" and "\<forall>\<sigma> \<in> set \<sigma>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and "results_typed r (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) (map (inst \<eta>) \<sigma>s)))"
proof -
  from dict_typed[OF assms(1) wf_env_tyvars[OF assms(3)]] obtain \<tau>' \<sigma>s where \<tau>: "\<tau> = TyDict \<tau>'"
    and kes: "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<eta> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
                kes \<sigma>s"
    by blast
  from kes have "\<forall>\<sigma> \<in> set \<sigma>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'" by (induction rule: list_all2_induct) auto
  moreover from kes have "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) (concat (map (\<lambda>(e, e'). [e, e']) kes))
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDict kes) \<tau>"
  then obtain \<tau>' \<sigma>s where \<tau>: "\<tau> = TyDict \<tau>'" and sub: "\<forall>\<sigma> \<in> set \<sigma>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) vs (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) (map (inst \<eta>) \<sigma>s)))"
    using assms(1) by (auto elim: dict_values_typed)
  from dict_entries_typed[OF this(3)] assms(2) sub
  have "\<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>')" by (fastforce intro: wf_val_inst_sub)
  then show "result_typed (Val (VDict (update [] \<delta>))) (inst \<eta> \<tau>)" by (simp add: \<tau> wf_dict_update)
qed simp_all

lemma dict_fail_sound:
  "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprDict kes) (Aborts \<kappa>)"
  by (rule sound_expr_typedI) (auto elim: dict_values_typed)

lemma dict_nonstr_sound:
  assumes "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Val vs)" and "dict_entries vs = None"
  shows "sound_expr \<rho> (ExprDict kes) (Aborts Excluded)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDict kes) \<tau>"
  show "result_typed (Aborts Excluded) (inst \<eta> \<tau>)"
  proof (rule dict_values_typed[OF typed assms(1) env])
    fix \<tau>' \<sigma>s
    assume "\<tau> = TyDict \<tau>'" and "\<forall>\<sigma> \<in> set \<sigma>s. \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
      and "results_typed (Val vs) (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) (map (inst \<eta>) \<sigma>s)))"
    from dict_entries_typed[OF this(3)[unfolded wf_result.simps(1)]] assms(2) show ?thesis by simp
  qed
qed simp_all

lemma wf_dict_entries:
  assumes "\<turnstile> v : Ty (TyDict \<tau>)"
  obtains \<delta> where "v = VDict \<delta>" and "\<forall>w u. (w, u) \<in> set \<delta> \<longrightarrow> \<turnstile> u : Ty \<tau>"
proof -
  from wf_val_intro(1)[OF assms] obtain \<sigma> where intro: "intro_typed v \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: TyDict \<tau>"
    by blast
  from subty_dict_inv(1)[OF sub refl] intro_typed_nonunion[OF intro] obtain \<sigma>' where \<sigma>: "\<sigma> = TyDict \<sigma>'"
    and sub': "\<Sigma> \<turnstile> \<sigma>' <: \<tau>"
    by blast
  from intro \<sigma> obtain \<delta> where v: "v = VDict \<delta>" and "\<forall>w u. (w, u) \<in> set \<delta> \<longrightarrow> \<turnstile> u : Ty \<sigma>'"
    by (cases v) auto
  with sub' that show thesis by (blast intro: ValSub)
qed

(* Element at an integer index of a sequence with elements satisfying P, or an index error *)
lemma getitem_elems:
  assumes "elems v = Some vs" and "\<forall>u \<in> set vs. P u"
  shows "wf_result P (getitem v (VLit (LitInt n)))"
  using assms by (cases v rule: elems.cases) (auto simp: Let_def nat_less_iff)

(* String, as a sequence of strings *)
lemma str_elems: "\<exists>vs. elems (VLit (LitString w)) = Some vs \<and> (\<forall>u \<in> set vs. \<turnstile> u : Ty (TyPrim str))"
  by (auto intro: wf_str_char)

(* Subscript of a value typed at a type with base type str *)
lemma subscript_str:
  assumes "base_type \<sigma> = TyPrim str" and "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    and "wf_result (\<lambda>u. \<exists>n. u = VLit (LitInt n)) r"
  shows "result_typed (mlet r (getitem v)) (TyPrim str)"
proof -
  have "\<exists>w. v = VLit (LitString w)"
  proof (cases \<sigma>)
    case (TyPrim p)
    with assms(1, 2) show ?thesis by (auto dest: wf_str[OF _ SubtyRefl])
  next
    case (TyLiteral l)
    with assms(1, 2) show ?thesis by (cases l) (auto dest: wf_lit)
  qed (use assms(1) in simp_all)
  then obtain w where v: "v = VLit (LitString w)" by blast
  from str_elems obtain vs where "elems v = Some vs" and "\<forall>u \<in> set vs. \<turnstile> u : Ty (TyPrim str)"
    unfolding v by blast
  note get = getitem_elems[OF this]
  with assms(3) show ?thesis by (cases r) auto
qed

(* Result of a subscript of a value typed at \<sigma>, with the index typed by the checks and synthesis supplied to
   the typing of the subscript *)
lemma subscript_result:
  assumes "subscript_type \<Sigma> \<sigma> int_ok str_ok p idx = Ok \<tau>" and "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    and int: "int_ok = Ok () \<Longrightarrow> wf_result (\<lambda>u. \<exists>n. u = VLit (LitInt n)) r"
    and str: "str_ok = Ok () \<Longrightarrow> wf_result (\<lambda>u. \<exists>w. u = VLit (LitString w)) r"
    and idx: "\<And>\<iota>. idx = Ok \<iota> \<Longrightarrow> result_typed r (inst \<eta> \<iota>)"
  shows "result_typed (mlet r (getitem v)) (inst \<eta> \<tau>)"
  using assms(1, 2)
proof (induction \<sigma> arbitrary: \<tau> v)
  case (TyUnion \<sigma>1 \<sigma>2)
  from TyUnion.prems(1) obtain \<tau>1 \<tau>2 where \<tau>1: "subscript_type \<Sigma> \<sigma>1 int_ok str_ok p idx = Ok \<tau>1"
    and \<tau>2: "subscript_type \<Sigma> \<sigma>2 int_ok str_ok p idx = Ok \<tau>2" and \<tau>: "\<tau> = \<tau>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>2"
    by (auto simp: bind_sum_def split: sum.splits)
  from TyUnion.prems(2) have "\<turnstile> v : Ty (inst \<eta> \<sigma>1) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>2)" by (auto dest: wf_val_union)
  then show ?case
  proof
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>1)"
    from result_typed_sub[OF TyUnion.IH(1)[OF \<tau>1 this] join_upper(1)] \<tau> show ?thesis by simp
  next
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>2)"
    from result_typed_sub[OF TyUnion.IH(2)[OF \<tau>2 this] join_upper(2)] \<tau> show ?thesis by simp
  qed
next
  case (TyList \<sigma>')
  then have "int_ok = Ok ()" and \<tau>: "\<tau> = \<sigma>'" by (auto simp: bind_sum_def split: sum.splits)
  with int have r: "wf_result (\<lambda>u. \<exists>n. u = VLit (LitInt n)) r" by blast
  from TyList.prems(2) obtain vs where v: "v = VList vs" and vs: "\<forall>u \<in> set vs. \<turnstile> u : Ty (inst \<eta> \<sigma>')"
    by (auto elim: wf_list)
  have "elems v = Some vs" by (simp add: v)
  note get = getitem_elems[OF this vs]
  with r \<tau> show ?case by (cases r) auto
next
  case (TyDict \<sigma>')
  then have "str_ok = Ok ()" and \<tau>: "\<tau> = \<sigma>'" by (auto simp: bind_sum_def split: sum.splits)
  with str have r: "wf_result (\<lambda>u. \<exists>w. u = VLit (LitString w)) r" by blast
  from TyDict.prems(2) obtain \<delta> where v: "v = VDict \<delta>"
    and \<delta>: "\<forall>w u. (w, u) \<in> set \<delta> \<longrightarrow> \<turnstile> u : Ty (inst \<eta> \<sigma>')"
    by (auto elim: wf_dict_entries)
  have get: "wf_result (\<lambda>u. \<turnstile> u : Ty (inst \<eta> \<sigma>')) (getitem v (VLit (LitString w)))" for w
    using \<delta> by (auto simp: v split: option.splits dest!: map_of_SomeD)
  with r \<tau> show ?case by (cases r) auto
next
  case (TyTuple \<sigma>s)
  from TyTuple.prems(2) obtain vs where v: "v = VTuple vs"
    and vs: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs (map (inst \<eta>) \<sigma>s)"
    by (auto elim: wf_tuple)
  have len: "length vs = length \<sigma>s" using vs by (auto dest: list_all2_lengthD)
  from TyTuple.prems(1) obtain \<iota> where \<iota>: "idx = Ok \<iota>" by (auto simp: bind_sum_def split: sum.splits)
  with idx have r: "result_typed r (inst \<eta> \<iota>)" by blast
  show ?case
  proof (cases "\<iota> = TyPrim int")
    case True
    with TyTuple.prems(1) \<iota> have \<tau>: "\<tau> = joins \<Sigma> \<sigma>s" by (simp add: bind_sum_def)
    have "\<turnstile> u : Ty (inst \<eta> (joins \<Sigma> \<sigma>s))" if "u \<in> set vs" for u
    proof -
      from that obtain k where k: "k < length vs" and u: "u = vs ! k" by (auto simp: in_set_conv_nth)
      from list_all2_nthD[OF vs k] k len u have "\<turnstile> u : Ty (inst \<eta> (\<sigma>s ! k))" by simp
      from wf_val_inst_sub[OF this joins_upper] k len show ?thesis by simp
    qed
    moreover have "elems v = Some vs" by (simp add: v)
    ultimately have get: "wf_result (\<lambda>u. \<turnstile> u : Ty (inst \<eta> (joins \<Sigma> \<sigma>s))) (getitem v (VLit (LitInt n)))" for n
      by (blast intro: getitem_elems)
    with r True \<tau> show ?thesis by (cases r) (auto dest: wf_int[OF _ SubtyRefl])
  next
    case False
    have "\<exists>n. \<iota> = TyLiteral (LitInt n)"
      using TyTuple.prems(1) \<iota> False by (auto simp: bind_sum_def split: ty.splits lit.splits prim_ty.splits)
    then obtain n where \<iota>': "\<iota> = TyLiteral (LitInt n)" by blast
    define i where "i = (if n < 0 then of_nat (length \<sigma>s) + n else n)"
    have range: "0 \<le> i" "i < of_nat (length \<sigma>s)" and \<tau>: "\<tau> = \<sigma>s ! nat i"
      using TyTuple.prems(1) \<iota> \<iota>' by (auto simp: bind_sum_def Let_def i_def split: if_splits)
    have k: "nat i < length vs" using range len by (simp add: nat_less_iff)
    from list_all2_nthD[OF vs k] len \<tau> k have elem: "\<turnstile> vs ! nat i : Ty (inst \<eta> \<tau>)" by simp
    have "getitem v (VLit (LitInt n)) = Val (vs ! nat i)" using v range len by (auto simp: Let_def i_def)
    with r \<iota>' elem show ?thesis by (cases r) (auto dest!: wf_lit)
  qed
next
  case (TyPrim p)
  then have "base_type (TyPrim p) = TyPrim str" and "int_ok = Ok ()" and "\<tau> = TyPrim str"
    by (auto simp: bind_sum_def split: if_splits sum.splits)
  with int subscript_str[OF this(1) TyPrim.prems(2)] show ?case by simp
next
  case (TyLiteral l)
  then have "base_type (TyLiteral l) = TyPrim str" and "int_ok = Ok ()" and "\<tau> = TyPrim str"
    by (auto simp: bind_sum_def split: if_splits sum.splits)
  with int subscript_str[OF this(1) TyLiteral.prems(2)] show ?case by simp
qed (simp_all split: if_splits)

lemma subscript_sound:
  assumes callee: "sound_expr \<rho> (node e) (Val v)" and nonclass: "\<not> is_class v"
    and index: "sound_expr \<rho> (node e') r"
  shows "sound_expr \<rho> (ExprSubscript e e') (mlet r (getitem v))"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprSubscript e e') = Ok \<tau>"
  then obtain \<sigma> where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
    and sub: "subscript_type \<Sigma> \<sigma> (check_expr_at \<Sigma> \<Gamma> e' (TyPrim int)) (check_expr_at \<Sigma> \<Gamma> e' (TyPrim str))
      (pos_of e') (synth_expr_at \<Sigma> \<Gamma> e') = Ok \<tau>"
    by (auto simp: bind_sum_def split: sum.splits)
  from sound_expr_synth_at[OF callee env \<sigma>] have v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by simp
  show "result_typed (mlet r (getitem v)) (inst \<eta> \<tau>)"
  proof (rule subscript_result[OF sub v])
    assume "check_expr_at \<Sigma> \<Gamma> e' (TyPrim int) = Ok ()"
    from prim_operand[OF index env this] show "wf_result (\<lambda>u. \<exists>n. u = VLit (LitInt n)) r"
      by (cases r) (auto dest: wf_int[OF _ SubtyRefl])
  next
    assume "check_expr_at \<Sigma> \<Gamma> e' (TyPrim str) = Ok ()"
    from prim_operand[OF index env this] show "wf_result (\<lambda>u. \<exists>w. u = VLit (LitString w)) r"
      by (cases r) (auto dest: wf_str[OF _ SubtyRefl])
  next
    fix \<iota>
    assume "synth_expr_at \<Sigma> \<Gamma> e' = Ok \<iota>"
    from sound_expr_synth_at[OF index env this] show "result_typed r (inst \<eta> \<iota>)" .
  qed
next
  fix \<eta> \<Gamma> \<tau>
  assume "check_expr' \<Sigma> \<Gamma> (ExprSubscript e e') \<tau> = Some (Ok ())"
  then show "result_typed (mlet r (getitem v)) (inst \<eta> \<tau>)" by (simp add: var_scheme_None)
next
  fix \<eta> \<Gamma>
  assume "call_stmt \<Sigma> \<Gamma> (ExprSubscript e e')"
  then show "result_typed (mlet r (getitem v)) (inst \<eta> (TyPrim object))" by simp
next
  show "sound_name \<rho> (ExprSubscript e e') (mlet r (getitem v))"
    unfolding sound_name_def
  proof (intro allI impI)
    fix \<eta> \<Gamma> \<theta>
    assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "expr_entry \<Gamma> (ExprSubscript e e') = Some \<theta>"
    then obtain C where "class_of_name \<Gamma> (node e) = Some C" by auto
    from sound_expr_class[OF callee env class_of_name_entry[OF this]] nonclass
    show "wf_result (\<lambda>v'. \<turnstile> v' : inst_entry \<eta> \<theta>) (mlet r (getitem v))" by simp
  qed
qed

lemma class_type_args_sound:
  assumes "sound_expr \<rho> (node e) (Val (VClass C))" and "type_args_of e' = Some \<psi>s"
  shows "sound_expr \<rho> (ExprSubscript e e') (Val (VClass C))"
proof (rule sound_exprI)
  show "sound_name \<rho> (ExprSubscript e e') (Val (VClass C))"
    using assms(1) by (auto simp: sound_name_def dest!: class_of_name_entry dest: sound_expr_name)
qed (auto simp: bind_sum_def var_scheme_None dest!: sound_expr_synth_at[OF assms(1)] wf_class_ty
    split: sum.splits)

lemma subscript_fail_sound:
  assumes "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprSubscript e e') (Aborts \<kappa>)"
proof (rule sound_exprI)
  show "sound_name \<rho> (ExprSubscript e e') (Aborts \<kappa>)"
    using assms by (auto simp: sound_name_def dest!: class_of_name_entry dest: sound_expr_name)
qed (auto simp: bind_sum_def var_scheme_None dest: sound_expr_synth_at[OF assms] split: sum.splits)

(* Element of a list comprehension typed under its qualifiers at a subtype of the element type *)
lemma list_comp_typed:
  assumes "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprListComp e gs) \<tau>"
  shows "\<exists>\<Delta> \<tau>' \<sigma>. \<tau> = TyList \<tau>' \<and> quals \<Sigma> \<Gamma> gs = Ok \<Delta> \<and> has_type_at \<Sigma> \<eta> (\<Gamma> \<otimes> \<Delta>) e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  using assms unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprListComp e gs) = Ok \<tau>"
  then show ?thesis by (auto simp: bind_sum_def intro: has_type_synth_at base_type_upper split: sum.splits)
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprListComp e gs) \<tau> = Some (Ok ()) \<and> fv \<tau> \<subseteq> fst ` set \<eta>"
  then show ?thesis
    by (auto simp: bind_sum_def intro: has_type_check_at SubtyRefl split: ty.splits sum.splits)
qed

lemma list_comp_sound:
  assumes "sound_quals \<rho> gs (Val \<rho>s)" and "sound_comp \<rho>s e (Val vs)"
  shows "sound_expr \<rho> (ExprListComp e gs) (Val (VList vs))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprListComp e gs) \<tau>"
  from list_comp_typed[OF this(2)] obtain \<Delta> \<tau>' \<sigma> where \<tau>: "\<tau> = TyList \<tau>'" and "quals \<Sigma> \<Gamma> gs = Ok \<Delta>"
    and e: "has_type_at \<Sigma> \<eta> (\<Gamma> \<otimes> \<Delta>) e \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    by blast
  with assms(1) env have "\<forall>\<rho>' \<in> set \<rho>s. \<eta> \<turnstile> \<rho>' : \<Gamma> \<otimes> \<Delta>" by (simp add: sound_quals_def)
  from sound_compD[OF assms(2) this e] sub show "result_typed (Val (VList vs)) (inst \<eta> \<tau>)"
    by (auto simp: \<tau> intro: ValList wf_val_inst_sub)
qed simp_all

lemma list_comp_fail_quals_sound:
  assumes "sound_quals \<rho> gs (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprListComp e gs) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprListComp e gs) \<tau>"
  from list_comp_typed[OF this(2)] assms env show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)"
    by (auto simp: sound_quals_def)
qed simp_all

lemma list_comp_fail_sound:
  assumes "sound_quals \<rho> gs (Val \<rho>s)" and "sound_comp \<rho>s e (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprListComp e gs) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprListComp e gs) \<tau>"
  from list_comp_typed[OF this(2)] obtain \<Delta> \<sigma> where "quals \<Sigma> \<Gamma> gs = Ok \<Delta>"
    and e: "has_type_at \<Sigma> \<eta> (\<Gamma> \<otimes> \<Delta>) e \<sigma>"
    by blast
  with assms(1) env have "\<forall>\<rho>' \<in> set \<rho>s. \<eta> \<turnstile> \<rho>' : \<Gamma> \<otimes> \<Delta>" by (simp add: sound_quals_def)
  from sound_compD[OF assms(2) this e] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by simp
qed simp_all

(* Key of a dictionary comprehension checked against str, and its value typed at a subtype of the value type,
   under its qualifiers *)
lemma dict_comp_typed:
  assumes "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDictComp e e' gs) \<tau>"
  shows "\<exists>\<Delta> \<tau>' \<sigma>. \<tau> = TyDict \<tau>' \<and> quals \<Sigma> \<Gamma> gs = Ok \<Delta> \<and> check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str) = Ok ()
           \<and> has_type_at \<Sigma> \<eta> (\<Gamma> \<otimes> \<Delta>) e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  using assms unfolding typed_by_rule_def
proof
  assume "synth_expr \<Sigma> \<Gamma> (ExprDictComp e e' gs) = Ok \<tau>"
  then show ?thesis by (auto simp: bind_sum_def intro: has_type_synth_at base_type_upper split: sum.splits)
next
  assume "check_expr' \<Sigma> \<Gamma> (ExprDictComp e e' gs) \<tau> = Some (Ok ()) \<and> fv \<tau> \<subseteq> fst ` set \<eta>"
  then show ?thesis
    by (auto simp: bind_sum_def intro: has_type_check_at SubtyRefl split: ty.splits sum.splits)
qed

lemma dict_comp_sound:
  assumes "sound_quals \<rho> gs (Val \<rho>s)" and "sound_entries \<rho>s e e' (Val \<delta>)"
  shows "sound_expr \<rho> (ExprDictComp e e' gs) (Val (VDict (update [] \<delta>)))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDictComp e e' gs) \<tau>"
  from dict_comp_typed[OF this(2)] obtain \<Delta> \<tau>' \<sigma> where \<tau>: "\<tau> = TyDict \<tau>'" and "quals \<Sigma> \<Gamma> gs = Ok \<Delta>"
    and key: "check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str) = Ok ()" and e': "has_type_at \<Sigma> \<eta> (\<Gamma> \<otimes> \<Delta>) e' \<sigma>"
    and sub: "\<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    by blast
  with assms(1) env have "\<forall>\<rho>' \<in> set \<rho>s. \<eta> \<turnstile> \<rho>' : \<Gamma> \<otimes> \<Delta>" by (simp add: sound_quals_def)
  from sound_entriesD[OF assms(2) this key e'] sub
  have "\<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>')" by (auto intro: wf_val_inst_sub)
  then show "result_typed (Val (VDict (update [] \<delta>))) (inst \<eta> \<tau>)" by (simp add: \<tau> wf_dict_update)
qed simp_all

lemma dict_comp_fail_quals_sound:
  assumes "sound_quals \<rho> gs (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprDictComp e e' gs) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDictComp e e' gs) \<tau>"
  from dict_comp_typed[OF this(2)] assms env show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)"
    by (auto simp: sound_quals_def)
qed simp_all

lemma dict_comp_fail_sound:
  assumes "sound_quals \<rho> gs (Val \<rho>s)" and "sound_entries \<rho>s e e' (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprDictComp e e' gs) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDictComp e e' gs) \<tau>"
  from dict_comp_typed[OF this(2)] obtain \<Delta> \<sigma> where "quals \<Sigma> \<Gamma> gs = Ok \<Delta>"
    and key: "check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str) = Ok ()" and e': "has_type_at \<Sigma> \<eta> (\<Gamma> \<otimes> \<Delta>) e' \<sigma>"
    by blast
  with assms(1) env have "\<forall>\<rho>' \<in> set \<rho>s. \<eta> \<turnstile> \<rho>' : \<Gamma> \<otimes> \<Delta>" by (simp add: sound_quals_def)
  from sound_entriesD[OF assms(2) this key e'] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by simp
qed simp_all

(* Field of class C at type arguments \<tau>s, a subtype of the attribute type of a type above the class *)
lemma attribute_field:
  "\<lbrakk> \<Sigma> \<turnstile> TyClass C \<tau>s <: inst \<eta> \<sigma> ; attribute_type \<Sigma> \<sigma> x = Ok \<tau> ; C |\<in>| fmdom \<Sigma> \<rbrakk>
  \<Longrightarrow> \<exists>\<sigma>'. map_of (instantiate (fields \<Sigma> C) \<tau>s) x = Some \<sigma>' \<and> \<Sigma> \<turnstile> \<sigma>' <: inst \<eta> \<tau>"
proof (induction \<sigma> arbitrary: \<tau>)
  case (TyUnion \<sigma> \<sigma>'')
  from TyUnion(4) obtain \<tau>' \<tau>'' where \<tau>': "attribute_type \<Sigma> \<sigma> x = Ok \<tau>'"
    and \<tau>'': "attribute_type \<Sigma> \<sigma>'' x = Ok \<tau>''" and \<tau>: "\<tau> = \<tau>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>''"
    by (auto simp: bind_sum_def split: sum.splits)
  have "\<Sigma> \<turnstile> inst \<eta> \<tau>' <: inst \<eta> \<tau>" and "\<Sigma> \<turnstile> inst \<eta> \<tau>'' <: inst \<eta> \<tau>"
    unfolding \<tau> by (rule subst_subty', rule join_upper)+
  moreover note nonunion_subty_union(1)[OF TyUnion(3)[simplified] refl, simplified]
  ultimately show ?case using TyUnion(1)[OF _ \<tau>' TyUnion(5)] TyUnion(2)[OF _ \<tau>'' TyUnion(5)]
    by (blast intro: subty_trans')
next
  case (TyClass D \<sigma>s)
  then have "map_of (instantiate (fields \<Sigma> D) \<sigma>s) x = Some \<tau>" by (simp add: or_else_def split: option.splits)
  then have "map_of (instantiate (fields \<Sigma> D) (map (inst \<eta>) \<sigma>s)) x = Some (inst \<eta> \<tau>)"
    by (rule instantiate_fields_subst')
  moreover from TyClass(2) have "\<Sigma> \<turnstile> TyClass C \<tau>s <: TyClass D (map (inst \<eta>) \<sigma>s)" by simp
  ultimately show ?case using subty_class_fields(1)[OF wf_class_table _ refl refl TyClass(4)] by blast
qed simp_all

(* Attribute typed through a checked module, at a member type, member scheme or type variable, or through the
   type synthesised by the object *)
lemma attr_typed:
  assumes "has_type \<Sigma> \<eta> \<Gamma> (ExprAttribute e x) \<tau>"
  obtains (module_ty) q q' \<Gamma>' \<sigma> where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
      and "fmlookup \<Gamma>' x = Some (Ty \<sigma>)" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    | (module_scheme) q q' \<Gamma>' \<alpha>s \<sigma> \<tau>s where "dotted_name (node e) = Some q"
      and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')" and "fmlookup \<Gamma>' x = Some (Scheme (TyScheme \<alpha>s \<sigma>))"
      and "Subtyping.type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s" and "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: \<tau>"
      and "fv \<tau> \<subseteq> fst ` set \<eta>"
    | (module_tyvar) q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
      and "fmlookup \<Gamma>' x = Some TypeVar"
    | (object) \<sigma> \<sigma>' where "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'" and "\<Sigma> \<turnstile> \<sigma>' <: \<tau>"
proof -
  have synth: thesis if "synth_expr \<Sigma> \<Gamma> (ExprAttribute e x) = Ok \<sigma>'" and "\<Sigma> \<turnstile> \<sigma>' <: \<tau>" for \<sigma>'
  proof (cases "module_attribute \<Gamma> (node e) x")
    case None
    with that show ?thesis by (auto simp: bind_sum_def split: sum.splits intro: object)
  next
    case (Some m)
    with that(1) obtain q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
      and "fmlookup \<Gamma>' x = Some (Ty \<sigma>') \<or> fmlookup \<Gamma>' x = Some TypeVar"
      by (auto simp: module_attribute_def attr_module_def bind_eq_Some_conv
          split: option.splits cxt_entry.splits)
    with that(2) show ?thesis by (blast intro: module_ty module_tyvar)
  qed
  have scheme: thesis if "var_scheme \<Sigma> \<Gamma> (ExprAttribute e x) \<tau> = Some (Ok ())" and "fv \<tau> \<subseteq> fst ` set \<eta>"
  proof -
    from that(1) obtain q q' \<Gamma>' \<alpha>s \<sigma> \<tau>s where "dotted_name (node e) = Some q"
      and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')" and "fmlookup \<Gamma>' x = Some (Scheme (TyScheme \<alpha>s \<sigma>))"
      and "Subtyping.type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s" and "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: \<tau>"
      by (auto simp: var_scheme_def scheme_of_name_def entry_of_def resolve_name_def bind_sum_def ensure_def
          Let_def bind_eq_Some_conv split: option.splits cxt_entry.splits ty_scheme.splits if_splits sum.splits)
    then show ?thesis using that(2) by (rule module_scheme)
  qed
  from assms show thesis unfolding has_type_def by (auto dest!: check_expr_cases intro: synth scheme SubtyRefl)
qed

(* Value of a dotted name bound to a checked module, as a loaded module with its environment typed by the
   context of the module *)
lemma sound_expr_module_env:
  assumes "sound_expr \<rho> e (Val v)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "dotted_name e = Some q"
    and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
  shows "\<exists>\<rho>'. v = VModLoaded q' \<rho>' \<and> [] \<turnstile> \<rho>' : \<Gamma>'"
  using sound_expr_module[OF assms, unfolded wf_result.simps(1)] by (rule wf_mod_checked)

(* Attribute of an expression with a value which is not a loaded module, typed through the type synthesised by
   the expression *)
lemma attr_typed_object:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<not> is_loaded_module v" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and "has_type \<Sigma> \<eta> \<Gamma> (ExprAttribute e x) \<tau>"
  obtains \<sigma> \<sigma>' where "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'" and "\<Sigma> \<turnstile> \<sigma>' <: \<tau>"
  using assms(4)
proof (cases rule: attr_typed)
  case (module_ty q q' \<Gamma>' \<sigma>)
  from sound_expr_module_env[OF assms(1, 3) module_ty(1, 2)] assms(2) show thesis by auto
next
  case (module_scheme q q' \<Gamma>' \<alpha>s \<sigma> \<tau>s)
  from sound_expr_module_env[OF assms(1, 3) module_scheme(1, 2)] assms(2) show thesis by auto
next
  case (module_tyvar q q' \<Gamma>')
  from sound_expr_module_env[OF assms(1, 3) module_tyvar(1, 2)] assms(2) show thesis by auto
next
  case (object \<sigma> \<sigma>')
  then show thesis by (rule that)
qed

(* Name clause for an attribute of an expression with a value which is not a loaded module *)
lemma sound_name_attr:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<not> is_loaded_module v"
  shows "sound_name \<rho> (ExprAttribute e x) r"
  unfolding sound_name_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<theta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "expr_entry \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
    and "fmlookup \<Gamma>' x = Some \<theta>"
    unfolding expr_entry_simps by (rule entry_of_attribute)
  from sound_expr_module_env[OF assms(1) env this(1, 2)] assms(2)
  show "wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r" by auto
qed

(* Field x of an object, typed by the attribute type of x at a type of the object *)
lemma object_attribute:
  assumes "\<turnstile> VObject C xvs : Ty (inst \<eta> \<sigma>)" and "attribute_type \<Sigma> \<sigma> x = Ok \<tau>"
  obtains v where "map_of xvs x = Some v" and "\<turnstile> v : Ty (inst \<eta> \<tau>)"
proof -
  from assms(1) obtain \<tau>s where C: "C |\<in>| fmdom \<Sigma>"
    and names: "map fst xvs = field_names \<Sigma> C"
    and fields: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s)"
    and sub: "\<Sigma> \<turnstile> TyClass C \<tau>s <: inst \<eta> \<sigma>"
    by (rule wf_object)
  from attribute_field[OF sub assms(2) C] obtain \<sigma>'
    where field: "map_of (instantiate (fields \<Sigma> C) \<tau>s) x = Some \<sigma>'"
    and sub': "\<Sigma> \<turnstile> \<sigma>' <: inst \<eta> \<tau>"
    by blast
  obtain v where "map_of xvs x = Some v" and "\<turnstile> v : Ty \<sigma>'" by (rule object_field[OF names fields field])
  from that[OF this(1) ValSub[OF this(2) sub']] show thesis .
qed

lemma attr_object_sound:
  assumes "sound_expr \<rho> (node e) (Val (VObject C xvs))" and "map_of xvs x = Some v"
  shows "sound_expr \<rho> (ExprAttribute e x) (Val v)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprAttribute e x) \<tau>"
  obtain \<sigma> \<sigma>' where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and attr: "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'"
    and sub: "\<Sigma> \<turnstile> \<sigma>' <: \<tau>"
    by (rule attr_typed_object[OF assms(1) _ env typed]) simp
  from sound_expr_synth_at[OF assms(1) env synth] have "\<turnstile> VObject C xvs : Ty (inst \<eta> \<sigma>)" by simp
  from object_attribute[OF this attr] assms(2) have "\<turnstile> v : Ty (inst \<eta> \<sigma>')" by auto
  with sub show "result_typed (Val v) (inst \<eta> \<tau>)" by (auto intro: wf_val_inst_sub)
next
  show "sound_name \<rho> (ExprAttribute e x) (Val v)" using assms(1) by (rule sound_name_attr) simp
qed

lemma attr_object_missing_sound:
  assumes "sound_expr \<rho> (node e) (Val (VObject C xvs))" and "map_of xvs x = None"
  shows "sound_expr \<rho> (ExprAttribute e x) (Aborts AttributeError)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprAttribute e x) \<tau>"
  obtain \<sigma> \<sigma>' where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and attr: "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'"
    by (rule attr_typed_object[OF assms(1) _ env typed]) simp
  from sound_expr_synth_at[OF assms(1) env synth] have "\<turnstile> VObject C xvs : Ty (inst \<eta> \<sigma>)" by simp
  from object_attribute[OF this attr] assms(2) show "result_typed (Aborts AttributeError) (inst \<eta> \<tau>)" by auto
next
  show "sound_name \<rho> (ExprAttribute e x) (Aborts AttributeError)"
    using assms(1) by (rule sound_name_attr) simp
qed

lemma attr_module_sound:
  assumes "sound_expr \<rho> (node e) (Val (VModLoaded q' \<rho>'))" and "fmlookup \<rho>' x = Some v"
  shows "sound_expr \<rho> (ExprAttribute e x) (Val v)"
  unfolding sound_expr_def sound_name_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprAttribute e x) \<tau>"
  from typed show "result_typed (Val v) (inst \<eta> \<tau>)"
  proof (cases rule: attr_typed)
    case (module_ty q q'' \<Gamma>' \<sigma>)
    from sound_expr_module_env[OF assms(1) env module_ty(1, 2)] have "[] \<turnstile> \<rho>' : \<Gamma>'" by auto
    with module_ty(3) assms(2) have "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by (auto dest!: module_member simp: subst_closed)
    with module_ty(4) show ?thesis by (auto intro: wf_val_inst_sub)
  next
    case (module_scheme q q'' \<Gamma>' \<alpha>s \<sigma> \<tau>s)
    from sound_expr_module_env[OF assms(1) env module_scheme(1, 2)] have "[] \<turnstile> \<rho>' : \<Gamma>'" by auto
    with module_scheme(3) assms(2) have v: "\<turnstile> v : Scheme (TyScheme \<alpha>s \<sigma>)" and fv: "fv \<sigma> \<subseteq> set \<alpha>s"
      by (auto dest!: module_member)
    have len: "length \<tau>s = length \<alpha>s" using module_scheme(4) by (rule type_args_of_length)
    have closed: "\<forall>\<tau>' \<in> set (map (inst \<eta>) \<tau>s). fv \<tau>' = {}"
      using type_args_fv[OF module_scheme(4)] module_scheme(6) wf_env_closed[OF env]
      by (auto intro!: inst_closed)
    have "length (map (inst \<eta>) \<tau>s) = length \<alpha>s" by (simp add: len)
    from v this closed have "\<turnstile> v : Ty (subst (map (inst \<eta>) \<tau>s) \<alpha>s \<sigma>)" by (rule ValInst)
    then have "\<turnstile> v : Ty (inst \<eta> (subst \<tau>s \<alpha>s \<sigma>))" by (simp only: subst_subst[OF fv len])
    with module_scheme(5) show ?thesis by (auto intro: wf_val_inst_sub)
  next
    case (module_tyvar q q'' \<Gamma>')
    from sound_expr_module_env[OF assms(1) env module_tyvar(1, 2)] module_tyvar(3) show ?thesis
      by (auto dest: module_member_TypeVar)
  next
    case (object \<sigma> \<sigma>')
    from sound_expr_synth_at[OF assms(1) env object(1)] show ?thesis by (auto dest: wf_mod_loaded)
  qed
next
  fix \<eta> \<Gamma> \<theta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "expr_entry \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q'' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q'' \<Gamma>')"
    and x: "fmlookup \<Gamma>' x = Some \<theta>"
    unfolding expr_entry_simps by (rule entry_of_attribute)
  from sound_expr_module_env[OF assms(1) env this(1, 2)] have "[] \<turnstile> \<rho>' : \<Gamma>'" by auto
  moreover from this x have "\<theta> \<noteq> TypeVar" by (auto dest: module_member_TypeVar)
  ultimately show "wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) (Val v)"
    using x assms(2) by (auto dest!: module_member simp: inst_entry_closed)
qed

lemma attr_module_missing_sound:
  assumes "sound_expr \<rho> (node e) (Val (VModLoaded q' \<rho>'))" and "fmlookup \<rho>' x = None"
  shows "sound_expr \<rho> (ExprAttribute e x) (Aborts AttributeError)"
  unfolding sound_expr_def sound_name_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprAttribute e x) \<tau>"
  from typed show "result_typed (Aborts AttributeError) (inst \<eta> \<tau>)"
  proof (cases rule: attr_typed)
    case (module_ty q q'' \<Gamma>' \<sigma>)
    from sound_expr_module_env[OF assms(1) env module_ty(1, 2)] module_ty(3) assms(2) show ?thesis
      by (auto dest!: module_member)
  next
    case (module_scheme q q'' \<Gamma>' \<alpha>s \<sigma> \<tau>s)
    from sound_expr_module_env[OF assms(1) env module_scheme(1, 2)] module_scheme(3) assms(2) show ?thesis
      by (auto dest!: module_member)
  next
    case (module_tyvar q q'' \<Gamma>')
    from sound_expr_module_env[OF assms(1) env module_tyvar(1, 2)] module_tyvar(3) show ?thesis
      by (auto dest: module_member_TypeVar)
  next
    case (object \<sigma> \<sigma>')
    from sound_expr_synth_at[OF assms(1) env object(1)] show ?thesis by (auto dest: wf_mod_loaded)
  qed
next
  fix \<eta> \<Gamma> \<theta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "expr_entry \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q'' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q'' \<Gamma>')"
    and x: "fmlookup \<Gamma>' x = Some \<theta>"
    unfolding expr_entry_simps by (rule entry_of_attribute)
  from sound_expr_module_env[OF assms(1) env this(1, 2)] have "[] \<turnstile> \<rho>' : \<Gamma>'" by auto
  moreover from this x have "\<theta> \<noteq> TypeVar" by (auto dest: module_member_TypeVar)
  ultimately show "wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) (Aborts AttributeError)"
    using x assms(2) by (auto dest!: module_member)
qed

lemma attr_nonobject_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<not> is_object v" and "\<not> is_loaded_module v"
  shows "sound_expr \<rho> (ExprAttribute e x) (Aborts Excluded)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprAttribute e x) \<tau>"
  obtain \<sigma> \<sigma>' where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" and attr: "attribute_type \<Sigma> \<sigma> x = Ok \<sigma>'"
    by (rule attr_typed_object[OF assms(1, 3) env typed])
  from sound_expr_synth_at[OF assms(1) env synth] have "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by simp
  moreover from attr have "object_type (inst \<eta> \<sigma>)"
    by (blast intro: object_type_subst attribute_type_object_type)
  ultimately show "result_typed (Aborts Excluded) (inst \<eta> \<tau>)" using assms(2) wf_object_type(1) by blast
next
  show "sound_name \<rho> (ExprAttribute e x) (Aborts Excluded)" using assms(1, 3) by (rule sound_name_attr)
qed

lemma attr_fail_sound:
  assumes "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprAttribute e x) (Aborts \<kappa>)"
  unfolding sound_expr_def sound_name_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprAttribute e x) \<tau>"
  from typed show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)"
    by (cases rule: attr_typed) (auto dest: sound_expr_module[OF assms env] sound_expr_synth_at[OF assms env])
next
  fix \<eta> \<Gamma> \<theta>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "expr_entry \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
    and "fmlookup \<Gamma>' x = Some \<theta>"
    unfolding expr_entry_simps by (rule entry_of_attribute)
  from sound_expr_module[OF assms env this(1, 2)]
  show "wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) (Aborts \<kappa>)" by simp
qed

lemma exprs_nil_sound: "sound_exprs \<rho> [] (Val [])"
  by (simp add: sound_exprs_def)

lemma exprs_cons_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and "sound_exprs \<rho> es r"
  shows "sound_exprs \<rho> (e # es) (mlet r (\<lambda>vs. Val (v # vs)))"
  unfolding sound_exprs_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<tau>s
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) (e # es) \<tau>s"
  then obtain \<tau> \<tau>s' where \<tau>s: "\<tau>s = \<tau> # \<tau>s'" and e: "has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>"
    and es: "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s'"
    by (auto simp: list_all2_Cons1)
  from assms(1) env e have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_has_type_at)
  moreover from assms(2) env es have "results_typed r (map (inst \<eta>) \<tau>s')" by (simp add: sound_exprs_def)
  ultimately show "results_typed (mlet r (\<lambda>vs. Val (v # vs))) (map (inst \<eta>) \<tau>s)" by (cases r) (simp_all add: \<tau>s)
qed

lemma exprs_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_exprs \<rho> (e # es) (Aborts \<kappa>)"
  unfolding sound_exprs_def by (auto simp: list_all2_Cons1 dest: sound_expr_has_type_at)

subsection \<open>Comprehensions\<close>

lemma quals_nil_sound: "sound_quals \<rho> [] (Val [\<rho>])"
  by (simp add: sound_quals_def)

lemma qual_guard_true_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val true) ; sound_quals \<rho> gs r \<rbrakk> \<Longrightarrow> sound_quals \<rho> (At p (Guard e) # gs) r"
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
  "\<lbrakk> \<turnstile> v : Ty (inst \<eta> \<sigma>) ; elem_type \<Sigma> \<sigma> = Some \<tau> ; iter v = Some us \<rbrakk> \<Longrightarrow> \<forall>u \<in> set us. \<turnstile> u : Ty (inst \<eta> \<tau>)"
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
  from wf_val_intro(1)[OF TyClass(2)] obtain \<sigma> where intro: "intro_typed v \<sigma>"
    and sub: "\<Sigma> \<turnstile> \<sigma> <: inst \<eta> (TyClass C \<sigma>s)"
    by blast
  from subty_class_inv(1)[OF sub] intro_typed_nonunion[OF intro] obtain D \<sigma>s' where "\<sigma> = TyClass D \<sigma>s'" by auto
  with intro obtain xvs where "v = VObject D xvs" by (cases v) auto
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
    moreover from this(2) have "\<Sigma> \<turnstile> base_type (\<sigma>s ! i) <: \<tau>" unfolding \<tau> by (auto intro: joins_upper)
    with base_type_upper have "\<Sigma> \<turnstile> \<sigma>s ! i <: \<tau>" by (rule subty_trans')
    ultimately show "\<turnstile> u : Ty (inst \<eta> \<tau>)" by (blast intro: wf_val_inst_sub)
  qed
next
  case (TyUnion \<sigma> \<sigma>')
  from TyUnion(4) obtain \<tau>' \<tau>'' where \<tau>': "elem_type \<Sigma> \<sigma> = Some \<tau>'" and \<tau>'': "elem_type \<Sigma> \<sigma>' = Some \<tau>''"
    and \<tau>: "\<tau> = \<tau>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>''"
    by (auto split: option.splits)
  from wf_val_union[of v "inst \<eta> \<sigma>" "inst \<eta> \<sigma>'"] TyUnion(3) have "\<turnstile> v : Ty (inst \<eta> \<sigma>) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>')"
    by simp
  then show ?case
  proof
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    from TyUnion(1)[OF this \<tau>' TyUnion(5)] show ?thesis unfolding \<tau> by (blast intro: wf_val_inst_sub join_upper)
  next
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>')"
    from TyUnion(2)[OF this \<tau>'' TyUnion(5)] show ?thesis unfolding \<tau> by (blast intro: wf_val_inst_sub join_upper)
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
  from iter_typed[OF this elem assms(2)] have us: "\<forall>u \<in> set us. \<turnstile> u : Ty (inst \<eta> \<tau>)" .
  have "fv \<tau> \<subseteq> fst ` set \<eta>" using elem_type_fv[OF elem] synth_at_tyvars[OF synth] wf_env_tyvars[OF env] by blast
  with assms(3) env us \<Delta>' have "wf_envs \<eta> r (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>')" by (simp add: sound_gen_def)
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
  from wf_val_intro(1)[OF v] obtain \<sigma> where intro: "intro_typed v \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: TyClass range_class []"
    by blast
  from subty_class_inv(1)[OF sub refl] intro_typed_nonunion[OF intro] obtain D \<sigma>s' where "\<sigma> = TyClass D \<sigma>s'"
    by auto
  with intro obtain xvs where v': "v = VObject D xvs" by (cases v) auto
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and fv: "fv \<tau> \<subseteq> fst ` set \<eta>" and us: "\<forall>u' \<in> set (u # us). \<turnstile> u' : Ty (inst \<eta> \<tau>)"
    and quals: "quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>"
  have "\<eta> \<turnstile> fmupd x u \<rho> : fmupd x (Ty \<tau>) \<Gamma>" using env fv us by (intro wf_env_upd) auto
  with assms(1) quals have "wf_envs \<eta> (Val \<rho>s) (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)" by (simp add: sound_quals_def)
  moreover from assms(2) env fv us quals have "wf_envs \<eta> r (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)"
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and fv: "fv \<tau> \<subseteq> fst ` set \<eta>" and us: "\<forall>u' \<in> set (u # us). \<turnstile> u' : Ty (inst \<eta> \<tau>)"
    and quals: "quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>"
  have "\<eta> \<turnstile> fmupd x u \<rho> : fmupd x (Ty \<tau>) \<Gamma>" using env fv us by (intro wf_env_upd) auto
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
  assume envs: "\<forall>\<rho> \<in> set (\<rho> # \<rho>s). \<eta> \<turnstile> \<rho> : \<Gamma>" and e: "has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>"
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
  assumes "sound_expr \<rho> (node e) (Val (VLit (LitString w)))" and "sound_expr \<rho> (node e') (Val v)"
    and "sound_entries \<rho>s e e' r"
  shows "sound_entries (\<rho> # \<rho>s) e e' (mlet r (\<lambda>\<delta>. Val ((w, v) # \<delta>)))"
  unfolding sound_entries_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume envs: "\<forall>\<rho> \<in> set (\<rho> # \<rho>s). \<eta> \<turnstile> \<rho> : \<Gamma>" and key: "check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()"
    and e': "has_type_at \<Sigma> \<eta> \<Gamma> e' \<tau>"
  from assms(2) envs e' have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_has_type_at)
  moreover from envs have "\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>" by simp
  with assms(3) key e' have "wf_entries r (inst \<eta> \<tau>)" by (blast intro: sound_entriesD)
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
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VLit (LitString w))) ; sound_expr \<rho> (node e') (Aborts \<kappa>) \<rbrakk>
  \<Longrightarrow> sound_entries (\<rho> # \<rho>s) e e' (Aborts \<kappa>)"
  unfolding sound_entries_def by (auto dest: sound_expr_has_type_at)

end

end
