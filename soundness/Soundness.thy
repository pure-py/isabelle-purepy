(* Type soundness *)
theory Soundness
  imports ValueTyping
begin

context evaluation
begin

(* Soundness of one evaluation, at every context, instantiation and typing at which the construct checks *)
definition sound_expr :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"
where
"sound_expr \<rho> e r = (\<forall>\<eta> \<Gamma> \<tau>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> has_type \<Sigma> \<eta> \<Gamma> e \<tau> \<longrightarrow> wf_result r (inst \<eta> \<tau>))"

definition sound_exprs :: "env \<Rightarrow> expr located list \<Rightarrow> val list result \<Rightarrow> bool"
where
"sound_exprs \<rho> es rs =
  (\<forall>\<eta> \<Gamma> \<tau>s. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s \<longrightarrow> wf_results rs (map (inst \<eta>) \<tau>s))"

definition sound_stmt :: "env \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_stmt \<rho> s o =
  (\<forall>\<eta> \<Gamma> \<zeta> R. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<eta> \<zeta> \<longrightarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R
     \<longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R)"

definition sound_elif :: "env \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_elif \<rho> eb o =
  (\<forall>\<eta> \<Gamma> \<zeta> Rs. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<eta> \<zeta> \<longrightarrow> those_sum (check_elif \<Sigma> \<Gamma> \<zeta> eb) = Ok Rs
     \<longrightarrow> (\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R))"

fun wf_envs :: "(var \<times> ty) list \<Rightarrow> env list result \<Rightarrow> cxt \<Rightarrow> bool"
where
"wf_envs \<eta> (Val \<rho>s) \<Gamma> = (\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>)" |
"wf_envs \<eta> (Aborts \<kappa>) \<Gamma> = (\<not> prevented \<kappa>)"

definition sound_quals :: "env \<Rightarrow> qualifier located list \<Rightarrow> env list result \<Rightarrow> bool"
where
"sound_quals \<rho> gs r = (\<forall>\<eta> \<Gamma> \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> quals \<Sigma> \<Gamma> gs = Ok \<Delta> \<longrightarrow> wf_envs \<eta> r (\<Gamma> \<otimes> \<Delta>))"

definition sound_gen :: "env \<Rightarrow> var \<Rightarrow> val list \<Rightarrow> qualifier located list \<Rightarrow> env list result \<Rightarrow> bool"
where
"sound_gen \<rho> x us gs r =
  (\<forall>\<eta> \<Gamma> \<tau> \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> fv \<tau> \<subseteq> fst ` set \<eta> \<longrightarrow> (\<forall>u \<in> set us. \<turnstile> u : Ty (inst \<eta> \<tau>))
     \<longrightarrow> quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>
     \<longrightarrow> wf_envs \<eta> r (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>))"

fun wf_elems :: "val list result \<Rightarrow> ty \<Rightarrow> bool"
where
"wf_elems (Val vs) \<tau> = (\<forall>v \<in> set vs. \<turnstile> v : Ty \<tau>)" |
"wf_elems (Aborts \<kappa>) \<tau> = (\<not> prevented \<kappa>)"

definition sound_comp :: "env list \<Rightarrow> expr located \<Rightarrow> val list result \<Rightarrow> bool"
where
"sound_comp \<rho>s e r =
  (\<forall>\<eta> \<Gamma> \<tau>. (\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) \<longrightarrow> has_type_at \<Sigma> \<eta> \<Gamma> e \<tau> \<longrightarrow> wf_elems r (inst \<eta> \<tau>))"

fun wf_entries :: "(str \<times> val) list result \<Rightarrow> ty \<Rightarrow> bool"
where
"wf_entries (Val \<delta>) \<tau> = (\<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau>)" |
"wf_entries (Aborts \<kappa>) \<tau> = (\<not> prevented \<kappa>)"

definition sound_entries :: "env list \<Rightarrow> expr located \<Rightarrow> expr located \<Rightarrow> (str \<times> val) list result \<Rightarrow> bool"
where
"sound_entries \<rho>s e e' r =
  (\<forall>\<eta> \<Gamma> \<tau>. (\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) \<longrightarrow> check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()
     \<longrightarrow> has_type_at \<Sigma> \<eta> \<Gamma> e' \<tau> \<longrightarrow> wf_entries r (inst \<eta> \<tau>))"

subsection \<open>Subtyping\<close>

lemma subty_trans: "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: \<tau> ; \<Sigma> \<turnstile> \<tau> <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  sorry

lemma subst_subty: "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: subst \<tau>s \<alpha>s \<tau>"
  sorry

lemma join_upper: "\<Sigma> \<turnstile> \<sigma> <: \<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>" "\<Sigma> \<turnstile> \<tau> <: \<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>"
  by (auto simp: join_def intro: SubtyRefl SubtyUnionLeft SubtyUnionRight)

lemma joins_upper: "\<tau> \<in> set \<tau>s \<Longrightarrow> \<Sigma> \<turnstile> \<tau> <: joins \<Sigma> \<tau>s"
  by (induction \<tau>s) (auto simp: joins_def intro: join_upper subty_trans)

lemma base_type_upper: "\<Sigma> \<turnstile> \<tau> <: base_type \<tau>"
  by (cases \<tau>) (auto intro: SubtyRefl SubtyLiteral)

lemma wf_result_sub: "\<lbrakk> wf_result r (inst \<eta> \<sigma>) ; \<Sigma> \<turnstile> \<sigma> <: \<tau> \<rbrakk> \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
  by (cases r) (auto intro: ValSub subst_subty)

lemma wf_lit_bool: "\<turnstile> VLit (LitBool b) : Ty (TyPrim bool)"
  by (rule ValSub[OF ValLit], rule SubtyLiteral) (simp add: SubtyRefl)

subsection \<open>Well-scoped types\<close>

(* Types produced by the checker are over the type variables in scope *)
lemma synth_tyvars: "synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<Longrightarrow> fv \<tau> \<subseteq> tyvars \<Gamma>"
  sorry

lemma synth_at_tyvars: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<Longrightarrow> fv \<tau> \<subseteq> tyvars \<Gamma>"
  by (cases e) (auto dest: synth_tyvars)

lemma resolve_type_tyvars: "resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau> \<Longrightarrow> fv \<tau> \<subseteq> tyvars \<Gamma>"
  sorry

lemma type_args_fv:
  "Subtyping.type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s \<Longrightarrow> \<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fv \<tau>"
  sorry

lemma type_args_of_length: "Subtyping.type_args_of \<gamma> \<alpha>s = Ok \<tau>s \<Longrightarrow> length \<tau>s = length \<alpha>s"
  by (auto simp: Subtyping.type_args_of_def dest!: those_sum_Ok list_all2_lengthD)

subsection \<open>Checking\<close>

(* Checking succeeds by the checking rule of the expression or by synthesising a subtype *)
lemma check_expr_cases:
  assumes "check_expr \<Sigma> \<Gamma> e \<tau> = Ok ()"
  shows "check_expr' \<Sigma> \<Gamma> e \<tau> = Some (Ok ()) \<or> (\<exists>\<sigma>. synth_expr \<Sigma> \<Gamma> e = Ok \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>)"
  using assms
  by (auto simp: check_expr.simps[of \<Sigma> \<Gamma> e \<tau>] ensure_def bind_sum_def
      split: option.splits sum.splits if_splits)

lemma sound_exprI:
  assumes synth: "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
  and check:
    "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr' \<Sigma> \<Gamma> e \<tau> = Some (Ok ()) ; fv \<tau> \<subseteq> fst ` set \<eta> \<rbrakk>
      \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
  and call: "\<And>\<eta> \<Gamma>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; call_stmt \<Sigma> \<Gamma> e \<rbrakk> \<Longrightarrow> wf_result r (inst \<eta> (TyPrim object))"
  shows "sound_expr \<rho> e r"
  unfolding sound_expr_def has_type_def by (blast dest: check_expr_cases synth check call wf_result_sub)

(* Expression with a synthesis rule only *)
lemma sound_expr_synthI:
  assumes "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
    and "\<And>\<Gamma> \<tau>. check_expr' \<Sigma> \<Gamma> e \<tau> = None" and "\<And>\<Gamma>. \<not> call_stmt \<Sigma> \<Gamma> e"
  shows "sound_expr \<rho> e r"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> e = Ok \<tau>"
  then show "wf_result r (inst \<eta> \<tau>)" by (rule assms(1))
qed (simp_all add: assms(2, 3))

lemma sound_expr_synth_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def has_type_def)

lemma sound_expr_check_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok () ; fv \<tau> \<subseteq> fst ` set \<eta> \<rbrakk>
  \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def has_type_def)

lemma sound_expr_has_type_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; has_type_at \<Sigma> \<eta> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def)

lemmas sound_expr_at = sound_expr_synth_at sound_expr_check_at

lemma sound_exprs_abort:
  "\<lbrakk> sound_exprs \<rho> es (Aborts \<kappa>) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s \<rbrakk> \<Longrightarrow> \<not> prevented \<kappa>"
  by (fastforce simp: sound_exprs_def)

lemma sound_stmt_at:
  assumes "sound_stmt \<rho> (node s) o" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "wf_return \<eta> \<zeta>"
    and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
proof -
  obtain p s' where s: "s = At p s'" by (cases s)
  obtain vs \<omega> where o: "o = (vs, \<omega>)" by (cases o)
  from assms(4) obtain R' where "check_stmt \<Sigma> \<Gamma> \<zeta> s' = Ok R'" and R': "bindings_of R' = bindings_of R"
    unfolding s by (blast dest: check_stmt_at_Ok)
  with assms(1-3) have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'" unfolding sound_stmt_def s by simp
  then show ?thesis using wf_completion_bindings[OF R'[symmetric]] by (simp add: o)
qed

subsection \<open>Canonical forms\<close>

lemma wf_bool: "\<lbrakk> \<turnstile> v : Ty \<tau> ; \<Sigma> \<turnstile> \<tau> <: TyPrim bool \<rbrakk> \<Longrightarrow> v = true \<or> v = false"
  sorry

lemma wf_str: "\<lbrakk> \<turnstile> v : Ty \<tau> ; \<Sigma> \<turnstile> \<tau> <: TyPrim str \<rbrakk> \<Longrightarrow> \<exists>w. v = VLit (LitString w)"
  sorry

(* Operands checked as Booleans or strings *)
lemma bool_operand:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()"
  shows "v = true \<or> v = false"
proof -
  have "wf_result (Val v) (inst \<eta> (TyPrim bool))" by (rule sound_expr_check_at[OF assms]) simp
  then show ?thesis by (auto dest!: wf_bool[OF _ SubtyRefl])
qed

lemma bool_operand_abort:
  assumes "sound_expr \<rho> (node e) (Aborts \<kappa>)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()"
  shows "\<not> prevented \<kappa>"
proof -
  have "wf_result (Aborts \<kappa>) (inst \<eta> (TyPrim bool))" by (rule sound_expr_check_at[OF assms]) simp
  then show ?thesis by simp
qed

lemma str_operand:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()"
  shows "\<exists>w. v = VLit (LitString w)"
proof -
  have "wf_result (Val v) (inst \<eta> (TyPrim str))" by (rule sound_expr_check_at[OF assms]) simp
  then show ?thesis by (auto dest!: wf_str[OF _ SubtyRefl])
qed

lemma str_operand_abort:
  assumes "sound_expr \<rho> (node e) (Aborts \<kappa>)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()"
  shows "\<not> prevented \<kappa>"
proof -
  have "wf_result (Aborts \<kappa>) (inst \<eta> (TyPrim str))" by (rule sound_expr_check_at[OF assms]) simp
  then show ?thesis by simp
qed

subsection \<open>Expressions\<close>

lemma var_sound:
  assumes "fmlookup \<rho> x = Some v" and "v \<noteq> VUnbound"
  shows "sound_expr \<rho> (ExprVar x) (Val v)"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprVar x) = Ok \<tau>"
  then have "fmlookup \<Gamma> x = Some (Ty \<tau>)" by (auto split: option.splits cxt_entry.splits)
  with env assms(1) show "wf_result (Val v) (inst \<eta> \<tau>)" by (auto dest!: wf_env_lookup)
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
  then show "wf_result (Val v) (inst \<eta> \<tau>)" using sub by (auto intro: ValSub subst_subty)
qed simp

lemma var_unknown_sound: "fmlookup \<rho> x = None \<Longrightarrow> sound_expr \<rho> (ExprVar x) (Aborts NameError)"
  by (rule sound_exprI)
     (auto simp: var_scheme_def scheme_of_name_def entry_of_def resolve_name_def
      split: option.splits cxt_entry.splits dest!: wf_env_lookup)

lemma var_unbound_sound: "fmlookup \<rho> x = Some VUnbound \<Longrightarrow> sound_expr \<rho> (ExprVar x) (Aborts NameError)"
  by (rule sound_exprI)
     (auto simp: var_scheme_def scheme_of_name_def entry_of_def resolve_name_def
      split: option.splits cxt_entry.splits dest!: wf_env_lookup wf_unbound_ty wf_unbound_scheme)

lemma literal_sound: "sound_expr \<rho> (ExprLiteral l) (Val (VLit l))"
  by (rule sound_expr_synthI) (auto simp: var_scheme_None intro: ValLit ValLitFloat split: lit.splits)

lemma lambda_sound: "sound_expr \<rho> (ExprLambda xs e) (Val Lam(\<rho>, xs, e))"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume "synth_expr \<Sigma> \<Gamma> (ExprLambda xs e) = Ok \<tau>"
  then show "wf_result (Val Lam(\<rho>, xs, e)) (inst \<eta> \<tau>)" by simp
next
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr' \<Sigma> \<Gamma> (ExprLambda xs e) \<tau> = Some (Ok ())" and "fv \<tau> \<subseteq> fst ` set \<eta>"
  then show "wf_result (Val Lam(\<rho>, xs, e)) (inst \<eta> \<tau>)"
    by (auto simp: bind_sum_def intro!: ValLambda[simplified] split: ty.splits if_splits sum.splits)
qed simp

lemma unop_sound: "sound_expr \<rho> (node e) r \<Longrightarrow> sound_expr \<rho> (ExprUnOp op e) (mlet r (unop_meaning op))"
  sorry

lemma binop_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; sound_expr \<rho> (node e') r \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprBinOp op e e') (mlet r (binop_meaning op v))"
  sorry

lemma binop_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprBinOp op e e') (Aborts \<kappa>)"
  by (rule sound_expr_synthI)
     (auto simp: bind_sum_def var_scheme_None dest: sound_expr_synth_at split: sum.splits)

lemma and_false_sound: "sound_expr \<rho> (node e) (Val false) \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Val false)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None intro: wf_lit_bool split: sum.splits)

lemma and_true_sound:
  assumes "sound_expr \<rho> (node e) (Val true)" and "sound_expr \<rho> (node e') r"
  shows "sound_expr \<rho> (ExprAnd e e') r"
proof (rule sound_expr_synthI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprAnd e e') = Ok \<tau>"
  then show "wf_result r (inst \<eta> \<tau>)"
    using sound_expr_check_at[OF assms(2), where \<tau> = "TyPrim bool"]
    by (auto simp: bind_sum_def split: sum.splits)
qed (simp_all add: var_scheme_None)

lemma and_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Aborts \<kappa>)"
  by (rule sound_expr_synthI)
     (auto simp: bind_sum_def var_scheme_None dest: bool_operand_abort split: sum.splits)

lemma and_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Aborts Excluded)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest!: bool_operand split: sum.splits)

lemma or_true_sound: "sound_expr \<rho> (node e) (Val true) \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Val true)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None intro: wf_lit_bool split: sum.splits)

lemma or_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_expr \<rho> (node e') r"
  shows "sound_expr \<rho> (ExprOr e e') r"
proof (rule sound_expr_synthI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprOr e e') = Ok \<tau>"
  then show "wf_result r (inst \<eta> \<tau>)"
    using sound_expr_check_at[OF assms(2), where \<tau> = "TyPrim bool"]
    by (auto simp: bind_sum_def split: sum.splits)
qed (simp_all add: var_scheme_None)

lemma or_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Aborts \<kappa>)"
  by (rule sound_expr_synthI)
     (auto simp: bind_sum_def var_scheme_None dest: bool_operand_abort split: sum.splits)

lemma or_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Aborts Excluded)"
  by (rule sound_expr_synthI) (auto simp: bind_sum_def var_scheme_None dest!: bool_operand split: sum.splits)

(* Synthesis of a conditional, from both branches or from one branch checked against the other *)
lemma synth_cond:
  assumes "synth_expr \<Sigma> \<Gamma> (ExprCond e1 e e2) = Ok \<tau>"
  obtains \<sigma>1 \<sigma>2 where "synth_expr_at \<Sigma> \<Gamma> e1 = Ok \<sigma>1" and "synth_expr_at \<Sigma> \<Gamma> e2 = Ok \<sigma>2" and "\<tau> = \<sigma>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<sigma>2"
    | "synth_expr_at \<Sigma> \<Gamma> e1 = Ok \<tau>" and "check_expr_at \<Sigma> \<Gamma> e2 \<tau> = Ok ()"
    | "check_expr_at \<Sigma> \<Gamma> e1 \<tau> = Ok ()" and "synth_expr_at \<Sigma> \<Gamma> e2 = Ok \<tau>"
  using assms by (auto simp: bind_sum_def split: sum.splits)

lemma cond_true_sound:
  assumes "sound_expr \<rho> (node e) (Val true)" and "sound_expr \<rho> (node e1) r"
  shows "sound_expr \<rho> (ExprCond e1 e e2) r"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and synth: "synth_expr \<Sigma> \<Gamma> (ExprCond e1 e e2) = Ok \<tau>"
  from synth show "wf_result r (inst \<eta> \<tau>)"
  proof (cases rule: synth_cond)
    case (1 \<sigma>1 \<sigma>2)
    then show ?thesis using wf_result_sub[OF sound_expr_synth_at[OF assms(2) env 1(1)] join_upper(1)] by simp
  next
    case 2
    then show ?thesis using sound_expr_synth_at[OF assms(2) env] by simp
  next
    case 3
    then show ?thesis
      using sound_expr_check_at[OF assms(2) env 3(1)] synth_at_tyvars[OF 3(2)] wf_env_tyvars[OF env]
      by (blast intro: subset_trans)
  qed
next
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr' \<Sigma> \<Gamma> (ExprCond e1 e e2) \<tau> = Some (Ok ())" and "fv \<tau> \<subseteq> fst ` set \<eta>"
  then have "check_expr_at \<Sigma> \<Gamma> e1 \<tau> = Ok ()" by (auto simp: bind_sum_def split: sum.splits)
  from \<open>\<eta> \<turnstile> \<rho> : \<Gamma>\<close> this \<open>fv \<tau> \<subseteq> fst ` set \<eta>\<close> show "wf_result r (inst \<eta> \<tau>)"
    by (rule sound_expr_check_at[OF assms(2)])
qed simp

lemma cond_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_expr \<rho> (node e2) r"
  shows "sound_expr \<rho> (ExprCond e1 e e2) r"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and synth: "synth_expr \<Sigma> \<Gamma> (ExprCond e1 e e2) = Ok \<tau>"
  from synth show "wf_result r (inst \<eta> \<tau>)"
  proof (cases rule: synth_cond)
    case (1 \<sigma>1 \<sigma>2)
    then show ?thesis using wf_result_sub[OF sound_expr_synth_at[OF assms(2) env 1(2)] join_upper(2)] by simp
  next
    case 2
    then show ?thesis
      using sound_expr_check_at[OF assms(2) env 2(2)] synth_at_tyvars[OF 2(1)] wf_env_tyvars[OF env]
      by (blast intro: subset_trans)
  next
    case 3
    then show ?thesis using sound_expr_synth_at[OF assms(2) env] by simp
  qed
next
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr' \<Sigma> \<Gamma> (ExprCond e1 e e2) \<tau> = Some (Ok ())" and "fv \<tau> \<subseteq> fst ` set \<eta>"
  then have "check_expr_at \<Sigma> \<Gamma> e2 \<tau> = Ok ()" by (auto simp: bind_sum_def split: sum.splits)
  from \<open>\<eta> \<turnstile> \<rho> : \<Gamma>\<close> this \<open>fv \<tau> \<subseteq> fst ` set \<eta>\<close> show "wf_result r (inst \<eta> \<tau>)"
    by (rule sound_expr_check_at[OF assms(2)])
qed simp

lemma cond_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) (Aborts \<kappa>)"
  by (rule sound_exprI) (auto simp: bind_sum_def dest: bool_operand_abort split: sum.splits)

lemma cond_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) (Aborts Excluded)"
  by (rule sound_exprI) (auto simp: bind_sum_def dest!: bool_operand split: sum.splits)

(* Elements of a list synthesise subtypes of the join, or check against it *)
lemma elements_join_Ok:
  assumes "elements_join \<Sigma> \<Gamma> es = Ok \<tau>" and "tyvars \<Gamma> \<subseteq> fst ` set \<eta>"
  shows "\<exists>\<tau>s. list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>) es \<tau>s"
  sorry

lemma list_synth:
  assumes "synth_expr \<Sigma> \<Gamma> (ExprList es) = Ok \<tau>" and "tyvars \<Gamma> \<subseteq> fst ` set \<eta>"
  shows "\<exists>\<tau>' \<tau>s. \<tau> = TyList \<tau>' \<and> list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s"
proof -
  from assms(1) obtain \<tau>' where "elements_join \<Sigma> \<Gamma> es = Ok \<tau>'" and "\<tau> = TyList \<tau>'"
    by (auto simp: bind_sum_def split: sum.splits)
  with elements_join_Ok[OF this(1) assms(2)] show ?thesis by blast
qed

lemma list_check:
  assumes "check_expr' \<Sigma> \<Gamma> (ExprList es) \<tau> = Some (Ok ())" and "fv \<tau> \<subseteq> fst ` set \<eta>"
  shows "\<exists>\<tau>' \<tau>s. \<tau> = TyList \<tau>' \<and> list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s"
proof -
  from assms(1) obtain \<tau>' where \<tau>: "\<tau> = TyList \<tau>'" and "all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e \<tau>') es) = Ok ()"
    by (auto split: ty.splits)
  then have "\<forall>e \<in> set es. check_expr_at \<Sigma> \<Gamma> e \<tau>' = Ok ()" by (auto dest: all_sum_map_Ok)
  with assms(2) have "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es (replicate (length es) \<tau>')"
    by (auto simp: list_all2_conv_all_nth \<tau> intro: has_type_check_at SubtyRefl)
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
    with sub show ?thesis by (blast intro: ValSub subst_subty)
  qed
  then show ?thesis by (auto intro!: ValList)
qed

lemma list_sound:
  assumes "sound_exprs \<rho> es (Val vs)"
  shows "sound_expr \<rho> (ExprList es) (Val (VList vs))"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprList es) = Ok \<tau>"
  with list_synth[OF this(2) wf_env_tyvars[OF env]] assms show "wf_result (Val (VList vs)) (inst \<eta> \<tau>)"
    by (auto intro: list_elems)
next
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr' \<Sigma> \<Gamma> (ExprList es) \<tau> = Some (Ok ())" and "fv \<tau> \<subseteq> fst ` set \<eta>"
  with list_check[OF this(2, 3)] assms show "wf_result (Val (VList vs)) (inst \<eta> \<tau>)" by (auto intro: list_elems)
qed simp

lemma list_fail_sound:
  assumes "sound_exprs \<rho> es (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprList es) (Aborts \<kappa>)"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and synth: "synth_expr \<Sigma> \<Gamma> (ExprList es) = Ok \<tau>"
  obtain \<tau>' \<tau>s where "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s"
    using list_synth[OF synth wf_env_tyvars[OF env]] by blast
  then have "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s" by (auto simp: list_all2_conv_all_nth)
  with assms env show "wf_result (Aborts \<kappa>) (inst \<eta> \<tau>)" by (auto dest: sound_exprs_abort)
next
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_expr' \<Sigma> \<Gamma> (ExprList es) \<tau> = Some (Ok ())"
    and fv: "fv \<tau> \<subseteq> fst ` set \<eta>"
  obtain \<tau>' \<tau>s where "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>') es \<tau>s"
    using list_check[OF chk fv] by blast
  then have "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s" by (auto simp: list_all2_conv_all_nth)
  with assms env show "wf_result (Aborts \<kappa>) (inst \<eta> \<tau>)" by (auto dest: sound_exprs_abort)
qed simp

(* Elements of a tuple synthesise or check against the components of its type *)
lemma tuple_typed:
  assumes "synth_expr \<Sigma> \<Gamma> (ExprTuple es) = Ok \<tau>
    \<or> check_expr' \<Sigma> \<Gamma> (ExprTuple es) \<tau> = Some (Ok ()) \<and> fv \<tau> \<subseteq> fst ` set \<eta>"
  shows "\<exists>\<tau>s. \<tau> = TyTuple \<tau>s \<and> list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s"
  using assms
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
  unfolding sound_expr_def has_type_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and "synth_expr \<Sigma> \<Gamma> (ExprTuple es) = Ok \<tau> \<or> check_expr \<Sigma> \<Gamma> (ExprTuple es) \<tau> = Ok () \<and> fv \<tau> \<subseteq> fst ` set \<eta>
         \<or> call_stmt \<Sigma> \<Gamma> (ExprTuple es) \<and> \<tau> = TyPrim object"
  then consider "synth_expr \<Sigma> \<Gamma> (ExprTuple es) = Ok \<tau>
      \<or> check_expr' \<Sigma> \<Gamma> (ExprTuple es) \<tau> = Some (Ok ()) \<and> fv \<tau> \<subseteq> fst ` set \<eta>"
    | \<sigma> where "synth_expr \<Sigma> \<Gamma> (ExprTuple es) = Ok \<sigma>" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    by (auto dest: check_expr_cases)
  then show "wf_result (Val (VTuple vs)) (inst \<eta> \<tau>)"
  proof cases
    case 1
    with tuple_typed[OF 1] assms env show ?thesis by (auto simp: sound_exprs_def ValTuple)
  next
    case 2
    with tuple_typed[of \<Gamma> es \<sigma> \<eta>] assms env have "wf_result (Val (VTuple vs)) (inst \<eta> \<sigma>)"
      by (auto simp: sound_exprs_def ValTuple)
    from this 2(2) show ?thesis by (rule wf_result_sub)
  qed
qed

lemma tuple_fail_sound:
  assumes "sound_exprs \<rho> es (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprTuple es) (Aborts \<kappa>)"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> (ExprTuple es) = Ok \<tau>"
  with tuple_typed[of \<Gamma> es \<tau> \<eta>] assms show "wf_result (Aborts \<kappa>) (inst \<eta> \<tau>)"
    by (auto dest: sound_exprs_abort)
next
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr' \<Sigma> \<Gamma> (ExprTuple es) \<tau> = Some (Ok ())" and "fv \<tau> \<subseteq> fst ` set \<eta>"
  with tuple_typed[of \<Gamma> es \<tau> \<eta>] assms show "wf_result (Aborts \<kappa>) (inst \<eta> \<tau>)"
    by (auto dest: sound_exprs_abort)
qed simp

lemma dict_sound:
  "\<lbrakk> sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Val vs) ; dict_entries vs = Some \<delta> \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprDict kes) (Val (VDict (update [] \<delta>)))"
  sorry

lemma dict_fail_sound:
  "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprDict kes) (Aborts \<kappa>)"
  sorry

lemma dict_nonstr_sound:
  "\<lbrakk> sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Val vs) ; dict_entries vs = None \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprDict kes) (Aborts Excluded)"
  sorry

lemma subscript_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; \<not> is_class v ; sound_expr \<rho> (node e') r \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprSubscript e e') (mlet r (getitem v))"
  sorry

lemma class_type_args_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VClass C)) ; type_args_of e' = Some \<psi>s \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprSubscript e e') (Val (VClass C))"
  sorry

lemma subscript_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprSubscript e e') (Aborts \<kappa>)"
  by (rule sound_expr_synthI)
     (auto simp: bind_sum_def var_scheme_None dest: sound_expr_synth_at split: sum.splits)

lemma list_comp_sound:
  "\<lbrakk> sound_quals \<rho> gs (Val \<rho>s) ; sound_comp \<rho>s e (Val vs) \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprListComp e gs) (Val (VList vs))"
  sorry

lemma list_comp_fail_quals_sound:
  "sound_quals \<rho> gs (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprListComp e gs) (Aborts \<kappa>)"
  sorry

lemma list_comp_fail_sound:
  "\<lbrakk> sound_quals \<rho> gs (Val \<rho>s) ; sound_comp \<rho>s e (Aborts \<kappa>) \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprListComp e gs) (Aborts \<kappa>)"
  sorry

lemma dict_comp_sound:
  "\<lbrakk> sound_quals \<rho> gs (Val \<rho>s) ; sound_entries \<rho>s e e' (Val \<delta>) \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprDictComp e e' gs) (Val (VDict (update [] \<delta>)))"
  sorry

lemma dict_comp_fail_quals_sound:
  "sound_quals \<rho> gs (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprDictComp e e' gs) (Aborts \<kappa>)"
  sorry

lemma dict_comp_fail_sound:
  "\<lbrakk> sound_quals \<rho> gs (Val \<rho>s) ; sound_entries \<rho>s e e' (Aborts \<kappa>) \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprDictComp e e' gs) (Aborts \<kappa>)"
  sorry

lemma attr_object_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VObject C xvs)) ; map_of xvs x = Some v \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprAttribute e x) (Val v)"
  sorry

lemma attr_object_missing_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VObject C xvs)) ; map_of xvs x = None \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprAttribute e x) (Aborts AttributeError)"
  sorry

lemma attr_module_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VModLoaded q' \<rho>')) ; fmlookup \<rho>' x = Some v \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprAttribute e x) (Val v)"
  sorry

lemma attr_module_missing_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VModLoaded q' \<rho>')) ; fmlookup \<rho>' x = None \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprAttribute e x) (Aborts AttributeError)"
  sorry

lemma attr_nonobject_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; \<not> is_object v ; \<not> is_loaded_module v \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprAttribute e x) (Aborts Excluded)"
  sorry

lemma attr_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprAttribute e x) (Aborts \<kappa>)"
  sorry

lemma call_lambda_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val Lam(\<rho>', xs, e')) ; sound_exprs \<rho> es (Val us) ; length xs = length us
   ; sound_expr (\<rho>' \<otimes> fmap_of_list (zip xs us)) (node e') r \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, [])) r"
  sorry

lemma call_lambda_arity_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val Lam(\<rho>', xs, e')) ; sound_exprs \<rho> es (Val us) ; length xs \<noteq> length us \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, [])) (Aborts TypeError)"
  sorry

lemma call_def_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val Def(\<rho>', ds, j)) ; node (ds ! j) = Def f \<alpha>s xps \<psi> s
   ; vs = map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds] ; sound_exprs \<rho> es (Val us) ; length xps = length us
   ; scope VUnbound (map fst xps) s = Some \<rho>s
   ; sound_stmt
       (\<rho>' \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) vs) \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s)
       (node s) ([], \<omega>)
   ; j < length ds \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, [])) (result_of \<omega>)"
  sorry

lemma call_def_arity_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val Def(\<rho>', ds, j)) ; node (ds ! j) = Def f \<alpha>s xps \<psi> s ; sound_exprs \<rho> es (Val us)
   ; length xps \<noteq> length us ; j < length ds \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, [])) (Aborts TypeError)"
  sorry

lemma call_prim_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VPrim f)) ; sound_exprs \<rho> es (Val us) \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, [])) (prim_meaning f us)"
  sorry

lemma call_nonfun_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; sound_exprs \<rho> es (Val us) ; \<not> is_closure v ; \<not> is_prim v ; \<not> is_class v \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, [])) (Aborts TypeError)"
  sorry

lemma call_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, kws)) (Aborts \<kappa>)"
  sorry

lemma call_fail_args_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; sound_exprs \<rho> es (Aborts \<kappa>) \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, [])) (Aborts \<kappa>)"
  sorry

lemma constr_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VClass C)) ; sound_exprs \<rho> (es @ map snd kws) (Val us)
   ; field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) = Some xus \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, kws)) (Val (VObject C xus))"
  sorry

lemma constr_arity_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VClass C)) ; sound_exprs \<rho> (es @ map snd kws) (Val us)
   ; field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) = None \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, kws)) (Aborts TypeError)"
  sorry

lemma constr_fail_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VClass C)) ; sound_exprs \<rho> (es @ map snd kws) (Aborts \<kappa>) \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, kws)) (Aborts \<kappa>)"
  sorry

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
  moreover from assms(2) env es have "wf_results r (map (inst \<eta>) \<tau>s')" by (simp add: sound_exprs_def)
  ultimately show "wf_results (mlet r (\<lambda>vs. Val (v # vs))) (map (inst \<eta>) \<tau>s)" by (cases r) (simp_all add: \<tau>s)
qed

lemma exprs_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_exprs \<rho> (e # es) (Aborts \<kappa>)"
  unfolding sound_exprs_def by (auto simp: list_all2_Cons1 dest: sound_expr_has_type_at)

subsection \<open>Statements\<close>

lemma pass_sound: "sound_stmt \<rho> StmtPass (assigns\<^sub>o \<epsilon>)"
  by (simp add: sound_stmt_def)

lemma declare_sound: "sound_stmt \<rho> (StmtDeclare x \<psi>) (assigns\<^sub>o \<epsilon>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtDeclare x \<psi>) = Ok R"
  from chk obtain \<tau> where \<tau>: "resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau>" and R: "R = Assigns\<^sub>R (fmupd x (DU \<tau>) fmempty) None"
    and "fmlookup \<Gamma> x = Some Unbound"
    by (auto simp: bind_sum_def check_unbound_def ensure_def split: sum.splits if_splits)
  with env have "fmlookup \<rho> x = Some VUnbound" by (auto dest!: wf_env_lookup wf_unbound_entry)
  moreover have "fv \<tau> \<subseteq> fst ` set \<eta>" using resolve_type_tyvars[OF \<tau>] wf_env_tyvars[OF env] by blast
  ultimately have "\<eta> \<turnstile> \<rho> : fmupd x (DU \<tau>) \<Gamma>" using env by (intro wf_env_upd_cxt) (auto intro: ValUnbound)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<epsilon>) R" by (simp add: R)
qed

lemma assign_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtAssign x \<pi> e) (mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>)))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x \<pi> e) = Ok R"
  from chk obtain \<tau> where chk_e: "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()"
    and R: "R = Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty) None" and "fv \<tau> \<subseteq> tyvars \<Gamma>"
    by (cases \<pi>)
       (auto simp: bind_sum_def check_unbound_def ensure_def
        split: sum.splits option.splits cxt_entry.splits if_splits dest: tyvars_entry resolve_type_tyvars)
  with wf_env_tyvars[OF env] have fv: "fv \<tau> \<subseteq> fst ` set \<eta>" by blast
  show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>))) R"
  proof (cases r)
    case (Val v)
    with assms env chk_e fv have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_check_at)
    then have "\<eta> \<turnstile> fmupd x v \<rho> : fmupd x (Ty \<tau>) \<Gamma>" using env fv by (intro wf_env_upd) auto
    then show ?thesis by (simp add: Val R)
  next
    case (Aborts \<kappa>)
    with assms env chk_e fv show ?thesis by (auto simp: R dest: sound_expr_check_at)
  qed
qed

(* An expression statement synthesises or is a call statement *)
lemma check_expr_stmt:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) = Ok R"
  shows "R = Assigns\<^sub>R fmempty None \<and> (\<exists>\<tau>. has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>)"
proof (cases e)
  case (At p e')
  show ?thesis
  proof (cases e')
    case (ExprCall e'' a)
    then obtain es kws where a: "a = (es, kws)" by (cases a)
    show ?thesis
      using assms
      by (cases "lambda_of (node e'') = None \<and> class_of_name \<Gamma> (node e'') = None")
         (auto simp: At ExprCall a has_type_def bind_sum_def split: sum.splits)
  qed (use assms in \<open>auto simp: At has_type_def bind_sum_def split: sum.splits\<close>)
qed

lemma expr_stmt_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtExpr e) (mlet r (\<lambda>v. assigns\<^sub>o \<epsilon>))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) = Ok R"
  from check_expr_stmt[OF chk] obtain \<tau> where R: "R = Assigns\<^sub>R fmempty None" and "has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>"
    by blast
  with assms env have "wf_result r (inst \<eta> \<tau>)" by (auto dest: sound_expr_has_type_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. assigns\<^sub>o \<epsilon>)) R" using env by (cases r) (simp_all add: R)
qed

lemma print_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtPrint e) (mlet r (\<lambda>v. ([v], Assigns \<epsilon>)))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtPrint e) = Ok R"
  then obtain \<tau> where R: "R = Assigns\<^sub>R fmempty None" and "synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau>"
    by (auto simp: bind_sum_def ensure_def split: sum.splits if_splits)
  with assms env have "wf_result r (inst \<eta> \<tau>)" by (auto dest: sound_expr_synth_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. ([v], Assigns \<epsilon>))) R" using env by (cases r) (simp_all add: R)
qed

lemma return_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtReturn (Some e)) (mlet r returns\<^sub>o)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn (Some e)) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with ret have fv: "fv \<tau> \<subseteq> fst ` set \<eta>" by simp
  from chk \<zeta> have "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()" by (auto simp: bind_sum_def split: sum.splits)
  with assms env fv have "wf_result r (inst \<eta> \<tau>)" by (auto dest: sound_expr_check_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r returns\<^sub>o) R" by (cases r) (simp_all add: \<zeta>)
qed

lemma return_none_sound: "sound_stmt \<rho> (StmtReturn None) (returns\<^sub>o (VLit LitNone))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn None) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with chk have "\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>" by (auto split: if_splits)
  then have "\<turnstile> VLit LitNone : Ty (inst \<eta> \<tau>)"
    by (intro ValSub[OF ValLit] SubtyLiteral)
       (auto dest: subst_subty[where \<tau>s = "map snd \<eta>" and \<alpha>s = "map fst \<eta>"])
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (returns\<^sub>o (VLit LitNone)) R" by (simp add: \<zeta>)
qed

lemma defs_sound:
  "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]
  \<Longrightarrow> sound_stmt \<rho> (StmtMutualRegion ds) (assigns\<^sub>o (fmap_of_list (zip (map (def_name \<circ> node) ds) vs)))"
  sorry

(* Static outcome of an assertion: a false literal returns, otherwise the condition checks as a Boolean; the
   message checks as a string *)
lemma check_assert:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R"
  shows "(node e = ExprLiteral (LitBool False) \<and> R = Returns\<^sub>R
          \<or> node e \<noteq> ExprLiteral (LitBool False) \<and> check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()
            \<and> (\<exists>r. R = Assigns\<^sub>R fmempty r))
    \<and> (\<forall>e''. e' = Some e'' \<longrightarrow> check_expr_at \<Sigma> \<Gamma> e'' (TyPrim str) = Ok ())"
  using assms by (auto simp: Let_def bind_sum_def split: sum.splits option.splits if_splits)

lemma literal_false_true: "\<rho>, ExprLiteral (LitBool False) \<Rightarrow>\<^sub>e Val true \<Longrightarrow> False"
  and literal_false_abort: "\<rho>, ExprLiteral (LitBool False) \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> False"
  and literal_false_val: "\<rho>, ExprLiteral (LitBool False) \<Rightarrow>\<^sub>e Val v \<Longrightarrow> v = false"
  by (auto elim!: LiteralE)

lemma assert_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val true"
  shows "sound_stmt \<rho> (StmtAssert e None) (assigns\<^sub>o \<epsilon>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e None) = Ok R"
  from check_assert[OF chk] assms obtain r where "R = Assigns\<^sub>R fmempty r" by (auto dest: literal_false_true)
  with env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<epsilon>) R" by simp
qed

lemma assert_false_sound: "sound_stmt \<rho> (StmtAssert e None) (aborts\<^sub>o (AssertionError None))"
  by (simp add: sound_stmt_def)

lemma assert_fail_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa>" and "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_stmt \<rho> (StmtAssert e None) (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e None) = Ok R"
  from check_assert[OF chk] assms(1) have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()"
    by (auto dest: literal_false_abort)
  with assms(2) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R" by (auto dest: bool_operand_abort)
qed

lemma assert_nonbool_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val v" and "sound_expr \<rho> (node e) (Val v)" and "v \<notin> {true, false}"
  shows "sound_stmt \<rho> (StmtAssert e None) (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e None) = Ok R"
  from check_assert[OF chk] assms(1, 3) have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()"
    by (auto dest: literal_false_val)
  with assms(2, 3) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o Excluded) R" by (auto dest!: bool_operand)
qed

lemma assert_msg_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val true"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (assigns\<^sub>o \<epsilon>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert[OF chk] assms obtain r where "R = Assigns\<^sub>R fmempty r" by (auto dest: literal_false_true)
  with env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<epsilon>) R" by simp
qed

lemma assert_msg_false_sound: "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o (AssertionError (Some w)))"
  by (simp add: sound_stmt_def)

lemma assert_msg_false_fail_sound:
  assumes "sound_expr \<rho> (node e') (Aborts \<kappa>)"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert[OF chk] have "check_expr_at \<Sigma> \<Gamma> e' (TyPrim str) = Ok ()" by simp
  with assms env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R" by (auto dest: str_operand_abort)
qed

lemma assert_msg_fail_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa>" and "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert[OF chk] assms(1) have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()"
    by (auto dest: literal_false_abort)
  with assms(2) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R" by (auto dest: bool_operand_abort)
qed

lemma assert_msg_nonbool_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val v" and "sound_expr \<rho> (node e) (Val v)" and "v \<notin> {true, false}"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert[OF chk] assms(1, 3) have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()"
    by (auto dest: literal_false_val)
  with assms(2, 3) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o Excluded) R" by (auto dest!: bool_operand)
qed

lemma assert_msg_nonstr_sound:
  assumes "sound_expr \<rho> (node e') (Val v)" and "\<forall>w. v \<noteq> VLit (LitString w)"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert[OF chk] have "check_expr_at \<Sigma> \<Gamma> e' (TyPrim str) = Ok ()" by simp
  with assms env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o Excluded) R" by (auto dest!: str_operand)
qed

(* A variable bound by the static outcome of a statement is unbound or declared unassigned before it *)
lemma check_stmt_bound:
  "\<lbrakk> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r) ; fmlookup \<Delta> x = Some \<theta> \<rbrakk>
  \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))"
  sorry

(* Soundness at one branch of an if statement carries to the merge of the branches *)
lemma wf_outcome_merge_if:
  assumes "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" and "R \<in> set Rs"
    and "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and "foldr (\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }) Rs (Ok Returns\<^sub>R) = Ok R'" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
  sorry

lemma if_true_sound:
  assumes "sound_expr \<rho> (node e) (Val true)" and "sound_stmt \<rho> (node s) o"
  shows "sound_stmt \<rho> (StmtIf e s elifs else') o"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  from chk obtain Rs where Rs: "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and R: "foldr (\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> (set (declares (StmtIf e s elifs else'))) R R' }) Rs
             (Ok Returns\<^sub>R) = Ok R"
    by (auto simp: check_stmt_if merges_def bind_sum_def split: sum.splits)
  from Rs obtain R0 where R0: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R0" and "R0 \<in> set Rs"
    by (auto simp: bind_sum_def split: sum.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R0" using assms(2) env ret R0 by (rule sound_stmt_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using \<open>R0 \<in> set Rs\<close> Rs R env by (rule wf_outcome_merge_if)
qed

lemma if_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_elif \<rho> (elifs, else') o"
  shows "sound_stmt \<rho> (StmtIf e s elifs else') o"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  from chk obtain Rs where Rs: "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and R: "foldr (\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> (set (declares (StmtIf e s elifs else'))) R R' }) Rs
             (Ok Returns\<^sub>R) = Ok R"
    by (auto simp: check_stmt_if merges_def bind_sum_def split: sum.splits)
  from Rs obtain R0 Rs' where Rs': "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs'" and "Rs = R0 # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  with assms(2) env ret obtain R' where "R' \<in> set Rs'" and "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
    unfolding sound_elif_def by blast
  moreover from this(1) have "R' \<in> set Rs" by (simp add: \<open>Rs = R0 # Rs'\<close>)
  ultimately show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using Rs R env by (blast intro: wf_outcome_merge_if)
qed

lemma if_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def by (auto simp: check_stmt_if bind_sum_def dest: bool_operand_abort split: sum.splits)

lemma if_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def by (auto simp: check_stmt_if bind_sum_def dest!: bool_operand split: sum.splits)

lemma match_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; dispatch \<rho> v cases = Val (\<rho>', s') ; sound_stmt (\<rho> \<otimes> \<rho>') (node s') o \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (assigns\<^sub>o \<rho>' \<otimes>\<^sub>o o)"
  sorry

lemma match_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def by (auto simp: bind_sum_def dest: sound_expr_synth_at split: sum.splits)

lemma match_abort_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; dispatch \<rho> v cases = Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
  sorry

lemma seq_sound:
  assumes "sound_stmt \<rho> (node s) (us, Assigns \<rho>')" and "sound_stmt (\<rho> \<otimes> \<rho>') (node s') o"
  shows "sound_stmt \<rho> (StmtSeq s s') ((us, Assigns \<rho>') \<otimes>\<^sub>o o)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R"
  from chk obtain \<Delta> r R' where chk1: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)"
    and chk2: "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s' = Ok R'" and R: "R = Assigns\<^sub>R \<Delta> r \<otimes>\<^sub>R R'"
    by (auto simp: bind_sum_def split: sum.splits static_outcome.splits)
  have o1: "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, Assigns \<rho>') (Assigns\<^sub>R \<Delta> r)"
    using assms(1) env ret chk1 by (rule sound_stmt_at)
  then have env': "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>" and dom: "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>" by simp_all
  have o2: "wf_outcome \<eta> (\<rho> \<otimes> \<rho>') (\<Gamma> \<otimes> \<Delta>) \<zeta> o R'" using assms(2) env' ret chk2 by (rule sound_stmt_at)
  obtain vs' \<omega>' where o: "o = (vs', \<omega>')" by (cases o)
  show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> ((us, Assigns \<rho>') \<otimes>\<^sub>o o) R"
  proof (cases \<omega>')
    case (Assigns \<rho>'')
    with o2 o obtain \<Delta>' where "bindings_of R' = Some \<Delta>'" and "fmdom \<rho>'' |\<subseteq>| fmdom \<Delta>'"
      and "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' \<otimes> \<rho>'' : \<Gamma> \<otimes> \<Delta> \<otimes> \<Delta>'" by auto
    moreover from this(1) obtain r' where "R' = Assigns\<^sub>R \<Delta>' r'" by (cases R') auto
    ultimately show ?thesis using dom by (auto simp: o Assigns R intro: le_supI1 le_supI2)
  qed (use o2 in \<open>simp_all add: o\<close>)
qed

lemma seq_return_sound:
  assumes "sound_stmt \<rho> (node s) (us, Returns v)"
  shows "sound_stmt \<rho> (StmtSeq s s') (us, Returns v)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R"
  from chk obtain \<Delta> r where chk1: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)"
    by (auto simp: bind_sum_def split: sum.splits static_outcome.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, Returns v) (Assigns\<^sub>R \<Delta> r)" using assms env ret chk1 by (rule sound_stmt_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, Returns v) R" by simp
qed

lemma seq_fail_sound:
  assumes "sound_stmt \<rho> (node s) (us, Aborts\<^sub>\<omega> \<kappa>)"
  shows "sound_stmt \<rho> (StmtSeq s s') (us, Aborts\<^sub>\<omega> \<kappa>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R"
  from chk obtain \<Delta> r where chk1: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)"
    by (auto simp: bind_sum_def split: sum.splits static_outcome.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, Aborts\<^sub>\<omega> \<kappa>) (Assigns\<^sub>R \<Delta> r)" using assms env ret chk1 by (rule sound_stmt_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, Aborts\<^sub>\<omega> \<kappa>) R" by simp
qed

lemma if_none_sound: "sound_elif \<rho> ([], None) (assigns\<^sub>o \<epsilon>)"
  by (auto simp: sound_elif_def bind_sum_def)

lemma else_sound:
  assumes "sound_stmt \<rho> (node s) o"
  shows "sound_elif \<rho> ([], Some s) o"
  unfolding sound_elif_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ([], Some s)) = Ok Rs"
  from chk obtain R where "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R" and "Rs = [R]"
    by (auto simp: bind_sum_def split: sum.splits)
  with assms env ret show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" by (auto intro: sound_stmt_at)
qed

lemma elif_true_sound:
  assumes "sound_expr \<rho> (node e) (Val true)" and "sound_stmt \<rho> (node s) o"
  shows "sound_elif \<rho> ((e, s) # elifs, else') o"
  unfolding sound_elif_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>"
    and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs, else')) = Ok Rs"
  from chk obtain R Rs' where R: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R" and Rs: "Rs = R # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using assms(2) env ret R by (rule sound_stmt_at)
  then show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" by (auto simp: Rs)
qed

lemma elif_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_elif \<rho> (elifs, else') o"
  shows "sound_elif \<rho> ((e, s) # elifs, else') o"
  unfolding sound_elif_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>"
    and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs, else')) = Ok Rs"
  from chk obtain R Rs' where "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs'" and "Rs = R # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  then show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using assms(2) env ret unfolding sound_elif_def by auto
qed

lemma elif_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') (aborts\<^sub>o \<kappa>)"
  unfolding sound_elif_def by (auto simp: bind_sum_def dest: bool_operand_abort split: sum.splits)

lemma elif_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') (aborts\<^sub>o Excluded)"
  unfolding sound_elif_def by (auto simp: bind_sum_def dest!: bool_operand split: sum.splits)

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
  by (auto simp: sound_quals_def bind_sum_def dest: bool_operand_abort split: sum.splits)

lemma qual_guard_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_quals \<rho> (At p (Guard e) # gs) (Aborts Excluded)"
  by (auto simp: sound_quals_def bind_sum_def dest!: bool_operand split: sum.splits)

lemma qual_generator_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; iter v = Some us ; sound_gen \<rho> x us gs r \<rbrakk>
  \<Longrightarrow> sound_quals \<rho> (At p (Generator x e) # gs) r"
  sorry

lemma qual_generator_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_quals \<rho> (At p (Generator x e) # gs) (Aborts \<kappa>)"
  by (auto simp: sound_quals_def bind_sum_def dest: sound_expr_synth_at split: sum.splits)

lemma qual_generator_nonseq_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; iter v = None \<rbrakk>
  \<Longrightarrow> sound_quals \<rho> (At p (Generator x e) # gs) (Aborts TypeError)"
  sorry

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
  with assms(2) e have "wf_elems r (inst \<eta> \<tau>)" unfolding sound_comp_def by blast
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
  with assms(3) key e' have "wf_entries r (inst \<eta> \<tau>)" unfolding sound_entries_def by blast
  ultimately show "wf_entries (mlet r (\<lambda>\<delta>. Val ((w, v) # \<delta>))) (inst \<eta> \<tau>)" by (cases r) auto
qed

lemma entries_fail_key_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_entries (\<rho> # \<rho>s) e e' (Aborts \<kappa>)"
  unfolding sound_entries_def by (auto dest: str_operand_abort)

lemma entries_nonstr_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; \<forall>w. v \<noteq> VLit (LitString w) \<rbrakk>
  \<Longrightarrow> sound_entries (\<rho> # \<rho>s) e e' (Aborts Excluded)"
  unfolding sound_entries_def by (auto dest!: str_operand)

lemma entries_fail_value_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val (VLit (LitString w))) ; sound_expr \<rho> (node e') (Aborts \<kappa>) \<rbrakk>
  \<Longrightarrow> sound_entries (\<rho> # \<rho>s) e e' (Aborts \<kappa>)"
  unfolding sound_entries_def by (auto dest: sound_expr_has_type_at)

subsection \<open>Soundness of evaluation\<close>

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
proof (induction
    rule: eval_expr_eval_exprs_eval_stmt_eval_elif_eval_quals_eval_gen_eval_comp_eval_entries.inducts)
  case EvalVar
  then show ?case by (blast intro: var_sound)
next
  case EvalVarUnknown
  then show ?case by (blast intro: var_unknown_sound)
next
  case EvalVarUnbound
  then show ?case by (blast intro: var_unbound_sound)
next
  case EvalLiteral
  show ?case by (rule literal_sound)
next
  case EvalLambda
  show ?case by (rule lambda_sound)
next
  case EvalUnOp
  then show ?case by (blast intro: unop_sound)
next
  case EvalBinOp
  then show ?case by (blast intro: binop_sound)
next
  case EvalBinOpFail
  then show ?case by (blast intro: binop_fail_sound)
next
  case EvalAndFalse
  then show ?case by (blast intro: and_false_sound)
next
  case EvalAndTrue
  then show ?case by (blast intro: and_true_sound)
next
  case EvalAndFail
  then show ?case by (blast intro: and_fail_sound)
next
  case EvalAndNonBool
  then show ?case by (blast intro: and_nonbool_sound)
next
  case EvalOrTrue
  then show ?case by (blast intro: or_true_sound)
next
  case EvalOrFalse
  then show ?case by (blast intro: or_false_sound)
next
  case EvalOrFail
  then show ?case by (blast intro: or_fail_sound)
next
  case EvalOrNonBool
  then show ?case by (blast intro: or_nonbool_sound)
next
  case EvalCondTrue
  then show ?case by (blast intro: cond_true_sound)
next
  case EvalCondFalse
  then show ?case by (blast intro: cond_false_sound)
next
  case EvalCondFail
  then show ?case by (blast intro: cond_fail_sound)
next
  case EvalCondNonBool
  then show ?case by (blast intro: cond_nonbool_sound)
next
  case EvalList
  then show ?case by (blast intro: list_sound)
next
  case EvalListFail
  then show ?case by (blast intro: list_fail_sound)
next
  case EvalTuple
  then show ?case by (blast intro: tuple_sound)
next
  case EvalTupleFail
  then show ?case by (blast intro: tuple_fail_sound)
next
  case EvalDict
  then show ?case by (blast intro: dict_sound)
next
  case EvalDictFail
  then show ?case by (blast intro: dict_fail_sound)
next
  case EvalDictNonStr
  then show ?case by (blast intro: dict_nonstr_sound)
next
  case EvalSubscript
  then show ?case by (blast intro: subscript_sound)
next
  case EvalClassTypeArgs
  then show ?case by (blast intro: class_type_args_sound)
next
  case EvalSubscriptFail
  then show ?case by (blast intro: subscript_fail_sound)
next
  case EvalListComp
  then show ?case by (blast intro: list_comp_sound)
next
  case EvalListCompFailQuals
  then show ?case by (blast intro: list_comp_fail_quals_sound)
next
  case EvalListCompFail
  then show ?case by (blast intro: list_comp_fail_sound)
next
  case EvalDictComp
  then show ?case by (blast intro: dict_comp_sound)
next
  case EvalDictCompFailQuals
  then show ?case by (blast intro: dict_comp_fail_quals_sound)
next
  case EvalDictCompFail
  then show ?case by (blast intro: dict_comp_fail_sound)
next
  case EvalAttrObject
  then show ?case by (blast intro: attr_object_sound)
next
  case EvalAttrObjectMissing
  then show ?case by (blast intro: attr_object_missing_sound)
next
  case EvalAttrModule
  then show ?case by (blast intro: attr_module_sound)
next
  case EvalAttrModuleMissing
  then show ?case by (blast intro: attr_module_missing_sound)
next
  case EvalAttrNonObject
  then show ?case by (blast intro: attr_nonobject_sound)
next
  case EvalAttrFail
  then show ?case by (blast intro: attr_fail_sound)
next
  case EvalCallLambda
  then show ?case by (blast intro: call_lambda_sound)
next
  case EvalCallLambdaArity
  then show ?case by (blast intro: call_lambda_arity_sound)
next
  case EvalCallDef
  then show ?case by (blast intro: call_def_sound)
next
  case EvalCallDefArity
  then show ?case by (blast intro: call_def_arity_sound)
next
  case EvalCallPrim
  then show ?case by (blast intro: call_prim_sound)
next
  case EvalCallNonFun
  then show ?case by (blast intro: call_nonfun_sound)
next
  case EvalCallFail
  then show ?case by (blast intro: call_fail_sound)
next
  case EvalCallFailArgs
  then show ?case by (blast intro: call_fail_args_sound)
next
  case EvalConstr
  then show ?case by (blast intro: constr_sound)
next
  case EvalConstrArity
  then show ?case by (blast intro: constr_arity_sound)
next
  case EvalConstrFail
  then show ?case by (blast intro: constr_fail_sound)
next
  case EvalExprsNil
  show ?case by (rule exprs_nil_sound)
next
  case EvalExprsCons
  then show ?case by (blast intro: exprs_cons_sound)
next
  case EvalExprsFail
  then show ?case by (blast intro: exprs_fail_sound)
next
  case EvalPass
  show ?case by (rule pass_sound)
next
  case EvalDeclare
  show ?case by (rule declare_sound)
next
  case EvalAssign
  then show ?case by (blast intro: assign_sound)
next
  case EvalExprStmt
  then show ?case by (blast intro: expr_stmt_sound)
next
  case EvalPrint
  then show ?case by (blast intro: print_sound)
next
  case EvalReturn
  then show ?case by (blast intro: return_sound)
next
  case EvalReturnNone
  show ?case by (rule return_none_sound)
next
  case EvalDefs
  then show ?case by (blast intro: defs_sound)
next
  case EvalAssert
  then show ?case by (blast intro: assert_sound)
next
  case EvalAssertFalse
  then show ?case by (blast intro: assert_false_sound)
next
  case EvalAssertFail
  then show ?case by (blast intro: assert_fail_sound)
next
  case EvalAssertNonBool
  then show ?case by (blast intro: assert_nonbool_sound)
next
  case EvalAssertMsg
  then show ?case by (blast intro: assert_msg_sound)
next
  case EvalAssertMsgFalse
  then show ?case by (blast intro: assert_msg_false_sound)
next
  case EvalAssertMsgFalseFail
  then show ?case by (blast intro: assert_msg_false_fail_sound)
next
  case EvalAssertMsgFail
  then show ?case by (blast intro: assert_msg_fail_sound)
next
  case EvalAssertMsgNonBool
  then show ?case by (blast intro: assert_msg_nonbool_sound)
next
  case EvalAssertMsgNonStr
  then show ?case by (blast intro: assert_msg_nonstr_sound)
next
  case EvalIfTrue
  then show ?case by (blast intro: if_true_sound)
next
  case EvalIfFalse
  then show ?case by (blast intro: if_false_sound)
next
  case EvalIfFail
  then show ?case by (blast intro: if_fail_sound)
next
  case EvalIfNonBool
  then show ?case by (blast intro: if_nonbool_sound)
next
  case EvalMatch
  then show ?case by (blast intro: match_sound)
next
  case EvalMatchFail
  then show ?case by (blast intro: match_fail_sound)
next
  case EvalMatchAbort
  then show ?case by (blast intro: match_abort_sound)
next
  case EvalSeq
  then show ?case by (blast intro: seq_sound)
next
  case EvalSeqReturn
  then show ?case by (blast intro: seq_return_sound)
next
  case EvalSeqFail
  then show ?case by (blast intro: seq_fail_sound)
next
  case EvalIfNone
  show ?case by (rule if_none_sound)
next
  case EvalElse
  then show ?case by (blast intro: else_sound)
next
  case EvalElifTrue
  then show ?case by (blast intro: elif_true_sound)
next
  case EvalElifFalse
  then show ?case by (blast intro: elif_false_sound)
next
  case EvalElifFail
  then show ?case by (blast intro: elif_fail_sound)
next
  case EvalElifNonBool
  then show ?case by (blast intro: elif_nonbool_sound)
next
  case EvalQualsNil
  show ?case by (rule quals_nil_sound)
next
  case EvalQualGuardTrue
  then show ?case by (blast intro: qual_guard_true_sound)
next
  case EvalQualGuardFalse
  then show ?case by (blast intro: qual_guard_false_sound)
next
  case EvalQualGuardFail
  then show ?case by (blast intro: qual_guard_fail_sound)
next
  case EvalQualGuardNonBool
  then show ?case by (blast intro: qual_guard_nonbool_sound)
next
  case EvalQualGenerator
  then show ?case by (blast intro: qual_generator_sound)
next
  case EvalQualGeneratorFail
  then show ?case by (blast intro: qual_generator_fail_sound)
next
  case EvalQualGeneratorNonSeq
  then show ?case by (blast intro: qual_generator_nonseq_sound)
next
  case EvalGenNil
  show ?case by (rule gen_nil_sound)
next
  case EvalGenCons
  then show ?case by (blast intro: gen_cons_sound)
next
  case EvalGenFail
  then show ?case by (blast intro: gen_fail_sound)
next
  case EvalCompNil
  show ?case by (rule comp_nil_sound)
next
  case EvalCompCons
  then show ?case by (blast intro: comp_cons_sound)
next
  case EvalCompFail
  then show ?case by (blast intro: comp_fail_sound)
next
  case EvalEntriesNil
  show ?case by (rule entries_nil_sound)
next
  case EvalEntriesCons
  then show ?case by (blast intro: entries_cons_sound)
next
  case EvalEntriesFailKey
  then show ?case by (blast intro: entries_fail_key_sound)
next
  case EvalEntriesNonStr
  then show ?case by (blast intro: entries_nonstr_sound)
next
  case EvalEntriesFailValue
  then show ?case by (blast intro: entries_fail_value_sound)
qed

end

end
