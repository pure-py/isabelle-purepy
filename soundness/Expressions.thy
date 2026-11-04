(* Soundness of expression evaluation *)
theory Expressions
  imports ValueTyping
begin

(* Equations with a variable on the left in place of a constructor, which as default simp rules would unfold
   every occurrence; applied explicitly instead *)
declare check_expr.simps [simp del] callee.simps [simp del] elements_join.simps [simp del]
  check_args.simps [simp del]

(* Termination kinds ruled out by well-formedness *)
fun prevented :: "termination_kind \<Rightarrow> bool"
where
"prevented TypeError = True" |
"prevented AttributeError = True" |
"prevented NameError = True" |
"prevented Excluded = True" |
"prevented _ = False"

(* Typing of a call statement, whose result may be None *)
fun call_stmt :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> bool"
where
"call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws)) =
  (lambda_of (node e) = None \<and> class_of_name \<Gamma> (node e) = None \<and>
   (\<exists>\<sigma>. callee \<Sigma> \<Gamma> e es = Ok \<sigma> \<and> check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok ()))" |
"call_stmt \<Sigma> \<Gamma> _ = False"

(* Typing of e at \<tau>: by synthesis, by checking when \<eta> binds the type variables of \<tau>, or at type
   object if e is a call statement *)
definition has_type :: "class_table \<Rightarrow> (var \<times> ty) list \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
where
"has_type \<Sigma> \<eta> \<Gamma> e \<tau> =
  (synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr \<Sigma> \<Gamma> e \<tau> = Ok () \<and> fv \<tau> \<subseteq> fst ` set \<eta> \<or>
   call_stmt \<Sigma> \<Gamma> e \<and> \<tau> = TyPrim object)"

fun has_type_at :: "class_table \<Rightarrow> (var \<times> ty) list \<Rightarrow> cxt \<Rightarrow> expr located \<Rightarrow> ty \<Rightarrow> bool"
where
"has_type_at \<Sigma> \<eta> \<Gamma> (At p e) \<tau> = has_type \<Sigma> \<eta> \<Gamma> e \<tau>"

lemma has_type_synth_at: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<Longrightarrow> has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>"
  by (cases e) (simp add: has_type_def)

lemma has_type_check_at:
  "\<lbrakk> check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok () ; fv \<tau> \<subseteq> fst ` set \<eta> \<rbrakk> \<Longrightarrow> has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>"
  by (cases e) (simp add: has_type_def)

lemma var_scheme_None: "dotted_name e = None \<Longrightarrow> var_scheme \<Sigma> \<Gamma> e \<tau> = None"
  by (simp add: var_scheme_def scheme_of_name_def entry_of_def)

context evaluation
begin

fun wf_result :: "val result \<Rightarrow> ty \<Rightarrow> bool"
where
"wf_result (Val v) \<tau> = (\<turnstile> v : Ty \<tau>)" |
"wf_result (Aborts \<kappa>) \<tau> = (\<not> prevented \<kappa>)"

fun wf_results :: "val list result \<Rightarrow> ty list \<Rightarrow> bool"
where
"wf_results (Val vs) \<tau>s = list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s" |
"wf_results (Aborts \<kappa>) \<tau>s = (\<not> prevented \<kappa>)"

(* Soundness of one evaluation, at every context, instantiation and typing at which the construct checks *)
definition sound_expr :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"
where
"sound_expr \<rho> e r = (\<forall>\<eta> \<Gamma> \<tau>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> has_type \<Sigma> \<eta> \<Gamma> e \<tau> \<longrightarrow> wf_result r (inst \<eta> \<tau>))"

definition sound_exprs :: "env \<Rightarrow> expr located list \<Rightarrow> val list result \<Rightarrow> bool"
where
"sound_exprs \<rho> es rs =
  (\<forall>\<eta> \<Gamma> \<tau>s. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s \<longrightarrow> wf_results rs (map (inst \<eta>) \<tau>s))"

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

end

end
