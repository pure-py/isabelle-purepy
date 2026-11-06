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

(* Result with a value satisfying P or a termination not prevented *)
fun wf_result :: "('a \<Rightarrow> bool) \<Rightarrow> 'a result \<Rightarrow> bool"
where
"wf_result P (Val x) = P x" |
"wf_result P (Aborts \<kappa>) = (\<not> prevented \<kappa>)"

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

(* Typing of e at \<tau> by its synthesis or checking rule, when \<eta> binds the type variables of \<tau> *)
definition typed_by_rule :: "class_table \<Rightarrow> (var \<times> ty) list \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
where
"typed_by_rule \<Sigma> \<eta> \<Gamma> e \<tau> =
  (synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr' \<Sigma> \<Gamma> e \<tau> = Some (Ok ()) \<and> fv \<tau> \<subseteq> fst ` set \<eta>)"

lemma var_scheme_None: "dotted_name e = None \<Longrightarrow> var_scheme \<Sigma> \<Gamma> e \<tau> = None"
  by (simp add: var_scheme_def scheme_of_name_def entry_of_def)

lemma def_signature_callable: "def_signature \<Sigma> \<Gamma> d = Ok (TyScheme \<alpha>s \<tau>) \<Longrightarrow> \<exists>\<sigma>s \<tau>'. \<tau> = TyCallable \<sigma>s \<tau>'"
  by (cases d) (auto simp: bind_sum_def Let_def split: sum.splits option.splits)

lemma prim_entry_callable:
  "\<lbrakk> fmlookup (\<E> \<A>) q = Some \<rho> ; fmlookup \<rho> x = Some (VPrim f) ; fmlookup \<P> q = Some \<Gamma> ; fmlookup \<Gamma> x = Some \<theta> \<rbrakk>
  \<Longrightarrow> \<exists>\<sigma>s \<tau>. \<theta> = Ty (TyCallable \<sigma>s \<tau>)"
  by (auto simp: \<E>_def \<P>_def builtins_def name_of_def fmlookup_of_list split: if_splits)

context evaluation
begin

abbreviation result_typed :: "val result \<Rightarrow> ty \<Rightarrow> bool"
where "result_typed r \<tau> \<equiv> wf_result (\<lambda>v. \<turnstile> v : Ty \<tau>) r"

abbreviation results_typed :: "val list result \<Rightarrow> ty list \<Rightarrow> bool"
where "results_typed rs \<tau>s \<equiv> wf_result (\<lambda>vs. list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s) rs"

definition sound_expr :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"
where
"sound_expr \<rho> e r = (\<forall>\<eta> \<Gamma> \<tau>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> has_type \<Sigma> \<eta> \<Gamma> e \<tau> \<longrightarrow> result_typed r (inst \<eta> \<tau>))"

definition sound_exprs :: "env \<Rightarrow> expr located list \<Rightarrow> val list result \<Rightarrow> bool"
where
"sound_exprs \<rho> es rs =
  (\<forall>\<eta> \<Gamma> \<tau>s. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s \<longrightarrow> results_typed rs (map (inst \<eta>) \<tau>s))"

abbreviation wf_envs :: "(var \<times> ty) list \<Rightarrow> env list result \<Rightarrow> cxt \<Rightarrow> bool"
where "wf_envs \<eta> r \<Gamma> \<equiv> wf_result (\<lambda>\<rho>s. \<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) r"

definition sound_quals :: "env \<Rightarrow> qualifier located list \<Rightarrow> env list result \<Rightarrow> bool"
where
"sound_quals \<rho> gs r = (\<forall>\<eta> \<Gamma> \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> quals \<Sigma> \<Gamma> gs = Ok \<Delta> \<longrightarrow> wf_envs \<eta> r (\<Gamma> \<otimes> \<Delta>))"

definition sound_gen :: "env \<Rightarrow> var \<Rightarrow> val list \<Rightarrow> qualifier located list \<Rightarrow> env list result \<Rightarrow> bool"
where
"sound_gen \<rho> x us gs r =
  (\<forall>\<eta> \<Gamma> \<tau> \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> fv \<tau> \<subseteq> fst ` set \<eta> \<longrightarrow> (\<forall>u \<in> set us. \<turnstile> u : Ty (inst \<eta> \<tau>))
     \<longrightarrow> quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>
     \<longrightarrow> wf_envs \<eta> r (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>))"

abbreviation wf_elems :: "val list result \<Rightarrow> ty \<Rightarrow> bool"
where "wf_elems r \<tau> \<equiv> wf_result (\<lambda>vs. \<forall>v \<in> set vs. \<turnstile> v : Ty \<tau>) r"

definition sound_comp :: "env list \<Rightarrow> expr located \<Rightarrow> val list result \<Rightarrow> bool"
where
"sound_comp \<rho>s e r =
  (\<forall>\<eta> \<Gamma> \<tau>. (\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) \<longrightarrow> has_type_at \<Sigma> \<eta> \<Gamma> e \<tau> \<longrightarrow> wf_elems r (inst \<eta> \<tau>))"

abbreviation wf_entries :: "(str \<times> val) list result \<Rightarrow> ty \<Rightarrow> bool"
where "wf_entries r \<tau> \<equiv> wf_result (\<lambda>\<delta>. \<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau>) r"

definition sound_entries :: "env list \<Rightarrow> expr located \<Rightarrow> expr located \<Rightarrow> (str \<times> val) list result \<Rightarrow> bool"
where
"sound_entries \<rho>s e e' r =
  (\<forall>\<eta> \<Gamma> \<tau>. (\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) \<longrightarrow> check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()
     \<longrightarrow> has_type_at \<Sigma> \<eta> \<Gamma> e' \<tau> \<longrightarrow> wf_entries r (inst \<eta> \<tau>))"

subsection \<open>Subtyping\<close>

(* Transitivity and substitution without the well-formedness of the types they need; delete once the types
   produced by checking are shown well-formed and the hypotheses supplied *)
lemma subty_trans': "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: \<tau> ; \<Sigma> \<turnstile> \<tau> <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  sorry

lemma subst_subty': "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: subst \<tau>s \<alpha>s \<tau>"
  sorry

lemma joins_upper: "\<tau> \<in> set \<tau>s \<Longrightarrow> \<Sigma> \<turnstile> \<tau> <: joins \<Sigma> \<tau>s"
  by (induction \<tau>s) (auto simp: joins_def intro: join_upper subty_trans')

lemma result_typed_sub: "\<lbrakk> result_typed r (inst \<eta> \<sigma>) ; \<Sigma> \<turnstile> \<sigma> <: \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  by (cases r) (auto intro: ValSub subst_subty')

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
  assumes synth: "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  and check:
    "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr' \<Sigma> \<Gamma> e \<tau> = Some (Ok ()) ; fv \<tau> \<subseteq> fst ` set \<eta> \<rbrakk>
      \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  and call: "\<And>\<eta> \<Gamma>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; call_stmt \<Sigma> \<Gamma> e \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> (TyPrim object))"
  shows "sound_expr \<rho> e r"
  unfolding sound_expr_def has_type_def by (blast dest: check_expr_cases synth check call result_typed_sub)

(* Expression with a synthesis rule only *)
lemma sound_expr_synthI:
  assumes "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
    and "\<And>\<Gamma> \<tau>. check_expr' \<Sigma> \<Gamma> e \<tau> = None" and "\<And>\<Gamma>. \<not> call_stmt \<Sigma> \<Gamma> e"
  shows "sound_expr \<rho> e r"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> e = Ok \<tau>"
  then show "result_typed r (inst \<eta> \<tau>)" by (rule assms(1))
qed (simp_all add: assms(2, 3))

(* Expression without a call statement rule *)
lemma sound_expr_typedI:
  assumes "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; typed_by_rule \<Sigma> \<eta> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
    and "\<And>\<Gamma>. \<not> call_stmt \<Sigma> \<Gamma> e"
  shows "sound_expr \<rho> e r"
  by (rule sound_exprI) (auto intro: assms(1) simp: typed_by_rule_def assms(2))

lemma sound_expr_synth_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def has_type_def)

lemma sound_expr_check_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok () ; fv \<tau> \<subseteq> fst ` set \<eta> \<rbrakk>
  \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def has_type_def)

lemma sound_expr_has_type_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; has_type_at \<Sigma> \<eta> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def)

lemma sound_exprs_abort:
  "\<lbrakk> sound_exprs \<rho> es (Aborts \<kappa>) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s \<rbrakk> \<Longrightarrow> \<not> prevented \<kappa>"
  by (fastforce simp: sound_exprs_def)

subsection \<open>Canonical forms\<close>

lemma wf_scheme_callable:
  "\<turnstile> v : \<theta> \<Longrightarrow> \<theta> = Scheme \<pi> \<longrightarrow> (\<exists>\<alpha>s \<sigma>s \<tau>. \<pi> = TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>))"
  "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
proof (induction rule: wf_val_wf_env.inducts)
  case (ValDef \<eta> \<rho> \<Gamma> ds \<pi>s \<Delta> i \<alpha>s \<tau>)
  then have "def_signature \<Sigma> \<Gamma> (node (ds ! i)) = Ok (TyScheme \<alpha>s \<tau>)"
    by (auto dest!: those_sum_map_Ok simp: list_all2_conv_all_nth)
  then show ?case by (auto dest!: def_signature_callable simp: inst_entry_signature_entry)
next
  case ValPrim
  then show ?case by (auto dest!: prim_entry_callable)
qed auto

(* Literal at a subtype of a primitive type p other than object and Sized *)
lemma wf_prim_subtype:
  assumes "p \<notin> {object, Sized}"
  shows "\<turnstile> v : \<theta> \<Longrightarrow> \<theta> = Ty \<tau> \<longrightarrow> prim_subtype p \<tau> \<longrightarrow> (\<exists>l. v = VLit l \<and> prim_subtype p (TyLiteral l))"
    and "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
proof (induction arbitrary: \<tau> rule: wf_val_wf_env.inducts)
  case (ValDef \<eta> \<rho> \<Gamma> ds \<pi>s \<Delta> i \<alpha>s \<sigma>)
  then have "def_signature \<Sigma> \<Gamma> (node (ds ! i)) = Ok (TyScheme \<alpha>s \<sigma>)"
    by (auto dest!: those_sum_map_Ok simp: list_all2_conv_all_nth)
  then show ?case by (auto dest!: def_signature_callable simp: inst_entry_signature_entry)
next
  case (ValInst v \<alpha>s \<sigma> \<tau>s)
  then show ?case by (auto dest!: wf_scheme_callable(1))
next
  case (ValSub v \<sigma> \<tau>)
  then show ?case using prim_subtype_subty(1)[OF assms] by blast
next
  case ValPrim
  then show ?case by (auto dest!: prim_entry_callable)
qed (use assms in \<open>auto split: lit.splits\<close>)

lemma wf_prim_lit:
  assumes "\<turnstile> v : Ty \<tau>" and "\<Sigma> \<turnstile> \<tau> <: TyPrim p" and "p \<notin> {object, Sized}"
  obtains l where "v = VLit l" and "prim_subtype p (TyLiteral l)"
proof -
  have "prim_subtype p \<tau>" using prim_subtype_subty(1)[OF assms(3, 2)] by simp
  with wf_prim_subtype(1)[OF assms(3, 1)] that show ?thesis by blast
qed

lemma wf_bool: "\<lbrakk> \<turnstile> v : Ty \<tau> ; \<Sigma> \<turnstile> \<tau> <: TyPrim bool \<rbrakk> \<Longrightarrow> v = true \<or> v = false"
  by (erule wf_prim_lit) (auto elim: base_type_lit.elims)

lemma wf_str: "\<lbrakk> \<turnstile> v : Ty \<tau> ; \<Sigma> \<turnstile> \<tau> <: TyPrim str \<rbrakk> \<Longrightarrow> \<exists>w. v = VLit (LitString w)"
  by (erule wf_prim_lit) (auto elim: base_type_lit.elims)

(* Operand checked at a primitive type *)
lemma prim_operand:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr_at \<Sigma> \<Gamma> e (TyPrim p) = Ok () \<rbrakk> \<Longrightarrow> result_typed r (TyPrim p)"
  using sound_expr_check_at[where \<tau> = "TyPrim p"] by simp

lemma bool_operand:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok () \<rbrakk>
  \<Longrightarrow> v = true \<or> v = false"
  by (auto dest!: prim_operand wf_bool[OF _ SubtyRefl])

lemma str_operand:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok () \<rbrakk>
  \<Longrightarrow> \<exists>w. v = VLit (LitString w)"
  by (auto dest!: prim_operand wf_str[OF _ SubtyRefl])

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
  then show "result_typed (Val v) (inst \<eta> \<tau>)" using sub by (auto intro: ValSub subst_subty')
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
  by (rule sound_exprI)
     (auto simp: bind_sum_def intro!: ValLambda[simplified] split: ty.splits if_splits sum.splits)

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

(* Synthesis of a conditional, from both branches or from one branch checked against the other *)
lemma synth_cond:
  assumes "synth_expr \<Sigma> \<Gamma> (ExprCond e1 e e2) = Ok \<tau>"
  obtains \<sigma>1 \<sigma>2 where "synth_expr_at \<Sigma> \<Gamma> e1 = Ok \<sigma>1" and "synth_expr_at \<Sigma> \<Gamma> e2 = Ok \<sigma>2" and "\<tau> = \<sigma>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<sigma>2"
    | "synth_expr_at \<Sigma> \<Gamma> e1 = Ok \<tau>" and "check_expr_at \<Sigma> \<Gamma> e2 \<tau> = Ok ()"
    | "check_expr_at \<Sigma> \<Gamma> e1 \<tau> = Ok ()" and "synth_expr_at \<Sigma> \<Gamma> e2 = Ok \<tau>"
  using assms by (auto simp: bind_sum_def split: sum.splits)

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
qed simp

lemma cond_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_expr \<rho> (node e2) r"
  shows "sound_expr \<rho> (ExprCond e1 e e2) r"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprCond e1 e e2) \<tau>"
  from cond_typed[OF this(2) wf_env_tyvars[OF env]] show "result_typed r (inst \<eta> \<tau>)"
    by (blast intro: result_typed_sub sound_expr_has_type_at[OF assms(2) env])
qed simp

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
  let ?\<tau>s = "map (\<lambda>e. case synth_expr_at \<Sigma> \<Gamma> e of Ok \<sigma> \<Rightarrow> \<sigma> | Fail _ \<Rightarrow> \<tau>) es"
  have "has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>"
    if "e \<in> set es" and "\<sigma> = (case synth_expr_at \<Sigma> \<Gamma> e of Ok \<sigma> \<Rightarrow> \<sigma> | Fail _ \<Rightarrow> \<tau>)" for e \<sigma>
  proof (cases "synth_expr_at \<Sigma> \<Gamma> e")
    case (Inl r)
    have "(e, Fail r) \<in> set (filter (isl \<circ> snd) (zip es ?\<sigma>s))"
      using that(1) Inl by (auto simp: zip_map2 zip_same_conv_map)
    with chk have "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()" by (fastforce dest: all_sum_map_Ok)
    with Inl that(2) fv show ?thesis by (auto intro: has_type_check_at SubtyRefl)
  next
    case (Inr \<sigma>')
    then have "base_type \<sigma>' \<in> set (map (base_type \<circ> projr) (filter (Not \<circ> isl) ?\<sigma>s))"
      using that(1) by force
    then have "\<Sigma> \<turnstile> \<sigma>' <: \<tau>" unfolding \<tau> by (blast intro: base_type_upper joins_upper subty_trans')
    with Inr that(2) show ?thesis by (auto intro: has_type_synth_at)
  qed
  then have "list_all2 (\<lambda>e \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>) es ?\<tau>s"
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
    with sub show ?thesis by (blast intro: ValSub subst_subty')
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
qed simp

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
qed simp

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
qed simp

lemma tuple_fail_sound:
  assumes "sound_exprs \<rho> es (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprTuple es) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprTuple es) \<tau>"
  with tuple_typed[OF this(2)] assms show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by (auto dest: sound_exprs_abort)
qed simp

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

(* Entries of the values of a dictionary display, from values at str for the keys *)
lemma dict_entries_typed:
  "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) vs (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) \<sigma>s))
  \<Longrightarrow> \<exists>\<delta>. dict_entries vs = Some \<delta> \<and> list_all2 (\<lambda>(w, v) \<sigma>. \<turnstile> v : Ty \<sigma>) \<delta> \<sigma>s"
proof (induction \<sigma>s arbitrary: vs)
  case (Cons \<sigma> \<sigma>s)
  then obtain u v vs' where vs: "vs = u # v # vs'" and "\<turnstile> u : Ty (TyPrim str)" and "\<turnstile> v : Ty \<sigma>"
    and "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) vs' (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) \<sigma>s))"
    by (auto simp: list_all2_Cons2)
  moreover from this(2) obtain w where "u = VLit (LitString w)" using wf_str[OF _ SubtyRefl] by blast
  ultimately show ?case using Cons.IH by fastforce
qed simp

(* Values of a dictionary display with its keys and values typed *)
lemma dict_values_typed:
  assumes "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<eta> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
      kes \<sigma>s"
    and "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) r" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
  shows "results_typed r (concat (map (\<lambda>\<sigma>. [TyPrim str, inst \<eta> \<sigma>]) \<sigma>s))"
proof -
  from assms(1) have "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) (concat (map (\<lambda>(e, e'). [e, e']) kes))
                        (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) \<sigma>s))"
    by (intro list_all2_interleave) (auto elim: list_all2_mono)
  moreover have "map (inst \<eta>) (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) \<sigma>s))
                  = concat (map (\<lambda>\<sigma>. [TyPrim str, inst \<eta> \<sigma>]) \<sigma>s)"
    by (induction \<sigma>s) simp_all
  ultimately show ?thesis using assms(2, 3) unfolding sound_exprs_def by metis
qed

lemma dict_sound:
  assumes "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Val vs)" and "dict_entries vs = Some \<delta>"
  shows "sound_expr \<rho> (ExprDict kes) (Val (VDict (update [] \<delta>)))"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDict kes) \<tau>"
  from dict_typed[OF this(2) wf_env_tyvars[OF env]] obtain \<tau>' \<sigma>s where \<tau>: "\<tau> = TyDict \<tau>'"
    and kes: "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<eta> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
                kes \<sigma>s"
    by blast
  from dict_values_typed[OF kes assms(1) env]
  have "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) vs (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) (map (inst \<eta>) \<sigma>s)))"
    by (simp add: comp_def)
  from dict_entries_typed[OF this] assms(2)
  have \<delta>: "list_all2 (\<lambda>(w, v) \<sigma>. \<turnstile> v : Ty (inst \<eta> \<sigma>)) \<delta> \<sigma>s"
    by (auto simp: list_all2_map2 elim!: list_all2_mono split: prod.splits)
  have "\<turnstile> v : Ty (inst \<eta> \<tau>')" if "(w, v) \<in> set \<delta>" for w v
  proof -
    from that \<delta> obtain i where "i < length \<sigma>s" and "\<delta> ! i = (w, v)" and "\<turnstile> v : Ty (inst \<eta> (\<sigma>s ! i))"
      by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
    moreover from this(1) kes have "\<Sigma> \<turnstile> \<sigma>s ! i <: \<tau>'"
      by (cases "kes ! i") (auto simp: list_all2_conv_all_nth)
    ultimately show ?thesis by (blast intro: ValSub subst_subty')
  qed
  then have "\<forall>w v. (w, v) \<in> set (update [] \<delta>) \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>')"
    using set_update[of "[]" \<delta>] by auto
  then show "result_typed (Val (VDict (update [] \<delta>))) (inst \<eta> \<tau>)"
    by (auto simp: \<tau> intro!: ValDict distinct_update)
qed simp

lemma dict_fail_sound:
  assumes "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprDict kes) (Aborts \<kappa>)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDict kes) \<tau>"
  from dict_typed[OF this(2) wf_env_tyvars[OF env]] obtain \<tau>' \<sigma>s
    where "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<eta> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
             kes \<sigma>s"
    by blast
  from dict_values_typed[OF this assms env] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by simp
qed simp

lemma dict_nonstr_sound:
  assumes "sound_exprs \<rho> (concat (map (\<lambda>(e, e'). [e, e']) kes)) (Val vs)" and "dict_entries vs = None"
  shows "sound_expr \<rho> (ExprDict kes) (Aborts Excluded)"
proof (rule sound_expr_typedI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "typed_by_rule \<Sigma> \<eta> \<Gamma> (ExprDict kes) \<tau>"
  from dict_typed[OF this(2) wf_env_tyvars[OF env]] obtain \<tau>' \<sigma>s
    where "list_all2 (\<lambda>(e, e') \<sigma>. has_type_at \<Sigma> \<eta> \<Gamma> e (TyPrim str) \<and> has_type_at \<Sigma> \<eta> \<Gamma> e' \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>')
             kes \<sigma>s"
    by blast
  from dict_values_typed[OF this assms(1) env]
  have "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) vs (concat (map (\<lambda>\<sigma>. [TyPrim str, \<sigma>]) (map (inst \<eta>) \<sigma>s)))"
    by (simp add: comp_def)
  from dict_entries_typed[OF this] assms(2) show "result_typed (Aborts Excluded) (inst \<eta> \<tau>)" by simp
qed simp

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
