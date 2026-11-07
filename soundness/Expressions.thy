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

(* Type built by union from class types and Never; closed downwards under subtyping *)
fun object_type :: "ty \<Rightarrow> bool"
where
"object_type (TyClass _ _) = True" |
"object_type (TyPrim Never) = True" |
"object_type (TyUnion \<sigma> \<tau>) = (object_type \<sigma> \<and> object_type \<tau>)" |
"object_type _ = False"

lemma object_type_subty: "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> object_type \<tau> \<Longrightarrow> object_type \<sigma>" and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) auto
qed auto

lemma object_type_subst: "object_type \<sigma> \<Longrightarrow> object_type (subst \<tau>s \<alpha>s \<sigma>)"
  by (induction \<sigma>) auto

lemma attribute_type_object_type: "attribute_type \<Sigma> \<sigma> x = Ok \<tau> \<Longrightarrow> object_type \<sigma>"
  by (induction \<Sigma> \<sigma> x arbitrary: \<tau> rule: attribute_type.induct) (auto simp: bind_sum_def split: sum.splits)

context evaluation
begin

abbreviation result_typed :: "val result \<Rightarrow> ty \<Rightarrow> bool"
where "result_typed r \<tau> \<equiv> wf_result (\<lambda>v. \<turnstile> v : Ty \<tau>) r"

abbreviation results_typed :: "val list result \<Rightarrow> ty list \<Rightarrow> bool"
where "results_typed rs \<tau>s \<equiv> wf_result (\<lambda>vs. list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s) rs"

(* Result of a dotted name, typed by the context entry to which the name resolves *)
definition sound_name :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"
where
"sound_name \<rho> e r =
  (\<forall>\<eta> \<Gamma> \<theta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> entry_of \<Gamma> e = Some \<theta> \<longrightarrow> wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r)"

definition sound_expr :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"
where
"sound_expr \<rho> e r =
  ((\<forall>\<eta> \<Gamma> \<tau>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> has_type \<Sigma> \<eta> \<Gamma> e \<tau> \<longrightarrow> result_typed r (inst \<eta> \<tau>)) \<and> sound_name \<rho> e r)"

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

lemma sound_name_None [simp]: "dotted_name e = None \<Longrightarrow> sound_name \<rho> e r"
  by (simp add: sound_name_def entry_of_def)

lemma sound_compD:
  "\<lbrakk> sound_comp \<rho>s e r ; \<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma> ; has_type_at \<Sigma> \<eta> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> wf_elems r (inst \<eta> \<tau>)"
  unfolding sound_comp_def by blast

lemma sound_entriesD:
  "\<lbrakk> sound_entries \<rho>s e e' r ; \<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()
   ; has_type_at \<Sigma> \<eta> \<Gamma> e' \<tau> \<rbrakk>
  \<Longrightarrow> wf_entries r (inst \<eta> \<tau>)"
  unfolding sound_entries_def by blast

subsection \<open>Subtyping\<close>

(* Transitivity, substitution and instantiation of fields without the well-formedness of the types they need;
   delete once the types produced by checking are shown well-formed and the hypotheses supplied *)
lemma subty_trans': "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: \<tau> ; \<Sigma> \<turnstile> \<tau> <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  sorry

lemma subst_subty': "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: subst \<tau>s \<alpha>s \<tau>"
  sorry

lemma instantiate_fields_subst':
  "map_of (instantiate (fields \<Sigma> C) \<sigma>s) x = Some \<sigma>
  \<Longrightarrow> map_of (instantiate (fields \<Sigma> C) (map (subst \<tau>s \<alpha>s) \<sigma>s)) x = Some (subst \<tau>s \<alpha>s \<sigma>)"
  sorry

lemma joins_upper: "\<tau> \<in> set \<tau>s \<Longrightarrow> \<Sigma> \<turnstile> \<tau> <: joins \<Sigma> \<tau>s"
  by (induction \<tau>s) (auto simp: joins_def intro: join_upper subty_trans')

lemma wf_val_inst_sub: "\<lbrakk> \<turnstile> v : Ty (inst \<eta> \<sigma>) ; \<Sigma> \<turnstile> \<sigma> <: \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>)"
  by (erule ValSub) (erule subst_subty')

lemma result_typed_sub: "\<lbrakk> result_typed r (inst \<eta> \<sigma>) ; \<Sigma> \<turnstile> \<sigma> <: \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  by (cases r) (auto intro: wf_val_inst_sub)

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
  and name: "sound_name \<rho> e r"
  shows "sound_expr \<rho> e r"
  unfolding sound_expr_def has_type_def using name
  by (blast dest: check_expr_cases synth check call result_typed_sub)

(* Expression with a synthesis rule only *)
lemma sound_expr_synthI:
  assumes "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
    and "\<And>\<Gamma> \<tau>. check_expr' \<Sigma> \<Gamma> e \<tau> = None" and "\<And>\<Gamma>. \<not> call_stmt \<Sigma> \<Gamma> e" and "dotted_name e = None"
  shows "sound_expr \<rho> e r"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> e = Ok \<tau>"
  then show "result_typed r (inst \<eta> \<tau>)" by (rule assms(1))
qed (simp_all add: assms(2, 3, 4))

(* Expression without a call statement rule *)
lemma sound_expr_typedI:
  assumes "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; typed_by_rule \<Sigma> \<eta> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
    and "\<And>\<Gamma>. \<not> call_stmt \<Sigma> \<Gamma> e" and "dotted_name e = None"
  shows "sound_expr \<rho> e r"
  by (rule sound_exprI) (auto intro: assms(1) simp: typed_by_rule_def assms(2, 3))

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

lemma sound_expr_name:
  "\<lbrakk> sound_expr \<rho> e r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; entry_of \<Gamma> e = Some \<theta> \<rbrakk> \<Longrightarrow> wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r"
  by (simp add: sound_expr_def sound_name_def)

lemma sound_expr_module:
  "\<lbrakk> sound_expr \<rho> e r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; dotted_name e = Some q ; lookup \<Gamma> q = Some (ModChecked q' \<Gamma>') \<rbrakk>
  \<Longrightarrow> wf_result (\<lambda>v. \<turnstile> v : ModChecked q' \<Gamma>') r"
  using sound_expr_name[of \<rho> e r \<eta> \<Gamma> "ModChecked q' \<Gamma>'"] by (simp add: entry_of_def resolve_name_def)

lemma sound_exprs_abort:
  "\<lbrakk> sound_exprs \<rho> es (Aborts \<kappa>) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s \<rbrakk> \<Longrightarrow> \<not> prevented \<kappa>"
  by (fastforce simp: sound_exprs_def)

subsection \<open>Canonical forms\<close>

lemma wf_scheme_callable:
  "\<turnstile> v : \<theta> \<Longrightarrow> \<theta> = Scheme \<pi> \<longrightarrow> (\<exists>\<alpha>s \<sigma>s \<tau>. \<pi> = TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>))"
  "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
proof (induction rule: wf_val_wf_env.inducts)
  case ValDef
  then show ?case by (auto dest!: def_signatures_callable simp: inst_entry_signature_entry)
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
  case ValDef
  then show ?case by (auto dest!: def_signatures_callable simp: inst_entry_signature_entry)
next
  case ValInst
  then show ?case by (auto dest!: wf_scheme_callable(1))
next
  case ValSub
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

lemma wf_object_type: "\<turnstile> v : \<theta> \<Longrightarrow> \<theta> = Ty \<tau> \<longrightarrow> object_type \<tau> \<longrightarrow> is_object v" "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
proof (induction arbitrary: \<tau> rule: wf_val_wf_env.inducts)
  case ValDef
  then show ?case by (auto dest!: def_signatures_callable simp: inst_entry_signature_entry)
next
  case ValInst
  then show ?case by (auto dest!: wf_scheme_callable(1))
next
  case ValSub
  then show ?case by (blast dest: object_type_subty)
next
  case ValPrim
  then show ?case by (auto dest!: prim_entry_callable)
qed auto

(* Object of class C, typed at a type above the class at type arguments typing its fields *)
lemma wf_object:
  "\<turnstile> v : \<theta> \<Longrightarrow> v = VObject C xvs \<Longrightarrow>
    (\<forall>\<tau>. \<theta> = Ty \<tau> \<longrightarrow> (\<exists>\<tau>s. C |\<in>| fmdom \<Sigma> \<and> map fst xvs = field_names \<Sigma> C
       \<and> list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s) \<and> \<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>))
    \<and> (\<forall>\<pi>. \<theta> \<noteq> Scheme \<pi>)"
  "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
proof (induction rule: wf_val_wf_env.inducts)
  case (ValObj C' xvs' \<tau>s)
  from ValObj(3) have "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs') (field_types \<Sigma> C' \<tau>s)"
    by (rule list_all2_mono) simp
  with ValObj(1, 2, 4) show ?case by (auto intro: SubtyRefl)
next
  case ValSub
  then show ?case by (blast intro: subty_trans')
qed auto

(* Field of an object of class C, typed by the field of the class at type arguments typing the fields *)
lemma object_field:
  assumes "map fst xvs = field_names \<Sigma> C" and "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s)"
    and "map_of (instantiate (fields \<Sigma> C) \<tau>s) x = Some \<tau>"
  obtains v where "map_of xvs x = Some v" and "\<turnstile> v : Ty \<tau>"
proof -
  let ?x\<tau>s = "instantiate (fields \<Sigma> C) \<tau>s"
  have "map fst xvs = map fst ?x\<tau>s" using assms(1) by (cases "fields \<Sigma> C") (simp add: field_names_def split_def)
  then have "zip (map fst xvs) (field_types \<Sigma> C \<tau>s) = ?x\<tau>s" by (simp add: field_types_def zip_map_fst_snd)
  from rel_option_map_of_zip[OF assms(2), of "map fst xvs" x, unfolded zip_map_fst_snd this] assms(3) that
  show thesis by (cases "map_of xvs x") auto
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
  moreover note class_subty_union(1)[OF TyUnion(3)[simplified] refl refl]
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "entry_of \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
    and "fmlookup \<Gamma>' x = Some \<theta>"
    by (rule entry_of_attribute)
  from sound_expr_module_env[OF assms(1) env this(1, 2)] assms(2)
  show "wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r" by auto
qed

(* Field x of an object, typed by the attribute type of x at a type of the object *)
lemma object_attribute:
  assumes "\<turnstile> VObject C xvs : Ty (inst \<eta> \<sigma>)" and "attribute_type \<Sigma> \<sigma> x = Ok \<tau>"
  obtains v where "map_of xvs x = Some v" and "\<turnstile> v : Ty (inst \<eta> \<tau>)"
proof -
  from wf_object(1)[OF assms(1) refl] obtain \<tau>s where C: "C |\<in>| fmdom \<Sigma>"
    and names: "map fst xvs = field_names \<Sigma> C"
    and fields: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s)"
    and sub: "\<Sigma> \<turnstile> TyClass C \<tau>s <: inst \<eta> \<sigma>"
    by blast
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "entry_of \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q'' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q'' \<Gamma>')"
    and x: "fmlookup \<Gamma>' x = Some \<theta>"
    by (rule entry_of_attribute)
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "entry_of \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q'' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q'' \<Gamma>')"
    and x: "fmlookup \<Gamma>' x = Some \<theta>"
    by (rule entry_of_attribute)
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and entry: "entry_of \<Gamma> (ExprAttribute e x) = Some \<theta>"
  from entry obtain q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
    and "fmlookup \<Gamma>' x = Some \<theta>"
    by (rule entry_of_attribute)
  from sound_expr_module[OF assms env this(1, 2)]
  show "wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) (Aborts \<kappa>)" by simp
qed

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
