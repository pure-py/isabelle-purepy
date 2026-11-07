(* Soundness of expression evaluation *)
theory Expressions
  imports ValueTyping
begin

(* Equations with a variable on the left in place of a constructor, which as default simp rules would unfold
   every occurrence; applied explicitly instead *)
declare check_expr.simps [simp del] callee.simps [simp del] elements_join.simps [simp del]
  check_args.simps [simp del] resolve_binop_union.simps [simp del]

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

context evaluation
begin

abbreviation result_typed :: "val result \<Rightarrow> ty \<Rightarrow> bool"
where "result_typed r \<tau> \<equiv> wf_result (\<lambda>v. \<turnstile> v : Ty \<tau>) r"

abbreviation results_typed :: "val list result \<Rightarrow> ty list \<Rightarrow> bool"
where "results_typed rs \<tau>s \<equiv> wf_result (\<lambda>vs. list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s) rs"

(* Context entry named by an expression: the entry to which a dotted name resolves, or the class of a class
   applied to type arguments *)
definition expr_entry :: "cxt \<Rightarrow> expr \<Rightarrow> cxt_entry option"
where
"expr_entry \<Gamma> e =
  (case e of ExprSubscript e' _ \<Rightarrow> map_option Type (class_of_name \<Gamma> (node e')) | _ \<Rightarrow> entry_of \<Gamma> e)"

lemma expr_entry_simps [simp]:
  "expr_entry \<Gamma> (ExprVar x) = entry_of \<Gamma> (ExprVar x)"
  "expr_entry \<Gamma> (ExprAttribute e x) = entry_of \<Gamma> (ExprAttribute e x)"
  "expr_entry \<Gamma> (ExprSubscript e e') = map_option Type (class_of_name \<Gamma> (node e))"
  by (simp_all add: expr_entry_def)

lemma class_of_name_entry: "class_of_name \<Gamma> e = Some C \<Longrightarrow> expr_entry \<Gamma> e = Some (Type C)"
  by (cases e) (auto simp: class_of_name_def entry_of_def split: option.splits cxt_entry.splits)

(* Result of an expression naming a context entry, typed by the entry *)
definition sound_name :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"
where
"sound_name \<rho> e r =
  (\<forall>\<eta> \<Gamma> \<theta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> expr_entry \<Gamma> e = Some \<theta> \<longrightarrow> wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r)"

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

lemma sound_name_None [simp]:
  "\<lbrakk> dotted_name e = None ; \<forall>e' e''. e \<noteq> ExprSubscript e' e'' \<rbrakk> \<Longrightarrow> sound_name \<rho> e r"
  by (cases e) (simp_all add: sound_name_def expr_entry_def entry_of_def)

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

lemma wf_str_char: "\<turnstile> VLit (LitString c) : Ty (TyPrim str)"
  by (rule ValSub[OF wf_val_wf_env.ValLit SubtyLiteral]) (simp add: SubtyRefl)

lemma wf_int_lit: "\<turnstile> VLit (LitInt k) : Ty (TyPrim int)"
  by (rule ValSub[OF wf_val_wf_env.ValLit SubtyLiteral]) (simp add: SubtyRefl)

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

lemma inferred_type_args_fv:
  "inferred_type_args \<Sigma> \<alpha>s \<sigma>s ms = Ok \<tau>s \<Longrightarrow> \<forall>\<tau> \<in> set \<tau>s. fv \<tau> \<subseteq> \<Union> {fv \<tau>' | \<tau>'. Ok \<tau>' \<in> set ms}"
  sorry

subsection \<open>Checking\<close>

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
    and "\<forall>e' e''. e \<noteq> ExprSubscript e' e''"
  shows "sound_expr \<rho> e r"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "synth_expr \<Sigma> \<Gamma> e = Ok \<tau>"
  then show "result_typed r (inst \<eta> \<tau>)" by (rule assms(1))
qed (simp_all add: assms(2-5))

(* Expression without a call statement rule *)
lemma sound_expr_typedI:
  assumes "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; typed_by_rule \<Sigma> \<eta> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
    and "\<And>\<Gamma>. \<not> call_stmt \<Sigma> \<Gamma> e" and "dotted_name e = None" and "\<forall>e' e''. e \<noteq> ExprSubscript e' e''"
  shows "sound_expr \<rho> e r"
  by (rule sound_exprI) (auto intro: assms(1) simp: typed_by_rule_def assms(2-4))

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
  "\<lbrakk> sound_expr \<rho> e r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; expr_entry \<Gamma> e = Some \<theta> \<rbrakk> \<Longrightarrow> wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r"
  by (simp add: sound_expr_def sound_name_def)

lemma expr_entry_dotted: "dotted_name e = Some q \<Longrightarrow> expr_entry \<Gamma> e = entry_of \<Gamma> e"
  by (cases e) simp_all

lemma sound_expr_module:
  "\<lbrakk> sound_expr \<rho> e r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; dotted_name e = Some q ; lookup \<Gamma> q = Some (ModChecked q' \<Gamma>') \<rbrakk>
  \<Longrightarrow> wf_result (\<lambda>v. \<turnstile> v : ModChecked q' \<Gamma>') r"
  using sound_expr_name[of \<rho> e r \<eta> \<Gamma> "ModChecked q' \<Gamma>'"]
  by (simp add: expr_entry_dotted entry_of_def resolve_name_def)

(* Class named by an expression, as the value of the expression *)
lemma sound_expr_class:
  assumes "sound_expr \<rho> e (Val v)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "expr_entry \<Gamma> e = Some (Type C)"
  shows "v = VClass C"
  using sound_expr_name[OF assms] by (auto dest: wf_type_entry)

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

(* Typing of a value at \<sigma> by the typing rule for its form, with its components typed *)
fun intro_typed :: "val \<Rightarrow> ty \<Rightarrow> bool"
where
"intro_typed (VLit l) \<sigma> = (\<sigma> = TyLiteral l \<or> (\<exists>x. l = LitFloat x) \<and> \<sigma> = TyPrim float)" |
"intro_typed (VList vs) \<sigma> = (\<exists>\<tau>. \<sigma> = TyList \<tau> \<and> (\<forall>v \<in> set vs. \<turnstile> v : Ty \<tau>))" |
"intro_typed (VTuple vs) \<sigma> = (\<exists>\<tau>s. \<sigma> = TyTuple \<tau>s \<and> list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s)" |
"intro_typed (VDict \<delta>) \<sigma> =
  (\<exists>\<tau>. \<sigma> = TyDict \<tau> \<and> (\<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau>) \<and> distinct (map fst \<delta>))" |
"intro_typed (VObject C xvs) \<sigma> =
  (\<exists>\<tau>s. \<sigma> = TyClass C \<tau>s \<and> C |\<in>| fmdom \<Sigma> \<and> map fst xvs = field_names \<Sigma> C
     \<and> list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s))" |
"intro_typed Lam(\<rho>, xs, e) \<sigma> =
  (\<exists>\<eta> \<Gamma> \<sigma>s \<tau> \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<and> length xs = length \<sigma>s \<and> params_cxt xs \<sigma>s = Ok \<Delta>
     \<and> check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau> = Ok () \<and> fv (TyCallable \<sigma>s \<tau>) \<subseteq> fst ` set \<eta>
     \<and> \<sigma> = inst \<eta> (TyCallable \<sigma>s \<tau>))" |
"intro_typed Def(\<rho>, ds, i) \<sigma> =
  (\<exists>\<eta> \<Gamma> \<pi>s \<alpha>s \<sigma>s \<tau> \<tau>s. \<eta> \<turnstile> \<rho> : \<Gamma>
     \<and> those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s
     \<and> all_sum
         (map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))))
           ds \<pi>s) = Ok ()
     \<and> (\<forall>\<pi> \<in> set \<pi>s. fv_scheme \<pi> \<subseteq> fst ` set \<eta>)
     \<and> (\<forall>d \<in> set ds. case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {})
     \<and> i < length ds \<and> \<pi>s ! i = TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>)
     \<and> length \<tau>s = length \<alpha>s \<and> (\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' = {})
     \<and> \<sigma> = subst \<tau>s \<alpha>s (inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) (TyCallable \<sigma>s \<tau>)))" |
"intro_typed (VPrim f) \<sigma> =
  ((\<exists>\<A> q \<rho> x \<Gamma>. fmlookup (\<E> \<A>) q = Some \<rho> \<and> fmlookup \<rho> x = Some (VPrim f) \<and> fmlookup \<P> q = Some \<Gamma>
      \<and> fmlookup \<Gamma> x = Some (Ty \<sigma>))
   \<and> (\<exists>\<sigma>s \<tau>. \<sigma> = TyCallable \<sigma>s \<tau>))" |
"intro_typed v \<sigma> = False"

lemma intro_def_wf:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s"
    and "all_sum
           (map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))))
             ds \<pi>s) = Ok ()"
    and "\<forall>\<pi> \<in> set \<pi>s. fv_scheme \<pi> \<subseteq> fst ` set \<eta>"
    and "\<forall>d \<in> set ds. case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}"
    and "i < length ds" and "\<pi>s ! i = TyScheme \<alpha>s \<tau>" and "length \<tau>s = length \<alpha>s" and "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' = {}"
  shows "\<turnstile> Def(\<rho>, ds, i) : Ty (subst \<tau>s \<alpha>s (inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) \<tau>))"
proof -
  have def: "\<turnstile> Def(\<rho>, ds, i) : inst_entry \<eta> (signature_entry (TyScheme \<alpha>s \<tau>))"
    by (rule wf_val_wf_env.ValDef[OF assms(1, 2) refl assms(3-7)])
  show ?thesis
  proof (cases "\<alpha>s = []")
    case True
    with def assms(8) show ?thesis by simp
  next
    case False
    with def have "\<turnstile> Def(\<rho>, ds, i) : Scheme (TyScheme \<alpha>s (inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) \<tau>))"
      by (simp add: inst_entry_signature_entry)
    from wf_val_wf_env.ValInst[OF this assms(8, 9)] show ?thesis .
  qed
qed

lemma intro_typed_wf: "intro_typed v \<sigma> \<Longrightarrow> \<turnstile> v : Ty \<sigma>"
proof (cases v)
  case (VLamClosure \<rho> xs e)
  then show "intro_typed v \<sigma> \<Longrightarrow> \<turnstile> v : Ty \<sigma>" by (auto intro: wf_val_wf_env.ValLambda[simplified])
next
  case (VDefClosure \<rho> ds i)
  then show "intro_typed v \<sigma> \<Longrightarrow> \<turnstile> v : Ty \<sigma>"
    by (clarsimp simp only: intro_typed.simps) (rule intro_def_wf, assumption+)
next
  case (VPrim f)
  then show "intro_typed v \<sigma> \<Longrightarrow> \<turnstile> v : Ty \<sigma>" by (auto intro: wf_val_wf_env.ValPrim)
qed (auto intro: wf_val_wf_env.ValLit wf_val_wf_env.ValLitFloat wf_val_wf_env.ValList wf_val_wf_env.ValTuple
     wf_val_wf_env.ValDict wf_val_wf_env.ValObj)

lemma intro_typed_nonunion: "intro_typed v \<sigma> \<Longrightarrow> \<not> is_union \<sigma> \<and> \<sigma> \<noteq> TyPrim Never"
  by (cases v) auto

lemma intro_witness: "intro_typed v \<sigma> \<Longrightarrow> \<exists>\<sigma>'. intro_typed v \<sigma>' \<and> \<Sigma> \<turnstile> \<sigma>' <: \<sigma>"
  by (blast intro: SubtyRefl)

lemma intro_witness_ty:
  "intro_typed v \<sigma> \<Longrightarrow> \<forall>\<tau>. Ty \<sigma> = Ty \<tau> \<longrightarrow> (\<exists>\<sigma>'. intro_typed v \<sigma>' \<and> \<Sigma> \<turnstile> \<sigma>' <: \<tau>)"
  by (auto intro: SubtyRefl)

(* Value typed at a scheme, typed by the typing rule for its form at any instance of the scheme *)
lemma wf_scheme_intro:
  "\<turnstile> v : \<theta> \<Longrightarrow> \<theta> = Scheme (TyScheme \<alpha>s \<sigma>) \<Longrightarrow> length \<tau>s = length \<alpha>s \<Longrightarrow> \<forall>\<tau> \<in> set \<tau>s. fv \<tau> = {}
    \<Longrightarrow> intro_typed v (subst \<tau>s \<alpha>s \<sigma>)"
  "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
proof (induction arbitrary: \<alpha>s \<sigma> \<tau>s rule: wf_val_wf_env.inducts)
  case (ValDef \<eta> \<rho> \<Gamma> ds \<pi>s \<Delta> i \<alpha>s' \<tau>)
  have "\<exists>\<sigma>s \<tau>'. \<tau> = TyCallable \<sigma>s \<tau>'" using ValDef by (blast intro: def_signatures_callable)
  then obtain \<sigma>s \<tau>' where \<tau>: "\<tau> = TyCallable \<sigma>s \<tau>'" by blast
  from ValDef(10) have "\<alpha>s' = \<alpha>s" and "\<sigma> = inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) \<tau>"
    by (auto simp: inst_entry_signature_entry split: if_splits)
  with ValDef \<tau> show ?case by simp blast
next
  case ValPrim
  then show ?case by (auto dest: prim_entry_callable)
qed auto

(* Value typed by the typing rule for its form at a type below any type at which it is typed *)
lemma wf_val_intro:
  "\<turnstile> v : \<theta> \<Longrightarrow> \<forall>\<tau>. \<theta> = Ty \<tau> \<longrightarrow> (\<exists>\<sigma>. intro_typed v \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>)"
  "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
proof (induction rule: wf_val_wf_env.inducts)
  case (ValLit l)
  show ?case by (auto intro!: exI[of _ "TyLiteral l"] SubtyRefl)
next
  case (ValLitFloat x)
  show ?case by (auto intro!: exI[of _ "TyPrim float"] SubtyRefl)
next
  case (ValList vs \<tau>)
  then have "intro_typed (VList vs) (TyList \<tau>)" by auto
  then show ?case by (rule intro_witness_ty)
next
  case (ValTuple vs \<tau>s)
  then have "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s" by (rule list_all2_mono) simp
  then have "intro_typed (VTuple vs) (TyTuple \<tau>s)" by simp
  then show ?case by (rule intro_witness_ty)
next
  case (ValDict \<delta> \<tau>)
  then have "intro_typed (VDict \<delta>) (TyDict \<tau>)" by auto
  then show ?case by (rule intro_witness_ty)
next
  case (ValLambda \<eta> \<rho> \<Gamma> xs \<sigma>s \<Delta> e \<tau>)
  then have "intro_typed Lam(\<rho>, xs, e) (inst \<eta> (TyCallable \<sigma>s \<tau>))" by (simp only: intro_typed.simps) blast
  then show ?case by (rule intro_witness_ty)
next
  case (ValDef \<eta> \<rho> \<Gamma> ds \<pi>s \<Delta> i \<alpha>s \<tau>)
  have "\<exists>\<sigma>s \<tau>'. \<tau> = TyCallable \<sigma>s \<tau>'" using ValDef by (blast intro: def_signatures_callable)
  then obtain \<sigma>s \<tau>' where \<tau>: "\<tau> = TyCallable \<sigma>s \<tau>'" by blast
  show ?case
  proof (intro allI impI)
    fix \<tau>''
    assume "inst_entry \<eta> (signature_entry (TyScheme \<alpha>s \<tau>)) = Ty \<tau>''"
    then have \<alpha>s: "\<alpha>s = []" and "\<tau>'' = inst \<eta> \<tau>" by (auto simp: inst_entry_signature_entry split: if_splits)
    with ValDef \<tau> have "intro_typed Def(\<rho>, ds, i) \<tau>''"
      by (simp only: intro_typed.simps)
         (rule exI[of _ \<eta>], rule exI[of _ \<Gamma>], rule exI[of _ \<pi>s], rule exI[of _ "[]"], rule exI[of _ \<sigma>s],
          rule exI[of _ \<tau>'], rule exI[of _ "[]"], simp)
    then show "\<exists>\<sigma>. intro_typed Def(\<rho>, ds, i) \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>''" by (rule intro_witness)
  qed
next
  case (ValInst v \<alpha>s \<sigma> \<tau>s)
  from wf_scheme_intro(1)[OF ValInst(1) refl ValInst(3, 4)] have "intro_typed v (subst \<tau>s \<alpha>s \<sigma>)" .
  then show ?case by (rule intro_witness_ty)
next
  case (ValObj C xvs \<tau>s)
  from ValObj(3) have "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s)"
    by (rule list_all2_mono) simp
  with ValObj(1, 2) have "intro_typed (VObject C xvs) (TyClass C \<tau>s)" by simp
  then show ?case by (rule intro_witness_ty)
next
  case (ValSub v \<sigma> \<tau>)
  then show ?case by (blast intro: subty_trans')
next
  case ValPrim
  from prim_entry_callable[OF ValPrim] ValPrim show ?case by auto (blast intro: SubtyRefl)
qed auto

(* Object of class C, typed at a type above the class at type arguments typing its fields *)
lemma wf_object:
  assumes "\<turnstile> VObject C xvs : Ty \<tau>"
  obtains \<tau>s where "C |\<in>| fmdom \<Sigma>" and "map fst xvs = field_names \<Sigma> C"
    and "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s)" and "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>"
  using wf_val_intro(1)[OF assms] that by auto

lemma wf_val_union:
  assumes "\<turnstile> v : Ty (TyUnion \<sigma> \<sigma>')"
  shows "\<turnstile> v : Ty \<sigma> \<or> \<turnstile> v : Ty \<sigma>'"
proof -
  from wf_val_intro(1)[OF assms] obtain \<tau> where intro: "intro_typed v \<tau>" and sub: "\<Sigma> \<turnstile> \<tau> <: TyUnion \<sigma> \<sigma>'"
    by blast
  from nonunion_subty_union(1)[OF sub refl] intro_typed_nonunion[OF intro] show ?thesis
    by (auto intro: ValSub[OF intro_typed_wf[OF intro]])
qed

lemma wf_list:
  assumes "\<turnstile> v : Ty (TyList \<tau>)"
  obtains vs where "v = VList vs" and "\<forall>u \<in> set vs. \<turnstile> u : Ty \<tau>"
proof -
  from wf_val_intro(1)[OF assms] obtain \<sigma> where intro: "intro_typed v \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: TyList \<tau>"
    by blast
  from subty_list_inv(1)[OF sub refl] intro_typed_nonunion[OF intro] obtain \<sigma>' where \<sigma>: "\<sigma> = TyList \<sigma>'"
    and sub': "\<Sigma> \<turnstile> \<sigma>' <: \<tau>"
    by blast
  from intro \<sigma> have "\<exists>vs. v = VList vs \<and> (\<forall>u \<in> set vs. \<turnstile> u : Ty \<sigma>')" by (cases v) auto
  then show thesis using that ValSub[OF _ sub'] by blast
qed

lemma wf_tuple:
  assumes "\<turnstile> v : Ty (TyTuple \<tau>s)"
  obtains vs where "v = VTuple vs" and "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s"
proof -
  from wf_val_intro(1)[OF assms] obtain \<sigma> where intro: "intro_typed v \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: TyTuple \<tau>s"
    by blast
  from subty_tuple_inv(1)[OF sub refl] intro_typed_nonunion[OF intro] obtain \<sigma>s where \<sigma>: "\<sigma> = TyTuple \<sigma>s"
    and sub': "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s"
    by blast
  from intro \<sigma> obtain vs where v: "v = VTuple vs" and vs: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<sigma>s"
    by (cases v) auto
  have "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s"
    by (rule list_all2_trans[OF _ vs sub'[unfolded subtys_list_all2]]) (rule ValSub)
  with v that show thesis by blast
qed

lemma wf_dict:
  assumes "\<turnstile> v : Ty (TyDict \<tau>)"
  obtains \<delta> where "v = VDict \<delta>"
proof -
  from wf_val_intro(1)[OF assms] obtain \<sigma> where intro: "intro_typed v \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: TyDict \<tau>"
    by blast
  from subty_dict_inv(1)[OF sub refl] intro_typed_nonunion[OF intro] obtain \<sigma>' where "\<sigma> = TyDict \<sigma>'"
    by blast
  with intro that show thesis by (cases v) auto
qed

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

lemma wf_int: "\<lbrakk> \<turnstile> v : Ty \<tau> ; \<Sigma> \<turnstile> \<tau> <: TyPrim int \<rbrakk> \<Longrightarrow> \<exists>n. v = VLit (LitInt n)"
  by (erule wf_prim_lit) (auto elim: base_type_lit.elims)

lemma wf_float:
  "\<lbrakk> \<turnstile> v : Ty \<tau> ; \<Sigma> \<turnstile> \<tau> <: TyPrim float \<rbrakk> \<Longrightarrow> (\<exists>n. v = VLit (LitInt n)) \<or> (\<exists>x. v = VLit (LitFloat x))"
  by (erule wf_prim_lit) (auto elim: base_type_lit.elims)

lemma wf_int_float: "\<turnstile> VLit (LitInt k) : Ty (TyPrim float)"
  by (rule ValSub[OF wf_int_lit SubtyIntFloat])

lemma wf_lit: "\<turnstile> v : Ty (TyLiteral l) \<Longrightarrow> v = VLit l"
proof -
  assume "\<turnstile> v : Ty (TyLiteral l)"
  from wf_val_intro(1)[OF this] obtain \<sigma> where intro: "intro_typed v \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: TyLiteral l"
    by blast
  from subty_literal_inv(1)[OF sub refl] intro_typed_nonunion[OF intro] have "\<sigma> = TyLiteral l" by blast
  with intro show "v = VLit l" by (cases v) auto
qed

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

lemma entry_of_expr_entry: "entry_of \<Gamma> e = Some \<theta> \<Longrightarrow> expr_entry \<Gamma> e = Some \<theta>"
  by (cases e) (simp_all add: entry_of_def)

lemma constructor_class_entry: "constructor_class \<Sigma> \<Gamma> e = Some m \<Longrightarrow> \<exists>C. expr_entry \<Gamma> (node e) = Some (Type C)"
  by (auto simp: constructor_class_def split: option.splits expr.splits if_splits dest: class_of_name_entry)

lemma callee_entry:
  "callee \<Sigma> \<Gamma> e es = Ok \<sigma> \<Longrightarrow> (\<exists>\<pi>. expr_entry \<Gamma> (node e) = Some (Scheme \<pi>)) \<or> synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
  by (auto simp: callee.simps scheme_of_name_def split: option.splits cxt_entry.splits
      dest!: entry_of_expr_entry)

(* Callee of a call, a lambda or typed as a class name, a name bound at a scheme or by synthesis *)
lemma call_callee_typed:
  assumes "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, kws)) \<tau>"
  shows "(\<exists>xs e'. lambda_of (node e) = Some (xs, e')) \<or> (\<exists>C. expr_entry \<Gamma> (node e) = Some (Type C))
    \<or> (\<exists>\<sigma>. callee \<Sigma> \<Gamma> e es = Ok \<sigma>)"
proof (cases "lambda_of (node e)")
  case None
  show ?thesis
  proof (cases "constructor_class \<Sigma> \<Gamma> e")
    case (Some m)
    then show ?thesis by (blast dest: constructor_class_entry)
  next
    case c: None
    with None assms show ?thesis
      by (auto simp: has_type_def check_expr.simps bind_sum_def ensure_def split: sum.splits)
  qed
qed auto

(* Entry of a name in a typed environment, with free type variables bound by the instantiation *)
lemma wf_env_resolve:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; lookup \<Gamma> q = Some \<theta> ; \<theta> \<noteq> TypeVar \<rbrakk>
  \<Longrightarrow> (\<exists>v. resolve \<rho> q = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>) \<and> fv_entry \<theta> \<subseteq> fst ` set \<eta>"
proof (induction q arbitrary: \<theta>)
  case (Simple x)
  then show ?case using wf_env_tyvars[OF Simple(1)] tyvars_entry[of \<Gamma> x \<theta>] by (auto dest: wf_env_lookup)
next
  case (Qualified q x)
  from Qualified(3) obtain q' \<Gamma>' where q: "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')" and x: "fmlookup \<Gamma>' x = Some \<theta>"
    by (auto split: option.splits cxt_entry.splits)
  from Qualified(1)[OF Qualified(2) q] obtain v where "resolve \<rho> q = Some v" and "\<turnstile> v : ModChecked q' \<Gamma>'"
    by auto
  moreover from this(2) obtain \<rho>' where "v = VModLoaded q' \<rho>'" and "[] \<turnstile> \<rho>' : \<Gamma>'" by (auto dest: wf_mod_checked)
  moreover from module_member[OF this(2) x Qualified(4)] obtain v' where "fmlookup \<rho>' x = Some v'"
    and "\<turnstile> v' : \<theta>" and "fv_entry \<theta> = {}"
    by blast
  ultimately show ?case by (simp add: inst_entry_closed)
qed

lemma expr_entry_fv:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "entry_of \<Gamma> e = Some \<theta>"
  shows "fv_entry \<theta> \<subseteq> fst ` set \<eta>"
proof -
  from assms(2) obtain q where "resolve_name \<Gamma> q = Some \<theta>" by (auto simp: entry_of_def bind_eq_Some_conv)
  from wf_env_resolve[OF assms(1) resolve_name_lookup[OF this] resolve_name_TypeVar[OF this]] show ?thesis
    by simp
qed

lemma lookup_scheme:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "lookup \<Gamma> q = Some (Scheme \<pi>)"
  shows "callable_scheme \<pi>"
proof (cases q)
  case (Simple x)
  with assms show ?thesis by (auto dest: wf_env_scheme)
next
  case (Qualified q' x)
  with assms(2) obtain q'' \<Gamma>' where q': "lookup \<Gamma> q' = Some (ModChecked q'' \<Gamma>')"
    and x: "fmlookup \<Gamma>' x = Some (Scheme \<pi>)"
    by (auto split: option.splits cxt_entry.splits)
  from wf_env_resolve[OF assms(1) q'] obtain v where "\<turnstile> v : ModChecked q'' \<Gamma>'" by auto
  then obtain \<rho>' where "[] \<turnstile> \<rho>' : \<Gamma>'" by (auto dest: wf_mod_checked)
  from wf_env_scheme[OF this x] show ?thesis .
qed

(* Value of the callee of a call, typed by the type of the callee, with its free type variables bound *)
lemma callee_value:
  assumes "sound_expr \<rho> (node e) (Val v)" and env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "callee \<Sigma> \<Gamma> e es = Ok \<sigma>"
  shows "\<turnstile> v : Ty (inst \<eta> \<sigma>)" and "fv \<sigma> \<subseteq> fst ` set \<eta>"
proof -
  have "\<turnstile> v : Ty (inst \<eta> \<sigma>) \<and> fv \<sigma> \<subseteq> fst ` set \<eta>"
  proof (cases "scheme_of_name \<Gamma> (node e)")
    case None
    with assms(3) have synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" by (simp add: callee.simps)
    with sound_expr_synth_at[OF assms(1) env this] synth_at_tyvars[OF synth] wf_env_tyvars[OF env] show ?thesis
      by auto
  next
    case (Some \<pi>)
    then have entry: "entry_of \<Gamma> (node e) = Some (Scheme \<pi>)"
      by (auto simp: scheme_of_name_def split: option.splits cxt_entry.splits)
    then obtain q where "resolve_name \<Gamma> q = Some (Scheme \<pi>)" by (auto simp: entry_of_def bind_eq_Some_conv)
    from lookup_scheme[OF env resolve_name_lookup[OF this]] obtain \<alpha>s \<sigma>s \<sigma>'
      where \<pi>: "\<pi> = TyScheme \<alpha>s (TyCallable \<sigma>s \<sigma>')"
      by (auto elim: callable_scheme.elims)
    with Some assms(3) obtain \<tau>s where \<tau>s: "inferred_type_args \<Sigma> \<alpha>s \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
      and \<sigma>: "\<sigma> = subst \<tau>s \<alpha>s (TyCallable \<sigma>s \<sigma>')"
      by (auto simp: callee.simps bind_sum_def split: sum.splits)
    from sound_expr_name[OF assms(1) env entry_of_expr_entry[OF entry]] \<pi>
    have v: "\<turnstile> v : Scheme (TyScheme \<alpha>s (inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) (TyCallable \<sigma>s \<sigma>')))"
      by simp
    have len: "length \<tau>s = length \<alpha>s" using \<tau>s by (rule inferred_type_args_length)
    have "\<Union> {fv \<tau>' | \<tau>'. Ok \<tau>' \<in> set (map (synth_expr_at \<Sigma> \<Gamma>) es)} \<subseteq> tyvars \<Gamma>"
    proof
      fix \<alpha>
      assume "\<alpha> \<in> \<Union> {fv \<tau>' | \<tau>'. Ok \<tau>' \<in> set (map (synth_expr_at \<Sigma> \<Gamma>) es)}"
      then obtain \<tau>' e' where "\<alpha> \<in> fv \<tau>'" and "Ok \<tau>' = synth_expr_at \<Sigma> \<Gamma> e'" by auto
      with synth_at_tyvars[OF this(2)[symmetric]] show "\<alpha> \<in> tyvars \<Gamma>" by blast
    qed
    with inferred_type_args_fv[OF \<tau>s] wf_env_tyvars[OF env] have fv_\<tau>s: "\<forall>\<tau> \<in> set \<tau>s. fv \<tau> \<subseteq> fst ` set \<eta>"
      by blast
    have closed: "\<forall>\<tau> \<in> set (map (inst \<eta>) \<tau>s). fv \<tau> = {}"
    proof
      fix \<tau>'
      assume "\<tau>' \<in> set (map (inst \<eta>) \<tau>s)"
      then obtain \<tau> where "\<tau> \<in> set \<tau>s" and "\<tau>' = inst \<eta> \<tau>" by auto
      with fv_\<tau>s show "fv \<tau>' = {}" by (simp add: inst_closed[OF wf_env_closed[OF env]])
    qed
    from wf_val_wf_env.ValInst[OF v _ closed] len have "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      unfolding \<sigma> by (simp only: inst_subst[OF wf_env_closed[OF env] len] length_map)
    moreover have "fv (TyCallable \<sigma>s \<sigma>') - set \<alpha>s \<subseteq> fst ` set \<eta>" using expr_entry_fv[OF env entry] \<pi> by simp
    with fv_subst_minus[OF len, of "TyCallable \<sigma>s \<sigma>'"] fv_\<tau>s have "fv \<sigma> \<subseteq> fst ` set \<eta>" unfolding \<sigma> by blast
    ultimately show ?thesis by blast
  qed
  then show "\<turnstile> v : Ty (inst \<eta> \<sigma>)" and "fv \<sigma> \<subseteq> fst ` set \<eta>" by simp_all
qed

(* Callable typing a callee value at the type of the callee, with the arguments checked against its parameter
   types *)
lemma synth_call_callable:
  "\<lbrakk> synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau> ; \<turnstile> v : Ty (inst \<eta> \<sigma>) \<rbrakk>
  \<Longrightarrow> \<exists>\<sigma>s \<tau>'. \<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>')) \<and> check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()
      \<and> \<Sigma> \<turnstile> \<tau>' <: \<tau> \<and> fv (TyCallable \<sigma>s \<tau>') \<subseteq> fv \<sigma>"
proof (induction \<sigma> arbitrary: \<tau>)
  case (TyUnion \<sigma> \<sigma>')
  from TyUnion(3) obtain \<tau>' \<tau>'' where \<tau>': "synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau>'"
    and \<tau>'': "synth_call \<Sigma> \<Gamma> e \<sigma>' kws es = Ok \<tau>''" and \<tau>: "\<tau> = \<tau>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>''"
    by (auto simp: bind_sum_def split: sum.splits)
  from wf_val_union[of v "inst \<eta> \<sigma>" "inst \<eta> \<sigma>'"] TyUnion(4)
  have "\<turnstile> v : Ty (inst \<eta> \<sigma>) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>')" by simp
  then show ?case
  proof
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    from TyUnion(1)[OF \<tau>' this] obtain \<sigma>s \<tau>0 where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>0))"
      and "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()" and "\<Sigma> \<turnstile> \<tau>0 <: \<tau>'" and "fv (TyCallable \<sigma>s \<tau>0) \<subseteq> fv \<sigma>"
      by blast
    then show ?case
      unfolding \<tau> by (intro exI[of _ \<sigma>s] exI[of _ \<tau>0]) (auto intro: subty_trans'[OF _ join_upper(1)])
  next
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>')"
    from TyUnion(2)[OF \<tau>'' this] obtain \<sigma>s \<tau>0 where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>0))"
      and "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()" and "\<Sigma> \<turnstile> \<tau>0 <: \<tau>''" and "fv (TyCallable \<sigma>s \<tau>0) \<subseteq> fv \<sigma>'"
      by blast
    then show ?case
      unfolding \<tau> by (intro exI[of _ \<sigma>s] exI[of _ \<tau>0]) (auto intro: subty_trans'[OF _ join_upper(2)])
  qed
next
  case (TyCallable \<sigma>s \<tau>')
  then show ?case by (auto simp: bind_sum_def ensure_def split: sum.splits if_splits intro: SubtyRefl)
qed simp_all

lemma check_call_stmt_callable:
  "\<lbrakk> check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok () ; \<turnstile> v : Ty (inst \<eta> \<sigma>) \<rbrakk>
  \<Longrightarrow> \<exists>\<sigma>s \<tau>'. \<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>')) \<and> check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()
      \<and> fv (TyCallable \<sigma>s \<tau>') \<subseteq> fv \<sigma>"
proof (induction \<sigma>)
  case (TyUnion \<sigma> \<sigma>')
  from TyUnion(3) have a: "check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok ()"
    and b: "check_call_stmt \<Sigma> \<Gamma> e \<sigma>' kws es = Ok ()"
    by (auto simp: bind_sum_def split: sum.splits)
  from wf_val_union[of v "inst \<eta> \<sigma>" "inst \<eta> \<sigma>'"] TyUnion(4)
  have "\<turnstile> v : Ty (inst \<eta> \<sigma>) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>')" by simp
  then show ?case
  proof
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    from TyUnion(1)[OF a this] obtain \<sigma>s \<tau>0 where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>0))"
      and "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()" and "fv (TyCallable \<sigma>s \<tau>0) \<subseteq> fv \<sigma>"
      by blast
    then show ?case by (intro exI[of _ \<sigma>s] exI[of _ \<tau>0]) auto
  next
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>')"
    from TyUnion(2)[OF b this] obtain \<sigma>s \<tau>0 where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>0))"
      and "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()" and "fv (TyCallable \<sigma>s \<tau>0) \<subseteq> fv \<sigma>'"
      by blast
    then show ?case by (intro exI[of _ \<sigma>s] exI[of _ \<tau>0]) auto
  qed
next
  case (TyCallable \<sigma>s \<tau>)
  show ?case
  proof (cases "\<tau> = TyPrim NoneType")
    case True
    with TyCallable show ?thesis by (intro exI[of _ \<sigma>s] exI[of _ \<tau>]) auto
  next
    case False
    from TyCallable(3) have "do { synth_call \<Sigma> \<Gamma> e (TyCallable \<sigma>s \<tau>) kws es; Ok () } = Ok ()"
      by (simp only: check_call_stmt_synth[OF False])
    then obtain \<tau>' where "synth_call \<Sigma> \<Gamma> e (TyCallable \<sigma>s \<tau>) kws es = Ok \<tau>'"
      by (cases "synth_call \<Sigma> \<Gamma> e (TyCallable \<sigma>s \<tau>) kws es") (simp_all add: bind_sum_def)
    from synth_call_callable[OF this TyCallable(4)] show ?thesis by blast
  qed
qed (auto simp: bind_sum_def split: sum.splits)

(* Value typed at a callable type, typed by the rule for its form at a callable type below it *)
lemma wf_callable:
  assumes "\<turnstile> v : Ty (TyCallable \<sigma>s \<tau>)"
  obtains \<sigma>s' \<tau>' where "intro_typed v (TyCallable \<sigma>s' \<tau>')" and "\<Sigma> \<turnstile> \<sigma>s [<:] \<sigma>s'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
proof -
  from wf_val_intro(1)[OF assms] obtain \<sigma> where intro: "intro_typed v \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: TyCallable \<sigma>s \<tau>"
    by blast
  from subty_callable_inv(1)[OF sub refl] intro_typed_nonunion[OF intro] intro that show thesis by blast
qed

lemma intro_callable_value: "intro_typed v (TyCallable \<sigma>s \<tau>) \<Longrightarrow> is_closure v \<or> is_prim v"
  by (cases v) auto

(* Call through a typed callee: by synthesis at a subtype, or as a call statement *)
lemma call_typed_callee:
  assumes "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, kws)) \<tau>" and "lambda_of (node e) = None"
    and "constructor_class \<Sigma> \<Gamma> e = None"
  obtains (synth) \<sigma> \<tau>' where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" and "synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau>'"
      and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
    | (stmt) \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" and "check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok ()"
      and "\<tau> = TyPrim object"
proof -
  from assms(2, 3) have synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) =
    do { \<sigma> \<leftarrow> callee \<Sigma> \<Gamma> e es; synth_call \<Sigma> \<Gamma> e \<sigma> kws es }" by simp
  from assms(2) have check': "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = None" by simp
  have "\<exists>\<tau>'. synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>' \<and> \<Sigma> \<turnstile> \<tau>' <: \<tau>"
    if "check_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = Ok ()"
    using that check'
    by (auto simp del: synth_expr.simps simp: check_expr.simps[of \<Sigma> \<Gamma> "ExprCall e (es, kws)" \<tau>] ensure_def
        bind_sum_def split: sum.splits if_splits)
  with assms(1) consider (s) \<tau>' where "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
    | (c) "call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws))" and "\<tau> = TyPrim object"
    unfolding has_type_def by (blast intro: SubtyRefl)
  then show thesis
  proof cases
    case s
    from s(1) synth have "(callee \<Sigma> \<Gamma> e es \<bind> (\<lambda>\<sigma>. synth_call \<Sigma> \<Gamma> e \<sigma> kws es)) = Ok \<tau>'" by simp
    then obtain \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" and "synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau>'"
      by (auto simp: bind_sum_def split: sum.splits)
    from that(1)[OF this s(2)] show thesis .
  next
    case c
    then show thesis by (auto intro: that(2))
  qed
qed

lemma call_nonfun_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val v" and "sound_expr \<rho> (node e) (Val v)" and "\<not> is_closure v" and "\<not> is_prim v"
    and "\<not> is_class v"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (Aborts TypeError)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, [])) \<tau>"
  have noncallable: False if "callee \<Sigma> \<Gamma> e es = Ok \<sigma>"
    and "\<exists>\<sigma>s \<tau>'. \<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" for \<sigma>
  proof -
    from that(2) obtain \<sigma>s \<tau>' where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" by blast
    then obtain \<sigma>s' \<tau>'' where "intro_typed v (TyCallable \<sigma>s' \<tau>'')" by (auto elim: wf_callable)
    with assms(3, 4) show False by (auto dest: intro_callable_value)
  qed
  show "result_typed (Aborts TypeError) (inst \<eta> \<tau>)"
  proof (cases "lambda_of (node e)")
    case (Some xe)
    then obtain xs e' where "node e = ExprLambda xs e'" by (cases "node e") auto
    with assms(1, 3) show ?thesis by (auto elim: LambdaE)
  next
    case None
    show ?thesis
    proof (cases "constructor_class \<Sigma> \<Gamma> e")
      case (Some m)
      from constructor_class_entry[OF this] obtain C where "expr_entry \<Gamma> (node e) = Some (Type C)" by blast
      from sound_expr_class[OF assms(2) env this] assms(5) show ?thesis by simp
    next
      case c: None
      from typed None c show ?thesis
      proof (cases rule: call_typed_callee)
        case (synth \<sigma> \<tau>')
        from synth_call_callable[OF synth(2) callee_value(1)[OF assms(2) env synth(1)]]
        have "\<exists>\<sigma>s \<tau>''. \<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>''))" by blast
        from noncallable[OF synth(1) this] show ?thesis ..
      next
        case (stmt \<sigma>)
        from check_call_stmt_callable[OF stmt(2) callee_value(1)[OF assms(2) env stmt(1)]]
        have "\<exists>\<sigma>s \<tau>''. \<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>''))" by blast
        from noncallable[OF stmt(1) this] show ?thesis ..
      qed
    qed
  qed
qed simp

lemma check_args_typed:
  assumes "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()" and "\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> fst ` set \<eta>"
  shows "kws = []" and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s"
proof -
  from assms(1) have kws: "kws = []" and len: "length es = length \<sigma>s"
    and checked: "all_sum (map2 (check_expr_at \<Sigma> \<Gamma>) es \<sigma>s) = Ok ()"
    by (auto simp: check_args.simps bind_sum_def ensure_def split: sum.splits if_splits)
  from all_sum_map2_Ok[OF checked len] have "list_all2 (\<lambda>e \<sigma>. check_expr_at \<Sigma> \<Gamma> e \<sigma> = Ok ()) es \<sigma>s" .
  then show "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s"
    by (rule list.rel_mono_strong) (use assms(2) in \<open>auto intro: has_type_check_at\<close>)
  from kws show "kws = []" .
qed

lemma sound_exprs_typed:
  "\<lbrakk> sound_exprs \<rho> es (Val us) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s \<rbrakk>
  \<Longrightarrow> list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty (inst \<eta> \<tau>)) us \<tau>s"
  by (simp add: sound_exprs_def list.rel_map)

(* Environment of a function body: the environment of the function, with the parameters bound to the arguments *)
lemma wf_env_params:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "params_cxt xs \<sigma>s = Ok \<Delta>" and "length xs = length \<sigma>s"
    and "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty (inst \<eta> \<sigma>)) vs \<sigma>s" and "\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> fst ` set \<eta>"
  shows "\<eta> \<turnstile> \<rho> \<otimes> fmap_of_list (zip xs vs) : \<Gamma> \<otimes> \<Delta>"
proof -
  from assms(2) have \<Delta>: "\<Delta> = fmap_of_list (zip xs (map Ty \<sigma>s))" by (auto simp: params_cxt_def split: if_splits)
  from assms(4) have len: "length vs = length \<sigma>s" by (rule list_all2_lengthD)
  from assms(4) have typed: "list_all2 (\<lambda>v \<theta>. \<turnstile> v : inst_entry \<eta> \<theta>) vs (map Ty \<sigma>s)" by (simp add: list.rel_map)
  show ?thesis
  proof (rule wf_env_add[OF assms(1)])
    have entries: "\<exists>\<sigma> \<in> set \<sigma>s. \<theta> = Ty \<sigma>" if "fmlookup \<Delta> x = Some \<theta>" for x \<theta>
      using that by (auto simp: \<Delta> fmlookup_of_list dest!: map_of_SomeD set_zip_rightD)
    show "tyvars \<Delta> \<subseteq> fst ` set \<eta>"
      using entries assms(5) by (fastforce simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff)
    show "fmdom (fmap_of_list (zip xs vs)) |\<subseteq>| fmdom \<Delta>" using assms(3) len by (simp add: \<Delta>)
    show "\<exists>v. fmlookup (\<rho> \<otimes> fmap_of_list (zip xs vs)) x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
      if "fmlookup \<Delta> x = Some \<theta>" and "\<theta> \<noteq> TypeVar" for x \<theta>
    proof -
      from rel_option_map_of_zip[OF typed, of xs x] that(1) obtain v where "map_of (zip xs vs) x = Some v"
        and "\<turnstile> v : inst_entry \<eta> \<theta>"
        by (cases "map_of (zip xs vs) x") (auto simp: \<Delta> fmlookup_of_list)
      then show ?thesis using fmdomI[of "fmap_of_list (zip xs vs)" x v] by (simp add: fmlookup_of_list)
    qed
    show "callable_scheme \<pi>" if "fmlookup \<Delta> x = Some (Scheme \<pi>)" for x \<pi>
      using that by (auto simp: \<Delta> fmlookup_of_list dest!: map_of_SomeD set_zip_rightD)
  qed
qed

(* Callee typed at the type of a call through it, with the arguments typed at the parameter types *)
lemma callee_call:
  assumes "sound_expr \<rho> (node e) (Val v)" and env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and callee: "callee \<Sigma> \<Gamma> e es = Ok \<sigma>"
    and "synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau>"
  obtains \<sigma>s \<tau>' where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" and "kws = []"
    and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s" and "fv (TyCallable \<sigma>s \<tau>') \<subseteq> fst ` set \<eta>" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
proof -
  from synth_call_callable[OF assms(4) callee_value(1)[OF assms(1) env callee]] obtain \<sigma>s \<tau>'
    where v: "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" and args: "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()"
      and sub: "\<Sigma> \<turnstile> \<tau>' <: \<tau>" and fv: "fv (TyCallable \<sigma>s \<tau>') \<subseteq> fv \<sigma>"
    by blast
  from fv callee_value(2)[OF assms(1) env callee] have fv': "fv (TyCallable \<sigma>s \<tau>') \<subseteq> fst ` set \<eta>" by blast
  then have "\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> fst ` set \<eta>" by auto
  from check_args_typed[OF args this] v sub fv' that show thesis by blast
qed

lemma callee_call_stmt:
  assumes "sound_expr \<rho> (node e) (Val v)" and env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and callee: "callee \<Sigma> \<Gamma> e es = Ok \<sigma>"
    and "check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok ()"
  obtains \<sigma>s \<tau>' where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" and "kws = []"
    and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s" and "fv (TyCallable \<sigma>s \<tau>') \<subseteq> fst ` set \<eta>"
proof -
  from check_call_stmt_callable[OF assms(4) callee_value(1)[OF assms(1) env callee]] obtain \<sigma>s \<tau>'
    where v: "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" and args: "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()"
      and fv: "fv (TyCallable \<sigma>s \<tau>') \<subseteq> fv \<sigma>"
    by blast
  from fv callee_value(2)[OF assms(1) env callee] have fv': "fv (TyCallable \<sigma>s \<tau>') \<subseteq> fst ` set \<eta>" by blast
  then have "\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> fst ` set \<eta>" by auto
  from check_args_typed[OF args this] v fv' that show thesis by blast
qed

(* Call of a lambda written as the callee, with its arguments typed by synthesis and its body typed under them *)
lemma call_lambda_typed:
  assumes "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, kws)) \<tau>" and "lambda_of (node e) = Some (xs, e')"
  obtains \<tau>s \<Delta> \<tau>' where "kws = []" and "length xs = length es"
    and "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
    and "params_cxt xs \<tau>s = Ok \<Delta>" and "has_type_at \<Sigma> \<eta> (\<Gamma> \<otimes> \<Delta>) e' \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
proof -
  note result = that
  let ?args = "lambda_args e xs kws es (map (synth_expr_at \<Sigma> \<Gamma>) es)"
  have args: "kws = [] \<and> length xs = length es \<and> (\<exists>\<tau>s. those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s
    \<and> params_cxt xs \<tau>s = Ok \<Delta>)" if "?args = Ok \<Delta>" for \<Delta>
    using that by (auto simp: lambda_args_def bind_sum_def ensure_def split: sum.splits if_splits)
  have synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) =
    by_rule RuleCallLambdaSyn (do { \<Delta> \<leftarrow> ?args; synth_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' })"
    using assms(2) by simp
  have check': "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> =
    Some (by_rule RuleCallLambda (do { \<Delta> \<leftarrow> ?args; check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau> }))"
    using assms(2) by simp
  have body: thesis if "?args = Ok \<Delta>" and "has_type_at \<Sigma> \<eta> (\<Gamma> \<otimes> \<Delta>) e' \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>" for \<Delta> \<tau>'
    using args[OF that(1)] that(2, 3) by (elim conjE exE) (rule result; assumption)
  have from_synth: thesis if "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>" for \<tau>'
    using that(1) unfolding synth
    by (auto simp: bind_sum_def split: sum.splits intro: body[OF _ has_type_synth_at that(2)])
  from assms(1) consider (s) "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>"
    | (c) "check_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = Ok ()" and "fv \<tau> \<subseteq> fst ` set \<eta>"
    | (stmt) "call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws))"
    unfolding has_type_def by blast
  then show thesis
  proof cases
    case s
    then show thesis by (rule from_synth) (rule SubtyRefl)
  next
    case c
    show thesis
    proof (cases "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau>")
      case None
      with check' show thesis by simp
    next
      case (Some m)
      show thesis
      proof (cases m)
        case (Inr u)
        with Some check' obtain \<Delta> where "?args = Ok \<Delta>" and "check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau> = Ok ()"
          by (auto simp: bind_sum_def split: sum.splits)
        with c(2) show thesis by (auto intro: body has_type_check_at SubtyRefl)
      next
        case (Inl r)
        with Some c(1) obtain \<sigma> where "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<sigma>" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
          by (auto simp del: synth_expr.simps simp: check_expr.simps[of \<Sigma> \<Gamma> "ExprCall e (es, kws)" \<tau>]
              split: sum.splits if_splits)
        then show thesis by (rule from_synth)
      qed
    qed
  next
    case stmt
    with assms(2) show thesis by simp
  qed
qed

lemma intro_lambda:
  "intro_typed Lam(\<rho>, xs, e) (TyCallable \<sigma>s \<tau>) \<Longrightarrow>
   \<exists>\<eta> \<Gamma> \<sigma>s' \<tau>' \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<and> length xs = length \<sigma>s' \<and> params_cxt xs \<sigma>s' = Ok \<Delta>
     \<and> check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau>' = Ok () \<and> fv (TyCallable \<sigma>s' \<tau>') \<subseteq> fst ` set \<eta>
     \<and> \<sigma>s = map (inst \<eta>) \<sigma>s' \<and> \<tau> = inst \<eta> \<tau>'"
  by auto

lemma call_lambda_arity_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')" and "sound_expr \<rho> (node e) (Val Lam(\<rho>', xs, e'))"
    and "sound_exprs \<rho> es (Val us)" and "length xs \<noteq> length us"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (Aborts TypeError)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, [])) \<tau>"
  have arity: False if "\<turnstile> Lam(\<rho>', xs, e') : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))"
    and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s" for \<sigma>s \<tau>'
  proof -
    from that(1) obtain \<sigma>s' \<tau>'' where "intro_typed Lam(\<rho>', xs, e') (TyCallable \<sigma>s' \<tau>'')"
      and sub: "\<Sigma> \<turnstile> map (inst \<eta>) \<sigma>s [<:] \<sigma>s'"
      by (auto elim: wf_callable)
    from intro_lambda[OF this(1)] have "length xs = length \<sigma>s'" by auto
    moreover from sub have "length \<sigma>s' = length \<sigma>s" by (auto simp: subtys_list_all2 dest: list_all2_lengthD)
    moreover from sound_exprs_typed[OF assms(3) env that(2)] have "length us = length \<sigma>s"
      by (rule list_all2_lengthD)
    ultimately show False using assms(4) by simp
  qed
  show "result_typed (Aborts TypeError) (inst \<eta> \<tau>)"
  proof (cases "lambda_of (node e)")
    case (Some xe)
    then obtain xs0 e0 where lam: "lambda_of (node e) = Some (xs0, e0)" and node: "node e = ExprLambda xs0 e0"
      by (cases "node e") auto
    from typed lam obtain \<tau>s where "length xs0 = length es"
      and \<tau>s: "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
      by (rule call_lambda_typed)
    moreover from assms(1) node have "xs = xs0" by (auto elim: LambdaE)
    moreover from those_sum_map_Ok[OF \<tau>s] have "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s"
      by (rule list.rel_mono_strong) (auto intro: has_type_synth_at)
    from sound_exprs_typed[OF assms(3) env this] have "length us = length \<tau>s" by (rule list_all2_lengthD)
    moreover have "length \<tau>s = length es" using list_all2_lengthD[OF those_sum_map_Ok[OF \<tau>s]] by simp
    ultimately show ?thesis using assms(4) by simp
  next
    case None
    show ?thesis
    proof (cases "constructor_class \<Sigma> \<Gamma> e")
      case (Some m)
      from constructor_class_entry[OF this] obtain C where "expr_entry \<Gamma> (node e) = Some (Type C)" by blast
      from sound_expr_class[OF assms(2) env this] show ?thesis by simp
    next
      case c: None
      from typed None c show ?thesis
      proof (cases rule: call_typed_callee)
        case (synth \<sigma> \<tau>')
        from assms(2) env synth(1, 2) show ?thesis by (rule callee_call) (metis arity)
      next
        case (stmt \<sigma>)
        from assms(2) env stmt(1, 2) show ?thesis by (rule callee_call_stmt) (metis arity)
      qed
    qed
  qed
qed simp

lemma call_lambda_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')" and "sound_expr \<rho> (node e) (Val Lam(\<rho>', xs, e'))"
    and "sound_exprs \<rho> es (Val us)" and "length xs = length us"
    and body: "sound_expr (\<rho>' \<otimes> fmap_of_list (zip xs us)) (node e') r"
  shows "sound_expr \<rho> (ExprCall e (es, [])) r"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, [])) \<tau>"
  (* Call through a callee typed at a callable type *)
  have callable: "result_typed r (inst \<eta> \<tau>')"
    if "\<turnstile> Lam(\<rho>', xs, e') : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s"
    for \<sigma>s \<tau>'
  proof -
    from that(1) obtain \<sigma>s' \<tau>'' where "intro_typed Lam(\<rho>', xs, e') (TyCallable \<sigma>s' \<tau>'')"
      and sub: "\<Sigma> \<turnstile> map (inst \<eta>) \<sigma>s [<:] \<sigma>s'" and ret: "\<Sigma> \<turnstile> \<tau>'' <: inst \<eta> \<tau>'"
      by (auto elim: wf_callable)
    from intro_lambda[OF this(1)] obtain \<eta>' \<Gamma>' \<sigma>s'' \<tau>b \<Delta> where env': "\<eta>' \<turnstile> \<rho>' : \<Gamma>'"
      and len: "length xs = length \<sigma>s''" and \<Delta>: "params_cxt xs \<sigma>s'' = Ok \<Delta>"
      and checked: "check_expr_at \<Sigma> (\<Gamma>' \<otimes> \<Delta>) e' \<tau>b = Ok ()" and fv: "fv (TyCallable \<sigma>s'' \<tau>b) \<subseteq> fst ` set \<eta>'"
      and \<sigma>s': "\<sigma>s' = map (inst \<eta>') \<sigma>s''" and \<tau>'': "\<tau>'' = inst \<eta>' \<tau>b"
      by blast
    from sound_exprs_typed[OF assms(3) env that(2)]
    have args: "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us (map (inst \<eta>) \<sigma>s)" by (simp add: list.rel_map)
    have "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s'"
      by (rule list_all2_trans[OF _ args sub[unfolded subtys_list_all2]]) (rule ValSub)
    then have "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty (inst \<eta>' \<sigma>)) us \<sigma>s''" by (simp add: \<sigma>s' list.rel_map)
    moreover have "\<forall>\<sigma> \<in> set \<sigma>s''. fv \<sigma> \<subseteq> fst ` set \<eta>'" using fv by auto
    ultimately have "\<eta>' \<turnstile> \<rho>' \<otimes> fmap_of_list (zip xs us) : \<Gamma>' \<otimes> \<Delta>" by (rule wf_env_params[OF env' \<Delta> len])
    moreover from checked fv have "has_type_at \<Sigma> \<eta>' (\<Gamma>' \<otimes> \<Delta>) e' \<tau>b" by (auto intro: has_type_check_at)
    ultimately have "result_typed r (inst \<eta>' \<tau>b)" using body by (auto dest: sound_expr_has_type_at)
    with ret \<tau>'' show ?thesis by (cases r) (auto intro: ValSub)
  qed
  show "result_typed r (inst \<eta> \<tau>)"
  proof (cases "lambda_of (node e)")
    case (Some xe)
    then obtain xs0 e0 where lam: "lambda_of (node e) = Some (xs0, e0)" and node: "node e = ExprLambda xs0 e0"
      by (cases "node e") auto
    from assms(1) node have \<rho>': "\<rho>' = \<rho>" and xs: "xs = xs0" and e': "e' = e0" by (auto elim: LambdaE)
    from typed lam obtain \<tau>s \<Delta> \<tau>' where "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
      and \<Delta>: "params_cxt xs0 \<tau>s = Ok \<Delta>" and body_typed: "has_type_at \<Sigma> \<eta> (\<Gamma> \<otimes> \<Delta>) e0 \<tau>'"
      and sub: "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
      by (rule call_lambda_typed)
    from those_sum_map_Ok[OF this(1)] have synths: "list_all2 (\<lambda>e \<tau>. synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau>) es \<tau>s" .
    then have "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s"
      by (rule list.rel_mono_strong) (auto intro: has_type_synth_at)
    from sound_exprs_typed[OF assms(3) env this] have us: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty (inst \<eta> \<tau>)) us \<tau>s" .
    have "\<forall>\<tau> \<in> set \<tau>s. fv \<tau> \<subseteq> fst ` set \<eta>"
    proof
      fix \<tau>
      assume "\<tau> \<in> set \<tau>s"
      then obtain i where "i < length \<tau>s" and "\<tau> = \<tau>s ! i" by (auto simp: in_set_conv_nth)
      with synths have "synth_expr_at \<Sigma> \<Gamma> (es ! i) = Ok \<tau>" by (auto simp: list_all2_conv_all_nth)
      from synth_at_tyvars[OF this] wf_env_tyvars[OF env] show "fv \<tau> \<subseteq> fst ` set \<eta>" by blast
    qed
    moreover have "length xs0 = length \<tau>s" using assms(4) us xs by (auto dest: list_all2_lengthD)
    ultimately have "\<eta> \<turnstile> \<rho> \<otimes> fmap_of_list (zip xs0 us) : \<Gamma> \<otimes> \<Delta>" using wf_env_params[OF env \<Delta> _ us] by blast
    with body body_typed \<rho>' xs e' have "result_typed r (inst \<eta> \<tau>')" by (auto dest: sound_expr_has_type_at)
    then show ?thesis using sub by (rule result_typed_sub)
  next
    case None
    show ?thesis
    proof (cases "constructor_class \<Sigma> \<Gamma> e")
      case (Some m)
      from constructor_class_entry[OF this] obtain C where "expr_entry \<Gamma> (node e) = Some (Type C)" by blast
      from sound_expr_class[OF assms(2) env this] show ?thesis by simp
    next
      case c: None
      from typed None c show ?thesis
      proof (cases rule: call_typed_callee)
        case (synth \<sigma> \<tau>')
        from assms(2) env synth(1, 2) obtain \<sigma>s \<tau>'' where "\<turnstile> Lam(\<rho>', xs, e') : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>''))"
          and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s" and "\<Sigma> \<turnstile> \<tau>'' <: \<tau>'"
          by (rule callee_call)
        from callable[OF this(1, 2)] have "result_typed r (inst \<eta> \<tau>'')" .
        then have "result_typed r (inst \<eta> \<tau>')" using \<open>\<Sigma> \<turnstile> \<tau>'' <: \<tau>'\<close> by (rule result_typed_sub)
        then show ?thesis using synth(3) by (rule result_typed_sub)
      next
        case (stmt \<sigma>)
        from assms(2) env stmt(1, 2) obtain \<sigma>s \<tau>'' where "\<turnstile> Lam(\<rho>', xs, e') : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>''))"
          and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s"
          by (rule callee_call_stmt)
        from callable[OF this] have "result_typed r (inst \<eta> \<tau>'')" .
        then have "result_typed r (inst \<eta> (TyPrim object))" by (rule result_typed_sub) (rule SubtyObject)
        with stmt(3) show ?thesis by simp
      qed
    qed
  qed
qed simp

lemma iter_range:
  assumes "\<turnstile> VObject C xvs : Ty (TyClass range_class \<tau>s)"
  shows "iter (VObject C xvs) \<noteq> None"
proof -
  from assms obtain \<tau>s' where C: "C |\<in>| fmdom \<Sigma>" and names: "map fst xvs = field_names \<Sigma> C"
    and fields: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s')"
    and sub: "\<Sigma> \<turnstile> TyClass C \<tau>s' <: TyClass range_class \<tau>s"
    by (rule wf_object)
  from subty_range(1)[OF wf_class_table sub refl refl C] have range: "C = range_class" .
  with names have "map fst xvs = [var ''start'', var ''stop'']" by (simp add: range_fields)
  then obtain u u' where xvs: "xvs = [(var ''start'', u), (var ''stop'', u')]" by (auto simp: map_eq_Cons_conv)
  with fields range have "\<turnstile> u : Ty (TyPrim int)" and "\<turnstile> u' : Ty (TyPrim int)" by (simp_all add: range_fields)
  then obtain m n where "u = VLit (LitInt m)" and "u' = VLit (LitInt n)" by (blast dest: wf_int[OF _ SubtyRefl])
  with xvs range show ?thesis by simp
qed

lemma iter_sized:
  assumes "\<turnstile> v : Ty \<tau>" and "\<Sigma> \<turnstile> \<tau> <: TyPrim Sized"
  shows "iter v \<noteq> None"
proof -
  from wf_val_intro(1)[OF assms(1)] obtain \<sigma> where intro: "intro_typed v \<sigma>" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>" by blast
  from subty_trans'[OF this(2) assms(2)] have sub: "\<Sigma> \<turnstile> \<sigma> <: TyPrim Sized" .
  from subty_sized_inv(1)[OF sub refl] intro_typed_nonunion[OF intro]
  consider (sized) "sized \<sigma>" | (literal) w where "\<sigma> = TyLiteral (LitString w)"
    | (range) C \<sigma>s where "\<sigma> = TyClass C \<sigma>s" and "\<Sigma> \<turnstile> \<sigma> <: TyClass range_class []"
    | (top) "\<sigma> = TyPrim Sized"
    by blast
  then show ?thesis
  proof cases
    case sized
    with intro show ?thesis
    proof (cases v)
      case (VObject C xvs)
      with intro obtain \<tau>s where \<sigma>: "\<sigma> = TyClass C \<tau>s" by auto
      with sized have "C = range_class" and "\<tau>s = []" by (cases \<tau>s; simp)+
      with intro_typed_wf[OF intro] \<sigma> VObject have "\<turnstile> VObject C xvs : Ty (TyClass range_class [])" by simp
      then show ?thesis unfolding VObject by (rule iter_range)
    qed (auto elim: sized.elims)
  next
    case literal
    with intro show ?thesis by (cases v) auto
  next
    case (range C \<sigma>s)
    with intro obtain xvs where v: "v = VObject C xvs" by (cases v) auto
    from ValSub[OF intro_typed_wf[OF intro] range(2)] have "\<turnstile> VObject C xvs : Ty (TyClass range_class [])"
      by (simp add: v)
    then show ?thesis unfolding v by (rule iter_range)
  next
    case top
    with intro show ?thesis by (cases v) auto
  qed
qed

(* Meaning of a primitive function at arguments typed by its parameter types *)
lemma prim_meaning_typed:
  assumes "intro_typed (VPrim f) (TyCallable \<sigma>s \<tau>)" and "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s"
  shows "result_typed (prim_meaning f us) \<tau>"
proof -
  from assms(1) obtain \<A> q \<rho> x \<Gamma> where "fmlookup (\<E> \<A>) q = Some \<rho>" and "fmlookup \<rho> x = Some (VPrim f)"
    and "fmlookup \<P> q = Some \<Gamma>" and "fmlookup \<Gamma> x = Some (Ty (TyCallable \<sigma>s \<tau>))"
    by auto
  from prim_entry_types[OF this] consider
      (len) "f = PrimLen" "\<sigma>s = [TyPrim Sized]" "\<tau> = TyPrim int"
    | (round) "f = PrimRound" "\<sigma>s = [TyPrim float]" "\<tau> = TyPrim int"
    | (exit) "f = PrimExit" "\<sigma>s = [TyPrim int]" "\<tau> = TyPrim Never"
    by auto
  then show ?thesis
  proof cases
    case len
    with assms(2) obtain u where us: "us = [u]" and "\<turnstile> u : Ty (TyPrim Sized)" by (auto simp: list_all2_Cons2)
    from iter_sized[OF this(2) SubtyRefl] obtain vs where "iter u = Some vs" by auto
    with us len show ?thesis by (simp add: wf_int_lit)
  next
    case round
    with assms(2) obtain u where us: "us = [u]" and u: "\<turnstile> u : Ty (TyPrim float)" by (auto simp: list_all2_Cons2)
    from u obtain l where "u = VLit l" and "prim_subtype float (TyLiteral l)"
      by (rule wf_prim_lit[OF _ SubtyRefl]) simp
    with us round show ?thesis
      by (cases l) (auto simp: wf_int_lit split: option.splits ereal.splits)
  next
    case exit
    with assms(2) obtain u where us: "us = [u]" and u: "\<turnstile> u : Ty (TyPrim int)" by (auto simp: list_all2_Cons2)
    from wf_int[OF u SubtyRefl] us exit show ?thesis by auto
  qed
qed

lemma call_prim_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val (VPrim f)" and "sound_expr \<rho> (node e) (Val (VPrim f))"
    and "sound_exprs \<rho> es (Val us)"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (prim_meaning f us)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, [])) \<tau>"
  have callable: "result_typed (prim_meaning f us) (inst \<eta> \<tau>')"
    if "\<turnstile> VPrim f : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s" for \<sigma>s \<tau>'
  proof -
    from that(1) obtain \<sigma>s' \<tau>'' where intro: "intro_typed (VPrim f) (TyCallable \<sigma>s' \<tau>'')"
      and sub: "\<Sigma> \<turnstile> map (inst \<eta>) \<sigma>s [<:] \<sigma>s'" and ret: "\<Sigma> \<turnstile> \<tau>'' <: inst \<eta> \<tau>'"
      by (auto elim: wf_callable)
    from sound_exprs_typed[OF assms(3) env that(2)]
    have args: "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us (map (inst \<eta>) \<sigma>s)" by (simp add: list.rel_map)
    have "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s'"
      by (rule list_all2_trans[OF _ args sub[unfolded subtys_list_all2]]) (rule ValSub)
    from prim_meaning_typed[OF intro this] ret show ?thesis
      by (cases "prim_meaning f us") (auto intro: ValSub)
  qed
  show "result_typed (prim_meaning f us) (inst \<eta> \<tau>)"
  proof (cases "lambda_of (node e)")
    case (Some xe)
    then obtain xs e' where "node e = ExprLambda xs e'" by (cases "node e") auto
    with assms(1) show ?thesis by (auto elim: LambdaE)
  next
    case None
    show ?thesis
    proof (cases "constructor_class \<Sigma> \<Gamma> e")
      case (Some m)
      from constructor_class_entry[OF this] obtain C where "expr_entry \<Gamma> (node e) = Some (Type C)" by blast
      from sound_expr_class[OF assms(2) env this] show ?thesis by simp
    next
      case c: None
      from typed None c show ?thesis
      proof (cases rule: call_typed_callee)
        case (synth \<sigma> \<tau>')
        from assms(2) env synth(1, 2) obtain \<sigma>s \<tau>'' where "\<turnstile> VPrim f : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>''))"
          and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s" and sub: "\<Sigma> \<turnstile> \<tau>'' <: \<tau>'"
          by (rule callee_call)
        from callable[OF this(1, 2)] have "result_typed (prim_meaning f us) (inst \<eta> \<tau>')"
          using sub by (rule result_typed_sub)
        then show ?thesis using synth(3) by (rule result_typed_sub)
      next
        case (stmt \<sigma>)
        from assms(2) env stmt(1, 2) obtain \<sigma>s \<tau>'' where "\<turnstile> VPrim f : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>''))"
          and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s"
          by (rule callee_call_stmt)
        from callable[OF this] have "result_typed (prim_meaning f us) (inst \<eta> (TyPrim object))"
          by (rule result_typed_sub) (rule SubtyObject)
        with stmt(3) show ?thesis by simp
      qed
    qed
  qed
qed simp

lemma call_def_arity_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val Def(\<rho>', ds, j)" and "sound_expr \<rho> (node e) (Val Def(\<rho>', ds, j))"
    and "node (ds ! j) = Def f \<alpha>s xps \<psi> s" and "sound_exprs \<rho> es (Val us)" and "length xps \<noteq> length us"
    and "j < length ds"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (Aborts TypeError)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, [])) \<tau>"
  have arity: False if "\<turnstile> Def(\<rho>', ds, j) : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))"
    and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<sigma>s" for \<sigma>s \<tau>'
  proof -
    from that(1) obtain \<sigma>s' \<tau>'' where intro: "intro_typed Def(\<rho>', ds, j) (TyCallable \<sigma>s' \<tau>'')"
      and sub: "\<Sigma> \<turnstile> map (inst \<eta>) \<sigma>s [<:] \<sigma>s'"
      by (auto elim: wf_callable)
    from intro obtain \<Gamma>' \<pi>s \<alpha>s' \<sigma>sD \<tau>D \<tau>s where
      sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma>' (node d))) ds) = Ok \<pi>s"
      and \<pi>: "\<pi>s ! j = TyScheme \<alpha>s' (TyCallable \<sigma>sD \<tau>D)" and "length \<sigma>s' = length \<sigma>sD"
      by auto
    moreover from def_signatures_arity[OF sigs assms(6, 3) \<pi>] have "length \<sigma>sD = length xps" .
    moreover from sub have "length \<sigma>s' = length \<sigma>s" by (auto simp: subtys_list_all2 dest: list_all2_lengthD)
    moreover from sound_exprs_typed[OF assms(4) env that(2)] have "length us = length \<sigma>s"
      by (rule list_all2_lengthD)
    ultimately show False using assms(5) by simp
  qed
  show "result_typed (Aborts TypeError) (inst \<eta> \<tau>)"
  proof (cases "lambda_of (node e)")
    case (Some xe)
    then obtain xs e' where "node e = ExprLambda xs e'" by (cases "node e") auto
    with assms(1) show ?thesis by (auto elim: LambdaE)
  next
    case None
    show ?thesis
    proof (cases "constructor_class \<Sigma> \<Gamma> e")
      case (Some m)
      from constructor_class_entry[OF this] obtain C where "expr_entry \<Gamma> (node e) = Some (Type C)" by blast
      from sound_expr_class[OF assms(2) env this] show ?thesis by simp
    next
      case c: None
      from typed None c show ?thesis
      proof (cases rule: call_typed_callee)
        case (synth \<sigma> \<tau>')
        from assms(2) env synth(1, 2) show ?thesis by (rule callee_call) (metis arity)
      next
        case (stmt \<sigma>)
        from assms(2) env stmt(1, 2) show ?thesis by (rule callee_call_stmt) (metis arity)
      qed
    qed
  qed
qed simp

lemma call_fail_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa>" and "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprCall e (es, kws)) (Aborts \<kappa>)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, kws)) \<tau>"
  from call_callee_typed[OF typed] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)"
  proof (elim disjE exE)
    fix xs e'
    assume "lambda_of (node e) = Some (xs, e')"
    then have "node e = ExprLambda xs e'" by (cases "node e") simp_all
    with assms(1) show ?thesis by (auto elim: LambdaE)
  next
    fix C
    assume "expr_entry \<Gamma> (node e) = Some (Type C)"
    from sound_expr_name[OF assms(2) env this] show ?thesis by simp
  next
    fix \<sigma>
    assume "callee \<Sigma> \<Gamma> e es = Ok \<sigma>"
    from callee_entry[OF this] show ?thesis
      by (auto dest: sound_expr_name[OF assms(2) env] sound_expr_synth_at[OF assms(2) env])
  qed
qed simp

lemma constructor_class_Ok_entry:
  "constructor_class \<Sigma> \<Gamma> e = Some (Ok (C, explicit)) \<Longrightarrow> expr_entry \<Gamma> (node e) = Some (Type C)"
  by (drule constructor_class_Ok) (auto intro: class_of_name_entry)

(* Callee of a call, a class, which is not typed by synthesis or at a scheme *)
lemma class_callee: "\<lbrakk> sound_expr \<rho> (node e) (Val (VClass C)) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; callee \<Sigma> \<Gamma> e es = Ok \<sigma> \<rbrakk> \<Longrightarrow> False"
  using callee_value(1) wf_class_ty by blast

(* Typing of a call by synthesis, or as a call statement *)
lemma call_typed:
  assumes "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, kws)) \<tau>" and "lambda_of (node e) = None"
  obtains (synth) \<tau>' where "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
    | (stmt) \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" and "check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok ()"
proof -
  from assms(2) have check': "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = None" by simp
  have "\<exists>\<tau>'. synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>' \<and> \<Sigma> \<turnstile> \<tau>' <: \<tau>"
    if "check_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = Ok ()"
    using that check'
    by (auto simp del: synth_expr.simps simp: check_expr.simps[of \<Sigma> \<Gamma> "ExprCall e (es, kws)" \<tau>] ensure_def
        bind_sum_def split: sum.splits if_splits)
  with assms(1) consider (s) \<tau>' where "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
    | (c) "call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws))"
    unfolding has_type_def by (blast intro: SubtyRefl)
  then show thesis
  proof cases
    case s
    then show thesis by (rule that(1))
  next
    case c
    then show thesis by (auto intro: that(2))
  qed
qed

(* Type arguments of a constructor call, supplied by the callee or inferred from the arguments, over the type
   variables bound by \<eta> *)
lemma constr_type_args:
  assumes env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and cc: "constructor_class \<Sigma> \<Gamma> e = Some (Ok (C, explicit))"
    and "explicit = Some \<tau>s \<or> explicit = None
      \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C) \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
  shows "length \<tau>s = length (type_params \<Sigma> C) \<and> (\<forall>\<tau> \<in> set \<tau>s. fv \<tau> \<subseteq> fst ` set \<eta>)"
  using assms(3)
proof
  assume "explicit = Some \<tau>s"
  with constructor_class_Ok[OF cc] obtain \<psi> where "resolve_type \<Sigma> \<Gamma> \<psi> = Ok (TyClass C \<tau>s)"
    and len: "length \<tau>s = length (type_params \<Sigma> C)"
    by auto
  from resolve_type_tyvars[OF this(1)] have "\<forall>\<tau> \<in> set \<tau>s. fv \<tau> \<subseteq> tyvars \<Gamma>" by auto
  with wf_env_tyvars[OF env] len show ?thesis by blast
next
  assume "explicit = None \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C) \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
  then have inferred: "inferred_type_args \<Sigma> (type_params \<Sigma> C) \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
    by blast
  have "fv \<tau>' \<subseteq> fst ` set \<eta>" if "Ok \<tau>' \<in> set (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es)" for \<tau>'
    using that wf_env_tyvars[OF env] by (fastforce dest!: synth_at_tyvars[OF sym])
  with inferred_type_args_length[OF inferred] inferred_type_args_fv[OF inferred] show ?thesis by blast
qed

(* Typing by synthesis of a call of the constructor of class C, at C and type arguments over the type variables
   bound by \<eta>, with each argument typed at the type of its field *)
lemma constr_call_typed:
  assumes callee: "sound_expr \<rho> (node e) (Val (VClass C))" and env: "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>" and nolam: "lambda_of (node e) = None"
  obtains x\<sigma>s \<sigma>es \<tau>s where "C |\<in>| fmdom \<Sigma>" and "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    and "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
    and "\<tau> = TyClass C \<tau>s" and "length \<tau>s = length (type_params \<Sigma> C)" and "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fst ` set \<eta>"
proof (cases "constructor_class \<Sigma> \<Gamma> e")
  case None
  with synth nolam obtain \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" by (auto simp: bind_sum_def split: sum.splits)
  from class_callee[OF callee env this] show thesis ..
next
  case (Some m)
  from synth nolam this obtain C' explicit x\<sigma>s \<sigma>es \<tau>s where m: "m = Ok (C', explicit)"
    and fields: "fields \<Sigma> C' = FieldScheme (type_params \<Sigma> C') x\<sigma>s"
    and args: "constructor_args C' (FieldScheme (type_params \<Sigma> C') x\<sigma>s) es kws = Ok \<sigma>es"
    and checked: "\<forall>(\<sigma>, e') \<in> set \<sigma>es. check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s (type_params \<Sigma> C') \<sigma>) = Ok ()"
    and \<tau>: "\<tau> = TyClass C' \<tau>s"
    and \<tau>s: "explicit = Some \<tau>s \<or> explicit = None
      \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C') (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
    by (rule constr_synth)
  from Some m have cc: "constructor_class \<Sigma> \<Gamma> e = Some (Ok (C', explicit))" by simp
  from sound_expr_class[OF callee env constructor_class_Ok_entry[OF cc]] have C': "C' = C" by simp
  from sound_expr_name[OF callee env constructor_class_Ok_entry[OF cc]] have "\<turnstile> VClass C : Type C'" by simp
  then have dom: "C |\<in>| fmdom \<Sigma>" using C' by (auto dest: wf_class_dom)
  from constr_type_args[OF env cc \<tau>s] C' have len: "length \<tau>s = length (type_params \<Sigma> C)"
    and fv: "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fst ` set \<eta>"
    by simp_all
  note fields = fields[unfolded C'] and args = args[unfolded C'] and checked = checked[unfolded C']
    and \<tau> = \<tau>[unfolded C']
  have fv_field: "fv \<sigma> \<subseteq> set (type_params \<Sigma> C)" if "\<sigma> \<in> snd ` set x\<sigma>s" for \<sigma>
  proof -
    from that obtain x where x: "(x, \<sigma>) \<in> set x\<sigma>s" by auto
    have "\<forall>(x, \<sigma>) \<in> set x\<sigma>s. fv \<sigma> \<subseteq> set (type_params \<Sigma> C)" using fields_fv[OF wf_class_table dom] fields by simp
    from bspec[OF this x] show ?thesis by simp
  qed
  have "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
    unfolding list_all2_map1 list_all2_map2
  proof (rule list.rel_refl_strong)
    fix z
    assume z: "z \<in> set \<sigma>es"
    obtain \<sigma> e' where z': "z = (\<sigma>, e')" by (cases z)
    from constructor_args_field[OF args z[unfolded z']] have "\<sigma> \<in> snd ` set x\<sigma>s" .
    with fv_field fv_subst[OF _ len] fv have "fv (subst \<tau>s (type_params \<Sigma> C) \<sigma>) \<subseteq> fst ` set \<eta>" by blast
    with checked z z' show "has_type_at \<Sigma> \<eta> \<Gamma> (snd z) ((subst \<tau>s (type_params \<Sigma> C) \<circ> fst) z)"
      by (auto intro: has_type_check_at)
  qed
  then show thesis by (rule that[OF dom fields args _ \<tau> len fv])
qed

lemma call_fail_args_sound:
  assumes callee: "sound_expr \<rho> (node e) (Val v)" and args: "sound_exprs \<rho> es (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (Aborts \<kappa>)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<eta> \<Gamma> (ExprCall e (es, [])) \<tau>"
  have "\<exists>\<tau>s. list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s"
  proof (cases "lambda_of (node e)")
    case (Some xe)
    then obtain xs e' where "lambda_of (node e) = Some (xs, e')" by (cases xe) simp
    with typed obtain \<tau>s where "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s" by (rule call_lambda_typed)
    from those_sum_map_Ok[OF this] show ?thesis by (blast intro: list.rel_mono_strong has_type_synth_at)
  next
    case None
    from typed None show ?thesis
    proof (cases rule: call_typed)
      case (synth \<tau>')
      show ?thesis
      proof (cases "constructor_class \<Sigma> \<Gamma> e")
        case (Some m)
        from constructor_class_entry[OF this] obtain C where "expr_entry \<Gamma> (node e) = Some (Type C)" by blast
        from sound_expr_class[OF callee env this] callee have cls: "sound_expr \<rho> (node e) (Val (VClass C))"
          by simp
        obtain x\<sigma>s \<sigma>es \<tau>s where "C |\<in>| fmdom \<Sigma>"
          and "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
          and args: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es [] = Ok \<sigma>es"
          and "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
          and "\<tau>' = TyClass C \<tau>s" and "length \<tau>s = length (type_params \<Sigma> C)"
          and "\<forall>\<tau>'' \<in> set \<tau>s. fv \<tau>'' \<subseteq> fst ` set \<eta>"
          by (rule constr_call_typed[OF cls env synth(1) None])
        with constructor_args_exprs(1)[OF args] show ?thesis by auto
      next
        case c: None
        with synth(1) None obtain \<sigma> \<tau>'' where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" and "synth_call \<Sigma> \<Gamma> e \<sigma> [] es = Ok \<tau>''"
          by (auto simp: bind_sum_def split: sum.splits)
        from callee_call[OF callee env this] show ?thesis by blast
      qed
    next
      case (stmt \<sigma>)
      from callee_call_stmt[OF callee env stmt] show ?thesis by blast
    qed
  qed
  then obtain \<tau>s where "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) es \<tau>s" by blast
  from sound_exprs_abort[OF args env this] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by simp
qed simp

lemma constr_sound:
  assumes eval: "\<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C)" and callee: "sound_expr \<rho> (node e) (Val (VClass C))"
    and args: "sound_exprs \<rho> (es @ map snd kws) (Val us)"
    and xus: "field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) = Some xus"
  shows "sound_expr \<rho> (ExprCall e (es, kws)) (Val (VObject C xus))"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>"
  obtain x\<sigma>s \<sigma>es \<tau>s where dom: "C |\<in>| fmdom \<Sigma>"
    and fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    and cargs: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and typed: "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
    and \<tau>: "\<tau> = TyClass C \<tau>s" and len: "length \<tau>s = length (type_params \<Sigma> C)"
    and fv: "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fst ` set \<eta>"
    by (rule constr_call_typed[OF callee env synth class_callee_lambda[OF eval]])
  let ?\<alpha>s = "type_params \<Sigma> C" and ?n = "length es" and ?xs = "map fst x\<sigma>s"
  let ?R = "\<lambda>v \<sigma>. \<turnstile> v : Ty (inst \<eta> (subst \<tau>s ?\<alpha>s \<sigma>))"
  have names: "field_names \<Sigma> C = ?xs" using fields by (simp add: field_names_def)
  note n_kws = constructor_args_Ok(1, 2)[OF cargs]
  from sound_exprs_typed[OF args env typed[unfolded constructor_args_exprs(1)[OF cargs]]]
  have "list_all2 ?R us (map fst \<sigma>es)" by (simp add: list_all2_map2)
  then have rel: "list_all2 ?R us (map snd (take ?n x\<sigma>s) @ map (\<lambda>(y, _). the (map_of x\<sigma>s y)) kws)"
    by (simp only: constructor_args_exprs(2)[OF cargs])
  have dist: "distinct ?xs" using wf_class_table_distinct[OF wf_class_table dom] names by simp
  have len_us: "length us = ?n + length kws" using rel n_kws(1) by (auto dest: list_all2_lengthD)
  have xus': "xus = zip (take ?n ?xs) (take ?n us)
    @ map (\<lambda>y. (y, the (map_of (zip (map fst kws) (drop ?n us)) y))) (drop ?n ?xs)"
    using xus names len_us by (simp add: field_map_def Let_def min_def split: if_splits)
  from field_values_rel[OF dist n_kws rel] len_us n_kws(1)
  have rel': "list_all2 ?R (map snd xus) (map snd x\<sigma>s)" by (simp add: xus' comp_def min_def)
  have eq: "inst \<eta> (subst \<tau>s ?\<alpha>s \<sigma>) = subst (map (inst \<eta>) \<tau>s) ?\<alpha>s \<sigma>" if "\<sigma> \<in> set (map snd x\<sigma>s)" for \<sigma>
  proof -
    from that obtain x where x: "(x, \<sigma>) \<in> set x\<sigma>s" by auto
    have "\<forall>(x, \<sigma>) \<in> set x\<sigma>s. fv \<sigma> \<subseteq> set ?\<alpha>s" using fields_fv[OF wf_class_table dom] fields by simp
    from bspec[OF this x] have "fv \<sigma> \<subseteq> set ?\<alpha>s" by simp
    then have "fv \<sigma> \<inter> set (map fst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set ?\<alpha>s) \<eta>)) = {}" by auto
    then have "inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set ?\<alpha>s) \<eta>) \<sigma> = \<sigma>" by (rule subst_fresh)
    with inst_subst[OF wf_env_closed[OF env] len] show ?thesis by simp
  qed
  have "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty (subst (map (inst \<eta>) \<tau>s) ?\<alpha>s \<sigma>)) (map snd xus) (map snd x\<sigma>s)"
  proof (rule list.rel_mono_strong[OF rel'])
    fix v \<sigma>
    assume "v \<in> set (map snd xus)" and "\<sigma> \<in> set (map snd x\<sigma>s)" and "?R v \<sigma>"
    with eq show "\<turnstile> v : Ty (subst (map (inst \<eta>) \<tau>s) ?\<alpha>s \<sigma>)" by simp
  qed
  then have "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xus) (field_types \<Sigma> C (map (inst \<eta>) \<tau>s))"
    by (simp add: field_types_def fields split_def list_all2_map2)
  moreover have "map fst xus = field_names \<Sigma> C" using len_us n_kws(1) by (simp add: xus' names min_def comp_def)
  ultimately have "\<turnstile> VObject C xus : Ty (TyClass C (map (inst \<eta>) \<tau>s))" using dom by (blast intro: ValObj)
  with \<tau> show "result_typed (Val (VObject C xus)) (inst \<eta> \<tau>)" by simp
next
  fix \<eta> \<Gamma> \<tau>
  assume "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = Some (Ok ())"
  with class_callee_lambda[OF eval] show "result_typed (Val (VObject C xus)) (inst \<eta> \<tau>)" by simp
next
  fix \<eta> \<Gamma>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws))"
  then obtain \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" by auto
  from class_callee[OF callee env this] show "result_typed (Val (VObject C xus)) (inst \<eta> (TyPrim object))" ..
qed simp

lemma constr_arity_sound:
  assumes eval: "\<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C)" and callee: "sound_expr \<rho> (node e) (Val (VClass C))"
    and args: "sound_exprs \<rho> (es @ map snd kws) (Val us)"
    and none: "field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) = None"
  shows "sound_expr \<rho> (ExprCall e (es, kws)) (Aborts TypeError)"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>"
  obtain x\<sigma>s \<sigma>es \<tau>s where dom: "C |\<in>| fmdom \<Sigma>"
    and fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    and cargs: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and typed: "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
    and \<tau>: "\<tau> = TyClass C \<tau>s" and len: "length \<tau>s = length (type_params \<Sigma> C)"
    and fv: "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fst ` set \<eta>"
    by (rule constr_call_typed[OF callee env synth class_callee_lambda[OF eval]])
  have names: "field_names \<Sigma> C = map fst x\<sigma>s" using fields by (simp add: field_names_def)
  note n_kws = constructor_args_Ok(1, 2)[OF cargs]
  have "length \<sigma>es = length es + length kws"
    using arg_cong[OF constructor_args_exprs(1)[OF cargs], of length] by simp
  with sound_exprs_typed[OF args env typed[unfolded constructor_args_exprs(1)[OF cargs]]]
  have "length us = length es + length kws" by (auto dest: list_all2_lengthD)
  with none n_kws names show "result_typed (Aborts TypeError) (inst \<eta> \<tau>)"
    by (simp add: field_map_def Let_def min_def split: if_splits)
next
  fix \<eta> \<Gamma> \<tau>
  assume "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = Some (Ok ())"
  with class_callee_lambda[OF eval] show "result_typed (Aborts TypeError) (inst \<eta> \<tau>)" by simp
next
  fix \<eta> \<Gamma>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws))"
  then obtain \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" by auto
  from class_callee[OF callee env this] show "result_typed (Aborts TypeError) (inst \<eta> (TyPrim object))" ..
qed simp

lemma constr_fail_sound:
  assumes eval: "\<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C)" and callee: "sound_expr \<rho> (node e) (Val (VClass C))"
    and args: "sound_exprs \<rho> (es @ map snd kws) (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprCall e (es, kws)) (Aborts \<kappa>)"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>"
  obtain x\<sigma>s \<sigma>es \<tau>s where dom: "C |\<in>| fmdom \<Sigma>"
    and fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    and cargs: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and typed: "list_all2 (has_type_at \<Sigma> \<eta> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
    and \<tau>: "\<tau> = TyClass C \<tau>s" and len: "length \<tau>s = length (type_params \<Sigma> C)"
    and fv: "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' \<subseteq> fst ` set \<eta>"
    by (rule constr_call_typed[OF callee env synth class_callee_lambda[OF eval]])
  from sound_exprs_abort[OF args env typed[unfolded constructor_args_exprs(1)[OF cargs]]]
  show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by simp
next
  fix \<eta> \<Gamma> \<tau>
  assume "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = Some (Ok ())"
  with class_callee_lambda[OF eval] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by simp
next
  fix \<eta> \<Gamma>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws))"
  then obtain \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" by auto
  from class_callee[OF callee env this] show "result_typed (Aborts \<kappa>) (inst \<eta> (TyPrim object))" ..
qed simp

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
