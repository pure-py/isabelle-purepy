(* Typing of evaluation results; canonical forms of values *)
theory ResultTyping
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
  by (rule ValSub[OF ValLit SubtyLiteral]) (simp add: SubtyRefl)

lemma wf_str_char: "\<turnstile> VLit (LitString c) : Ty (TyPrim str)"
  by (rule ValSub[OF ValLit SubtyLiteral]) (simp add: SubtyRefl)

lemma wf_int_lit: "\<turnstile> VLit (LitInt k) : Ty (TyPrim int)"
  by (rule ValSub[OF ValLit SubtyLiteral]) (simp add: SubtyRefl)

lemma wf_int_float: "\<turnstile> VLit (LitInt k) : Ty (TyPrim float)"
  by (rule ValSub[OF wf_int_lit SubtyIntFloat])

(* None at an instance of a type above NoneType *)
lemma wf_none: "\<Sigma> \<turnstile> TyPrim NoneType <: \<tau> \<Longrightarrow> \<turnstile> VLit LitNone : Ty (inst \<eta> \<tau>)"
  by (intro ValSub[OF ValLit] SubtyLiteral)
     (auto dest: subst_subty'[where \<tau>s = "map snd \<eta>" and \<alpha>s = "map fst \<eta>"])

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

(* Bindings of a statement are over the type variables in scope *)
lemma check_stmt_tyvars: "check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r) \<Longrightarrow> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
  sorry

lemma check_stmt_at_tyvars:
  assumes "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)"
  shows "tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
proof -
  from check_stmt_at_Ok[OF assms] obtain R where R: "check_stmt \<Sigma> \<Gamma> \<zeta> (node s) = Ok R"
    and "bindings_of R = Some \<Delta>"
    by auto
  then obtain r' where "R = Assigns\<^sub>R \<Delta> r'" by (cases R) auto
  with R show ?thesis by (simp add: check_stmt_tyvars)
qed

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
    by (rule ValDef[OF assms(1, 2) refl assms(3-7)])
  show ?thesis
  proof (cases "\<alpha>s = []")
    case True
    with def assms(8) show ?thesis by simp
  next
    case False
    with def have "\<turnstile> Def(\<rho>, ds, i) : Scheme (TyScheme \<alpha>s (inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) \<tau>))"
      by (simp add: inst_entry_signature_entry)
    from ValInst[OF this assms(8, 9)] show ?thesis .
  qed
qed

lemma intro_typed_wf: "intro_typed v \<sigma> \<Longrightarrow> \<turnstile> v : Ty \<sigma>"
proof (cases v)
  case (VLamClosure \<rho> xs e)
  then show "intro_typed v \<sigma> \<Longrightarrow> \<turnstile> v : Ty \<sigma>" by (auto intro: ValLambda[simplified])
next
  case (VDefClosure \<rho> ds i)
  then show "intro_typed v \<sigma> \<Longrightarrow> \<turnstile> v : Ty \<sigma>"
    by (clarsimp simp only: intro_typed.simps) (rule intro_def_wf, assumption+)
next
  case (VPrim f)
  then show "intro_typed v \<sigma> \<Longrightarrow> \<turnstile> v : Ty \<sigma>" by (auto intro: ValPrim)
qed (auto intro: ValLit ValLitFloat ValList ValTuple ValDict ValObj)

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

end

end
