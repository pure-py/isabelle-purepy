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

(* Typing of e at \<tau>: by synthesis, by checking when \<tau> is well-formed, or at type object if e is a call
   statement *)
definition has_type :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
where
"has_type \<Sigma> \<Gamma> e \<tau> =
  (synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr \<Sigma> \<Gamma> e \<tau> = Ok () \<and> wf_ty \<Sigma> \<tau> \<or> call_stmt \<Sigma> \<Gamma> e \<and> \<tau> = TyPrim object)"

fun has_type_at :: "class_table \<Rightarrow> cxt \<Rightarrow> expr located \<Rightarrow> ty \<Rightarrow> bool"
where
"has_type_at \<Sigma> \<Gamma> (At p e) \<tau> = has_type \<Sigma> \<Gamma> e \<tau>"

lemma has_type_synth_at: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<Longrightarrow> has_type_at \<Sigma> \<Gamma> e \<tau>"
  by (cases e) (simp add: has_type_def)

lemma has_type_check_at: "\<lbrakk> check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok () ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> has_type_at \<Sigma> \<Gamma> e \<tau>"
  by (cases e) (simp add: has_type_def)

(* Typing of e at \<tau> by its synthesis or checking rule, when \<tau> is well-formed *)
definition typed_by_rule :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool"
where
"typed_by_rule \<Sigma> \<Gamma> e \<tau> = (synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr' \<Sigma> \<Gamma> e \<tau> = Some (Ok ()) \<and> wf_ty \<Sigma> \<tau>)"

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
  (\<forall>\<eta> \<Gamma> \<theta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> expr_entry \<Gamma> e = Some \<theta> \<longrightarrow> \<not> unbound_entry \<theta>
     \<longrightarrow> wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r)"

definition sound_expr :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"
where
"sound_expr \<rho> e r =
  ((\<forall>\<eta> \<Gamma> \<tau>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> has_type \<Sigma> \<Gamma> e \<tau> \<longrightarrow> result_typed r (inst \<eta> \<tau>)) \<and> sound_name \<rho> e r)"

definition sound_exprs :: "env \<Rightarrow> expr located list \<Rightarrow> val list result \<Rightarrow> bool"
where
"sound_exprs \<rho> es rs =
  (\<forall>\<eta> \<Gamma> \<tau>s. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s \<longrightarrow> results_typed rs (map (inst \<eta>) \<tau>s))"

abbreviation wf_envs :: "(var \<Rightarrow> ty) \<Rightarrow> env list result \<Rightarrow> cxt \<Rightarrow> bool"
where "wf_envs \<eta> r \<Gamma> \<equiv> wf_result (\<lambda>\<rho>s. \<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) r"

definition sound_quals :: "env \<Rightarrow> qualifier located list \<Rightarrow> env list result \<Rightarrow> bool"
where
"sound_quals \<rho> gs r = (\<forall>\<eta> \<Gamma> \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> quals \<Sigma> \<Gamma> gs = Ok \<Delta> \<longrightarrow> wf_envs \<eta> r (\<Gamma> \<otimes> \<Delta>))"

definition sound_gen :: "env \<Rightarrow> var \<Rightarrow> val list \<Rightarrow> qualifier located list \<Rightarrow> env list result \<Rightarrow> bool"
where
"sound_gen \<rho> x us gs r =
  (\<forall>\<eta> \<Gamma> \<tau> \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_ty \<Sigma> \<tau> \<longrightarrow> (\<forall>u \<in> set us. \<turnstile> u : Ty (inst \<eta> \<tau>))
     \<longrightarrow> quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>
     \<longrightarrow> wf_envs \<eta> r (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>))"

abbreviation wf_elems :: "val list result \<Rightarrow> ty \<Rightarrow> bool"
where "wf_elems r \<tau> \<equiv> wf_result (\<lambda>vs. \<forall>v \<in> set vs. \<turnstile> v : Ty \<tau>) r"

definition sound_comp :: "env list \<Rightarrow> expr located \<Rightarrow> val list result \<Rightarrow> bool"
where
"sound_comp \<rho>s e r =
  (\<forall>\<eta> \<Gamma> \<tau>. (\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) \<longrightarrow> has_type_at \<Sigma> \<Gamma> e \<tau> \<longrightarrow> wf_elems r (inst \<eta> \<tau>))"

abbreviation wf_entries :: "(str \<times> val) list result \<Rightarrow> ty \<Rightarrow> bool"
where "wf_entries r \<tau> \<equiv> wf_result (\<lambda>\<delta>. \<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau>) r"

definition sound_entries :: "env list \<Rightarrow> expr located \<Rightarrow> expr located \<Rightarrow> (str \<times> val) list result \<Rightarrow> bool"
where
"sound_entries \<rho>s e e' r =
  (\<forall>\<eta> \<Gamma> \<tau>. (\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) \<longrightarrow> check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()
     \<longrightarrow> has_type_at \<Sigma> \<Gamma> e' \<tau> \<longrightarrow> wf_entries r (inst \<eta> \<tau>))"

lemma sound_name_None [simp]:
  "\<lbrakk> dotted_name e = None ; \<forall>e' e''. e \<noteq> ExprSubscript e' e'' \<rbrakk> \<Longrightarrow> sound_name \<rho> e r"
  by (cases e) (simp_all add: sound_name_def expr_entry_def entry_of_def)

lemma sound_compD:
  "\<lbrakk> sound_comp \<rho>s e r ; \<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma> ; has_type_at \<Sigma> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> wf_elems r (inst \<eta> \<tau>)"
  unfolding sound_comp_def by blast

lemma sound_entriesD:
  "\<lbrakk> sound_entries \<rho>s e e' r ; \<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()
   ; has_type_at \<Sigma> \<Gamma> e' \<tau> \<rbrakk>
  \<Longrightarrow> wf_entries r (inst \<eta> \<tau>)"
  unfolding sound_entries_def by blast

(* Return type, well-formed *)
fun wf_return :: "ty option \<Rightarrow> bool"
where
"wf_return (Some \<tau>) = wf_ty \<Sigma> \<tau>" |
"wf_return None = True"

(* Completion of a statement checked at \<Gamma> and return type \<zeta> with static outcome R, run in \<rho> *)
fun wf_completion :: "(var \<Rightarrow> ty) \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> completion \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Assigns \<rho>') R =
  (\<exists>\<Delta>. bindings_of R = Some \<Delta> \<and> fmdom \<rho>' |\<subseteq>| fmdom \<Delta> \<and> \<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>)" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Returns v) R = (\<forall>\<tau>. \<zeta> = Some \<tau> \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>))" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Aborts\<^sub>\<omega> \<kappa>) R = (\<not> prevented \<kappa>)"

fun wf_outcome :: "(var \<Rightarrow> ty) \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> outcome \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (vs, \<omega>) R = wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R"

lemma wf_completion_bindings:
  "bindings_of R = bindings_of R' \<Longrightarrow> wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R = wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R'"
  by (cases \<omega>) simp_all

definition sound_stmt :: "env \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_stmt \<rho> s o =
  (\<forall>\<eta> \<Gamma> \<zeta> R. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<zeta> \<longrightarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R
     \<longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R)"

definition sound_elif :: "env \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_elif \<rho> eb o =
  (\<forall>\<eta> \<Gamma> \<zeta> Rs. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<zeta> \<longrightarrow> those_sum (check_elif \<Sigma> \<Gamma> \<zeta> eb) = Ok Rs
     \<longrightarrow> (\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R))"

lemma sound_stmt_at:
  assumes "sound_stmt \<rho> (node s) o" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "wf_return \<zeta>"
    and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
proof -
  from assms(4) obtain R' where "check_stmt \<Sigma> \<Gamma> \<zeta> (node s) = Ok R'" and R': "bindings_of R' = bindings_of R"
    by (blast dest: check_stmt_at_Ok)
  with assms(1-3) have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'" unfolding sound_stmt_def by simp
  then show ?thesis by (cases o) (simp add: wf_completion_bindings[OF R'])
qed

lemma sound_stmtI:
  assumes "\<And>\<eta> \<Gamma> \<zeta> R. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_return \<zeta> ; check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R \<rbrakk> \<Longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
  shows "sound_stmt \<rho> s o"
  unfolding sound_stmt_def using assms by blast

lemma sound_elifI:
  assumes "\<And>\<eta> \<Gamma> \<zeta> Rs. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_return \<zeta> ; those_sum (check_elif \<Sigma> \<Gamma> \<zeta> eb) = Ok Rs \<rbrakk>
            \<Longrightarrow> \<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
  shows "sound_elif \<rho> eb o"
  unfolding sound_elif_def using assms by blast


subsection \<open>Subtyping\<close>

lemma joins_upper: "\<lbrakk> \<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>' ; \<tau> \<in> set \<tau>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<tau> <: joins \<Sigma> \<tau>s"
proof (induction \<tau>s)
  case (Cons \<tau>' \<tau>s)
  show ?case
  proof (cases "\<tau> = \<tau>'")
    case True
    then show ?thesis by (simp add: joins_def join_upper)
  next
    case False
    with Cons.prems have \<tau>: "\<tau> \<in> set \<tau>s" by simp
    with Cons have "\<Sigma> \<turnstile> \<tau> <: joins \<Sigma> \<tau>s" by simp
    from subty_trans[OF wf_class_table _ joins_wf this join_upper(2)] Cons.prems(1) \<tau> show ?thesis
      by (simp add: joins_def)
  qed
qed simp

(* Value at an instance of \<sigma>, at the instance of a well-formed type above \<sigma> *)
lemma wf_val_inst_sub:
  assumes "\<turnstile> v : Ty (inst \<eta> \<sigma>)" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>" and "wf_ty \<Sigma> \<tau>" and "wf_inst \<Sigma> \<eta>"
  shows "\<turnstile> v : Ty (inst \<eta> \<tau>)"
proof -
  have "wf_ty \<Sigma> \<sigma>" using wf_val_ty[OF assms(1)] by (rule wf_ty_inst_inv)
  with inst_subty[OF wf_class_table assms(2)] assms(3) have "\<Sigma> \<turnstile> inst \<eta> \<sigma> <: inst \<eta> \<tau>" by simp
  from wf_val_sub[OF assms(1) this inst_wf[OF assms(4, 3)]] show ?thesis .
qed

lemma result_typed_sub:
  "\<lbrakk> result_typed r (inst \<eta> \<sigma>) ; \<Sigma> \<turnstile> \<sigma> <: \<tau> ; wf_ty \<Sigma> \<tau> ; wf_inst \<Sigma> \<eta> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  by (cases r) (auto intro: wf_val_inst_sub)

lemma wf_lit_bool: "\<turnstile> VLit (LitBool b) : Ty (TyPrim bool)"
  by (rule ValLit[OF SubtyLiteral]) (simp_all add: SubtyRefl)

lemma wf_str_char: "\<turnstile> VLit (LitString c) : Ty (TyPrim str)"
  by (rule ValLit[OF SubtyLiteral]) (simp_all add: SubtyRefl)

lemma wf_int_lit: "\<turnstile> VLit (LitInt k) : Ty (TyPrim int)"
  by (rule ValLit[OF SubtyLiteral]) (simp_all add: SubtyRefl)

lemma wf_int_float: "\<turnstile> VLit (LitInt k) : Ty (TyPrim float)"
  by (rule ValLit[OF SubtyLiteral]) (simp_all add: SubtyIntFloat)

(* None at an instance of a well-formed type above NoneType *)
lemma wf_none:
  assumes "\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>" and "wf_ty \<Sigma> \<tau>" and "wf_inst \<Sigma> \<eta>"
  shows "\<turnstile> VLit LitNone : Ty (inst \<eta> \<tau>)"
proof -
  have "\<Sigma> \<turnstile> inst \<eta> (TyPrim NoneType) <: inst \<eta> \<tau>"
    using inst_subty[OF wf_class_table assms(1)] assms(2) by simp
  then have "\<Sigma> \<turnstile> TyLiteral LitNone <: inst \<eta> \<tau>" by (auto intro: SubtyLiteral)
  from ValLit[OF this inst_wf[OF assms(3, 2)]] show ?thesis .
qed

subsection \<open>Well-formed types produced by the checker\<close>

(* Types produced by the checker in a well-formed context: well-formed and over the type variables in scope *)
lemma synth_wf_ty: "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  using synth_wf(1)[OF wf_class_table] by blast

lemma synth_at_wf_ty: "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  and synth_at_tyvars: "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> fv \<tau> \<subseteq> tyvars \<Gamma>"
  using synth_wf(2)[OF wf_class_table] by blast+

(* Type arguments matched against well-formed \<tau>, well-formed *)
lemma type_args_wf:
  "\<lbrakk> wf_ty \<Sigma> \<tau> ; Subtyping.type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s = Ok \<tau>s \<rbrakk> \<Longrightarrow> \<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>'"
  using type_args_range(1)[OF wf_class_table] by (blast dest: type_args_of_elem)

lemma inferred_type_args_fv:
  "\<lbrakk> inferred_type_args \<Sigma> \<alpha>s \<sigma>s ms = Ok \<tau>s ; \<forall>\<tau>. Ok \<tau> \<in> set ms \<longrightarrow> wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> V \<rbrakk>
  \<Longrightarrow> \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<and> fv \<tau> \<subseteq> V"
  by (rule inferred_type_args_wf[OF wf_class_table])

(* Bindings of a statement checked in a well-formed context: well-formed and over the type variables in scope *)
lemma check_stmt_wf_cxt:
  "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r) \<rbrakk> \<Longrightarrow> wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
  using check_stmt_wf(1)[OF _ wf_class_table] .

lemma check_stmt_at_wf_cxt:
  assumes "wf_cxt \<Sigma> \<Gamma>" and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)"
  shows "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
proof -
  from check_stmt_at_Ok[OF assms(2)] obtain R where R: "check_stmt \<Sigma> \<Gamma> \<zeta> (node s) = Ok R"
    and "bindings_of R = Some \<Delta>"
    by auto
  then obtain r' where "R = Assigns\<^sub>R \<Delta> r'" by (cases R) auto
  with R show ?thesis by (simp add: check_stmt_wf_cxt[OF assms(1)])
qed

(* Type at which an expression is typed in a well-formed context, well-formed *)
lemma has_type_wf: "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; has_type \<Sigma> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  by (auto simp: has_type_def dest: synth_wf_ty)

lemma typed_by_rule_wf: "\<lbrakk> wf_cxt \<Sigma> \<Gamma> ; typed_by_rule \<Sigma> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  by (auto simp: typed_by_rule_def dest: synth_wf_ty)

subsection \<open>Checking\<close>

lemma sound_exprI:
  assumes synth: "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  and check:
    "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr' \<Sigma> \<Gamma> e \<tau> = Some (Ok ()) ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  and call: "\<And>\<eta> \<Gamma>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; call_stmt \<Sigma> \<Gamma> e \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> (TyPrim object))"
  and name: "sound_name \<rho> e r"
  shows "sound_expr \<rho> e r"
  unfolding sound_expr_def has_type_def using name
  by (blast dest: check_expr_cases synth check call result_typed_sub wf_env_wf_inst)

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
  assumes "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; typed_by_rule \<Sigma> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
    and "\<And>\<Gamma>. \<not> call_stmt \<Sigma> \<Gamma> e" and "dotted_name e = None" and "\<forall>e' e''. e \<noteq> ExprSubscript e' e''"
  shows "sound_expr \<rho> e r"
  by (rule sound_exprI) (auto intro: assms(1) simp: typed_by_rule_def assms(2-4))

lemma sound_expr_synth_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def has_type_def)

lemma sound_expr_check_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok () ; wf_ty \<Sigma> \<tau> \<rbrakk>
  \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def has_type_def)

lemma sound_expr_has_type_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; has_type_at \<Sigma> \<Gamma> e \<tau> \<rbrakk> \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def)

lemma sound_expr_name:
  "\<lbrakk> sound_expr \<rho> e r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; expr_entry \<Gamma> e = Some \<theta> ; \<not> unbound_entry \<theta> \<rbrakk>
  \<Longrightarrow> wf_result (\<lambda>v. \<turnstile> v : inst_entry \<eta> \<theta>) r"
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
  "\<lbrakk> sound_exprs \<rho> es (Aborts \<kappa>) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s \<rbrakk> \<Longrightarrow> \<not> prevented \<kappa>"
  by (fastforce simp: sound_exprs_def)

subsection \<open>Canonical forms\<close>

lemma wf_class_ty: "\<turnstile> VClass C : Ty \<tau> \<Longrightarrow> False"
  by (erule WfTyE) simp_all

(* Literal at a subtype of a primitive type p other than object and Sized *)
lemma wf_prim_lit:
  assumes "\<turnstile> v : Ty \<tau>" and "\<Sigma> \<turnstile> \<tau> <: TyPrim p" and "p \<notin> {object, Sized}"
  obtains l where "v = VLit l" and "prim_subtype p (TyLiteral l)"
proof -
  from wf_val_sub[OF assms(1, 2)] have "\<turnstile> v : Ty (TyPrim p)" by simp
  then show thesis by (cases rule: WfTyE) (auto dest!: prim_subtype_subty(1)[OF assms(3)] intro: that)
qed

lemma wf_object_type: "\<lbrakk> \<turnstile> v : Ty \<tau> ; object_type \<tau> \<rbrakk> \<Longrightarrow> is_object v"
  by (erule WfTyE) (auto dest: object_type_subty(1))

(* Object of class C, typed at a type above the class at type arguments typing its fields *)
lemma wf_object:
  assumes "\<turnstile> VObject C xvs : Ty \<tau>"
  obtains \<tau>s where "wf_ty \<Sigma> (TyClass C \<tau>s)" and "map fst xvs = field_names \<Sigma> C"
    and "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s)" and "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>"
  using assms by (cases rule: WfTyE) (auto intro: that)

lemma wf_val_union:
  assumes "\<turnstile> v : Ty (TyUnion \<sigma> \<sigma>')"
  shows "\<turnstile> v : Ty \<sigma> \<or> \<turnstile> v : Ty \<sigma>'"
proof -
  from wf_val_ty[OF assms] have "wf_ty \<Sigma> \<sigma>" and "wf_ty \<Sigma> \<sigma>'" by simp_all
  with assms show ?thesis
    by (cases rule: WfTyE) (auto dest!: nonunion_subty_union(1)[OF _ refl] intro: wf_val_wf_env.intros)
qed

lemma wf_list:
  assumes "\<turnstile> v : Ty (TyList \<tau>)"
  obtains vs where "v = VList vs" and "\<forall>u \<in> set vs. \<turnstile> u : Ty \<tau>"
proof -
  from assms obtain vs \<sigma> where v: "v = VList vs" and typed: "\<forall>u \<in> set vs. \<turnstile> u : Ty \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    by (cases rule: WfTyE) (auto dest!: subty_list_inv(1)[OF _ refl])
  have "wf_ty \<Sigma> \<tau>" using wf_val_ty[OF assms] by simp
  with typed sub have "\<forall>u \<in> set vs. \<turnstile> u : Ty \<tau>" by (blast intro: wf_val_sub)
  with v that show thesis by blast
qed

lemma wf_tuple:
  assumes "\<turnstile> v : Ty (TyTuple \<tau>s)"
  obtains vs where "v = VTuple vs" and "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s"
proof -
  from assms obtain vs \<sigma>s where v: "v = VTuple vs" and vs: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<sigma>s"
    and sub: "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s"
    by (cases rule: WfTyE) (auto dest!: subty_tuple_inv(1)[OF _ refl])
  have "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s"
  proof (rule list_all2_all_nthI)
    show len: "length vs = length \<tau>s" using vs sub by (simp add: list_all2_lengthD subtys_list_all2)
    fix i
    assume i: "i < length vs"
    with vs sub have "\<turnstile> vs ! i : Ty (\<sigma>s ! i)" and "\<Sigma> \<turnstile> \<sigma>s ! i <: \<tau>s ! i"
      by (auto simp: list_all2_conv_all_nth subtys_list_all2)
    moreover have "wf_ty \<Sigma> (\<tau>s ! i)" using wf_val_ty[OF assms] i len by simp
    ultimately show "\<turnstile> vs ! i : Ty (\<tau>s ! i)" by (rule wf_val_sub)
  qed
  with v that show thesis by blast
qed

lemma wf_dict:
  assumes "\<turnstile> v : Ty (TyDict \<tau>)"
  obtains \<delta> where "v = VDict \<delta>" and "\<forall>w u. (w, u) \<in> set \<delta> \<longrightarrow> \<turnstile> u : Ty \<tau>"
proof -
  from assms obtain \<delta> \<sigma> where v: "v = VDict \<delta>" and typed: "\<forall>w u. (w, u) \<in> set \<delta> \<longrightarrow> \<turnstile> u : Ty \<sigma>"
    and sub: "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    by (cases rule: WfTyE) (auto dest!: subty_dict_inv(1)[OF _ refl])
  have "wf_ty \<Sigma> \<tau>" using wf_val_ty[OF assms] by simp
  with typed sub have "\<forall>w u. (w, u) \<in> set \<delta> \<longrightarrow> \<turnstile> u : Ty \<tau>" by (blast intro: wf_val_sub)
  with v that show thesis by blast
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
  by (erule WfTyE) (auto dest!: subty_literal_inv(1)[OF _ refl])

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
  from assms obtain \<tau>s' where wf: "wf_ty \<Sigma> (TyClass C \<tau>s')" and names: "map fst xvs = field_names \<Sigma> C"
    and fields: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s')"
    and sub: "\<Sigma> \<turnstile> TyClass C \<tau>s' <: TyClass range_class \<tau>s"
    by (rule wf_object)
  from wf have C: "C |\<in>| fmdom \<Sigma>" by simp
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
  from wf_val_sub[OF assms] have v: "\<turnstile> v : Ty (TyPrim Sized)" by simp
  show ?thesis
  proof (cases v)
    case (VObject C xvs)
    from v obtain \<sigma>s where wf: "wf_ty \<Sigma> (TyClass C \<sigma>s)" and names: "map fst xvs = field_names \<Sigma> C"
      and fields: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<sigma>s)"
      and sub: "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyPrim Sized"
      unfolding VObject by (rule wf_object)
    from subty_sized_inv(1)[OF sub refl] have "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass range_class []"
      by (cases \<sigma>s) (auto intro: SubtyRefl)
    from ValObj[OF wf names fields this range_class_wf] show ?thesis unfolding VObject by (rule iter_range)
  qed (use v in \<open>auto elim!: WfTyE dest!: subty_sized_inv(1)[OF _ refl]\<close>)
qed

end

end
