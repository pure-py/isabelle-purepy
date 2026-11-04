(* Value and environment typing *)
theory ValueTyping
  imports "isabelle-purepy.Programs" "isabelle-purepy.Determinism"
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


subsection \<open>Instantiation of type variables\<close>

lemma tyvars_entry: "fmlookup \<Gamma> x = Some \<theta> \<Longrightarrow> fv_entry \<theta> \<subseteq> tyvars \<Gamma>"
  by (force simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff)

lemma tyvars_add: "tyvars (\<Gamma> \<otimes> \<Delta>) \<subseteq> tyvars \<Gamma> \<union> tyvars \<Delta>"
  by (fastforce simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff split: if_splits)

lemma tyvars_single: "\<theta> \<noteq> TypeVar \<Longrightarrow> tyvars (fmupd x \<theta> fmempty) = fv_entry \<theta>"
  by (auto simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff split: if_splits)

(* Instantiation of the type variables in scope at the closed types bound to them by \<eta>, since values have
   closed types *)
abbreviation inst :: "(var \<times> ty) list \<Rightarrow> ty \<Rightarrow> ty"
where
"inst \<eta> \<equiv> subst (map snd \<eta>) (map fst \<eta>)"

definition closed_inst :: "(var \<times> ty) list \<Rightarrow> bool"
where
"closed_inst \<eta> = (\<forall>\<alpha> \<tau>. (\<alpha>, \<tau>) \<in> set \<eta> \<longrightarrow> fv \<tau> = {})"

(* Instantiation under the parameters of a scheme, which shadow the type variables in scope *)
fun inst_scheme :: "(var \<times> ty) list \<Rightarrow> ty_scheme \<Rightarrow> ty_scheme"
where
"inst_scheme \<eta> (TyScheme \<alpha>s \<tau>) = TyScheme \<alpha>s (inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) \<tau>)"

fun inst_entry :: "(var \<times> ty) list \<Rightarrow> cxt_entry \<Rightarrow> cxt_entry"
where
"inst_entry \<eta> (Ty \<tau>) = Ty (inst \<eta> \<tau>)" |
"inst_entry \<eta> (DU \<tau>) = DU (inst \<eta> \<tau>)" |
"inst_entry \<eta> (PU \<tau> b) = PU (inst \<eta> \<tau>) b" |
"inst_entry \<eta> (Scheme \<pi>) = Scheme (inst_scheme \<eta> \<pi>)" |
"inst_entry \<eta> (PUScheme \<pi> b) = PUScheme (inst_scheme \<eta> \<pi>) b" |
"inst_entry \<eta> \<theta> = \<theta>"

lemma inst_entry_signature_entry:
  "inst_entry \<eta> (signature_entry (TyScheme \<alpha>s \<tau>)) =
   (if \<alpha>s = [] then Ty (inst \<eta> \<tau>) else Scheme (TyScheme \<alpha>s (inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) \<tau>)))"
  by (cases \<alpha>s) simp_all

lemma subst_closed: "fv \<tau> = {} \<Longrightarrow> subst \<tau>s \<alpha>s \<tau> = \<tau>"
  by (induction \<tau>) (auto intro: map_idI)

lemma inst_closed: "\<lbrakk> closed_inst \<eta> ; fv \<tau> \<subseteq> fst ` set \<eta> \<rbrakk> \<Longrightarrow> fv (inst \<eta> \<tau>) = {}"
  by (induction \<tau>)
     (auto simp: closed_inst_def zip_map_fst_snd map_of_eq_None_iff UN_subset_iff split: option.splits
      dest!: map_of_SomeD)

(* Instantiation after substitution of closed types for the parameters of a scheme *)
lemma inst_subst:
  assumes "closed_inst \<eta>" and "length \<tau>s = length \<alpha>s"
  shows "inst \<eta> (subst \<tau>s \<alpha>s \<sigma>) = subst (map (inst \<eta>) \<tau>s) \<alpha>s (inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) \<sigma>)"
proof (induction \<sigma>)
  case (TyVar \<beta>)
  show ?case
  proof (cases "\<beta> \<in> set \<alpha>s")
    case True
    then obtain \<tau> where "map_of (zip \<alpha>s \<tau>s) \<beta> = Some \<tau>"
      using map_of_zip_is_Some[OF assms(2)[symmetric]] by blast
    with True assms(2) show ?thesis by (simp add: map_of_zip_map_snd zip_map_fst_snd map_of_filter_key)
  next
    case False
    then have "map_of (zip \<alpha>s \<tau>s) \<beta> = None" by (simp add: assms(2))
    with False assms show ?thesis
      by (auto simp: zip_map_fst_snd map_of_filter_key subst_closed closed_inst_def split: option.splits
          dest!: map_of_SomeD dest: set_zip_leftD)
  qed
qed (simp_all cong: map_cong)


subsection \<open>Typing of expressions and statements\<close>

(* Typing of a call statement, whose result may be None *)
fun call_stmt :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> bool"
where
"call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws)) =
  (lambda_of (node e) = None \<and> class_of_name \<Gamma> (node e) = None \<and>
   (\<exists>\<sigma>. callee \<Sigma> \<Gamma> e es = Ok \<sigma> \<and> check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok ()))" |
"call_stmt \<Sigma> \<Gamma> _ = False"

(* e synthesises \<tau>, checks against \<tau>, whose type variables \<eta> binds, or is a call statement, at type object *)
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

type_synonym elif_block = "(expr located \<times> stmt located) list \<times> stmt located option"

(* Static outcomes of the branches of an elif block, as listed by the if rule *)
fun check_elif :: "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> elif_block \<Rightarrow> static_outcome may_fail list"
where
"check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else') =
  map (\<lambda>(e', s'). do { check_expr_at \<Sigma> \<Gamma> e' (TyPrim bool); check_stmt_at \<Sigma> \<Gamma> \<zeta> s' }) elifs
  @ [case else' of Some s' \<Rightarrow> check_stmt_at \<Sigma> \<Gamma> \<zeta> s' | None \<Rightarrow> Ok (Assigns\<^sub>R fmempty None)]"

lemma check_stmt_if:
  "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = do {
     check_expr_at \<Sigma> \<Gamma> e (TyPrim bool);
     merges \<Sigma> (set (declares (StmtIf e s elifs else')))
       (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))
   }"
  by simp

(* Return type over the type variables bound by \<eta> *)
fun wf_return :: "(var \<times> ty) list \<Rightarrow> ty option \<Rightarrow> bool"
where
"wf_return \<eta> (Some \<tau>) = (fv \<tau> \<subseteq> fst ` set \<eta>)" |
"wf_return \<eta> None = True"

fun bindings_of :: "static_outcome \<Rightarrow> cxt option"
where
"bindings_of (Assigns\<^sub>R \<Delta> _) = Some \<Delta>" |
"bindings_of Returns\<^sub>R = None"

lemma check_stmt_at_Ok:
  "check_stmt_at \<Sigma> \<Gamma> \<zeta> (At p s) = Ok R \<Longrightarrow> \<exists>R'. check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R' \<and> bindings_of R' = bindings_of R"
  by (cases "check_stmt \<Sigma> \<Gamma> \<zeta> s") (auto split: static_outcome.splits)

context evaluation
begin

inductive wf_val :: "val \<Rightarrow> cxt_entry \<Rightarrow> bool" ("\<turnstile> _ : _" [51, 51] 50)
and wf_env :: "(var \<times> ty) list \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> bool" ("_ \<turnstile> _ : _" [51, 51, 51] 50)
where
ValLit: "\<turnstile> VLit l : Ty (TyLiteral l)" |
ValLitFloat: "\<turnstile> VLit (LitFloat x) : Ty (TyPrim float)" |
ValList: "\<forall>v \<in> set vs. \<turnstile> v : Ty \<tau> \<Longrightarrow> \<turnstile> VList vs : Ty (TyList \<tau>)" |
ValTuple: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s \<Longrightarrow> \<turnstile> VTuple vs : Ty (TyTuple \<tau>s)" |
ValDict:
  "\<lbrakk> \<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau> ; distinct (map fst \<delta>) \<rbrakk> \<Longrightarrow> \<turnstile> VDict \<delta> : Ty (TyDict \<tau>)" |
ValLambda:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; params_cxt xs \<sigma>s = Ok \<Delta> ; check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau> = Ok ()
   ; fv (TyCallable \<sigma>s \<tau>) \<subseteq> fst ` set \<eta> \<rbrakk>
  \<Longrightarrow> \<turnstile> Lam(\<rho>, xs, e) : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>))" |
ValDef:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s
   ; \<Delta> = fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))
   ; all_sum (map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> \<Delta>)) ds \<pi>s) = Ok ()
   ; \<forall>\<pi> \<in> set \<pi>s. fv_scheme \<pi> \<subseteq> fst ` set \<eta>
   ; \<forall>d \<in> set ds. case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}
   ; i < length ds ; \<pi>s ! i = TyScheme \<alpha>s \<tau> \<rbrakk>
  \<Longrightarrow> \<turnstile> Def(\<rho>, ds, i) : inst_entry \<eta> (signature_entry (TyScheme \<alpha>s \<tau>))" |
ValInst:
  "\<lbrakk> \<turnstile> v : Scheme (TyScheme \<alpha>s \<sigma>) ; length \<tau>s = length \<alpha>s ; \<forall>\<tau> \<in> set \<tau>s. fv \<tau> = {} \<rbrakk>
  \<Longrightarrow> \<turnstile> v : Ty (subst \<tau>s \<alpha>s \<sigma>)" |
ValObj:
  "\<lbrakk> map fst xvs = field_names \<Sigma> C ; list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s) \<rbrakk>
  \<Longrightarrow> \<turnstile> VObject C xvs : Ty (TyClass C \<tau>s)" |
ValSub: "\<lbrakk> \<turnstile> v : Ty \<sigma> ; \<Sigma> \<turnstile> \<sigma> <: \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> v : Ty \<tau>" |
ValPrimLen: "\<turnstile> VPrim PrimLen : Ty (TyCallable [TyPrim Sized] (TyPrim int))" |
ValPrimRound: "\<turnstile> VPrim PrimRound : Ty (TyCallable [TyPrim float] (TyPrim int))" |
ValPrimExit: "\<turnstile> VPrim PrimExit : Ty (TyCallable [TyPrim int] (TyPrim Never))" |
ValPredef: "\<turnstile> VPredef q : PredefName" |
ValMod: "\<turnstile> VModStub q : ModStub q" |
ValModLoaded: "[] \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> \<turnstile> VModLoaded q \<rho> : ModChecked q \<Gamma>" |
ValClass: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> \<turnstile> VClass C : Type C" |
ValTypeAlias: "\<turnstile> VTypeAlias q \<chi>s i : TypeAlias \<Gamma> q \<chi>s i" |
ValUnbound: "\<theta> = Unbound \<or> (\<exists>\<tau>. \<theta> = DU \<tau>) \<Longrightarrow> \<turnstile> VUnbound : \<theta>" |
ValPU: "v = VUnbound \<or> \<turnstile> v : Ty \<tau> \<Longrightarrow> \<turnstile> v : PU \<tau> b" |
ValPUScheme: "v = VUnbound \<or> \<turnstile> v : Scheme \<pi> \<Longrightarrow> \<turnstile> v : PUScheme \<pi> b" |

WfEnv:
  "\<lbrakk> closed_inst \<eta> ; tyvars \<Gamma> \<subseteq> fst ` set \<eta>
   ; \<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> \<theta> \<noteq> TypeVar \<longrightarrow> (\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>) \<rbrakk>
  \<Longrightarrow> \<eta> \<turnstile> \<rho> : \<Gamma>"

inductive_cases WfEnvE: "\<eta> \<turnstile> \<rho> : \<Gamma>"

lemma wf_env_closed: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> closed_inst \<eta>"
  by (auto elim!: WfEnvE)

lemma wf_env_tyvars: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> tyvars \<Gamma> \<subseteq> fst ` set \<eta>"
  by (auto elim!: WfEnvE)

lemma wf_env_lookup:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; fmlookup \<Gamma> x = Some \<theta> ; \<theta> \<noteq> TypeVar \<rbrakk>
  \<Longrightarrow> \<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
  by (auto elim!: WfEnvE)

(* Extension of an environment and its context in parallel, the extension of the context binding every
   extended variable *)
lemma wf_env_add:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "tyvars \<Delta> \<subseteq> fst ` set \<eta>" and "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>"
    and "\<And>x \<theta>. \<lbrakk> fmlookup \<Delta> x = Some \<theta> ; \<theta> \<noteq> TypeVar \<rbrakk>
          \<Longrightarrow> \<exists>v. fmlookup (\<rho> \<otimes> \<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
  shows "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>"
proof (rule WfEnv)
  show "closed_inst \<eta>" using assms(1) by (rule wf_env_closed)
  show "tyvars (\<Gamma> \<otimes> \<Delta>) \<subseteq> fst ` set \<eta>" using wf_env_tyvars[OF assms(1)] assms(2) tyvars_add by blast
  show "\<forall>x \<theta>. fmlookup (\<Gamma> \<otimes> \<Delta>) x = Some \<theta> \<longrightarrow> \<theta> \<noteq> TypeVar
          \<longrightarrow> (\<exists>v. fmlookup (\<rho> \<otimes> \<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>)"
  proof (intro allI impI)
    fix x \<theta>
    assume lookup: "fmlookup (\<Gamma> \<otimes> \<Delta>) x = Some \<theta>" and "\<theta> \<noteq> TypeVar"
    show "\<exists>v. fmlookup (\<rho> \<otimes> \<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
    proof (cases "fmlookup \<Delta> x")
      case None
      with lookup have "fmlookup \<Gamma> x = Some \<theta>" by (simp add: fmlookup_dom_iff)
      moreover from None assms(3) have "fmlookup \<rho>' x = None" by (metis fmdom_notD fmdom_notI fsubsetD)
      ultimately show ?thesis using wf_env_lookup[OF assms(1)] \<open>\<theta> \<noteq> TypeVar\<close> by (auto simp: fmlookup_dom_iff)
    next
      case (Some \<theta>')
      with lookup have "\<theta>' = \<theta>" by (auto simp: fmlookup_dom_iff)
      with Some \<open>\<theta> \<noteq> TypeVar\<close> show ?thesis by (intro assms(4)) simp_all
    qed
  qed
qed

(* Binding of one variable, in the environment and its context, or in the context only when the variable
   keeps its value *)
lemma wf_env_upd:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<theta> \<noteq> TypeVar" and "fv_entry \<theta> \<subseteq> fst ` set \<eta>" and "\<turnstile> v : inst_entry \<eta> \<theta>"
  shows "\<eta> \<turnstile> fmupd x v \<rho> : fmupd x \<theta> \<Gamma>"
proof -
  have "\<eta> \<turnstile> \<rho> \<otimes> fmupd x v fmempty : \<Gamma> \<otimes> fmupd x \<theta> fmempty"
    using assms by (intro wf_env_add) (auto simp: tyvars_single split: if_splits)
  then show ?thesis by simp
qed

lemma wf_env_upd_cxt:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<theta> \<noteq> TypeVar" and "fv_entry \<theta> \<subseteq> fst ` set \<eta>" and "fmlookup \<rho> x = Some v"
    and "\<turnstile> v : inst_entry \<eta> \<theta>"
  shows "\<eta> \<turnstile> \<rho> : fmupd x \<theta> \<Gamma>"
proof -
  have "\<eta> \<turnstile> \<rho> \<otimes> fmempty : \<Gamma> \<otimes> fmupd x \<theta> fmempty"
    using assms by (intro wf_env_add) (auto simp: tyvars_single split: if_splits)
  then show ?thesis by simp
qed

lemma wf_unbound:
  "\<turnstile> v : \<theta> \<Longrightarrow> v = VUnbound \<longrightarrow> \<theta> = Unbound \<or> (\<exists>\<tau>. \<theta> = DU \<tau>) \<or> (\<exists>\<tau> b. \<theta> = PU \<tau> b) \<or> (\<exists>\<pi> b. \<theta> = PUScheme \<pi> b)"
  "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
  by (induction rule: wf_val_wf_env.inducts) (auto simp: inst_entry_signature_entry split: if_splits)

lemma wf_unbound_ty: "\<turnstile> VUnbound : Ty \<tau> \<Longrightarrow> False"
  and wf_unbound_scheme: "\<turnstile> VUnbound : Scheme \<pi> \<Longrightarrow> False"
  by (auto dest!: wf_unbound(1))

inductive_cases WfUnboundE: "\<turnstile> v : Unbound"
inductive_cases WfDUE: "\<turnstile> v : DU \<tau>"

lemma wf_unbound_entry: "\<turnstile> v : Unbound \<Longrightarrow> v = VUnbound" "\<turnstile> v : DU \<tau> \<Longrightarrow> v = VUnbound"
  by (auto elim!: WfUnboundE WfDUE simp: inst_entry_signature_entry split: if_splits)

fun wf_result :: "val result \<Rightarrow> ty \<Rightarrow> bool"
where
"wf_result (Val v) \<tau> = (\<turnstile> v : Ty \<tau>)" |
"wf_result (Aborts \<kappa>) \<tau> = (\<not> prevented \<kappa>)"

fun wf_results :: "val list result \<Rightarrow> ty list \<Rightarrow> bool"
where
"wf_results (Val vs) \<tau>s = list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s" |
"wf_results (Aborts \<kappa>) \<tau>s = (\<not> prevented \<kappa>)"

(* Completion of a statement checked at \<Gamma> and return type \<zeta> with static outcome R, run in \<rho> *)
fun wf_completion :: "(var \<times> ty) list \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> completion \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Assigns \<rho>') R =
  (\<exists>\<Delta>. bindings_of R = Some \<Delta> \<and> fmdom \<rho>' |\<subseteq>| fmdom \<Delta> \<and> \<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>)" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Returns v) R = (\<forall>\<tau>. \<zeta> = Some \<tau> \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>))" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Aborts\<^sub>\<omega> \<kappa>) R = (\<not> prevented \<kappa>)"

fun wf_outcome :: "(var \<times> ty) list \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> outcome \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (vs, \<omega>) R = wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R"

lemma wf_completion_bindings:
  "bindings_of R = bindings_of R' \<Longrightarrow> wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R = wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R'"
  by (cases \<omega>) simp_all

end

end
