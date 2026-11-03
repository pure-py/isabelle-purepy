(* Value and environment well-formedness; type soundness *)
theory Soundness
  imports "isabelle-purepy.Programs" "isabelle-purepy.Determinism"
begin

(* Free o for outcomes, as in the values theory, since the typing theories keep the composition notation *)
no_notation (ASCII) comp (infixl \<open>o\<close> 55)

(* Termination kinds ruled out by well-formedness *)
fun prevented :: "termination_kind \<Rightarrow> bool"
where
"prevented TypeError = True" |
"prevented AttributeError = True" |
"prevented NameError = True" |
"prevented Excluded = True" |
"prevented _ = False"

(* Type variables bound by a context *)
definition tyvars :: "cxt \<Rightarrow> var set"
where
"tyvars \<Gamma> = {\<alpha>. fmlookup \<Gamma> \<alpha> = Some TypeVar}"

fun fv_scheme :: "ty_scheme \<Rightarrow> var set"
where
"fv_scheme (TyScheme \<alpha>s \<tau>) = fv \<tau> - set \<alpha>s"

fun fv_entry :: "cxt_entry \<Rightarrow> var set"
where
"fv_entry (Ty \<tau>) = fv \<tau>" |
"fv_entry (DU \<tau>) = fv \<tau>" |
"fv_entry (PU \<tau> _) = fv \<tau>" |
"fv_entry (Scheme \<pi>) = fv_scheme \<pi>" |
"fv_entry (PUScheme \<pi> _) = fv_scheme \<pi>" |
"fv_entry _ = {}"

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

(* Static outcomes of the branches of an elif block, as listed by the if rule *)
type_synonym elif_block = "(expr located \<times> stmt located) list \<times> stmt located option"

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

(* Names declared in the branches of an elif block, and names bound by their patterns *)
fun declarations_elif :: "elif_block \<Rightarrow> var located list"
where
"declarations_elif (elifs, else') =
  concat (map (\<lambda>(_, s'). declarations_stmt s') elifs)
  @ (case else' of None \<Rightarrow> [] | Some s' \<Rightarrow> declarations_stmt s')"

fun binds_elif :: "elif_block \<Rightarrow> var set"
where
"binds_elif (elifs, else') =
  \<Union> (set (map (\<lambda>(_, s'). binds s') elifs)) \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> binds s')"

(* Declared names xs, distinct, disjoint from the pattern-bound names Y and unbound in \<Gamma>, as the scope function
   ensures for a function body or module *)
definition scoped :: "cxt \<Rightarrow> var list \<Rightarrow> var set \<Rightarrow> bool"
where
"scoped \<Gamma> xs Y = (distinct xs \<and> set xs \<inter> Y = {} \<and> (\<forall>x \<in> set xs. fmlookup \<Gamma> x = Some Unbound))"

(* Equations which rewrite unconditionally, to be used by name *)
declare check_expr.simps [simp del] callee.simps [simp del] elements_join.simps [simp del]
  check_args.simps [simp del]

lemma locate_Ok [simp]: "(locate p m = Ok x) = (m = Ok x)"
  by (cases m) (simp_all add: locate_def)

lemma var_scheme_None: "dotted_name e = None \<Longrightarrow> var_scheme \<Sigma> \<Gamma> e \<tau> = None"
  by (simp add: var_scheme_def scheme_of_name_def entry_of_def)

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
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; params_cxt xs \<sigma>s = Ok \<Delta> ; check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau> = Ok () \<rbrakk>
  \<Longrightarrow> \<turnstile> Lam(\<rho>, xs, e) : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>))" |
ValDef:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; check_stmt \<Sigma> \<Gamma> None (StmtMutualRegion ds) = Ok (Assigns\<^sub>R \<Delta> None) ; i < length ds
   ; node (ds ! i) = Def f \<alpha>s xps \<psi> s ; set \<alpha>s \<inter> tyvars \<Gamma> = {} ; fmlookup \<Delta> f = Some \<theta> \<rbrakk>
  \<Longrightarrow> \<turnstile> Def(\<rho>, ds, i) : inst_entry \<eta> \<theta>" |
ValInst:
  "\<lbrakk> \<turnstile> v : Scheme (TyScheme \<alpha>s \<sigma>) ; length \<tau>s = length \<alpha>s ; \<forall>\<tau> \<in> set \<tau>s. fv \<tau> = {} \<rbrakk>
  \<Longrightarrow> \<turnstile> v : Ty (subst \<tau>s \<alpha>s \<sigma>)" |
ValObj:
  "\<lbrakk> map fst xvs = field_names \<Sigma> C ; list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s) \<rbrakk>
  \<Longrightarrow> \<turnstile> VObject C xvs : Ty (TyClass C \<tau>s)" |
ValSub: "\<lbrakk> \<turnstile> v : Ty \<sigma> ; \<Sigma> \<turnstile> \<sigma> <: \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> v : Ty \<tau>" |
ValPrim:
  "\<lbrakk> fmlookup (\<E> \<A>) q = Some \<rho> ; fmlookup \<rho> x = Some (VPrim f) ; fmlookup \<P> q = Some \<Gamma> ; fmlookup \<Gamma> x = Some \<theta> \<rbrakk>
  \<Longrightarrow> \<turnstile> VPrim f : \<theta>" |
ValPredef: "\<turnstile> VPredef q : PredefName" |
ValMod: "\<turnstile> VModStub q : ModStub q" |
ValModLoaded: "[] \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> \<turnstile> VModLoaded q \<rho> : ModChecked q \<Gamma>" |
ValClass: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> \<turnstile> VClass C : Type C" |
ValTypeAlias: "\<turnstile> VTypeAlias q \<chi>s i : TypeAlias \<Gamma> q \<chi>s i" |
ValUnbound: "\<theta> = Unbound \<or> (\<exists>\<tau>. \<theta> = DU \<tau>) \<Longrightarrow> \<turnstile> VUnbound : \<theta>" |
ValPU: "v = VUnbound \<or> \<turnstile> v : Ty \<tau> \<Longrightarrow> \<turnstile> v : PU \<tau> b" |
ValPUScheme: "v = VUnbound \<or> \<turnstile> v : Scheme \<pi> \<Longrightarrow> \<turnstile> v : PUScheme \<pi> b" |

WfEnv:
  "\<lbrakk> closed_inst \<eta> ; tyvars \<Gamma> \<subseteq> set (map fst \<eta>)
   ; \<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> \<theta> \<noteq> TypeVar
       \<longrightarrow> fv_entry \<theta> \<subseteq> tyvars \<Gamma> \<and> (\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>) \<rbrakk>
  \<Longrightarrow> \<eta> \<turnstile> \<rho> : \<Gamma>"

inductive_cases WfEnvE: "\<eta> \<turnstile> \<rho> : \<Gamma>"

lemma wf_env_lookup:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; fmlookup \<Gamma> x = Some \<theta> ; \<theta> \<noteq> TypeVar \<rbrakk>
  \<Longrightarrow> \<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
  by (auto elim!: WfEnvE)

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
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Assigns \<rho>') R = (\<exists>\<Delta> r. R = Assigns\<^sub>R \<Delta> r \<and> \<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>)" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Returns v) R = (\<forall>\<tau>. \<zeta> = Some \<tau> \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>))" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Aborts\<^sub>\<omega> \<kappa>) R = (\<not> prevented \<kappa>)"

fun wf_outcome :: "(var \<times> ty) list \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> outcome \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (vs, \<omega>) R = wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R"

(* Soundness of one evaluation, at every context, instantiation and typing at which the construct checks *)
definition sound_expr :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"
where
"sound_expr \<rho> e r =
  (\<forall>\<eta> \<Gamma> \<tau>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> synth_expr \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr \<Sigma> \<Gamma> e \<tau> = Ok () \<longrightarrow> wf_result r (inst \<eta> \<tau>))"

definition sound_exprs :: "env \<Rightarrow> expr located list \<Rightarrow> val list result \<Rightarrow> bool"
where
"sound_exprs \<rho> es rs =
  (\<forall>\<eta> \<Gamma> \<tau>s. \<eta> \<turnstile> \<rho> : \<Gamma>
     \<longrightarrow> list_all2 (\<lambda>e \<tau>. synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()) es \<tau>s
     \<longrightarrow> wf_results rs (map (inst \<eta>) \<tau>s))"

definition sound_stmt :: "env \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_stmt \<rho> s o =
  (\<forall>\<eta> \<Gamma> \<zeta> R. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> scoped \<Gamma> (declares s) (binds (At no_pos s)) \<longrightarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R
     \<longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R)"

definition sound_elif :: "env \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_elif \<rho> eb o =
  (\<forall>\<eta> \<Gamma> \<zeta> Rs. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> scoped \<Gamma> (map node (declarations_elif eb)) (binds_elif eb)
     \<longrightarrow> those_sum (check_elif \<Sigma> \<Gamma> \<zeta> eb) = Ok Rs \<longrightarrow> (\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R))"

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
  (\<forall>\<eta> \<Gamma> \<tau> \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> (\<forall>u \<in> set us. \<turnstile> u : Ty (inst \<eta> \<tau>))
     \<longrightarrow> quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs = Ok \<Delta>
     \<longrightarrow> wf_envs \<eta> r (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>))"

fun wf_elems :: "val list result \<Rightarrow> ty \<Rightarrow> bool"
where
"wf_elems (Val vs) \<tau> = (\<forall>v \<in> set vs. \<turnstile> v : Ty \<tau>)" |
"wf_elems (Aborts \<kappa>) \<tau> = (\<not> prevented \<kappa>)"

definition sound_comp :: "env list \<Rightarrow> expr located \<Rightarrow> val list result \<Rightarrow> bool"
where
"sound_comp \<rho>s e r =
  (\<forall>\<eta> \<Gamma> \<tau>. (\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) \<longrightarrow> synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()
     \<longrightarrow> wf_elems r (inst \<eta> \<tau>))"

fun wf_entries :: "(str \<times> val) list result \<Rightarrow> ty \<Rightarrow> bool"
where
"wf_entries (Val \<delta>) \<tau> = (\<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau>)" |
"wf_entries (Aborts \<kappa>) \<tau> = (\<not> prevented \<kappa>)"

definition sound_entries :: "env list \<Rightarrow> expr located \<Rightarrow> expr located \<Rightarrow> (str \<times> val) list result \<Rightarrow> bool"
where
"sound_entries \<rho>s e e' r =
  (\<forall>\<eta> \<Gamma> \<tau>. (\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>) \<longrightarrow> check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()
     \<longrightarrow> synth_expr_at \<Sigma> \<Gamma> e' = Ok \<tau> \<or> check_expr_at \<Sigma> \<Gamma> e' \<tau> = Ok () \<longrightarrow> wf_entries r (inst \<eta> \<tau>))"


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
  and check: "\<And>\<eta> \<Gamma> \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr' \<Sigma> \<Gamma> e \<tau> = Some (Ok ()) \<rbrakk> \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
  shows "sound_expr \<rho> e r"
  unfolding sound_expr_def by (blast dest: check_expr_cases synth check wf_result_sub)

lemma sound_expr_synth_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<rbrakk> \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def)

lemma sound_expr_check_at:
  "\<lbrakk> sound_expr \<rho> (node e) r ; \<eta> \<turnstile> \<rho> : \<Gamma> ; check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok () \<rbrakk> \<Longrightarrow> wf_result r (inst \<eta> \<tau>)"
  by (cases e) (auto simp: sound_expr_def)

lemmas sound_expr_at = sound_expr_synth_at sound_expr_check_at

lemma wf_lit_bool: "\<turnstile> VLit (LitBool b) : Ty (TyPrim bool)"
  by (rule ValSub[OF ValLit], rule SubtyLiteral) (simp add: SubtyRefl)


subsection \<open>Canonical forms\<close>

lemma wf_bool: "\<lbrakk> \<turnstile> v : Ty \<tau> ; \<Sigma> \<turnstile> \<tau> <: TyPrim bool \<rbrakk> \<Longrightarrow> v = true \<or> v = false"
  sorry

lemma wf_str: "\<lbrakk> \<turnstile> v : Ty \<tau> ; \<Sigma> \<turnstile> \<tau> <: TyPrim str \<rbrakk> \<Longrightarrow> \<exists>w. v = VLit (LitString w)"
  sorry

(* Operands checked as Booleans or strings *)
lemma bool_operand:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()"
  shows "v = true \<or> v = false"
  using sound_expr_check_at[OF assms] by (auto dest!: wf_bool[OF _ SubtyRefl])

lemma bool_operand_abort:
  assumes "sound_expr \<rho> (node e) (Aborts \<kappa>)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()"
  shows "\<not> prevented \<kappa>"
  using sound_expr_check_at[OF assms] by simp

lemma str_operand:
  assumes "sound_expr \<rho> (node e) (Val v)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()"
  shows "\<exists>w. v = VLit (LitString w)"
  using sound_expr_check_at[OF assms] by (auto dest!: wf_str[OF _ SubtyRefl])

lemma str_operand_abort:
  assumes "sound_expr \<rho> (node e) (Aborts \<kappa>)" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr_at \<Sigma> \<Gamma> e (TyPrim str) = Ok ()"
  shows "\<not> prevented \<kappa>"
  using sound_expr_check_at[OF assms] by simp


subsection \<open>Expressions\<close>

lemma var_sound: "\<lbrakk> fmlookup \<rho> x = Some v ; v \<noteq> VUnbound \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprVar x) (Val v)"
  sorry

lemma var_unknown_sound: "fmlookup \<rho> x = None \<Longrightarrow> sound_expr \<rho> (ExprVar x) (Aborts NameError)"
  unfolding sound_expr_def
  by (auto simp: var_scheme_def scheme_of_name_def entry_of_def resolve_name_def
      dest!: check_expr_cases wf_env_lookup split: option.splits cxt_entry.splits)

lemma var_unbound_sound: "fmlookup \<rho> x = Some VUnbound \<Longrightarrow> sound_expr \<rho> (ExprVar x) (Aborts NameError)"
  sorry

lemma literal_sound: "sound_expr \<rho> (ExprLiteral l) (Val (VLit l))"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume "synth_expr \<Sigma> \<Gamma> (ExprLiteral l) = Ok \<tau>"
  then show "wf_result (Val (VLit l)) (inst \<eta> \<tau>)" by (cases l) (auto intro: ValLit ValLitFloat)
next
  fix \<eta> \<Gamma> \<tau>
  assume "check_expr' \<Sigma> \<Gamma> (ExprLiteral l) \<tau> = Some (Ok ())"
  then show "wf_result (Val (VLit l)) (inst \<eta> \<tau>)"
    by (simp add: var_scheme_def scheme_of_name_def entry_of_def split: option.splits)
qed

lemma lambda_sound: "sound_expr \<rho> (ExprLambda xs e) (Val Lam(\<rho>, xs, e))"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume "synth_expr \<Sigma> \<Gamma> (ExprLambda xs e) = Ok \<tau>"
  then show "wf_result (Val Lam(\<rho>, xs, e)) (inst \<eta> \<tau>)" by simp
next
  fix \<eta> \<Gamma> \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "check_expr' \<Sigma> \<Gamma> (ExprLambda xs e) \<tau> = Some (Ok ())"
  then show "wf_result (Val Lam(\<rho>, xs, e)) (inst \<eta> \<tau>)"
    by (auto simp: bind_sum_def intro!: ValLambda[simplified] split: ty.splits if_splits sum.splits)
qed

lemma unop_sound: "sound_expr \<rho> (node e) r \<Longrightarrow> sound_expr \<rho> (ExprUnOp op e) (mlet r (unop_meaning op))"
  sorry

lemma binop_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; sound_expr \<rho> (node e') r \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprBinOp op e e') (mlet r (binop_meaning op v))"
  sorry

lemma binop_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprBinOp op e e') (Aborts \<kappa>)"
  sorry

lemma and_false_sound: "sound_expr \<rho> (node e) (Val false) \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Val false)"
  by (rule sound_exprI) (auto simp: bind_sum_def var_scheme_None intro: wf_lit_bool split: sum.splits)

lemma and_true_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val true) ; sound_expr \<rho> (node e') r \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') r"
  sorry

lemma and_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Aborts \<kappa>)"
  sorry

lemma and_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprAnd e e') (Aborts Excluded)"
  sorry

lemma or_true_sound: "sound_expr \<rho> (node e) (Val true) \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Val true)"
  sorry

lemma or_false_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val false) ; sound_expr \<rho> (node e') r \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprOr e e') r"
  sorry

lemma or_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Aborts \<kappa>)"
  sorry

lemma or_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprOr e e') (Aborts Excluded)"
  sorry

lemma cond_true_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val true) ; sound_expr \<rho> (node e1) r \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) r"
  sorry

lemma cond_false_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val false) ; sound_expr \<rho> (node e2) r \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) r"
  sorry

lemma cond_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) (Aborts \<kappa>)"
  sorry

lemma cond_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_expr \<rho> (ExprCond e1 e e2) (Aborts Excluded)"
  sorry

lemma list_sound: "sound_exprs \<rho> es (Val vs) \<Longrightarrow> sound_expr \<rho> (ExprList es) (Val (VList vs))"
  sorry

lemma list_fail_sound: "sound_exprs \<rho> es (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprList es) (Aborts \<kappa>)"
  sorry

lemma tuple_sound: "sound_exprs \<rho> es (Val vs) \<Longrightarrow> sound_expr \<rho> (ExprTuple es) (Val (VTuple vs))"
  sorry

lemma tuple_fail_sound: "sound_exprs \<rho> es (Aborts \<kappa>) \<Longrightarrow> sound_expr \<rho> (ExprTuple es) (Aborts \<kappa>)"
  sorry

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
  sorry

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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and "list_all2 (\<lambda>e \<tau>. synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()) (e # es) \<tau>s"
  then obtain \<tau> \<tau>s' where \<tau>s: "\<tau>s = \<tau> # \<tau>s'"
    and e: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()"
    and es: "list_all2 (\<lambda>e \<tau>. synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()) es \<tau>s'"
    by (auto simp: list_all2_Cons1)
  from assms(1) env e have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_at)
  moreover from assms(2) env es have "wf_results r (map (inst \<eta>) \<tau>s')" by (simp add: sound_exprs_def)
  ultimately show "wf_results (mlet r (\<lambda>vs. Val (v # vs))) (map (inst \<eta>) \<tau>s)" by (cases r) (simp_all add: \<tau>s)
qed

lemma exprs_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_exprs \<rho> (e # es) (Aborts \<kappa>)"
  unfolding sound_exprs_def by (auto simp: list_all2_Cons1 dest: sound_expr_at)


subsection \<open>Statements\<close>

lemma pass_sound: "sound_stmt \<rho> StmtPass (assigns\<^sub>o \<epsilon>)"
  sorry

lemma declare_sound: "sound_stmt \<rho> (StmtDeclare x \<psi>) (assigns\<^sub>o \<epsilon>)"
  sorry

lemma assign_sound:
  "sound_expr \<rho> (node e) r \<Longrightarrow> sound_stmt \<rho> (StmtAssign x \<pi> e) (mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>)))"
  sorry

lemma expr_stmt_sound: "sound_expr \<rho> (node e) r \<Longrightarrow> sound_stmt \<rho> (StmtExpr e) (mlet r (\<lambda>v. assigns\<^sub>o \<epsilon>))"
  sorry

lemma print_sound: "sound_expr \<rho> (node e) r \<Longrightarrow> sound_stmt \<rho> (StmtPrint e) (mlet r (\<lambda>v. ([v], Assigns \<epsilon>)))"
  sorry

lemma return_sound: "sound_expr \<rho> (node e) r \<Longrightarrow> sound_stmt \<rho> (StmtReturn (Some e)) (mlet r returns\<^sub>o)"
  sorry

lemma return_none_sound: "sound_stmt \<rho> (StmtReturn None) (returns\<^sub>o (VLit LitNone))"
  sorry

lemma defs_sound:
  "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]
  \<Longrightarrow> sound_stmt \<rho> (StmtMutualRegion ds) (assigns\<^sub>o (fmap_of_list (zip (map (def_name \<circ> node) ds) vs)))"
  sorry

lemma assert_sound: "sound_expr \<rho> (node e) (Val true) \<Longrightarrow> sound_stmt \<rho> (StmtAssert e None) (assigns\<^sub>o \<epsilon>)"
  sorry

lemma assert_false_sound:
  "sound_expr \<rho> (node e) (Val false) \<Longrightarrow> sound_stmt \<rho> (StmtAssert e None) (aborts\<^sub>o (AssertionError None))"
  sorry

lemma assert_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtAssert e None) (aborts\<^sub>o \<kappa>)"
  sorry

lemma assert_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> sound_stmt \<rho> (StmtAssert e None) (aborts\<^sub>o Excluded)"
  sorry

lemma assert_msg_sound: "sound_expr \<rho> (node e) (Val true) \<Longrightarrow> sound_stmt \<rho> (StmtAssert e (Some e')) (assigns\<^sub>o \<epsilon>)"
  sorry

lemma assert_msg_false_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val false) ; sound_expr \<rho> (node e') (Val (VLit (LitString w))) \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o (AssertionError (Some w)))"
  sorry

lemma assert_msg_false_fail_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val false) ; sound_expr \<rho> (node e') (Aborts \<kappa>) \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o \<kappa>)"
  sorry

lemma assert_msg_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o \<kappa>)"
  sorry

lemma assert_msg_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o Excluded)"
  sorry

lemma assert_msg_nonstr_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val false) ; sound_expr \<rho> (node e') (Val v) ; \<forall>w. v \<noteq> VLit (LitString w) \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o Excluded)"
  sorry

lemma if_true_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val true) ; sound_stmt \<rho> (node s) o \<rbrakk> \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') o"
  sorry

lemma if_false_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val false) ; sound_elif \<rho> (elifs, else') o \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') o"
  sorry

lemma if_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') (aborts\<^sub>o \<kappa>)"
  sorry

lemma if_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') (aborts\<^sub>o Excluded)"
  sorry

lemma match_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; dispatch \<rho> v cases = Val (\<rho>', s') ; sound_stmt (\<rho> \<otimes> \<rho>') (node s') o \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (assigns\<^sub>o \<rho>' \<otimes>\<^sub>o o)"
  sorry

lemma match_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
  sorry

lemma match_abort_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; dispatch \<rho> v cases = Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
  sorry

lemma seq_sound:
  "\<lbrakk> sound_stmt \<rho> (node s) (us, Assigns \<rho>') ; sound_stmt (\<rho> \<otimes> \<rho>') (node s') o \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtSeq s s') ((us, Assigns \<rho>') \<otimes>\<^sub>o o)"
  sorry

lemma seq_return_sound: "sound_stmt \<rho> (node s) (us, Returns v) \<Longrightarrow> sound_stmt \<rho> (StmtSeq s s') (us, Returns v)"
  sorry

lemma seq_fail_sound: "sound_stmt \<rho> (node s) (us, Aborts\<^sub>\<omega> \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtSeq s s') (us, Aborts\<^sub>\<omega> \<kappa>)"
  sorry

lemma if_none_sound: "sound_elif \<rho> ([], None) (assigns\<^sub>o \<epsilon>)"
  sorry

lemma else_sound: "sound_stmt \<rho> (node s) o \<Longrightarrow> sound_elif \<rho> ([], Some s) o"
  sorry

lemma elif_true_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val true) ; sound_stmt \<rho> (node s) o \<rbrakk> \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') o"
  sorry

lemma elif_false_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val false) ; sound_elif \<rho> (elifs, else') o \<rbrakk>
  \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') o"
  sorry

lemma elif_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') (aborts\<^sub>o \<kappa>)"
  sorry

lemma elif_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') (aborts\<^sub>o Excluded)"
  sorry


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
  sorry

lemma qual_generator_nonseq_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; iter v = None \<rbrakk>
  \<Longrightarrow> sound_quals \<rho> (At p (Generator x e) # gs) (Aborts TypeError)"
  sorry

lemma gen_nil_sound: "sound_gen \<rho> x [] gs (Val [])"
  by (simp add: sound_gen_def)

lemma gen_cons_sound:
  "\<lbrakk> sound_quals (fmupd x u \<rho>) gs (Val \<rho>s) ; sound_gen \<rho> x us gs r \<rbrakk>
  \<Longrightarrow> sound_gen \<rho> x (u # us) gs (mlet r (\<lambda>\<rho>ss. Val (\<rho>s @ \<rho>ss)))"
  sorry

lemma gen_fail_sound: "sound_quals (fmupd x u \<rho>) gs (Aborts \<kappa>) \<Longrightarrow> sound_gen \<rho> x (u # us) gs (Aborts \<kappa>)"
  sorry

lemma comp_nil_sound: "sound_comp [] e (Val [])"
  by (simp add: sound_comp_def)

lemma comp_cons_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and "sound_comp \<rho>s e r"
  shows "sound_comp (\<rho> # \<rho>s) e (mlet r (\<lambda>vs. Val (v # vs)))"
  unfolding sound_comp_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume envs: "\<forall>\<rho> \<in> set (\<rho> # \<rho>s). \<eta> \<turnstile> \<rho> : \<Gamma>"
    and e: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau> \<or> check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()"
  from assms(1) envs e have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_at)
  moreover from envs have "\<forall>\<rho> \<in> set \<rho>s. \<eta> \<turnstile> \<rho> : \<Gamma>" by simp
  with assms(2) e have "wf_elems r (inst \<eta> \<tau>)" unfolding sound_comp_def by blast
  ultimately show "wf_elems (mlet r (\<lambda>vs. Val (v # vs))) (inst \<eta> \<tau>)" by (cases r) simp_all
qed

lemma comp_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_comp (\<rho> # \<rho>s) e (Aborts \<kappa>)"
  unfolding sound_comp_def by (auto dest: sound_expr_at)

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
    and e': "synth_expr_at \<Sigma> \<Gamma> e' = Ok \<tau> \<or> check_expr_at \<Sigma> \<Gamma> e' \<tau> = Ok ()"
  from assms(2) envs e' have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_at)
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
  unfolding sound_entries_def by (auto dest: sound_expr_at)


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
