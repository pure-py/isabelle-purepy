(* Value and environment typing *)
theory ValueTyping
  imports WellFormed "isabelle-purepy.Determinism"
begin

subsection \<open>Instantiation of type variables\<close>

(* Application of a closing type substitution, given as a list of pairs *)
abbreviation inst :: "(var \<times> ty) list \<Rightarrow> ty \<Rightarrow> ty"
where
"inst \<eta> \<equiv> subst (map snd \<eta>) (map fst \<eta>)"

definition closed_inst :: "(var \<times> ty) list \<Rightarrow> bool"
where
"closed_inst \<eta> = (\<forall>\<alpha> \<tau>. (\<alpha>, \<tau>) \<in> set \<eta> \<longrightarrow> fv \<tau> = {})"

(* Instantiation at well-formed types *)
definition wf_inst :: "class_table \<Rightarrow> (var \<times> ty) list \<Rightarrow> bool"
where
"wf_inst \<Sigma> \<eta> = (\<forall>\<alpha> \<tau>. (\<alpha>, \<tau>) \<in> set \<eta> \<longrightarrow> wf_ty \<Sigma> \<tau>)"

lemma inst_wf: "\<lbrakk> wf_inst \<Sigma> \<eta> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> (inst \<eta> \<tau>)"
  by (rule wf_ty_subst) (auto simp: wf_inst_def)

lemma wf_inst_filter: "wf_inst \<Sigma> \<eta> \<Longrightarrow> wf_inst \<Sigma> (filter P \<eta>)"
  by (auto simp: wf_inst_def)

lemma wf_ty_subst_inv: "wf_ty \<Sigma> (subst \<tau>s \<alpha>s \<sigma>) \<Longrightarrow> wf_ty \<Sigma> \<sigma>"
  by (induction \<sigma>) auto

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

lemma inst_entry_wf:
  assumes "wf_inst \<Sigma> \<eta>" and "wf_entry \<Sigma> \<theta>"
  shows "wf_entry \<Sigma> (inst_entry \<eta> \<theta>)"
proof (cases \<theta>)
  case (Scheme \<pi>)
  then show ?thesis using assms by (cases \<pi>) (auto intro: inst_wf wf_inst_filter)
next
  case (PUScheme \<pi> b)
  then show ?thesis using assms by (cases \<pi>) (auto intro: inst_wf wf_inst_filter)
qed (use assms in \<open>auto intro: inst_wf\<close>)

lemma inst_scheme_Nil [simp]: "inst_scheme [] \<pi> = \<pi>"
  by (cases \<pi>) simp

lemma inst_entry_Nil [simp]: "inst_entry [] \<theta> = \<theta>"
  by (cases \<theta>) simp_all

lemma inst_scheme_closed: "fv_scheme \<pi> = {} \<Longrightarrow> inst_scheme \<eta> \<pi> = \<pi>"
  by (cases \<pi>) (force intro!: subst_fresh)

lemma inst_entry_closed: "fv_entry \<theta> = {} \<Longrightarrow> inst_entry \<eta> \<theta> = \<theta>"
  by (cases \<theta>) (simp_all add: subst_closed inst_scheme_closed)

lemma inst_cong:
  assumes "\<And>\<alpha>. \<alpha> \<in> fv \<sigma> \<Longrightarrow> map_of \<eta> \<alpha> = map_of \<eta>' \<alpha>"
  shows "inst \<eta> \<sigma> = inst \<eta>' \<sigma>"
  using assms by (intro subst_cong) (simp add: zip_map_fst_snd)

lemma inst_entry_cong:
  assumes "\<And>\<alpha>. \<alpha> \<in> fv_entry \<theta> \<Longrightarrow> map_of \<eta> \<alpha> = map_of \<eta>' \<alpha>"
  shows "inst_entry \<eta> \<theta> = inst_entry \<eta>' \<theta>"
proof (cases \<theta>)
  case (Scheme \<pi>)
  then show ?thesis using assms by (cases \<pi>) (auto simp: map_of_filter_key intro!: inst_cong)
next
  case (PUScheme \<pi> b)
  then show ?thesis using assms by (cases \<pi>) (auto simp: map_of_filter_key intro!: inst_cong)
qed (use assms in \<open>auto intro!: inst_cong\<close>)

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

(* Instantiation of the type parameters \<alpha>s at \<tau>s, shadowing their bindings in \<eta> *)
definition inst_params :: "var list \<Rightarrow> ty list \<Rightarrow> (var \<times> ty) list \<Rightarrow> (var \<times> ty) list"
where
"inst_params \<alpha>s \<tau>s \<eta> = zip \<alpha>s \<tau>s @ filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>"

lemma map_of_inst_params:
  "length \<tau>s = length \<alpha>s
  \<Longrightarrow> map_of (inst_params \<alpha>s \<tau>s \<eta>) \<alpha> = (if \<alpha> \<in> set \<alpha>s then map_of (zip \<alpha>s \<tau>s) \<alpha> else map_of \<eta> \<alpha>)"
  by (auto simp: inst_params_def map_of_filter_key map_of_zip_is_None map_add_def split: option.splits
      dest: map_of_SomeD set_zip_leftD)

lemma fst_inst_params: "length \<tau>s = length \<alpha>s \<Longrightarrow> fst ` set (inst_params \<alpha>s \<tau>s \<eta>) = set \<alpha>s \<union> fst ` set \<eta>"
proof -
  assume "length \<tau>s = length \<alpha>s"
  then have zip: "fst ` set (zip \<alpha>s \<tau>s) = set \<alpha>s" by (metis map_fst_zip set_map)
  have filter: "fst ` set (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) = fst ` set \<eta> - set \<alpha>s"
    by (auto simp: image_iff case_prod_beta)
  show ?thesis unfolding inst_params_def set_append image_Un zip filter by auto
qed

lemma closed_inst_params:
  "\<lbrakk> closed_inst \<eta> ; \<forall>\<tau> \<in> set \<tau>s. fv \<tau> = {} \<rbrakk> \<Longrightarrow> closed_inst (inst_params \<alpha>s \<tau>s \<eta>)"
  by (auto simp: closed_inst_def inst_params_def dest: set_zip_rightD)

lemma wf_inst_params:
  "\<lbrakk> wf_inst \<Sigma> \<eta> ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_inst \<Sigma> (inst_params \<alpha>s \<tau>s \<eta>)"
  by (auto simp: wf_inst_def inst_params_def dest: set_zip_rightD)

lemma inst_inst_params:
  assumes "closed_inst \<eta>" and "length \<tau>s = length \<alpha>s"
  shows "inst (inst_params \<alpha>s \<tau>s \<eta>) \<sigma> = subst \<tau>s \<alpha>s (inst (filter (\<lambda>(\<alpha>, _). \<alpha> \<notin> set \<alpha>s) \<eta>) \<sigma>)"
proof (induction \<sigma>)
  case (TyVar \<beta>)
  show ?case
    using assms
    by (auto simp: zip_map_fst_snd map_of_inst_params map_of_filter_key map_of_zip_is_None closed_inst_def
        subst_closed split: option.splits dest!: map_of_SomeD dest: set_zip_leftD)
qed (simp_all cong: map_cong)

(* Type scheme of a function signature *)
fun callable_scheme :: "ty_scheme \<Rightarrow> bool"
where
"callable_scheme (TyScheme _ (TyCallable _ _)) = True" |
"callable_scheme _ = False"

context evaluation
begin

inductive wf_val :: "val \<Rightarrow> cxt_entry \<Rightarrow> bool" ("\<turnstile> _ : _" [51, 51] 50)
and wf_env :: "(var \<times> ty) list \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> bool" ("_ \<turnstile> _ : _" [51, 51, 51] 50)
where
ValLit: "\<turnstile> VLit l : Ty (TyLiteral l)" |
ValLitFloat: "\<turnstile> VLit (LitFloat x) : Ty (TyPrim float)" |
ValList: "\<lbrakk> \<forall>v \<in> set vs. \<turnstile> v : Ty \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> VList vs : Ty (TyList \<tau>)" |
ValTuple: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s \<Longrightarrow> \<turnstile> VTuple vs : Ty (TyTuple \<tau>s)" |
ValDict:
  "\<lbrakk> \<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau> ; distinct (map fst \<delta>) ; wf_ty \<Sigma> \<tau> \<rbrakk>
  \<Longrightarrow> \<turnstile> VDict \<delta> : Ty (TyDict \<tau>)" |
ValLambda:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; length xs = length \<sigma>s ; params_cxt xs \<sigma>s = Ok \<Delta> ; check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau> = Ok ()
   ; fv (TyCallable \<sigma>s \<tau>) \<subseteq> fst ` set \<eta> ; wf_ty \<Sigma> (TyCallable \<sigma>s \<tau>) \<rbrakk>
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
  "\<lbrakk> \<turnstile> v : Scheme (TyScheme \<alpha>s \<sigma>) ; length \<tau>s = length \<alpha>s ; \<forall>\<tau> \<in> set \<tau>s. fv \<tau> = {}
   ; \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau> \<rbrakk>
  \<Longrightarrow> \<turnstile> v : Ty (subst \<tau>s \<alpha>s \<sigma>)" |
ValObj:
  "\<lbrakk> wf_ty \<Sigma> (TyClass C \<tau>s) ; map fst xvs = field_names \<Sigma> C
   ; list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xvs) (field_types \<Sigma> C \<tau>s) \<rbrakk>
  \<Longrightarrow> \<turnstile> VObject C xvs : Ty (TyClass C \<tau>s)" |
ValSub: "\<lbrakk> \<turnstile> v : Ty \<sigma> ; \<Sigma> \<turnstile> \<sigma> <: \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> v : Ty \<tau>" |
ValPrim:
  "\<lbrakk> fmlookup (\<E> \<A>) q = Some \<rho> ; fmlookup \<rho> x = Some (VPrim f) ; fmlookup \<P> q = Some \<Gamma>
   ; fmlookup \<Gamma> x = Some \<theta> \<rbrakk>
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
  "\<lbrakk> closed_inst \<eta> ; wf_inst \<Sigma> \<eta> ; tyvars \<Gamma> \<subseteq> fst ` set \<eta> ; wf_cxt \<Sigma> \<Gamma>
   ; \<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> \<theta> \<noteq> TypeVar \<longrightarrow> (\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>) \<rbrakk>
  \<Longrightarrow> \<eta> \<turnstile> \<rho> : \<Gamma>"

inductive_cases WfEnvE: "\<eta> \<turnstile> \<rho> : \<Gamma>"

lemma wf_env_closed: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> closed_inst \<eta>"
  by (auto elim!: WfEnvE)

lemma wf_env_wf_inst: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> wf_inst \<Sigma> \<eta>"
  by (auto elim!: WfEnvE)

lemma wf_env_wf_cxt: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> wf_cxt \<Sigma> \<Gamma>"
  by (auto elim!: WfEnvE)

lemma wf_env_tyvars: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> tyvars \<Gamma> \<subseteq> fst ` set \<eta>"
  by (auto elim!: WfEnvE)

lemma wf_env_fv: "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; fv (\<tau> :: ty) \<subseteq> tyvars \<Gamma> \<rbrakk> \<Longrightarrow> fv \<tau> \<subseteq> fst ` set \<eta>"
  using wf_env_tyvars by blast

lemma wf_env_scheme:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "fmlookup \<Gamma> x = Some (Scheme \<pi>)"
  shows "callable_scheme \<pi>"
  using wf_cxt_lookup[OF wf_env_wf_cxt[OF assms(1)] assms(2)] by (cases \<pi>) auto

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
    and "wf_cxt \<Sigma> \<Delta>"
  shows "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>"
proof (rule WfEnv)
  show "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>)" using wf_env_wf_cxt[OF assms(1)] assms(5) by (rule wf_cxt_add)
  show "closed_inst \<eta>" using assms(1) by (rule wf_env_closed)
  show "wf_inst \<Sigma> \<eta>" using assms(1) by (rule wf_env_wf_inst)
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

(* Instantiation agreeing with \<eta> on the type variables of the context *)
lemma wf_env_inst:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "closed_inst \<eta>'" and "wf_inst \<Sigma> \<eta>'"
    and agree: "\<And>\<alpha>. \<alpha> \<in> tyvars \<Gamma> \<Longrightarrow> map_of \<eta>' \<alpha> = map_of \<eta> \<alpha>"
  shows "\<eta>' \<turnstile> \<rho> : \<Gamma>"
proof (rule WfEnv[OF assms(2, 3)])
  show "wf_cxt \<Sigma> \<Gamma>" using assms(1) by (rule wf_env_wf_cxt)
  show "tyvars \<Gamma> \<subseteq> fst ` set \<eta>'"
  proof
    fix \<alpha>
    assume \<alpha>: "\<alpha> \<in> tyvars \<Gamma>"
    with wf_env_tyvars[OF assms(1)] have "\<alpha> \<in> fst ` set \<eta>" by blast
    then have "map_of \<eta> \<alpha> \<noteq> None" by (simp add: map_of_eq_None_iff)
    then have "map_of \<eta>' \<alpha> \<noteq> None" by (simp add: agree[OF \<alpha>])
    then show "\<alpha> \<in> fst ` set \<eta>'" by (simp add: map_of_eq_None_iff)
  qed
  show "\<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> \<theta> \<noteq> TypeVar \<longrightarrow> (\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta>' \<theta>)"
  proof (intro allI impI)
    fix x \<theta>
    assume look: "fmlookup \<Gamma> x = Some \<theta>" and "\<theta> \<noteq> TypeVar"
    have "inst_entry \<eta>' \<theta> = inst_entry \<eta> \<theta>" using agree tyvars_entry[OF look] by (intro inst_entry_cong) blast
    with wf_env_lookup[OF assms(1) look \<open>\<theta> \<noteq> TypeVar\<close>]
    show "\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta>' \<theta>" by simp
  qed
qed

(* Type parameters brought into scope *)
lemma wf_env_type_params:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "set \<alpha>s \<subseteq> fst ` set \<eta>"
  shows "\<eta> \<turnstile> \<rho> : \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar"
proof -
  have "\<eta> \<turnstile> \<rho> \<otimes> fmempty : \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar"
  proof (rule wf_env_add[OF assms(1)])
    show "tyvars (fmconst (set \<alpha>s) TypeVar) \<subseteq> fst ` set \<eta>" using tyvars_fmconst assms(2) by blast
  qed (auto dest!: fmconst_entry intro!: wf_cxt_fmconst)
  then show ?thesis by simp
qed

(* Variables of a scope, unbound *)
lemma wf_env_unbound:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>"
  shows "\<eta> \<turnstile> \<rho> \<otimes> fmconst A VUnbound : \<Gamma> \<otimes> fmconst A Unbound"
proof (rule wf_env_add[OF assms])
  show "tyvars (fmconst A Unbound) \<subseteq> fst ` set \<eta>"
    by (auto simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff dest!: fmconst_entry)
  show "fmdom (fmconst A VUnbound) |\<subseteq>| fmdom (fmconst A Unbound)"
    unfolding fmconst_map[of A VUnbound Unbound] by simp
  show "\<exists>v. fmlookup (\<rho> \<otimes> fmconst A VUnbound) x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
    if "fmlookup (fmconst A Unbound) x = Some \<theta>" for x \<theta>
  proof -
    from that have mem: "x |\<in>| fmdom (fmconst A VUnbound)"
      unfolding fmconst_map[of A VUnbound Unbound] by (simp add: fmlookup_dom_iff)
    then obtain v where v: "fmlookup (fmconst A VUnbound) x = Some v" by (auto simp: fmlookup_dom_iff)
    from fmconst_entry[OF v] fmconst_entry[OF that] have "\<turnstile> v : inst_entry \<eta> \<theta>" by (simp add: ValUnbound)
    with mem v show ?thesis by simp
  qed
qed (auto dest!: fmconst_entry intro!: wf_cxt_fmconst)

lemma wf_env_upd:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<theta> \<noteq> TypeVar" and "fv_entry \<theta> \<subseteq> fst ` set \<eta>" and "\<turnstile> v : inst_entry \<eta> \<theta>"
    and "wf_entry \<Sigma> \<theta>"
  shows "\<eta> \<turnstile> fmupd x v \<rho> : fmupd x \<theta> \<Gamma>"
proof -
  have "\<eta> \<turnstile> \<rho> \<otimes> fmupd x v fmempty : \<Gamma> \<otimes> fmupd x \<theta> fmempty"
    using assms by (intro wf_env_add) (auto simp: tyvars_single intro: wf_cxt_upd split: if_splits)
  then show ?thesis by simp
qed

(* Rebinding in the context alone *)
lemma wf_env_upd_cxt:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<theta> \<noteq> TypeVar" and "fv_entry \<theta> \<subseteq> fst ` set \<eta>" and "fmlookup \<rho> x = Some v"
    and "\<turnstile> v : inst_entry \<eta> \<theta>" and "wf_entry \<Sigma> \<theta>"
  shows "\<eta> \<turnstile> \<rho> : fmupd x \<theta> \<Gamma>"
proof -
  have "fmupd x v \<rho> = \<rho>" using assms(4) by (intro fmap_ext) auto
  with wf_env_upd[OF assms(1-3,5,6), of x] show ?thesis by simp
qed

lemma wf_unbound:
  "\<turnstile> v : \<theta> \<Longrightarrow> v = VUnbound \<longrightarrow> \<theta> = Unbound \<or> (\<exists>\<tau>. \<theta> = DU \<tau>) \<or> (\<exists>\<tau> b. \<theta> = PU \<tau> b) \<or> (\<exists>\<pi> b. \<theta> = PUScheme \<pi> b)"
  "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
  by (induction rule: wf_val_wf_env.inducts) (auto simp: inst_entry_signature_entry split: if_splits)

lemma wf_unbound_ty: "\<turnstile> VUnbound : Ty \<tau> \<Longrightarrow> False"
  and wf_unbound_scheme: "\<turnstile> VUnbound : Scheme \<pi> \<Longrightarrow> False"
  by (auto dest!: wf_unbound(1))

(* Contexts of the predefined modules, well-formed *)
lemma predefined_cxt_wf: "fmlookup \<P> q = Some \<Gamma> \<Longrightarrow> wf_cxt \<Sigma> \<Gamma>"
proof -
  have "range_class |\<in>| fmdom \<Sigma>" using range_lookup by (simp add: predefined_classes_def fmlookup_dom_iff)
  then show "fmlookup \<P> q = Some \<Gamma> \<Longrightarrow> wf_cxt \<Sigma> \<Gamma>"
    by (auto simp: \<P>_def fmlookup_of_list wf_cxt_iff split: if_splits)
qed

lemma wf_range_class: "wf_ty \<Sigma> (TyClass range_class [])"
  using range_lookup by (simp add: predefined_classes_def fmlookup_dom_iff type_params_def)

lemma wf_entry_cases:
  "wf_entry \<Sigma> \<theta> \<Longrightarrow> (\<forall>\<tau>. \<theta> = Ty \<tau> \<longrightarrow> wf_ty \<Sigma> \<tau>) \<and> (\<forall>\<pi>. \<theta> = Scheme \<pi> \<longrightarrow> wf_entry \<Sigma> (Scheme \<pi>))"
  by auto

(* Type or scheme at which a value is typed, well-formed *)
lemma wf_val_wf:
  "\<turnstile> v : \<theta> \<Longrightarrow> (\<forall>\<tau>. \<theta> = Ty \<tau> \<longrightarrow> wf_ty \<Sigma> \<tau>) \<and> (\<forall>\<pi>. \<theta> = Scheme \<pi> \<longrightarrow> wf_entry \<Sigma> (Scheme \<pi>))"
  "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> True"
proof (induction rule: wf_val_wf_env.inducts)
  case (ValTuple vs \<tau>s)
  then have "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>" by (auto simp: in_set_conv_nth list_all2_conv_all_nth)
  then show ?case by simp
next
  case (ValLambda \<eta> \<rho> \<Gamma> xs \<sigma>s \<Delta> e \<tau>)
  have "wf_ty \<Sigma> (TyCallable \<sigma>s \<tau>)" by fact
  from inst_wf[OF wf_env_wf_inst[OF ValLambda(1)] this] show ?case by simp
next
  case (ValDef \<eta> \<rho> \<Gamma> ds \<pi>s \<Delta> i \<alpha>s \<tau>)
  have sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s"
    and i: "i < length ds" and \<pi>: "\<pi>s ! i = TyScheme \<alpha>s \<tau>"
    by fact+
  have "\<pi>s ! i \<in> set \<pi>s" using those_sum_map_Ok[OF sigs] i by (simp add: list_all2_lengthD)
  from those_sum_map_Ok_elem[OF sigs this] obtain d where "def_signature \<Sigma> \<Gamma> (node d) = Ok (\<pi>s ! i)" by auto
  from def_signature_wf[OF wf_env_wf_cxt[OF ValDef(1)] this]
  have "wf_entry \<Sigma> (signature_entry (TyScheme \<alpha>s \<tau>))" by (simp add: \<pi>)
  from inst_entry_wf[OF wf_env_wf_inst[OF ValDef(1)] this] show ?case by (rule wf_entry_cases)
next
  case (ValInst v \<alpha>s \<sigma> \<tau>s)
  then show ?case by (auto intro: wf_ty_subst)
next
  case (ValPrim \<A> q \<rho> x f \<Gamma> \<theta>)
  from wf_cxt_lookup[OF predefined_cxt_wf[OF ValPrim(3)] ValPrim(4)] show ?case by (rule wf_entry_cases)
qed auto

lemma wf_val_ty: "\<turnstile> v : Ty \<tau> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  and wf_val_scheme: "\<turnstile> v : Scheme \<pi> \<Longrightarrow> wf_entry \<Sigma> (Scheme \<pi>)"
  by (auto dest!: wf_val_wf(1))

inductive_cases WfUnboundE: "\<turnstile> v : Unbound"

inductive_cases WfDUE: "\<turnstile> v : DU \<tau>"

lemma wf_val_unbound: "\<turnstile> v : Unbound \<Longrightarrow> v = VUnbound"
  and wf_val_du: "\<turnstile> v : DU \<tau> \<Longrightarrow> v = VUnbound"
  by (auto elim!: WfUnboundE WfDUE simp: inst_entry_signature_entry \<E>_def \<P>_def split: if_splits)

inductive_cases WfPUE: "\<turnstile> v : PU \<tau> b"

inductive_cases WfPUSchemeE: "\<turnstile> v : PUScheme \<pi> b"

lemma wf_val_pu: "\<turnstile> v : PU \<tau> b \<Longrightarrow> v = VUnbound \<or> \<turnstile> v : Ty \<tau>"
  and wf_val_puscheme: "\<turnstile> v : PUScheme \<pi> b \<Longrightarrow> v = VUnbound \<or> \<turnstile> v : Scheme \<pi>"
  by (auto elim!: WfPUE WfPUSchemeE simp: inst_entry_signature_entry \<E>_def \<P>_def split: if_splits)

lemma wf_dict_update:
  "\<lbrakk> \<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> VDict (update [] \<delta>) : Ty (TyDict \<tau>)"
  using set_update[of "[]" \<delta>] by (auto intro!: ValDict distinct_update)

lemma wf_mod_checked: "\<turnstile> v : ModChecked q \<Gamma> \<Longrightarrow> \<exists>\<rho>. v = VModLoaded q \<rho> \<and> [] \<turnstile> \<rho> : \<Gamma>"
proof -
  have "\<turnstile> v : \<theta> \<Longrightarrow> \<theta> = ModChecked q \<Gamma> \<longrightarrow> (\<exists>\<rho>. v = VModLoaded q \<rho> \<and> [] \<turnstile> \<rho> : \<Gamma>)"
    and "\<eta> \<turnstile> \<rho> : \<Gamma>' \<Longrightarrow> True" for \<theta> \<eta> \<rho> \<Gamma>'
    by (induction rule: wf_val_wf_env.inducts)
       (auto simp: inst_entry_signature_entry split: if_splits dest: prim_entry_callable)
  then show "\<turnstile> v : ModChecked q \<Gamma> \<Longrightarrow> ?thesis" by blast
qed

lemma wf_mod_loaded: "\<turnstile> VModLoaded q \<rho> : \<theta> \<Longrightarrow> \<exists>\<Gamma>. \<theta> = ModChecked q \<Gamma>"
proof -
  have "\<turnstile> v : \<theta> \<Longrightarrow> v = VModLoaded q \<rho> \<longrightarrow> (\<exists>\<Gamma>. \<theta> = ModChecked q \<Gamma>)" and "\<eta> \<turnstile> \<rho>' : \<Gamma>' \<Longrightarrow> True"
    for v \<theta> \<eta> \<rho>' \<Gamma>'
    by (induction rule: wf_val_wf_env.inducts) auto
  then show "\<turnstile> VModLoaded q \<rho> : \<theta> \<Longrightarrow> ?thesis" by blast
qed

(* Member of a module environment typed by the context of the module, which is closed *)
lemma module_member:
  "\<lbrakk> [] \<turnstile> \<rho> : \<Gamma> ; fmlookup \<Gamma> x = Some \<theta> ; \<theta> \<noteq> TypeVar \<rbrakk>
  \<Longrightarrow> \<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : \<theta> \<and> fv_entry \<theta> = {}"
  using wf_env_lookup[of "[]" \<rho> \<Gamma> x \<theta>] wf_env_tyvars[of "[]" \<rho> \<Gamma>] tyvars_entry[of \<Gamma> x \<theta>] by auto

inductive_cases WfTypeE: "\<turnstile> v : Type C"

lemma wf_type_entry: "\<turnstile> v : Type C \<Longrightarrow> v = VClass C"
  by (erule WfTypeE) (auto dest: prim_entry_callable simp: inst_entry_signature_entry split: if_splits)

lemma wf_class_dom: "\<turnstile> v : Type C \<Longrightarrow> C |\<in>| fmdom \<Sigma>"
  by (erule WfTypeE) (auto dest: prim_entry_callable simp: inst_entry_signature_entry split: if_splits)

lemma module_member_TypeVar: "[] \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> fmlookup \<Gamma> x \<noteq> Some TypeVar"
  using wf_env_tyvars[of "[]" \<rho> \<Gamma>] by (force simp: tyvars_def fmlookup_dom'_iff)

end

end
