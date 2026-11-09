(* Value and environment typing *)
theory ValueTyping
  imports WellFormedStatements "isabelle-purepy.Determinism"
begin

subsection \<open>Instantiation of type variables\<close>

(* Type with its type variables instantiated by \<eta> *)
primrec inst :: "(var \<Rightarrow> ty) \<Rightarrow> ty \<Rightarrow> ty"
where
"inst \<eta> (TyPrim p) = TyPrim p" |
"inst \<eta> (TyList \<sigma>) = TyList (inst \<eta> \<sigma>)" |
"inst \<eta> (TyTuple \<sigma>s) = TyTuple (map (inst \<eta>) \<sigma>s)" |
"inst \<eta> (TyDict \<sigma>) = TyDict (inst \<eta> \<sigma>)" |
"inst \<eta> (TyCallable \<sigma>s \<sigma>) = TyCallable (map (inst \<eta>) \<sigma>s) (inst \<eta> \<sigma>)" |
"inst \<eta> (TyLiteral l) = TyLiteral l" |
"inst \<eta> (TyVar \<alpha>) = \<eta> \<alpha>" |
"inst \<eta> (TyClass C \<sigma>s) = TyClass C (map (inst \<eta>) \<sigma>s)" |
"inst \<eta> (TyUnion \<sigma> \<sigma>') = TyUnion (inst \<eta> \<sigma>) (inst \<eta> \<sigma>')"

(* Instantiation at closed well-formed types *)
definition wf_inst :: "class_table \<Rightarrow> (var \<Rightarrow> ty) \<Rightarrow> bool"
where
"wf_inst \<Sigma> \<eta> = (\<forall>\<alpha>. wf_ty \<Sigma> (\<eta> \<alpha>) \<and> fv (\<eta> \<alpha>) = {})"

lemma finite_fv: "finite (fv (\<tau> :: ty))"
  by (induction \<tau>) auto

lemma inst_TyVar [simp]: "inst TyVar \<tau> = \<tau>"
  by (induction \<tau>) (auto intro: map_idI)

lemma inst_cong: "(\<And>\<alpha>. \<alpha> \<in> fv \<sigma> \<Longrightarrow> \<eta> \<alpha> = \<eta>' \<alpha>) \<Longrightarrow> inst \<eta> \<sigma> = inst \<eta>' \<sigma>"
  by (induction \<sigma>) (auto cong: map_cong)

lemma inst_closed_ty: "fv \<tau> = {} \<Longrightarrow> inst \<eta> \<tau> = \<tau>"
  by (induction \<tau>) (auto intro: map_idI)

lemma fv_inst: "fv (inst \<eta> \<tau>) = (\<Union>\<alpha> \<in> fv \<tau>. fv (\<eta> \<alpha>))"
  by (induction \<tau>) auto

lemma inst_closed: "wf_inst \<Sigma> \<eta> \<Longrightarrow> fv (inst \<eta> \<tau>) = {}"
  by (simp add: fv_inst wf_inst_def)

lemma inst_wf_ty: "\<lbrakk> \<And>\<alpha>. wf_ty \<Sigma> (\<eta> \<alpha>) ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> (inst \<eta> \<tau>)"
  by (induction \<tau>) auto

lemma inst_wf: "\<lbrakk> wf_inst \<Sigma> \<eta> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_ty \<Sigma> (inst \<eta> \<tau>)"
  by (rule inst_wf_ty) (simp_all add: wf_inst_def)

lemma wf_ty_inst_inv: "wf_ty \<Sigma> (inst \<eta> \<sigma>) \<Longrightarrow> wf_ty \<Sigma> \<sigma>"
  by (induction \<sigma>) auto

lemma object_type_inst: "object_type \<sigma> \<Longrightarrow> object_type (inst \<eta> \<sigma>)"
  by (induction \<sigma>) auto

(* Instantiation as the substitution for a list of type variables covering those of the type *)
lemma inst_subst_eq: "fv \<tau> \<subseteq> set \<alpha>s \<Longrightarrow> inst \<eta> \<tau> = subst (map \<eta> \<alpha>s) \<alpha>s \<tau>"
  by (induction \<tau>) (auto simp: map_of_zip_map cong: map_cong)

(* Instantiation as the substitution for a list of type variables covering a finite set *)
lemma inst_subst_cover: "finite S \<Longrightarrow> \<exists>\<alpha>s. \<forall>\<tau>. fv \<tau> \<subseteq> S \<longrightarrow> inst \<eta> \<tau> = subst (map \<eta> \<alpha>s) \<alpha>s \<tau>"
  by (intro exI[of _ "sorted_list_of_set S"] allI impI) (simp add: inst_subst_eq)

lemma inst_as_subst:
  obtains \<alpha>s where "inst \<eta> \<tau> = subst (map \<eta> \<alpha>s) \<alpha>s \<tau>"
  by (rule that[of "sorted_list_of_set (fv \<tau>)"]) (simp add: inst_subst_eq finite_fv)

lemma inst_as_subst_pair:
  obtains \<alpha>s where "inst \<eta> \<sigma> = subst (map \<eta> \<alpha>s) \<alpha>s \<sigma>" and "inst \<eta> \<tau> = subst (map \<eta> \<alpha>s) \<alpha>s \<tau>"
  by (rule that[of "sorted_list_of_set (fv \<sigma> \<union> fv \<tau>)"]) (simp_all add: inst_subst_eq finite_fv)

lemma inst_subty:
  assumes "wf_class_table \<Sigma>" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>" and "wf_ty \<Sigma> \<sigma>" and "wf_ty \<Sigma> \<tau>"
  shows "\<Sigma> \<turnstile> inst \<eta> \<sigma> <: inst \<eta> \<tau>"
proof -
  let ?\<alpha>s = "sorted_list_of_set (fv \<sigma> \<union> fv \<tau>)"
  have "inst \<eta> \<sigma> = subst (map \<eta> ?\<alpha>s) ?\<alpha>s \<sigma>" and "inst \<eta> \<tau> = subst (map \<eta> ?\<alpha>s) ?\<alpha>s \<tau>"
    by (intro inst_subst_eq; simp add: finite_fv)+
  with subst_subty(1)[OF assms(1, 2)] assms(3, 4) show ?thesis by simp
qed

(* Instantiation under the type parameters \<alpha>s of a scheme, which shadow the type variables in scope *)
definition shadow :: "var list \<Rightarrow> (var \<Rightarrow> ty) \<Rightarrow> var \<Rightarrow> ty"
where
"shadow \<alpha>s \<eta> = (\<lambda>\<beta>. if \<beta> \<in> set \<alpha>s then TyVar \<beta> else \<eta> \<beta>)"

lemma shadow_Nil [simp]: "shadow [] \<eta> = \<eta>"
  by (simp add: shadow_def)

lemma shadow_wf: "wf_inst \<Sigma> \<eta> \<Longrightarrow> wf_ty \<Sigma> (shadow \<alpha>s \<eta> \<alpha>)"
  by (simp add: shadow_def wf_inst_def)

fun inst_scheme :: "(var \<Rightarrow> ty) \<Rightarrow> ty_scheme \<Rightarrow> ty_scheme"
where
"inst_scheme \<eta> (TyScheme \<alpha>s \<tau>) = TyScheme \<alpha>s (inst (shadow \<alpha>s \<eta>) \<tau>)"

fun inst_entry :: "(var \<Rightarrow> ty) \<Rightarrow> cxt_entry \<Rightarrow> cxt_entry"
where
"inst_entry \<eta> (Ty \<tau>) = Ty (inst \<eta> \<tau>)" |
"inst_entry \<eta> (DU \<tau>) = DU (inst \<eta> \<tau>)" |
"inst_entry \<eta> (PU \<tau> b) = PU (inst \<eta> \<tau>) b" |
"inst_entry \<eta> (Scheme \<pi>) = Scheme (inst_scheme \<eta> \<pi>)" |
"inst_entry \<eta> (PUScheme \<pi> b) = PUScheme (inst_scheme \<eta> \<pi>) b" |
"inst_entry \<eta> \<theta> = \<theta>"

lemma inst_entry_signature_entry:
  "inst_entry \<eta> (signature_entry (TyScheme \<alpha>s \<tau>)) =
   (if \<alpha>s = [] then Ty (inst \<eta> \<tau>) else Scheme (TyScheme \<alpha>s (inst (shadow \<alpha>s \<eta>) \<tau>)))"
  by (cases \<alpha>s) simp_all

lemma inst_entry_wf:
  assumes "wf_inst \<Sigma> \<eta>" and "wf_entry \<Sigma> \<theta>"
  shows "wf_entry \<Sigma> (inst_entry \<eta> \<theta>)"
proof (cases \<theta>)
  case (Scheme \<pi>)
  then show ?thesis using assms by (cases \<pi>) (auto intro: inst_wf_ty shadow_wf)
next
  case (PUScheme \<pi> b)
  then show ?thesis using assms by (cases \<pi>) (auto intro: inst_wf_ty shadow_wf)
qed (use assms in \<open>auto intro: inst_wf\<close>)

lemma inst_scheme_closed:
  assumes "fv_scheme \<pi> = {}"
  shows "inst_scheme \<eta> \<pi> = \<pi>"
proof (cases \<pi>)
  case (TyScheme \<alpha>s \<tau>)
  with assms have "inst (shadow \<alpha>s \<eta>) \<tau> = inst TyVar \<tau>" by (intro inst_cong) (auto simp: shadow_def)
  with TyScheme show ?thesis by simp
qed

lemma inst_entry_closed: "fv_entry \<theta> = {} \<Longrightarrow> inst_entry \<eta> \<theta> = \<theta>"
  by (cases \<theta>) (simp_all add: inst_closed_ty inst_scheme_closed)

lemma inst_entry_cong:
  assumes "\<And>\<alpha>. \<alpha> \<in> fv_entry \<theta> \<Longrightarrow> \<eta> \<alpha> = \<eta>' \<alpha>"
  shows "inst_entry \<eta> \<theta> = inst_entry \<eta>' \<theta>"
proof (cases \<theta>)
  case (Scheme \<pi>)
  then show ?thesis using assms by (cases \<pi>) (auto simp: shadow_def intro!: inst_cong)
next
  case (PUScheme \<pi> b)
  then show ?thesis using assms by (cases \<pi>) (auto simp: shadow_def intro!: inst_cong)
qed (use assms in \<open>auto intro!: inst_cong\<close>)

(* Instantiation after substitution of types for the parameters of a scheme *)
lemma inst_subst:
  assumes "wf_inst \<Sigma> \<eta>" and "length \<tau>s = length \<alpha>s"
  shows "inst \<eta> (subst \<tau>s \<alpha>s \<sigma>) = subst (map (inst \<eta>) \<tau>s) \<alpha>s (inst (shadow \<alpha>s \<eta>) \<sigma>)"
proof (induction \<sigma>)
  case (TyVar \<beta>)
  show ?case
  proof (cases "\<beta> \<in> set \<alpha>s")
    case True
    then obtain \<tau> where "map_of (zip \<alpha>s \<tau>s) \<beta> = Some \<tau>"
      using map_of_zip_is_Some[OF assms(2)[symmetric]] by blast
    with True assms(2) show ?thesis by (simp add: shadow_def map_of_zip_map_snd)
  next
    case False
    have "fv (\<eta> \<beta>) = {}" using assms(1) by (simp add: wf_inst_def)
    with False show ?thesis
      by (auto simp: shadow_def subst_closed split: option.splits dest!: map_of_SomeD dest: set_zip_leftD)
  qed
qed (simp_all cong: map_cong)

(* Instantiation after substitution for the parameters of a scheme, into a type over those parameters *)
lemma inst_subst_closed:
  assumes "wf_inst \<Sigma> \<eta>" and "length \<tau>s = length \<alpha>s" and "fv \<sigma> \<subseteq> set \<alpha>s"
  shows "inst \<eta> (subst \<tau>s \<alpha>s \<sigma>) = subst (map (inst \<eta>) \<tau>s) \<alpha>s \<sigma>"
proof -
  have "inst (shadow \<alpha>s \<eta>) \<sigma> = inst TyVar \<sigma>" using assms(3) by (intro inst_cong) (auto simp: shadow_def)
  with inst_subst[OF assms(1, 2)] show ?thesis by simp
qed

(* Instantiation of the type parameters \<alpha>s at \<tau>s, shadowing their bindings in \<eta> *)
definition inst_params :: "var list \<Rightarrow> ty list \<Rightarrow> (var \<Rightarrow> ty) \<Rightarrow> var \<Rightarrow> ty"
where
"inst_params \<alpha>s \<tau>s \<eta> = (\<lambda>\<beta>. case map_of (zip \<alpha>s \<tau>s) \<beta> of Some \<tau> \<Rightarrow> \<tau> | None \<Rightarrow> \<eta> \<beta>)"

lemma inst_params_notin [simp]: "\<beta> \<notin> set \<alpha>s \<Longrightarrow> inst_params \<alpha>s \<tau>s \<eta> \<beta> = \<eta> \<beta>"
  by (auto simp: inst_params_def split: option.splits dest!: map_of_SomeD dest: set_zip_leftD)

lemma inst_params_wf:
  "\<lbrakk> wf_inst \<Sigma> \<eta> ; \<forall>\<tau> \<in> set \<tau>s. fv \<tau> = {} \<and> wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> wf_inst \<Sigma> (inst_params \<alpha>s \<tau>s \<eta>)"
  by (auto simp: wf_inst_def inst_params_def split: option.splits dest!: map_of_SomeD set_zip_rightD)

lemma inst_inst_params:
  assumes "wf_inst \<Sigma> \<eta>" and "length \<tau>s = length \<alpha>s"
  shows "inst (inst_params \<alpha>s \<tau>s \<eta>) \<sigma> = subst \<tau>s \<alpha>s (inst (shadow \<alpha>s \<eta>) \<sigma>)"
proof (induction \<sigma>)
  case (TyVar \<beta>)
  have "fv (\<eta> \<beta>) = {}" using assms(1) by (simp add: wf_inst_def)
  then show ?case
    by (auto simp: inst_params_def shadow_def subst_closed map_of_zip_is_None[OF assms(2)[symmetric]]
        split: option.splits dest!: map_of_SomeD dest: set_zip_leftD)
qed (simp_all cong: map_cong)

(* Type scheme of a function signature *)
fun callable_scheme :: "ty_scheme \<Rightarrow> bool"
where
"callable_scheme (TyScheme _ (TyCallable _ _)) = True" |
"callable_scheme _ = False"

context evaluation
begin

(* Definitions ds checked at signatures \<pi>s in \<Gamma> extended by those signatures, their type parameters fresh
   for \<Gamma> *)
definition defs_checked :: "cxt \<Rightarrow> func located list \<Rightarrow> ty_scheme list \<Rightarrow> bool"
where
"defs_checked \<Gamma> ds \<pi>s =
  (those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s
   \<and> all_sum (map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))))
       ds \<pi>s) = Ok ()
   \<and> (\<forall>d \<in> set ds. case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}))"

inductive wf_val :: "val \<Rightarrow> cxt_entry \<Rightarrow> bool" ("\<turnstile> _ : _" [51, 51] 50)
and wf_env :: "(var \<Rightarrow> ty) \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> bool" ("_ \<turnstile> _ : _" [51, 51, 51] 50)
where
ValLit: "\<lbrakk> \<Sigma> \<turnstile> TyLiteral l <: \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> VLit l : Ty \<tau>" |
ValLitFloat: "\<lbrakk> \<Sigma> \<turnstile> TyPrim float <: \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> VLit (LitFloat x) : Ty \<tau>" |
ValList:
  "\<lbrakk> \<forall>v \<in> set vs. \<turnstile> v : Ty \<sigma> ; wf_ty \<Sigma> \<sigma> ; \<Sigma> \<turnstile> TyList \<sigma> <: \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> VList vs : Ty \<tau>" |
ValTuple:
  "\<lbrakk> list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) vs \<sigma>s ; \<Sigma> \<turnstile> TyTuple \<sigma>s <: \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> VTuple vs : Ty \<tau>" |
ValDict:
  "\<lbrakk> \<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<sigma> ; distinct (map fst \<delta>) ; wf_ty \<Sigma> \<sigma> ; \<Sigma> \<turnstile> TyDict \<sigma> <: \<tau>
   ; wf_ty \<Sigma> \<tau> \<rbrakk>
  \<Longrightarrow> \<turnstile> VDict \<delta> : Ty \<tau>" |
ValLambda:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; length xs = length \<sigma>s ; params_cxt xs \<sigma>s = Ok \<Delta> ; check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<sigma> = Ok ()
   ; wf_ty \<Sigma> (TyCallable \<sigma>s \<sigma>) ; \<Sigma> \<turnstile> inst \<eta> (TyCallable \<sigma>s \<sigma>) <: \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk>
  \<Longrightarrow> \<turnstile> Lam(\<rho>, xs, e) : Ty \<tau>" |
ValDef:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; defs_checked \<Gamma> ds \<pi>s ; i < length ds ; \<pi>s ! i = TyScheme \<alpha>s (TyCallable \<sigma>s \<sigma>)
   ; length \<tau>s = length \<alpha>s ; \<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' = {} \<and> wf_ty \<Sigma> \<tau>'
   ; \<Sigma> \<turnstile> subst \<tau>s \<alpha>s (inst (shadow \<alpha>s \<eta>) (TyCallable \<sigma>s \<sigma>)) <: \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk>
  \<Longrightarrow> \<turnstile> Def(\<rho>, ds, i) : Ty \<tau>" |
ValDefScheme:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; defs_checked \<Gamma> ds \<pi>s ; i < length ds ; \<pi>s ! i = TyScheme \<alpha>s (TyCallable \<sigma>s \<sigma>) ; \<alpha>s \<noteq> [] \<rbrakk>
  \<Longrightarrow> \<turnstile> Def(\<rho>, ds, i) : Scheme (TyScheme \<alpha>s (inst (shadow \<alpha>s \<eta>) (TyCallable \<sigma>s \<sigma>)))" |
ValObj:
  "\<lbrakk> wf_ty \<Sigma> (TyClass C \<sigma>s) ; map fst xvs = field_names \<Sigma> C
   ; list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) (map snd xvs) (field_types \<Sigma> C \<sigma>s) ; \<Sigma> \<turnstile> TyClass C \<sigma>s <: \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk>
  \<Longrightarrow> \<turnstile> VObject C xvs : Ty \<tau>" |
ValPrim:
  "\<lbrakk> fmlookup (\<E> \<A>) q = Some \<rho> ; fmlookup \<rho> x = Some (VPrim f) ; fmlookup \<P> q = Some \<Gamma>
   ; fmlookup \<Gamma> x = Some (Ty (TyCallable \<sigma>s \<sigma>)) ; \<Sigma> \<turnstile> TyCallable \<sigma>s \<sigma> <: \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk>
  \<Longrightarrow> \<turnstile> VPrim f : Ty \<tau>" |
ValPredef: "\<turnstile> VPredef q : PredefName" |
ValMod: "\<turnstile> VModStub q : ModStub q" |
ValModLoaded: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> \<turnstile> VModLoaded q \<rho> : ModChecked q \<Gamma>" |
ValClass: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> \<turnstile> VClass C : Type C" |
ValTypeAlias: "\<turnstile> VTypeAlias q \<chi>s i : TypeAlias \<Gamma> q \<chi>s i" |
ValUnbound: "\<theta> = Unbound \<or> (\<exists>\<tau>. \<theta> = DU \<tau>) \<Longrightarrow> \<turnstile> VUnbound : \<theta>" |
ValPU: "v = VUnbound \<or> \<turnstile> v : Ty \<tau> \<Longrightarrow> \<turnstile> v : PU \<tau> b" |
ValPUScheme: "v = VUnbound \<or> \<turnstile> v : Scheme \<pi> \<Longrightarrow> \<turnstile> v : PUScheme \<pi> b" |

WfEnv:
  "\<lbrakk> wf_inst \<Sigma> \<eta> ; wf_cxt \<Sigma> \<Gamma>
   ; \<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> \<theta> \<noteq> TypeVar \<longrightarrow> (\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>) \<rbrakk>
  \<Longrightarrow> \<eta> \<turnstile> \<rho> : \<Gamma>"

inductive_cases WfEnvE: "\<eta> \<turnstile> \<rho> : \<Gamma>"

lemma wf_env_wf_inst: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> wf_inst \<Sigma> \<eta>"
  by (auto elim!: WfEnvE)

lemma wf_env_wf_cxt: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> wf_cxt \<Sigma> \<Gamma>"
  by (auto elim!: WfEnvE)

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
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>"
    and "\<And>x \<theta>. \<lbrakk> fmlookup \<Delta> x = Some \<theta> ; \<theta> \<noteq> TypeVar \<rbrakk>
          \<Longrightarrow> \<exists>v. fmlookup (\<rho> \<otimes> \<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
    and "wf_cxt \<Sigma> \<Delta>"
  shows "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>"
proof (rule WfEnv)
  show "wf_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>)" using wf_env_wf_cxt[OF assms(1)] assms(4) by (rule wf_cxt_add)
  show "wf_inst \<Sigma> \<eta>" using assms(1) by (rule wf_env_wf_inst)
  show "\<forall>x \<theta>. fmlookup (\<Gamma> \<otimes> \<Delta>) x = Some \<theta> \<longrightarrow> \<theta> \<noteq> TypeVar
          \<longrightarrow> (\<exists>v. fmlookup (\<rho> \<otimes> \<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>)"
  proof (intro allI impI)
    fix x \<theta>
    assume lookup: "fmlookup (\<Gamma> \<otimes> \<Delta>) x = Some \<theta>" and "\<theta> \<noteq> TypeVar"
    show "\<exists>v. fmlookup (\<rho> \<otimes> \<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
    proof (cases "fmlookup \<Delta> x")
      case None
      with lookup have "fmlookup \<Gamma> x = Some \<theta>" by (simp add: fmlookup_dom_iff)
      moreover from None assms(2) have "fmlookup \<rho>' x = None" by (metis fmdom_notD fmdom_notI fsubsetD)
      ultimately show ?thesis using wf_env_lookup[OF assms(1)] \<open>\<theta> \<noteq> TypeVar\<close> by (auto simp: fmlookup_dom_iff)
    next
      case (Some \<theta>')
      with lookup have "\<theta>' = \<theta>" by (auto simp: fmlookup_dom_iff)
      with Some \<open>\<theta> \<noteq> TypeVar\<close> show ?thesis by (intro assms(3)) simp_all
    qed
  qed
qed

(* Instantiation agreeing with \<eta> on the type variables of the context *)
lemma wf_env_inst:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "wf_inst \<Sigma> \<eta>'" and agree: "\<And>\<alpha>. \<alpha> \<in> tyvars \<Gamma> \<Longrightarrow> \<eta>' \<alpha> = \<eta> \<alpha>"
  shows "\<eta>' \<turnstile> \<rho> : \<Gamma>"
proof (rule WfEnv[OF assms(2)])
  show "wf_cxt \<Sigma> \<Gamma>" using assms(1) by (rule wf_env_wf_cxt)
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
lemma wf_env_type_params: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> \<eta> \<turnstile> \<rho> : \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar"
proof -
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>"
  then have "\<eta> \<turnstile> \<rho> \<otimes> fmempty : \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar"
    by (rule wf_env_add) (auto dest!: fmconst_entry intro!: wf_cxt_fmconst)
  then show ?thesis by simp
qed

(* Variables of a scope, unbound *)
lemma wf_env_unbound:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>"
  shows "\<eta> \<turnstile> \<rho> \<otimes> fmconst A VUnbound : \<Gamma> \<otimes> fmconst A Unbound"
proof (rule wf_env_add[OF assms])
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
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<theta> \<noteq> TypeVar" and "\<turnstile> v : inst_entry \<eta> \<theta>" and "wf_entry \<Sigma> \<theta>"
  shows "\<eta> \<turnstile> fmupd x v \<rho> : fmupd x \<theta> \<Gamma>"
proof -
  have "\<eta> \<turnstile> \<rho> \<otimes> fmupd x v fmempty : \<Gamma> \<otimes> fmupd x \<theta> fmempty"
    using assms by (intro wf_env_add) (auto intro: wf_cxt_upd split: if_splits)
  then show ?thesis by simp
qed

(* Rebinding in the context alone *)
lemma wf_env_upd_cxt:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<theta> \<noteq> TypeVar" and "fmlookup \<rho> x = Some v" and "\<turnstile> v : inst_entry \<eta> \<theta>"
    and "wf_entry \<Sigma> \<theta>"
  shows "\<eta> \<turnstile> \<rho> : fmupd x \<theta> \<Gamma>"
proof -
  have "fmupd x v \<rho> = \<rho>" using assms(3) by (intro fmap_ext) auto
  with wf_env_upd[OF assms(1, 2, 4, 5), of x] show ?thesis by simp
qed

lemma wf_unbound:
  "\<turnstile> VUnbound : \<theta> \<Longrightarrow> \<theta> = Unbound \<or> (\<exists>\<tau>. \<theta> = DU \<tau>) \<or> (\<exists>\<tau> b. \<theta> = PU \<tau> b) \<or> (\<exists>\<pi> b. \<theta> = PUScheme \<pi> b)"
  by (erule wf_val.cases) auto

lemma wf_unbound_ty: "\<turnstile> VUnbound : Ty \<tau> \<Longrightarrow> False"
  and wf_unbound_scheme: "\<turnstile> VUnbound : Scheme \<pi> \<Longrightarrow> False"
  by (auto dest!: wf_unbound)

(* Contexts of the predefined modules, well-formed *)
lemma predefined_cxt_wf: "fmlookup \<P> q = Some \<Gamma> \<Longrightarrow> wf_cxt \<Sigma> \<Gamma>"
proof -
  have "range_class |\<in>| fmdom \<Sigma>" using range_lookup by (simp add: predefined_classes_def fmlookup_dom_iff)
  then show "fmlookup \<P> q = Some \<Gamma> \<Longrightarrow> wf_cxt \<Sigma> \<Gamma>"
    by (auto simp: \<P>_def fmlookup_of_list wf_cxt_iff split: if_splits)
qed

lemma range_class_wf: "wf_ty \<Sigma> (TyClass range_class [])"
  using range_lookup by (simp add: predefined_classes_def fmlookup_dom_iff type_params_def)

inductive_cases WfTyE: "\<turnstile> v : Ty \<tau>"

inductive_cases WfSchemeE: "\<turnstile> v : Scheme \<pi>"

lemma wf_val_ty: "\<turnstile> v : Ty \<tau> \<Longrightarrow> wf_ty \<Sigma> \<tau>"
  by (erule WfTyE) simp_all

lemma wf_vals_tys: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s \<Longrightarrow> \<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>"
  by (induction rule: list_all2_induct) (auto dest: wf_val_ty)

lemma wf_val_lit: "\<turnstile> VLit l : Ty (TyLiteral l)"
  by (rule ValLit) (simp_all add: SubtyRefl)

lemma wf_val_float: "\<turnstile> VLit (LitFloat x) : Ty (TyPrim float)"
  by (rule ValLitFloat) (simp_all add: SubtyRefl)

lemma wf_val_list: "\<lbrakk> \<forall>v \<in> set vs. \<turnstile> v : Ty \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> VList vs : Ty (TyList \<tau>)"
  by (rule ValList[OF _ _ SubtyRefl]) simp_all

lemma wf_val_tuple: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs \<tau>s \<Longrightarrow> \<turnstile> VTuple vs : Ty (TyTuple \<tau>s)"
  by (frule wf_vals_tys) (rule ValTuple[OF _ SubtyRefl]; simp)

(* Signature of a checked definition, well-formed and callable *)
lemma defs_checked_wf:
  assumes "wf_cxt \<Sigma> \<Gamma>" and "defs_checked \<Gamma> ds \<pi>s" and "i < length ds" and "\<pi>s ! i = TyScheme \<alpha>s \<sigma>"
  shows "wf_ty \<Sigma> \<sigma> \<and> (\<exists>\<sigma>s \<sigma>'. \<sigma> = TyCallable \<sigma>s \<sigma>')"
proof -
  have sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s"
    using assms(2) by (simp add: defs_checked_def)
  have "\<pi>s ! i \<in> set \<pi>s" using those_sum_map_Ok[OF sigs] assms(3) by (simp add: list_all2_lengthD)
  from those_sum_map_Ok_elem[OF sigs this] obtain d where "def_signature \<Sigma> \<Gamma> (node d) = Ok (\<pi>s ! i)" by auto
  from def_signature_wf[OF assms(1) this] def_signatures_callable[OF sigs assms(3, 4)] show ?thesis
    by (cases \<alpha>s) (auto simp: assms(4))
qed

lemma wf_val_scheme: "\<turnstile> v : Scheme \<pi> \<Longrightarrow> wf_entry \<Sigma> (Scheme \<pi>)"
  by (erule WfSchemeE)
     (auto dest: defs_checked_wf[OF wf_env_wf_cxt] intro!: inst_wf_ty shadow_wf intro: wf_env_wf_inst)

(* Subsumption *)
lemma wf_val_sub:
  assumes "\<turnstile> v : Ty \<sigma>" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>" and "wf_ty \<Sigma> \<tau>"
  shows "\<turnstile> v : Ty \<tau>"
proof -
  have trans: "\<Sigma> \<turnstile> \<sigma>' <: \<tau>" if "\<Sigma> \<turnstile> \<sigma>' <: \<sigma>" and "wf_ty \<Sigma> \<sigma>'" for \<sigma>'
    using subty_trans[OF wf_class_table that(2) wf_val_ty[OF assms(1)] that(1) assms(2)] .
  from assms(1) show ?thesis
  proof (cases rule: wf_val.cases)
    case ValTuple
    then show ?thesis
      by (auto intro!: wf_val_wf_env.ValTuple trans assms(3) dest: wf_vals_tys)
  next
    case ValLambda
    then show ?thesis by (auto intro!: wf_val_wf_env.ValLambda trans assms(3) inst_wf intro: wf_env_wf_inst)
  next
    case ValDef
    then show ?thesis
      by (auto intro!: wf_val_wf_env.ValDef trans assms(3) wf_ty_subst inst_wf_ty shadow_wf
          intro: wf_env_wf_inst dest: defs_checked_wf[OF wf_env_wf_cxt])
  next
    case ValPrim
    then show ?thesis
      by (auto intro!: wf_val_wf_env.ValPrim trans assms(3) dest: wf_cxt_lookup[OF predefined_cxt_wf])
  qed (auto intro!: wf_val_wf_env.intros trans assms(3))
qed

(* Instantiation of a scheme *)
lemma wf_val_inst:
  assumes "\<turnstile> v : Scheme (TyScheme \<alpha>s \<sigma>)" and "length \<tau>s = length \<alpha>s" and "\<forall>\<tau> \<in> set \<tau>s. fv \<tau> = {}"
    and "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>"
  shows "\<turnstile> v : Ty (subst \<tau>s \<alpha>s \<sigma>)"
proof -
  have wf: "wf_ty \<Sigma> (subst \<tau>s \<alpha>s \<sigma>)" using wf_val_scheme[OF assms(1)] assms(4) by (auto intro: wf_ty_subst)
  from assms(1) show ?thesis
    by (cases rule: WfSchemeE) (use assms(2-4) wf in \<open>auto intro!: ValDef SubtyRefl\<close>)
qed

(* Closure of a definition, at the entry of its signature *)
lemma wf_def_entry:
  assumes env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and defs: "defs_checked \<Gamma> ds \<pi>s" and i: "i < length ds"
    and \<pi>: "\<pi>s ! i = TyScheme \<alpha>s \<sigma>"
  shows "\<turnstile> Def(\<rho>, ds, i) : inst_entry \<eta> (signature_entry (TyScheme \<alpha>s \<sigma>))"
proof -
  from defs_checked_wf[OF wf_env_wf_cxt[OF env] defs i \<pi>] obtain \<sigma>s \<sigma>' where wf: "wf_ty \<Sigma> \<sigma>"
    and \<sigma>: "\<sigma> = TyCallable \<sigma>s \<sigma>'"
    by blast
  show ?thesis
  proof (cases "\<alpha>s = []")
    case True
    have "wf_ty \<Sigma> (inst \<eta> \<sigma>)" using wf_env_wf_inst[OF env] wf by (rule inst_wf)
    then have "\<turnstile> Def(\<rho>, ds, i) : Ty (inst \<eta> \<sigma>)"
      using True
      by (intro ValDef[OF env defs i \<pi>[unfolded \<sigma>], where \<tau>s = "[]"]) (simp_all add: \<sigma> SubtyRefl comp_def)
    with True show ?thesis by simp
  next
    case False
    with ValDefScheme[OF env defs i \<pi>[unfolded \<sigma>]] show ?thesis by (simp add: inst_entry_signature_entry \<sigma>)
  qed
qed

inductive_cases WfUnboundE: "\<turnstile> v : Unbound"

inductive_cases WfDUE: "\<turnstile> v : DU \<tau>"

lemma wf_val_unbound: "\<turnstile> v : Unbound \<Longrightarrow> v = VUnbound"
  and wf_val_du: "\<turnstile> v : DU \<tau> \<Longrightarrow> v = VUnbound"
  by (auto elim!: WfUnboundE WfDUE)

inductive_cases WfPUE: "\<turnstile> v : PU \<tau> b"

inductive_cases WfPUSchemeE: "\<turnstile> v : PUScheme \<pi> b"

lemma wf_val_pu: "\<turnstile> v : PU \<tau> b \<Longrightarrow> v = VUnbound \<or> \<turnstile> v : Ty \<tau>"
  and wf_val_puscheme: "\<turnstile> v : PUScheme \<pi> b \<Longrightarrow> v = VUnbound \<or> \<turnstile> v : Scheme \<pi>"
  by (auto elim!: WfPUE WfPUSchemeE)

lemma wf_dict_update:
  "\<lbrakk> \<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau> ; wf_ty \<Sigma> \<tau> \<rbrakk> \<Longrightarrow> \<turnstile> VDict (update [] \<delta>) : Ty (TyDict \<tau>)"
  using set_update[of "[]" \<delta>] by (auto intro!: ValDict SubtyRefl distinct_update)

lemma wf_mod_checked: "\<turnstile> v : ModChecked q \<Gamma> \<Longrightarrow> \<exists>\<rho> \<eta>. v = VModLoaded q \<rho> \<and> \<eta> \<turnstile> \<rho> : \<Gamma>"
  by (erule wf_val.cases) auto

lemma wf_mod_loaded: "\<turnstile> VModLoaded q \<rho> : \<theta> \<Longrightarrow> \<exists>\<Gamma>. \<theta> = ModChecked q \<Gamma>"
  by (erule wf_val.cases) (auto elim: WfTyE WfSchemeE)

(* Member of a module environment typed by the context of the module, which is closed *)
lemma module_member:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; tyvars \<Gamma> = {} ; fmlookup \<Gamma> x = Some \<theta> ; \<theta> \<noteq> TypeVar \<rbrakk>
  \<Longrightarrow> \<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : \<theta> \<and> fv_entry \<theta> = {}"
  using wf_env_lookup[of \<eta> \<rho> \<Gamma> x \<theta>] tyvars_entry[of \<Gamma> x \<theta>] by (auto simp: inst_entry_closed)

inductive_cases WfTypeE: "\<turnstile> v : Type C"

lemma wf_type_entry: "\<turnstile> v : Type C \<Longrightarrow> v = VClass C"
  and wf_class_dom: "\<turnstile> v : Type C \<Longrightarrow> C |\<in>| fmdom \<Sigma>"
  by (auto elim!: WfTypeE)

lemma module_member_TypeVar: "tyvars \<Gamma> = {} \<Longrightarrow> fmlookup \<Gamma> x \<noteq> Some TypeVar"
  by (force simp: tyvars_def fmlookup_dom'_iff)

end

end
