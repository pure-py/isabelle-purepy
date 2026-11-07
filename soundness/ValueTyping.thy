(* Value and environment typing *)
theory ValueTyping
  imports "isabelle-purepy.Programs" "isabelle-purepy.Determinism"
begin

subsection \<open>Instantiation of type variables\<close>

lemma tyvars_entry: "fmlookup \<Gamma> x = Some \<theta> \<Longrightarrow> fv_entry \<theta> \<subseteq> tyvars \<Gamma>"
  by (force simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff)

lemma tyvars_add: "tyvars (\<Gamma> \<otimes> \<Delta>) \<subseteq> tyvars \<Gamma> \<union> tyvars \<Delta>"
  by (fastforce simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff split: if_splits)

lemma tyvars_single: "\<theta> \<noteq> TypeVar \<Longrightarrow> tyvars (fmupd x \<theta> fmempty) = fv_entry \<theta>"
  by (auto simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff split: if_splits)

(* Application of a closing type substitution, given as a list of pairs *)
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

lemma subst_Nil [simp]: "subst [] \<alpha>s \<tau> = \<tau>"
  by (induction \<tau>) (auto intro: map_idI)

lemma inst_scheme_Nil [simp]: "inst_scheme [] \<pi> = \<pi>"
  by (cases \<pi>) simp

lemma inst_entry_Nil [simp]: "inst_entry [] \<theta> = \<theta>"
  by (cases \<theta>) simp_all

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
  "\<lbrakk> closed_inst \<eta> ; tyvars \<Gamma> \<subseteq> fst ` set \<eta>
   ; \<forall>x \<theta>. fmlookup \<Gamma> x = Some \<theta> \<longrightarrow> \<theta> \<noteq> TypeVar \<longrightarrow> (\<exists>v. fmlookup \<rho> x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>) \<rbrakk>
  \<Longrightarrow> \<eta> \<turnstile> \<rho> : \<Gamma>"

inductive_cases WfEnvE: "\<eta> \<turnstile> \<rho> : \<Gamma>"

lemma wf_env_closed: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> closed_inst \<eta>"
  by (auto elim!: WfEnvE)

lemma wf_env_tyvars: "\<eta> \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> tyvars \<Gamma> \<subseteq> fst ` set \<eta>"
  by (auto elim!: WfEnvE)

lemma wf_env_fv: "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; fv (\<tau> :: ty) \<subseteq> tyvars \<Gamma> \<rbrakk> \<Longrightarrow> fv \<tau> \<subseteq> fst ` set \<eta>"
  using wf_env_tyvars by blast

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

lemma wf_env_upd:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<theta> \<noteq> TypeVar" and "fv_entry \<theta> \<subseteq> fst ` set \<eta>" and "\<turnstile> v : inst_entry \<eta> \<theta>"
  shows "\<eta> \<turnstile> fmupd x v \<rho> : fmupd x \<theta> \<Gamma>"
proof -
  have "\<eta> \<turnstile> \<rho> \<otimes> fmupd x v fmempty : \<Gamma> \<otimes> fmupd x \<theta> fmempty"
    using assms by (intro wf_env_add) (auto simp: tyvars_single split: if_splits)
  then show ?thesis by simp
qed

(* Rebinding in the context alone *)
lemma wf_env_upd_cxt:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<theta> \<noteq> TypeVar" and "fv_entry \<theta> \<subseteq> fst ` set \<eta>" and "fmlookup \<rho> x = Some v"
    and "\<turnstile> v : inst_entry \<eta> \<theta>"
  shows "\<eta> \<turnstile> \<rho> : fmupd x \<theta> \<Gamma>"
proof -
  have "fmupd x v \<rho> = \<rho>" using assms(4) by (intro fmap_ext) auto
  with wf_env_upd[OF assms(1-3,5), of x] show ?thesis by simp
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

lemma wf_val_unbound: "\<turnstile> v : Unbound \<Longrightarrow> v = VUnbound"
  and wf_val_du: "\<turnstile> v : DU \<tau> \<Longrightarrow> v = VUnbound"
  by (auto elim!: WfUnboundE WfDUE simp: inst_entry_signature_entry \<E>_def \<P>_def split: if_splits)

lemma wf_dict_update: "\<forall>w v. (w, v) \<in> set \<delta> \<longrightarrow> \<turnstile> v : Ty \<tau> \<Longrightarrow> \<turnstile> VDict (update [] \<delta>) : Ty (TyDict \<tau>)"
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

lemma module_member_TypeVar: "[] \<turnstile> \<rho> : \<Gamma> \<Longrightarrow> fmlookup \<Gamma> x \<noteq> Some TypeVar"
  using wf_env_tyvars[of "[]" \<rho> \<Gamma>] by (force simp: tyvars_def fmlookup_dom'_iff)

end

end
