(* Soundness of pattern matching and of dispatch over the cases of a match statement *)
theory Dispatch
  imports Calls "HOL-Library.Multiset"
begin

no_notation (ASCII) comp (infixl \<open>o\<close> 55)

subsection \<open>Chains of base classes\<close>

(* Class reached from C through k base classes *)
fun base_steps :: "class_table \<Rightarrow> nat \<Rightarrow> name \<Rightarrow> name option"
where
"base_steps \<Sigma> 0 C = Some C" |
"base_steps \<Sigma> (Suc k) C = (case base \<Sigma> C of None \<Rightarrow> None | Some (D, _) \<Rightarrow> base_steps \<Sigma> k D)"

lemma base_steps_add:
  "base_steps \<Sigma> (k + j) C = (case base_steps \<Sigma> k C of None \<Rightarrow> None | Some D \<Rightarrow> base_steps \<Sigma> j D)"
  by (induction k arbitrary: C) (auto split: option.splits)

lemma inherits_within_steps: "inherits_within n \<Sigma> C \<Longrightarrow> base_steps \<Sigma> n C = None"
  by (induction n arbitrary: C) (auto split: option.splits)

(* Cycle of k base classes through C: every number of steps from C reaches a class *)
lemma base_steps_cycle:
  "\<lbrakk> base_steps \<Sigma> k C = Some C ; 0 < k \<rbrakk> \<Longrightarrow> base_steps \<Sigma> n C \<noteq> None"
proof -
  assume cyc: "base_steps \<Sigma> k C = Some C" and k: "0 < k"
  have "base_steps \<Sigma> (m * k) C = Some C" for m
    by (induction m) (auto simp: base_steps_add cyc)
  moreover have "n \<le> n * k" using k by (cases k) simp_all
  ultimately have "base_steps \<Sigma> (n + (n * k - n)) C = Some C" by simp
  then show ?thesis by (auto simp: base_steps_add split: option.splits)
qed

lemma instantiated_ancestors_upto_steps:
  "\<lbrakk> inherits_within n \<Sigma> C ; D \<in> set (map fst (instantiated_ancestors_upto n \<Sigma> C \<tau>s)) \<rbrakk>
  \<Longrightarrow> \<exists>k < n. base_steps \<Sigma> k C = Some D"
proof (induction n arbitrary: C \<tau>s)
  case (Suc n)
  show ?case
  proof (cases "base \<Sigma> C")
    case None
    with Suc.prems show ?thesis by (auto intro: exI[of _ 0])
  next
    case (Some E\<rho>s)
    then obtain E \<rho>s where base: "base \<Sigma> C = Some (E, \<rho>s)" by (cases E\<rho>s) simp
    with Suc.prems consider "D = C"
      | "D \<in> set (map fst (instantiated_ancestors_upto n \<Sigma> E (map (subst \<tau>s (type_params \<Sigma> C)) \<rho>s)))"
      by auto
    then show ?thesis
    proof cases
      case 1
      then show ?thesis by (auto intro: exI[of _ 0])
    next
      case 2
      from Suc.prems(1) base have "inherits_within n \<Sigma> E" by simp
      from Suc.IH[OF this 2] obtain k where "k < n" and "base_steps \<Sigma> k E = Some D" by blast
      with base show ?thesis by (auto intro!: exI[of _ "Suc k"])
    qed
  qed
qed simp

lemma instantiated_ancestors_upto_distinct:
  "inherits_within n \<Sigma> C \<Longrightarrow> distinct (map fst (instantiated_ancestors_upto n \<Sigma> C \<tau>s))"
proof (induction n arbitrary: C \<tau>s)
  case (Suc n)
  show ?case
  proof (cases "base \<Sigma> C")
    case (Some D\<sigma>s)
    then obtain D \<sigma>s where base: "base \<Sigma> C = Some (D, \<sigma>s)" by (cases D\<sigma>s) simp
    let ?\<sigma>s = "map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s"
    from Suc.prems base have D: "inherits_within n \<Sigma> D" by simp
    have "C \<notin> set (map fst (instantiated_ancestors_upto n \<Sigma> D ?\<sigma>s))"
    proof
      assume "C \<in> set (map fst (instantiated_ancestors_upto n \<Sigma> D ?\<sigma>s))"
      from instantiated_ancestors_upto_steps[OF D this] obtain k where "base_steps \<Sigma> k D = Some C" by blast
      with base have "base_steps \<Sigma> (Suc k) C = Some C" by simp
      from base_steps_cycle[OF this] inherits_within_steps[OF Suc.prems] show False by blast
    qed
    with Suc.IH[OF D] base show ?thesis by simp
  qed simp
qed simp

lemma instantiated_ancestors_distinct:
  "\<lbrakk> wf_class_table \<Sigma> ; C |\<in>| fmdom \<Sigma> \<rbrakk> \<Longrightarrow> distinct (map fst (instantiated_ancestors \<Sigma> C \<tau>s))"
  unfolding instantiated_ancestors_def
  by (rule instantiated_ancestors_upto_distinct[OF wf_class_table_inherits])

(* Ancestors of a class in the chain of C, as a suffix of the chain of C *)
lemma instantiated_ancestors_upto_suffix:
  "\<lbrakk> inherits_within n \<Sigma> C ; (D, \<sigma>s) \<in> set (instantiated_ancestors_upto n \<Sigma> C \<tau>s) \<rbrakk>
  \<Longrightarrow> \<exists>m \<le> n. inherits_within m \<Sigma> D
        \<and> (\<exists>pre. instantiated_ancestors_upto n \<Sigma> C \<tau>s = pre @ instantiated_ancestors_upto m \<Sigma> D \<sigma>s)"
proof (induction n arbitrary: C \<tau>s)
  case (Suc n)
  show ?case
  proof (cases "(D, \<sigma>s) = (C, \<tau>s)")
    case True
    with Suc.prems(1) show ?thesis by (intro exI[of _ "Suc n"]) auto
  next
    case False
    with Suc.prems obtain E \<rho>s where base: "base \<Sigma> C = Some (E, \<rho>s)"
      and mem: "(D, \<sigma>s) \<in> set (instantiated_ancestors_upto n \<Sigma> E (map (subst \<tau>s (type_params \<Sigma> C)) \<rho>s))"
      by (auto split: option.splits)
    from Suc.prems(1) base have "inherits_within n \<Sigma> E" by simp
    from Suc.IH[OF this mem] obtain m pre where "m \<le> n" and "inherits_within m \<Sigma> D"
      and "instantiated_ancestors_upto n \<Sigma> E (map (subst \<tau>s (type_params \<Sigma> C)) \<rho>s)
             = pre @ instantiated_ancestors_upto m \<Sigma> D \<sigma>s"
      by blast
    with base show ?thesis by (intro exI[of _ m]) auto
  qed
qed simp

lemma instantiated_ancestors_suffix:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "(D, \<sigma>s) \<in> set (instantiated_ancestors \<Sigma> C \<tau>s)"
  shows "\<exists>pre. instantiated_ancestors \<Sigma> C \<tau>s = pre @ instantiated_ancestors \<Sigma> D \<sigma>s"
proof -
  from instantiated_ancestors_upto_suffix[OF wf_class_table_inherits[OF assms(1, 2)]
      assms(3)[unfolded instantiated_ancestors_def]]
  obtain m pre where "m \<le> fcard (fmdom \<Sigma>)" and "inherits_within m \<Sigma> D"
    and "instantiated_ancestors_upto (fcard (fmdom \<Sigma>)) \<Sigma> C \<tau>s = pre @ instantiated_ancestors_upto m \<Sigma> D \<sigma>s"
    by blast
  with instantiated_ancestors_upto_mono[OF this(2, 1)] show ?thesis
    unfolding instantiated_ancestors_def by auto
qed

lemma ancestors_dom:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "D \<in> set (ancestors \<Sigma> C)"
  shows "D |\<in>| fmdom \<Sigma>"
proof -
  have "wf_ty \<Sigma> (TyClass C (map TyVar (type_params \<Sigma> C)))" using assms(2) by simp
  from assms(3) obtain \<sigma>s where "(D, \<sigma>s) \<in> set (instantiated_ancestors \<Sigma> C (map TyVar (type_params \<Sigma> C)))"
    by (auto simp: ancestors_def)
  from instantiated_ancestors_wf[OF assms(1) \<open>wf_ty \<Sigma> _\<close> this] show ?thesis by simp
qed

lemma instantiated_ancestor_mem:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "D \<in> set (ancestors \<Sigma> C)"
  shows "(D, instantiated_ancestor \<Sigma> C \<tau>s D) \<in> set (instantiated_ancestors \<Sigma> C \<tau>s)"
proof -
  from assms(3) obtain \<sigma>s where "(D, \<sigma>s) \<in> set (instantiated_ancestors \<Sigma> C \<tau>s)"
    using ancestors_instantiated[of \<Sigma> C \<tau>s] by auto
  with instantiated_ancestors_distinct[OF assms(1, 2)] show ?thesis
    by (simp add: instantiated_ancestor_def)
qed

lemma fcard_fmdom_Suc: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> \<exists>n. fcard (fmdom \<Sigma>) = Suc n"
  by (cases "fcard (fmdom \<Sigma>)") auto

lemma instantiated_ancestor_head [simp]: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> instantiated_ancestor \<Sigma> C \<tau>s C = \<tau>s"
  unfolding instantiated_ancestor_def instantiated_ancestors_def by (auto dest!: fcard_fmdom_Suc)

lemma ancestors_head [simp]: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> C \<in> set (ancestors \<Sigma> C)"
  unfolding ancestors_def instantiated_ancestors_def by (auto dest!: fcard_fmdom_Suc)

(* Ancestors of a class with a base class: the class, then the ancestors of the base class *)
lemma instantiated_ancestors_base:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "base \<Sigma> C = Some (D, \<sigma>s)"
  shows "instantiated_ancestors \<Sigma> C \<tau>s
         = (C, \<tau>s) # instantiated_ancestors \<Sigma> D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s)"
proof -
  from wf_class_table_inherits[OF assms(1, 2)] obtain n where n: "fcard (fmdom \<Sigma>) = Suc n"
    and "inherits_within n \<Sigma> D"
    using assms(3) by (cases "fcard (fmdom \<Sigma>)") auto
  from instantiated_ancestors_upto_mono[OF this(2), of "Suc n"] show ?thesis
    unfolding instantiated_ancestors_def n using assms(3) by simp
qed

(* Ancestor of an ancestor: an ancestor, with the type arguments composed *)
lemma instantiated_ancestor_compose:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "D \<in> set (ancestors \<Sigma> C)" and "E \<in> set (ancestors \<Sigma> D)"
  shows "E \<in> set (ancestors \<Sigma> C)"
    and "instantiated_ancestor \<Sigma> C \<tau>s E = instantiated_ancestor \<Sigma> D (instantiated_ancestor \<Sigma> C \<tau>s D) E"
proof -
  let ?\<sigma>s = "instantiated_ancestor \<Sigma> C \<tau>s D"
  have D: "D |\<in>| fmdom \<Sigma>" using ancestors_dom[OF assms(1-3)] .
  from instantiated_ancestors_suffix[OF assms(1, 2) instantiated_ancestor_mem[OF assms(1-3)]]
  obtain pre where suffix: "instantiated_ancestors \<Sigma> C \<tau>s = pre @ instantiated_ancestors \<Sigma> D ?\<sigma>s" by blast
  from instantiated_ancestor_mem[OF assms(1) D assms(4), of ?\<sigma>s]
  have mem: "(E, instantiated_ancestor \<Sigma> D ?\<sigma>s E) \<in> set (instantiated_ancestors \<Sigma> C \<tau>s)"
    unfolding suffix by simp
  then show "E \<in> set (ancestors \<Sigma> C)" using ancestors_instantiated[of \<Sigma> C \<tau>s] by force
  from mem instantiated_ancestors_distinct[OF assms(1, 2)]
  show "instantiated_ancestor \<Sigma> C \<tau>s E = instantiated_ancestor \<Sigma> D ?\<sigma>s E"
    by (simp add: instantiated_ancestor_def)
qed

lemma ancestors_antisym:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "D \<in> set (ancestors \<Sigma> C)" and "C \<in> set (ancestors \<Sigma> D)"
  shows "C = D"
proof -
  let ?\<tau>s = "map TyVar (type_params \<Sigma> C)"
  have D: "D |\<in>| fmdom \<Sigma>" using ancestors_dom[OF assms(1-3)] .
  from instantiated_ancestors_suffix[OF assms(1, 2) instantiated_ancestor_mem[OF assms(1-3), of ?\<tau>s]]
  obtain pre where C: "instantiated_ancestors \<Sigma> C ?\<tau>s
                       = pre @ instantiated_ancestors \<Sigma> D (instantiated_ancestor \<Sigma> C ?\<tau>s D)"
    by blast
  from instantiated_ancestors_suffix[OF assms(1) D instantiated_ancestor_mem[OF assms(1) D assms(4)]]
  obtain pre' where "instantiated_ancestors \<Sigma> D (instantiated_ancestor \<Sigma> C ?\<tau>s D)
                     = pre' @ instantiated_ancestors \<Sigma> C
                                (instantiated_ancestor \<Sigma> D (instantiated_ancestor \<Sigma> C ?\<tau>s D) C)"
    by blast
  moreover have "length (instantiated_ancestors \<Sigma> C ?\<tau>s)
                 = length (instantiated_ancestors \<Sigma> C
                             (instantiated_ancestor \<Sigma> D (instantiated_ancestor \<Sigma> C ?\<tau>s D) C))"
    using instantiated_ancestors_upto_names[of "fcard (fmdom \<Sigma>)" \<Sigma> C ?\<tau>s]
    unfolding instantiated_ancestors_def by (metis length_map)
  ultimately have "length pre = 0" using C by auto
  with C have "hd (instantiated_ancestors \<Sigma> C ?\<tau>s)
               = hd (instantiated_ancestors \<Sigma> D (instantiated_ancestor \<Sigma> C ?\<tau>s D))"
    by simp
  then show ?thesis
    unfolding instantiated_ancestors_def using fcard_fmdom_Suc[OF assms(2)] by auto
qed

(* Ancestors at substituted type arguments: the substitution into the ancestors at the type arguments *)
lemma instantiated_ancestors_upto_subst:
  assumes "wf_class_table \<Sigma>"
  shows "\<lbrakk> C |\<in>| fmdom \<Sigma> ; inherits_within n \<Sigma> C ; length \<tau>s = length (type_params \<Sigma> C) \<rbrakk>
    \<Longrightarrow> instantiated_ancestors_upto n \<Sigma> C (map (subst \<tau>s' \<alpha>s) \<tau>s)
        = map (\<lambda>(D, \<sigma>s). (D, map (subst \<tau>s' \<alpha>s) \<sigma>s)) (instantiated_ancestors_upto n \<Sigma> C \<tau>s)"
proof (induction n arbitrary: C \<tau>s)
  case (Suc n)
  show ?case
  proof (cases "base \<Sigma> C")
    case (Some D\<sigma>s)
    then obtain D \<sigma>s where base: "base \<Sigma> C = Some (D, \<sigma>s)" by (cases D\<sigma>s) simp
    from wf_class_table_baseD[OF assms Suc.prems(1) base] have D: "D |\<in>| fmdom \<Sigma>"
      and fv: "\<forall>\<sigma> \<in> set \<sigma>s. fv \<sigma> \<subseteq> set (type_params \<Sigma> C)" and len: "length \<sigma>s = length (type_params \<Sigma> D)"
      by auto
    have args: "map (subst (map (subst \<tau>s' \<alpha>s) \<tau>s) (type_params \<Sigma> C)) \<sigma>s
                = map (subst \<tau>s' \<alpha>s) (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s)"
      using fv Suc.prems(3) by (simp add: subst_subst cong: map_cong)
    from Suc.prems(2) base have "inherits_within n \<Sigma> D" by simp
    have "instantiated_ancestors_upto n \<Sigma> D (map (subst \<tau>s' \<alpha>s) (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s))
          = map (\<lambda>(D, \<sigma>s). (D, map (subst \<tau>s' \<alpha>s) \<sigma>s))
              (instantiated_ancestors_upto n \<Sigma> D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s))"
      using len by (intro Suc.IH[OF D \<open>inherits_within n \<Sigma> D\<close>]) simp
    with base show ?thesis by (simp add: args)
  qed simp
qed simp

lemma instantiated_ancestor_subst:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "length \<tau>s = length (type_params \<Sigma> C)"
    and "D \<in> set (ancestors \<Sigma> C)"
  shows "instantiated_ancestor \<Sigma> C (map (subst \<tau>s' \<alpha>s) \<tau>s) D
         = map (subst \<tau>s' \<alpha>s) (instantiated_ancestor \<Sigma> C \<tau>s D)"
proof -
  have "instantiated_ancestors \<Sigma> C (map (subst \<tau>s' \<alpha>s) \<tau>s)
        = map (\<lambda>(D, \<sigma>s). (D, map (subst \<tau>s' \<alpha>s) \<sigma>s)) (instantiated_ancestors \<Sigma> C \<tau>s)"
    unfolding instantiated_ancestors_def
    by (rule instantiated_ancestors_upto_subst[OF assms(1, 2) wf_class_table_inherits[OF assms(1, 2)] assms(3)])
  moreover from assms(4) obtain \<sigma>s where "map_of (instantiated_ancestors \<Sigma> C \<tau>s) D = Some \<sigma>s"
    using ancestors_instantiated[of \<Sigma> C \<tau>s] by (auto dest: weak_map_of_SomeI)
  ultimately show ?thesis by (simp add: instantiated_ancestor_def map_of_map)
qed

lemma instantiated_ancestor_inst:
  assumes "wf_class_table \<Sigma>" and "wf_ty \<Sigma> (TyClass C \<tau>s)" and "D \<in> set (ancestors \<Sigma> C)"
  shows "instantiated_ancestor \<Sigma> C (map (inst \<eta>) \<tau>s) D = map (inst \<eta>) (instantiated_ancestor \<Sigma> C \<tau>s D)"
proof -
  have "finite (\<Union> (fv ` set \<tau>s))" by (simp add: finite_fv)
  then obtain \<alpha>s where \<alpha>s: "\<And>\<tau>. fv \<tau> \<subseteq> \<Union> (fv ` set \<tau>s) \<Longrightarrow> inst \<eta> \<tau> = subst (map \<eta> \<alpha>s) \<alpha>s \<tau>"
    using inst_subst_cover by blast
  have \<tau>s: "map (inst \<eta>) \<tau>s = map (subst (map \<eta> \<alpha>s) \<alpha>s) \<tau>s" by (intro map_cong[OF refl] \<alpha>s) auto
  have anc: "map (subst (map \<eta> \<alpha>s) \<alpha>s) (instantiated_ancestor \<Sigma> C \<tau>s D)
             = map (inst \<eta>) (instantiated_ancestor \<Sigma> C \<tau>s D)"
    using instantiated_ancestor_wf[OF assms] by (intro map_cong[OF refl]) (auto simp: \<alpha>s)
  have "C |\<in>| fmdom \<Sigma>" and "length \<tau>s = length (type_params \<Sigma> C)" using assms(2) by simp_all
  from instantiated_ancestor_subst[OF assms(1) this assms(3), of "map \<eta> \<alpha>s" \<alpha>s] show ?thesis
    unfolding \<tau>s by (simp add: anc)
qed

(* Type arguments of ancestor D of class C at \<tau>s, as the substitution of \<tau>s into those at the type parameters *)
lemma instantiated_ancestor_params:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "length \<tau>s = length (type_params \<Sigma> C)"
    and "D \<in> set (ancestors \<Sigma> C)"
  shows "instantiated_ancestor \<Sigma> C \<tau>s D
         = map (subst \<tau>s (type_params \<Sigma> C)) (instantiated_ancestor \<Sigma> C (map TyVar (type_params \<Sigma> C)) D)"
proof -
  have "map (subst \<tau>s (type_params \<Sigma> C)) (map TyVar (type_params \<Sigma> C)) = \<tau>s"
    using assms(3) wf_class_table_distinct_params[OF assms(1, 2)]
    by (auto simp: map_of_zip_nth intro: nth_equalityI)
  with instantiated_ancestor_subst[OF assms(1, 2) _ assms(4), where \<tau>s = "map TyVar (type_params \<Sigma> C)"
      and \<tau>s' = \<tau>s and \<alpha>s = "type_params \<Sigma> C"]
  show ?thesis by simp
qed

(* Class below each of its ancestors *)
lemma subty_ancestors_upto:
  assumes "wf_class_table \<Sigma>"
  shows "\<lbrakk> C |\<in>| fmdom \<Sigma> ; inherits_within n \<Sigma> C ; (D, \<sigma>s) \<in> set (instantiated_ancestors_upto n \<Sigma> C \<tau>s) \<rbrakk>
    \<Longrightarrow> \<Sigma> \<turnstile> TyClass C \<tau>s <: TyClass D \<sigma>s"
proof (induction n arbitrary: C \<tau>s)
  case (Suc n)
  show ?case
  proof (cases "(D, \<sigma>s) = (C, \<tau>s)")
    case True
    then show ?thesis by (simp add: SubtyRefl)
  next
    case False
    with Suc.prems obtain E \<rho>s where base: "base \<Sigma> C = Some (E, \<rho>s)"
      and mem: "(D, \<sigma>s) \<in> set (instantiated_ancestors_upto n \<Sigma> E (map (subst \<tau>s (type_params \<Sigma> C)) \<rho>s))"
      by (auto split: option.splits)
    from wf_class_table_baseD[OF assms Suc.prems(1) base] have E: "E |\<in>| fmdom \<Sigma>" by simp
    from Suc.prems(2) base have "inherits_within n \<Sigma> E" by simp
    from Suc.IH[OF E this mem] base show ?thesis by (rule SubtyClassExtend[rotated])
  qed
qed simp

lemma subty_ancestor:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "D \<in> set (ancestors \<Sigma> C)"
  shows "\<Sigma> \<turnstile> TyClass C \<tau>s <: TyClass D (instantiated_ancestor \<Sigma> C \<tau>s D)"
  using instantiated_ancestor_mem[OF assms, of \<tau>s]
  unfolding instantiated_ancestors_def
  by (rule subty_ancestors_upto[OF assms(1, 2) wf_class_table_inherits[OF assms(1, 2)]])

(* Subtyping between class types: the supertype's class an ancestor, at equivalent type arguments *)
lemma subty_class_class:
  assumes "wf_class_table \<Sigma>"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<sigma> = TyClass C \<tau>s \<Longrightarrow> \<tau> = TyClass D \<sigma>s \<Longrightarrow> C |\<in>| fmdom \<Sigma>
    \<Longrightarrow> D \<in> set (ancestors \<Sigma> C) \<and> list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> C \<tau>s D) \<sigma>s"
    and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s' \<Longrightarrow> True"
proof (induction arbitrary: C \<tau>s rule: subty_subtys.inducts)
  case (SubtyRefl \<tau>)
  then show ?case by (auto simp: list_all2_conv_all_nth subty_subtys.SubtyRefl)
next
  case (SubtyClassExtend C' E \<rho>s \<tau>s' \<tau>)
  from SubtyClassExtend(4) have C': "C' = C" and \<tau>s': "\<tau>s' = \<tau>s" by simp_all
  note base = SubtyClassExtend(1)[unfolded C' \<tau>s']
  let ?\<rho>s = "map (subst \<tau>s (type_params \<Sigma> C)) \<rho>s"
  from wf_class_table_baseD[OF assms SubtyClassExtend(6) base] have E: "E |\<in>| fmdom \<Sigma>" by simp
  from SubtyClassExtend(3)[OF refl SubtyClassExtend(5) E, unfolded \<tau>s' C']
  have anc: "D \<in> set (ancestors \<Sigma> E)"
    and equiv: "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> E ?\<rho>s D) \<sigma>s"
    by auto
  note chain = instantiated_ancestors_base[OF assms SubtyClassExtend(6) base, of \<tau>s]
  have "D \<noteq> C"
  proof
    assume "D = C"
    with anc have "C \<in> set (ancestors \<Sigma> E)" by simp
    then obtain \<rho>s' where "(C, \<rho>s') \<in> set (instantiated_ancestors \<Sigma> E ?\<rho>s)"
      using ancestors_instantiated[of \<Sigma> E ?\<rho>s] by auto
    then have "\<not> distinct (map fst (instantiated_ancestors \<Sigma> C \<tau>s))" unfolding chain by force
    with instantiated_ancestors_distinct[OF assms SubtyClassExtend(6)] show False by blast
  qed
  with anc have "D \<in> set (ancestors \<Sigma> C)"
    using ancestors_instantiated[of \<Sigma> C \<tau>s] ancestors_instantiated[of \<Sigma> E ?\<rho>s] unfolding chain by auto
  moreover have "instantiated_ancestor \<Sigma> C \<tau>s D = instantiated_ancestor \<Sigma> E ?\<rho>s D"
    using \<open>D \<noteq> C\<close> unfolding instantiated_ancestor_def chain by simp
  ultimately show ?case using equiv by simp
next
  case (SubtyClass \<sigma>s' \<tau>s' C')
  then show ?case by (auto simp: subtys_list_all2 list_all2_conv_all_nth)
qed auto

(* Equivalence of class types: the same class at equivalent type arguments *)
lemma equiv_class_class:
  assumes "wf_class_table \<Sigma>" and "\<Sigma> \<turnstile> TyClass C \<tau>s \<approx> TyClass D \<sigma>s" and "C |\<in>| fmdom \<Sigma>" and "D |\<in>| fmdom \<Sigma>"
  shows "C = D" and "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) \<tau>s \<sigma>s"
proof -
  from subty_class_class(1)[OF assms(1) _ refl refl assms(3)] assms(2) have D: "D \<in> set (ancestors \<Sigma> C)"
    and equiv: "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> C \<tau>s D) \<sigma>s"
    by auto
  from subty_class_class(1)[OF assms(1) _ refl refl assms(4)] assms(2) have "C \<in> set (ancestors \<Sigma> D)" by auto
  from ancestors_antisym[OF assms(1, 3) D this] show "C = D" .
  with equiv show "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) \<tau>s \<sigma>s" using instantiated_ancestor_head[OF assms(3)] by simp
qed


subsection \<open>Matching of type arguments\<close>

lemma base_type_lit_never [simp]: "base_type_lit l \<noteq> TyPrim Never"
  by (cases l) simp_all

(* Type below Never other than a union: Never *)
lemma subty_never_inv: "\<lbrakk> \<Sigma> \<turnstile> \<tau> <: TyPrim Never ; \<not> is_union \<tau> \<rbrakk> \<Longrightarrow> \<tau> = TyPrim Never"
  by (cases \<tau>) (auto simp: subty_prim_iff)

lemma subty_prim_prim: "\<lbrakk> \<Sigma> \<turnstile> TyPrim p <: TyPrim q ; \<Sigma> \<turnstile> TyPrim q <: TyPrim p \<rbrakk> \<Longrightarrow> p = q"
proof -
  assume equiv: "\<Sigma> \<turnstile> TyPrim p <: TyPrim q" "\<Sigma> \<turnstile> TyPrim q <: TyPrim p"
  have "\<not> \<Sigma> \<turnstile> TyPrim object <: TyPrim Sized" using subty_sized_inv(1)[OF _ refl, of \<Sigma> "TyPrim object"] by auto
  with equiv show "p = q"
    by (cases "p \<in> {object, Sized}"; cases "q \<in> {object, Sized}") (auto simp: subty_prim_iff split: if_splits)
qed

lemma subst_fresh: "(\<And>\<alpha>. \<alpha> \<in> fv \<sigma> \<Longrightarrow> \<alpha> \<notin> set \<alpha>s) \<Longrightarrow> subst \<tau>s \<alpha>s \<sigma> = \<sigma>"
proof (induction \<sigma>)
  case (TyVar \<alpha>)
  then show ?case by (auto split: option.splits dest!: map_of_SomeD set_zip_leftD)
qed (auto intro: map_idI)

(* Sequence matching clashes when lengths differ or a pair of types clashes *)
lemma match_args_seq_Clash:
  "match_args_seq \<rho>s \<sigma>s = Clash
  \<Longrightarrow> length \<rho>s \<noteq> length \<sigma>s \<or> (\<exists>i < length \<rho>s. match_args (\<rho>s ! i) (\<sigma>s ! i) = Clash)"
proof (induction \<rho>s arbitrary: \<sigma>s)
  case Nil
  then show ?case by (cases \<sigma>s) auto
next
  case (Cons \<rho> \<rho>s)
  note IH = Cons.IH
  show ?case
  proof (cases \<sigma>s)
    case (Cons \<sigma> \<sigma>s')
    with Cons.prems have "match_args \<rho> \<sigma> = Clash \<or> match_args_seq \<rho>s \<sigma>s' = Clash"
      by (cases "match_args \<rho> \<sigma>"; cases "match_args_seq \<rho>s \<sigma>s'") auto
    then show ?thesis
    proof
      assume "match_args \<rho> \<sigma> = Clash"
      then show ?thesis unfolding Cons by (auto intro: exI[of _ 0])
    next
      assume "match_args_seq \<rho>s \<sigma>s' = Clash"
      from IH[OF this] show ?thesis
      proof
        assume "\<exists>i < length \<rho>s. match_args (\<rho>s ! i) (\<sigma>s' ! i) = Clash"
        then obtain i where "i < length \<rho>s" and "match_args (\<rho>s ! i) (\<sigma>s' ! i) = Clash" by blast
        then show ?thesis unfolding Cons by (auto intro!: exI[of _ "Suc i"])
      qed (simp add: Cons)
    qed
  qed simp
qed

lemma match_args_seq_length: "match_args_seq \<rho>s \<sigma>s = Matched \<gamma> \<Longrightarrow> length \<rho>s = length \<sigma>s"
proof (induction \<rho>s arbitrary: \<sigma>s \<gamma>)
  case Nil
  then show ?case by (cases \<sigma>s) auto
next
  case (Cons \<rho> \<rho>s)
  then show ?case by (cases \<sigma>s) (auto dest!: merge_match_Matched)
qed

lemma match_args_seq_Matched:
  "\<lbrakk> match_args_seq \<rho>s \<sigma>s = Matched \<gamma> ; fmlookup \<gamma> \<alpha> = Some \<sigma>' \<rbrakk>
  \<Longrightarrow> length \<rho>s = length \<sigma>s
      \<and> (\<exists>i < length \<rho>s. \<exists>\<gamma>'. match_args (\<rho>s ! i) (\<sigma>s ! i) = Matched \<gamma>' \<and> fmlookup \<gamma>' \<alpha> = Some \<sigma>')"
proof (induction \<rho>s arbitrary: \<sigma>s \<gamma>)
  case Nil
  then show ?case by (cases \<sigma>s) auto
next
  case (Cons \<rho> \<rho>s)
  note IH = Cons.IH
  from Cons.prems(1) obtain \<sigma> \<sigma>s' where \<sigma>s: "\<sigma>s = \<sigma> # \<sigma>s'" by (cases \<sigma>s) auto
  with Cons.prems(1) have "merge_match (match_args \<rho> \<sigma>) (match_args_seq \<rho>s \<sigma>s') = Matched \<gamma>" by simp
  from merge_match_Matched[OF this] obtain \<gamma>\<^sub>1 \<gamma>\<^sub>2
    where m: "match_args \<rho> \<sigma> = Matched \<gamma>\<^sub>1" "match_args_seq \<rho>s \<sigma>s' = Matched \<gamma>\<^sub>2" and "\<gamma> = \<gamma>\<^sub>1 ++\<^sub>f \<gamma>\<^sub>2"
    by blast
  with Cons.prems(2) have "fmlookup \<gamma>\<^sub>1 \<alpha> = Some \<sigma>' \<or> fmlookup \<gamma>\<^sub>2 \<alpha> = Some \<sigma>'"
    by (auto simp: fmlookup_add split: if_splits option.splits)
  then show ?case
  proof
    assume "fmlookup \<gamma>\<^sub>1 \<alpha> = Some \<sigma>'"
    with m(1) match_args_seq_length[OF m(2)] show ?thesis unfolding \<sigma>s by (auto intro!: exI[of _ 0])
  next
    assume "fmlookup \<gamma>\<^sub>2 \<alpha> = Some \<sigma>'"
    from IH[OF m(2) this] obtain i \<gamma>' where "length \<rho>s = length \<sigma>s'" and "i < length \<rho>s"
      and "match_args (\<rho>s ! i) (\<sigma>s' ! i) = Matched \<gamma>'" and "fmlookup \<gamma>' \<alpha> = Some \<sigma>'"
      by blast
    then show ?thesis unfolding \<sigma>s by (auto intro!: exI[of _ "Suc i"])
  qed
qed

(* Inversion of subtyping by a structured type, for a type other than a union *)
lemma subty_list_inv':
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: TyList \<tau> ; \<not> is_union \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> = TyPrim Never \<or> (\<exists>\<sigma>'. \<sigma> = TyList \<sigma>' \<and> \<Sigma> \<turnstile> \<sigma>' \<approx> \<tau>)"
  using subty_list_inv(1)[OF _ refl] by blast

lemma subty_dict_inv':
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: TyDict \<tau> ; \<not> is_union \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> = TyPrim Never \<or> (\<exists>\<sigma>'. \<sigma> = TyDict \<sigma>' \<and> \<Sigma> \<turnstile> \<sigma>' \<approx> \<tau>)"
  using subty_dict_inv(1)[OF _ refl] by blast

lemma subty_tuple_inv':
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: TyTuple \<tau>s ; \<not> is_union \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> = TyPrim Never \<or> (\<exists>\<sigma>s. \<sigma> = TyTuple \<sigma>s \<and> \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s)"
  using subty_tuple_inv(1)[OF _ refl] by blast

lemma subty_callable_inv':
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: TyCallable \<tau>s \<tau> ; \<not> is_union \<sigma> \<rbrakk>
  \<Longrightarrow> \<sigma> = TyPrim Never \<or> (\<exists>\<sigma>s \<sigma>'. \<sigma> = TyCallable \<sigma>s \<sigma>' \<and> \<Sigma> \<turnstile> \<tau>s [<:] \<sigma>s \<and> \<Sigma> \<turnstile> \<sigma>' <: \<tau>)"
  using subty_callable_inv(1)[OF _ refl] by blast

lemma subty_class_inv':
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: TyClass C \<tau>s ; \<not> is_union \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> = TyPrim Never \<or> (\<exists>D \<sigma>s. \<sigma> = TyClass D \<sigma>s)"
  using subty_class_inv(1)[OF _ refl] by blast

lemma subty_literal_inv':
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: TyLiteral l ; \<not> is_union \<sigma> \<rbrakk> \<Longrightarrow> \<sigma> = TyPrim Never \<or> \<sigma> = TyLiteral l"
  using subty_literal_inv(1)[OF _ refl] by blast

lemmas subty_structured_inv =
  subty_list_inv' subty_dict_inv' subty_tuple_inv' subty_callable_inv' subty_class_inv' subty_literal_inv'

(* Types matching with a clash: never equivalent under substitution *)
lemma match_args_clash:
  assumes wf: "wf_class_table \<Sigma>"
  shows "\<lbrakk> match_args \<rho> \<sigma> = Clash ; wf_ty \<Sigma> \<rho> ; wf_ty \<Sigma> \<sigma> \<rbrakk> \<Longrightarrow> \<not> \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>"
proof (induction \<rho> arbitrary: \<sigma>)
  case (TyPrim p)
  show ?case
  proof (cases "p \<in> {object, Sized}")
    case True
    with TyPrim.prems show ?thesis
      by (cases \<sigma>) (auto dest!: subty_structured_inv subty_never_inv dest: subty_prim_prim split: if_splits)
  next
    case False
    with TyPrim.prems show ?thesis
      by (cases \<sigma>)
         (auto dest!: subty_structured_inv subty_never_inv dest: subty_prim_prim simp: subty_prim_iff
          split: if_splits)
  qed
next
  case (TyLiteral l)
  then show ?case
    by (cases \<sigma>) (auto dest!: subty_structured_inv subty_never_inv simp: subty_prim_iff split: if_splits)
next
  case (TyList \<rho>)
  then show ?case
    by (cases \<sigma>)
       (auto dest!: subty_list_inv' subty_never_inv subty_literal_inv' simp: subty_prim_iff split: if_splits)
next
  case (TyDict \<rho>)
  then show ?case
    by (cases \<sigma>)
       (auto dest!: subty_dict_inv' subty_never_inv subty_literal_inv' simp: subty_prim_iff split: if_splits)
next
  case (TyTuple \<rho>s)
  show ?case
  proof (cases \<sigma>)
    case (TyTuple \<sigma>s)
    with TyTuple.prems(1) have "match_args_seq \<rho>s \<sigma>s = Clash" by simp
    from match_args_seq_Clash[OF this] show ?thesis
    proof
      assume "length \<rho>s \<noteq> length \<sigma>s"
      then show ?thesis
        unfolding TyTuple by (auto dest!: subty_tuple_inv(1)[OF _ refl] list_all2_lengthD simp: subtys_list_all2)
    next
      assume "\<exists>i < length \<rho>s. match_args (\<rho>s ! i) (\<sigma>s ! i) = Clash"
      then obtain i where i: "i < length \<rho>s" and clash: "match_args (\<rho>s ! i) (\<sigma>s ! i) = Clash" by blast
      show ?thesis
      proof
        assume "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyTuple \<rho>s) \<approx> subst \<upsilon>s \<beta>s \<sigma>"
        then have "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>) \<rho>s \<sigma>s"
          unfolding TyTuple
          by (auto dest!: subty_tuple_inv(1)[OF _ refl] simp: subtys_list_all2 list_all2_map1 list_all2_map2
              list_all2_conv_all_nth)
        with i have equiv: "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (\<rho>s ! i) \<approx> subst \<upsilon>s \<beta>s (\<sigma>s ! i)" and "i < length \<sigma>s"
          by (auto simp: list_all2_conv_all_nth)
        then have "wf_ty \<Sigma> (\<rho>s ! i)" and "wf_ty \<Sigma> (\<sigma>s ! i)" using TyTuple.prems(2, 3) i unfolding TyTuple by auto
        with TyTuple.IH[OF nth_mem[OF i] clash] equiv show False by blast
      qed
    qed
  qed (use TyTuple.prems in
       \<open>auto dest!: subty_tuple_inv' subty_never_inv subty_literal_inv' simp: subty_prim_iff split: if_splits\<close>)
next
  case (TyCallable \<rho>s \<rho>\<^sub>0)
  show ?case
  proof (cases \<sigma>)
    case (TyCallable \<sigma>s \<sigma>\<^sub>0)
    with TyCallable.prems(1) have "match_args_seq (\<rho>\<^sub>0 # \<rho>s) (\<sigma>\<^sub>0 # \<sigma>s) = Clash" by simp
    from match_args_seq_Clash[OF this] show ?thesis
    proof
      assume "length (\<rho>\<^sub>0 # \<rho>s) \<noteq> length (\<sigma>\<^sub>0 # \<sigma>s)"
      then show ?thesis
        unfolding TyCallable
        by (auto dest!: subty_callable_inv(1)[OF _ refl] list_all2_lengthD simp: subtys_list_all2)
    next
      assume "\<exists>i < length (\<rho>\<^sub>0 # \<rho>s). match_args ((\<rho>\<^sub>0 # \<rho>s) ! i) ((\<sigma>\<^sub>0 # \<sigma>s) ! i) = Clash"
      then obtain i where i: "i < length (\<rho>\<^sub>0 # \<rho>s)"
        and clash: "match_args ((\<rho>\<^sub>0 # \<rho>s) ! i) ((\<sigma>\<^sub>0 # \<sigma>s) ! i) = Clash"
        by blast
      show ?thesis
      proof
        assume "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyCallable \<rho>s \<rho>\<^sub>0) \<approx> subst \<upsilon>s \<beta>s \<sigma>"
        then have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho>\<^sub>0 \<approx> subst \<upsilon>s \<beta>s \<sigma>\<^sub>0"
          and "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>) \<rho>s \<sigma>s"
          unfolding TyCallable
          by (auto dest!: subty_callable_inv(1)[OF _ refl] simp: subtys_list_all2 list_all2_map1 list_all2_map2
              list_all2_conv_all_nth)
        then have "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>) (\<rho>\<^sub>0 # \<rho>s) (\<sigma>\<^sub>0 # \<sigma>s)" by simp
        with i have equiv: "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s ((\<rho>\<^sub>0 # \<rho>s) ! i) \<approx> subst \<upsilon>s \<beta>s ((\<sigma>\<^sub>0 # \<sigma>s) ! i)"
          and len: "i < length (\<sigma>\<^sub>0 # \<sigma>s)"
          by (auto simp: list_all2_conv_all_nth)
        have wf: "wf_ty \<Sigma> ((\<rho>\<^sub>0 # \<rho>s) ! i)" "wf_ty \<Sigma> ((\<sigma>\<^sub>0 # \<sigma>s) ! i)"
          using TyCallable.prems(2, 3) i len unfolding TyCallable by (auto simp: nth_Cons split: nat.splits)
        show False
        proof (cases i)
          case 0
          with clash wf equiv have "match_args \<rho>\<^sub>0 \<sigma>\<^sub>0 = Clash" and "wf_ty \<Sigma> \<rho>\<^sub>0" and "wf_ty \<Sigma> \<sigma>\<^sub>0"
            and "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho>\<^sub>0 \<approx> subst \<upsilon>s \<beta>s \<sigma>\<^sub>0"
            by simp_all
          with TyCallable.IH(2)[OF this(1-3)] show False by blast
        next
          case (Suc j)
          with i have mem: "\<rho>s ! j \<in> set \<rho>s" by simp
          from Suc clash wf equiv have "match_args (\<rho>s ! j) (\<sigma>s ! j) = Clash" and "wf_ty \<Sigma> (\<rho>s ! j)"
            and "wf_ty \<Sigma> (\<sigma>s ! j)" and "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (\<rho>s ! j) \<approx> subst \<upsilon>s \<beta>s (\<sigma>s ! j)"
            by simp_all
          with TyCallable.IH(1)[OF mem this(1-3)] show False by blast
        qed
      qed
    qed
  qed (use TyCallable.prems in
       \<open>auto dest!: subty_callable_inv' subty_never_inv subty_literal_inv' simp: subty_prim_iff split: if_splits\<close>)
next
  case (TyClass C \<rho>s)
  show ?case
  proof (cases \<sigma>)
    case (TyClass D \<sigma>s)
    show ?thesis
    proof
      assume equiv: "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyClass C \<rho>s) \<approx> subst \<upsilon>s \<beta>s \<sigma>"
      have "C |\<in>| fmdom \<Sigma>" and "D |\<in>| fmdom \<Sigma>" using TyClass.prems(2, 3) unfolding TyClass by auto
      from equiv_class_class[OF wf equiv[unfolded TyClass, simplified] this]
      have CD: "C = D" and args: "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>) \<rho>s \<sigma>s"
        by (auto simp: list_all2_map1 list_all2_map2)
      with TyClass.prems(1) have "match_args_seq \<rho>s \<sigma>s = Clash" unfolding TyClass by simp
      from match_args_seq_Clash[OF this] show False
      proof
        assume "length \<rho>s \<noteq> length \<sigma>s"
        with args show False by (auto dest: list_all2_lengthD)
      next
        assume "\<exists>i < length \<rho>s. match_args (\<rho>s ! i) (\<sigma>s ! i) = Clash"
        then obtain i where i: "i < length \<rho>s" and clash: "match_args (\<rho>s ! i) (\<sigma>s ! i) = Clash" by blast
        with args have equiv: "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (\<rho>s ! i) \<approx> subst \<upsilon>s \<beta>s (\<sigma>s ! i)" and "i < length \<sigma>s"
          by (auto simp: list_all2_conv_all_nth)
        then have "wf_ty \<Sigma> (\<rho>s ! i)" and "wf_ty \<Sigma> (\<sigma>s ! i)" using TyClass.prems(2, 3) i unfolding TyClass by auto
        with TyClass.IH[OF nth_mem[OF i] clash] equiv show False by blast
      qed
    qed
  qed (use TyClass.prems in
       \<open>auto dest!: subty_class_inv' subty_never_inv subty_literal_inv' simp: subty_prim_iff split: if_splits\<close>)
qed simp_all

(* Type bound at a determined occurrence by matching: equivalent under any substitutions equating the types *)
lemma match_args_unique:
  assumes wf: "wf_class_table \<Sigma>"
  shows "\<lbrakk> match_args \<rho> \<sigma> = Matched \<gamma> ; fmlookup \<gamma> \<alpha> = Some \<sigma>' ; wf_ty \<Sigma> \<rho> ; wf_ty \<Sigma> \<sigma>
          ; \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma> \<rbrakk>
    \<Longrightarrow> \<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyVar \<alpha>) \<approx> subst \<upsilon>s \<beta>s \<sigma>'"
proof (induction \<rho> arbitrary: \<sigma> \<gamma>)
  case (TyVar \<beta>)
  then show ?case by (auto split: if_splits)
next
  case (TyList \<rho>)
  from TyList.prems(1) obtain \<sigma>\<^sub>1 where \<sigma>: "\<sigma> = TyList \<sigma>\<^sub>1" and m: "match_args \<rho> \<sigma>\<^sub>1 = Matched \<gamma>"
    by (cases \<sigma>) (auto split: if_splits)
  from TyList.prems(5) have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>\<^sub>1"
    unfolding \<sigma> by (auto dest!: subty_list_inv(1)[OF _ refl])
  with TyList.IH[OF m TyList.prems(2)] TyList.prems(3, 4) show ?case unfolding \<sigma> by simp
next
  case (TyDict \<rho>)
  from TyDict.prems(1) obtain \<sigma>\<^sub>1 where \<sigma>: "\<sigma> = TyDict \<sigma>\<^sub>1" and m: "match_args \<rho> \<sigma>\<^sub>1 = Matched \<gamma>"
    by (cases \<sigma>) (auto split: if_splits)
  from TyDict.prems(5) have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>\<^sub>1"
    unfolding \<sigma> by (auto dest!: subty_dict_inv(1)[OF _ refl])
  with TyDict.IH[OF m TyDict.prems(2)] TyDict.prems(3, 4) show ?case unfolding \<sigma> by simp
next
  case (TyTuple \<rho>s)
  from TyTuple.prems(1) obtain \<sigma>s where \<sigma>: "\<sigma> = TyTuple \<sigma>s" and m: "match_args_seq \<rho>s \<sigma>s = Matched \<gamma>"
    by (cases \<sigma>) (auto split: if_splits)
  from match_args_seq_Matched[OF m TyTuple.prems(2)] obtain i \<gamma>' where i: "i < length \<rho>s"
    and mi: "match_args (\<rho>s ! i) (\<sigma>s ! i) = Matched \<gamma>'" and look: "fmlookup \<gamma>' \<alpha> = Some \<sigma>'"
    and len: "length \<rho>s = length \<sigma>s"
    by blast
  from TyTuple.prems(5) have "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>) \<rho>s \<sigma>s"
    unfolding \<sigma>
    by (auto dest!: subty_tuple_inv(1)[OF _ refl] simp: subtys_list_all2 list_all2_map1 list_all2_map2
        list_all2_conv_all_nth)
  with i have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (\<rho>s ! i) \<approx> subst \<upsilon>s \<beta>s (\<sigma>s ! i)" by (auto simp: list_all2_conv_all_nth)
  moreover have "wf_ty \<Sigma> (\<rho>s ! i)" and "wf_ty \<Sigma> (\<sigma>s ! i)" using TyTuple.prems(3, 4) i len unfolding \<sigma> by auto
  ultimately show ?case using TyTuple.IH[OF nth_mem[OF i] mi look] by blast
next
  case (TyCallable \<rho>s \<rho>\<^sub>0)
  from TyCallable.prems(1) obtain \<sigma>s \<sigma>\<^sub>0 where \<sigma>: "\<sigma> = TyCallable \<sigma>s \<sigma>\<^sub>0"
    and m: "match_args_seq (\<rho>\<^sub>0 # \<rho>s) (\<sigma>\<^sub>0 # \<sigma>s) = Matched \<gamma>"
    by (cases \<sigma>) (auto split: if_splits)
  from match_args_seq_Matched[OF m TyCallable.prems(2)] obtain i \<gamma>' where i: "i < length (\<rho>\<^sub>0 # \<rho>s)"
    and mi: "match_args ((\<rho>\<^sub>0 # \<rho>s) ! i) ((\<sigma>\<^sub>0 # \<sigma>s) ! i) = Matched \<gamma>'" and look: "fmlookup \<gamma>' \<alpha> = Some \<sigma>'"
    and len: "length (\<rho>\<^sub>0 # \<rho>s) = length (\<sigma>\<^sub>0 # \<sigma>s)"
    by blast
  from TyCallable.prems(5) have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho>\<^sub>0 \<approx> subst \<upsilon>s \<beta>s \<sigma>\<^sub>0"
    and "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>) \<rho>s \<sigma>s"
    unfolding \<sigma>
    by (auto dest!: subty_callable_inv(1)[OF _ refl] simp: subtys_list_all2 list_all2_map1 list_all2_map2
        list_all2_conv_all_nth)
  then have "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>) (\<rho>\<^sub>0 # \<rho>s) (\<sigma>\<^sub>0 # \<sigma>s)" by simp
  with i have equiv: "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s ((\<rho>\<^sub>0 # \<rho>s) ! i) \<approx> subst \<upsilon>s \<beta>s ((\<sigma>\<^sub>0 # \<sigma>s) ! i)"
    by (auto simp: list_all2_conv_all_nth)
  have wf: "wf_ty \<Sigma> ((\<rho>\<^sub>0 # \<rho>s) ! i)" "wf_ty \<Sigma> ((\<sigma>\<^sub>0 # \<sigma>s) ! i)"
    using TyCallable.prems(3, 4) i len unfolding \<sigma> by (auto simp: nth_Cons split: nat.splits)
  show ?case
  proof (cases i)
    case 0
    with mi wf equiv have "match_args \<rho>\<^sub>0 \<sigma>\<^sub>0 = Matched \<gamma>'" and "wf_ty \<Sigma> \<rho>\<^sub>0" and "wf_ty \<Sigma> \<sigma>\<^sub>0"
      and "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho>\<^sub>0 \<approx> subst \<upsilon>s \<beta>s \<sigma>\<^sub>0"
      by simp_all
    from TyCallable.IH(2)[OF this(1) look this(2-4)] show ?thesis .
  next
    case (Suc j)
    with i have mem: "\<rho>s ! j \<in> set \<rho>s" by simp
    from Suc mi wf equiv have "match_args (\<rho>s ! j) (\<sigma>s ! j) = Matched \<gamma>'" and "wf_ty \<Sigma> (\<rho>s ! j)"
      and "wf_ty \<Sigma> (\<sigma>s ! j)" and "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (\<rho>s ! j) \<approx> subst \<upsilon>s \<beta>s (\<sigma>s ! j)"
      by simp_all
    from TyCallable.IH(1)[OF mem this(1) look this(2-4)] show ?thesis .
  qed
next
  case (TyClass C \<rho>s)
  from TyClass.prems(1) obtain \<sigma>s where \<sigma>: "\<sigma> = TyClass C \<sigma>s" and m: "match_args_seq \<rho>s \<sigma>s = Matched \<gamma>"
    by (cases \<sigma>) (auto split: if_splits)
  from match_args_seq_Matched[OF m TyClass.prems(2)] obtain i \<gamma>' where i: "i < length \<rho>s"
    and mi: "match_args (\<rho>s ! i) (\<sigma>s ! i) = Matched \<gamma>'" and look: "fmlookup \<gamma>' \<alpha> = Some \<sigma>'"
    and len: "length \<rho>s = length \<sigma>s"
    by blast
  have C: "C |\<in>| fmdom \<Sigma>" using TyClass.prems(3) by simp
  from equiv_class_class(2)[OF wf TyClass.prems(5)[unfolded \<sigma>, simplified] C C]
  have "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<rho> \<approx> subst \<upsilon>s \<beta>s \<sigma>) \<rho>s \<sigma>s" by (simp add: list_all2_map1 list_all2_map2)
  with i have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (\<rho>s ! i) \<approx> subst \<upsilon>s \<beta>s (\<sigma>s ! i)" by (auto simp: list_all2_conv_all_nth)
  moreover have "wf_ty \<Sigma> (\<rho>s ! i)" and "wf_ty \<Sigma> (\<sigma>s ! i)" using TyClass.prems(3, 4) i len unfolding \<sigma> by auto
  ultimately show ?case using TyClass.IH[OF nth_mem[OF i] mi look] by blast
next
  case (TyPrim p)
  then show ?case by (cases \<sigma>) (auto split: if_splits)
next
  case (TyLiteral l)
  then show ?case by (cases \<sigma>) (auto split: if_splits)
qed auto


context evaluation
begin

subsection \<open>Values at types\<close>

lemma wf_val_never: "\<turnstile> v : Ty (TyPrim Never) \<Longrightarrow> False"
proof -
  assume "\<turnstile> v : Ty (TyPrim Never)"
  from wf_val_intro(1)[OF this] obtain \<sigma> where "intro_typed v \<sigma>" and "\<Sigma> \<turnstile> \<sigma> <: TyPrim Never" by blast
  with intro_typed_nonunion[OF this(1)] subty_never_inv show False by blast
qed

(* Value at an instance of a type: at the instance of one of its disjuncts *)
lemma wf_val_inst_disjunct: "\<turnstile> v : Ty (inst \<eta> \<tau>) \<Longrightarrow> \<exists>\<sigma> \<in> set (disjuncts \<tau>). \<turnstile> v : Ty (inst \<eta> \<sigma>)"
  by (induction \<tau>) (auto dest: wf_val_union)

(* Introduction type of a value, below each of its types *)
lemma wf_list_sub: "\<turnstile> VList vs : Ty \<tau> \<Longrightarrow> \<exists>\<upsilon>. \<Sigma> \<turnstile> TyList \<upsilon> <: \<tau>"
  using wf_val_intro(1) by fastforce

lemma wf_tuple_sub: "\<turnstile> VTuple vs : Ty \<tau> \<Longrightarrow> \<exists>\<upsilon>s. \<Sigma> \<turnstile> TyTuple \<upsilon>s <: \<tau>"
  using wf_val_intro(1) by fastforce

lemma wf_dict_sub: "\<turnstile> VDict \<delta> : Ty \<tau> \<Longrightarrow> \<exists>\<upsilon>. \<Sigma> \<turnstile> TyDict \<upsilon> <: \<tau>"
  using wf_val_intro(1) by fastforce

lemma wf_lit_sub:
  "\<turnstile> VLit l : Ty \<tau> \<Longrightarrow> \<Sigma> \<turnstile> TyLiteral l <: \<tau> \<or> (\<exists>x. l = LitFloat x \<and> \<Sigma> \<turnstile> TyPrim float <: \<tau>)"
  using wf_val_intro(1) by fastforce

(* Range class: no base class, no type parameters, no other ancestor *)
lemma range_base: "base \<Sigma> range_class = None"
  using range_lookup by (simp add: base_def predefined_classes_def)

lemma range_params: "type_params \<Sigma> range_class = []"
  using range_lookup by (simp add: type_params_def predefined_classes_def)

lemma range_ancestors: "instantiated_ancestors \<Sigma> range_class \<tau>s = [(range_class, \<tau>s)]"
proof -
  have "range_class |\<in>| fmdom \<Sigma>" using range_lookup by (simp add: predefined_classes_def fmlookup_dom_iff)
  from fcard_fmdom_Suc[OF this] show ?thesis by (auto simp: instantiated_ancestors_def range_base)
qed

lemma wf_range_sub: "\<turnstile> VObject range_class xvs : Ty \<tau> \<Longrightarrow> \<Sigma> \<turnstile> TyClass range_class [] <: \<tau>"
  by (auto elim!: wf_object simp: range_params)

(* Value of a kind at an instance of a type: the type has values of that kind *)
lemma list_has_values: "\<turnstile> VList vs : Ty (inst \<eta> \<sigma>) \<Longrightarrow> has_values \<Sigma> ListKind \<sigma>"
proof (induction \<sigma>)
  case (TyUnion \<sigma> \<tau>)
  then show ?case by (auto dest: wf_val_union)
next
  case (TyPrim p)
  from wf_list_sub[OF TyPrim.prems] obtain \<upsilon> where "\<Sigma> \<turnstile> TyList \<upsilon> <: TyPrim p" by auto
  then show ?case by (cases p) (auto simp: subty_prim_iff intro: SubtyObject SubtySized)
qed (auto dest!: wf_list_sub subty_structured_inv)

lemma tuple_has_values: "\<turnstile> VTuple vs : Ty (inst \<eta> \<sigma>) \<Longrightarrow> has_values \<Sigma> TupleKind \<sigma>"
proof (induction \<sigma>)
  case (TyUnion \<sigma> \<tau>)
  then show ?case by (auto dest: wf_val_union)
next
  case (TyPrim p)
  from wf_tuple_sub[OF TyPrim.prems] obtain \<upsilon>s where "\<Sigma> \<turnstile> TyTuple \<upsilon>s <: TyPrim p" by auto
  then show ?case by (cases p) (auto simp: subty_prim_iff intro: SubtyObject SubtySized)
qed (auto dest!: wf_tuple_sub subty_structured_inv)

lemma dict_has_values: "\<turnstile> VDict \<delta> : Ty (inst \<eta> \<sigma>) \<Longrightarrow> has_dict_values \<Sigma> \<sigma>"
proof (induction \<sigma>)
  case (TyUnion \<sigma> \<tau>)
  then show ?case by (auto dest: wf_val_union)
next
  case (TyPrim p)
  from wf_dict_sub[OF TyPrim.prems] obtain \<upsilon> where "\<Sigma> \<turnstile> TyDict \<upsilon> <: TyPrim p" by auto
  then show ?case by (cases p) (auto simp: subty_prim_iff intro: SubtyObject SubtySized)
qed (auto dest!: wf_dict_sub subty_structured_inv)

lemma range_has_values: "\<turnstile> VObject range_class xvs : Ty (inst \<eta> \<sigma>) \<Longrightarrow> has_values \<Sigma> RangeKind \<sigma>"
proof (induction \<sigma>)
  case (TyUnion \<sigma> \<tau>)
  then show ?case by (auto dest: wf_val_union)
next
  case (TyClass D \<sigma>s)
  have range: "range_class |\<in>| fmdom \<Sigma>" using range_lookup by (simp add: predefined_classes_def fmlookup_dom_iff)
  from subty_class_class(1)[OF wf_class_table wf_range_sub[OF TyClass.prems, simplified] refl refl range]
  have "D \<in> set (ancestors \<Sigma> range_class)"
    and "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> range_class [] D) (map (inst \<eta>) \<sigma>s)"
    by auto
  then have "D = range_class" and "\<sigma>s = []"
    by (auto simp: ancestors_def range_ancestors instantiated_ancestor_def dest: list_all2_lengthD)
  then show ?case by (simp add: SubtyRefl)
qed (auto dest!: wf_range_sub subty_structured_inv)

lemma float_has_values: "\<turnstile> VLit (LitFloat x) : Ty (inst \<eta> \<sigma>) \<Longrightarrow> has_float_values \<Sigma> \<sigma>"
proof (induction \<sigma>)
  case (TyUnion \<sigma> \<tau>)
  then show ?case by (auto dest: wf_val_union)
next
  case (TyPrim p)
  have "\<not> \<Sigma> \<turnstile> TyLiteral (LitFloat x) <: TyPrim Sized" using subty_sized_inv(1)[OF _ refl] by fastforce
  with wf_lit_sub[OF TyPrim.prems] show ?case
    by (cases p) (auto simp: subty_prim_iff intro: SubtyObject SubtyRefl)
next
  case (TyLiteral l)
  then show ?case by (cases l) (auto dest!: wf_lit_sub subty_literal_inv')
qed (auto dest!: wf_lit_sub subty_structured_inv)

subsection \<open>Literals\<close>

(* Literals other than floats which compare equal: the same literal *)
lemma eq_lit_same: "\<lbrakk> eq_lit l l' = Val True ; \<forall>x. l \<noteq> LitFloat x ; \<forall>x. l' \<noteq> LitFloat x \<rbrakk> \<Longrightarrow> l = l'"
  by (cases l; cases l') auto

lemma eq_lit_float: "eq_lit (LitFloat x) l' = Val True \<Longrightarrow> is_number (VLit l')"
  by (cases l') auto

subsection \<open>Resolution of the class of a constructor pattern\<close>

lemma lookup_root:
  "lookup \<Gamma> q = Some \<theta> \<Longrightarrow> \<exists>\<theta>'. fmlookup \<Gamma> (root q) = Some \<theta>' \<and> (\<theta>' = \<theta> \<or> (\<exists>q' \<Gamma>'. \<theta>' = ModChecked q' \<Gamma>'))"
  by (induction q arbitrary: \<theta>) (auto split: option.splits cxt_entry.splits)

(* Class named by a constructor pattern checked in \<Gamma>, as resolved in an environment typed by \<Gamma> *)
lemma pattern_class_value:
  assumes env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and cls: "check_pattern_class \<Gamma> q = Ok C"
  shows "\<exists>u. fmlookup \<rho> (root q) = Some u \<and> u \<noteq> VUnbound" and "resolve \<rho> q = Some (VClass C)"
    and "C \<noteq> range_class"
proof -
  from cls have look: "lookup \<Gamma> q = Some (Type C)"
    by (auto simp: check_pattern_class_def resolve_name_def split: option.splits cxt_entry.splits if_splits)
  from cls show "C \<noteq> range_class"
    by (auto simp: check_pattern_class_def split: option.splits cxt_entry.splits if_splits)
  from wf_env_resolve[OF env look] obtain v where "resolve \<rho> q = Some v" and "\<turnstile> v : Type C" by auto
  then show "resolve \<rho> q = Some (VClass C)" using wf_type_entry by simp
  from lookup_root[OF look] obtain \<theta>' where root: "fmlookup \<Gamma> (root q) = Some \<theta>'"
    and \<theta>': "\<theta>' = Type C \<or> (\<exists>q' \<Gamma>'. \<theta>' = ModChecked q' \<Gamma>')"
    by blast
  then have "\<theta>' \<noteq> TypeVar" by auto
  from wf_env_lookup[OF env root this] obtain u where "fmlookup \<rho> (root q) = Some u" and "\<turnstile> u : inst_entry \<eta> \<theta>'"
    by blast
  with \<theta>' show "\<exists>u. fmlookup \<rho> (root q) = Some u \<and> u \<noteq> VUnbound"
    by (auto dest!: wf_type_entry wf_mod_checked)
qed

end


subsection \<open>Bindings of sub-patterns\<close>

lemma distinct_concat_nth:
  "\<lbrakk> distinct (concat xss) ; i < length xss ; j < length xss ; i \<noteq> j \<rbrakk> \<Longrightarrow> set (xss ! i) \<inter> set (xss ! j) = {}"
proof (induction xss arbitrary: i j)
  case (Cons xs xss)
  then show ?case by (cases i; cases j) (auto dest!: nth_mem)
qed simp

lemma foldr_fmadd_dom': "fmdom' (foldr fmadd \<Delta>s \<Delta>) = fmdom' \<Delta> \<union> \<Union> (fmdom' ` set \<Delta>s)"
  by (induction \<Delta>s) auto

lemma fold_fmadd_lookup_notin: "x \<notin> \<Union> (fmdom' ` set \<Delta>s) \<Longrightarrow> fmlookup (fold fmadd \<Delta>s \<Delta>) x = fmlookup \<Delta> x"
  by (induction \<Delta>s arbitrary: \<Delta>) (auto simp: fmdom'_alt_def fmlookup_dom_iff)

(* Variable in the domain of one map of a list only: in none of the others *)
lemma notin_others:
  "\<lbrakk> \<forall>j < Suc (length \<Delta>s). j \<noteq> 0 \<longrightarrow> x \<notin> fmdom' ((\<Delta>' # \<Delta>s) ! j) \<rbrakk> \<Longrightarrow> x \<notin> \<Union> (fmdom' ` set \<Delta>s)"
proof
  assume all: "\<forall>j < Suc (length \<Delta>s). j \<noteq> 0 \<longrightarrow> x \<notin> fmdom' ((\<Delta>' # \<Delta>s) ! j)" and "x \<in> \<Union> (fmdom' ` set \<Delta>s)"
  then obtain i where "i < length \<Delta>s" and "x \<in> fmdom' (\<Delta>s ! i)" by (auto simp: in_set_conv_nth)
  with all[rule_format, of "Suc i"] show False by simp
qed

(* Lookup in a fold of maps, at a variable in the domain of one of them only *)
lemma fold_fmadd_lookup_nth:
  "\<lbrakk> i < length \<Delta>s ; x \<in> fmdom' (\<Delta>s ! i) ; \<forall>j < length \<Delta>s. j \<noteq> i \<longrightarrow> x \<notin> fmdom' (\<Delta>s ! j) ; x \<notin> fmdom' \<Delta> \<rbrakk>
  \<Longrightarrow> fmlookup (fold fmadd \<Delta>s \<Delta>) x = fmlookup (\<Delta>s ! i) x"
proof (induction \<Delta>s arbitrary: i \<Delta>)
  case (Cons \<Delta>' \<Delta>s)
  show ?case
  proof (cases i)
    case 0
    with Cons.prems have "x \<notin> \<Union> (fmdom' ` set \<Delta>s)" by (intro notin_others) simp
    with Cons.prems 0 show ?thesis by (simp add: fold_fmadd_lookup_notin fmdom'_alt_def)
  next
    case (Suc i')
    with Cons.prems have "x \<notin> fmdom' \<Delta>'" by fastforce
    with Cons.prems Suc show ?thesis by (auto intro!: Cons.IH simp: fmdom'_alt_def)
  qed
qed simp

(* Bindings of sub-patterns from the checks of each of them *)
lemma pattern_bindings_Ok:
  "pattern_bindings ms = Ok \<Delta> \<Longrightarrow> \<exists>\<Delta>s. list_all2 (\<lambda>m \<Delta>'. m = Ok \<Delta>') ms \<Delta>s \<and> \<Delta> = fold fmadd \<Delta>s fmempty"
  by (auto simp: pattern_bindings_def bind_sum_Ok dest!: those_sum_Ok)

(* Bindings of a pattern at the disjuncts of a type, from the bindings at each disjunct *)
lemma bindings_at_Ok:
  assumes "bindings_at \<Sigma> \<Gamma> p ms = Ok \<Delta>"
  obtains \<Delta>s where "list_all2 (\<lambda>m \<Delta>'. case m of Some m' \<Rightarrow> m' = Ok \<Delta>'
                               | None \<Rightarrow> \<Delta>' = fmconst (binds p) (TyPrim Never)
                                   \<and> (\<forall>x \<in> binds p. fmlookup \<Gamma> x = Some Unbound)) ms \<Delta>s"
    and "\<Delta> = fmmap_keys (\<lambda>x _. joins \<Sigma> (map (\<lambda>\<Delta>'. the (fmlookup \<Delta>' x)) \<Delta>s)) (hd \<Delta>s)"
proof -
  let ?g = "\<lambda>m. case m of
                  Some m' \<Rightarrow> m'
                | None \<Rightarrow> do {
                    all_sum (map (check_unbound \<Gamma>) (sorted_list_of_set (binds p)));
                    Ok (fmconst (binds p) (TyPrim Never))
                  }"
  from assms obtain \<Delta>s where \<Delta>s: "those_sum (map ?g ms) = Ok \<Delta>s"
    and \<Delta>: "\<Delta> = fmmap_keys (\<lambda>x _. joins \<Sigma> (map (\<lambda>\<Delta>'. the (fmlookup \<Delta>' x)) \<Delta>s)) (hd \<Delta>s)"
    unfolding bindings_at_def bind_sum_Ok by auto
  have "case m of Some m' \<Rightarrow> m' = Ok \<Delta>'
        | None \<Rightarrow> \<Delta>' = fmconst (binds p) (TyPrim Never) \<and> (\<forall>x \<in> binds p. fmlookup \<Gamma> x = Some Unbound)"
    if "?g m = Ok \<Delta>'" for m \<Delta>'
    using that finite_binds_pat[of p]
    by (auto simp: bind_sum_Ok intro: check_unbound_Ok dest!: all_sum_map_Ok[where x = "x" for x] split: option.splits)
  with those_sum_map_Ok[OF \<Delta>s] \<Delta> that show thesis by (blast intro: list_all2_mono)
qed

subsection \<open>Outcomes of matching sequences of patterns\<close>

lemma foldr_match_Match:
  "foldr seq_compose_match ms (Match fmempty) = Match \<rho>'
  \<Longrightarrow> \<exists>\<rho>s. list_all2 (\<lambda>m \<rho>. m = Match \<rho>) ms \<rho>s \<and> \<rho>' = foldr fmadd \<rho>s fmempty"
proof (induction ms arbitrary: \<rho>')
  case (Cons m ms)
  from Cons.prems obtain \<rho>\<^sub>1 \<rho>\<^sub>2 where "m = Match \<rho>\<^sub>1" and rest: "foldr seq_compose_match ms (Match fmempty) = Match \<rho>\<^sub>2"
    and "\<rho>' = \<rho>\<^sub>1 ++\<^sub>f \<rho>\<^sub>2"
    by (cases m; cases "foldr seq_compose_match ms (Match fmempty)") auto
  from Cons.IH[OF rest] obtain \<rho>s where "list_all2 (\<lambda>m \<rho>. m = Match \<rho>) ms \<rho>s" and "\<rho>\<^sub>2 = foldr fmadd \<rho>s fmempty"
    by blast
  with \<open>m = Match \<rho>\<^sub>1\<close> \<open>\<rho>' = \<rho>\<^sub>1 ++\<^sub>f \<rho>\<^sub>2\<close> show ?case by (auto intro!: exI[of _ "\<rho>\<^sub>1 # \<rho>s"])
qed simp

lemma foldr_match_NoMatch: "foldr seq_compose_match ms (Match fmempty) = NoMatch \<Longrightarrow> NoMatch \<in> set ms"
proof (induction ms)
  case (Cons m ms)
  then show ?case by (cases m; cases "foldr seq_compose_match ms (Match fmempty)") auto
qed simp

lemma foldr_match_Aborts:
  "foldr seq_compose_match ms (Match fmempty) = MatchAborts \<kappa> \<Longrightarrow> MatchAborts \<kappa> \<in> set ms"
proof (induction ms)
  case (Cons m ms)
  then show ?case by (cases m; cases "foldr seq_compose_match ms (Match fmempty)") auto
qed simp

subsection \<open>Fields of a class at an ancestor\<close>

lemma map_fst_instantiate: "map fst (instantiate (fields \<Sigma> C) \<tau>s) = field_names \<Sigma> C"
  by (cases "fields \<Sigma> C") (auto simp: field_names_def comp_def case_prod_beta)

(* Fields of a class: those of each ancestor, at the type arguments of the ancestor, first *)
lemma instantiate_fields_upto:
  assumes "wf_class_table \<Sigma>"
  shows "\<lbrakk> D |\<in>| fmdom \<Sigma> ; inherits_within n \<Sigma> D ; (C, \<sigma>s) \<in> set (instantiated_ancestors_upto n \<Sigma> D \<upsilon>s) \<rbrakk>
    \<Longrightarrow> \<exists>rest. instantiate (fields \<Sigma> D) \<upsilon>s = instantiate (fields \<Sigma> C) \<sigma>s @ rest"
proof (induction n arbitrary: D \<upsilon>s)
  case (Suc n)
  show ?case
  proof (cases "(C, \<sigma>s) = (D, \<upsilon>s)")
    case True
    then show ?thesis by auto
  next
    case False
    with Suc.prems obtain E \<rho>s where base: "base \<Sigma> D = Some (E, \<rho>s)"
      and mem: "(C, \<sigma>s) \<in> set (instantiated_ancestors_upto n \<Sigma> E (map (subst \<upsilon>s (type_params \<Sigma> D)) \<rho>s))"
      by (auto split: option.splits)
    from wf_class_table_baseD[OF assms Suc.prems(1) base] have E: "E |\<in>| fmdom \<Sigma>" by simp
    from Suc.prems(2) base have "inherits_within n \<Sigma> E" by simp
    from Suc.IH[OF E this mem] obtain rest
      where "instantiate (fields \<Sigma> E) (map (subst \<upsilon>s (type_params \<Sigma> D)) \<rho>s) = instantiate (fields \<Sigma> C) \<sigma>s @ rest"
      by blast
    with instantiate_fields_base[OF assms Suc.prems(1) base] show ?thesis by auto
  qed
qed simp

lemma instantiate_fields_ancestor:
  assumes "wf_class_table \<Sigma>" and "D |\<in>| fmdom \<Sigma>" and "C \<in> set (ancestors \<Sigma> D)"
  shows "\<exists>rest. instantiate (fields \<Sigma> D) \<upsilon>s = instantiate (fields \<Sigma> C) (instantiated_ancestor \<Sigma> D \<upsilon>s C) @ rest"
  using instantiate_fields_upto[OF assms(1, 2) wf_class_table_inherits[OF assms(1, 2)]
      instantiated_ancestor_mem[OF assms, of \<upsilon>s, unfolded instantiated_ancestors_def]] .

subsection \<open>Meets with a literal, float or class type\<close>

lemma meet_literal:
  "\<not> is_union \<tau> \<Longrightarrow> meet \<Sigma> (TyLiteral l) \<tau>
    = (if \<Sigma> \<turnstile> TyLiteral l <: \<tau> then TyLiteral l else if \<Sigma> \<turnstile> \<tau> <: TyLiteral l then \<tau> else TyPrim Never)"
  by (cases \<tau>) auto

lemma meet_float:
  "\<not> is_union \<tau> \<Longrightarrow> meet \<Sigma> (TyPrim float) \<tau>
    = (if \<Sigma> \<turnstile> TyPrim float <: \<tau> then TyPrim float else if \<Sigma> \<turnstile> \<tau> <: TyPrim float then \<tau> else TyPrim Never)"
  by (cases \<tau>) auto

lemma meet_class:
  "\<not> is_union \<sigma> \<Longrightarrow> meet \<Sigma> \<sigma> (TyClass C \<tau>s)
    = (if \<Sigma> \<turnstile> \<sigma> <: TyClass C \<tau>s then \<sigma> else if \<Sigma> \<turnstile> TyClass C \<tau>s <: \<sigma> then TyClass C \<tau>s else TyPrim Never)"
  by (cases \<sigma>) auto

context evaluation
begin

subsection \<open>Matched and remaining types at a disjunct\<close>

lemma matched_as_lift:
  "\<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; check_pat \<Sigma> \<Gamma> p \<tau> = Ok \<Delta> ; wf_cxt \<Sigma> \<Gamma> ; wf_ty \<Sigma> \<tau> ; wf_inst \<Sigma> \<eta>
   ; \<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<sigma> p)) \<rbrakk>
  \<Longrightarrow> \<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> p))"
proof (induction \<tau> arbitrary: \<Delta>)
  case (TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2)
  from check_pat_union(1)[OF TyUnion.prems(2) refl] obtain \<Delta>\<^sub>1 \<Delta>\<^sub>2 where c\<^sub>1: "check_pat \<Sigma> \<Gamma> p \<sigma>\<^sub>1 = Ok \<Delta>\<^sub>1"
    and c\<^sub>2: "check_pat \<Sigma> \<Gamma> p \<sigma>\<^sub>2 = Ok \<Delta>\<^sub>2"
    by blast
  let ?m\<^sub>1 = "matched_as \<Sigma> \<Gamma> \<sigma>\<^sub>1 p" and ?m\<^sub>2 = "matched_as \<Sigma> \<Gamma> \<sigma>\<^sub>2 p"
  have wf\<^sub>1: "wf_ty \<Sigma> ?m\<^sub>1" and wf\<^sub>2: "wf_ty \<Sigma> ?m\<^sub>2"
    using matched_as_wf[OF wf_class_table TyUnion.prems(3) _ c\<^sub>1] matched_as_wf[OF wf_class_table TyUnion.prems(3) _ c\<^sub>2]
      TyUnion.prems(4)
    by auto
  have "\<turnstile> v : Ty (inst \<eta> ?m\<^sub>1) \<or> \<turnstile> v : Ty (inst \<eta> ?m\<^sub>2)"
    using TyUnion.prems(1, 6) TyUnion.IH(1)[OF _ c\<^sub>1] TyUnion.IH(2)[OF _ c\<^sub>2] TyUnion.prems(3-5) by auto
  moreover have "\<Sigma> \<turnstile> inst \<eta> ?m\<^sub>1 <: inst \<eta> (?m\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> ?m\<^sub>2)" and "\<Sigma> \<turnstile> inst \<eta> ?m\<^sub>2 <: inst \<eta> (?m\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> ?m\<^sub>2)"
    using inst_subty[OF wf_class_table join_upper(1)] inst_subty[OF wf_class_table join_upper(2)]
      wf\<^sub>1 wf\<^sub>2 wf_join[OF wf\<^sub>1 wf\<^sub>2]
    by blast+
  ultimately show ?case using inst_wf[OF TyUnion.prems(5) wf_join[OF wf\<^sub>1 wf\<^sub>2]] by (auto intro: ValSub)
qed auto

lemma remaining_lift:
  "\<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; wf_ty \<Sigma> \<tau> ; wf_inst \<Sigma> \<eta> ; \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> p)) \<rbrakk>
  \<Longrightarrow> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> p))"
proof (induction \<tau>)
  case (TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2)
  let ?r\<^sub>1 = "remaining \<Sigma> \<Gamma> \<sigma>\<^sub>1 p" and ?r\<^sub>2 = "remaining \<Sigma> \<Gamma> \<sigma>\<^sub>2 p"
  have wf\<^sub>1: "wf_ty \<Sigma> ?r\<^sub>1" and wf\<^sub>2: "wf_ty \<Sigma> ?r\<^sub>2" using remaining_wf TyUnion.prems(2) by auto
  have "\<turnstile> v : Ty (inst \<eta> ?r\<^sub>1) \<or> \<turnstile> v : Ty (inst \<eta> ?r\<^sub>2)"
    using TyUnion.prems TyUnion.IH by auto
  moreover have "\<Sigma> \<turnstile> inst \<eta> ?r\<^sub>1 <: inst \<eta> (?r\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> ?r\<^sub>2)" and "\<Sigma> \<turnstile> inst \<eta> ?r\<^sub>2 <: inst \<eta> (?r\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> ?r\<^sub>2)"
    using inst_subty[OF wf_class_table join_upper(1)] inst_subty[OF wf_class_table join_upper(2)]
      wf\<^sub>1 wf\<^sub>2 wf_join[OF wf\<^sub>1 wf\<^sub>2]
    by blast+
  ultimately show ?case using inst_wf[OF TyUnion.prems(3) wf_join[OF wf\<^sub>1 wf\<^sub>2]] by (auto intro: ValSub)
qed auto

subsection \<open>Canonical forms of literals\<close>

lemma wf_val_literal: "\<turnstile> v : Ty (TyLiteral l) \<Longrightarrow> v = VLit l"
proof -
  assume "\<turnstile> v : Ty (TyLiteral l)"
  from wf_val_intro(1)[OF this] obtain \<sigma> where intro: "intro_typed v \<sigma>" and "\<Sigma> \<turnstile> \<sigma> <: TyLiteral l" by blast
  with intro_typed_nonunion[OF intro] subty_literal_inv' have "\<sigma> = TyLiteral l" by blast
  with intro show "v = VLit l" by (cases v) auto
qed

lemma wf_val_bool: "\<turnstile> v : Ty (TyPrim bool) \<Longrightarrow> \<exists>b. v = VLit (LitBool b)"
  by (erule wf_prim_lit[OF _ SubtyRefl]) (auto elim: base_type_lit.elims split: if_splits)

lemma wf_val_none: "\<turnstile> v : Ty (TyPrim NoneType) \<Longrightarrow> v = VLit LitNone"
  by (erule wf_prim_lit[OF _ SubtyRefl]) (auto elim: base_type_lit.elims split: if_splits)

subsection \<open>Values at a disjunct of another kind\<close>

lemma tuple_at_nontuple:
  assumes "\<turnstile> VTuple vs : Ty (inst \<eta> \<sigma>)" and "\<not> is_union \<sigma>" and "\<forall>\<sigma>s. \<sigma> \<noteq> TyTuple \<sigma>s"
  shows "has_values \<Sigma> ListKind \<sigma>"
proof (cases \<sigma>)
  case (TyPrim p)
  with wf_tuple_sub[OF assms(1)] obtain \<upsilon>s where "\<Sigma> \<turnstile> TyTuple \<upsilon>s <: TyPrim p" by auto
  then show ?thesis unfolding TyPrim by (cases p) (auto simp: subty_prim_iff intro: SubtyObject SubtySized)
qed (use assms in \<open>auto dest!: wf_tuple_sub subty_structured_inv\<close>)

lemma list_at_nonlist:
  assumes "\<turnstile> VList vs : Ty (inst \<eta> \<sigma>)" and "\<not> is_union \<sigma>" and "\<forall>\<sigma>'. \<sigma> \<noteq> TyList \<sigma>'"
  shows "has_values \<Sigma> TupleKind \<sigma>"
proof (cases \<sigma>)
  case (TyPrim p)
  with wf_list_sub[OF assms(1)] obtain \<upsilon> where "\<Sigma> \<turnstile> TyList \<upsilon> <: TyPrim p" by auto
  then show ?thesis unfolding TyPrim by (cases p) (auto simp: subty_prim_iff intro: SubtyObject SubtySized)
qed (use assms in \<open>auto dest!: wf_list_sub subty_structured_inv\<close>)

(* Range: an ancestor of no other class *)
lemma range_not_ancestor_upto:
  "\<lbrakk> inherits_within n \<Sigma> C ; C |\<in>| fmdom \<Sigma> ; C \<noteq> range_class
   ; range_class \<in> set (map fst (instantiated_ancestors_upto n \<Sigma> C \<tau>s)) \<rbrakk> \<Longrightarrow> False"
proof (induction n arbitrary: C \<tau>s)
  case (Suc n)
  show ?case
  proof (cases "base \<Sigma> C")
    case None
    with Suc.prems show ?thesis by simp
  next
    case (Some E\<rho>s)
    then obtain E \<rho>s where base: "base \<Sigma> C = Some (E, \<rho>s)" by (cases E\<rho>s) simp
    from wf_class_table_baseD[OF wf_class_table Suc.prems(2) base] have "E |\<in>| fmdom \<Sigma>" and "E \<noteq> range_class"
      by auto
    with Suc.prems base Suc.IH show ?thesis by auto
  qed
qed simp

lemma range_not_ancestor: "\<lbrakk> C |\<in>| fmdom \<Sigma> ; C \<noteq> range_class \<rbrakk> \<Longrightarrow> range_class \<notin> set (ancestors \<Sigma> C)"
  unfolding ancestors_def instantiated_ancestors_def
  using range_not_ancestor_upto[OF wf_class_table_inherits[OF wf_class_table]] by blast

end


subsection \<open>Ancestors of one class\<close>

(* Two ancestors of a class: one an ancestor of the other *)
lemma ancestors_comparable:
  assumes "wf_class_table \<Sigma>" and "D |\<in>| fmdom \<Sigma>" and "C \<in> set (ancestors \<Sigma> D)" and "E \<in> set (ancestors \<Sigma> D)"
  shows "C \<in> set (ancestors \<Sigma> E) \<or> E \<in> set (ancestors \<Sigma> C)"
proof -
  let ?\<upsilon>s = "map TyVar (type_params \<Sigma> D)"
  let ?L = "\<lambda>F. instantiated_ancestors \<Sigma> F (instantiated_ancestor \<Sigma> D ?\<upsilon>s F)"
  from instantiated_ancestors_suffix[OF assms(1, 2) instantiated_ancestor_mem[OF assms(1-3)]]
  obtain pre where C: "instantiated_ancestors \<Sigma> D ?\<upsilon>s = pre @ ?L C" by blast
  from instantiated_ancestors_suffix[OF assms(1, 2) instantiated_ancestor_mem[OF assms(1, 2, 4)]]
  obtain pre' where E: "instantiated_ancestors \<Sigma> D ?\<upsilon>s = pre' @ ?L E" by blast
  let ?W = "instantiated_ancestors \<Sigma> D ?\<upsilon>s"
  have 1: "?L C = drop (length pre) ?W" using C by (simp add: append_eq_conv_conj)
  have 2: "?L E = drop (length pre') ?W" using E by (simp add: append_eq_conv_conj)
  show ?thesis
  proof (cases "length pre \<le> length pre'")
    case True
    then obtain k where "length pre' = length pre + k" by (auto simp: le_iff_add)
    then have "?L E = drop k (?L C)" unfolding 1 2 by (simp add: add.commute)
    then have sub: "set (?L E) \<subseteq> set (?L C)" by (simp add: set_drop_subset)
    have "E \<in> fst ` set (?L E)"
      using ancestors_head[OF ancestors_dom[OF assms(1, 2, 4)]] ancestors_instantiated[of \<Sigma> E] by blast
    with sub have "E \<in> fst ` set (?L C)" by blast
    then show ?thesis using ancestors_instantiated[of \<Sigma> C] by blast
  next
    case False
    then have "length pre' \<le> length pre" by simp
    then obtain k where "length pre = length pre' + k" by (auto simp: le_iff_add)
    then have "?L C = drop k (?L E)" unfolding 1 2 by (simp add: add.commute)
    then have sub: "set (?L C) \<subseteq> set (?L E)" by (simp add: set_drop_subset)
    have "C \<in> fst ` set (?L C)"
      using ancestors_head[OF ancestors_dom[OF assms(1-3)]] ancestors_instantiated[of \<Sigma> C] by blast
    with sub have "C \<in> fst ` set (?L E)" by blast
    then show ?thesis using ancestors_instantiated[of \<Sigma> E] by blast
  qed
qed

lemma type_args_of_nth:
  assumes "type_args_of \<gamma> \<alpha>s = Ok \<sigma>s" and "i < length \<alpha>s"
  shows "fmlookup \<gamma> (\<alpha>s ! i) = Some (\<sigma>s ! i)"
proof -
  from assms(1) have "list_all2 (\<lambda>\<alpha> \<sigma>. or_else (NoTypeArgument \<alpha>) (fmlookup \<gamma> \<alpha>) = Ok \<sigma>) \<alpha>s \<sigma>s"
    unfolding type_args_of_def by (rule those_sum_map_Ok)
  with assms(2) have "or_else (NoTypeArgument (\<alpha>s ! i)) (fmlookup \<gamma> (\<alpha>s ! i)) = Ok (\<sigma>s ! i)"
    by (simp add: list_all2_conv_all_nth)
  then show ?thesis by (auto simp: or_else_def split: option.splits)
qed

(* Type arguments with pairwise equivalent substitutions at distinct type parameters: pairwise equivalent *)
lemma equiv_args_of_vars:
  assumes "distinct \<alpha>s" and "length \<tau>s = length \<alpha>s" and "length \<tau>s' = length \<alpha>s"
    and "\<forall>\<alpha> \<in> set \<alpha>s. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyVar \<alpha>) \<approx> subst \<tau>s' \<alpha>s (TyVar \<alpha>)"
  shows "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) \<tau>s \<tau>s'"
proof -
  have "\<Sigma> \<turnstile> \<tau>s ! i \<approx> \<tau>s' ! i" if i: "i < length \<alpha>s" for i
  proof -
    from assms(4) i have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyVar (\<alpha>s ! i)) \<approx> subst \<tau>s' \<alpha>s (TyVar (\<alpha>s ! i))" by simp
    then show ?thesis
      using i assms(2, 3)
      by (simp add: map_of_zip_nth[OF assms(2)[symmetric] assms(1)] map_of_zip_nth[OF assms(3)[symmetric] assms(1)])
  qed
  then show ?thesis using assms(2, 3) by (simp add: list_all2_conv_all_nth)
qed

context evaluation
begin

subsection \<open>Objects matched by constructor patterns\<close>

(* Instance of class C at a type other than a union, comparable with the type *)
lemma instance_at_comparable:
  assumes "instance_at \<Sigma> C \<sigma> = Instance \<sigma>s" and "\<not> is_union \<sigma>" and "wf_ty \<Sigma> \<sigma>" and "C |\<in>| fmdom \<Sigma>"
  shows "\<Sigma> \<turnstile> \<sigma> <: TyClass C \<sigma>s \<or> \<Sigma> \<turnstile> TyClass C \<sigma>s <: \<sigma>"
proof (cases "instance_above \<Sigma> C \<sigma>")
  case (Instance \<sigma>s')
  with assms(1) have \<sigma>s: "\<sigma>s' = \<sigma>s" by (simp add: instance_at_def)
  show ?thesis
  proof (cases \<sigma>)
    case (TyClass E \<sigma>s\<^sub>E)
    with Instance \<sigma>s have "C \<in> set (ancestors \<Sigma> E)" and "\<sigma>s = instantiated_ancestor \<Sigma> E \<sigma>s\<^sub>E C"
      by (auto split: if_splits)
    with subty_ancestor[OF wf_class_table _ this(1), of \<sigma>s\<^sub>E] assms(3) show ?thesis unfolding TyClass by auto
  next
    case (TyPrim p)
    with Instance show ?thesis by (cases p) (auto split: if_splits intro: SubtyNever)
  qed (use Instance in auto)
next
  case NoInstance
  with assms(1) have below: "instance_below \<Sigma> C \<sigma> = Instance \<sigma>s" by (simp add: instance_at_def)
  show ?thesis
  proof (cases \<sigma>)
    case (TyClass E \<sigma>s\<^sub>E)
    with below have E: "E \<in> set (ancestors \<Sigma> C)"
      and equiv: "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> C \<sigma>s E) \<sigma>s\<^sub>E"
      by (auto simp: Let_def split: if_splits arg_match.splits sum.splits)
    have wf\<sigma>s: "wf_ty \<Sigma> (TyClass C \<sigma>s)"
      using instance_at_class_wf[OF wf_class_table assms(3, 1, 4)] .
    from instantiated_ancestor_wf[OF wf_class_table wf\<sigma>s E]
    have wf_anc: "wf_ty \<Sigma> (TyClass E (instantiated_ancestor \<Sigma> C \<sigma>s E))" by simp
    have "\<Sigma> \<turnstile> TyClass E (instantiated_ancestor \<Sigma> C \<sigma>s E) <: TyClass E \<sigma>s\<^sub>E"
      using equiv by (auto intro!: SubtyClass simp: subtys_list_all2 list_all2_conv_all_nth)
    from subty_trans[OF wf_class_table wf\<sigma>s wf_anc subty_ancestor[OF wf_class_table assms(4) E] this]
    show ?thesis unfolding TyClass by simp
  next
    case (TyPrim p)
    with below show ?thesis by (cases p) (auto split: if_splits intro: SubtyObject)
  qed (use below in auto)
next
  case Undetermined
  with assms(1) show ?thesis by (simp add: instance_at_def)
qed

(* Class type below the instance of C at a type other than a union, below the instance *)
lemma instance_at_sub:
  assumes inst: "instance_at \<Sigma> C \<sigma> = Instance \<sigma>s" and nonunion: "\<not> is_union \<sigma>" and wf: "wf_ty \<Sigma> \<sigma>"
    and C: "C |\<in>| fmdom \<Sigma>" and sub: "\<Sigma> \<turnstile> TyClass D \<upsilon>s <: inst \<eta> \<sigma>" and wfD: "wf_ty \<Sigma> (TyClass D \<upsilon>s)"
    and anc: "C \<in> set (ancestors \<Sigma> D)"
  shows "\<Sigma> \<turnstile> TyClass D \<upsilon>s <: inst \<eta> (TyClass C \<sigma>s)"
proof -
  let ?\<alpha>s = "type_params \<Sigma> C" and ?\<tau>s' = "instantiated_ancestor \<Sigma> D \<upsilon>s C"
  have D: "D |\<in>| fmdom \<Sigma>" using wfD by simp
  have wf\<sigma>s: "wf_ty \<Sigma> (TyClass C \<sigma>s)" using instance_at_class_wf[OF wf_class_table wf inst C] .
  then have len\<sigma>s: "length \<sigma>s = length ?\<alpha>s" by simp
  from instantiated_ancestor_wf[OF wf_class_table wfD anc] have wf\<tau>s': "wf_ty \<Sigma> (TyClass C ?\<tau>s')" by simp
  then have len\<tau>s': "length ?\<tau>s' = length ?\<alpha>s" by simp
  have distinct: "distinct ?\<alpha>s" using wf_class_table_distinct_params[OF wf_class_table C] .
  have "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) ?\<tau>s' (map (inst \<eta>) \<sigma>s)"
  proof (cases "instance_above \<Sigma> C \<sigma>")
    case (Instance \<sigma>s')
    with inst have \<sigma>s': "\<sigma>s' = \<sigma>s" by (simp add: instance_at_def)
    show ?thesis
    proof (cases \<sigma>)
      case (TyClass E \<sigma>s\<^sub>E)
      let ?\<beta>s = "type_params \<Sigma> E"
      from Instance \<sigma>s' have CE: "C \<in> set (ancestors \<Sigma> E)" and \<sigma>s: "\<sigma>s = instantiated_ancestor \<Sigma> E \<sigma>s\<^sub>E C"
        unfolding TyClass by (auto split: if_splits)
      have E: "E |\<in>| fmdom \<Sigma>" and len\<^sub>E: "length \<sigma>s\<^sub>E = length ?\<beta>s" using wf unfolding TyClass by auto
      from subty_class_class(1)[OF wf_class_table sub[unfolded TyClass, simplified] refl refl D]
      have ED: "E \<in> set (ancestors \<Sigma> D)"
        and equiv: "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> D \<upsilon>s E) (map (inst \<eta>) \<sigma>s\<^sub>E)"
        by auto
      from instantiated_ancestor_wf[OF wf_class_table wfD ED]
      have len\<^sub>D: "length (instantiated_ancestor \<Sigma> D \<upsilon>s E) = length ?\<beta>s" by simp
      have "?\<tau>s' = instantiated_ancestor \<Sigma> E (instantiated_ancestor \<Sigma> D \<upsilon>s E) C"
        using instantiated_ancestor_compose(2)[OF wf_class_table D ED CE] .
      also have "\<dots> = map (subst (instantiated_ancestor \<Sigma> D \<upsilon>s E) ?\<beta>s)
                       (instantiated_ancestor \<Sigma> E (map TyVar ?\<beta>s) C)"
        using instantiated_ancestor_params[OF wf_class_table E len\<^sub>D CE] .
      finally have \<tau>s': "?\<tau>s' = map (subst (instantiated_ancestor \<Sigma> D \<upsilon>s E) ?\<beta>s)
                                (instantiated_ancestor \<Sigma> E (map TyVar ?\<beta>s) C)" .
      have wfE: "wf_ty \<Sigma> (TyClass E \<sigma>s\<^sub>E)" using wf unfolding TyClass .
      have "map (inst \<eta>) \<sigma>s = instantiated_ancestor \<Sigma> E (map (inst \<eta>) \<sigma>s\<^sub>E) C"
        unfolding \<sigma>s by (simp add: instantiated_ancestor_inst[OF wf_class_table wfE CE])
      also have "\<dots> = map (subst (map (inst \<eta>) \<sigma>s\<^sub>E) ?\<beta>s) (instantiated_ancestor \<Sigma> E (map TyVar ?\<beta>s) C)"
        using instantiated_ancestor_params[OF wf_class_table E _ CE, of "map (inst \<eta>) \<sigma>s\<^sub>E"] len\<^sub>E by simp
      finally show ?thesis
        unfolding \<tau>s' using subst_equiv[OF equiv] by (auto simp: list_all2_conv_all_nth)
    next
      case (TyPrim p)
      with Instance sub show ?thesis by (cases p) (auto split: if_splits dest: subty_never_inv)
    qed (use Instance in auto)
  next
    case NoInstance
    with inst have below: "instance_below \<Sigma> C \<sigma> = Instance \<sigma>s" by (simp add: instance_at_def)
    show ?thesis
    proof (cases \<sigma>)
      case (TyClass E \<sigma>s\<^sub>E)
      let ?\<rho>s = "instantiated_ancestor \<Sigma> C (map TyVar ?\<alpha>s) E"
      from below obtain \<gamma> where E: "E \<in> set (ancestors \<Sigma> C)" and m: "match_args_seq ?\<rho>s \<sigma>s\<^sub>E = Matched \<gamma>"
        and args: "Subtyping.type_args_of \<gamma> ?\<alpha>s = Ok \<sigma>s"
        unfolding TyClass by (auto simp: Let_def split: if_splits arg_match.splits sum.splits)
      from subty_class_class(1)[OF wf_class_table sub[unfolded TyClass, simplified] refl refl D]
      have ED: "E \<in> set (ancestors \<Sigma> D)"
        and equiv: "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> D \<upsilon>s E) (map (inst \<eta>) \<sigma>s\<^sub>E)"
        by auto
      have "instantiated_ancestor \<Sigma> D \<upsilon>s E = instantiated_ancestor \<Sigma> C ?\<tau>s' E"
        using instantiated_ancestor_compose(2)[OF wf_class_table D anc E] .
      also have "\<dots> = map (subst ?\<tau>s' ?\<alpha>s) ?\<rho>s" using instantiated_ancestor_params[OF wf_class_table C len\<tau>s' E] .
      finally have equiv': "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst ?\<tau>s' ?\<alpha>s \<rho> \<approx> inst \<eta> \<sigma>) ?\<rho>s \<sigma>s\<^sub>E"
        using equiv by (simp add: list_all2_map1 list_all2_map2)
      have wf\<rho>s: "\<forall>\<rho> \<in> set ?\<rho>s. wf_ty \<Sigma> \<rho>"
        using instantiated_ancestor_wf[OF wf_class_table _ E, of "map TyVar ?\<alpha>s"] C by auto
      have wf\<sigma>s\<^sub>E: "\<forall>\<sigma>' \<in> set \<sigma>s\<^sub>E. wf_ty \<Sigma> \<sigma>'" using wf unfolding TyClass by simp
      have "\<Sigma> \<turnstile> subst ?\<tau>s' ?\<alpha>s (TyVar \<alpha>) \<approx> subst (map (inst \<eta>) \<sigma>s) ?\<alpha>s (TyVar \<alpha>)" if \<alpha>: "\<alpha> \<in> set ?\<alpha>s" for \<alpha>
      proof -
        from \<alpha> obtain i where i: "i < length ?\<alpha>s" and \<alpha>i: "\<alpha> = ?\<alpha>s ! i" by (auto simp: in_set_conv_nth)
        from type_args_of_nth[OF args i] have look: "fmlookup \<gamma> \<alpha> = Some (\<sigma>s ! i)" by (simp add: \<alpha>i)
        from match_args_seq_Matched[OF m look] obtain j \<gamma>' where j: "j < length ?\<rho>s"
          and mj: "match_args (?\<rho>s ! j) (\<sigma>s\<^sub>E ! j) = Matched \<gamma>'" and lookj: "fmlookup \<gamma>' \<alpha> = Some (\<sigma>s ! i)"
          and len: "length ?\<rho>s = length \<sigma>s\<^sub>E"
          by blast
        have eq: "\<Sigma> \<turnstile> subst ?\<tau>s' ?\<alpha>s (?\<rho>s ! j) \<approx> inst \<eta> (\<sigma>s\<^sub>E ! j)" using equiv' j by (auto simp: list_all2_conv_all_nth)
        obtain \<beta>s where e1: "inst \<eta> (\<sigma>s\<^sub>E ! j) = subst (map \<eta> \<beta>s) \<beta>s (\<sigma>s\<^sub>E ! j)"
          and e2: "inst \<eta> (\<sigma>s ! i) = subst (map \<eta> \<beta>s) \<beta>s (\<sigma>s ! i)"
          by (rule inst_as_subst_pair)
        from match_args_unique[OF wf_class_table mj lookj _ _ eq[unfolded e1]] wf\<rho>s wf\<sigma>s\<^sub>E j len
        have "\<Sigma> \<turnstile> subst ?\<tau>s' ?\<alpha>s (TyVar \<alpha>) \<approx> inst \<eta> (\<sigma>s ! i)" unfolding e2 by auto
        moreover have "subst (map (inst \<eta>) \<sigma>s) ?\<alpha>s (TyVar \<alpha>) = inst \<eta> (\<sigma>s ! i)"
          using i len\<sigma>s distinct by (simp add: \<alpha>i map_of_zip_nth)
        ultimately show ?thesis by simp
      qed
      then show ?thesis using equiv_args_of_vars[OF distinct len\<tau>s'] len\<sigma>s by simp
    next
      case (TyPrim p)
      with below have "p = object" by (cases p) (auto split: if_splits)
      with below TyPrim have "\<sigma>s = []" and "type_params \<Sigma> C = []" by (auto split: if_splits)
      with len\<tau>s' show ?thesis by simp
    qed (use below in auto)
  next
    case Undetermined
    with inst show ?thesis by (simp add: instance_at_def)
  qed
  then have "\<Sigma> \<turnstile> TyClass C ?\<tau>s' <: TyClass C (map (inst \<eta>) \<sigma>s)"
    by (auto intro!: SubtyClass simp: subtys_list_all2 list_all2_conv_all_nth)
  from subty_trans[OF wf_class_table wfD wf\<tau>s' subty_ancestor[OF wf_class_table D anc] this] show ?thesis by simp
qed

(* Class type below a type other than a union at which C has no instance: C not an ancestor *)
lemma instance_at_none:
  assumes none: "instance_at \<Sigma> C \<sigma> = NoInstance" and nonunion: "\<not> is_union \<sigma>" and wf: "wf_ty \<Sigma> \<sigma>"
    and C: "C |\<in>| fmdom \<Sigma>" and range: "C \<noteq> range_class" and sub: "\<Sigma> \<turnstile> TyClass D \<upsilon>s <: inst \<eta> \<sigma>"
    and wfD: "wf_ty \<Sigma> (TyClass D \<upsilon>s)" and anc: "C \<in> set (ancestors \<Sigma> D)"
  shows False
proof -
  let ?\<alpha>s = "type_params \<Sigma> C" and ?\<tau>s' = "instantiated_ancestor \<Sigma> D \<upsilon>s C"
  have D: "D |\<in>| fmdom \<Sigma>" using wfD by simp
  from none have above: "instance_above \<Sigma> C \<sigma> = NoInstance" and below: "instance_below \<Sigma> C \<sigma> = NoInstance"
    by (auto simp: instance_at_def split: instances.splits)
  show False
  proof (cases \<sigma>)
    case (TyClass E \<sigma>s\<^sub>E)
    let ?\<rho>s = "instantiated_ancestor \<Sigma> C (map TyVar ?\<alpha>s) E"
    from subty_class_class(1)[OF wf_class_table sub[unfolded TyClass, simplified] refl refl D]
    have ED: "E \<in> set (ancestors \<Sigma> D)"
      and equiv: "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> D \<upsilon>s E) (map (inst \<eta>) \<sigma>s\<^sub>E)"
      by auto
    from above have "C \<notin> set (ancestors \<Sigma> E)" unfolding TyClass by (auto split: if_splits)
    with ancestors_comparable[OF wf_class_table D anc ED] have E: "E \<in> set (ancestors \<Sigma> C)" by blast
    with below have clash: "match_args_seq ?\<rho>s \<sigma>s\<^sub>E = Clash"
      unfolding TyClass by (auto simp: Let_def split: if_splits arg_match.splits sum.splits)
    from instantiated_ancestor_wf[OF wf_class_table wfD anc] have len\<tau>s': "length ?\<tau>s' = length ?\<alpha>s" by simp
    have "instantiated_ancestor \<Sigma> D \<upsilon>s E = map (subst ?\<tau>s' ?\<alpha>s) ?\<rho>s"
      using instantiated_ancestor_compose(2)[OF wf_class_table D anc E]
        instantiated_ancestor_params[OF wf_class_table C len\<tau>s' E]
      by simp
    with equiv have equiv': "list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> subst ?\<tau>s' ?\<alpha>s \<rho> \<approx> inst \<eta> \<sigma>) ?\<rho>s \<sigma>s\<^sub>E"
      by (simp add: list_all2_map1 list_all2_map2)
    have wf\<rho>s: "\<forall>\<rho> \<in> set ?\<rho>s. wf_ty \<Sigma> \<rho>"
      using instantiated_ancestor_wf[OF wf_class_table _ E, of "map TyVar ?\<alpha>s"] C by auto
    have wf\<sigma>s\<^sub>E: "\<forall>\<sigma>' \<in> set \<sigma>s\<^sub>E. wf_ty \<Sigma> \<sigma>'" using wf unfolding TyClass by simp
    from match_args_seq_Clash[OF clash] show False
    proof
      assume "length ?\<rho>s \<noteq> length \<sigma>s\<^sub>E"
      with equiv' show False by (auto dest: list_all2_lengthD)
    next
      assume "\<exists>i < length ?\<rho>s. match_args (?\<rho>s ! i) (\<sigma>s\<^sub>E ! i) = Clash"
      then obtain i where i: "i < length ?\<rho>s" and clash_i: "match_args (?\<rho>s ! i) (\<sigma>s\<^sub>E ! i) = Clash" by blast
      with equiv' have eq: "\<Sigma> \<turnstile> subst ?\<tau>s' ?\<alpha>s (?\<rho>s ! i) \<approx> inst \<eta> (\<sigma>s\<^sub>E ! i)" and "i < length \<sigma>s\<^sub>E"
        by (auto simp: list_all2_conv_all_nth)
      obtain \<beta>s where "inst \<eta> (\<sigma>s\<^sub>E ! i) = subst (map \<eta> \<beta>s) \<beta>s (\<sigma>s\<^sub>E ! i)" by (rule inst_as_subst)
      with match_args_clash[OF wf_class_table clash_i] wf\<rho>s wf\<sigma>s\<^sub>E i \<open>i < length \<sigma>s\<^sub>E\<close> eq show False by auto
    qed
  next
    case (TyPrim p)
    with above below have "p \<noteq> Never" and "p \<noteq> object" by (auto split: if_splits)
    with sub TyPrim have "p = Sized" by (cases p) (auto simp: subty_prim_iff)
    with sub TyPrim subty_sized_inv(1)[OF _ refl, of \<Sigma> "TyClass D \<upsilon>s"]
    have "\<Sigma> \<turnstile> TyClass D \<upsilon>s <: TyClass range_class []" by (auto elim!: sized.elims intro: SubtyRefl)
    from subty_class_class(1)[OF wf_class_table this refl refl D] have "range_class \<in> set (ancestors \<Sigma> D)" by simp
    from ancestors_comparable[OF wf_class_table D anc this] range_not_ancestor[OF C range] show False
      by (auto simp: ancestors_def range_ancestors)
  qed (use above sub nonunion in \<open>auto dest!: subty_structured_inv subty_never_inv\<close>)
qed

end


subsection \<open>Patterns at a type other than a union\<close>

lemma disjuncts_nonunion: "\<sigma> \<in> set (disjuncts \<tau>) \<Longrightarrow> \<not> is_union \<sigma>"
  by (induction \<tau>) auto

lemma has_values_disjunct: "\<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; has_values \<Sigma> k \<sigma> \<rbrakk> \<Longrightarrow> has_values \<Sigma> k \<tau>"
  by (induction \<tau>) (auto simp: has_values_union)

lemma has_float_values_disjunct: "\<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; has_float_values \<Sigma> \<sigma> \<rbrakk> \<Longrightarrow> has_float_values \<Sigma> \<tau>"
  by (induction \<tau>) auto

lemma matched_as_as: "matched_as \<Sigma> \<Gamma> \<tau> (PatAs p x) = matched_as \<Sigma> \<Gamma> \<tau> (node p)"
  by (induction \<tau>) auto

lemma remaining_as: "remaining \<Sigma> \<Gamma> \<tau> (PatAs p x) = remaining \<Sigma> \<Gamma> \<tau> (node p)"
  by (induction \<tau>) auto

lemma matched_as_var: "\<not> is_union \<tau> \<Longrightarrow> matched_as \<Sigma> \<Gamma> \<tau> (PatVar x) = \<tau>"
  by (cases \<tau>) auto

lemma matched_as_wild: "\<not> is_union \<tau> \<Longrightarrow> matched_as \<Sigma> \<Gamma> \<tau> PatWildcard = \<tau>"
  by (cases \<tau>) auto

lemma matched_as_literal:
  "\<lbrakk> \<not> is_union \<tau> ; \<forall>\<beta>. \<tau> \<noteq> TyVar \<beta> \<rbrakk>
  \<Longrightarrow> matched_as \<Sigma> \<Gamma> \<tau> (PatLiteral l)
      = (case l of LitFloat _ \<Rightarrow> meet \<Sigma> (TyPrim float) \<tau> | _ \<Rightarrow> meet \<Sigma> (TyLiteral l) \<tau>)"
  by (cases \<tau>; cases l) auto

lemma matched_as_constr:
  "\<lbrakk> \<not> is_union \<tau> ; resolve_name \<Gamma> q = Some (Type C) \<rbrakk> \<Longrightarrow> matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q a)
    = (case instance_at \<Sigma> C \<tau> of Instance \<sigma>s \<Rightarrow> meet \<Sigma> \<tau> (TyClass C \<sigma>s) | _ \<Rightarrow> TyPrim Never)"
  by (cases \<tau>) auto

lemma remaining_tuple_other: "\<lbrakk> \<not> is_union \<tau> ; \<forall>\<sigma>s. \<tau> \<noteq> TyTuple \<sigma>s \<rbrakk> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> (PatTuple ps) = \<tau>"
  by (cases \<tau>) auto

lemma remaining_list: "\<not> is_union \<tau> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> (PatList ps) = \<tau>"
  by (cases \<tau>) auto

lemma remaining_dict: "\<lbrakk> \<not> is_union \<tau> ; kps \<noteq> [] \<or> (\<forall>\<sigma>. \<tau> \<noteq> TyDict \<sigma>) \<rbrakk> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> (PatDict kps) = \<tau>"
  by (cases \<tau>; cases kps) auto

lemma remaining_constr:
  "\<lbrakk> \<not> is_union \<tau> ; resolve_name \<Gamma> q = Some (Type C) \<rbrakk> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> (PatConstr q a)
    = (case instance_at \<Sigma> C \<tau> of
         Instance \<sigma>s \<Rightarrow>
           if \<Sigma> \<turnstile> \<tau> <: TyClass C \<sigma>s
              \<and> (\<forall>(p, \<sigma>) \<in> set (zip (field_patterns \<Sigma> C a) (field_types \<Sigma> C \<sigma>s)).
                   remaining \<Sigma> \<Gamma> \<sigma> (node p) = TyPrim Never)
           then TyPrim Never else \<tau>
       | _ \<Rightarrow> \<tau>)"
  by (cases \<tau>) auto

subsection \<open>Field patterns of a constructor pattern\<close>

lemma check_field_map_Ok:
  "check_field_map a u xs n ys = Ok () \<Longrightarrow> n + length ys = length xs \<and> set ys = set (drop n xs)"
  by (auto simp: check_field_map_def split: if_splits)

lemma distinct_cover: "\<lbrakk> distinct xs ; n + length ys = length xs ; set ys = set (drop n xs) \<rbrakk> \<Longrightarrow> distinct ys"
proof -
  assume "distinct xs" and "n + length ys = length xs" and "set ys = set (drop n xs)"
  then have "card (set ys) = length ys" using distinct_card[of "drop n xs"] by simp
  then show "distinct ys" by (rule card_distinct)
qed

lemma kw_pattern_single:
  "\<lbrakk> distinct (map fst kps) ; x \<in> set (map fst kps) \<rbrakk>
  \<Longrightarrow> concat (map (\<lambda>(y, p). if y = x then [p] else []) kps) = [the (map_of kps x)]"
proof (induction kps)
  case (Cons kp kps)
  obtain y p where kp: "kp = (y, p)" by (cases kp)
  show ?case
  proof (cases "y = x")
    case True
    with Cons.prems kp have "x \<notin> set (map fst kps)" by simp
    then have "concat (map (\<lambda>(y, p). if y = x then [p] else []) kps) = []" by (induction kps) auto
    with True kp show ?thesis by simp
  next
    case False
    with Cons kp show ?thesis by simp
  qed
qed simp

lemma concat_map_singleton: "(\<And>z. z \<in> set zs \<Longrightarrow> g z = [h z]) \<Longrightarrow> concat (map g zs) = map h zs"
  by (induction zs) auto

(* Sub-patterns of a constructor pattern with well-formed arguments: the positional ones, then one for each
   remaining field, by keyword *)
lemma field_patterns_eq:
  assumes "distinct (field_names \<Sigma> C)" and "length ps + length kps = length (field_names \<Sigma> C)"
    and "set (map fst kps) = set (drop (length ps) (field_names \<Sigma> C))"
  shows "field_patterns \<Sigma> C (ps, kps) = ps @ map (\<lambda>x. the (map_of kps x)) (drop (length ps) (field_names \<Sigma> C))"
    and "distinct (map fst kps)"
proof -
  show dist: "distinct (map fst kps)" using distinct_cover[OF assms(1) _ assms(3)] assms(2) by simp
  show "field_patterns \<Sigma> C (ps, kps) = ps @ map (\<lambda>x. the (map_of kps x)) (drop (length ps) (field_names \<Sigma> C))"
    using kw_pattern_single[OF dist] assms(3) by (auto intro!: concat_map_singleton)
qed

lemma map_of_nth: "\<lbrakk> distinct (map fst xs) ; i < length xs \<rbrakk> \<Longrightarrow> map_of xs (fst (xs ! i)) = Some (snd (xs ! i))"
  by (metis map_of_is_SomeI nth_mem prod.collapse)

(* Lookups in two association lists with the same keys and related values *)
lemma map_of_list_all2:
  "\<lbrakk> map fst xs = map fst ys ; list_all2 R (map snd xs) (map snd ys) ; map_of ys k = Some b \<rbrakk>
  \<Longrightarrow> \<exists>a. map_of xs k = Some a \<and> R a b"
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  then obtain y ys' where "ys = y # ys'" by (cases ys) auto
  with Cons show ?case by (cases "fst x = k") auto
qed simp

lemma field_types_inst:
  assumes "wf_class_table \<Sigma>" and "C |\<in>| fmdom \<Sigma>" and "length \<sigma>s = length (type_params \<Sigma> C)"
  shows "field_types \<Sigma> C (map (subst \<tau>s \<alpha>s) \<sigma>s) = map (subst \<tau>s \<alpha>s) (field_types \<Sigma> C \<sigma>s)"
  unfolding field_types_def instantiate_fields_subst[OF assms] by (simp add: case_prod_beta)

lemma inst_field_types:
  assumes "wf_class_table \<Sigma>" and "wf_ty \<Sigma> (TyClass C \<sigma>s)"
  shows "field_types \<Sigma> C (map (inst \<eta>) \<sigma>s) = map (inst \<eta>) (field_types \<Sigma> C \<sigma>s)"
proof -
  have "finite (\<Union> (fv ` set \<sigma>s))" by (simp add: finite_fv)
  then obtain \<alpha>s where \<alpha>s: "\<And>\<tau>. fv \<tau> \<subseteq> \<Union> (fv ` set \<sigma>s) \<Longrightarrow> inst \<eta> \<tau> = subst (map \<eta> \<alpha>s) \<alpha>s \<tau>"
    using inst_subst_cover by blast
  have \<sigma>s: "map (inst \<eta>) \<sigma>s = map (subst (map \<eta> \<alpha>s) \<alpha>s) \<sigma>s" by (intro map_cong[OF refl] \<alpha>s) auto
  have C: "C |\<in>| fmdom \<Sigma>" and len: "length \<sigma>s = length (type_params \<Sigma> C)" using assms(2) by simp_all
  show ?thesis
    unfolding \<sigma>s field_types_inst[OF assms(1) C len, of "map \<eta> \<alpha>s" \<alpha>s]
    by (intro map_cong[OF refl]) (simp add: \<alpha>s[symmetric] field_types_fv[OF assms])
qed

lemma remaining_literal_bool:
  "remaining \<Sigma> \<Gamma> (TyPrim bool) (PatLiteral l) = (case l of LitBool b \<Rightarrow> TyLiteral (LitBool (\<not> b)) | _ \<Rightarrow> TyPrim bool)"
  by (cases l) auto

lemma remaining_literal_none:
  "remaining \<Sigma> \<Gamma> (TyPrim NoneType) (PatLiteral l) = (if l = LitNone then TyPrim Never else TyPrim NoneType)"
  by (cases l) auto

lemma remaining_literal_prim: "p \<notin> {bool, NoneType} \<Longrightarrow> remaining \<Sigma> \<Gamma> (TyPrim p) (PatLiteral l) = TyPrim p"
  by (cases p; cases l) auto

lemma remaining_literal_other:
  "\<lbrakk> \<not> is_union \<sigma> ; \<forall>l'. \<sigma> \<noteq> TyLiteral l' ; \<forall>p. \<sigma> \<noteq> TyPrim p \<rbrakk> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<sigma> (PatLiteral l) = \<sigma>"
  by (cases \<sigma>) auto

(* Lookup in a fold of maps agreeing at a variable *)
lemma foldr_fmadd_lookup_agree:
  "\<lbrakk> j < length \<rho>s ; x \<in> fmdom' (\<rho>s ! j)
   ; \<forall>k < length \<rho>s. x \<in> fmdom' (\<rho>s ! k) \<longrightarrow> fmlookup (\<rho>s ! k) x = fmlookup (\<rho>s ! j) x \<rbrakk>
  \<Longrightarrow> fmlookup (foldr fmadd \<rho>s fmempty) x = fmlookup (\<rho>s ! j) x"
proof (induction \<rho>s arbitrary: j)
  case (Cons \<rho> \<rho>s)
  show ?case
  proof (cases "x \<in> fmdom' (foldr fmadd \<rho>s fmempty)")
    case True
    then obtain k where k: "k < length \<rho>s" and xk: "x \<in> fmdom' (\<rho>s ! k)"
      by (auto simp: foldr_fmadd_dom' in_set_conv_nth)
    have agree: "fmlookup (\<rho>s ! k') x = fmlookup (\<rho>s ! k) x" if "k' < length \<rho>s" and "x \<in> fmdom' (\<rho>s ! k')" for k'
      using Cons.prems(3)[rule_format, of "Suc k'"] Cons.prems(3)[rule_format, of "Suc k"] that k xk by simp
    have "\<forall>k' < length \<rho>s. x \<in> fmdom' (\<rho>s ! k') \<longrightarrow> fmlookup (\<rho>s ! k') x = fmlookup (\<rho>s ! k) x"
      using agree by blast
    then have "fmlookup (foldr fmadd \<rho>s fmempty) x = fmlookup (\<rho>s ! k) x" by (rule Cons.IH[OF k xk])
    moreover have "fmlookup (\<rho>s ! k) x = fmlookup ((\<rho> # \<rho>s) ! j) x"
      using Cons.prems(3)[rule_format, of "Suc k"] k xk by simp
    ultimately show ?thesis using True by (simp add: fmdom'_alt_def)
  next
    case False
    with Cons.prems have "x \<in> fmdom' \<rho>" by (cases j) (auto simp: foldr_fmadd_dom' dest!: nth_mem)
    with False Cons.prems(3) show ?thesis by (auto simp: fmdom'_alt_def)
  qed
qed simp

lemma UN_set_nth: "\<Union> (f ` set xs) = (\<Union>j \<in> {..<length xs}. f (xs ! j))"
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> \<Union> (f ` set xs)"
  then obtain y where "y \<in> set xs" and "x \<in> f y" by blast
  then obtain j where "j < length xs" and "y = xs ! j" by (auto simp: in_set_conv_nth)
  with \<open>x \<in> f y\<close> show "x \<in> (\<Union>j \<in> {..<length xs}. f (xs ! j))" by auto
next
  fix x
  assume "x \<in> (\<Union>j \<in> {..<length xs}. f (xs ! j))"
  then obtain j where "j < length xs" and "x \<in> f (xs ! j)" by auto
  then show "x \<in> \<Union> (f ` set xs)" using nth_mem by blast
qed

(* Distinctness of a concatenation, invariant under permutation of the lists *)
lemma distinct_concat_perm: "mset xss = mset yss \<Longrightarrow> distinct (concat xss) = distinct (concat yss)"
proof -
  assume "mset xss = mset yss"
  then have "mset (concat xss) = mset (concat yss)" by (metis mset_concat sum_mset_sum_list mset_map)
  then show ?thesis by (metis distinct_count_atmost_1 mset_eq_setD)
qed

lemma map_of_keys: "distinct (map fst kps) \<Longrightarrow> map (\<lambda>x. the (map_of kps x)) (map fst kps) = map snd kps"
  by (intro nth_equalityI) (auto simp: map_of_nth)

(* Keyword patterns listed by the fields they supply: a permutation of the keyword patterns *)
lemma kw_perm:
  assumes "distinct (map fst kps)" and "distinct zs" and "set (map fst kps) = set zs"
  shows "mset (map (\<lambda>x. the (map_of kps x)) zs) = mset (map snd kps)"
proof -
  have "mset zs = mset (map fst kps)" using assms by (metis set_eq_iff_mset_eq_distinct)
  then have "mset (map (\<lambda>x. the (map_of kps x)) zs) = mset (map (\<lambda>x. the (map_of kps x)) (map fst kps))"
    by (metis mset_map)
  from this[unfolded map_of_keys[OF assms(1)]] show ?thesis .
qed

lemma kw_set:
  assumes "distinct (map fst kps)" and "set (map fst kps) = set zs"
  shows "set (map (\<lambda>(y, p). (p, g y)) kps) = set (map (\<lambda>x. (the (map_of kps x), g x)) zs)"
proof -
  have "set (map (\<lambda>(y, p). (p, g y)) kps) = (\<lambda>y. (the (map_of kps y), g y)) ` set (map fst kps)"
  proof (intro set_eqI iffI)
    fix pu
    assume "pu \<in> set (map (\<lambda>(y, p). (p, g y)) kps)"
    then obtain y p where "(y, p) \<in> set kps" and "pu = (p, g y)" by auto
    with map_of_is_SomeI[OF assms(1)] show "pu \<in> (\<lambda>y. (the (map_of kps y), g y)) ` set (map fst kps)" by force
  next
    fix pu
    assume "pu \<in> (\<lambda>y. (the (map_of kps y), g y)) ` set (map fst kps)"
    then obtain y where "y \<in> set (map fst kps)" and "pu = (the (map_of kps y), g y)" by auto
    then obtain p where "(y, p) \<in> set kps" by auto
    with map_of_is_SomeI[OF assms(1) this] \<open>pu = _\<close> show "pu \<in> set (map (\<lambda>(y, p). (p, g y)) kps)" by force
  qed
  then show ?thesis unfolding assms(2) by auto
qed

lemma foldr_match_append:
  "foldr seq_compose_match (xs @ ys) (Match fmempty)
   = seq_compose_match (foldr seq_compose_match xs (Match fmempty)) (foldr seq_compose_match ys (Match fmempty))"
proof (induction xs)
  case (Cons x xs)
  then show ?case by (cases x; cases "foldr seq_compose_match xs (Match fmempty)";
                      cases "foldr seq_compose_match ys (Match fmempty)") auto
qed (cases "foldr seq_compose_match ys (Match fmempty)", auto)

context evaluation
begin

subsection \<open>Soundness of pattern matching\<close>

(* Match of pattern p, checked at \<tau> with bindings \<Delta>, against value v: aborts are not prevented; a match binds the
   variables of \<Delta> at instances of their types and v is at the matched type; no match leaves v at the remaining type *)
definition pat_sound :: "cxt \<Rightarrow> (var \<Rightarrow> ty) \<Rightarrow> env \<Rightarrow> pat \<Rightarrow> ty \<Rightarrow> (var, ty) fmap \<Rightarrow> val \<Rightarrow> bool"
where
"pat_sound \<Gamma> \<eta> \<rho> p \<tau> \<Delta> v =
  ((\<forall>\<kappa>. match \<rho> p v = MatchAborts \<kappa> \<longrightarrow> \<not> prevented \<kappa>)
   \<and> (\<forall>\<rho>'. match \<rho> p v = Match \<rho>' \<longrightarrow> fmdom' \<rho>' = fmdom' \<Delta>
        \<and> (\<forall>x \<sigma>. fmlookup \<Delta> x = Some \<sigma> \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>)))
        \<and> \<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> p)))
   \<and> (match \<rho> p v = NoMatch \<longrightarrow> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> p))))"

lemma match_all_foldr:
  "length ps = length vs
  \<Longrightarrow> match_all \<rho> ps vs = foldr seq_compose_match (map (\<lambda>(p, v). match \<rho> (node p) v) (zip ps vs)) (Match fmempty)"
  by (induction ps vs rule: list_induct2) auto

lemma match_kws_foldr:
  "match_kws \<rho> kps zvs
   = foldr seq_compose_match (map (\<lambda>(y, p). match \<rho> (node p) (the (map_of zvs y))) kps) (Match fmempty)"
  by (induction kps) auto

lemma match_dict_foldr:
  "match_dict \<rho> kps \<delta>
   = foldr seq_compose_match (map (\<lambda>(w, p). match \<rho> (node p) (the (map_of \<delta> w))) kps) (Match fmempty)"
  by (induction kps) auto

(* Literal at an instance of a type other than a union or a type variable: the literal type below the type *)
lemma lit_comparable:
  assumes "\<turnstile> VLit l : Ty (inst \<eta> \<sigma>)" and "\<forall>x. l \<noteq> LitFloat x" and "\<not> is_union \<sigma>" and "\<forall>\<beta>. \<sigma> \<noteq> TyVar \<beta>"
  shows "\<Sigma> \<turnstile> TyLiteral l <: \<sigma>"
proof -
  from wf_lit_sub[OF assms(1)] assms(2) have "\<Sigma> \<turnstile> TyLiteral l <: inst \<eta> \<sigma>" by auto
  with assms(3, 4) show ?thesis by (cases \<sigma>) (auto dest!: subty_structured_inv)
qed

(* Number at an instance of a type other than a union or a type variable: the type comparable with float *)
lemma number_comparable_float:
  assumes "\<turnstile> VLit l : Ty (inst \<eta> \<sigma>)" and "is_number (VLit l)" and "\<not> is_union \<sigma>" and "\<forall>\<beta>. \<sigma> \<noteq> TyVar \<beta>"
  shows "\<Sigma> \<turnstile> TyPrim float <: \<sigma> \<or> \<Sigma> \<turnstile> \<sigma> <: TyPrim float"
proof (cases \<sigma>)
  case (TyPrim p)
  have "\<not> \<Sigma> \<turnstile> TyLiteral l <: TyPrim Sized" using assms(2) subty_sized_inv(1)[OF _ refl] by (cases l) fastforce+
  with wf_lit_sub[OF assms(1)] assms(2) show ?thesis
    unfolding TyPrim by (cases p; cases l) (auto simp: subty_prim_iff intro: SubtyObject SubtyRefl SubtyIntFloat)
next
  case (TyLiteral l')
  with wf_lit_sub[OF assms(1)] have "l' = l" by (auto dest!: subty_literal_inv')
  with assms(2) show ?thesis unfolding TyLiteral by (cases l) (auto intro!: SubtyLiteral intro: SubtyRefl SubtyIntFloat)
qed (use assms in \<open>auto dest!: wf_lit_sub subty_structured_inv\<close>)

(* Binding of a pattern at a disjunct: below its binding at the type, a join over the disjuncts *)
lemma bindings_at_sound:
  assumes b: "bindings_at \<Sigma> \<Gamma> p (map f (disjuncts \<tau>)) = Ok \<Delta>" and k: "k < length (disjuncts \<tau>)"
    and fk: "f (disjuncts \<tau> ! k) = Some (Ok \<Delta>\<^sub>d)"
    and dom: "\<forall>\<sigma> \<Delta>'. \<sigma> \<in> set (disjuncts \<tau>) \<and> f \<sigma> = Some (Ok \<Delta>')
                \<longrightarrow> fmdom' \<Delta>' = binds p \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)"
    and look: "fmlookup \<Delta>\<^sub>d x = Some \<upsilon>"
  shows "\<exists>\<sigma>'. fmlookup \<Delta> x = Some \<sigma>' \<and> \<Sigma> \<turnstile> \<upsilon> <: \<sigma>' \<and> wf_ty \<Sigma> \<sigma>'"
proof -
  from bindings_at_Ok[OF b] obtain \<Delta>s
    where rel: "list_all2 (\<lambda>m \<Delta>'. case m of Some m' \<Rightarrow> m' = Ok \<Delta>'
                              | None \<Rightarrow> \<Delta>' = fmconst (binds p) (TyPrim Never)
                                  \<and> (\<forall>x \<in> binds p. fmlookup \<Gamma> x = Some Unbound)) (map f (disjuncts \<tau>)) \<Delta>s"
    and \<Delta>: "\<Delta> = fmmap_keys (\<lambda>x _. joins \<Sigma> (map (\<lambda>\<Delta>'. the (fmlookup \<Delta>' x)) \<Delta>s)) (hd \<Delta>s)"
    by blast
  have len: "length \<Delta>s = length (disjuncts \<tau>)" using list_all2_lengthD[OF rel] by simp
  have \<Delta>k: "\<Delta>s ! k = \<Delta>\<^sub>d" using rel k fk by (auto simp: list_all2_conv_all_nth)
  have each: "fmdom' (\<Delta>s ! j) = binds p \<and> (\<forall>x \<upsilon>. fmlookup (\<Delta>s ! j) x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)"
    if j: "j < length (disjuncts \<tau>)" for j
  proof (cases "f (disjuncts \<tau> ! j)")
    case None
    with rel j have "\<Delta>s ! j = fmconst (binds p) (TyPrim Never)" by (auto simp: list_all2_conv_all_nth)
    then show ?thesis by (auto simp: fmlookup_dom'_iff fmlookup_fmconst finite_binds_pat split: if_splits)
  next
    case (Some m')
    with rel j have "m' = Ok (\<Delta>s ! j)" by (auto simp: list_all2_conv_all_nth)
    with dom[rule_format, of "disjuncts \<tau> ! j" "\<Delta>s ! j"] Some j show ?thesis by auto
  qed
  have x: "x \<in> binds p" using each[OF k] look \<Delta>k by (auto simp: fmlookup_dom'_iff)
  have zero: "0 < length (disjuncts \<tau>)" using k by linarith
  have ne: "\<Delta>s \<noteq> []" using zero len by auto
  from each[OF zero] x have "x \<in> fmdom' (hd \<Delta>s)" by (simp add: hd_conv_nth[OF ne])
  then have \<Delta>x: "fmlookup \<Delta> x = Some (joins \<Sigma> (map (\<lambda>\<Delta>'. the (fmlookup \<Delta>' x)) \<Delta>s))"
    unfolding \<Delta> by (auto simp: fmlookup_dom'_iff)
  have wf_all: "\<forall>\<tau>' \<in> set (map (\<lambda>\<Delta>'. the (fmlookup \<Delta>' x)) \<Delta>s). wf_ty \<Sigma> \<tau>'"
  proof
    fix \<tau>'
    assume "\<tau>' \<in> set (map (\<lambda>\<Delta>'. the (fmlookup \<Delta>' x)) \<Delta>s)"
    then obtain j where j: "j < length \<Delta>s" and \<tau>': "\<tau>' = the (fmlookup (\<Delta>s ! j) x)" by (auto simp: in_set_conv_nth)
    have jl: "j < length (disjuncts \<tau>)" using j len by simp
    have "x \<in> fmdom' (\<Delta>s ! j)" using each[OF jl] x by simp
    then obtain \<upsilon>' where \<upsilon>': "fmlookup (\<Delta>s ! j) x = Some \<upsilon>'" unfolding fmlookup_dom'_iff by blast
    with each[OF jl] have "wf_ty \<Sigma> \<upsilon>'" by blast
    then show "wf_ty \<Sigma> \<tau>'" by (simp add: \<tau>' \<upsilon>')
  qed
  have "\<Delta>s ! k \<in> set \<Delta>s" using k len by simp
  then have mem: "\<upsilon> \<in> set (map (\<lambda>\<Delta>'. the (fmlookup \<Delta>' x)) \<Delta>s)" using \<Delta>k look by force
  from joins_upper[OF wf_all mem] wf_joins[OF wf_all] \<Delta>x show ?thesis by auto
qed

lemma bindings_at_typed:
  assumes b: "bindings_at \<Sigma> \<Gamma> p (map f (disjuncts \<tau>)) = Ok \<Delta>" and k: "k < length (disjuncts \<tau>)"
    and fk: "f (disjuncts \<tau> ! k) = Some (Ok \<Delta>\<^sub>d)"
    and dom: "\<forall>\<sigma> \<Delta>'. \<sigma> \<in> set (disjuncts \<tau>) \<and> f \<sigma> = Some (Ok \<Delta>')
                \<longrightarrow> fmdom' \<Delta>' = binds p \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)"
    and look: "fmlookup \<Delta>\<^sub>d x = Some \<upsilon>" and u: "\<turnstile> u : Ty (inst \<eta> \<upsilon>)" and wf\<eta>: "wf_inst \<Sigma> \<eta>"
  shows "\<exists>\<sigma>'. fmlookup \<Delta> x = Some \<sigma>' \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>')"
proof -
  from bindings_at_sound[OF b k fk dom look] obtain \<sigma>' where \<sigma>': "fmlookup \<Delta> x = Some \<sigma>'" and sub: "\<Sigma> \<turnstile> \<upsilon> <: \<sigma>'"
    and wf: "wf_ty \<Sigma> \<sigma>'"
    by blast
  have "wf_ty \<Sigma> \<upsilon>" using dom[rule_format, of "disjuncts \<tau> ! k" \<Delta>\<^sub>d] k fk look by auto
  with inst_subty[OF wf_class_table sub] wf have "\<Sigma> \<turnstile> inst \<eta> \<upsilon> <: inst \<eta> \<sigma>'" by blast
  with u inst_wf[OF wf\<eta> wf] \<sigma>' show ?thesis by (auto intro: ValSub)
qed

(* Disjunct of a type at which a pattern has bindings: the check there succeeds, or there is none *)
lemma bindings_at_disjunct:
  assumes "bindings_at \<Sigma> \<Gamma> p (map f (disjuncts \<tau>)) = Ok \<Delta>" and "\<sigma> \<in> set (disjuncts \<tau>)"
  shows "(\<exists>\<Delta>'. f \<sigma> = Some (Ok \<Delta>')) \<or> f \<sigma> = None"
proof -
  from bindings_at_Ok[OF assms(1)] obtain \<Delta>s
    where rel: "list_all2 (\<lambda>m \<Delta>'. case m of Some m' \<Rightarrow> m' = Ok \<Delta>'
                              | None \<Rightarrow> \<Delta>' = fmconst (binds p) (TyPrim Never)
                                  \<and> (\<forall>x \<in> binds p. fmlookup \<Gamma> x = Some Unbound)) (map f (disjuncts \<tau>)) \<Delta>s"
    by blast
  from assms(2) obtain k where "k < length (disjuncts \<tau>)" and "disjuncts \<tau> ! k = \<sigma>" by (auto simp: in_set_conv_nth)
  with rel show ?thesis by (cases "f \<sigma>") (auto simp: list_all2_conv_all_nth)
qed

(* Pattern sound at each disjunct of a type with its bindings there, and matching no value at a disjunct without
   bindings: sound at the type with the joined bindings *)
lemma pat_sound_lift:
  assumes check: "check_pat \<Sigma> \<Gamma> p \<tau> = Ok \<Delta>" and b: "bindings_at \<Sigma> \<Gamma> p (map f (disjuncts \<tau>)) = Ok \<Delta>"
    and wf_f: "\<And>\<sigma> \<Delta>'. \<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; f \<sigma> = Some (Ok \<Delta>') \<rbrakk>
      \<Longrightarrow> fmdom' \<Delta>' = binds p \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)"
    and some: "\<And>\<sigma> \<Delta>'. \<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; f \<sigma> = Some (Ok \<Delta>') ; \<turnstile> v : Ty (inst \<eta> \<sigma>) \<rbrakk>
      \<Longrightarrow> pat_sound \<Gamma> \<eta> \<rho> p \<sigma> \<Delta>' v"
    and none: "\<And>\<sigma>. \<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; f \<sigma> = None ; \<turnstile> v : Ty (inst \<eta> \<sigma>) \<rbrakk>
      \<Longrightarrow> match \<rho> p v = NoMatch \<and> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> p))"
    and env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and wf: "wf_ty \<Sigma> \<tau>" and v: "\<turnstile> v : Ty (inst \<eta> \<tau>)"
  shows "pat_sound \<Gamma> \<eta> \<rho> p \<tau> \<Delta> v"
proof -
  note wf\<Gamma> = wf_env_wf_cxt[OF env] and wf\<eta> = wf_env_wf_inst[OF env]
  from wf_val_inst_disjunct[OF v] obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and v\<sigma>: "\<turnstile> v : Ty (inst \<eta> \<sigma>)" by blast
  note lift_m = matched_as_lift[OF \<sigma> check wf\<Gamma> wf wf\<eta>] and lift_r = remaining_lift[OF \<sigma> wf wf\<eta>]
  from bindings_at_disjunct[OF b \<sigma>] show ?thesis
  proof (elim disjE exE)
    assume "f \<sigma> = None"
    with none[OF \<sigma> this v\<sigma>] show ?thesis by (simp add: pat_sound_def lift_r)
  next
    fix \<Delta>\<^sub>d
    assume f: "f \<sigma> = Some (Ok \<Delta>\<^sub>d)"
    note sound = some[OF \<sigma> f v\<sigma>, unfolded pat_sound_def]
    from \<sigma> obtain k where k: "k < length (disjuncts \<tau>)" and "disjuncts \<tau> ! k = \<sigma>" by (auto simp: in_set_conv_nth)
    then have fk: "f (disjuncts \<tau> ! k) = Some (Ok \<Delta>\<^sub>d)" by (simp add: f)
    have dom: "fmdom' \<Delta> = fmdom' \<Delta>\<^sub>d" using check_pat_wf(1)[OF wf_class_table wf\<Gamma> wf check] wf_f[OF \<sigma> f] by simp
    have wf_f': "\<forall>\<sigma> \<Delta>'. \<sigma> \<in> set (disjuncts \<tau>) \<and> f \<sigma> = Some (Ok \<Delta>')
                  \<longrightarrow> fmdom' \<Delta>' = binds p \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)"
      using wf_f by blast
    show ?thesis
      unfolding pat_sound_def
    proof (intro conjI allI impI)
      show "\<And>\<kappa>. match \<rho> p v = MatchAborts \<kappa> \<Longrightarrow> \<not> prevented \<kappa>" using sound by blast
      show "match \<rho> p v = NoMatch \<Longrightarrow> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> p))" using sound lift_r by blast
      fix \<rho>'
      assume m: "match \<rho> p v = Match \<rho>'"
      with sound dom show "fmdom' \<rho>' = fmdom' \<Delta>" by simp
      from sound m show "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> p))" by (blast intro: lift_m)
      show "\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>')" if x: "fmlookup \<Delta> x = Some \<sigma>'" for x \<sigma>'
      proof -
        have "x \<in> fmdom' \<Delta>\<^sub>d" using x unfolding dom[symmetric] by (auto simp: fmlookup_dom'_iff)
        then obtain \<upsilon> where \<upsilon>: "fmlookup \<Delta>\<^sub>d x = Some \<upsilon>" by (auto simp: fmlookup_dom'_iff)
        with sound m obtain u where u: "fmlookup \<rho>' x = Some u" and typed: "\<turnstile> u : Ty (inst \<eta> \<upsilon>)" by blast
        from bindings_at_typed[OF b k fk wf_f' \<upsilon> typed wf\<eta>] x u show ?thesis by auto
      qed
    qed
  qed
qed

(* Bindings of sub-patterns checked at well-formed types: over the variables of the sub-patterns, well-formed *)
lemma pattern_bindings_check_wf:
  assumes "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) = Ok \<Delta>" and "length ps = length \<sigma>s"
    and "wf_cxt \<Sigma> \<Gamma>" and "\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>"
  shows "fmdom' \<Delta> = \<Union> ((binds \<circ> node) ` set ps) \<and> (\<forall>x \<sigma>. fmlookup \<Delta> x = Some \<sigma> \<longrightarrow> wf_ty \<Sigma> \<sigma>)"
proof -
  have sub: "fmdom' \<Delta>' = binds (node p) \<and> (\<forall>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<longrightarrow> wf_ty \<Sigma> \<sigma>' \<and> fv \<sigma>' \<subseteq> UNIV)"
    if "(p, \<sigma>) \<in> set (zip ps \<sigma>s)" and "check_pat_at \<Sigma> \<Gamma> p \<sigma> = Ok \<Delta>'" for p \<sigma> \<Delta>'
  proof -
    have "wf_ty \<Sigma> \<sigma>" using assms(4) set_zip_rightD[OF that(1)] by blast
    from check_pat_wf(2)[OF wf_class_table assms(3) this that(2)] show ?thesis by simp
  qed
  from pattern_bindings_wf[OF assms(1, 2) sub] show ?thesis by simp
qed

lemma pattern_bindings_check:
  assumes "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) fps fts) = Ok \<Delta>" and "length fps = length fts"
    and "i < length fps"
  shows "\<exists>\<Delta>'. check_pat_at \<Sigma> \<Gamma> (fps ! i) (fts ! i) = Ok \<Delta>'"
proof -
  from pattern_bindings_Ok[OF assms(1)] obtain \<Delta>s
    where "list_all2 (\<lambda>m \<Delta>'. m = Ok \<Delta>') (map2 (check_pat_at \<Sigma> \<Gamma>) fps fts) \<Delta>s"
    by blast
  with assms(2, 3) have "check_pat_at \<Sigma> \<Gamma> (fps ! i) (fts ! i) = Ok (\<Delta>s ! i)" by (simp add: list_all2_conv_all_nth)
  then show ?thesis ..
qed
(* Sub-patterns with bindings at types, each sound against the value at its index: the sequence matched against
   the values sound, binding the variables of the disjoint union of the bindings *)
lemma pattern_bindings_sound:
  assumes pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) fps fts) = Ok \<Delta>"
    and len: "length fps = length fts" "length fps = length us"
    and sound: "\<forall>i < length fps. \<forall>\<Delta>'. check_pat_at \<Sigma> \<Gamma> (fps ! i) (fts ! i) = Ok \<Delta>'
      \<longrightarrow> pat_sound \<Gamma> \<eta> \<rho> (node (fps ! i)) (fts ! i) \<Delta>' (us ! i)"
    and wf\<Gamma>: "wf_cxt \<Sigma> \<Gamma>" and wf: "\<forall>\<sigma> \<in> set fts. wf_ty \<Sigma> \<sigma>"
    and once: "distinct (concat (map (sorted_list_of_set \<circ> binds \<circ> node) fps))"
    and pus: "set pus = set (zip fps us)"
  defines "m \<equiv> foldr seq_compose_match (map (\<lambda>(p, u). match \<rho> (node p) u) pus) (Match fmempty)"
  shows "\<And>\<kappa>. m = MatchAborts \<kappa> \<Longrightarrow> \<not> prevented \<kappa>"
    and "m = NoMatch \<Longrightarrow> \<exists>i < length fps. match \<rho> (node (fps ! i)) (us ! i) = NoMatch"
    and "m = Match \<rho>' \<Longrightarrow> fmdom' \<rho>' = fmdom' \<Delta>
      \<and> (\<forall>x \<upsilon>. fmlookup \<Delta> x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>)))
      \<and> (\<forall>i < length fps. \<exists>\<rho>\<^sub>i. match \<rho> (node (fps ! i)) (us ! i) = Match \<rho>\<^sub>i)"
proof -
  from pattern_bindings_Ok[OF pb] obtain \<Delta>s
    where chk: "list_all2 (\<lambda>m \<Delta>'. m = Ok \<Delta>') (map2 (check_pat_at \<Sigma> \<Gamma>) fps fts) \<Delta>s"
    and \<Delta>: "\<Delta> = fold fmadd \<Delta>s fmempty"
    by blast
  have len\<Delta>s: "length fps = length \<Delta>s" using list_all2_lengthD[OF chk] len(1) by simp
  have chk_i: "check_pat_at \<Sigma> \<Gamma> (fps ! i) (fts ! i) = Ok (\<Delta>s ! i)" if "i < length fps" for i
    using chk that len(1) by (auto simp: list_all2_conv_all_nth)
  have sound_i: "pat_sound \<Gamma> \<eta> \<rho> (node (fps ! i)) (fts ! i) (\<Delta>s ! i) (us ! i)" if "i < length fps" for i
    using sound chk_i[OF that] that by blast
  have dom: "fmdom' (\<Delta>s ! i) = binds (node (fps ! i))" if "i < length fps" for i
    using check_pat_wf(2)[OF wf_class_table wf\<Gamma> _ chk_i[OF that]] wf that len(1) by auto
  let ?ms = "map (\<lambda>(p, u). match \<rho> (node p) u) pus"
  have index: "\<exists>i < length fps. p = fps ! i \<and> u = us ! i" if "(p, u) \<in> set pus" for p u
    using that pus len(2) by (auto simp: in_set_zip)
  have index': "(fps ! i, us ! i) \<in> set pus" if "i < length fps" for i
    using that pus len(2) by (auto simp: in_set_zip)
  have disjoint: "binds (node (fps ! i)) \<inter> binds (node (fps ! j)) = {}"
    if "i < length fps" and "j < length fps" and "i \<noteq> j" for i j
    using distinct_concat_nth[OF once, of i j] that finite_binds_pat by simp
  show "\<not> prevented \<kappa>" if "m = MatchAborts \<kappa>" for \<kappa>
  proof -
    from foldr_match_Aborts[OF that[unfolded m_def]] obtain p u where "(p, u) \<in> set pus"
      and "match \<rho> (node p) u = MatchAborts \<kappa>"
      by auto
    with index[OF this(1)] sound_i show ?thesis by (auto simp: pat_sound_def)
  qed
  show "\<exists>i < length fps. match \<rho> (node (fps ! i)) (us ! i) = NoMatch" if "m = NoMatch"
  proof -
    from foldr_match_NoMatch[OF that[unfolded m_def]] obtain p u where "(p, u) \<in> set pus"
      and "match \<rho> (node p) u = NoMatch"
      by auto
    with index[OF this(1)] show ?thesis by auto
  qed
  show "fmdom' \<rho>' = fmdom' \<Delta>
      \<and> (\<forall>x \<upsilon>. fmlookup \<Delta> x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>)))
      \<and> (\<forall>i < length fps. \<exists>\<rho>\<^sub>i. match \<rho> (node (fps ! i)) (us ! i) = Match \<rho>\<^sub>i)"
    if "m = Match \<rho>'"
  proof -
    from foldr_match_Match[OF that[unfolded m_def]] obtain \<rho>s
      where rel: "list_all2 (\<lambda>m \<rho>. m = Match \<rho>) ?ms \<rho>s" and \<rho>': "\<rho>' = foldr fmadd \<rho>s fmempty"
      by blast
    have len\<rho>s: "length \<rho>s = length pus" using list_all2_lengthD[OF rel] by simp
    have at: "match \<rho> (node (fst (pus ! j))) (snd (pus ! j)) = Match (\<rho>s ! j)" if "j < length pus" for j
      using rel that by (auto simp: list_all2_conv_all_nth case_prod_beta)
    (* Runtime result j: the result for the sub-pattern at index i, with its domain *)
    have at_i: "\<exists>i < length fps. fst (pus ! j) = fps ! i \<and> snd (pus ! j) = us ! i
                 \<and> fmdom' (\<rho>s ! j) = fmdom' (\<Delta>s ! i)
                 \<and> (\<forall>x \<upsilon>. fmlookup (\<Delta>s ! i) x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup (\<rho>s ! j) x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>)))"
      if j: "j < length pus" for j
    proof -
      from index[of "fst (pus ! j)" "snd (pus ! j)"] j obtain i where i: "i < length fps"
        and p: "fst (pus ! j) = fps ! i" and u: "snd (pus ! j) = us ! i"
        by auto
      from sound_i[OF i] at[OF j] have "fmdom' (\<rho>s ! j) = fmdom' (\<Delta>s ! i)
        \<and> (\<forall>x \<upsilon>. fmlookup (\<Delta>s ! i) x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup (\<rho>s ! j) x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>)))"
        unfolding pat_sound_def p u by blast
      with i p u show ?thesis by blast
    qed
    have matched: "\<exists>\<rho>\<^sub>i. match \<rho> (node (fps ! i)) (us ! i) = Match \<rho>\<^sub>i" if i: "i < length fps" for i
    proof -
      from index'[OF i] obtain j where "j < length pus" and "pus ! j = (fps ! i, us ! i)"
        by (auto simp: in_set_conv_nth)
      with at[OF this(1)] show ?thesis by auto
    qed
    have dom': "fmdom' \<rho>' = fmdom' \<Delta>"
    proof -
      have eq: "fmdom' (\<rho>s ! j) = binds (node (fst (pus ! j)))" if "j < length pus" for j
        using at_i[OF that] dom by auto
      have "fmdom' \<rho>' = (\<Union>j \<in> {..<length pus}. fmdom' (\<rho>s ! j))"
        unfolding \<rho>' foldr_fmadd_dom' UN_set_nth len\<rho>s by simp
      also have "\<dots> = (\<Union>j \<in> {..<length pus}. (\<lambda>(p, u). binds (node p)) (pus ! j))"
        using eq by (intro SUP_cong) (auto simp: case_prod_beta)
      also have "\<dots> = \<Union> ((\<lambda>(p, u). binds (node p)) ` set pus)" by (simp only: UN_set_nth)
      also have "\<dots> = \<Union> ((\<lambda>(p, u). binds (node p)) ` set (zip fps us))" by (simp add: pus)
      also have "\<dots> = (\<Union>i \<in> {..<length fps}. binds (node (fps ! i)))"
        unfolding UN_set_nth using len(2) by (simp add: case_prod_beta)
      also have "\<dots> = (\<Union>i \<in> {..<length \<Delta>s}. fmdom' (\<Delta>s ! i))" using dom len\<Delta>s by (intro SUP_cong) auto
      also have "\<dots> = fmdom' \<Delta>" by (simp add: \<Delta> fmdom'_fold_fmadd UN_set_nth)
      finally show ?thesis .
    qed
    have look: "\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>)" if \<upsilon>: "fmlookup \<Delta> x = Some \<upsilon>" for x \<upsilon>
    proof -
      from \<upsilon> have "x \<in> fmdom' \<Delta>" by (simp add: fmlookup_dom'_iff)
      then obtain i where i: "i < length \<Delta>s" and xi: "x \<in> fmdom' (\<Delta>s ! i)"
        by (auto simp: \<Delta> fmdom'_fold_fmadd in_set_conv_nth)
      have others: "x \<notin> fmdom' (\<Delta>s ! k)" if "k < length \<Delta>s" and "k \<noteq> i" for k
        using disjoint[of i k] dom[of i] dom[of k] i that len\<Delta>s xi by auto
      from fold_fmadd_lookup_nth[OF i xi] others \<upsilon> have \<upsilon>i: "fmlookup (\<Delta>s ! i) x = Some \<upsilon>" by (auto simp: \<Delta>)
      from index'[of i] i len\<Delta>s obtain j where j: "j < length pus" and pj: "pus ! j = (fps ! i, us ! i)"
        by (auto simp: in_set_conv_nth)
      from at_i[OF j] pj obtain i' where i': "i' < length fps" and "fps ! i = fps ! i'" and "us ! i = us ! i'"
        and domj: "fmdom' (\<rho>s ! j) = fmdom' (\<Delta>s ! i')"
        and lookj: "\<forall>x \<upsilon>. fmlookup (\<Delta>s ! i') x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup (\<rho>s ! j) x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>))"
        by auto
      have "i' = i"
      proof (rule ccontr)
        assume "i' \<noteq> i"
        with others[of i'] i' len\<Delta>s have "x \<notin> fmdom' (\<Delta>s ! i')" by simp
        moreover have "x \<in> fmdom' (\<Delta>s ! i')"
          using dom[of i] dom[of i'] \<open>fps ! i = fps ! i'\<close> \<upsilon>i i i' len\<Delta>s by (auto simp: fmlookup_dom'_iff)
        ultimately show False ..
      qed
      with lookj \<upsilon>i obtain u where u: "fmlookup (\<rho>s ! j) x = Some u" and typed: "\<turnstile> u : Ty (inst \<eta> \<upsilon>)" by blast
      have agree: "fmlookup (\<rho>s ! k) x = fmlookup (\<rho>s ! j) x" if k: "k < length \<rho>s" and xk: "x \<in> fmdom' (\<rho>s ! k)" for k
      proof -
        from at_i[OF k[unfolded len\<rho>s]] obtain i'' where i'': "i'' < length fps" and pk: "fst (pus ! k) = fps ! i''"
          and uk: "snd (pus ! k) = us ! i''" and domk: "fmdom' (\<rho>s ! k) = fmdom' (\<Delta>s ! i'')"
          by blast
        with xk others i len\<Delta>s have "i'' = i" by (cases "i'' = i") auto
        with at[OF k[unfolded len\<rho>s]] at[OF j] pj pk uk show ?thesis by simp
      qed
      have all: "\<forall>k < length \<rho>s. x \<in> fmdom' (\<rho>s ! k) \<longrightarrow> fmlookup (\<rho>s ! k) x = fmlookup (\<rho>s ! j) x"
        using agree by blast
      have "fmlookup \<rho>' x = fmlookup (\<rho>s ! j) x"
        unfolding \<rho>' using j len\<rho>s domj \<open>i' = i\<close> xi by (intro foldr_fmadd_lookup_agree[OF _ _ all]) simp_all
      with u typed show ?thesis by simp
    qed
    from dom' look matched show ?thesis by blast
  qed
qed

(* Sub-pattern of a pattern, smaller *)
lemma size_sub_pat:
  "p \<in> set ps \<Longrightarrow> size (node p) < size (PatTuple ps)"
  "p \<in> set ps \<Longrightarrow> size (node p) < size (PatList ps)"
  "p \<in> set (map snd wps) \<Longrightarrow> size (node p) < size (PatDict wps)"
  "p \<in> set (field_patterns \<Sigma> C (ps, kps)) \<Longrightarrow> size (node p) < size (PatConstr q (ps, kps))"
  by (auto dest!: field_patterns_elem dest: size_node_elem size_node_snd_elem size_node_snd_elem'
      simp del: field_patterns.simps)

lemma size_node_as: "size (node p) < size (PatAs p x)"
  by (cases p) simp

(* Match of a pattern checked at a type against a value at an instance of the type, sound *)
lemma check_pat_sound:
  "\<lbrakk> check_pat \<Sigma> \<Gamma> p \<tau> = Ok \<Delta> ; \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_ty \<Sigma> \<tau> ; \<turnstile> v : Ty (inst \<eta> \<tau>) \<rbrakk> \<Longrightarrow> pat_sound \<Gamma> \<eta> \<rho> p \<tau> \<Delta> v"
proof (induction p arbitrary: \<tau> \<Delta> v rule: measure_induct_rule[where f = size])
  case (less p)
  note env = less.prems(2)
  note wf\<Gamma> = wf_env_wf_cxt[OF env] and wf\<eta> = wf_env_wf_inst[OF env]
  (* Sub-pattern checked at a type, sound against a value at an instance of the type *)
  have IH: "pat_sound \<Gamma> \<eta> \<rho> (node p') \<tau>' \<Delta>' u"
    if "size (node p') < size p" and "check_pat_at \<Sigma> \<Gamma> p' \<tau>' = Ok \<Delta>'" and "wf_ty \<Sigma> \<tau>'" and "\<turnstile> u : Ty (inst \<eta> \<tau>')"
    for p' \<tau>' \<Delta>' u
    using less.IH[OF that(1) check_pat_at_node[OF that(2)] env that(3, 4)] .
  (* Value at the matched type when the pattern matches each disjunct as itself *)
  have matched_self: "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> p))" if "\<And>\<sigma>. \<not> is_union \<sigma> \<Longrightarrow> matched_as \<Sigma> \<Gamma> \<sigma> p = \<sigma>"
  proof -
    from wf_val_inst_disjunct[OF less.prems(4)] obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      by blast
    with matched_as_lift[OF \<sigma> less.prems(1) wf\<Gamma> less.prems(3) wf\<eta>] that[OF disjuncts_nonunion[OF \<sigma>]] show ?thesis
      by simp
  qed
  show ?case
  proof (cases p)
    case PatWildcard
    with less.prems(1) have "\<Delta> = fmempty" by simp
    with matched_self[OF matched_as_wild[unfolded PatWildcard[symmetric]]] show ?thesis
      by (simp add: pat_sound_def PatWildcard)
  next
    case (PatVar x)
    with less.prems(1) have "\<Delta> = fmupd x \<tau> fmempty" by (auto simp: bind_sum_Ok)
    with matched_self[OF matched_as_var[where x = x, unfolded PatVar[symmetric]]] less.prems(4) show ?thesis
      by (simp add: pat_sound_def PatVar)
  next
    case (PatAs p' x)
    from less.prems(1)[unfolded PatAs] obtain \<Delta>\<^sub>p where unb: "check_unbound \<Gamma> x = Ok ()"
      and once: "ensure (x \<notin> binds (node p')) (SelectsNoRule JudgementCheckPattern (PatternBindsTwice x)) = Ok ()"
      and chk: "check_pat_at \<Sigma> \<Gamma> p' \<tau> = Ok \<Delta>\<^sub>p"
      and \<Delta>: "\<Delta> = \<Delta>\<^sub>p ++\<^sub>f fmupd x (matched_as \<Sigma> \<Gamma> \<tau> (node p')) fmempty"
      by (auto simp: bind_sum_Ok)
    from once have x: "x \<notin> binds (node p')" by (simp add: ensure_def split: if_splits)
    note sound = IH[OF size_node_as[of p' x, unfolded PatAs[symmetric]] chk less.prems(3, 4),
        unfolded pat_sound_def]
    have dom\<^sub>p: "fmdom' \<Delta>\<^sub>p = binds (node p')"
      using check_pat_wf(2)[OF wf_class_table wf\<Gamma> less.prems(3) chk] by simp
    show ?thesis
      unfolding pat_sound_def PatAs
    proof (intro conjI allI impI)
      show "\<And>\<kappa>. match \<rho> (PatAs p' x) v = MatchAborts \<kappa> \<Longrightarrow> \<not> prevented \<kappa>"
        using sound by (cases "match \<rho> (node p') v") auto
      show "match \<rho> (PatAs p' x) v = NoMatch \<Longrightarrow> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (PatAs p' x)))"
        using sound by (cases "match \<rho> (node p') v") (auto simp: remaining_as)
      fix \<rho>'
      assume "match \<rho> (PatAs p' x) v = Match \<rho>'"
      then obtain \<rho>\<^sub>p where mp: "match \<rho> (node p') v = Match \<rho>\<^sub>p" and \<rho>': "\<rho>' = \<rho>\<^sub>p ++\<^sub>f fmupd x v fmempty"
        by (cases "match \<rho> (node p') v") auto
      with sound have dom: "fmdom' \<rho>\<^sub>p = fmdom' \<Delta>\<^sub>p"
        and look: "\<forall>y \<sigma>. fmlookup \<Delta>\<^sub>p y = Some \<sigma> \<longrightarrow> (\<exists>u. fmlookup \<rho>\<^sub>p y = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>))"
        and matched: "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (node p')))"
        by auto
      show "fmdom' \<rho>' = fmdom' \<Delta>" using dom x dom\<^sub>p unfolding \<rho>' \<Delta> by (auto simp: fmdom'_alt_def)
      show "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (PatAs p' x)))" using matched by (simp add: matched_as_as)
      show "\<exists>u. fmlookup \<rho>' y = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>)" if "fmlookup \<Delta> y = Some \<sigma>" for y \<sigma>
        using that look matched x dom dom\<^sub>p less.prems(4) unfolding \<rho>' \<Delta>
        by (auto simp: fmlookup_dom'_iff split: if_splits)
    qed
  next
    case (PatLiteral l)
    from less.prems(1)[unfolded PatLiteral] have \<Delta>: "\<Delta> = fmempty"
      and no_float: "\<not> (is_int_lit l \<and> has_float_values \<Sigma> \<tau>)"
      by (auto simp: bind_sum_Ok ensure_def split: if_splits)
    from wf_val_inst_disjunct[OF less.prems(4)] obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)"
      and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      by blast
    note nonunion = disjuncts_nonunion[OF \<sigma>]
    note lift_m = matched_as_lift[OF \<sigma> less.prems(1)[unfolded PatLiteral] wf\<Gamma> less.prems(3) wf\<eta>]
    note lift_r = remaining_lift[OF \<sigma> less.prems(3) wf\<eta>]
    have not_float: "\<not> (is_int_lit l \<and> is_float v)"
    proof
      assume "is_int_lit l \<and> is_float v"
      then obtain x where "v = VLit (LitFloat x)" by (cases v) (auto elim: is_float.elims)
      with v float_has_values has_float_values_disjunct[OF \<sigma>] no_float \<open>is_int_lit l \<and> is_float v\<close> show False
        by blast
    qed
    show ?thesis
      unfolding pat_sound_def PatLiteral \<Delta>
    proof (intro conjI allI impI)
      fix \<kappa>
      assume "match \<rho> (PatLiteral l) v = MatchAborts \<kappa>"
      with not_float have "eq (VLit l) v = Aborts \<kappa>" by (auto split: if_splits result.splits bool.splits)
      with eq_abort(1)[OF this] show "\<not> prevented \<kappa>" by simp
    next
      assume no: "match \<rho> (PatLiteral l) v = NoMatch"
      have "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatLiteral l)))"
      proof (cases \<sigma>)
        case (TyLiteral l')
        with v have "v = VLit l'" by (auto dest: wf_val_literal)
        with no not_float have "l' \<noteq> l" by (cases l) (auto split: if_splits result.splits bool.splits)
        with \<open>v = VLit l'\<close> show ?thesis unfolding TyLiteral by (simp add: ValLit)
      next
        case (TyPrim p)
        consider "p = bool" | "p = NoneType" | "p \<notin> {bool, NoneType}" by blast
        then show ?thesis
        proof cases
          case 1
          with v TyPrim obtain b' where v': "v = VLit (LitBool b')" by (auto dest: wf_val_bool)
          show ?thesis
          proof (cases l)
            case (LitBool b)
            with no v' have "b' \<noteq> b" by (auto split: if_splits bool.splits result.splits)
            with v' show ?thesis unfolding TyPrim 1 LitBool by (simp add: remaining_literal_bool ValLit)
          qed (use v TyPrim 1 in \<open>simp_all add: remaining_literal_bool\<close>)
        next
          case 2
          with v TyPrim have v': "v = VLit LitNone" by (auto dest: wf_val_none)
          with no have "l \<noteq> LitNone" by (cases l) (auto split: if_splits)
          with v TyPrim 2 show ?thesis by (simp add: remaining_literal_none)
        next
          case 3
          with v TyPrim show ?thesis by (simp add: remaining_literal_prim)
        qed
      qed (use v nonunion in \<open>simp_all add: remaining_literal_other\<close>)
      then show "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (PatLiteral l)))" by (rule lift_r)
    next
      fix \<rho>'
      assume m: "match \<rho> (PatLiteral l) v = Match \<rho>'"
      with not_float have \<rho>': "\<rho>' = fmempty" and eq: "eq (VLit l) v = Val True"
        by (auto split: if_splits result.splits bool.splits)
      from eq obtain l' where v': "v = VLit l'" and eq_lit: "eq_lit l l' = Val True" by (cases v) auto
      have "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<sigma> (PatLiteral l)))"
      proof (cases "\<exists>\<beta>. \<sigma> = TyVar \<beta>")
        case True
        with v show ?thesis by auto
      next
        case False
        note matched = matched_as_literal[OF nonunion, of \<Sigma> \<Gamma> l] False
        show ?thesis
        proof (cases "\<exists>x. l = LitFloat x")
          case True
          then obtain x where l: "l = LitFloat x" by blast
          from eq_lit_float[OF eq_lit[unfolded l]] have number: "is_number (VLit l')" .
          then have float: "\<turnstile> v : Ty (TyPrim float)"
            unfolding v' by (cases l') (auto intro: wf_int_float ValLitFloat)
          from number_comparable_float[OF v[unfolded v'] number nonunion] False
          consider "\<Sigma> \<turnstile> TyPrim float <: \<sigma>" | "\<Sigma> \<turnstile> \<sigma> <: TyPrim float" by blast
          then show ?thesis using matched float v unfolding l by cases (auto simp: meet_float[OF nonunion])
        next
          case no_float: False
          with not_float v' eq_lit have "\<forall>x. l' \<noteq> LitFloat x" by (cases l; cases l') auto
          with eq_lit_same[OF eq_lit] no_float have "l' = l" by auto
          with v' have lit: "\<turnstile> v : Ty (TyLiteral l)" by (simp add: ValLit)
          from lit_comparable[OF v[unfolded v' \<open>l' = l\<close>] _ nonunion] False no_float have "\<Sigma> \<turnstile> TyLiteral l <: \<sigma>"
            by auto
          with matched lit no_float show ?thesis by (cases l) (auto simp: meet_literal[OF nonunion])
        qed
      qed
      then show "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (PatLiteral l)))" by (rule lift_m)
      show "fmdom' \<rho>' = fmdom' fmempty" by (simp add: \<rho>')
      show "\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>')" if "fmlookup fmempty x = Some \<sigma>'" for x \<sigma>'
        using that by simp
    qed
  next
    case (PatTuple ps)
    note prems = less.prems[unfolded PatTuple]
    let ?f = "\<lambda>\<sigma>. case \<sigma> of
                TyTuple \<sigma>s \<Rightarrow>
                  if length \<sigma>s = length ps then Some (pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s))
                  else None
              | _ \<Rightarrow> None"
    from prems(1) obtain u where ens: "by_rule RuleCheckTupleNone (do {
        ensure (\<not> has_values \<Sigma> ListKind \<tau>) (SequenceKindMismatch TupleKind \<tau> ListKind);
        ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch TupleKind \<tau> RangeKind)
      }) = Ok u"
      and cb: "check_bound_once ps = Ok ()" and b: "bindings_at \<Sigma> \<Gamma> (PatTuple ps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
      by (auto simp: bind_sum_Ok)
    from ens have no_list: "\<not> has_values \<Sigma> ListKind \<tau>" and no_range: "\<not> has_values \<Sigma> RangeKind \<tau>"
      by (auto simp: bind_sum_Ok ensure_def split: if_splits)
    show ?thesis
      unfolding PatTuple
    proof (rule pat_sound_lift[OF prems(1) b _ _ _ env prems(3, 4)])
      fix \<sigma> \<Delta>'
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')"
      then obtain \<sigma>s where \<sigma>s: "\<sigma> = TyTuple \<sigma>s" and len: "length \<sigma>s = length ps"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) = Ok \<Delta>'"
        by (auto split: ty.splits if_splits)
      have "\<forall>\<sigma>' \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>'" using disjuncts_wf[OF prems(3) \<sigma>] by (simp add: \<sigma>s)
      from pattern_bindings_check_wf[OF pb len[symmetric] wf\<Gamma> this]
      show "fmdom' \<Delta>' = binds (PatTuple ps) \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)" by simp
    next
      fix \<sigma> \<Delta>'
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      from f obtain \<sigma>s where \<sigma>s: "\<sigma> = TyTuple \<sigma>s" and len: "length \<sigma>s = length ps"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) = Ok \<Delta>'"
        by (auto split: ty.splits if_splits)
      have wf\<sigma>s: "\<forall>\<sigma>' \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>'" using disjuncts_wf[OF prems(3) \<sigma>] by (simp add: \<sigma>s)
      obtain vs where vs: "v = VTuple vs" and typed: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs (map (inst \<eta>) \<sigma>s)"
        using v unfolding \<sigma>s by (auto elim: wf_tuple)
      have len_vs: "length vs = length ps" using list_all2_lengthD[OF typed] len by simp
      have sound_i: "pat_sound \<Gamma> \<eta> \<rho> (node (ps ! i)) (\<sigma>s ! i) \<Delta>'' (vs ! i)"
        if i: "i < length ps" and chk: "check_pat_at \<Sigma> \<Gamma> (ps ! i) (\<sigma>s ! i) = Ok \<Delta>''" for i \<Delta>''
      proof (rule IH[OF _ chk])
        show "size (node (ps ! i)) < size p" unfolding PatTuple by (intro size_sub_pat(1) nth_mem i)
        show "wf_ty \<Sigma> (\<sigma>s ! i)" using wf\<sigma>s i len by simp
        show "\<turnstile> vs ! i : Ty (inst \<eta> (\<sigma>s ! i))" using typed i len by (auto simp: list_all2_conv_all_nth)
      qed
      have sound_all: "\<forall>i < length ps. \<forall>\<Delta>''. check_pat_at \<Sigma> \<Gamma> (ps ! i) (\<sigma>s ! i) = Ok \<Delta>''
        \<longrightarrow> pat_sound \<Gamma> \<eta> \<rho> (node (ps ! i)) (\<sigma>s ! i) \<Delta>'' (vs ! i)"
        using sound_i by blast
      note seq = pattern_bindings_sound[OF pb len[symmetric] len_vs[symmetric] sound_all wf\<Gamma> wf\<sigma>s
          check_bound_once_Ok[OF cb] refl]
      have m: "match \<rho> (PatTuple ps) v
               = foldr seq_compose_match (map (\<lambda>(p, u). match \<rho> (node p) u) (zip ps vs)) (Match fmempty)"
        using len_vs by (simp add: vs match_all_foldr)
      show "pat_sound \<Gamma> \<eta> \<rho> (PatTuple ps) \<sigma> \<Delta>' v"
        unfolding pat_sound_def
      proof (intro conjI allI impI)
        show "\<And>\<kappa>. match \<rho> (PatTuple ps) v = MatchAborts \<kappa> \<Longrightarrow> \<not> prevented \<kappa>" using seq(1) unfolding m by blast
        fix \<rho>'
        assume "match \<rho> (PatTuple ps) v = Match \<rho>'"
        note seq\<^sub>3 = seq(3)[OF this[unfolded m]]
        then show "fmdom' \<rho>' = fmdom' \<Delta>'"
          and "\<And>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<Longrightarrow> \<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>')"
          by blast+
        have "\<turnstile> vs ! i : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> (\<sigma>s ! i) (node (ps ! i))))" if i: "i < length ps" for i
        proof -
          from pattern_bindings_check[OF pb len[symmetric] i] obtain \<Delta>''
            where "check_pat_at \<Sigma> \<Gamma> (ps ! i) (\<sigma>s ! i) = Ok \<Delta>''"
            by blast
          from sound_i[OF i this] seq\<^sub>3 i show ?thesis by (auto simp: pat_sound_def)
        qed
        then show "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<sigma> (PatTuple ps)))"
          unfolding \<sigma>s vs using len len_vs by (auto intro!: ValTuple simp: list_all2_conv_all_nth)
      next
        assume "match \<rho> (PatTuple ps) v = NoMatch"
        from seq(2)[OF this[unfolded m]] obtain i where i: "i < length ps"
          and no_i: "match \<rho> (node (ps ! i)) (vs ! i) = NoMatch"
          by blast
        from pattern_bindings_check[OF pb len[symmetric] i] obtain \<Delta>''
          where "check_pat_at \<Sigma> \<Gamma> (ps ! i) (\<sigma>s ! i) = Ok \<Delta>''"
          by blast
        from sound_i[OF i this] no_i have vi: "\<turnstile> vs ! i : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> (\<sigma>s ! i) (node (ps ! i))))"
          by (simp add: pat_sound_def)
        let ?\<rho>s = "map2 (\<lambda>\<tau> p. remaining \<Sigma> \<Gamma> \<tau> (node p)) \<sigma>s ps"
        have \<rho>s_i: "?\<rho>s ! i = remaining \<Sigma> \<Gamma> (\<sigma>s ! i) (node (ps ! i))" using i len by simp
        have ne: "?\<rho>s ! i \<noteq> TyPrim Never" using vi wf_val_never unfolding \<rho>s_i by (cases "?\<rho>s ! i") auto
        show "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatTuple ps)))"
        proof (cases "filter (\<lambda>j. ?\<rho>s ! j \<noteq> TyPrim Never) [0..<length ?\<rho>s]")
          case Nil
          with i len ne have False by (auto simp: filter_empty_conv)
          then show ?thesis ..
        next
          case (Cons j js)
          show ?thesis
          proof (cases js)
            case Nil
            with Cons have single: "filter (\<lambda>j. ?\<rho>s ! j \<noteq> TyPrim Never) [0..<length ?\<rho>s] = [j]" by simp
            have "i \<in> set (filter (\<lambda>j. ?\<rho>s ! j \<noteq> TyPrim Never) [0..<length ?\<rho>s])" using i len ne by simp
            with single have ji: "j = i" by simp
            have "remaining \<Sigma> \<Gamma> \<sigma> (PatTuple ps) = TyTuple (\<sigma>s[i := ?\<rho>s ! i])"
              unfolding \<sigma>s using len single ji by (simp add: Let_def)
            moreover have "\<turnstile> v : Ty (TyTuple (map (inst \<eta>) (\<sigma>s[i := ?\<rho>s ! i])))"
              using typed vi i len unfolding vs \<rho>s_i
              by (auto intro!: ValTuple simp: list_all2_conv_all_nth nth_list_update)
            ultimately show ?thesis by simp
          next
            case (Cons j' js')
            with \<open>filter _ _ = j # js\<close> have "remaining \<Sigma> \<Gamma> \<sigma> (PatTuple ps) = TyTuple \<sigma>s"
              unfolding \<sigma>s using len by (simp add: Let_def)
            with v show ?thesis unfolding \<sigma>s by simp
          qed
        qed
      qed
    next
      fix \<sigma>
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = None" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      note nonunion = disjuncts_nonunion[OF \<sigma>]
      show "match \<rho> (PatTuple ps) v = NoMatch \<and> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatTuple ps)))"
      proof (cases "\<exists>\<sigma>s. \<sigma> = TyTuple \<sigma>s")
        case True
        then obtain \<sigma>s where \<sigma>s: "\<sigma> = TyTuple \<sigma>s" by blast
        with f have len: "length \<sigma>s \<noteq> length ps" by (auto split: if_splits)
        obtain vs where vs: "v = VTuple vs" and "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs (map (inst \<eta>) \<sigma>s)"
          using v unfolding \<sigma>s by (auto elim: wf_tuple)
        with len have "length ps \<noteq> length vs" by (auto dest: list_all2_lengthD)
        with v len show ?thesis unfolding \<sigma>s vs by simp
      next
        case False
        have "match \<rho> (PatTuple ps) v = NoMatch"
        proof (cases v)
          case (VTuple vs)
          with tuple_at_nontuple[OF v[unfolded VTuple] nonunion] False has_values_disjunct[OF \<sigma>] no_list
          show ?thesis by auto
        next
          case (VList vs)
          with v list_has_values has_values_disjunct[OF \<sigma>] no_list show ?thesis by blast
        next
          case (VObject D zvs)
          with v range_has_values has_values_disjunct[OF \<sigma>] no_range show ?thesis by (cases "D = range_class") auto
        qed simp_all
        with v False show ?thesis by (simp add: remaining_tuple_other[OF nonunion])
      qed
    qed
  next
    case (PatList ps)
    note prems = less.prems[unfolded PatList]
    let ?f = "\<lambda>\<sigma>. case \<sigma> of
                TyList \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p. check_pat_at \<Sigma> \<Gamma> p \<sigma>') ps))
              | _ \<Rightarrow> None"
    from prems(1) obtain u where ens: "by_rule RuleCheckListNone (do {
        ensure (\<not> has_values \<Sigma> TupleKind \<tau>) (SequenceKindMismatch ListKind \<tau> TupleKind);
        ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch ListKind \<tau> RangeKind)
      }) = Ok u"
      and cb: "check_bound_once ps = Ok ()" and b: "bindings_at \<Sigma> \<Gamma> (PatList ps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
      by (auto simp: bind_sum_Ok)
    from ens have no_tuple: "\<not> has_values \<Sigma> TupleKind \<tau>" and no_range: "\<not> has_values \<Sigma> RangeKind \<tau>"
      by (auto simp: bind_sum_Ok ensure_def split: if_splits)
    show ?thesis
      unfolding PatList
    proof (rule pat_sound_lift[OF prems(1) b _ _ _ env prems(3, 4)])
      fix \<sigma> \<Delta>'
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')"
      then obtain \<sigma>' where \<sigma>s: "\<sigma> = TyList \<sigma>'"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps (replicate (length ps) \<sigma>')) = Ok \<Delta>'"
        by (auto simp: map2_replicate split: ty.splits)
      have "\<forall>\<sigma>'' \<in> set (replicate (length ps) \<sigma>'). wf_ty \<Sigma> \<sigma>''" using disjuncts_wf[OF prems(3) \<sigma>] by (simp add: \<sigma>s)
      from pattern_bindings_check_wf[OF pb _ wf\<Gamma> this]
      show "fmdom' \<Delta>' = binds (PatList ps) \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)" by simp
    next
      fix \<sigma> \<Delta>'
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      from f obtain \<sigma>' where \<sigma>s: "\<sigma> = TyList \<sigma>'"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps (replicate (length ps) \<sigma>')) = Ok \<Delta>'"
        by (auto simp: map2_replicate split: ty.splits)
      let ?\<sigma>s = "replicate (length ps) \<sigma>'"
      have wf\<sigma>': "wf_ty \<Sigma> \<sigma>'" using disjuncts_wf[OF prems(3) \<sigma>] by (simp add: \<sigma>s)
      obtain vs where vs: "v = VList vs" and typed: "\<forall>u \<in> set vs. \<turnstile> u : Ty (inst \<eta> \<sigma>')"
        using v unfolding \<sigma>s by (auto elim: wf_list)
      have other: "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatList ps)))" using v by (simp add: \<sigma>s remaining_list)
      show "pat_sound \<Gamma> \<eta> \<rho> (PatList ps) \<sigma> \<Delta>' v"
      proof (cases "length ps = length vs")
        case False
        then have "match \<rho> (PatList ps) v = NoMatch" by (simp add: vs)
        with other show ?thesis by (simp add: pat_sound_def)
      next
        case True
        have sound_i: "pat_sound \<Gamma> \<eta> \<rho> (node (ps ! i)) (?\<sigma>s ! i) \<Delta>'' (vs ! i)"
          if i: "i < length ps" and chk: "check_pat_at \<Sigma> \<Gamma> (ps ! i) (?\<sigma>s ! i) = Ok \<Delta>''" for i \<Delta>''
        proof (rule IH[OF _ chk])
          show "size (node (ps ! i)) < size p" unfolding PatList by (intro size_sub_pat(2) nth_mem i)
          show "wf_ty \<Sigma> (?\<sigma>s ! i)" using wf\<sigma>' i by simp
          show "\<turnstile> vs ! i : Ty (inst \<eta> (?\<sigma>s ! i))" using typed i True by simp
        qed
        have len: "length ps = length ?\<sigma>s" and wf: "\<forall>\<sigma>'' \<in> set ?\<sigma>s. wf_ty \<Sigma> \<sigma>''" using wf\<sigma>' by simp_all
        have sound_all: "\<forall>i < length ps. \<forall>\<Delta>''. check_pat_at \<Sigma> \<Gamma> (ps ! i) (?\<sigma>s ! i) = Ok \<Delta>''
        \<longrightarrow> pat_sound \<Gamma> \<eta> \<rho> (node (ps ! i)) (?\<sigma>s ! i) \<Delta>'' (vs ! i)"
        using sound_i by blast
        note seq = pattern_bindings_sound[OF pb len True sound_all wf\<Gamma> wf check_bound_once_Ok[OF cb] refl]
        have m: "match \<rho> (PatList ps) v
                 = foldr seq_compose_match (map (\<lambda>(p, u). match \<rho> (node p) u) (zip ps vs)) (Match fmempty)"
          using True by (simp add: vs match_all_foldr)
        show ?thesis
          unfolding pat_sound_def
        proof (intro conjI allI impI)
          show "\<And>\<kappa>. match \<rho> (PatList ps) v = MatchAborts \<kappa> \<Longrightarrow> \<not> prevented \<kappa>" using seq(1) unfolding m by blast
          show "match \<rho> (PatList ps) v = NoMatch \<Longrightarrow> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatList ps)))"
            using other by blast
          fix \<rho>'
          assume "match \<rho> (PatList ps) v = Match \<rho>'"
          from seq(3)[OF this[unfolded m]] show "fmdom' \<rho>' = fmdom' \<Delta>'"
            and "\<And>x \<sigma>''. fmlookup \<Delta>' x = Some \<sigma>'' \<Longrightarrow> \<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>'')"
            by blast+
          show "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<sigma> (PatList ps)))" using v by (simp add: \<sigma>s)
        qed
      qed
    next
      fix \<sigma>
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = None" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      note nonunion = disjuncts_nonunion[OF \<sigma>]
      from f have nonlist: "\<forall>\<sigma>'. \<sigma> \<noteq> TyList \<sigma>'" by (auto split: ty.splits)
      have "match \<rho> (PatList ps) v = NoMatch"
      proof (cases v)
        case (VList vs)
        with list_at_nonlist[OF v[unfolded VList] nonunion nonlist] has_values_disjunct[OF \<sigma>] no_tuple have False
          by blast
        then show ?thesis ..
      next
        case (VTuple vs)
        with v tuple_has_values has_values_disjunct[OF \<sigma>] no_tuple have False by blast
        then show ?thesis ..
      next
        case (VObject D zvs)
        with v range_has_values has_values_disjunct[OF \<sigma>] no_range show ?thesis by (cases "D = range_class") auto
      qed simp_all
      with v show "match \<rho> (PatList ps) v = NoMatch \<and> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatList ps)))"
        by (simp add: remaining_list[OF nonunion])
    qed
  next
    case (PatDict kps)
    note prems = less.prems[unfolded PatDict]
    note m2r = map2_replicate[of _ "map snd kps", simplified]
    let ?ps = "map snd kps"
    let ?f = "\<lambda>\<sigma>. case \<sigma> of
                TyDict \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p. check_pat_at \<Sigma> \<Gamma> p \<sigma>') ?ps))
              | _ \<Rightarrow> if has_dict_values \<Sigma> \<sigma> then Some (Fail (Violates RuleCheckDictNone (DictPatternDictValues \<sigma>)))
                     else None"
    from prems(1) have cb: "check_bound_once ?ps = Ok ()"
      and b: "bindings_at \<Sigma> \<Gamma> (PatDict kps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
      by (auto simp: bind_sum_Ok)
    show ?thesis
      unfolding PatDict
    proof (rule pat_sound_lift[OF prems(1) b _ _ _ env prems(3, 4)])
      fix \<sigma> \<Delta>'
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')"
      then obtain \<sigma>' where \<sigma>s: "\<sigma> = TyDict \<sigma>'"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ?ps (replicate (length ?ps) \<sigma>')) = Ok \<Delta>'"
        by (auto simp: m2r split: ty.splits if_splits)
      have "\<forall>\<sigma>'' \<in> set (replicate (length ?ps) \<sigma>'). wf_ty \<Sigma> \<sigma>''"
        using disjuncts_wf[OF prems(3) \<sigma>] by (simp add: \<sigma>s)
      from pattern_bindings_check_wf[OF pb _ wf\<Gamma> this]
      show "fmdom' \<Delta>' = binds (PatDict kps) \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)" by auto
    next
      fix \<sigma> \<Delta>'
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      from f obtain \<sigma>' where \<sigma>s: "\<sigma> = TyDict \<sigma>'"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ?ps (replicate (length ?ps) \<sigma>')) = Ok \<Delta>'"
        by (auto simp: m2r split: ty.splits if_splits)
      let ?\<sigma>s = "replicate (length ?ps) \<sigma>'"
      have wf\<sigma>': "wf_ty \<Sigma> \<sigma>'" using disjuncts_wf[OF prems(3) \<sigma>] by (simp add: \<sigma>s)
      obtain \<delta> where \<delta>: "v = VDict \<delta>" and typed: "\<forall>w u. (w, u) \<in> set \<delta> \<longrightarrow> \<turnstile> u : Ty (inst \<eta> \<sigma>')"
        using v unfolding \<sigma>s by (auto elim: wf_dict)
      have other: "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatDict kps)))" if "kps \<noteq> []"
        using v that by (simp add: \<sigma>s remaining_dict)
      show "pat_sound \<Gamma> \<eta> \<rho> (PatDict kps) \<sigma> \<Delta>' v"
      proof (cases "set (map fst kps) \<subseteq> set (map fst \<delta>)")
        case False
        then have no: "match \<rho> (PatDict kps) v = NoMatch" by (simp add: \<delta>)
        from False have "kps \<noteq> []" by auto
        with no other show ?thesis by (simp add: pat_sound_def)
      next
        case True
        let ?us = "map (\<lambda>(w, p). the (map_of \<delta> w)) kps"
        have us_typed: "\<turnstile> ?us ! i : Ty (inst \<eta> \<sigma>')" if i: "i < length kps" for i
        proof -
          obtain w p where kp: "kps ! i = (w, p)" by (cases "kps ! i")
          with i have "w \<in> set (map fst kps)" by (metis fst_conv image_eqI nth_mem set_map)
          with True have "w \<in> set (map fst \<delta>)" by blast
          then obtain u where "map_of \<delta> w = Some u" by (auto dest: weak_map_of_SomeI)
          with typed map_of_SomeD[OF this] i kp show ?thesis by simp
        qed
        have sound_i: "pat_sound \<Gamma> \<eta> \<rho> (node (?ps ! i)) (?\<sigma>s ! i) \<Delta>'' (?us ! i)"
          if i: "i < length ?ps" and chk: "check_pat_at \<Sigma> \<Gamma> (?ps ! i) (?\<sigma>s ! i) = Ok \<Delta>''" for i \<Delta>''
        proof (rule IH[OF _ chk])
          show "size (node (?ps ! i)) < size p" unfolding PatDict by (intro size_sub_pat(3) nth_mem i)
          show "wf_ty \<Sigma> (?\<sigma>s ! i)" using wf\<sigma>' i by simp
          show "\<turnstile> ?us ! i : Ty (inst \<eta> (?\<sigma>s ! i))" using us_typed i by simp
        qed
        have len: "length ?ps = length ?\<sigma>s" and len_us: "length ?ps = length ?us"
          and wf: "\<forall>\<sigma>'' \<in> set ?\<sigma>s. wf_ty \<Sigma> \<sigma>''"
          using wf\<sigma>' by simp_all
        have sound_all: "\<forall>i < length ?ps. \<forall>\<Delta>''. check_pat_at \<Sigma> \<Gamma> (?ps ! i) (?\<sigma>s ! i) = Ok \<Delta>''
        \<longrightarrow> pat_sound \<Gamma> \<eta> \<rho> (node (?ps ! i)) (?\<sigma>s ! i) \<Delta>'' (?us ! i)"
        using sound_i by blast
        note seq = pattern_bindings_sound[OF pb len len_us sound_all wf\<Gamma> wf check_bound_once_Ok[OF cb] refl]
        have "map (\<lambda>(w, p). match \<rho> (node p) (the (map_of \<delta> w))) kps
              = map (\<lambda>(p, u). match \<rho> (node p) u) (zip ?ps ?us)"
          by (induction kps) auto
        then have m: "match \<rho> (PatDict kps) v
                      = foldr seq_compose_match (map (\<lambda>(p, u). match \<rho> (node p) u) (zip ?ps ?us)) (Match fmempty)"
          using True by (simp add: \<delta> match_dict_foldr)
        show ?thesis
          unfolding pat_sound_def
        proof (intro conjI allI impI)
          show "\<And>\<kappa>. match \<rho> (PatDict kps) v = MatchAborts \<kappa> \<Longrightarrow> \<not> prevented \<kappa>" using seq(1) unfolding m by blast
        next
          assume "match \<rho> (PatDict kps) v = NoMatch"
          from seq(2)[OF this[unfolded m]] have "kps \<noteq> []" by auto
          then show "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatDict kps)))" by (rule other)
        next
          fix \<rho>'
          assume "match \<rho> (PatDict kps) v = Match \<rho>'"
          from seq(3)[OF this[unfolded m]] show "fmdom' \<rho>' = fmdom' \<Delta>'"
            and "\<And>x \<sigma>''. fmlookup \<Delta>' x = Some \<sigma>'' \<Longrightarrow> \<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>'')"
            by blast+
          show "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<sigma> (PatDict kps)))" using v by (simp add: \<sigma>s)
        qed
      qed
    next
      fix \<sigma>
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = None" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      note nonunion = disjuncts_nonunion[OF \<sigma>]
      from f have nondict: "\<forall>\<sigma>'. \<sigma> \<noteq> TyDict \<sigma>'" and no_dict: "\<not> has_dict_values \<Sigma> \<sigma>"
        by (auto split: ty.splits if_splits)
      have "match \<rho> (PatDict kps) v = NoMatch"
      proof (cases v)
        case (VDict \<delta>)
        from dict_has_values[OF v[unfolded VDict]] no_dict show ?thesis by blast
      qed simp_all
      with v nondict show "match \<rho> (PatDict kps) v = NoMatch \<and> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatDict kps)))"
        by (simp add: remaining_dict[OF nonunion])
    qed
  next
    case (PatConstr q a)
    obtain ps kps where a: "a = (ps, kps)" by (cases a)
    note prems = less.prems[unfolded PatConstr a]
    from prems(1) obtain C where cls: "check_pattern_class \<Gamma> q = Ok C" by (auto simp: bind_sum_Ok)
    let ?f = "\<lambda>\<sigma>. case instance_at \<Sigma> C \<sigma> of
                Instance \<sigma>s \<Rightarrow>
                  Some (pattern_bindings
                    (map2 (check_pat_at \<Sigma> \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s)))
              | NoInstance \<Rightarrow> None
              | Undetermined \<Rightarrow>
                  Some (Fail (Violates
                    (if instance_above \<Sigma> C \<sigma> = Undetermined then RuleInstanceAbove else RuleInstanceBelow)
                    (PatternClassUndetermined (short_name C) \<sigma>)))"
    from prems(1) cls
    have fm: "check_field_map (PatternArityMismatch (short_name C)) (UnknownFieldInPattern (short_name C))
                (field_names \<Sigma> C) (length ps) (map fst kps) = Ok ()"
      and cb: "check_bound_once (ps @ map snd kps) = Ok ()"
      and b: "bindings_at \<Sigma> \<Gamma> (PatConstr q (ps, kps)) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
      by (auto simp: bind_sum_Ok)
    let ?xs = "field_names \<Sigma> C" and ?n = "length ps" and ?fps = "field_patterns \<Sigma> C (ps, kps)"
    from check_pattern_class_dom[OF wf\<Gamma> cls] have C: "C |\<in>| fmdom \<Sigma>" and rn: "resolve_name \<Gamma> q = Some (Type C)"
      by auto
    from pattern_class_value[OF env cls] have range: "C \<noteq> range_class" by blast
    have cls_ok: "(do {
        u \<leftarrow> or_else NameError (fmlookup \<rho> (root q));
        ensure (u \<noteq> VUnbound) NameError;
        u' \<leftarrow> or_else AttributeError (resolve \<rho> q);
        ensure (\<not> is_opaque_builtin u') Excluded;
        or_else TypeError (class_of u') }) = Ok C"
      using pattern_class_value[OF env cls] by (auto simp: or_else_def ensure_def bind_sum_def)
    have distinct_xs: "distinct ?xs" using wf_class_table_distinct[OF wf_class_table C] .
    from check_field_map_Ok[OF fm] have len_kps: "?n + length kps = length ?xs"
      and keys: "set (map fst kps) = set (drop ?n ?xs)"
      by auto
    from field_patterns_eq[OF distinct_xs len_kps keys]
    have fps: "?fps = ps @ map (\<lambda>x. the (map_of kps x)) (drop ?n ?xs)" and distinct_keys: "distinct (map fst kps)"
      by auto
    have len_fps: "length ?fps = length ?xs" using fps len_kps by simp
    have set_fps: "set ?fps = set ps \<union> set (map snd kps)"
      using field_patterns_cover(2)[OF distinct_xs len_kps keys] by simp
    have n_le: "?n \<le> length ?xs" using len_kps by simp
    show ?thesis
      unfolding PatConstr a
    proof (rule pat_sound_lift[OF prems(1) b _ _ _ env prems(3, 4)])
      fix \<sigma> \<Delta>'
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')"
      then obtain \<sigma>s where inst: "instance_at \<Sigma> C \<sigma> = Instance \<sigma>s"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ?fps (field_types \<Sigma> C \<sigma>s)) = Ok \<Delta>'"
        by (auto split: instances.splits)
      have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" using disjuncts_wf[OF prems(3) \<sigma>] by simp
      have wfC: "wf_ty \<Sigma> (TyClass C \<sigma>s)" by (rule instance_at_class_wf[OF wf_class_table wf\<sigma> inst C])
      have "\<forall>\<sigma>' \<in> set (field_types \<Sigma> C \<sigma>s). wf_ty \<Sigma> \<sigma>'" using field_types_wf[OF wf_class_table wfC] by blast
      moreover have "length ?fps = length (field_types \<Sigma> C \<sigma>s)" by (simp only: length_field_types len_fps)
      ultimately show "fmdom' \<Delta>' = binds (PatConstr q (ps, kps)) \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)"
        using pattern_bindings_check_wf[OF pb _ wf\<Gamma>] set_fps by auto
    next
      fix \<sigma> \<Delta>'
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = Some (Ok \<Delta>')" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      note nonunion = disjuncts_nonunion[OF \<sigma>]
      have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" using disjuncts_wf[OF prems(3) \<sigma>] by simp
      from f obtain \<sigma>s where inst: "instance_at \<Sigma> C \<sigma> = Instance \<sigma>s"
        and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ?fps (field_types \<Sigma> C \<sigma>s)) = Ok \<Delta>'"
        by (auto split: instances.splits)
      have wfC: "wf_ty \<Sigma> (TyClass C \<sigma>s)" by (rule instance_at_class_wf[OF wf_class_table wf\<sigma> inst C])
      let ?fts = "field_types \<Sigma> C \<sigma>s"
      have len_fts: "length ?fps = length ?fts" by (simp only: length_field_types len_fps)
      have wf_fts: "\<forall>\<sigma>' \<in> set ?fts. wf_ty \<Sigma> \<sigma>'" using field_types_wf[OF wf_class_table wfC] by blast
      (* Value not matched: at the remaining type, the disjunct itself *)
      have remaining_other: "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatConstr q (ps, kps))))"
        if "\<not> (\<Sigma> \<turnstile> \<sigma> <: TyClass C \<sigma>s
                \<and> (\<forall>(p, \<sigma>') \<in> set (zip ?fps ?fts). remaining \<Sigma> \<Gamma> \<sigma>' (node p) = TyPrim Never))"
      proof -
        have "remaining \<Sigma> \<Gamma> \<sigma> (PatConstr q (ps, kps)) = \<sigma>"
          unfolding remaining_constr[OF nonunion rn] inst instances.case by (rule if_not_P[OF that])
        with v show ?thesis by simp
      qed
      (* Disjunct below the instance: the value an object whose class has C as an ancestor *)
      have below: "\<exists>D zvs. v = VObject D zvs \<and> C \<in> set (ancestors \<Sigma> D)" if sub: "\<Sigma> \<turnstile> \<sigma> <: TyClass C \<sigma>s"
      proof -
        from inst_subty[OF wf_class_table sub] wf\<sigma> wfC have "\<Sigma> \<turnstile> inst \<eta> \<sigma> <: inst \<eta> (TyClass C \<sigma>s)" by blast
        with v inst_wf[OF wf\<eta> wfC] have vC: "\<turnstile> v : Ty (TyClass C (map (inst \<eta>) \<sigma>s))" by (auto intro: ValSub)
        from wf_object_type[OF vC] obtain D zvs where vD: "v = VObject D zvs" by (cases v) auto
        from wf_object[OF vC[unfolded vD]] obtain \<upsilon>s where "\<Sigma> \<turnstile> TyClass D \<upsilon>s <: TyClass C (map (inst \<eta>) \<sigma>s)"
          and "wf_ty \<Sigma> (TyClass D \<upsilon>s)"
          by blast
        from subty_class_class(1)[OF wf_class_table this(1) refl refl] this(2) vD show ?thesis by auto
      qed
      show "pat_sound \<Gamma> \<eta> \<rho> (PatConstr q (ps, kps)) \<sigma> \<Delta>' v"
      proof (cases "\<exists>D zvs. v = VObject D zvs \<and> C \<in> set (ancestors \<Sigma> D)")
        case False
        then have no: "match \<rho> (PatConstr q (ps, kps)) v = NoMatch" by (cases v) (auto simp: cls_ok)
        from below False have "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatConstr q (ps, kps))))"
          by (intro remaining_other) blast
        with no show ?thesis by (simp add: pat_sound_def)
      next
        case True
        then obtain D zvs where vD: "v = VObject D zvs" and anc: "C \<in> set (ancestors \<Sigma> D)" by blast
        from wf_object[OF v[unfolded vD]] obtain \<upsilon>s where wfD: "wf_ty \<Sigma> (TyClass D \<upsilon>s)"
          and names: "map fst zvs = field_names \<Sigma> D"
          and typed: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd zvs) (field_types \<Sigma> D \<upsilon>s)"
          and subD: "\<Sigma> \<turnstile> TyClass D \<upsilon>s <: inst \<eta> \<sigma>"
          by blast
        have D: "D |\<in>| fmdom \<Sigma>" using wfD by simp
        have below: "\<Sigma> \<turnstile> TyClass D \<upsilon>s <: inst \<eta> (TyClass C \<sigma>s)"
          by (rule instance_at_sub[OF inst nonunion wf\<sigma> C subD wfD anc])
        have wfC\<eta>: "wf_ty \<Sigma> (TyClass C (map (inst \<eta>) \<sigma>s))" using inst_wf[OF wf\<eta> wfC] by simp
        have vC: "\<turnstile> v : Ty (inst \<eta> (TyClass C \<sigma>s))"
          using ValObj[OF wfD names typed] below wfC\<eta> unfolding vD by (auto intro: ValSub)
        (* Field names of C: the first fields of D *)
        from instantiate_fields_ancestor[OF wf_class_table D anc, of \<upsilon>s] obtain rest
          where fieldsD: "instantiate (fields \<Sigma> D) \<upsilon>s = instantiate (fields \<Sigma> C) (instantiated_ancestor \<Sigma> D \<upsilon>s C) @ rest"
          by blast
        have "field_names \<Sigma> D = field_names \<Sigma> C @ map fst rest"
          using map_fst_instantiate[of \<Sigma> D \<upsilon>s] map_fst_instantiate[of \<Sigma> C] unfolding fieldsD by simp
        then have names_sub: "set ?xs \<subseteq> set (map fst zvs)" using names by simp
        (* Value of each field of C, at the instance of the field type *)
        let ?g = "\<lambda>y. the (map_of zvs y)"
        let ?us = "map ?g ?xs"
        have us_typed: "\<turnstile> ?us ! i : Ty (inst \<eta> (?fts ! i))" if i: "i < length ?xs" for i
        proof -
          let ?instC = "instantiate (fields \<Sigma> C) (map (inst \<eta>) \<sigma>s)"
          have keysC: "map fst ?instC = ?xs" by (rule map_fst_instantiate)
          have len_inst: "length ?instC = length ?xs" using keysC by (metis length_map)
          have "map_of ?instC (fst (?instC ! i)) = Some (snd (?instC ! i))"
            using distinct_xs i keysC len_inst by (intro map_of_nth) simp_all
          moreover have "fst (?instC ! i) = ?xs ! i"
          proof -
            have "i < length ?instC" using i len_inst by simp
            from nth_map[OF this, of fst] show ?thesis unfolding keysC by (rule sym)
          qed
          moreover have "snd (?instC ! i) = inst \<eta> (?fts ! i)"
          proof -
            have eq: "map snd ?instC = map (inst \<eta>) ?fts"
              using inst_field_types[OF wf_class_table wfC] by (simp add: field_types_def)
            have "snd (?instC ! i) = map snd ?instC ! i" using i len_inst by (simp add: nth_map)
            also have "\<dots> = map (inst \<eta>) ?fts ! i" unfolding eq ..
            also have "\<dots> = inst \<eta> (?fts ! i)" using i len_fts len_fps by (simp add: nth_map)
            finally show ?thesis .
          qed
          ultimately have lookC: "map_of ?instC (?xs ! i) = Some (inst \<eta> (?fts ! i))" by simp
          from subty_class_fields(1)[OF wf_class_table below[simplified] refl refl D lookC] obtain \<tau>'
            where lookD: "map_of (instantiate (fields \<Sigma> D) \<upsilon>s) (?xs ! i) = Some \<tau>'"
            and equiv: "\<Sigma> \<turnstile> \<tau>' \<approx> inst \<eta> (?fts ! i)"
            by blast
          have "map fst zvs = map fst (instantiate (fields \<Sigma> D) \<upsilon>s)" using names map_fst_instantiate by simp
          from map_of_list_all2[OF this typed[unfolded field_types_def] lookD] obtain u
            where u: "map_of zvs (?xs ! i) = Some u" and "\<turnstile> u : Ty \<tau>'"
            by blast
          have "wf_ty \<Sigma> (inst \<eta> (?fts ! i))" by (rule fields_wf[OF wf_class_table wfC\<eta> map_of_SomeD[OF lookC]])
          with \<open>\<turnstile> u : Ty \<tau>'\<close> equiv have "\<turnstile> u : Ty (inst \<eta> (?fts ! i))" by (auto intro: ValSub)
          with u i show ?thesis by simp
        qed
        have sound_i: "pat_sound \<Gamma> \<eta> \<rho> (node (?fps ! i)) (?fts ! i) \<Delta>'' (?us ! i)"
          if i: "i < length ?fps" and chk: "check_pat_at \<Sigma> \<Gamma> (?fps ! i) (?fts ! i) = Ok \<Delta>''" for i \<Delta>''
        proof (rule IH[OF _ chk])
          show "size (node (?fps ! i)) < size p"
            unfolding PatConstr a by (intro size_sub_pat(4)[where C = C] nth_mem i)
          show "wf_ty \<Sigma> (?fts ! i)" using wf_fts i len_fts by simp
          show "\<turnstile> ?us ! i : Ty (inst \<eta> (?fts ! i))" using us_typed i len_fps by simp
        qed
        (* Variables bound once across the field patterns, a permutation of the sub-patterns *)
        have once: "distinct (concat (map (sorted_list_of_set \<circ> binds \<circ> node) ?fps))"
        proof -
          let ?h = "sorted_list_of_set \<circ> binds_pat \<circ> node"
          have "mset (map (\<lambda>x. the (map_of kps x)) (drop ?n ?xs)) = mset (map snd kps)"
            using kw_perm[OF distinct_keys _ keys] distinct_xs by simp
          then have "mset (map ?h (map (\<lambda>x. the (map_of kps x)) (drop ?n ?xs))) = mset (map ?h (map snd kps))"
            by (metis mset_map)
          then have "mset (map ?h ?fps) = mset (map ?h (ps @ map snd kps))"
            unfolding fps by (simp only: map_append mset_append)
          from distinct_concat_perm[OF this] check_bound_once_Ok[OF cb] show ?thesis by simp
        qed
        have len_us: "length ?fps = length ?us" by (simp only: length_map len_fps)
        (* Runtime sequence: the positional sub-patterns, then the keyword ones in their order *)
        let ?pus = "zip ps (map ?g (take ?n ?xs)) @ map (\<lambda>(y, p). (p, ?g y)) kps"
        have len_take: "length ps = length (map ?g (take ?n ?xs))" using n_le by simp
        have pus: "set ?pus = set (zip ?fps ?us)"
        proof -
          have split: "map ?g ?xs = map ?g (take ?n ?xs) @ map ?g (drop ?n ?xs)" by (metis append_take_drop_id map_append)
          have "zip ?fps ?us
                = zip ps (map ?g (take ?n ?xs)) @ zip (map (\<lambda>x. the (map_of kps x)) (drop ?n ?xs)) (map ?g (drop ?n ?xs))"
            unfolding fps by (subst split) (rule zip_append[OF len_take])
          moreover have "zip (map (\<lambda>x. the (map_of kps x)) (drop ?n ?xs)) (map ?g (drop ?n ?xs))
                         = map (\<lambda>x. (the (map_of kps x), ?g x)) (drop ?n ?xs)"
            by (simp add: zip_map_map zip_same_conv_map)
          ultimately show ?thesis using kw_set[OF distinct_keys keys, of ?g] by simp
        qed
        have sound_all: "\<forall>i < length ?fps. \<forall>\<Delta>''. check_pat_at \<Sigma> \<Gamma> (?fps ! i) (?fts ! i) = Ok \<Delta>''
        \<longrightarrow> pat_sound \<Gamma> \<eta> \<rho> (node (?fps ! i)) (?fts ! i) \<Delta>'' (?us ! i)"
        using sound_i by blast
        note seq = pattern_bindings_sound[OF pb len_fts len_us sound_all wf\<Gamma> wf_fts once pus]
        have field_map: "field_map C ps kps \<noteq> None" using len_kps keys by (simp add: field_map_def Let_def)
        have m: "match \<rho> (PatConstr q (ps, kps)) v
                 = foldr seq_compose_match (map (\<lambda>(p, u). match \<rho> (node p) u) ?pus) (Match fmempty)"
        proof -
          have kw_eq: "map (\<lambda>(p, u). match \<rho> (node p) u) (map (\<lambda>(y, p). (p, ?g y)) kps)
                       = map (\<lambda>(y, p). match \<rho> (node p) (?g y)) kps"
            by (induction kps) auto
          have "match \<rho> (PatConstr q (ps, kps)) v
                = seq_compose_match (match_all \<rho> ps (map ?g (take ?n ?xs))) (match_kws \<rho> kps zvs)"
            using anc range field_map names_sub by (simp add: vD cls_ok Let_def)
          also have "\<dots> = seq_compose_match
              (foldr seq_compose_match (map (\<lambda>(p, u). match \<rho> (node p) u) (zip ps (map ?g (take ?n ?xs)))) (Match fmempty))
              (foldr seq_compose_match (map (\<lambda>(y, p). match \<rho> (node p) (?g y)) kps) (Match fmempty))"
            by (simp only: match_all_foldr[OF len_take] match_kws_foldr)
          also have "\<dots> = foldr seq_compose_match
              (map (\<lambda>(p, u). match \<rho> (node p) u) (zip ps (map ?g (take ?n ?xs)))
               @ map (\<lambda>(y, p). match \<rho> (node p) (?g y)) kps) (Match fmempty)"
            by (simp only: foldr_match_append)
          also have "\<dots> = foldr seq_compose_match (map (\<lambda>(p, u). match \<rho> (node p) u) ?pus) (Match fmempty)"
            by (simp only: map_append kw_eq)
          finally show ?thesis .
        qed
        show ?thesis
          unfolding pat_sound_def
        proof (intro conjI allI impI)
          show "\<And>\<kappa>. match \<rho> (PatConstr q (ps, kps)) v = MatchAborts \<kappa> \<Longrightarrow> \<not> prevented \<kappa>"
            using seq(1) unfolding m by blast
        next
          assume "match \<rho> (PatConstr q (ps, kps)) v = NoMatch"
          from seq(2)[OF this[unfolded m]] obtain i where i: "i < length ?fps"
            and no_i: "match \<rho> (node (?fps ! i)) (?us ! i) = NoMatch"
            by blast
          from pattern_bindings_check[OF pb len_fts i] obtain \<Delta>''
            where "check_pat_at \<Sigma> \<Gamma> (?fps ! i) (?fts ! i) = Ok \<Delta>''"
            by blast
          from sound_i[OF i this] no_i
          have vi: "\<turnstile> ?us ! i : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> (?fts ! i) (node (?fps ! i))))"
            by (simp add: pat_sound_def)
          have "\<not> (\<forall>(p, \<sigma>') \<in> set (zip ?fps ?fts). remaining \<Sigma> \<Gamma> \<sigma>' (node p) = TyPrim Never)"
          proof
            assume "\<forall>(p, \<sigma>') \<in> set (zip ?fps ?fts). remaining \<Sigma> \<Gamma> \<sigma>' (node p) = TyPrim Never"
            moreover have "(?fps ! i, ?fts ! i) \<in> set (zip ?fps ?fts)" using i len_fts by (auto simp: in_set_zip)
            ultimately have "remaining \<Sigma> \<Gamma> (?fts ! i) (node (?fps ! i)) = TyPrim Never" by auto
            with vi wf_val_never show False by simp
          qed
          then show "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatConstr q (ps, kps))))" by (intro remaining_other) blast
        next
          fix \<rho>'
          assume "match \<rho> (PatConstr q (ps, kps)) v = Match \<rho>'"
          from seq(3)[OF this[unfolded m]] show "fmdom' \<rho>' = fmdom' \<Delta>'"
            and "\<And>x \<sigma>'. fmlookup \<Delta>' x = Some \<sigma>' \<Longrightarrow> \<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>')"
            by blast+
          from instance_at_comparable[OF inst nonunion wf\<sigma> C]
          have "meet \<Sigma> \<sigma> (TyClass C \<sigma>s) = \<sigma> \<or> meet \<Sigma> \<sigma> (TyClass C \<sigma>s) = TyClass C \<sigma>s"
            by (auto simp: meet_class[OF nonunion])
          with v vC show "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<sigma> (PatConstr q (ps, kps))))"
            by (auto simp: matched_as_constr[OF nonunion rn] inst)
        qed
      qed
    next
      fix \<sigma>
      assume \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and f: "?f \<sigma> = None" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
      note nonunion = disjuncts_nonunion[OF \<sigma>]
      have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" using disjuncts_wf[OF prems(3) \<sigma>] by simp
      from f have none: "instance_at \<Sigma> C \<sigma> = NoInstance" by (auto split: instances.splits)
      have "match \<rho> (PatConstr q (ps, kps)) v = NoMatch"
      proof (cases v)
        case (VObject D zvs)
        from wf_object[OF v[unfolded VObject]] obtain \<upsilon>s where wfD: "wf_ty \<Sigma> (TyClass D \<upsilon>s)"
          and subD: "\<Sigma> \<turnstile> TyClass D \<upsilon>s <: inst \<eta> \<sigma>"
          by blast
        from instance_at_none[OF none nonunion wf\<sigma> C range subD wfD] show ?thesis unfolding VObject
          by (auto simp: cls_ok)
      qed (simp_all add: cls_ok)
      with v none
      show "match \<rho> (PatConstr q (ps, kps)) v = NoMatch
            \<and> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatConstr q (ps, kps))))"
        by (simp add: remaining_constr[OF nonunion rn])
    qed
  qed
qed

lemmas check_pat_at_sound = check_pat_sound[OF check_pat_at_node]

subsection \<open>Dispatch over the cases of a match statement\<close>

lemma match_cases_length: "match_cases \<Sigma> \<Gamma> \<tau> L ps = Ok (\<Delta>s, \<tau>', L') \<Longrightarrow> length \<Delta>s = length ps"
  by (induction ps arbitrary: \<tau> L \<Delta>s) (auto simp: bind_sum_Ok split: prod.splits)

(* Dispatch of a value over the cases of a match checked at its type: a case is chosen, binding its variables
   below the bindings of its pattern; or no case matches, and the value is at the remaining type; or an abort
   which is not prevented *)
lemma dispatch_sound:
  "\<lbrakk> match_cases \<Sigma> \<Gamma> \<tau> L (map fst cases) = Ok (\<Delta>s, \<tau>', L') ; \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_ty \<Sigma> \<tau> ; \<turnstile> v : Ty (inst \<eta> \<tau>) \<rbrakk>
  \<Longrightarrow> (\<exists>i < length cases. \<exists>\<rho>'. dispatch \<rho> v cases = Val (\<rho>', snd (cases ! i))
         \<and> fmdom \<rho>' |\<subseteq>| fmdom (\<Delta>s ! i) \<and> \<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> (\<Delta>s ! i))
      \<or> (dispatch \<rho> v cases = Val (fmempty, At no_pos StmtPass) \<and> \<turnstile> v : Ty (inst \<eta> \<tau>'))
      \<or> (\<exists>\<kappa>. dispatch \<rho> v cases = Aborts \<kappa> \<and> \<not> prevented \<kappa>)"
proof (induction "cases" arbitrary: \<tau> L \<Delta>s)
  case Nil
  then show ?case by simp
next
  case (Cons c "cases")
  obtain p s where c: "c = (p, s)" by (cases c)
  from Cons.prems(1) obtain \<Delta> L\<^sub>1 \<Delta>s' where chk: "check_pat_at \<Sigma> \<Gamma> p \<tau> = Ok \<Delta>"
    and mc: "match_cases \<Sigma> \<Gamma> (remaining \<Sigma> \<Gamma> \<tau> (node p)) L\<^sub>1 (map fst cases) = Ok (\<Delta>s', \<tau>', L')"
    and \<Delta>s: "\<Delta>s = fmmap Ty \<Delta> # \<Delta>s'"
    unfolding c by (auto simp: bind_sum_Ok split: prod.splits)
  note sound = check_pat_at_sound[OF chk Cons.prems(2-4), unfolded pat_sound_def]
  from match_cases_wf[OF wf_class_table wf_env_wf_cxt[OF Cons.prems(2)] Cons.prems(3) Cons.prems(1), of "fmmap Ty \<Delta>"]
  have wf\<Delta>: "wf_cxt \<Sigma> (fmmap Ty \<Delta>)" by (simp add: \<Delta>s)
  show ?case
  proof (cases "match \<rho> (node p) v")
    case (Match \<rho>')
    with sound have dom: "fmdom' \<rho>' = fmdom' \<Delta>"
      and look: "\<forall>x \<sigma>. fmlookup \<Delta> x = Some \<sigma> \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>))"
      by auto
    have dom': "fmdom \<rho>' = fmdom \<Delta>" using dom by (simp add: fmdom'_alt_def fset_inject)
    have "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> fmmap Ty \<Delta>"
    proof (rule wf_env_add[OF Cons.prems(2)])
      show "fmdom \<rho>' |\<subseteq>| fmdom (fmmap Ty \<Delta>)" using dom' by simp
      show "wf_cxt \<Sigma> (fmmap Ty \<Delta>)" by (rule wf\<Delta>)
      fix x \<theta>
      assume "fmlookup (fmmap Ty \<Delta>) x = Some \<theta>"
      then obtain \<sigma> where "fmlookup \<Delta> x = Some \<sigma>" and \<theta>: "\<theta> = Ty \<sigma>" by auto
      with look obtain u where "fmlookup \<rho>' x = Some u" and "\<turnstile> u : Ty (inst \<eta> \<sigma>)" by blast
      then show "\<exists>u. fmlookup (\<rho> \<otimes> \<rho>') x = Some u \<and> \<turnstile> u : inst_entry \<eta> \<theta>" by (auto simp: \<theta> fmdomI)
    qed
    with Match dom' show ?thesis by (auto simp: c \<Delta>s intro!: exI[of _ 0])
  next
    case NoMatch
    with sound have v': "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (node p)))" by auto
    have wf': "wf_ty \<Sigma> (remaining \<Sigma> \<Gamma> \<tau> (node p))" using remaining_wf[OF Cons.prems(3), of \<Gamma> "node p"] by simp
    from Cons.IH[OF mc Cons.prems(2) wf' v'] show ?thesis
    proof (elim disjE exE conjE)
      fix i \<rho>'
      assume "i < length cases" and "dispatch \<rho> v cases = Val (\<rho>', snd (cases ! i))"
        and "fmdom \<rho>' |\<subseteq>| fmdom (\<Delta>s' ! i)" and "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> (\<Delta>s' ! i)"
      then show ?thesis using NoMatch by (auto simp: c \<Delta>s intro!: exI[of _ "Suc i"])
    qed (auto simp: c \<Delta>s NoMatch)
  next
    case (MatchAborts \<kappa>)
    with sound show ?thesis by (auto simp: c)
  qed
qed

end

end
