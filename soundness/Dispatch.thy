(* Soundness of pattern matching and of dispatch over the cases of a match statement *)
theory Dispatch
  imports Calls
begin

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

(* Substitutions agreeing on the type variables of \<sigma> up to equivalence, equivalent at \<sigma> *)
lemma subst_equiv_vars:
  "\<forall>\<alpha> \<in> fv \<sigma>. \<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyVar \<alpha>) \<approx> subst \<tau>s' \<alpha>s (TyVar \<alpha>)
  \<Longrightarrow> \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> \<approx> subst \<tau>s' \<alpha>s \<sigma>"
proof (induction \<sigma>)
  case (TyTuple \<sigma>s)
  have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> \<approx> subst \<tau>s' \<alpha>s \<sigma>" if "\<sigma> \<in> set \<sigma>s" for \<sigma>
    using TyTuple.IH[OF that] TyTuple.prems that by auto
  then show ?case
    by (auto intro!: SubtyTuple list.rel_refl_strong simp: subtys_list_all2 list_all2_map1 list_all2_map2)
next
  case (TyCallable \<sigma>s \<sigma>)
  have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma>' \<approx> subst \<tau>s' \<alpha>s \<sigma>'" if "\<sigma>' \<in> set \<sigma>s" for \<sigma>'
    using TyCallable.IH(1)[OF that] TyCallable.prems that by auto
  with TyCallable.IH(2) TyCallable.prems show ?case
    by (auto intro!: SubtyCallable list.rel_refl_strong simp: subtys_list_all2 list_all2_map1 list_all2_map2)
next
  case (TyClass C \<sigma>s)
  have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> \<approx> subst \<tau>s' \<alpha>s \<sigma>" if "\<sigma> \<in> set \<sigma>s" for \<sigma>
    using TyClass.IH[OF that] TyClass.prems that by auto
  then show ?case
    by (auto intro!: SubtyClass list.rel_refl_strong simp: subtys_list_all2 list_all2_map1 list_all2_map2)
qed (auto intro: subty_subtys.intros)

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

lemma disjunct_subty: "\<sigma> \<in> set (disjuncts \<tau>) \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>"
  by (induction \<tau>) (auto intro: SubtyRefl SubtyUnionLeft SubtyUnionRight)

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

lemma eq_lit_refl: "eq_lit l l = Val True \<or> (\<exists>\<kappa>. eq_lit l l = Aborts \<kappa>)"
  by (cases l) auto

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

lemma fold_fmadd_dom': "fmdom' (fold fmadd \<Delta>s \<Delta>) = fmdom' \<Delta> \<union> \<Union> (fmdom' ` set \<Delta>s)"
  by (induction \<Delta>s arbitrary: \<Delta>) auto

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
lemma fold_fmadd_lookup:
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

lemma foldr_fmadd_lookup:
  "\<lbrakk> i < length \<Delta>s ; x \<in> fmdom' (\<Delta>s ! i) ; \<forall>j < length \<Delta>s. j \<noteq> i \<longrightarrow> x \<notin> fmdom' (\<Delta>s ! j) ; x \<notin> fmdom' \<Delta> \<rbrakk>
  \<Longrightarrow> fmlookup (foldr fmadd \<Delta>s \<Delta>) x = fmlookup (\<Delta>s ! i) x"
proof (induction \<Delta>s arbitrary: i)
  case (Cons \<Delta>' \<Delta>s)
  show ?case
  proof (cases i)
    case 0
    with Cons.prems have "x \<notin> \<Union> (fmdom' ` set \<Delta>s)" by (intro notin_others) simp
    with Cons.prems have "x \<notin> fmdom' (foldr fmadd \<Delta>s \<Delta>)" by (simp add: foldr_fmadd_dom')
    with 0 show ?thesis by (simp add: fmdom'_alt_def)
  next
    case (Suc i')
    with Cons.prems have "x \<notin> fmdom' \<Delta>'" by fastforce
    moreover from Cons.prems Suc have "fmlookup (foldr fmadd \<Delta>s \<Delta>) x = fmlookup (\<Delta>s ! i') x" by (auto intro!: Cons.IH)
    moreover from Cons.prems Suc have "x \<in> fmdom' (foldr fmadd \<Delta>s \<Delta>)" by (auto simp: foldr_fmadd_dom')
    ultimately show ?thesis using Suc by (simp add: fmdom'_alt_def)
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

(* Pattern checked at a type: checked at each disjunct *)
lemma check_pat_disjunct:
  "\<lbrakk> check_pat \<Sigma> \<Gamma> p \<tau> = Ok \<Delta> ; \<sigma> \<in> set (disjuncts \<tau>) \<rbrakk> \<Longrightarrow> \<exists>\<Delta>'. check_pat \<Sigma> \<Gamma> p \<sigma> = Ok \<Delta>'"
proof (induction \<tau> arbitrary: \<Delta>)
  case (TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2)
  from check_pat_union(1)[OF TyUnion.prems(1) refl] obtain \<Delta>\<^sub>1 \<Delta>\<^sub>2 where "check_pat \<Sigma> \<Gamma> p \<sigma>\<^sub>1 = Ok \<Delta>\<^sub>1"
    and "check_pat \<Sigma> \<Gamma> p \<sigma>\<^sub>2 = Ok \<Delta>\<^sub>2"
    by blast
  with TyUnion.IH TyUnion.prems(2) show ?case by auto
qed auto

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
    using subst_subty(1)[OF wf_class_table join_upper(1)] subst_subty(1)[OF wf_class_table join_upper(2)]
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
    using subst_subty(1)[OF wf_class_table join_upper(1)] subst_subty(1)[OF wf_class_table join_upper(2)]
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

lemma wf_val_float: "\<turnstile> v : Ty (TyPrim float) \<Longrightarrow> \<exists>l. v = VLit l \<and> is_number (VLit l)"
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
    and anc: "C \<in> set (ancestors \<Sigma> D)" and closed: "closed_inst \<eta>"
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
      have "map (inst \<eta>) \<sigma>s = instantiated_ancestor \<Sigma> E (map (inst \<eta>) \<sigma>s\<^sub>E) C"
        unfolding \<sigma>s using instantiated_ancestor_subst[OF wf_class_table E len\<^sub>E CE] by simp
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
        have "\<Sigma> \<turnstile> subst ?\<tau>s' ?\<alpha>s (?\<rho>s ! j) \<approx> inst \<eta> (\<sigma>s\<^sub>E ! j)" using equiv' j by (auto simp: list_all2_conv_all_nth)
        from match_args_unique[OF wf_class_table mj lookj _ _ this] wf\<rho>s wf\<sigma>s\<^sub>E j len
        have "\<Sigma> \<turnstile> subst ?\<tau>s' ?\<alpha>s (TyVar \<alpha>) \<approx> inst \<eta> (\<sigma>s ! i)" by auto
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
      with equiv' have "\<Sigma> \<turnstile> subst ?\<tau>s' ?\<alpha>s (?\<rho>s ! i) \<approx> inst \<eta> (\<sigma>s\<^sub>E ! i)" and "i < length \<sigma>s\<^sub>E"
        by (auto simp: list_all2_conv_all_nth)
      with match_args_clash[OF wf_class_table clash_i] wf\<rho>s wf\<sigma>s\<^sub>E i show False by auto
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
  "\<not> is_union \<tau> \<Longrightarrow> matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q a)
    = (case instance_at \<Sigma> (pattern_class \<Gamma> q) \<tau> of
         Instance \<sigma>s \<Rightarrow> meet \<Sigma> \<tau> (TyClass (pattern_class \<Gamma> q) \<sigma>s) | _ \<Rightarrow> TyPrim Never)"
  by (cases \<tau>) (auto simp: Let_def)

lemma remaining_var: "\<not> is_union \<tau> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> (PatVar x) = TyPrim Never"
  by (cases \<tau>) auto

lemma remaining_wild: "\<not> is_union \<tau> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> PatWildcard = TyPrim Never"
  by (cases \<tau>) auto

lemma remaining_tuple_other: "\<lbrakk> \<not> is_union \<tau> ; \<forall>\<sigma>s. \<tau> \<noteq> TyTuple \<sigma>s \<rbrakk> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> (PatTuple ps) = \<tau>"
  by (cases \<tau>) auto

lemma remaining_list: "\<not> is_union \<tau> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> (PatList ps) = \<tau>"
  by (cases \<tau>) auto

lemma remaining_dict: "\<lbrakk> \<not> is_union \<tau> ; kps \<noteq> [] \<or> (\<forall>\<sigma>. \<tau> \<noteq> TyDict \<sigma>) \<rbrakk> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> (PatDict kps) = \<tau>"
  by (cases \<tau>; cases kps) auto

lemma remaining_constr:
  "\<not> is_union \<tau> \<Longrightarrow> remaining \<Sigma> \<Gamma> \<tau> (PatConstr q a)
    = (case instance_at \<Sigma> (pattern_class \<Gamma> q) \<tau> of
         Instance \<sigma>s \<Rightarrow>
           if \<Sigma> \<turnstile> \<tau> <: TyClass (pattern_class \<Gamma> q) \<sigma>s
              \<and> (\<forall>(p, \<sigma>) \<in> set (zip (field_patterns \<Sigma> (pattern_class \<Gamma> q) a)
                                 (field_types \<Sigma> (pattern_class \<Gamma> q) \<sigma>s)).
                   remaining \<Sigma> \<Gamma> \<sigma> (node p) = TyPrim Never)
           then TyPrim Never else \<tau>
       | _ \<Rightarrow> \<tau>)"
  by (cases \<tau>) (auto simp: Let_def)

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

lemma remaining_literal_literal:
  "remaining \<Sigma> \<Gamma> (TyLiteral l') (PatLiteral l) = (if l' = l then TyPrim Never else TyLiteral l')"
  by simp

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
definition pat_sound :: "cxt \<Rightarrow> (var \<times> ty) list \<Rightarrow> env \<Rightarrow> pat \<Rightarrow> ty \<Rightarrow> (var, ty) fmap \<Rightarrow> val \<Rightarrow> bool"
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
  with subst_subty(1)[OF wf_class_table sub] wf have "\<Sigma> \<turnstile> inst \<eta> \<upsilon> <: inst \<eta> \<sigma>'" by blast
  with u inst_wf[OF wf\<eta> wf] \<sigma>' show ?thesis by (auto intro: ValSub)
qed

(* Sequence of sub-patterns matched against values, each sound against its type: the sequence sound *)
lemma match_seq_sound:
  assumes pus: "set pus = set (zip fps us)" and len: "length fps = length us" "length fps = length \<Delta>s"
    and sound: "\<forall>i < length fps. pat_sound \<Gamma> \<eta> \<rho> (node (fps ! i)) (fts ! i) (\<Delta>s ! i) (us ! i)"
    and dom: "\<forall>i < length fps. fmdom' (\<Delta>s ! i) = binds (node (fps ! i))"
    and once: "distinct (concat (map (sorted_list_of_set \<circ> binds \<circ> node) fps))"
  defines "m \<equiv> foldr seq_compose_match (map (\<lambda>(p, u). match \<rho> (node p) u) pus) (Match fmempty)"
  shows "\<And>\<kappa>. m = MatchAborts \<kappa> \<Longrightarrow> \<not> prevented \<kappa>"
    and "m = NoMatch \<Longrightarrow> \<exists>i < length fps. match \<rho> (node (fps ! i)) (us ! i) = NoMatch"
    and "m = Match \<rho>' \<Longrightarrow> fmdom' \<rho>' = fmdom' (fold fmadd \<Delta>s fmempty)
      \<and> (\<forall>x \<upsilon>. fmlookup (fold fmadd \<Delta>s fmempty) x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>)))
      \<and> (\<forall>i < length fps. \<exists>\<rho>\<^sub>i. match \<rho> (node (fps ! i)) (us ! i) = Match \<rho>\<^sub>i)"
proof -
  let ?ms = "map (\<lambda>(p, u). match \<rho> (node p) u) pus"
  have index: "\<exists>i < length fps. p = fps ! i \<and> u = us ! i" if "(p, u) \<in> set pus" for p u
    using that pus len(1) by (auto simp: in_set_zip)
  have index': "(fps ! i, us ! i) \<in> set pus" if "i < length fps" for i
    using that pus len(1) by (auto simp: in_set_zip)
  have disjoint: "binds (node (fps ! i)) \<inter> binds (node (fps ! j)) = {}"
    if "i < length fps" and "j < length fps" and "i \<noteq> j" for i j
    using distinct_concat_nth[OF once, of i j] that finite_binds_pat by simp
  show "\<not> prevented \<kappa>" if "m = MatchAborts \<kappa>" for \<kappa>
  proof -
    from foldr_match_Aborts[OF that[unfolded m_def]] obtain p u where "(p, u) \<in> set pus"
      and "match \<rho> (node p) u = MatchAborts \<kappa>"
      by auto
    with index[OF this(1)] sound show ?thesis by (auto simp: pat_sound_def)
  qed
  show "\<exists>i < length fps. match \<rho> (node (fps ! i)) (us ! i) = NoMatch" if "m = NoMatch"
  proof -
    from foldr_match_NoMatch[OF that[unfolded m_def]] obtain p u where "(p, u) \<in> set pus"
      and "match \<rho> (node p) u = NoMatch"
      by auto
    with index[OF this(1)] show ?thesis by auto
  qed
  show "fmdom' \<rho>' = fmdom' (fold fmadd \<Delta>s fmempty)
      \<and> (\<forall>x \<upsilon>. fmlookup (fold fmadd \<Delta>s fmempty) x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>)))
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
      from sound[rule_format, OF i] at[OF j] have "fmdom' (\<rho>s ! j) = fmdom' (\<Delta>s ! i)
        \<and> (\<forall>x \<upsilon>. fmlookup (\<Delta>s ! i) x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup (\<rho>s ! j) x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>)))"
        unfolding pat_sound_def p u by blast
      with i p u show ?thesis by blast
    qed
    have matched: "\<exists>\<rho>\<^sub>i. match \<rho> (node (fps ! i)) (us ! i) = Match \<rho>\<^sub>i" if i: "i < length fps" for i
    proof -
      from index'[OF i] obtain j where "j < length pus" and "pus ! j = (fps ! i, us ! i)" by (auto simp: in_set_conv_nth)
      with at[OF this(1)] show ?thesis by auto
    qed
    have dom': "fmdom' \<rho>' = fmdom' (fold fmadd \<Delta>s fmempty)"
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
        unfolding UN_set_nth using len(1) by (simp add: case_prod_beta)
      also have "\<dots> = (\<Union>i \<in> {..<length \<Delta>s}. fmdom' (\<Delta>s ! i))" using dom len(2) by (intro SUP_cong) auto
      also have "\<dots> = fmdom' (fold fmadd \<Delta>s fmempty)" by (simp add: fold_fmadd_dom' UN_set_nth)
      finally show ?thesis .
    qed
    have look: "\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>)" if \<upsilon>: "fmlookup (fold fmadd \<Delta>s fmempty) x = Some \<upsilon>"
      for x \<upsilon>
    proof -
      from \<upsilon> have "x \<in> fmdom' (fold fmadd \<Delta>s fmempty)" by (simp add: fmlookup_dom'_iff)
      then obtain i where i: "i < length \<Delta>s" and xi: "x \<in> fmdom' (\<Delta>s ! i)"
        by (auto simp: fold_fmadd_dom' in_set_conv_nth)
      have others: "x \<notin> fmdom' (\<Delta>s ! k)" if "k < length \<Delta>s" and "k \<noteq> i" for k
        using disjoint[of i k] dom[rule_format, of i] dom[rule_format, of k] i that len(2) xi by auto
      from fold_fmadd_lookup[OF i xi] others \<upsilon> have \<upsilon>i: "fmlookup (\<Delta>s ! i) x = Some \<upsilon>" by auto
      from index'[of i] i len(2) obtain j where j: "j < length pus" and pj: "pus ! j = (fps ! i, us ! i)"
        by (auto simp: in_set_conv_nth)
      from at_i[OF j] pj obtain i' where i': "i' < length fps" and "fps ! i = fps ! i'" and "us ! i = us ! i'"
        and domj: "fmdom' (\<rho>s ! j) = fmdom' (\<Delta>s ! i')"
        and lookj: "\<forall>x \<upsilon>. fmlookup (\<Delta>s ! i') x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup (\<rho>s ! j) x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>))"
        by auto
      have "i' = i"
      proof (rule ccontr)
        assume "i' \<noteq> i"
        with others[of i'] i' len(2) have "x \<notin> fmdom' (\<Delta>s ! i')" by simp
        moreover have "x \<in> fmdom' (\<Delta>s ! i')"
          using dom[rule_format, of i] dom[rule_format, of i'] \<open>fps ! i = fps ! i'\<close> \<upsilon>i i i' len(2)
          by (auto simp: fmlookup_dom'_iff)
        ultimately show False ..
      qed
      with lookj \<upsilon>i obtain u where u: "fmlookup (\<rho>s ! j) x = Some u" and typed: "\<turnstile> u : Ty (inst \<eta> \<upsilon>)" by blast
      have agree: "fmlookup (\<rho>s ! k) x = fmlookup (\<rho>s ! j) x" if k: "k < length \<rho>s" and xk: "x \<in> fmdom' (\<rho>s ! k)" for k
      proof -
        from at_i[OF k[unfolded len\<rho>s]] obtain i'' where i'': "i'' < length fps" and pk: "fst (pus ! k) = fps ! i''"
          and uk: "snd (pus ! k) = us ! i''" and domk: "fmdom' (\<rho>s ! k) = fmdom' (\<Delta>s ! i'')"
          by blast
        with xk others i len(2) have "i'' = i" by (cases "i'' = i") auto
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

lemma check_pat_sound_aux:
  "\<lbrakk> \<Sigma>' = \<Sigma> ; check_pat \<Sigma>' \<Gamma> p \<tau> = Ok \<Delta> ; \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_ty \<Sigma> \<tau> ; fv \<tau> \<subseteq> fst ` set \<eta> ; \<turnstile> v : Ty (inst \<eta> \<tau>) \<rbrakk>
  \<Longrightarrow> pat_sound \<Gamma> \<eta> \<rho> p \<tau> \<Delta> v"
  "\<lbrakk> \<Sigma>' = \<Sigma> ; check_pat_at \<Sigma>' \<Gamma> p' \<tau>' = Ok \<Delta>' ; \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_ty \<Sigma> \<tau>' ; fv \<tau>' \<subseteq> fst ` set \<eta>
   ; \<turnstile> v : Ty (inst \<eta> \<tau>') \<rbrakk>
  \<Longrightarrow> pat_sound \<Gamma> \<eta> \<rho> (node p') \<tau>' \<Delta>' v"
proof (induction \<Sigma>' \<Gamma> p \<tau> and \<Sigma>' \<Gamma> p' \<tau>' arbitrary: \<Delta> v and \<Delta>' v rule: check_pat_check_pat_at.induct)
  case (1 \<Sigma>' \<Gamma> \<tau>)
  note env = "1.prems"(3)
  from "1.prems"(2) have \<Delta>: "\<Delta> = fmempty" by simp
  from wf_val_inst_disjunct[OF "1.prems"(6)] obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    by blast
  have "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> PatWildcard))"
    using matched_as_lift[OF \<sigma> "1.prems"(2)[unfolded "1.prems"(1)] wf_env_wf_cxt[OF env] "1.prems"(4) wf_env_wf_inst[OF env]]
      v matched_as_wild[OF disjuncts_nonunion[OF \<sigma>]]
    by simp
  then show ?case by (simp add: pat_sound_def \<Delta>)
next
  case (2 \<Sigma>' \<Gamma> x \<tau>)
  note env = "2.prems"(3)
  from "2.prems"(2) have \<Delta>: "\<Delta> = fmupd x \<tau> fmempty" by (auto simp: bind_sum_Ok)
  from wf_val_inst_disjunct[OF "2.prems"(6)] obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    by blast
  have "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (PatVar x)))"
    using matched_as_lift[OF \<sigma> "2.prems"(2)[unfolded "2.prems"(1)] wf_env_wf_cxt[OF env] "2.prems"(4) wf_env_wf_inst[OF env]]
      v matched_as_var[OF disjuncts_nonunion[OF \<sigma>]]
    by simp
  with "2.prems"(6) show ?case by (simp add: pat_sound_def \<Delta>)
next
  case (3 \<Sigma>' \<Gamma> p x \<tau>)
  note env = "3.prems"(3)
  from "3.prems"(2) obtain \<Delta>\<^sub>p where unb: "check_unbound \<Gamma> x = Ok ()"
    and once: "ensure (x \<notin> binds (node p)) (SelectsNoRule JudgementCheckPattern (PatternBindsTwice x)) = Ok ()"
    and chk: "check_pat_at \<Sigma>' \<Gamma> p \<tau> = Ok \<Delta>\<^sub>p"
    and \<Delta>: "\<Delta> = \<Delta>\<^sub>p ++\<^sub>f fmupd x (matched_as \<Sigma>' \<Gamma> \<tau> (node p)) fmempty"
    by (auto simp: bind_sum_Ok)
  from once have x: "x \<notin> binds (node p)" by (simp add: ensure_def split: if_splits)
  note IH = "3.IH"[OF unb once "3.prems"(1) chk "3.prems"(3-6), unfolded pat_sound_def]
  have dom\<^sub>p: "fmdom' \<Delta>\<^sub>p = binds (node p)"
    using check_pat_wf(2)[OF wf_class_table wf_env_wf_cxt[OF env] "3.prems"(4) chk[unfolded "3.prems"(1)]] by simp
  show ?case
    unfolding pat_sound_def
  proof (intro conjI)
    show "\<forall>\<kappa>. match \<rho> (PatAs p x) v = MatchAborts \<kappa> \<longrightarrow> \<not> prevented \<kappa>"
      using IH by (cases "match \<rho> (node p) v") auto
    show "match \<rho> (PatAs p x) v = NoMatch \<longrightarrow> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (PatAs p x)))"
      using IH by (cases "match \<rho> (node p) v") (auto simp: remaining_as)
    show "\<forall>\<rho>'. match \<rho> (PatAs p x) v = Match \<rho>' \<longrightarrow> fmdom' \<rho>' = fmdom' \<Delta>
          \<and> (\<forall>y \<sigma>. fmlookup \<Delta> y = Some \<sigma> \<longrightarrow> (\<exists>u. fmlookup \<rho>' y = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>)))
          \<and> \<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (PatAs p x)))"
    proof (intro allI impI)
    fix \<rho>'
    assume m: "match \<rho> (PatAs p x) v = Match \<rho>'"
    then obtain \<rho>\<^sub>p where mp: "match \<rho> (node p) v = Match \<rho>\<^sub>p" and \<rho>': "\<rho>' = \<rho>\<^sub>p ++\<^sub>f fmupd x v fmempty"
      by (cases "match \<rho> (node p) v") auto
    with IH have dom: "fmdom' \<rho>\<^sub>p = fmdom' \<Delta>\<^sub>p"
      and look: "\<forall>y \<sigma>. fmlookup \<Delta>\<^sub>p y = Some \<sigma> \<longrightarrow> (\<exists>u. fmlookup \<rho>\<^sub>p y = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>))"
      and matched: "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (node p)))"
      by auto
    show "fmdom' \<rho>' = fmdom' \<Delta>
          \<and> (\<forall>y \<sigma>. fmlookup \<Delta> y = Some \<sigma> \<longrightarrow> (\<exists>u. fmlookup \<rho>' y = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>)))
          \<and> \<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (PatAs p x)))"
      using dom look matched x dom\<^sub>p unfolding \<rho>' \<Delta> "3.prems"(1) matched_as_as
      by (auto simp: fmdom'_alt_def fmlookup_dom'_iff split: if_splits)
    qed
  qed
next
  case (4 \<Sigma>' \<Gamma> l \<tau>)
  note env = "4.prems"(3)
  from "4.prems"(2) have \<Delta>: "\<Delta> = fmempty" and no_float: "\<not> (is_int_lit l \<and> has_float_values \<Sigma> \<tau>)"
    by (auto simp: bind_sum_Ok ensure_def "4.prems"(1) split: if_splits)
  from wf_val_inst_disjunct[OF "4.prems"(6)] obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    by blast
  note nonunion = disjuncts_nonunion[OF \<sigma>]
  note lift_m = matched_as_lift[OF \<sigma> "4.prems"(2)[unfolded "4.prems"(1)] wf_env_wf_cxt[OF env] "4.prems"(4)
      wf_env_wf_inst[OF env]]
  note lift_r = remaining_lift[OF \<sigma> "4.prems"(4) wf_env_wf_inst[OF env]]
  have not_float: "\<not> (is_int_lit l \<and> is_float v)"
  proof
    assume "is_int_lit l \<and> is_float v"
    then obtain x where "v = VLit (LitFloat x)" by (cases v) (auto elim: is_float.elims)
    with v float_has_values has_float_values_disjunct[OF \<sigma>] no_float \<open>is_int_lit l \<and> is_float v\<close> show False by blast
  qed
  show ?case
    unfolding pat_sound_def
  proof (intro conjI)
    show "\<forall>\<kappa>. match \<rho> (PatLiteral l) v = MatchAborts \<kappa> \<longrightarrow> \<not> prevented \<kappa>"
    proof (intro allI impI)
      fix \<kappa>
      assume "match \<rho> (PatLiteral l) v = MatchAborts \<kappa>"
      with not_float have "eq (VLit l) v = Aborts \<kappa>" by (auto split: if_splits result.splits bool.splits)
      with eq_abort(1)[OF this] show "\<not> prevented \<kappa>" by simp
    qed
    show "match \<rho> (PatLiteral l) v = NoMatch \<longrightarrow> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (PatLiteral l)))"
    proof
    assume no: "match \<rho> (PatLiteral l) v = NoMatch"
    have "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatLiteral l)))"
    proof (cases \<sigma>)
      case (TyLiteral l')
      with v have "v = VLit l'" by (auto dest: wf_val_literal)
      with no not_float have "l' \<noteq> l" by (cases l) (auto split: if_splits result.splits bool.splits)
      with \<open>v = VLit l'\<close> show ?thesis unfolding TyLiteral by (simp add: ValLit)
    next
      case (TyPrim p)
      show ?thesis
      proof (cases "p \<in> {bool, NoneType}")
        case True
        then have "p = bool \<or> p = NoneType" by simp
        then show ?thesis
        proof
          assume p: "p = bool"
          with v TyPrim obtain b' where v': "v = VLit (LitBool b')" by (auto dest: wf_val_bool)
          show ?thesis
          proof (cases l)
            case (LitBool b)
            with no v' have "b' \<noteq> b" by (auto split: if_splits bool.splits result.splits)
            with v' show ?thesis unfolding TyPrim p LitBool by (simp add: remaining_literal_bool ValLit)
          qed (use v TyPrim p in \<open>simp_all add: remaining_literal_bool\<close>)
        next
          assume p: "p = NoneType"
          with v TyPrim have v': "v = VLit LitNone" by (auto dest: wf_val_none)
          with no have "l \<noteq> LitNone" by (cases l) (auto split: if_splits)
          with v TyPrim p show ?thesis by (simp add: remaining_literal_none)
        qed
      next
        case False
        with v TyPrim show ?thesis by (simp add: remaining_literal_prim)
      qed
    qed (use v nonunion in \<open>simp_all add: remaining_literal_other\<close>)
    then show "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (PatLiteral l)))" by (rule lift_r)
    qed
    show "\<forall>\<rho>'. match \<rho> (PatLiteral l) v = Match \<rho>' \<longrightarrow> fmdom' \<rho>' = fmdom' \<Delta>
          \<and> (\<forall>x \<sigma>. fmlookup \<Delta> x = Some \<sigma> \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>)))
          \<and> \<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (PatLiteral l)))"
    proof (intro allI impI)
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
      proof (cases l)
        case (LitFloat x)
        from eq_lit_float[OF eq_lit[unfolded LitFloat]] have number: "is_number (VLit l')" .
        then have float: "\<turnstile> v : Ty (TyPrim float)" unfolding v' by (cases l') (auto intro: wf_int_float ValLitFloat)
        from number_comparable_float[OF v[unfolded v'] number nonunion] False
        consider "\<Sigma> \<turnstile> TyPrim float <: \<sigma>" | "\<Sigma> \<turnstile> \<sigma> <: TyPrim float" by blast
        then show ?thesis
          using matched float v unfolding LitFloat by cases (auto simp: meet_float[OF nonunion])
      next
        case LitInt
        with not_float v' have "\<forall>x. l' \<noteq> LitFloat x" by auto
        with eq_lit_same[OF eq_lit] LitInt have "l' = l" by auto
        with v' have lit: "\<turnstile> v : Ty (TyLiteral l)" by (simp add: ValLit)
        from lit_comparable[OF v[unfolded v' \<open>l' = l\<close>] _ nonunion] False LitInt have "\<Sigma> \<turnstile> TyLiteral l <: \<sigma>" by auto
        with matched lit show ?thesis unfolding LitInt by (simp add: meet_literal[OF nonunion])
      next
        case LitString
        with eq_lit have "l' = l" by (cases l') auto
        with v' have lit: "\<turnstile> v : Ty (TyLiteral l)" by (simp add: ValLit)
        from lit_comparable[OF v[unfolded v' \<open>l' = l\<close>] _ nonunion] False LitString have "\<Sigma> \<turnstile> TyLiteral l <: \<sigma>" by auto
        with matched lit show ?thesis unfolding LitString by (simp add: meet_literal[OF nonunion])
      next
        case LitBool
        with eq_lit have "l' = l" by (cases l') auto
        with v' have lit: "\<turnstile> v : Ty (TyLiteral l)" by (simp add: ValLit)
        from lit_comparable[OF v[unfolded v' \<open>l' = l\<close>] _ nonunion] False LitBool have "\<Sigma> \<turnstile> TyLiteral l <: \<sigma>" by auto
        with matched lit show ?thesis unfolding LitBool by (simp add: meet_literal[OF nonunion])
      next
        case LitNone
        with eq_lit have "l' = l" by (cases l') auto
        with v' have lit: "\<turnstile> v : Ty (TyLiteral l)" by (simp add: ValLit)
        from lit_comparable[OF v[unfolded v' \<open>l' = l\<close>] _ nonunion] False LitNone have "\<Sigma> \<turnstile> TyLiteral l <: \<sigma>" by auto
        with matched lit show ?thesis unfolding LitNone by (simp add: meet_literal[OF nonunion])
      qed
    qed
    then show "fmdom' \<rho>' = fmdom' \<Delta>
          \<and> (\<forall>x \<sigma>. fmlookup \<Delta> x = Some \<sigma> \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>)))
          \<and> \<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (PatLiteral l)))"
      using lift_m by (simp add: \<rho>' \<Delta>)
    qed
  qed
next
  case (5 \<Sigma>' \<Gamma> ps \<tau>)
  note \<Sigma>' = "5.prems"(1)
  note env = "5.prems"(3)
  note wf\<Gamma> = wf_env_wf_cxt[OF env] and wf\<eta> = wf_env_wf_inst[OF env]
  note IH = "5.IH"[unfolded \<Sigma>']
  let ?f = "\<lambda>\<sigma>. case \<sigma> of
              TyTuple \<sigma>s \<Rightarrow>
                if length \<sigma>s = length ps then Some (pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s))
                else None
            | _ \<Rightarrow> None"
  from "5.prems"(2)[unfolded \<Sigma>'] obtain u where ens: "by_rule RuleCheckTupleNone (do {
      ensure (\<not> has_values \<Sigma> ListKind \<tau>) (SequenceKindMismatch TupleKind \<tau> ListKind);
      ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch TupleKind \<tau> RangeKind)
    }) = Ok u"
    and cb: "check_bound_once ps = Ok ()" and b: "bindings_at \<Sigma> \<Gamma> (PatTuple ps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>"
    by (auto simp: bind_sum_Ok)
  from ens have no_list: "\<not> has_values \<Sigma> ListKind \<tau>" and no_range: "\<not> has_values \<Sigma> RangeKind \<tau>"
    by (auto simp: bind_sum_Ok ensure_def split: if_splits)
  from wf_val_inst_disjunct[OF "5.prems"(6)] obtain \<sigma> where \<sigma>: "\<sigma> \<in> set (disjuncts \<tau>)" and v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    by blast
  note nonunion = disjuncts_nonunion[OF \<sigma>]
  note lift_m = matched_as_lift[OF \<sigma> "5.prems"(2)[unfolded \<Sigma>'] wf\<Gamma> "5.prems"(4) wf\<eta>]
  note lift_r = remaining_lift[OF \<sigma> "5.prems"(4) wf\<eta>]
  have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" and fv\<sigma>: "fv \<sigma> \<subseteq> fst ` set \<eta>" using disjuncts_wf[OF "5.prems"(4) \<sigma>] "5.prems"(5) by auto
  have dom_f: "\<forall>\<sigma>' \<Delta>'. \<sigma>' \<in> set (disjuncts \<tau>) \<and> ?f \<sigma>' = Some (Ok \<Delta>')
                 \<longrightarrow> fmdom' \<Delta>' = binds (PatTuple ps) \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)"
  proof (intro allI impI)
    fix \<sigma>' \<Delta>'
    assume "\<sigma>' \<in> set (disjuncts \<tau>) \<and> ?f \<sigma>' = Some (Ok \<Delta>')"
    then obtain \<sigma>s where \<sigma>': "\<sigma>' = TyTuple \<sigma>s" and len: "length \<sigma>s = length ps"
      and pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) = Ok \<Delta>'" and mem: "\<sigma>' \<in> set (disjuncts \<tau>)"
      by (auto split: ty.splits if_splits)
    have wf': "wf_ty \<Sigma> \<sigma>'" using disjuncts_wf[OF "5.prems"(4) mem] by simp
    have sub: "fmdom' \<Delta>'' = binds (node p) \<and> (\<forall>x \<sigma>''. fmlookup \<Delta>'' x = Some \<sigma>'' \<longrightarrow> wf_ty \<Sigma> \<sigma>'' \<and> fv \<sigma>'' \<subseteq> fv \<sigma>')"
      if "(p, \<sigma>'') \<in> set (zip ps \<sigma>s)" and "check_pat_at \<Sigma> \<Gamma> p \<sigma>'' = Ok \<Delta>''" for p \<sigma>'' \<Delta>''
    proof -
      have "wf_ty \<Sigma> \<sigma>''" and "fv \<sigma>'' \<subseteq> fv \<sigma>'" using wf' set_zip_rightD[OF that(1)] unfolding \<sigma>' by auto
      with check_pat_wf(2)[OF wf_class_table wf\<Gamma> this(1) that(2)] show ?thesis by blast
    qed
    from pattern_bindings_wf[OF pb len[symmetric] sub]
    show "fmdom' \<Delta>' = binds (PatTuple ps) \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)" by auto
  qed
  (* Value other than a tuple: at the remaining type, the disjunct itself *)
  have other: "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (PatTuple ps)))" if "\<forall>vs. v \<noteq> VTuple vs"
  proof -
    have "\<forall>\<sigma>s. \<sigma> \<noteq> TyTuple \<sigma>s"
    proof (intro allI notI)
      fix \<sigma>s
      assume "\<sigma> = TyTuple \<sigma>s"
      with v have "\<turnstile> v : Ty (TyTuple (map (inst \<eta>) \<sigma>s))" by simp
      from wf_tuple[OF this] that show False by blast
    qed
    with v have "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatTuple ps)))" by (simp add: remaining_tuple_other[OF nonunion])
    then show ?thesis by (rule lift_r)
  qed
  show ?case
  proof (cases v)
    case (VTuple vs)
    have "\<exists>\<sigma>s. \<sigma> = TyTuple \<sigma>s"
    proof (rule ccontr)
      assume "\<nexists>\<sigma>s. \<sigma> = TyTuple \<sigma>s"
      with tuple_at_nontuple[OF v[unfolded VTuple] nonunion] has_values_disjunct[OF \<sigma>] no_list show False by auto
    qed
    then obtain \<sigma>s where \<sigma>s: "\<sigma> = TyTuple \<sigma>s" by blast
    have typed: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) vs (map (inst \<eta>) \<sigma>s)"
      using v unfolding VTuple \<sigma>s by (auto elim: wf_tuple)
    then have len_vs: "length vs = length \<sigma>s" by (simp add: list_all2_lengthD)
    show ?thesis
    proof (cases "length \<sigma>s = length ps")
      case False
      with len_vs have no: "match \<rho> (PatTuple ps) v = NoMatch" by (simp add: VTuple)
      moreover have "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (PatTuple ps)))"
        using v False unfolding \<sigma>s by (intro lift_r[unfolded \<sigma>s]) simp
      ultimately show ?thesis by (simp add: pat_sound_def)
    next
      case True
      from \<sigma> obtain k where k: "k < length (disjuncts \<tau>)" and \<sigma>k: "disjuncts \<tau> ! k = \<sigma>" by (auto simp: in_set_conv_nth)
      have fk: "?f \<sigma> = Some (pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s))" using \<sigma>s True by simp
      from bindings_at_Ok[OF b] obtain \<Delta>s_all
        where rel: "list_all2 (\<lambda>m \<Delta>'. case m of Some m' \<Rightarrow> m' = Ok \<Delta>'
                        | None \<Rightarrow> \<Delta>' = fmconst (binds (PatTuple ps)) (TyPrim Never)
                            \<and> (\<forall>x \<in> binds (PatTuple ps). fmlookup \<Gamma> x = Some Unbound)) (map ?f (disjuncts \<tau>)) \<Delta>s_all"
        by blast
      with k \<sigma>k fk obtain \<Delta>\<^sub>d where pb: "pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) = Ok \<Delta>\<^sub>d"
        by (auto simp: list_all2_conv_all_nth)
      have fk': "?f (disjuncts \<tau> ! k) = Some (Ok \<Delta>\<^sub>d)" using fk pb \<sigma>k by simp
      from pattern_bindings_Ok[OF pb] obtain \<Delta>s
        where chk: "list_all2 (\<lambda>m \<Delta>'. m = Ok \<Delta>') (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s) \<Delta>s"
        and \<Delta>\<^sub>d: "\<Delta>\<^sub>d = fold fmadd \<Delta>s fmempty"
        by blast
      have len\<Delta>s: "length \<Delta>s = length ps" using list_all2_lengthD[OF chk] True by simp
      have chk_i: "check_pat_at \<Sigma> \<Gamma> (ps ! i) (\<sigma>s ! i) = Ok (\<Delta>s ! i)" if "i < length ps" for i
        using chk that True by (auto simp: list_all2_conv_all_nth)
      have sound_i: "pat_sound \<Gamma> \<eta> \<rho> (node (ps ! i)) (\<sigma>s ! i) (\<Delta>s ! i) (vs ! i)" if i: "i < length ps" for i
      proof -
        have mem: "(ps ! i, \<sigma>s ! i) \<in> set (zip ps \<sigma>s)" using i True by (auto simp: in_set_zip)
        have mem_i: "\<sigma>s ! i \<in> set \<sigma>s" using i True by simp
        have wfi: "wf_ty \<Sigma> (\<sigma>s ! i)" and fvi: "fv (\<sigma>s ! i) \<subseteq> fst ` set \<eta>"
          using wf\<sigma> fv\<sigma> mem_i unfolding \<sigma>s by auto
        have vi: "\<turnstile> vs ! i : Ty (inst \<eta> (\<sigma>s ! i))" using typed i True by (auto simp: list_all2_conv_all_nth)
        from IH[OF ens cb \<sigma> \<sigma>s True mem refl refl chk_i[OF i] env wfi fvi vi] show ?thesis .
      qed
      have dom_i: "fmdom' (\<Delta>s ! i) = binds (node (ps ! i))" if i: "i < length ps" for i
        using check_pat_wf(2)[OF wf_class_table wf\<Gamma> _ chk_i[OF i]] wf\<sigma> i True unfolding \<sigma>s by auto
      have once: "distinct (concat (map (sorted_list_of_set \<circ> binds \<circ> node) ps))" using check_bound_once_Ok[OF cb] .
      have l1: "length ps = length vs" and l2: "length ps = length \<Delta>s" using True len_vs len\<Delta>s by simp_all
      have sound_all: "\<forall>i < length ps. pat_sound \<Gamma> \<eta> \<rho> (node (ps ! i)) (\<sigma>s ! i) (\<Delta>s ! i) (vs ! i)"
        using sound_i by blast
      have dom_all: "\<forall>i < length ps. fmdom' (\<Delta>s ! i) = binds (node (ps ! i))" using dom_i by blast
      note seq = match_seq_sound[where pus = "zip ps vs" and fps = ps and us = vs and \<Delta>s = \<Delta>s and fts = \<sigma>s,
          OF refl l1 l2 sound_all dom_all once]
      have m: "match \<rho> (PatTuple ps) v
               = foldr seq_compose_match (map (\<lambda>(p, u). match \<rho> (node p) u) (zip ps vs)) (Match fmempty)"
        using l1 by (simp add: VTuple match_all_foldr)
      have dom\<Delta>: "fmdom' \<Delta> = binds (PatTuple ps)"
        using check_pat_wf(1)[OF wf_class_table wf\<Gamma> "5.prems"(4) "5.prems"(2)[unfolded \<Sigma>']] by simp
      have dom\<Delta>\<^sub>d: "fmdom' \<Delta>\<^sub>d = binds (PatTuple ps)"
        using dom_f[rule_format, of \<sigma> \<Delta>\<^sub>d] \<sigma> fk pb by simp
      show ?thesis
        unfolding pat_sound_def
      proof (intro conjI)
        show "\<forall>\<kappa>. match \<rho> (PatTuple ps) v = MatchAborts \<kappa> \<longrightarrow> \<not> prevented \<kappa>" using seq(1) unfolding m by blast
        show "match \<rho> (PatTuple ps) v = NoMatch \<longrightarrow> \<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (PatTuple ps)))"
        proof
          assume "match \<rho> (PatTuple ps) v = NoMatch"
          from seq(2)[OF this[unfolded m]] obtain i where i: "i < length ps"
            and no_i: "match \<rho> (node (ps ! i)) (vs ! i) = NoMatch"
            by blast
          from sound_i[OF i] no_i have vi: "\<turnstile> vs ! i : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> (\<sigma>s ! i) (node (ps ! i))))"
            by (simp add: pat_sound_def)
          let ?\<rho>s = "map2 (\<lambda>\<tau> p. remaining \<Sigma> \<Gamma> \<tau> (node p)) \<sigma>s ps"
          have len\<rho>s: "length ?\<rho>s = length ps" using True by simp
          have \<rho>s_i: "?\<rho>s ! i = remaining \<Sigma> \<Gamma> (\<sigma>s ! i) (node (ps ! i))" using i True by simp
          have ne: "?\<rho>s ! i \<noteq> TyPrim Never"
            using vi wf_val_never unfolding \<rho>s_i by (cases "remaining \<Sigma> \<Gamma> (\<sigma>s ! i) (node (ps ! i))") auto
          have "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<sigma> (PatTuple ps)))"
          proof (cases "filter (\<lambda>j. ?\<rho>s ! j \<noteq> TyPrim Never) [0..<length ?\<rho>s]")
            case Nil
            with i len\<rho>s ne have False by (auto simp: filter_empty_conv)
            then show ?thesis ..
          next
            case (Cons j js)
            show ?thesis
            proof (cases js)
              case Nil
              with Cons have single: "filter (\<lambda>j. ?\<rho>s ! j \<noteq> TyPrim Never) [0..<length ?\<rho>s] = [j]" by simp
              have "i \<in> set (filter (\<lambda>j. ?\<rho>s ! j \<noteq> TyPrim Never) [0..<length ?\<rho>s])" using i len\<rho>s ne by simp
              with single have ji: "j = i" by simp
              have "remaining \<Sigma> \<Gamma> \<sigma> (PatTuple ps) = TyTuple (\<sigma>s[i := ?\<rho>s ! i])"
                unfolding \<sigma>s using True single ji by (simp add: Let_def)
              moreover have "\<turnstile> v : Ty (TyTuple (map (inst \<eta>) (\<sigma>s[i := ?\<rho>s ! i])))"
                using typed vi i True unfolding VTuple \<rho>s_i
                by (auto intro!: ValTuple simp: list_all2_conv_all_nth nth_list_update)
              ultimately show ?thesis by simp
            next
              case (Cons j' js')
              with \<open>filter _ _ = j # js\<close> have "remaining \<Sigma> \<Gamma> \<sigma> (PatTuple ps) = TyTuple \<sigma>s"
                unfolding \<sigma>s using True by (simp add: Let_def)
              with v show ?thesis unfolding \<sigma>s by simp
            qed
          qed
          then show "\<turnstile> v : Ty (inst \<eta> (remaining \<Sigma> \<Gamma> \<tau> (PatTuple ps)))" by (rule lift_r)
        qed
        show "\<forall>\<rho>'. match \<rho> (PatTuple ps) v = Match \<rho>' \<longrightarrow> fmdom' \<rho>' = fmdom' \<Delta>
              \<and> (\<forall>x \<sigma>'. fmlookup \<Delta> x = Some \<sigma>' \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>')))
              \<and> \<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (PatTuple ps)))"
        proof (intro allI impI)
          fix \<rho>'
          assume "match \<rho> (PatTuple ps) v = Match \<rho>'"
          from seq(3)[OF this[unfolded m]] have dom: "fmdom' \<rho>' = fmdom' \<Delta>\<^sub>d"
            and look: "\<forall>x \<upsilon>. fmlookup \<Delta>\<^sub>d x = Some \<upsilon> \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<upsilon>))"
            and matched: "\<forall>i < length ps. \<exists>\<rho>\<^sub>i. match \<rho> (node (ps ! i)) (vs ! i) = Match \<rho>\<^sub>i"
            unfolding \<Delta>\<^sub>d by auto
          have "\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>')" if \<sigma>': "fmlookup \<Delta> x = Some \<sigma>'" for x \<sigma>'
          proof -
            from \<sigma>' have "x \<in> fmdom' \<Delta>\<^sub>d" using dom\<Delta> dom\<Delta>\<^sub>d by (auto simp: fmlookup_dom'_iff)
            then obtain \<upsilon> where \<upsilon>: "fmlookup \<Delta>\<^sub>d x = Some \<upsilon>" by (auto simp: fmlookup_dom'_iff)
            with look obtain u where u: "fmlookup \<rho>' x = Some u" and "\<turnstile> u : Ty (inst \<eta> \<upsilon>)" by blast
            note u_typed = this
            have "\<exists>\<sigma>''. fmlookup \<Delta> x = Some \<sigma>'' \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>'')"
            proof (rule bindings_at_typed[where f = ?f and \<tau> = \<tau> and p = "PatTuple ps" and k = k and \<Delta>\<^sub>d = \<Delta>\<^sub>d])
              show "bindings_at \<Sigma> \<Gamma> (PatTuple ps) (map ?f (disjuncts \<tau>)) = Ok \<Delta>" by (rule b)
              show "k < length (disjuncts \<tau>)" by (rule k)
              show "?f (disjuncts \<tau> ! k) = Some (Ok \<Delta>\<^sub>d)" by (rule fk')
              show "\<forall>\<sigma>' \<Delta>'. \<sigma>' \<in> set (disjuncts \<tau>) \<and> ?f \<sigma>' = Some (Ok \<Delta>')
                      \<longrightarrow> fmdom' \<Delta>' = binds (PatTuple ps) \<and> (\<forall>x \<upsilon>. fmlookup \<Delta>' x = Some \<upsilon> \<longrightarrow> wf_ty \<Sigma> \<upsilon>)"
                by (rule dom_f)
              show "fmlookup \<Delta>\<^sub>d x = Some \<upsilon>" by (rule \<upsilon>)
              show "\<turnstile> u : Ty (inst \<eta> \<upsilon>)" by (rule u_typed)
              show "wf_inst \<Sigma> \<eta>" by (rule wf\<eta>)
            qed
            with \<sigma>' u show ?thesis by auto
          qed
          moreover have "\<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<sigma> (PatTuple ps)))"
          proof -
            have "\<turnstile> vs ! i : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> (\<sigma>s ! i) (node (ps ! i))))" if i: "i < length ps" for i
              using sound_i[OF i] matched i by (auto simp: pat_sound_def)
            then show ?thesis
              unfolding \<sigma>s VTuple using True len_vs by (auto intro!: ValTuple simp: list_all2_conv_all_nth)
          qed
          ultimately show "fmdom' \<rho>' = fmdom' \<Delta>
              \<and> (\<forall>x \<sigma>'. fmlookup \<Delta> x = Some \<sigma>' \<longrightarrow> (\<exists>u. fmlookup \<rho>' x = Some u \<and> \<turnstile> u : Ty (inst \<eta> \<sigma>')))
              \<and> \<turnstile> v : Ty (inst \<eta> (matched_as \<Sigma> \<Gamma> \<tau> (PatTuple ps)))"
            using dom dom\<Delta> dom\<Delta>\<^sub>d lift_m by blast
        qed
      qed
    qed
  next
    case (VList vs)
    with v list_has_values has_values_disjunct[OF \<sigma>] no_list have False by blast
    then show ?thesis ..
  next
    case (VObject D zvs)
    show ?thesis
    proof (cases "D = range_class")
      case True
      with v VObject range_has_values has_values_disjunct[OF \<sigma>] no_range have False by blast
      then show ?thesis ..
    next
      case False
      then have no: "match \<rho> (PatTuple ps) v = NoMatch" by (simp add: VObject)
      with other show ?thesis by (simp add: pat_sound_def VObject)
    qed
  qed (use other in \<open>simp_all add: pat_sound_def\<close>)
next
  case (6 \<Sigma>' \<Gamma> ps \<tau>)
  then show ?case sorry
next
  case (7 \<Sigma>' \<Gamma> kps \<tau>)
  then show ?case sorry
next
  case (8 \<Sigma>' \<Gamma> q ps kps \<tau>)
  then show ?case sorry
next
  case (9 \<Sigma>' \<Gamma> p q \<tau>)
  from "9.prems"(2) have "check_pat \<Sigma>' \<Gamma> q \<tau> = Ok \<Delta>'" using check_pat_at_node[of \<Sigma>' \<Gamma> "At p q"] by simp
  with "9.IH" "9.prems" show ?case by simp
qed

lemmas check_pat_sound = check_pat_sound_aux[OF refl]

end

end
