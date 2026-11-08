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

end
