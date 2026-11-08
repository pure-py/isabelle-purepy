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

end
