(* Termination of the order of loading of a well-formed program *)
theory LoadsTermination
    imports WellFormedTopLevel "isabelle-purepy.Correctness"
begin

(* Modules checked by submodules, from q, for the variables xs in turn *)
fun chain :: "name \<Rightarrow> var list \<Rightarrow> name list"
where
"chain q [] = []" |
"chain q (x # xs) = Qualified q x # chain (Qualified q x) xs"

lemma chain_snoc: "chain q (xs @ [x]) = chain q xs @ [Qualified (foldl Qualified q xs) x]"
  by (induction xs arbitrary: q) simp_all

lemma variables_nonempty: "variables q \<noteq> []"
  by (induction q) simp_all

lemma hd_variables: "hd (variables q) = root q"
  by (induction q) (simp_all add: hd_append variables_nonempty)

lemma variables_root: "variables q = root q # tl (variables q)"
  by (metis hd_variables list.collapse variables_nonempty)

lemma tl_variables_snoc: "tl (variables q @ [x]) = tl (variables q) @ [x]"
  by (simp add: tl_append2 variables_nonempty)

lemma foldl_variables: "foldl Qualified (Simple (root q)) (tl (variables q)) = q"
  by (induction q) (simp_all add: tl_variables_snoc)

lemma proper_prefixes_chain:
  "proper_prefixes q @ [q] = Simple (root q) # chain (Simple (root q)) (tl (variables q))"
  by (induction q) (simp_all add: tl_variables_snoc chain_snoc foldl_variables)

context loading
begin

abbreviation submod_loads_dom :: "name list \<Rightarrow> name \<Rightarrow> var list \<Rightarrow> bool"
where "submod_loads_dom qs q xs \<equiv> loads_submod_loads_imports_loads_import_loads_dom (Inl (Inr (qs, q, xs)))"

abbreviation imports_loads_dom :: "name list \<Rightarrow> name \<Rightarrow> import located list \<Rightarrow> bool"
where "imports_loads_dom qs q \<iota>s \<equiv> loads_submod_loads_imports_loads_import_loads_dom (Inr (Inl (qs, q, \<iota>s)))"

(* Loading terminates from every list of modules loaded so far *)
abbreviation loads_all :: "name list \<Rightarrow> bool"
where "loads_all qs' \<equiv> \<forall>qs. loads_dom qs qs'"

lemma loads_all_Nil: "loads_all []"
  by (auto intro: loads_domintros)

lemma loads_dom_skip: "\<lbrakk> q \<in> set qs \<or> q |\<in>| fmdom \<P> ; loads_dom qs qs' \<rbrakk> \<Longrightarrow> loads_dom qs (q # qs')"
  by (auto intro: loads_domintros)

lemma loads_dom_body:
  "\<lbrakk> the (fmlookup \<M> q) = ModuleBody \<iota>s t ; \<forall>qs. imports_loads_dom qs q \<iota>s ; loads_all qs' \<rbrakk>
  \<Longrightarrow> loads_dom qs (q # qs')"
  by (auto intro: loads_domintros)

lemma submod_loads_dom:
  "(\<And>x. \<lbrakk> x \<in> set xs ; q |\<notin>| fmdom \<P> ; Qualified q x |\<in>| fmdom \<M> \<rbrakk> \<Longrightarrow> loads_all [Qualified q x])
  \<Longrightarrow> submod_loads_dom qs q xs"
proof (induction xs arbitrary: qs)
  case Nil
  then show ?case by (auto intro: loads_domintros)
next
  case (Cons x xs)
  then show ?case by (auto intro: loads_domintros)
qed

(* A name of the context of a module which is a submodule; by disjointness, the module itself binds no such name *)
lemma submodule_unbound:
  assumes "(fmdom \<Gamma> |\<union>| fmdom \<Delta>) |\<inter>| fmdom (submods \<M> q) = {||}" and "fmlookup \<M> (Qualified q x) = Some b"
  shows "fmlookup \<Delta> x = None"
proof -
  have "fmlookup (submods \<M> q) x = Some (ModStub (Qualified q x))"
    using assms(2) by (simp add: submods.rep_eq fmdom'I)
  then have "x |\<in>| fmdom (submods \<M> q)" by (rule fmdomI)
  with assms(1) have "x |\<notin>| fmdom \<Delta>" by (metis fempty_iff finter_iff funion_iff)
  then show ?thesis by (rule fmdom_notD)
qed

(* Every submodule of a checked module which is not predefined is a stub of its context *)
lemma check_module_stub:
  assumes "check_module \<M> V \<Sigma> q\<^sub>0 q = Ok (\<Delta>, \<Sigma>')" and "q |\<notin>| fmdom \<P>" and "Qualified q x |\<in>| fmdom \<M>"
  shows "fmlookup \<Delta> x = Some (ModStub (Qualified q x))"
  using assms
  by (auto simp: fmlookup_dom_iff fmlookup_dom'_iff submods.rep_eq Let_def bind_sum_def dest: submodule_unbound
    split: option.splits if_splits module_body.splits sum.splits prod.splits static_outcome.splits)

end

(* The domain of loading, outside the locale, where the induction over the type checker can vary the program *)
abbreviation loads_all_in :: "program \<Rightarrow> name list \<Rightarrow> bool"
where "loads_all_in \<M> qs' \<equiv> \<forall>qs. loading.loads_submod_loads_imports_loads_import_loads_dom \<M> (Inl (Inl (qs, qs')))"

abbreviation imports_loads_dom_in :: "program \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> import located list \<Rightarrow> bool"
where "imports_loads_dom_in \<M> qs q \<iota>s \<equiv> loading.loads_submod_loads_imports_loads_import_loads_dom \<M> (Inr (Inl (qs, q, \<iota>s)))"

lemmas loads_domintros = loading.loads_submod_loads_imports_loads_import_loads.domintros

(* Each function of the type checker, accepting, visits every module that loading visits from the same place *)
theorem check_loads:
  shows "check_module \<M> V \<Sigma> q' q = Ok r\<^sub>1 \<Longrightarrow> loads_all_in \<M> qs' \<Longrightarrow> loads_all_in \<M> (q # qs')"
    and "check_imports \<M> V \<Sigma> q \<iota>s = Ok r\<^sub>2 \<Longrightarrow> imports_loads_dom_in \<M> qs q \<iota>s"
    and "submodules \<M> V \<Sigma> q q' \<Gamma> xs = Ok r\<^sub>3 \<Longrightarrow> loads_all_in \<M> qs' \<Longrightarrow> loads_all_in \<M> (chain q' xs @ qs')"
    and "imports_entry \<M> V \<Sigma> q q' \<Gamma> x = Ok r\<^sub>4 \<Longrightarrow> fmlookup \<Gamma> x = Some (ModStub q'')
      \<Longrightarrow> loads_all_in \<M> qs' \<Longrightarrow> loads_all_in \<M> (q'' # qs')"
    and "imports_entries \<M> V \<Sigma> q q' \<Gamma> xs = Ok r\<^sub>5 \<Longrightarrow> y \<in> set xs \<Longrightarrow> fmlookup \<Gamma> y = Some (ModStub q'')
      \<Longrightarrow> loads_all_in \<M> qs' \<Longrightarrow> loads_all_in \<M> (q'' # qs')"
    and "check_modules \<M> V \<Sigma> q qs\<^sub>0 = Ok \<Sigma>' \<Longrightarrow> loads_all_in \<M> qs' \<Longrightarrow> loads_all_in \<M> (qs\<^sub>0 @ qs')"
proof (induction \<M> V \<Sigma> q' q and \<M> V \<Sigma> q \<iota>s and \<M> V \<Sigma> q q' \<Gamma> xs and \<M> V \<Sigma> q q' \<Gamma> x
    and \<M> V \<Sigma> q q' \<Gamma> xs and \<M> V \<Sigma> q qs\<^sub>0
    arbitrary: r\<^sub>1 qs' and r\<^sub>2 qs and r\<^sub>3 qs' and r\<^sub>4 q'' qs' and r\<^sub>5 y q'' qs' and \<Sigma>' qs'
    rule: check_module_check_imports_submodules_imports_entry_imports_entries_check_modules.induct)
  case (1 \<M> V \<Sigma> q' q r\<^sub>1 qs')
  show ?case
  proof
    fix qs
    show "loading.loads_submod_loads_imports_loads_import_loads_dom \<M> (Inl (Inl (qs, q # qs')))"
    proof (cases "q \<in> set qs \<or> q |\<in>| fmdom \<P>")
      case True
      with "1.prems"(2) show ?thesis by (blast intro: loading.loads_dom_skip)
    next
      case False
      then have P: "fmlookup \<P> q = None" by (simp add: fmdom_notD)
      have nV: "q \<notin> set V" using "1.prems"(1) P by (auto split: if_splits)
      obtain b where Mq: "fmlookup \<M> q = Some b"
        using "1.prems"(1) P nV by (cases "fmlookup \<M> q") auto
      obtain \<iota>s t where b: "b = ModuleBody \<iota>s t" by (cases b)
      obtain r where ci: "check_imports \<M> (V @ [q]) \<Sigma> q \<iota>s = Ok r"
        using "1.prems"(1) P nV Mq b by (cases "check_imports \<M> (V @ [q]) \<Sigma> q \<iota>s") auto
      have "\<forall>qs. imports_loads_dom_in \<M> qs q \<iota>s" using "1.IH"[OF P nV Mq b ci] by blast
      moreover have "the (fmlookup \<M> q) = ModuleBody \<iota>s t" using Mq b by simp
      ultimately show ?thesis using "1.prems"(2) by (blast intro: loading.loads_dom_body)
    qed
  qed
next
  case (2 \<M> V \<Sigma> q r\<^sub>2 qs)
  show ?case by (rule loads_domintros)
next
  case (3 \<M> V \<Sigma> q p q' \<iota>s r\<^sub>2 qs)
  define x xs where "x = root q'" and "xs = tl (variables q')"
  have vq: "variables q' = x # xs" using variables_root by (simp add: x_def xs_def)
  obtain e where e: "ensure (\<not> q \<prec> q') (q, ImportOfContainedModule q' q) = Ok e"
    using "3.prems" vq by (cases "ensure (\<not> q \<prec> q') (q, ImportOfContainedModule q' q)") (auto simp: locate_in_def)
  obtain \<Delta> \<Sigma>\<^sub>1 where m: "check_module \<M> V \<Sigma> q (Simple x) = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    using "3.prems" vq e by (cases "check_module \<M> V \<Sigma> q (Simple x)") (auto simp: locate_in_def)
  obtain \<Delta>' \<Sigma>\<^sub>2 where s: "submodules \<M> V \<Sigma>\<^sub>1 q (Simple x) \<Delta> xs = Ok (\<Delta>', \<Sigma>\<^sub>2)"
    using "3.prems" vq e m by (cases "submodules \<M> V \<Sigma>\<^sub>1 q (Simple x) \<Delta> xs") (auto simp: locate_in_def)
  obtain r where i: "check_imports \<M> V \<Sigma>\<^sub>2 q \<iota>s = Ok r"
    using "3.prems" vq e m s by (cases "check_imports \<M> V \<Sigma>\<^sub>2 q \<iota>s") (auto simp: locate_in_def)
  have "loads_all_in \<M> (chain (Simple x) xs @ [])"
    using "3.IH"(2)[OF vq e m refl s] loading.loads_all_Nil by blast
  then have "loads_all_in \<M> (Simple x # chain (Simple x) xs @ [])"
    using "3.IH"(1)[OF vq e m] by blast
  then have "loading.loads_submod_loads_imports_loads_import_loads_dom \<M> (Inr (Inr (qs, q, Import q')))"
    by (auto intro: loads_domintros simp: proper_prefixes_chain x_def xs_def)
  moreover have "\<forall>qs. imports_loads_dom_in \<M> qs q \<iota>s" using "3.IH"(3)[OF vq e m refl s refl i] by blast
  ultimately show ?case by (auto intro: loads_domintros)
next
  case (4 \<M> V \<Sigma> q p q' xs \<iota>s r\<^sub>2 qs)
  obtain \<Delta> \<Sigma>\<^sub>1 where m: "check_module \<M> V \<Sigma> q q' = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    using "4.prems" by (cases "check_module \<M> V \<Sigma> q q'") (auto simp: locate_in_def)
  obtain \<Sigma>\<^sub>2 where ms: "check_modules \<M> V \<Sigma>\<^sub>1 q (unique_to q' q) = Ok \<Sigma>\<^sub>2"
    using "4.prems" m by (cases "check_modules \<M> V \<Sigma>\<^sub>1 q (unique_to q' q)") (auto simp: locate_in_def)
  obtain c where c: "(case redeclared id {} xs of None \<Rightarrow> Ok () | Some x \<Rightarrow> Fail (q, DuplicateImportedName x)) = Ok c"
    using "4.prems" m ms by (cases "redeclared id {} xs") (auto simp: locate_in_def)
  obtain \<theta>s \<Sigma>\<^sub>3 where es: "imports_entries \<M> V \<Sigma>\<^sub>2 q q' \<Delta> xs = Ok (\<theta>s, \<Sigma>\<^sub>3)"
    using "4.prems" m ms c by (cases "imports_entries \<M> V \<Sigma>\<^sub>2 q q' \<Delta> xs") (auto simp: locate_in_def)
  obtain r where i: "check_imports \<M> V \<Sigma>\<^sub>3 q \<iota>s = Ok r"
    using "4.prems" m ms c es by (cases "check_imports \<M> V \<Sigma>\<^sub>3 q \<iota>s") (auto simp: locate_in_def)
  have q': "loads_all_in \<M> [q']" using "4.IH"(1)[OF m] loading.loads_all_Nil by blast
  have "loads_all_in \<M> (unique_to q' q @ [q'])" using "4.IH"(2)[OF m refl ms q'] .
  moreover have "loading.loads_submod_loads_imports_loads_import_loads_dom \<M> (Inl (Inr (qs', q', xs)))" for qs'
  proof (rule loading.submod_loads_dom)
    fix x
    assume "x \<in> set xs" and "q' |\<notin>| fmdom \<P>" and "Qualified q' x |\<in>| fmdom \<M>"
    with m have "fmlookup \<Delta> x = Some (ModStub (Qualified q' x))" by (blast intro: loading.check_module_stub)
    with "4.IH"(3)[OF m refl ms c es \<open>x \<in> set xs\<close>] loading.loads_all_Nil
    show "loads_all_in \<M> [Qualified q' x]" by blast
  qed
  ultimately have "loading.loads_submod_loads_imports_loads_import_loads_dom \<M> (Inr (Inr (qs, q, FromImport q' xs)))"
    by (auto intro: loads_domintros)
  moreover have "\<forall>qs. imports_loads_dom_in \<M> qs q \<iota>s" using "4.IH"(4)[OF m refl ms c es refl i] by blast
  ultimately show ?case by (auto intro: loads_domintros)
next
  case (5 \<M> V \<Sigma> q q' \<Gamma> r\<^sub>3 qs')
  then show ?case by simp
next
  case (6 \<M> V \<Sigma> q q' \<Gamma> x xs r\<^sub>3 qs')
  obtain \<Delta> \<Sigma>\<^sub>1 where m: "check_module \<M> V \<Sigma> q (Qualified q' x) = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    using "6.prems"(1) by (cases "check_module \<M> V \<Sigma> q (Qualified q' x)") auto
  obtain r where s: "submodules \<M> V \<Sigma>\<^sub>1 q (Qualified q' x) \<Delta> xs = Ok r"
    using "6.prems"(1) m by (cases "submodules \<M> V \<Sigma>\<^sub>1 q (Qualified q' x) \<Delta> xs") auto
  have "loads_all_in \<M> (chain (Qualified q' x) xs @ qs')" using "6.IH"(2)[OF m refl s "6.prems"(2)] .
  then show ?case using "6.IH"(1)[OF m] by simp
next
  case (7 \<M> V \<Sigma> q q' \<Gamma> x r\<^sub>4 q'' qs')
  obtain r where m: "check_module \<M> V \<Sigma> q q'' = Ok r"
    using "7.prems"(1,2) by (cases "check_module \<M> V \<Sigma> q q''") auto
  show ?case using "7.IH"[OF "7.prems"(2) refl m "7.prems"(3)] .
next
  case (8 \<M> V \<Sigma> q q' \<Gamma> r\<^sub>5 y q'' qs')
  then show ?case by simp
next
  case (9 \<M> V \<Sigma> q q' \<Gamma> x xs r\<^sub>5 y q'' qs')
  obtain \<theta> \<Sigma>\<^sub>1 where e: "imports_entry \<M> V \<Sigma> q q' \<Gamma> x = Ok (\<theta>, \<Sigma>\<^sub>1)"
    using "9.prems"(1) by (cases "imports_entry \<M> V \<Sigma> q q' \<Gamma> x") auto
  obtain r where es: "imports_entries \<M> V \<Sigma>\<^sub>1 q q' \<Gamma> xs = Ok r"
    using "9.prems"(1) e by (cases "imports_entries \<M> V \<Sigma>\<^sub>1 q q' \<Gamma> xs") auto
  show ?case
  proof (cases "y = x")
    case True
    with "9.prems"(3) show ?thesis using "9.IH"(1)[OF e _ "9.prems"(4)] by simp
  next
    case False
    with "9.prems"(2) have "y \<in> set xs" by simp
    then show ?thesis using "9.IH"(2)[OF e refl es _ "9.prems"(3,4)] by simp
  qed
next
  case (10 \<M> V \<Sigma> q \<Sigma>' qs')
  then show ?case by simp
next
  case (11 \<M> V \<Sigma> q q' qs \<Sigma>' qs')
  obtain \<Gamma> \<Sigma>\<^sub>1 where m: "check_module \<M> V \<Sigma> q q' = Ok (\<Gamma>, \<Sigma>\<^sub>1)"
    using "11.prems"(1) by (cases "check_module \<M> V \<Sigma> q q'") auto
  have ms: "check_modules \<M> V \<Sigma>\<^sub>1 q qs = Ok \<Sigma>'" using "11.prems"(1) m by simp
  have "loads_all_in \<M> (qs @ qs')" using "11.IH"(2)[OF m refl ms "11.prems"(2)] .
  then show ?case using "11.IH"(1)[OF m] by simp
qed

context loading
begin

(* Loading terminates for a program the type checker accepts *)
corollary check_program_loads_dom: "check_program \<M> = None \<Longrightarrow> loads_dom [] [main]"
  using check_loads(1)[of \<M> "[]" predefined_classes main main _ "[]"] loads_all_Nil
  by (auto simp: check_program_def split: sum.splits)

(* Completeness of the evaluator for a program the type checker accepts *)
corollary checked_program_completeness:
  "\<lbrakk> eval_program \<A> vs \<kappa> ; check_program \<M> = None \<rbrakk> \<Longrightarrow> \<exists>n. run_program n \<A> = Done (vs, \<kappa>)"
  by (blast intro: program_completeness check_program_loads_dom)

end

end
