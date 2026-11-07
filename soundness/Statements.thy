(* Soundness of statement evaluation *)
theory Statements
  imports ResultTyping
begin

(* Return type over the type variables bound by \<eta> *)
fun wf_return :: "(var \<times> ty) list \<Rightarrow> ty option \<Rightarrow> bool"
where
"wf_return \<eta> (Some \<tau>) = (fv \<tau> \<subseteq> fst ` set \<eta>)" |
"wf_return \<eta> None = True"

context evaluation
begin

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

definition sound_stmt :: "env \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_stmt \<rho> s o =
  (\<forall>\<eta> \<Gamma> \<zeta> R. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<eta> \<zeta> \<longrightarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R
     \<longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R)"

definition sound_elif :: "env \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_elif \<rho> eb o =
  (\<forall>\<eta> \<Gamma> \<zeta> Rs. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<eta> \<zeta> \<longrightarrow> those_sum (check_elif \<Sigma> \<Gamma> \<zeta> eb) = Ok Rs
     \<longrightarrow> (\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R))"

lemma sound_stmt_at:
  assumes "sound_stmt \<rho> (node s) o" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "wf_return \<eta> \<zeta>"
    and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
proof -
  from assms(4) obtain R' where "check_stmt \<Sigma> \<Gamma> \<zeta> (node s) = Ok R'" and R': "bindings_of R' = bindings_of R"
    by (blast dest: check_stmt_at_Ok)
  with assms(1-3) have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'" unfolding sound_stmt_def by simp
  then show ?thesis by (cases o) (simp add: wf_completion_bindings[OF R'])
qed

lemma sound_stmtI:
  assumes "\<And>\<eta> \<Gamma> \<zeta> R. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_return \<eta> \<zeta> ; check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R \<rbrakk> \<Longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
  shows "sound_stmt \<rho> s o"
  unfolding sound_stmt_def using assms by blast

lemma sound_elifI:
  assumes "\<And>\<eta> \<Gamma> \<zeta> Rs. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_return \<eta> \<zeta> ; those_sum (check_elif \<Sigma> \<Gamma> \<zeta> eb) = Ok Rs \<rbrakk>
            \<Longrightarrow> \<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
  shows "sound_elif \<rho> eb o"
  unfolding sound_elif_def using assms by blast

subsection \<open>Statements\<close>

lemma pass_sound: "sound_stmt \<rho> StmtPass (assigns\<^sub>o \<epsilon>)"
  by (simp add: sound_stmt_def)

lemma declare_sound: "sound_stmt \<rho> (StmtDeclare x \<psi>) (assigns\<^sub>o \<epsilon>)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtDeclare x \<psi>) = Ok R"
  from chk obtain \<tau> where \<tau>: "resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau>" and R: "R = Assigns\<^sub>R (fmupd x (DU \<tau>) fmempty) None"
    and "fmlookup \<Gamma> x = Some Unbound"
    by (auto simp: bind_sum_def check_unbound_def ensure_def split: sum.splits if_splits)
  with env have "fmlookup \<rho> x = Some VUnbound" by (auto dest!: wf_env_lookup wf_val_unbound wf_val_du)
  moreover have "fv \<tau> \<subseteq> fst ` set \<eta>" using env resolve_type_tyvars[OF \<tau>] by (rule wf_env_fv)
  ultimately have "\<eta> \<turnstile> \<rho> : fmupd x (DU \<tau>) \<Gamma>" using env by (intro wf_env_upd_cxt) (auto intro: ValUnbound)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<epsilon>) R" by (simp add: R)
qed

lemma assign_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtAssign x \<pi> e) (mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>)))"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x \<pi> e) = Ok R"
  from chk obtain \<tau> where chk_e: "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()"
    and R: "R = Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty) None" and fv_\<Gamma>: "fv \<tau> \<subseteq> tyvars \<Gamma>"
    by (cases \<pi>)
       (auto simp: bind_sum_def check_unbound_def ensure_def
        split: sum.splits option.splits cxt_entry.splits if_splits dest: tyvars_entry resolve_type_tyvars)
  from env fv_\<Gamma> have fv: "fv \<tau> \<subseteq> fst ` set \<eta>" by (rule wf_env_fv)
  show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>))) R"
  proof (cases r)
    case (Val v)
    with assms env chk_e fv have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_check_at)
    then have "\<eta> \<turnstile> fmupd x v \<rho> : fmupd x (Ty \<tau>) \<Gamma>" using env fv by (intro wf_env_upd) auto
    then show ?thesis by (simp add: Val R)
  next
    case (Aborts \<kappa>)
    with assms env chk_e fv show ?thesis by (auto simp: R dest: sound_expr_check_at)
  qed
qed

(* An expression statement synthesises or is a call statement *)
lemma check_expr_stmt:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) = Ok R"
  shows "R = Assigns\<^sub>R fmempty None \<and> (\<exists>\<tau>. has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>)"
proof (cases e)
  case (At p e')
  show ?thesis
  proof (cases e')
    case (ExprCall e'' a)
    then obtain es kws where a: "a = (es, kws)" by (cases a)
    show ?thesis
      using assms
      by (cases "lambda_of (node e'') = None \<and> class_of_name \<Gamma> (node e'') = None")
         (auto simp: At ExprCall a has_type_def bind_sum_def split: sum.splits)
  qed (use assms in \<open>auto simp: At has_type_def bind_sum_def split: sum.splits\<close>)
qed

lemma expr_stmt_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtExpr e) (mlet r (\<lambda>v. assigns\<^sub>o \<epsilon>))"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) = Ok R"
  from check_expr_stmt[OF chk] obtain \<tau> where R: "R = Assigns\<^sub>R fmempty None" and "has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>"
    by blast
  with assms env have "result_typed r (inst \<eta> \<tau>)" by (auto dest: sound_expr_has_type_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. assigns\<^sub>o \<epsilon>)) R" using env by (cases r) (simp_all add: R)
qed

lemma print_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtPrint e) (mlet r (\<lambda>v. ([v], Assigns \<epsilon>)))"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtPrint e) = Ok R"
  then obtain \<tau> where R: "R = Assigns\<^sub>R fmempty None" and "synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau>"
    by (auto simp: bind_sum_def ensure_def split: sum.splits if_splits)
  with assms env have "result_typed r (inst \<eta> \<tau>)" by (auto dest: sound_expr_synth_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. ([v], Assigns \<epsilon>))) R" using env by (cases r) (simp_all add: R)
qed

lemma return_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtReturn (Some e)) (mlet r returns\<^sub>o)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn (Some e)) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with ret have fv: "fv \<tau> \<subseteq> fst ` set \<eta>" by simp
  from chk \<zeta> have "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()" by (auto simp: bind_sum_def split: sum.splits)
  with assms env fv have "result_typed r (inst \<eta> \<tau>)" by (auto dest: sound_expr_check_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r returns\<^sub>o) R" by (cases r) (simp_all add: \<zeta>)
qed

lemma return_none_sound: "sound_stmt \<rho> (StmtReturn None) (returns\<^sub>o (VLit LitNone))"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn None) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with chk have "\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>" by (auto split: if_splits)
  then have "\<turnstile> VLit LitNone : Ty (inst \<eta> \<tau>)"
    by (intro ValSub[OF ValLit] SubtyLiteral)
       (auto dest: subst_subty'[where \<tau>s = "map snd \<eta>" and \<alpha>s = "map fst \<eta>"])
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (returns\<^sub>o (VLit LitNone)) R" by (simp add: \<zeta>)
qed

(* Free type variables of a function signature, among the type variables of the context *)
lemma def_signature_fv:
  assumes "def_signature \<Sigma> \<Gamma> d = Ok \<pi>"
  shows "fv_scheme \<pi> \<subseteq> tyvars \<Gamma>"
proof (cases d)
  case (Def f \<alpha>s xps \<psi> s)
  let ?\<Gamma>' = "\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar"
  from assms Def obtain \<sigma>s \<tau> where \<sigma>s: "those_sum (map (resolve_type \<Sigma> ?\<Gamma>' \<circ> snd) xps) = Ok \<sigma>s"
    and \<tau>: "resolve_type \<Sigma> ?\<Gamma>' \<psi> = Ok \<tau>" and \<pi>: "\<pi> = TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>)"
    by (auto simp: Let_def bind_sum_def split: sum.splits option.splits)
  have \<Gamma>': "tyvars ?\<Gamma>' \<subseteq> tyvars \<Gamma> \<union> set \<alpha>s" using tyvars_add tyvars_fmconst by blast
  have "fv \<sigma> \<subseteq> tyvars ?\<Gamma>'" if "\<sigma> \<in> set \<sigma>s" for \<sigma>
  proof -
    from that obtain i where "i < length \<sigma>s" and "\<sigma> = \<sigma>s ! i" by (auto simp: in_set_conv_nth)
    with those_sum_map_Ok[OF \<sigma>s] have "resolve_type \<Sigma> ?\<Gamma>' (snd (xps ! i)) = Ok \<sigma>"
      by (auto simp: list_all2_conv_all_nth)
    then show ?thesis by (rule resolve_type_tyvars)
  qed
  with resolve_type_tyvars[OF \<tau>] \<Gamma>' show ?thesis by (auto simp: \<pi>)
qed

lemma defs_sound:
  assumes vs: "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]"
  shows "sound_stmt \<rho> (StmtMutualRegion ds) (assigns\<^sub>o (fmap_of_list (zip (map (def_name \<circ> node) ds) vs)))"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMutualRegion ds) = Ok R"
  let ?xs = "map (def_name \<circ> node) ds"
  from chk obtain \<pi>s where red: "redeclared node {} (map (\<lambda>d. At (pos_of d) (def_name (node d))) ds) = None"
    and sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s"
    and defs: "all_sum (map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip ?xs (map signature_entry \<pi>s)))) ds \<pi>s)
                = Ok ()"
    and R: "R = Assigns\<^sub>R (fmap_of_list (zip ?xs (map signature_entry \<pi>s))) None"
    by (auto simp: Let_def bind_sum_def split: sum.splits option.splits)
  let ?\<Delta> = "fmap_of_list (zip ?xs (map signature_entry \<pi>s))"
  let ?\<rho>' = "fmap_of_list (zip ?xs vs)"
  have sig: "def_signature \<Sigma> \<Gamma> (node (ds ! i)) = Ok (\<pi>s ! i)" if "i < length ds" for i
    using those_sum_map_Ok[OF sigs] that by (simp add: list_all2_conv_all_nth)
  have len: "length \<pi>s = length ds" using those_sum_map_Ok[OF sigs] by (simp add: list_all2_lengthD)
  from redeclared_None[OF red] have distinct: "distinct ?xs" by (simp add: comp_def)
  have fv: "\<forall>\<pi> \<in> set \<pi>s. fv_scheme \<pi> \<subseteq> fst ` set \<eta>"
  proof
    fix \<pi>
    assume "\<pi> \<in> set \<pi>s"
    then obtain i where i: "i < length ds" and \<pi>: "\<pi> = \<pi>s ! i" using len by (auto simp: in_set_conv_nth)
    from def_signature_fv[OF sig[OF i]] \<pi> wf_env_tyvars[OF env] show "fv_scheme \<pi> \<subseteq> fst ` set \<eta>" by blast
  qed
  have disjoint: "\<forall>d \<in> set ds. case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}"
  proof
    fix d
    assume "d \<in> set ds"
    then obtain i where i: "i < length ds" and d: "d = ds ! i" by (auto simp: in_set_conv_nth)
    from sig[OF i] d have "def_signature \<Sigma> \<Gamma> (node d) = Ok (\<pi>s ! i)" by simp
    then show "case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}" by (rule def_signature_disjoint)
  qed
  (* Entry of the i-th definition, typing its closure *)
  have entry: "\<turnstile> Def(\<rho>, ds, i) : inst_entry \<eta> (signature_entry (\<pi>s ! i))" if "i < length ds" for i
  proof -
    obtain \<alpha>s \<tau> where \<pi>: "\<pi>s ! i = TyScheme \<alpha>s \<tau>" by (cases "\<pi>s ! i")
    from ValDef[OF env sigs refl defs fv disjoint that \<pi>] \<pi> show ?thesis by simp
  qed
  have lookup: "\<exists>i < length ds. ?xs ! i = x \<and> \<theta> = signature_entry (\<pi>s ! i)" if "fmlookup ?\<Delta> x = Some \<theta>" for x \<theta>
  proof -
    from that have "(x, \<theta>) \<in> set (zip ?xs (map signature_entry \<pi>s))"
      by (auto simp: fmlookup_of_list dest: map_of_SomeD)
    with len show ?thesis by (force simp: in_set_zip)
  qed
  have "\<eta> \<turnstile> \<rho> \<otimes> ?\<rho>' : \<Gamma> \<otimes> ?\<Delta>"
  proof (rule wf_env_add[OF env])
    have "tyvars ?\<Delta> \<subseteq> \<Union> (fv_scheme ` set \<pi>s)"
    proof
      fix \<alpha>
      assume "\<alpha> \<in> tyvars ?\<Delta>"
      then obtain x \<theta> where look: "fmlookup ?\<Delta> x = Some \<theta>" and \<alpha>: "\<alpha> \<in> fv_entry \<theta> \<or> \<theta> = TypeVar"
        by (auto simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff)
      from lookup[OF look] obtain i where i: "i < length ds" and \<theta>: "\<theta> = signature_entry (\<pi>s ! i)" by blast
      obtain \<alpha>s \<tau> where \<pi>i: "\<pi>s ! i = TyScheme \<alpha>s \<tau>" by (cases "\<pi>s ! i")
      from \<alpha> \<theta> \<pi>i have "\<alpha> \<in> fv_scheme (\<pi>s ! i)" by (cases \<alpha>s) auto
      with i len show "\<alpha> \<in> \<Union> (fv_scheme ` set \<pi>s)" by (metis UN_I nth_mem)
    qed
    with fv show "tyvars ?\<Delta> \<subseteq> fst ` set \<eta>" by blast
    show "fmdom ?\<rho>' |\<subseteq>| fmdom ?\<Delta>" using len by (simp add: vs)
  next
    fix x \<theta>
    assume "fmlookup ?\<Delta> x = Some \<theta>"
    then obtain i where i: "i < length ds" and x: "?xs ! i = x" and \<theta>: "\<theta> = signature_entry (\<pi>s ! i)"
      by (blast dest: lookup)
    have "fmlookup ?\<rho>' x = Some (vs ! i)"
      using map_of_zip_nth[of ?xs vs i] distinct i x by (simp add: vs fmlookup_of_list)
    moreover from fmdomI[OF this] have "x |\<in>| fmdom ?\<rho>'" .
    ultimately have "fmlookup (\<rho> \<otimes> ?\<rho>') x = Some (vs ! i)" by (simp only: fmlookup_add if_True)
    with entry[OF i] i \<theta> show "\<exists>v. fmlookup (\<rho> \<otimes> ?\<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
      by (simp add: vs)
  next
    fix x \<pi>
    assume "fmlookup ?\<Delta> x = Some (Scheme \<pi>)"
    then obtain i where i: "i < length ds" and \<pi>: "Scheme \<pi> = signature_entry (\<pi>s ! i)" by (blast dest: lookup)
    obtain \<alpha>s \<tau> where \<pi>i: "\<pi>s ! i = TyScheme \<alpha>s \<tau>" by (cases "\<pi>s ! i")
    from def_signatures_callable[OF sigs i \<pi>i] \<pi> \<pi>i show "callable_scheme \<pi>"
      by (cases \<alpha>s) auto
  qed
  moreover have "fmdom ?\<rho>' |\<subseteq>| fmdom ?\<Delta>" using len by (simp add: vs)
  ultimately show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o ?\<rho>') R" by (simp add: R)
qed

(* Static outcome of an assertion whose condition does not evaluate to false: the condition checks as a Boolean
   and nothing is assigned *)
lemma check_assert:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R" and "\<rho>, node e \<Rightarrow>\<^sub>e r" and "r \<noteq> Val false"
  shows "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok () \<and> (\<exists>r'. R = Assigns\<^sub>R fmempty r')"
  using assms by (auto simp: Let_def bind_sum_def split: sum.splits option.splits if_splits dest: literal_false)

lemma assert_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val true"
  shows "sound_stmt \<rho> (StmtAssert e e') (assigns\<^sub>o \<epsilon>)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R"
  from check_assert[OF chk assms] obtain r where "R = Assigns\<^sub>R fmempty r" by auto
  with env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<epsilon>) R" by simp
qed

lemma assert_false_sound: "sound_stmt \<rho> (StmtAssert e e') (aborts\<^sub>o (AssertionError w))"
  by (simp add: sound_stmt_def)

lemma assert_fail_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa>" and "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_stmt \<rho> (StmtAssert e e') (aborts\<^sub>o \<kappa>)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R"
  from check_assert[OF chk assms(1)] have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()" by simp
  with assms(2) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R" by (auto dest: prim_operand)
qed

lemma assert_nonbool_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val v" and "sound_expr \<rho> (node e) (Val v)" and "v \<notin> {true, false}"
  shows "sound_stmt \<rho> (StmtAssert e e') (aborts\<^sub>o Excluded)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R"
  from check_assert[OF chk assms(1)] assms(3) have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()" by simp
  with assms(2, 3) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o Excluded) R" by (auto dest!: bool_operand)
qed

lemma assert_msg_false_fail_sound:
  assumes "sound_expr \<rho> (node e') (Aborts \<kappa>)"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o \<kappa>)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert_msg[OF chk] assms env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R"
    by (auto dest: prim_operand)
qed

lemma assert_msg_nonstr_sound:
  assumes "sound_expr \<rho> (node e') (Val v)" and "\<forall>w. v \<noteq> VLit (LitString w)"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o Excluded)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert_msg[OF chk] assms env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o Excluded) R"
    by (auto dest!: str_operand)
qed

(* Entry \<theta>' above \<theta>: the values of \<theta> are values of \<theta>', and \<theta>' is a type scheme or a type variable only if \<theta> is
   the same *)
definition entry_above :: "(var \<times> ty) list \<Rightarrow> cxt_entry \<Rightarrow> cxt_entry \<Rightarrow> bool"
where
"entry_above \<eta> \<theta> \<theta>' =
  ((\<forall>v. \<turnstile> v : inst_entry \<eta> \<theta> \<longrightarrow> \<turnstile> v : inst_entry \<eta> \<theta>') \<and> (\<forall>\<pi>. \<theta>' = Scheme \<pi> \<longrightarrow> \<theta> = Scheme \<pi>)
   \<and> (\<theta>' = TypeVar \<longleftrightarrow> \<theta> = TypeVar))"

lemma entry_above_refl: "entry_above \<eta> \<theta> \<theta>"
  by (simp add: entry_above_def)

lemma entry_above_trans: "\<lbrakk> entry_above \<eta> \<theta> \<theta>' ; entry_above \<eta> \<theta>' \<theta>'' \<rbrakk> \<Longrightarrow> entry_above \<eta> \<theta> \<theta>''"
  by (simp add: entry_above_def)

lemma possibly_unassigned_above: "possibly_unassigned b \<theta> = Some \<theta>' \<Longrightarrow> entry_above \<eta> \<theta> \<theta>'"
  by (cases \<theta>) (auto simp: entry_above_def intro!: ValPU ValPUScheme dest!: wf_val_du wf_val_pu wf_val_puscheme)

lemma possibly_unassigned_unbound: "possibly_unassigned b \<theta> = Some \<theta>' \<Longrightarrow> \<turnstile> VUnbound : inst_entry \<eta> \<theta>'"
  by (cases \<theta>) (auto intro: ValPU ValPUScheme)

lemma merge_entry_above:
  "merge_cxt_entry \<Sigma> b (Some \<theta>) e = Some \<theta>'' \<Longrightarrow> entry_above \<eta> \<theta> \<theta>''"
  "merge_cxt_entry \<Sigma> b e (Some \<theta>) = Some \<theta>'' \<Longrightarrow> entry_above \<eta> \<theta> \<theta>''"
proof -
  have ty: "entry_above \<eta> (Ty \<sigma>) (Ty \<tau>)" if "\<Sigma> \<turnstile> \<sigma> <: \<tau>" for \<sigma> \<tau>
    using that by (auto simp: entry_above_def intro: wf_val_inst_sub)
  have scheme: "entry_above \<eta> \<theta> (PUScheme \<pi> b)" if "scheme_of \<theta> = Some \<pi>" for \<theta> \<pi>
    using scheme_of_Some[OF that]
    by (auto simp: entry_above_def intro!: ValPUScheme dest!: wf_val_puscheme)
  have var: "entry_above \<eta> \<theta> (PU \<tau> b)" if "var_ty \<theta> = Some \<sigma>" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>" for \<theta> \<sigma> \<tau>
    using var_ty_Some[OF that(1)] that(2)
    by (auto simp: entry_above_def intro!: ValPU dest!: wf_val_du wf_val_pu intro: wf_val_inst_sub)
  show "merge_cxt_entry \<Sigma> b (Some \<theta>) e = Some \<theta>'' \<Longrightarrow> entry_above \<eta> \<theta> \<theta>''"
  proof (cases e)
    case (Some \<theta>')
    assume "merge_cxt_entry \<Sigma> b (Some \<theta>) e = Some \<theta>''"
    with Some merge_cxt_entry_cases show ?thesis
      by (blast intro: ty scheme var join_upper entry_above_refl)
  qed (auto intro: possibly_unassigned_above)
  show "merge_cxt_entry \<Sigma> b e (Some \<theta>) = Some \<theta>'' \<Longrightarrow> entry_above \<eta> \<theta> \<theta>''"
  proof (cases e)
    case (Some \<theta>')
    assume "merge_cxt_entry \<Sigma> b e (Some \<theta>) = Some \<theta>''"
    with Some merge_cxt_entry_cases[of \<Sigma> b \<theta>' \<theta> \<theta>''] scheme_of_Some show ?thesis
      by (auto intro: ty scheme var join_upper entry_above_refl)
  qed (auto intro: possibly_unassigned_above)
qed

lemma merge_entry_unbound:
  "merge_cxt_entry \<Sigma> b None e = Some \<theta>'' \<Longrightarrow> \<turnstile> VUnbound : inst_entry \<eta> \<theta>''"
  "merge_cxt_entry \<Sigma> b e None = Some \<theta>'' \<Longrightarrow> \<turnstile> VUnbound : inst_entry \<eta> \<theta>''"
  by (cases e; auto dest: possibly_unassigned_unbound)+

(* Soundness at one branch of an if statement carries to the merge of the branches *)
lemma wf_outcome_merge_if:
  assumes "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" and "R \<in> set Rs"
    and "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and "merges \<Sigma> X (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R'" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
  sorry

lemma if_true_sound:
  assumes "sound_stmt \<rho> (node s) o"
  shows "sound_stmt \<rho> (StmtIf e s elifs else') o"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  from check_if[OF chk] obtain Rs
    where Rs: "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and R: "merges \<Sigma> (set (declares (StmtIf e s elifs else')))
              (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R"
    by blast
  from Rs obtain R0 where R0: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R0" and "R0 \<in> set Rs"
    by (auto simp: bind_sum_def split: sum.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R0" using assms env ret R0 by (rule sound_stmt_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using \<open>R0 \<in> set Rs\<close> Rs R env by (rule wf_outcome_merge_if)
qed

lemma if_false_sound:
  assumes "sound_elif \<rho> (elifs, else') o"
  shows "sound_stmt \<rho> (StmtIf e s elifs else') o"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  from check_if[OF chk] obtain Rs
    where Rs: "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and R: "merges \<Sigma> (set (declares (StmtIf e s elifs else')))
              (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R"
    by blast
  from Rs obtain R0 Rs' where Rs': "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs'" and "Rs = R0 # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  with assms env ret obtain R' where "R' \<in> set Rs'" and "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
    unfolding sound_elif_def by blast
  moreover from this(1) have "R' \<in> set Rs" by (simp add: \<open>Rs = R0 # Rs'\<close>)
  ultimately show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using Rs R env by (blast intro: wf_outcome_merge_if)
qed

lemma if_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def by (auto simp: check_stmt_if bind_sum_def dest: prim_operand split: sum.splits)

lemma if_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def by (auto simp: check_stmt_if bind_sum_def dest!: bool_operand split: sum.splits)

lemma match_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; dispatch \<rho> v cases = Val (\<rho>', s') ; sound_stmt (\<rho> \<otimes> \<rho>') (node s') o \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (assigns\<^sub>o \<rho>' \<otimes> o)"
  sorry

lemma match_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def by (auto simp: bind_sum_def dest: sound_expr_synth_at split: sum.splits)

lemma match_abort_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; dispatch \<rho> v cases = Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
  sorry

lemma seq_sound:
  assumes "sound_stmt \<rho> (node s) (us, Assigns \<rho>')" and "sound_stmt (\<rho> \<otimes> \<rho>') (node s') o"
  shows "sound_stmt \<rho> (StmtSeq s s') ((us, Assigns \<rho>') \<otimes> o)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R"
  from check_seq[OF chk] obtain \<Delta> r R' where chk1: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)"
    and chk2: "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s' = Ok R'" and R: "R = Assigns\<^sub>R \<Delta> r \<otimes> R'" by blast
  have o1: "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, Assigns \<rho>') (Assigns\<^sub>R \<Delta> r)"
    using assms(1) env ret chk1 by (rule sound_stmt_at)
  then have env': "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>" and dom: "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>" by simp_all
  have o2: "wf_outcome \<eta> (\<rho> \<otimes> \<rho>') (\<Gamma> \<otimes> \<Delta>) \<zeta> o R'" using assms(2) env' ret chk2 by (rule sound_stmt_at)
  obtain vs' \<omega>' where o: "o = (vs', \<omega>')" by (cases o)
  show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> ((us, Assigns \<rho>') \<otimes> o) R"
  proof (cases \<omega>')
    case (Assigns \<rho>'')
    with o2 o obtain \<Delta>' where "bindings_of R' = Some \<Delta>'" and "fmdom \<rho>'' |\<subseteq>| fmdom \<Delta>'"
      and "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' \<otimes> \<rho>'' : \<Gamma> \<otimes> \<Delta> \<otimes> \<Delta>'" by auto
    moreover from this(1) obtain r' where "R' = Assigns\<^sub>R \<Delta>' r'" by (cases R') auto
    ultimately show ?thesis using dom by (auto simp: o Assigns R intro: le_supI1 le_supI2)
  qed (use o2 in \<open>simp_all add: o\<close>)
qed

(* Sequence whose first statement returns or aborts *)
lemma seq_exit_sound:
  assumes "sound_stmt \<rho> (node s) (us, \<omega>)" and "\<And>\<rho>'. \<omega> \<noteq> Assigns \<rho>'"
  shows "sound_stmt \<rho> (StmtSeq s s') (us, \<omega>)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R"
  from check_seq[OF chk] obtain \<Delta> r where "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)" by blast
  with assms(1) env ret have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, \<omega>) (Assigns\<^sub>R \<Delta> r)" by (rule sound_stmt_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, \<omega>) R" using assms(2) by (cases \<omega>) (simp_all, blast)
qed

lemma if_none_sound: "sound_elif \<rho> ([], None) (assigns\<^sub>o \<epsilon>)"
  by (auto simp: sound_elif_def bind_sum_def)

lemma else_sound:
  assumes "sound_stmt \<rho> (node s) o"
  shows "sound_elif \<rho> ([], Some s) o"
proof (rule sound_elifI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ([], Some s)) = Ok Rs"
  from chk obtain R where "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R" and "Rs = [R]"
    by (auto simp: bind_sum_def split: sum.splits)
  with assms env ret show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" by (auto intro: sound_stmt_at)
qed

lemma elif_true_sound:
  assumes "sound_stmt \<rho> (node s) o"
  shows "sound_elif \<rho> ((e, s) # elifs, else') o"
proof (rule sound_elifI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>"
    and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs, else')) = Ok Rs"
  from chk obtain R Rs' where R: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R" and Rs: "Rs = R # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using assms env ret R by (rule sound_stmt_at)
  then show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" by (auto simp: Rs)
qed

lemma elif_false_sound:
  assumes "sound_elif \<rho> (elifs, else') o"
  shows "sound_elif \<rho> ((e, s) # elifs, else') o"
proof (rule sound_elifI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>"
    and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs, else')) = Ok Rs"
  from chk obtain R Rs' where "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs'" and "Rs = R # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  then show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using assms env ret unfolding sound_elif_def by auto
qed

lemma elif_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') (aborts\<^sub>o \<kappa>)"
  unfolding sound_elif_def by (auto simp: bind_sum_def dest: prim_operand split: sum.splits)

lemma elif_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') (aborts\<^sub>o Excluded)"
  unfolding sound_elif_def by (auto simp: bind_sum_def dest!: bool_operand split: sum.splits)

subsection \<open>Calls of function definitions\<close>

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

end

end
