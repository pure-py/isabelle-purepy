(* Soundness of statement evaluation *)
theory Statements
  imports Dispatch
begin

context evaluation
begin

(* Return type, well-formed *)
fun wf_return :: "ty option \<Rightarrow> bool"
where
"wf_return (Some \<tau>) = wf_ty \<Sigma> \<tau>" |
"wf_return None = True"

(* Completion of a statement checked at \<Gamma> and return type \<zeta> with static outcome R, run in \<rho> *)
fun wf_completion :: "(var \<Rightarrow> ty) \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> completion \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Assigns \<rho>') R =
  (\<exists>\<Delta>. bindings_of R = Some \<Delta> \<and> fmdom \<rho>' |\<subseteq>| fmdom \<Delta> \<and> \<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>)" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Returns v) R = (\<forall>\<tau>. \<zeta> = Some \<tau> \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>))" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Aborts\<^sub>\<omega> \<kappa>) R = (\<not> prevented \<kappa>)"

fun wf_outcome :: "(var \<Rightarrow> ty) \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> outcome \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (vs, \<omega>) R = wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R"

lemma wf_completion_bindings:
  "bindings_of R = bindings_of R' \<Longrightarrow> wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R = wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R'"
  by (cases \<omega>) simp_all

definition sound_stmt :: "env \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_stmt \<rho> s o =
  (\<forall>\<eta> \<Gamma> \<zeta> R. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<zeta> \<longrightarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R
     \<longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R)"

definition sound_elif :: "env \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_elif \<rho> eb o =
  (\<forall>\<eta> \<Gamma> \<zeta> Rs. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<zeta> \<longrightarrow> those_sum (check_elif \<Sigma> \<Gamma> \<zeta> eb) = Ok Rs
     \<longrightarrow> (\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R))"

lemma sound_stmt_at:
  assumes "sound_stmt \<rho> (node s) o" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "wf_return \<zeta>"
    and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
proof -
  from assms(4) obtain R' where "check_stmt \<Sigma> \<Gamma> \<zeta> (node s) = Ok R'" and R': "bindings_of R' = bindings_of R"
    by (blast dest: check_stmt_at_Ok)
  with assms(1-3) have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'" unfolding sound_stmt_def by simp
  then show ?thesis by (cases o) (simp add: wf_completion_bindings[OF R'])
qed

lemma sound_stmtI:
  assumes "\<And>\<eta> \<Gamma> \<zeta> R. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_return \<zeta> ; check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R \<rbrakk> \<Longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
  shows "sound_stmt \<rho> s o"
  unfolding sound_stmt_def using assms by blast

lemma sound_elifI:
  assumes "\<And>\<eta> \<Gamma> \<zeta> Rs. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; wf_return \<zeta> ; those_sum (check_elif \<Sigma> \<Gamma> \<zeta> eb) = Ok Rs \<rbrakk>
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
  moreover have "wf_ty \<Sigma> \<tau>" using resolve_type_wf[OF wf_env_wf_cxt[OF env] \<tau>] by simp
  ultimately have "\<eta> \<turnstile> \<rho> : fmupd x (DU \<tau>) \<Gamma>" using env by (intro wf_env_upd_cxt) (auto intro: ValUnbound)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<epsilon>) R" by (simp add: R)
qed

lemma assign_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtAssign x \<pi> e) (mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>)))"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x \<pi> e) = Ok R"
  have "\<exists>\<tau>. check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok () \<and> R = Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty) None \<and> wf_ty \<Sigma> \<tau>"
  proof (cases \<pi>)
    case None
    with chk obtain \<tau> where "fmlookup \<Gamma> x = Some (DU \<tau>)" and "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()"
      and "R = Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty) None"
      by (auto simp: bind_sum_def split: sum.splits option.splits cxt_entry.splits)
    with wf_cxt_lookup[OF wf_env_wf_cxt[OF env] this(1)] show ?thesis by auto
  next
    case (Some \<psi>)
    with chk obtain \<tau> where "resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau>" and "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()"
      and "R = Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty) None"
      by (auto simp: bind_sum_def check_unbound_def ensure_def split: sum.splits if_splits)
    with resolve_type_wf[OF wf_env_wf_cxt[OF env] this(1)] show ?thesis by auto
  qed
  then obtain \<tau> where chk_e: "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()"
    and R: "R = Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty) None" and wf: "wf_ty \<Sigma> \<tau>"
    by blast
  show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>))) R"
  proof (cases r)
    case (Val v)
    with assms env chk_e wf have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_check_at)
    then have "\<eta> \<turnstile> fmupd x v \<rho> : fmupd x (Ty \<tau>) \<Gamma>" using env wf by (intro wf_env_upd) auto
    then show ?thesis by (simp add: Val R)
  next
    case (Aborts \<kappa>)
    with assms env chk_e wf show ?thesis by (auto simp: R dest: sound_expr_check_at)
  qed
qed

(* An expression statement synthesises or is a call statement *)
lemma check_expr_stmt:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) = Ok R"
  shows "R = Assigns\<^sub>R fmempty None \<and> (\<exists>\<tau>. has_type_at \<Sigma> \<Gamma> e \<tau>)"
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
  from check_expr_stmt[OF chk] obtain \<tau> where R: "R = Assigns\<^sub>R fmempty None" and "has_type_at \<Sigma> \<Gamma> e \<tau>"
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn (Some e)) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with ret have wf: "wf_ty \<Sigma> \<tau>" by simp
  from chk \<zeta> have "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()" by (auto simp: bind_sum_def split: sum.splits)
  with assms env wf have "result_typed r (inst \<eta> \<tau>)" by (auto dest: sound_expr_check_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r returns\<^sub>o) R" by (cases r) (simp_all add: \<zeta>)
qed

lemma return_none_sound: "sound_stmt \<rho> (StmtReturn None) (returns\<^sub>o (VLit LitNone))"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn None) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with chk have "\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>" by (auto split: if_splits)
  moreover have "wf_ty \<Sigma> \<tau>" using ret by (simp add: \<zeta>)
  ultimately have "\<turnstile> VLit LitNone : Ty (inst \<eta> \<tau>)" using wf_env_wf_inst[OF env] by (rule wf_none)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (returns\<^sub>o (VLit LitNone)) R" by (simp add: \<zeta>)
qed

(* Environment of a region of mutually recursive definitions, binding each to its closure *)
lemma wf_env_defs:
  assumes env: "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s"
    and defs:
      "all_sum (map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds)
                                                     (map signature_entry \<pi>s)))) ds \<pi>s) = Ok ()"
    and disjoint: "\<forall>d \<in> set ds. case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}"
    and vs: "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]"
  shows "\<eta> \<turnstile> \<rho> \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) vs)
           : \<Gamma> \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))"
proof -
  let ?xs = "map (def_name \<circ> node) ds"
  let ?\<Delta> = "fmap_of_list (zip ?xs (map signature_entry \<pi>s))"
  let ?\<rho>' = "fmap_of_list (zip ?xs vs)"
  have len: "length \<pi>s = length ds" using those_sum_map_Ok[OF sigs] by (simp add: list_all2_lengthD)
  (* Entry of the i-th definition, typing its closure *)
  have entry: "\<turnstile> Def(\<rho>, ds, i) : inst_entry \<eta> (signature_entry (\<pi>s ! i))" if "i < length ds" for i
  proof -
    obtain \<alpha>s \<tau> where \<pi>: "\<pi>s ! i = TyScheme \<alpha>s \<tau>" by (cases "\<pi>s ! i")
    have "defs_checked \<Gamma> ds \<pi>s" using sigs defs disjoint by (simp add: defs_checked_def)
    from wf_def_entry[OF env this that \<pi>] \<pi> show ?thesis by simp
  qed
  then have typed: "list_all2 (\<lambda>v \<theta>. \<turnstile> v : inst_entry \<eta> \<theta>) vs (map signature_entry \<pi>s)"
    using len by (auto simp: vs list_all2_conv_all_nth)
  show ?thesis
  proof (rule wf_env_add[OF env])
    show "wf_cxt \<Sigma> ?\<Delta>" using defs_wf[OF wf_env_wf_cxt[OF env] sigs] by blast
    show "fmdom ?\<rho>' |\<subseteq>| fmdom ?\<Delta>" using len by (simp add: vs)
  next
    fix x \<theta>
    assume "fmlookup ?\<Delta> x = Some \<theta>"
    with rel_option_map_of_zip[OF typed, of ?xs x] obtain v where "map_of (zip ?xs vs) x = Some v"
      and "\<turnstile> v : inst_entry \<eta> \<theta>"
      by (cases "map_of (zip ?xs vs) x") (auto simp: fmlookup_of_list)
    then show "\<exists>v. fmlookup (\<rho> \<otimes> ?\<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
      using fmdomI[of ?\<rho>' x v] by (simp add: fmlookup_of_list)
  qed
qed

lemma defs_sound:
  assumes vs: "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]"
  shows "sound_stmt \<rho> (StmtMutualRegion ds) (assigns\<^sub>o (fmap_of_list (zip (map (def_name \<circ> node) ds) vs)))"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMutualRegion ds) = Ok R"
  let ?xs = "map (def_name \<circ> node) ds"
  from chk obtain \<pi>s
    where sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s"
    and defs: "all_sum (map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip ?xs (map signature_entry \<pi>s)))) ds \<pi>s)
                = Ok ()"
    and R: "R = Assigns\<^sub>R (fmap_of_list (zip ?xs (map signature_entry \<pi>s))) None"
    by (auto simp: Let_def bind_sum_def split: sum.splits option.splits)
  have len: "length \<pi>s = length ds" using those_sum_map_Ok[OF sigs] by (simp add: list_all2_lengthD)
  have disjoint: "\<forall>d \<in> set ds. case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}"
  proof
    fix d
    assume "d \<in> set ds"
    then obtain i where "i < length ds" and d: "d = ds ! i" by (auto simp: in_set_conv_nth)
    with those_sum_map_Ok[OF sigs] have "def_signature \<Sigma> \<Gamma> (node d) = Ok (\<pi>s ! i)"
      by (auto simp: list_all2_conv_all_nth)
    then show "case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}" by (rule def_signature_disjoint)
  qed
  from wf_env_defs[OF env sigs defs disjoint vs] len
  show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o (fmap_of_list (zip ?xs vs))) R" by (simp add: R vs)
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
definition entry_above :: "(var \<Rightarrow> ty) \<Rightarrow> cxt_entry \<Rightarrow> cxt_entry \<Rightarrow> bool"
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

(* Merge of two well-formed entries, above each *)
lemma merge_entry_above_both:
  assumes wf\<eta>: "wf_inst \<Sigma> \<eta>" and m: "merge_cxt_entry \<Sigma> b (Some \<theta>) (Some \<theta>') = Some \<theta>''"
    and wf: "wf_entry \<Sigma> \<theta>" "wf_entry \<Sigma> \<theta>'"
  shows "entry_above \<eta> \<theta> \<theta>'' \<and> entry_above \<eta> \<theta>' \<theta>''"
proof -
  have ty: "entry_above \<eta> (Ty \<sigma>) (Ty \<tau>)" if "\<Sigma> \<turnstile> \<sigma> <: \<tau>" and "wf_ty \<Sigma> \<tau>" for \<sigma> \<tau>
    using that by (auto simp: entry_above_def intro: wf_val_inst_sub[OF _ _ _ wf\<eta>])
  have scheme: "entry_above \<eta> \<theta> (PUScheme \<pi> b)" if "scheme_of \<theta> = Some \<pi>" for \<theta> \<pi>
    using scheme_of_Some[OF that]
    by (auto simp: entry_above_def intro!: ValPUScheme dest!: wf_val_puscheme)
  have var: "entry_above \<eta> \<theta> (PU \<tau> b)" if "var_ty \<theta> = Some \<sigma>" and "\<Sigma> \<turnstile> \<sigma> <: \<tau>" and "wf_ty \<Sigma> \<tau>" for \<theta> \<sigma> \<tau>
    using var_ty_Some[OF that(1)] that(2, 3)
    by (auto simp: entry_above_def intro!: ValPU dest!: wf_val_du wf_val_pu
        intro: wf_val_inst_sub[OF _ _ _ wf\<eta>])
  from merge_cxt_entry_cases[OF m] consider
      (tys) \<sigma> \<tau> where "\<theta> = Ty \<sigma>" "\<theta>' = Ty \<tau>" "\<theta>'' = Ty (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)"
    | (same) "\<theta>'' = \<theta>" "\<theta>' = \<theta>"
    | (schemes) \<pi> where "scheme_of \<theta> = Some \<pi>" "scheme_of \<theta>' = Some \<pi>" "\<theta>'' = PUScheme \<pi> b"
    | (vars) \<sigma> \<tau> where "var_ty \<theta> = Some \<sigma>" "var_ty \<theta>' = Some \<tau>" "\<theta>'' = PU (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>) b"
    by blast
  then show ?thesis
  proof cases
    case tys
    with wf have "wf_ty \<Sigma> (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)" by (auto intro: wf_join)
    with tys show ?thesis by (auto intro: ty join_upper)
  next
    case same
    then show ?thesis by (simp add: entry_above_refl)
  next
    case schemes
    then show ?thesis by (auto intro: scheme)
  next
    case vars
    have "wf_ty \<Sigma> (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)"
      using wf_entry_var_ty[OF vars(1) wf(1)] wf_entry_var_ty[OF vars(2) wf(2)] by (rule wf_join)
    with vars show ?thesis by (auto intro: var join_upper)
  qed
qed

lemma merge_entry_above:
  assumes "wf_inst \<Sigma> \<eta>"
  shows "\<lbrakk> merge_cxt_entry \<Sigma> b (Some \<theta>) e = Some \<theta>'' ; wf_entry \<Sigma> \<theta> ; \<forall>\<theta>' \<in> set_option e. wf_entry \<Sigma> \<theta>' \<rbrakk>
      \<Longrightarrow> entry_above \<eta> \<theta> \<theta>''"
    and "\<lbrakk> merge_cxt_entry \<Sigma> b e (Some \<theta>) = Some \<theta>'' ; wf_entry \<Sigma> \<theta> ; \<forall>\<theta>' \<in> set_option e. wf_entry \<Sigma> \<theta>' \<rbrakk>
      \<Longrightarrow> entry_above \<eta> \<theta> \<theta>''"
proof -
  show "\<lbrakk> merge_cxt_entry \<Sigma> b (Some \<theta>) e = Some \<theta>'' ; wf_entry \<Sigma> \<theta> ; \<forall>\<theta>' \<in> set_option e. wf_entry \<Sigma> \<theta>' \<rbrakk>
    \<Longrightarrow> entry_above \<eta> \<theta> \<theta>''"
  proof (cases e)
    case (Some \<theta>')
    assume "merge_cxt_entry \<Sigma> b (Some \<theta>) e = Some \<theta>''" and "wf_entry \<Sigma> \<theta>"
      and "\<forall>\<theta>' \<in> set_option e. wf_entry \<Sigma> \<theta>'"
    with Some show ?thesis using merge_entry_above_both[OF assms, of b \<theta> \<theta>' \<theta>''] by simp
  qed (auto intro: possibly_unassigned_above)
  show "\<lbrakk> merge_cxt_entry \<Sigma> b e (Some \<theta>) = Some \<theta>'' ; wf_entry \<Sigma> \<theta> ; \<forall>\<theta>' \<in> set_option e. wf_entry \<Sigma> \<theta>' \<rbrakk>
    \<Longrightarrow> entry_above \<eta> \<theta> \<theta>''"
  proof (cases e)
    case (Some \<theta>')
    assume "merge_cxt_entry \<Sigma> b e (Some \<theta>) = Some \<theta>''" and "wf_entry \<Sigma> \<theta>"
      and "\<forall>\<theta>' \<in> set_option e. wf_entry \<Sigma> \<theta>'"
    with Some show ?thesis using merge_entry_above_both[OF assms, of b \<theta>' \<theta> \<theta>''] by simp
  qed (auto intro: possibly_unassigned_above)
qed

lemma merge_entry_unbound:
  "merge_cxt_entry \<Sigma> b None e = Some \<theta>'' \<Longrightarrow> \<turnstile> VUnbound : inst_entry \<eta> \<theta>''"
  "merge_cxt_entry \<Sigma> b e None = Some \<theta>'' \<Longrightarrow> \<turnstile> VUnbound : inst_entry \<eta> \<theta>''"
  by (cases e; auto dest: possibly_unassigned_unbound)+

(* Context \<Delta>' above \<Delta>: every entry of \<Delta> below the entry of \<Delta>', and a variable of \<Delta>' absent from \<Delta> possibly
   unassigned *)
definition cxt_above :: "(var \<Rightarrow> ty) \<Rightarrow> cxt \<Rightarrow> cxt \<Rightarrow> bool"
where
"cxt_above \<eta> \<Delta> \<Delta>' =
  (fmdom \<Delta> |\<subseteq>| fmdom \<Delta>'
   \<and> (\<forall>x \<theta> \<theta>'. fmlookup \<Delta> x = Some \<theta> \<longrightarrow> fmlookup \<Delta>' x = Some \<theta>' \<longrightarrow> entry_above \<eta> \<theta> \<theta>')
   \<and> (\<forall>x \<theta>'. fmlookup \<Delta> x = None \<longrightarrow> fmlookup \<Delta>' x = Some \<theta>' \<longrightarrow> \<turnstile> VUnbound : inst_entry \<eta> \<theta>'))"

lemma cxt_above_refl: "cxt_above \<eta> \<Delta> \<Delta>"
  by (simp add: cxt_above_def entry_above_refl)

lemma cxt_above_trans:
  assumes "cxt_above \<eta> \<Delta> \<Delta>'" and "cxt_above \<eta> \<Delta>' \<Delta>''"
  shows "cxt_above \<eta> \<Delta> \<Delta>''"
proof -
  have "entry_above \<eta> \<theta> \<theta>''" if "fmlookup \<Delta> x = Some \<theta>" and "fmlookup \<Delta>'' x = Some \<theta>''" for x \<theta> \<theta>''
  proof -
    from assms(1) have "fmdom \<Delta> |\<subseteq>| fmdom \<Delta>'" by (simp add: cxt_above_def)
    with that(1) have "x |\<in>| fmdom \<Delta>'" by (meson fmdomI fsubsetD)
    then obtain \<theta>' where \<theta>': "fmlookup \<Delta>' x = Some \<theta>'" by (auto simp: fmlookup_dom_iff)
    from assms(1) that(1) \<theta>' have "entry_above \<eta> \<theta> \<theta>'" by (simp add: cxt_above_def)
    moreover from assms(2) \<theta>' that(2) have "entry_above \<eta> \<theta>' \<theta>''" by (simp add: cxt_above_def)
    ultimately show ?thesis by (rule entry_above_trans)
  qed
  moreover have "\<turnstile> VUnbound : inst_entry \<eta> \<theta>''" if "fmlookup \<Delta> x = None" and "fmlookup \<Delta>'' x = Some \<theta>''"
    for x \<theta>''
  proof (cases "fmlookup \<Delta>' x")
    case None
    with assms(2) that(2) show ?thesis by (simp add: cxt_above_def)
  next
    case (Some \<theta>')
    with assms(1) that(1) have "\<turnstile> VUnbound : inst_entry \<eta> \<theta>'" by (simp add: cxt_above_def)
    moreover from assms(2) Some that(2) have "entry_above \<eta> \<theta>' \<theta>''" by (simp add: cxt_above_def)
    ultimately show ?thesis by (simp add: entry_above_def)
  qed
  ultimately show ?thesis using assms unfolding cxt_above_def by (blast intro: order_trans)
qed

(* Merge of two well-formed contexts, above each *)
lemma merge_above:
  assumes "merge \<Sigma> X \<Delta> \<Delta>' = Ok \<Delta>''" and wf\<eta>: "wf_inst \<Sigma> \<eta>" and wf: "wf_cxt \<Sigma> \<Delta>" "wf_cxt \<Sigma> \<Delta>'"
  shows "cxt_above \<eta> \<Delta> \<Delta>''" and "cxt_above \<eta> \<Delta>' \<Delta>''"
proof -
  have opt: "\<forall>\<theta> \<in> set_option (fmlookup \<Delta> x). wf_entry \<Sigma> \<theta>" "\<forall>\<theta> \<in> set_option (fmlookup \<Delta>' x). wf_entry \<Sigma> \<theta>" for x
    using wf by (auto simp: wf_cxt_iff split: option.splits)
  have dom: "fmdom \<Delta>'' = fmdom \<Delta> |\<union>| fmdom \<Delta>'" using merge_dom[OF assms(1)] by simp
  have lookup: "fmlookup \<Delta>'' x = merge_cxt_entry \<Sigma> (x \<in> X) (fmlookup \<Delta> x) (fmlookup \<Delta>' x)"
    if "x |\<in>| fmdom \<Delta>''" for x
    using merge_lookup[OF assms(1)] that dom by simp
  show "cxt_above \<eta> \<Delta> \<Delta>''"
    unfolding cxt_above_def
  proof (intro conjI allI impI)
    show "fmdom \<Delta> |\<subseteq>| fmdom \<Delta>''" by (simp add: dom)
  next
    fix x \<theta> \<theta>''
    assume "fmlookup \<Delta> x = Some \<theta>" and "fmlookup \<Delta>'' x = Some \<theta>''"
    with lookup[OF fmdomI[OF this(2)]] wf_cxt_lookup[OF wf(1) this(1)] opt(2)[of x] show "entry_above \<eta> \<theta> \<theta>''"
      by (auto intro: merge_entry_above(1)[OF wf\<eta>])
  next
    fix x \<theta>''
    assume "fmlookup \<Delta> x = None" and "fmlookup \<Delta>'' x = Some \<theta>''"
    with lookup[OF fmdomI[OF this(2)]] show "\<turnstile> VUnbound : inst_entry \<eta> \<theta>''"
      by (auto intro: merge_entry_unbound(1))
  qed
  show "cxt_above \<eta> \<Delta>' \<Delta>''"
    unfolding cxt_above_def
  proof (intro conjI allI impI)
    show "fmdom \<Delta>' |\<subseteq>| fmdom \<Delta>''" by (simp add: dom)
  next
    fix x \<theta> \<theta>''
    assume "fmlookup \<Delta>' x = Some \<theta>" and "fmlookup \<Delta>'' x = Some \<theta>''"
    with lookup[OF fmdomI[OF this(2)]] wf_cxt_lookup[OF wf(2) this(1)] opt(1)[of x] show "entry_above \<eta> \<theta> \<theta>''"
      by (auto intro: merge_entry_above(2)[OF wf\<eta>])
  next
    fix x \<theta>''
    assume "fmlookup \<Delta>' x = None" and "fmlookup \<Delta>'' x = Some \<theta>''"
    with lookup[OF fmdomI[OF this(2)]] show "\<turnstile> VUnbound : inst_entry \<eta> \<theta>''"
      by (auto intro: merge_entry_unbound(2))
  qed
qed

lemma merge_outcome_above:
  assumes "merge_outcome \<Sigma> X R R' = Ok R''" and wf\<eta>: "wf_inst \<Sigma> \<eta>"
    and wf: "\<forall>\<Delta> r. R = Assigns\<^sub>R \<Delta> r \<longrightarrow> wf_cxt \<Sigma> \<Delta>" "\<forall>\<Delta> r. R' = Assigns\<^sub>R \<Delta> r \<longrightarrow> wf_cxt \<Sigma> \<Delta>"
  shows "R = Assigns\<^sub>R \<Delta> r \<Longrightarrow> \<exists>\<Delta>'' r''. R'' = Assigns\<^sub>R \<Delta>'' r'' \<and> cxt_above \<eta> \<Delta> \<Delta>''"
    and "R' = Assigns\<^sub>R \<Delta> r \<Longrightarrow> \<exists>\<Delta>'' r''. R'' = Assigns\<^sub>R \<Delta>'' r'' \<and> cxt_above \<eta> \<Delta> \<Delta>''"
proof -
  let ?P = "\<exists>\<Delta>'' r''. R'' = Assigns\<^sub>R \<Delta>'' r'' \<and> cxt_above \<eta> \<Delta> \<Delta>''"
  have "(R = Assigns\<^sub>R \<Delta> r \<longrightarrow> ?P) \<and> (R' = Assigns\<^sub>R \<Delta> r \<longrightarrow> ?P)"
  proof (cases R)
    case (Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1)
    note R = this
    show ?thesis
    proof (cases R')
      case (Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2)
      with R assms obtain \<Delta>'' where m: "merge \<Sigma> X \<Delta>\<^sub>1 \<Delta>\<^sub>2 = Ok \<Delta>''"
        and R'': "R'' = Assigns\<^sub>R \<Delta>'' (if r\<^sub>2 = None then None else r\<^sub>1)"
        by (auto simp: bind_sum_Ok)
      from merge_above[OF m wf\<eta> wf(1)[rule_format, OF R] wf(2)[rule_format, OF Assigns\<^sub>R]] R R'' Assigns\<^sub>R
      show ?thesis by auto
    next
      case Returns\<^sub>R
      with R assms show ?thesis by (auto intro: cxt_above_refl)
    qed
  next
    case Returns\<^sub>R
    with assms show ?thesis by (cases R') (auto intro: cxt_above_refl)
  qed
  then show "R = Assigns\<^sub>R \<Delta> r \<Longrightarrow> ?P" and "R' = Assigns\<^sub>R \<Delta> r \<Longrightarrow> ?P" by blast+
qed

(* Merge of static outcomes, with bindings above those of each outcome which assigns *)
lemma merges_above:
  assumes "merges \<Sigma> X ms = Ok R''" and "Ok (Assigns\<^sub>R \<Delta> r) \<in> set ms" and wf\<eta>: "wf_inst \<Sigma> \<eta>"
    and wf: "\<And>\<Delta> r. Ok (Assigns\<^sub>R \<Delta> r) \<in> set ms \<Longrightarrow> wf_cxt \<Sigma> \<Delta>"
  obtains \<Delta>'' r'' where "R'' = Assigns\<^sub>R \<Delta>'' r''" and "cxt_above \<eta> \<Delta> \<Delta>''"
proof -
  let ?f = "\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }"
  from assms(1) obtain Rs where Rs: "those_sum ms = Ok Rs" and fold: "foldr ?f Rs (Ok Returns\<^sub>R) = Ok R''"
    by (auto simp: merges_def bind_sum_Ok)
  from those_sum_eq[OF Rs] assms(2) have "Assigns\<^sub>R \<Delta> r \<in> set Rs" by auto
  moreover have "\<And>\<Delta>' r'. Assigns\<^sub>R \<Delta>' r' \<in> set Rs \<Longrightarrow> wf_cxt \<Sigma> \<Delta>'" using those_sum_eq[OF Rs] wf by auto
  ultimately have "\<exists>\<Delta>'' r''. R'' = Assigns\<^sub>R \<Delta>'' r'' \<and> cxt_above \<eta> \<Delta> \<Delta>''" using fold
  proof (induction Rs arbitrary: R'')
    case (Cons R Rs)
    from Cons.prems(3) obtain R' where R': "foldr ?f Rs (Ok Returns\<^sub>R) = Ok R'"
      and m: "merge_outcome \<Sigma> X R R' = Ok R''"
      by (auto simp: bind_sum_Ok)
    have wfR: "\<forall>\<Delta>' r'. R = Assigns\<^sub>R \<Delta>' r' \<longrightarrow> wf_cxt \<Sigma> \<Delta>'" using Cons.prems(2) by auto
    have wfR': "\<forall>\<Delta>' r'. R' = Assigns\<^sub>R \<Delta>' r' \<longrightarrow> wf_cxt \<Sigma> \<Delta>'"
    proof (intro allI impI)
      fix \<Delta>' r'
      assume "R' = Assigns\<^sub>R \<Delta>' r'"
      show "wf_cxt \<Sigma> \<Delta>'"
        by (rule merge_fold_wf[OF R'[unfolded \<open>R' = Assigns\<^sub>R \<Delta>' r'\<close>]]) (meson Cons.prems(2) list.set_intros(2))
    qed
    show ?case
    proof (cases "R = Assigns\<^sub>R \<Delta> r")
      case True
      from merge_outcome_above(1)[OF m wf\<eta> wfR wfR' True] show ?thesis .
    next
      case False
      with Cons.prems(1) have "Assigns\<^sub>R \<Delta> r \<in> set Rs" by simp
      have "\<exists>\<Delta>' r'. R' = Assigns\<^sub>R \<Delta>' r' \<and> cxt_above \<eta> \<Delta> \<Delta>'"
        by (rule Cons.IH[OF \<open>Assigns\<^sub>R \<Delta> r \<in> set Rs\<close> _ R']) (meson Cons.prems(2) list.set_intros(2))
      then obtain \<Delta>' r' where "R' = Assigns\<^sub>R \<Delta>' r'" and "cxt_above \<eta> \<Delta> \<Delta>'" by blast
      with merge_outcome_above(2)[OF m wf\<eta> wfR wfR' this(1)] show ?thesis by (blast intro: cxt_above_trans)
    qed
  qed simp
  with that show thesis by blast
qed

(* Bindings of a branch, typed by the merge of the branches *)
lemma wf_env_merge:
  assumes env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and env': "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>" and dom: "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>"
    and above: "cxt_above \<eta> \<Delta> \<Delta>'" and wf: "wf_cxt \<Sigma> \<Delta>'"
    and bound: "\<And>x. x |\<in>| fmdom \<Delta>' \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))"
  shows "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>'"
proof (rule wf_env_add[OF env _ _ wf])
  show "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>'" using dom above unfolding cxt_above_def by (blast intro: order_trans)
next
  fix x \<theta>'
  assume look': "fmlookup \<Delta>' x = Some \<theta>'" and "\<theta>' \<noteq> TypeVar"
  show "\<exists>v. fmlookup (\<rho> \<otimes> \<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>'"
  proof (cases "fmlookup \<Delta> x")
    case (Some \<theta>)
    with above look' have ab: "entry_above \<eta> \<theta> \<theta>'" by (simp add: cxt_above_def)
    with \<open>\<theta>' \<noteq> TypeVar\<close> have "\<theta> \<noteq> TypeVar" by (simp add: entry_above_def)
    moreover from Some have "fmlookup (\<Gamma> \<otimes> \<Delta>) x = Some \<theta>" by (simp add: fmdomI)
    ultimately obtain v where "fmlookup (\<rho> \<otimes> \<rho>') x = Some v" and "\<turnstile> v : inst_entry \<eta> \<theta>"
      using wf_env_lookup[OF env'] by blast
    with ab show ?thesis by (auto simp: entry_above_def)
  next
    case None
    with dom have "x |\<notin>| fmdom \<rho>'" by (metis fmdom_notI fsubsetD)
    then have "fmlookup (\<rho> \<otimes> \<rho>') x = fmlookup \<rho> x" by simp
    moreover have "fmlookup \<rho> x = Some VUnbound"
      using bound[OF fmdomI[OF look']] env by (auto dest!: wf_env_lookup wf_val_unbound wf_val_du)
    moreover from above None look' have "\<turnstile> VUnbound : inst_entry \<eta> \<theta>'" by (simp add: cxt_above_def)
    ultimately show ?thesis by simp
  qed
qed

(* Soundness at one branch carries to the merge of the branches, when the bindings of every branch are over
   the type variables in scope and bind only variables unbound or declared beforehand *)
lemma wf_outcome_merges:
  assumes "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" and "Ok R \<in> set ms" and "merges \<Sigma> X ms = Ok R'" and env: "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and wf: "\<And>\<Delta> r. Ok (Assigns\<^sub>R \<Delta> r) \<in> set ms \<Longrightarrow> wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
    and bound: "\<And>\<Delta> r x. \<lbrakk> Ok (Assigns\<^sub>R \<Delta> r) \<in> set ms ; x |\<in>| fmdom \<Delta> \<rbrakk>
                 \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
proof -
  obtain vs \<omega> where o: "o = (vs, \<omega>)" by (cases o)
  show ?thesis
  proof (cases \<omega>)
    case (Assigns \<rho>')
    with assms(1) o obtain \<Delta> r where R: "R = Assigns\<^sub>R \<Delta> r" and dom: "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>"
      and env': "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>"
      by (cases R) auto
    from assms(2) R have mem: "Ok (Assigns\<^sub>R \<Delta> r) \<in> set ms" by simp
    obtain \<Delta>' r' where R': "R' = Assigns\<^sub>R \<Delta>' r'" and above: "cxt_above \<eta> \<Delta> \<Delta>'"
      by (rule merges_above[OF assms(3) mem wf_env_wf_inst[OF env]]) (use wf in blast)
    from merges_wf[OF assms(3)[unfolded R'] wf] have wf': "wf_cxt \<Sigma> \<Delta>'" by auto
    have bound': "fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))" if "x |\<in>| fmdom \<Delta>'" for x
      using assms(3) R' that bound by (auto elim: merges_dom)
    have "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>'" using env env' dom above wf' bound' by (rule wf_env_merge)
    moreover have "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>'" using dom above unfolding cxt_above_def by (blast intro: order_trans)
    ultimately show ?thesis by (simp add: o Assigns R')
  qed (use assms(1) in \<open>simp_all add: o\<close>)
qed

(* Soundness at one branch of an if statement carries to the merge of the branches *)
lemma wf_outcome_merge_if:
  assumes "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" and "R \<in> set Rs"
    and "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and "merges \<Sigma> X (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R'" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
proof (rule wf_outcome_merges[OF assms(1) _ assms(4, 5)])
  show "Ok R \<in> set (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))"
    using those_sum_eq[OF assms(3)] assms(2) by auto
next
  fix \<Delta> r
  assume "Ok (Assigns\<^sub>R \<Delta> r) \<in> set (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))"
  then consider s' where "check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta> r)" | "\<Delta> = fmempty"
    using check_elif_branch by blast
  then show "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
  proof cases
    case 1
    then show ?thesis by (rule check_stmt_at_wf_cxt[OF wf_env_wf_cxt[OF assms(5)]])
  next
    case 2
    then show ?thesis by simp
  qed
next
  fix \<Delta> r x
  assume "Ok (Assigns\<^sub>R \<Delta> r) \<in> set (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))"
    and "x |\<in>| fmdom \<Delta>"
  with check_elif_branch[OF this(1)] show "fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))"
    by (auto dest: check_stmt_bound(2))
qed

lemma if_true_sound:
  assumes "sound_stmt \<rho> (node s) o"
  shows "sound_stmt \<rho> (StmtIf e s elifs else') o"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
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

(* Member of the merged outcomes of a match statement with bindings: well-formed over the type variables in
   scope, binding variables unbound or declared but unassigned *)
lemma match_branches_member:
  assumes mc: "match_cases \<Sigma> \<Gamma> \<sigma> L\<^sub>0 (map fst cases) = Ok (\<Delta>s, \<tau>, L)" and wf\<Gamma>: "wf_cxt \<Sigma> \<Gamma>" and wf\<sigma>: "wf_ty \<Sigma> \<sigma>"
    and fv\<sigma>: "fv \<sigma> \<subseteq> tyvars \<Gamma>" and mem: "Ok (Assigns\<^sub>R \<Delta> r) \<in> set (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s cases \<tau> L)"
  shows "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
    and "x |\<in>| fmdom \<Delta> \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>'. fmlookup \<Gamma> x = Some (DU \<tau>'))"
proof -
  let ?f = "\<lambda>\<Delta> (_, s). do { R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) }"
  have "(wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>)
        \<and> (x |\<in>| fmdom \<Delta> \<longrightarrow> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>'. fmlookup \<Gamma> x = Some (DU \<tau>')))"
  proof (cases "Ok (Assigns\<^sub>R \<Delta> r) \<in> set (map2 ?f \<Delta>s cases)")
    case True
    then obtain \<Delta>\<^sub>i c where zip: "(\<Delta>\<^sub>i, c) \<in> set (zip \<Delta>s cases)" and f: "?f \<Delta>\<^sub>i c = Ok (Assigns\<^sub>R \<Delta> r)" by auto
    obtain p s where c: "c = (p, s)" by (cases c)
    from f obtain R' where chk': "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>i) \<zeta> s = Ok R'"
      and eq: "Assigns\<^sub>R \<Delta>\<^sub>i None \<otimes> R' = Assigns\<^sub>R \<Delta> r"
      unfolding c by (auto simp: bind_sum_Ok)
    then obtain \<Delta>' r' where "R' = Assigns\<^sub>R \<Delta>' r'" and \<Delta>: "\<Delta> = \<Delta>\<^sub>i \<otimes> \<Delta>'" by (cases R') auto
    with chk' have chk: "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>i) \<zeta> s = Ok (Assigns\<^sub>R \<Delta>' r')" by simp
    have \<Delta>\<^sub>i: "\<Delta>\<^sub>i \<in> set \<Delta>s" using set_zip_leftD[OF zip] .
    from match_cases_wf[OF wf_class_table wf\<Gamma> wf\<sigma> mc \<Delta>\<^sub>i] have wf\<^sub>i: "wf_cxt \<Sigma> \<Delta>\<^sub>i" and tv\<^sub>i: "tyvars \<Delta>\<^sub>i \<subseteq> fv \<sigma>" by auto
    from check_stmt_at_wf_cxt[OF wf_cxt_add[OF wf\<Gamma> wf\<^sub>i] chk] tyvars_add[of \<Gamma> \<Delta>\<^sub>i]
    have wf': "wf_cxt \<Sigma> \<Delta>'" and tv': "tyvars \<Delta>' \<subseteq> tyvars \<Gamma> \<union> tyvars \<Delta>\<^sub>i" by auto
    have wf: "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
      using wf_cxt_add[OF wf\<^sub>i wf'] tyvars_add[of \<Delta>\<^sub>i \<Delta>'] tv\<^sub>i tv' fv\<sigma> unfolding \<Delta> by blast
    have "fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>'. fmlookup \<Gamma> x = Some (DU \<tau>'))" if x: "x |\<in>| fmdom \<Delta>"
    proof (cases "x |\<in>| fmdom \<Delta>\<^sub>i")
      case True
      then show ?thesis using match_cases_unbound[OF mc \<Delta>\<^sub>i] by blast
    next
      case False
      with x have "x |\<in>| fmdom \<Delta>'" unfolding \<Delta> by simp
      from check_stmt_bound(2)[OF chk this] False show ?thesis by auto
    qed
    with wf show ?thesis by blast
  next
    case False
    with mem have "\<Delta> = fmempty" by (auto simp: match_branches_def split: if_splits)
    then show ?thesis by simp
  qed
  then show "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>"
    and "x |\<in>| fmdom \<Delta> \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>'. fmlookup \<Gamma> x = Some (DU \<tau>'))"
    by blast+
qed

lemma match_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and disp: "dispatch \<rho> v cases = Val (\<rho>', s')"
    and "sound_stmt (\<rho> \<otimes> \<rho>') (node s') o"
  shows "sound_stmt \<rho> (StmtMatch e cases) (assigns\<^sub>o \<rho>' \<otimes> o)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMatch e cases) = Ok R"
  from check_match[OF chk] obtain \<sigma> \<Delta>s \<tau> L where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
    and mc: "match_cases \<Sigma> \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst cases) = Ok (\<Delta>s, \<tau>, L)"
    and merges: "merges \<Sigma> (set (declares (StmtMatch e cases))) (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s cases \<tau> L) = Ok R"
    by blast
  let ?ms = "match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s cases \<tau> L"
  have v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)" using sound_expr_synth_at[OF assms(1) env synth] by simp
  note wf\<Gamma> = wf_env_wf_cxt[OF env]
  have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" and fv\<sigma>: "fv \<sigma> \<subseteq> tyvars \<Gamma>" using synth_at_wf_ty[OF wf\<Gamma> synth] synth_at_tyvars[OF wf\<Gamma> synth] by auto
  have len: "length \<Delta>s = length cases" using match_cases_length[OF mc] by simp
  from merges_Ok[OF merges] obtain Rs where Rs: "those_sum ?ms = Ok Rs" by blast
  note member = match_branches_member[OF mc wf\<Gamma> wf\<sigma> fv\<sigma>]
  have lift: "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<rho>' \<otimes> o) R"
    if "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<rho>' \<otimes> o) R'" and "Ok R' \<in> set ?ms" for R'
  proof (rule wf_outcome_merges[OF that merges env])
    fix \<Delta> r
    assume "Ok (Assigns\<^sub>R \<Delta> r) \<in> set ?ms"
    then show "wf_cxt \<Sigma> \<Delta> \<and> tyvars \<Delta> \<subseteq> tyvars \<Gamma>" by (rule member(1))
  next
    fix \<Delta> r x
    assume "Ok (Assigns\<^sub>R \<Delta> r) \<in> set ?ms" and "x |\<in>| fmdom \<Delta>"
    then show "fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))" by (rule member(2))
  qed
  from dispatch_sound[OF mc env wf\<sigma> v] show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<rho>' \<otimes> o) R"
  proof (elim disjE exE conjE)
    fix i \<rho>''
    assume i: "i < length cases" and disp': "dispatch \<rho> v cases = Val (\<rho>'', snd (cases ! i))"
      and dom: "fmdom \<rho>'' |\<subseteq>| fmdom (\<Delta>s ! i)" and env': "\<eta> \<turnstile> \<rho> \<otimes> \<rho>'' : \<Gamma> \<otimes> (\<Delta>s ! i)"
    from disp disp' have \<rho>'': "\<rho>'' = \<rho>'" and s': "s' = snd (cases ! i)" by simp_all
    let ?f = "\<lambda>\<Delta> (_, s). do { R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) }"
    have "map2 ?f \<Delta>s cases ! i = ?f (\<Delta>s ! i) (cases ! i)" using i len by simp
    moreover have "map2 ?f \<Delta>s cases ! i \<in> set (map2 ?f \<Delta>s cases)" using i len by (intro nth_mem) simp
    ultimately have "?f (\<Delta>s ! i) (cases ! i) \<in> set ?ms" by (simp add: match_branches_def)
    with Rs obtain R\<^sub>i where chk\<^sub>i: "check_stmt_at \<Sigma> (\<Gamma> \<otimes> (\<Delta>s ! i)) \<zeta> (snd (cases ! i)) = Ok R\<^sub>i"
      and mem: "Ok (Assigns\<^sub>R (\<Delta>s ! i) None \<otimes> R\<^sub>i) \<in> set ?ms"
      using those_sum_eq[OF Rs] by (cases "cases ! i") (auto simp: bind_sum_def split: sum.splits)
    have o2: "wf_outcome \<eta> (\<rho> \<otimes> \<rho>') (\<Gamma> \<otimes> (\<Delta>s ! i)) \<zeta> o R\<^sub>i"
      using assms(3) env'[unfolded \<rho>''] ret chk\<^sub>i unfolding s' by (rule sound_stmt_at)
    obtain vs' \<omega>' where o: "o = (vs', \<omega>')" by (cases o)
    have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<rho>' \<otimes> o) (Assigns\<^sub>R (\<Delta>s ! i) None \<otimes> R\<^sub>i)"
    proof (cases \<omega>')
      case (Assigns \<rho>\<^sub>2)
      with o2 o obtain \<Delta>' where "bindings_of R\<^sub>i = Some \<Delta>'" and "fmdom \<rho>\<^sub>2 |\<subseteq>| fmdom \<Delta>'"
        and "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' \<otimes> \<rho>\<^sub>2 : \<Gamma> \<otimes> (\<Delta>s ! i) \<otimes> \<Delta>'"
        by auto
      moreover from this(1) obtain r' where "R\<^sub>i = Assigns\<^sub>R \<Delta>' r'" by (cases R\<^sub>i) auto
      ultimately show ?thesis using dom unfolding \<rho>'' by (auto simp: o Assigns intro: le_supI1 le_supI2)
    qed (use o2 in \<open>simp_all add: o\<close>)
    from lift[OF this mem] show ?thesis .
  next
    assume disp': "dispatch \<rho> v cases = Val (fmempty, At no_pos StmtPass)" and v\<tau>: "\<turnstile> v : Ty (inst \<eta> \<tau>)"
    from disp disp' have \<rho>': "\<rho>' = fmempty" and s': "s' = At no_pos StmtPass" by simp_all
    have "\<tau> \<noteq> TyPrim Never" using v\<tau> wf_val_never by auto
    then have mem: "Ok (Assigns\<^sub>R fmempty (if L = [] then Some (MypyCompatibility (Violates RuleMatchPartial (MissingReturnMatchPartial \<tau>))) else None))
                    \<in> set ?ms"
      by (simp add: match_branches_def)
    have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o (Assigns\<^sub>R fmempty None)"
      using assms(3) env ret unfolding \<rho>' s' sound_stmt_def by simp
    then have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<rho>' \<otimes> o)
                 (Assigns\<^sub>R fmempty (if L = [] then Some (MypyCompatibility (Violates RuleMatchPartial (MissingReturnMatchPartial \<tau>))) else None))"
      unfolding \<rho>' by (cases o; cases "snd o") (auto simp: wf_completion_bindings)
    from lift[OF this mem] show ?thesis .
  next
    fix \<kappa>
    assume "dispatch \<rho> v cases = Aborts \<kappa>"
    with disp show ?thesis by simp
  qed
qed

lemma match_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def by (auto simp: bind_sum_def dest: sound_expr_synth_at split: sum.splits)

lemma match_abort_sound:
  assumes "sound_expr \<rho> (node e) (Val v)" and disp: "dispatch \<rho> v cases = Aborts \<kappa>"
  shows "sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMatch e cases) = Ok R"
  from check_match[OF chk] obtain \<sigma> \<Delta>s \<tau> L where synth: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
    and mc: "match_cases \<Sigma> \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst cases) = Ok (\<Delta>s, \<tau>, L)"
    and "merges \<Sigma> (set (declares (StmtMatch e cases))) (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s cases \<tau> L) = Ok R"
    by blast
  have v: "\<turnstile> v : Ty (inst \<eta> \<sigma>)" using sound_expr_synth_at[OF assms(1) env synth] by simp
  note wf\<Gamma> = wf_env_wf_cxt[OF env]
  have wf\<sigma>: "wf_ty \<Sigma> \<sigma>" using synth_at_wf_ty[OF wf\<Gamma> synth] .
  from dispatch_sound[OF mc env wf\<sigma> v] disp show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R" by auto
qed

lemma seq_sound:
  assumes "sound_stmt \<rho> (node s) (us, Assigns \<rho>')" and "sound_stmt (\<rho> \<otimes> \<rho>') (node s') o"
  shows "sound_stmt \<rho> (StmtSeq s s') ((us, Assigns \<rho>') \<otimes> o)"
proof (rule sound_stmtI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R"
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R"
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>" and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ([], Some s)) = Ok Rs"
  from chk obtain R where "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R" and "Rs = [R]"
    by (auto simp: bind_sum_def split: sum.splits)
  with assms env ret show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" by (auto intro: sound_stmt_at)
qed

lemma elif_true_sound:
  assumes "sound_stmt \<rho> (node s) o"
  shows "sound_elif \<rho> ((e, s) # elifs, else') o"
proof (rule sound_elifI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>"
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
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<zeta>"
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
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val Def(\<rho>', ds, j)" and "sound_expr \<rho> (node e) (Val Def(\<rho>', ds, j))"
    and d: "node (ds ! j) = Def f \<alpha>s xps \<psi> s" and vs: "vs = map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds]"
    and "sound_exprs \<rho> es (Val us)" and "length xps = length us"
    and scope: "scope VUnbound (map fst xps) s = Some \<rho>s"
    and body:
      "sound_stmt (\<rho>' \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) vs)
                     \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s) (node s) ([], \<omega>)"
    and j: "j < length ds"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (result_of \<omega>)"
proof (rule call_callable_exprI[OF assms(1, 2)])
  fix \<eta> \<Gamma> \<sigma>s \<tau>'
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and v: "\<turnstile> Def(\<rho>', ds, j) : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))"
    and es: "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<sigma>s"
  let ?xs = "map (def_name \<circ> node) ds"
  from v obtain \<eta>' \<Gamma>' \<pi>s \<alpha>s' \<sigma>s\<^sub>d \<tau>\<^sub>d \<tau>s where env': "\<eta>' \<turnstile> \<rho>' : \<Gamma>'" and checked: "defs_checked \<Gamma>' ds \<pi>s"
    and "j < length ds" and \<pi>: "\<pi>s ! j = TyScheme \<alpha>s' (TyCallable \<sigma>s\<^sub>d \<tau>\<^sub>d)"
    and "length \<tau>s = length \<alpha>s'" and closed_wf: "\<forall>\<tau>' \<in> set \<tau>s. fv \<tau>' = {} \<and> wf_ty \<Sigma> \<tau>'"
    and sub: "\<Sigma> \<turnstile> inst (inst_params \<alpha>s' \<tau>s \<eta>') (TyCallable \<sigma>s\<^sub>d \<tau>\<^sub>d) <: inst \<eta> (TyCallable \<sigma>s \<tau>')"
    and wf: "wf_ty \<Sigma> (inst (inst_params \<alpha>s' \<tau>s \<eta>') (TyCallable \<sigma>s\<^sub>d \<tau>\<^sub>d))"
    by (rule wf_def)
  from wf have "\<forall>\<sigma> \<in> set (map (inst (inst_params \<alpha>s' \<tau>s \<eta>')) \<sigma>s\<^sub>d). wf_ty \<Sigma> \<sigma>" by simp
  note args = callable_args[OF sub[unfolded inst.simps] this assms(5) env es]
  show "result_typed (result_of \<omega>) (inst \<eta> \<tau>')"
  proof -
    from checked have sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma>' (node d))) ds) = Ok \<pi>s"
      and defs: "all_sum (map2 (check_def_at \<Sigma> (\<Gamma>' \<otimes> fmap_of_list (zip ?xs (map signature_entry \<pi>s)))) ds \<pi>s)
                  = Ok ()"
      and disjoint: "\<forall>d \<in> set ds. case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma>' = {}"
      by (simp_all add: defs_checked_def)
    let ?\<Delta> = "fmap_of_list (zip ?xs (map signature_entry \<pi>s))"
    let ?\<eta> = "inst_params \<alpha>s \<tau>s \<eta>'"
    have len: "length \<pi>s = length ds" using those_sum_map_Ok[OF sigs] by (simp add: list_all2_lengthD)
    have sig: "def_signature \<Sigma> \<Gamma>' (Def f \<alpha>s xps \<psi> s) = Ok (TyScheme \<alpha>s' (TyCallable \<sigma>s\<^sub>d \<tau>\<^sub>d))"
      using those_sum_map_Ok[OF sigs] j by (auto simp: list_all2_conv_all_nth d[symmetric] \<pi>[symmetric])
    from def_signature_Ok[OF this] have \<alpha>s': "\<alpha>s' = \<alpha>s" .
    with \<pi> have \<pi>': "\<pi>s ! j = TyScheme \<alpha>s (TyCallable \<sigma>s\<^sub>d \<tau>\<^sub>d)" by simp
    have wf_\<tau>\<^sub>d: "wf_ty \<Sigma> \<tau>\<^sub>d" using def_signature_wf[OF wf_env_wf_cxt[OF env'] sig] by (cases \<alpha>s') auto
    from disjoint d j have disjoint_j: "set \<alpha>s \<inter> tyvars \<Gamma>' = {}" by (auto dest!: bspec[OF _ nth_mem])
    from all_sum_map2_Ok[OF defs len[symmetric]] j
    have "check_def_at \<Sigma> (\<Gamma>' \<otimes> ?\<Delta>) (ds ! j) (\<pi>s ! j) = Ok ()" by (auto simp: list_all2_conv_all_nth)
    then have "check_def \<Sigma> (\<Gamma>' \<otimes> ?\<Delta>) (Def f \<alpha>s xps \<psi> s) (TyScheme \<alpha>s (TyCallable \<sigma>s\<^sub>d \<tau>\<^sub>d)) = Ok ()"
      by (cases "ds ! j") (simp add: d[symmetric] \<pi>'[symmetric])
    then obtain \<Delta> \<Delta>' R where \<Delta>: "scope Unbound (map fst xps) s = Some \<Delta>" and len_\<sigma>s: "length xps = length \<sigma>s\<^sub>d"
      and \<Delta>': "params_cxt (map fst xps) \<sigma>s\<^sub>d = Ok \<Delta>'"
      and chk: "check_stmt_at \<Sigma> (\<Gamma>' \<otimes> ?\<Delta> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> \<Delta>' \<otimes> \<Delta>) (Some \<tau>\<^sub>d) s = Ok R"
      and R: "R = Returns\<^sub>R \<or> (\<exists>\<Delta>'' r. R = Assigns\<^sub>R \<Delta>'' r \<and> \<Sigma> \<turnstile> \<tau>\<^sub>d \<approx> TyPrim NoneType)"
      by (rule check_def_Ok)
    (* Instantiation of the body: that of the closure, with the type parameters at the type arguments *)
    have wf_\<eta>: "wf_inst \<Sigma> ?\<eta>" using wf_env_wf_inst[OF env'] closed_wf by (rule wf_inst_params)
    (* Environment of the body *)
    have env_defs: "\<eta>' \<turnstile> \<rho>' \<otimes> fmap_of_list (zip ?xs vs) : \<Gamma>' \<otimes> ?\<Delta>"
      using env' sigs defs disjoint vs by (rule wf_env_defs)
    have "?\<eta> \<turnstile> \<rho>' \<otimes> fmap_of_list (zip ?xs vs) : \<Gamma>' \<otimes> ?\<Delta>"
    proof (rule wf_env_inst[OF env_defs wf_\<eta>])
      fix \<alpha>
      assume "\<alpha> \<in> tyvars (\<Gamma>' \<otimes> ?\<Delta>)"
      with tyvars_add defs_wf[OF wf_env_wf_cxt[OF env'] sigs] have "\<alpha> \<in> tyvars \<Gamma>'" by blast
      with disjoint_j have "\<alpha> \<notin> set \<alpha>s" by blast
      then show "?\<eta> \<alpha> = \<eta>' \<alpha>" by simp
    qed
    then have env_params: "?\<eta> \<turnstile> \<rho>' \<otimes> fmap_of_list (zip ?xs vs) : \<Gamma>' \<otimes> ?\<Delta> \<otimes> fmconst (set \<alpha>s) TypeVar"
      by (rule wf_env_type_params)
    from args(1) have us': "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty (inst ?\<eta> \<sigma>)) us \<sigma>s\<^sub>d" by (simp add: \<alpha>s' list.rel_map)
    have len_xs: "length (map fst xps) = length \<sigma>s\<^sub>d" using len_\<sigma>s by simp
    from wf_env_params[OF env_params \<Delta>' len_xs us']
    have "?\<eta> \<turnstile> \<rho>' \<otimes> fmap_of_list (zip ?xs vs) \<otimes> fmap_of_list (zip (map fst xps) us)
      : \<Gamma>' \<otimes> ?\<Delta> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> \<Delta>'" .
    then have env_body: "?\<eta> \<turnstile> \<rho>' \<otimes> fmap_of_list (zip ?xs vs) \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s
      : \<Gamma>' \<otimes> ?\<Delta> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> \<Delta>' \<otimes> \<Delta>"
      using scope_stmt_Some[OF scope] scope_stmt_Some[OF \<Delta>] by (simp add: wf_env_unbound)
    have "wf_outcome ?\<eta> (\<rho>' \<otimes> fmap_of_list (zip ?xs vs) \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s)
      (\<Gamma>' \<otimes> ?\<Delta> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> \<Delta>' \<otimes> \<Delta>) (Some \<tau>\<^sub>d) ([], \<omega>) R"
      using body env_body wf_\<tau>\<^sub>d chk by (intro sound_stmt_at) simp_all
    then have "result_typed (result_of \<omega>) (inst ?\<eta> \<tau>\<^sub>d)"
    proof (cases \<omega>)
      case (Assigns \<rho>'')
      with \<open>wf_outcome _ _ _ _ _ _\<close> R have "\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>\<^sub>d" by (cases R) auto
      from wf_none[OF this wf_\<tau>\<^sub>d wf_\<eta>] show ?thesis by (simp add: Assigns)
    qed simp_all
    moreover have "wf_ty \<Sigma> (inst \<eta> \<tau>')" using wf_val_ty[OF v] by simp
    ultimately show ?thesis using args(2) \<alpha>s' by (cases \<omega>) (auto intro: wf_val_sub)
  qed
qed simp_all

end

end
