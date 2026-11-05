(* Soundness of statement evaluation *)
theory Statements
  imports Expressions
begin

type_synonym elif_block = "(expr located \<times> stmt located) list \<times> stmt located option"

(* Static outcomes of the branches of an elif block, as listed by the if rule *)
fun check_elif :: "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> elif_block \<Rightarrow> static_outcome may_fail list"
where
"check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else') =
  map (\<lambda>(e', s'). do { check_expr_at \<Sigma> \<Gamma> e' (TyPrim bool); check_stmt_at \<Sigma> \<Gamma> \<zeta> s' }) elifs
  @ [case else' of Some s' \<Rightarrow> check_stmt_at \<Sigma> \<Gamma> \<zeta> s' | None \<Rightarrow> Ok (Assigns\<^sub>R fmempty None)]"

lemma merges_Ok: "merges \<Sigma> X ms = Ok R \<Longrightarrow> \<exists>Rs. those_sum ms = Ok Rs"
  by (auto simp: merges_def bind_sum_def split: sum.splits)

lemma check_stmt_if:
  "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = do {
     check_expr_at \<Sigma> \<Gamma> e (TyPrim bool);
     merges \<Sigma> (set (declares (StmtIf e s elifs else')))
       (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))
   }"
  by simp

(* Return type over the type variables bound by \<eta> *)
fun wf_return :: "(var \<times> ty) list \<Rightarrow> ty option \<Rightarrow> bool"
where
"wf_return \<eta> (Some \<tau>) = (fv \<tau> \<subseteq> fst ` set \<eta>)" |
"wf_return \<eta> None = True"

fun bindings_of :: "static_outcome \<Rightarrow> cxt option"
where
"bindings_of (Assigns\<^sub>R \<Delta> _) = Some \<Delta>" |
"bindings_of Returns\<^sub>R = None"

lemma check_stmt_at_Ok:
  assumes "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R"
  shows "\<exists>R'. check_stmt \<Sigma> \<Gamma> \<zeta> (node s) = Ok R' \<and> bindings_of R' = bindings_of R"
proof (cases s)
  case (At p s')
  then show ?thesis using assms by (cases "check_stmt \<Sigma> \<Gamma> \<zeta> s'") (auto split: static_outcome.splits)
qed

lemma check_seq:
  "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R
  \<Longrightarrow> \<exists>\<Delta> r R'. check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r) \<and> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s' = Ok R'
     \<and> R = Assigns\<^sub>R \<Delta> r \<otimes> R'"
  by (auto simp: bind_sum_def split: sum.splits static_outcome.splits)

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

subsection \<open>Statements\<close>

lemma pass_sound: "sound_stmt \<rho> StmtPass (assigns\<^sub>o \<epsilon>)"
  by (simp add: sound_stmt_def)

lemma declare_sound: "sound_stmt \<rho> (StmtDeclare x \<psi>) (assigns\<^sub>o \<epsilon>)"
  unfolding sound_stmt_def
proof (intro allI impI)
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
  unfolding sound_stmt_def
proof (intro allI impI)
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
  unfolding sound_stmt_def
proof (intro allI impI)
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
  unfolding sound_stmt_def
proof (intro allI impI)
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
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn (Some e)) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with ret have fv: "fv \<tau> \<subseteq> fst ` set \<eta>" by simp
  from chk \<zeta> have "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()" by (auto simp: bind_sum_def split: sum.splits)
  with assms env fv have "result_typed r (inst \<eta> \<tau>)" by (auto dest: sound_expr_check_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r returns\<^sub>o) R" by (cases r) (simp_all add: \<zeta>)
qed

lemma return_none_sound: "sound_stmt \<rho> (StmtReturn None) (returns\<^sub>o (VLit LitNone))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn None) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with chk have "\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>" by (auto split: if_splits)
  then have "\<turnstile> VLit LitNone : Ty (inst \<eta> \<tau>)"
    by (intro ValSub[OF ValLit] SubtyLiteral)
       (auto dest: subst_subty[where \<tau>s = "map snd \<eta>" and \<alpha>s = "map fst \<eta>"])
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (returns\<^sub>o (VLit LitNone)) R" by (simp add: \<zeta>)
qed

lemma defs_sound:
  "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]
  \<Longrightarrow> sound_stmt \<rho> (StmtMutualRegion ds) (assigns\<^sub>o (fmap_of_list (zip (map (def_name \<circ> node) ds) vs)))"
  sorry

lemma literal_false: "\<rho>, ExprLiteral (LitBool False) \<Rightarrow>\<^sub>e r \<Longrightarrow> r = Val false"
  by (auto elim!: LiteralE)

(* Static outcome of an assertion whose condition does not evaluate to false: the condition checks as a Boolean
   and nothing is assigned *)
lemma check_assert:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R" and "\<rho>, node e \<Rightarrow>\<^sub>e r" and "r \<noteq> Val false"
  shows "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok () \<and> (\<exists>r'. R = Assigns\<^sub>R fmempty r')"
  using assms by (auto simp: Let_def bind_sum_def split: sum.splits option.splits if_splits dest: literal_false)

lemma check_assert_msg:
  "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R \<Longrightarrow> check_expr_at \<Sigma> \<Gamma> e' (TyPrim str) = Ok ()"
  by (auto simp: Let_def bind_sum_def split: sum.splits if_splits)

lemma assert_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val true"
  shows "sound_stmt \<rho> (StmtAssert e e') (assigns\<^sub>o \<epsilon>)"
  unfolding sound_stmt_def
proof (intro allI impI)
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
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R"
  from check_assert[OF chk assms(1)] have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()" by simp
  with assms(2) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R" by (auto dest: prim_operand)
qed

lemma assert_nonbool_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val v" and "sound_expr \<rho> (node e) (Val v)" and "v \<notin> {true, false}"
  shows "sound_stmt \<rho> (StmtAssert e e') (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R"
  from check_assert[OF chk assms(1)] assms(3) have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()" by simp
  with assms(2, 3) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o Excluded) R" by (auto dest!: bool_operand)
qed

lemma assert_msg_false_fail_sound:
  assumes "sound_expr \<rho> (node e') (Aborts \<kappa>)"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert_msg[OF chk] assms env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R"
    by (auto dest: prim_operand)
qed

lemma assert_msg_nonstr_sound:
  assumes "sound_expr \<rho> (node e') (Val v)" and "\<forall>w. v \<noteq> VLit (LitString w)"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert_msg[OF chk] assms env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o Excluded) R"
    by (auto dest!: str_operand)
qed

lemma check_stmt_bound:
  "\<lbrakk> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r) ; fmlookup \<Delta> x = Some \<theta> \<rbrakk>
  \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))"
  sorry

(* Soundness at one branch of an if statement carries to the merge of the branches *)
lemma wf_outcome_merge_if:
  assumes "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" and "R \<in> set Rs"
    and "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and "merges \<Sigma> X (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R'" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
  sorry

lemma check_if:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  shows "\<exists>Rs. those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs
     \<and> merges \<Sigma> (set (declares (StmtIf e s elifs else')))
         (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R"
  using assms by (auto simp: check_stmt_if bind_sum_def split: sum.splits dest: merges_Ok)

lemma if_true_sound:
  assumes "sound_expr \<rho> (node e) (Val true)" and "sound_stmt \<rho> (node s) o"
  shows "sound_stmt \<rho> (StmtIf e s elifs else') o"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  from check_if[OF chk] obtain Rs
    where Rs: "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and R: "merges \<Sigma> (set (declares (StmtIf e s elifs else')))
              (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R"
    by blast
  from Rs obtain R0 where R0: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R0" and "R0 \<in> set Rs"
    by (auto simp: bind_sum_def split: sum.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R0" using assms(2) env ret R0 by (rule sound_stmt_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using \<open>R0 \<in> set Rs\<close> Rs R env by (rule wf_outcome_merge_if)
qed

lemma if_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_elif \<rho> (elifs, else') o"
  shows "sound_stmt \<rho> (StmtIf e s elifs else') o"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  from check_if[OF chk] obtain Rs
    where Rs: "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and R: "merges \<Sigma> (set (declares (StmtIf e s elifs else')))
              (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R"
    by blast
  from Rs obtain R0 Rs' where Rs': "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs'" and "Rs = R0 # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  with assms(2) env ret obtain R' where "R' \<in> set Rs'" and "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
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
  unfolding sound_stmt_def
proof (intro allI impI)
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
  unfolding sound_stmt_def
proof (intro allI impI)
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
  unfolding sound_elif_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ([], Some s)) = Ok Rs"
  from chk obtain R where "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R" and "Rs = [R]"
    by (auto simp: bind_sum_def split: sum.splits)
  with assms env ret show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" by (auto intro: sound_stmt_at)
qed

lemma elif_true_sound:
  assumes "sound_expr \<rho> (node e) (Val true)" and "sound_stmt \<rho> (node s) o"
  shows "sound_elif \<rho> ((e, s) # elifs, else') o"
  unfolding sound_elif_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>"
    and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs, else')) = Ok Rs"
  from chk obtain R Rs' where R: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R" and Rs: "Rs = R # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using assms(2) env ret R by (rule sound_stmt_at)
  then show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" by (auto simp: Rs)
qed

lemma elif_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_elif \<rho> (elifs, else') o"
  shows "sound_elif \<rho> ((e, s) # elifs, else') o"
  unfolding sound_elif_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>"
    and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs, else')) = Ok Rs"
  from chk obtain R Rs' where "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs'" and "Rs = R # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  then show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using assms(2) env ret unfolding sound_elif_def by auto
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
