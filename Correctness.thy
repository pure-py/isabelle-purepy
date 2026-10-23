theory Correctness
    imports Eval
begin

lemma flet_case:
  "flet m f =
    (case m of Done (Val v) \<Rightarrow> f v | Done (Aborts \<kappa>) \<Rightarrow> Done (Aborts \<kappa>) | Stuck \<Rightarrow> Stuck | OutOfFuel \<Rightarrow> OutOfFuel)"
  by (cases "(m, f)" rule: flet.cases) simp_all

lemma mlet_case: "mlet_result r f = (case r of Val v \<Rightarrow> f v | Aborts \<kappa> \<Rightarrow> Aborts \<kappa>)"
  by (cases r) simp_all

lemma as_bool_Some: "as_bool v = Some b \<longleftrightarrow> v = VLit (LitBool b)"
  by (cases v rule: as_bool.cases) auto

lemma as_bool_None: "as_bool v = None \<longleftrightarrow> v \<notin> {true, false}"
  by (cases v rule: as_bool.cases) auto

lemma as_bool_nonbool: "v \<noteq> true \<Longrightarrow> v \<noteq> false \<Longrightarrow> as_bool v = None"
  by (simp add: as_bool_None)

(* Rules with the monadic let of the conclusion evaluated, one per shape of the last result *)
lemma EvalUnOpVal: "\<rho>, e \<Rightarrow>\<^sub>e Val v \<Longrightarrow> \<rho>, ExprUnOp op e \<Rightarrow>\<^sub>e unop_meaning op v"
  using EvalUnOp by fastforce

lemma EvalUnOpAborts: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprUnOp op e \<Rightarrow>\<^sub>e Aborts \<kappa>"
  using EvalUnOp by fastforce

lemma EvalBinOpVal:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, e' \<Rightarrow>\<^sub>e Val v' \<rbrakk> \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e binop_meaning op v v'"
  using EvalBinOp by fastforce

lemma EvalBinOpAborts:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e Aborts \<kappa>"
  using EvalBinOp by fastforce

lemma EvalExprsConsVal:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val vs \<rbrakk> \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s Val (v # vs)"
  using EvalExprsCons by fastforce

lemma EvalExprsConsAborts:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa>"
  using EvalExprsCons by fastforce

lemmas eval_intros =
  eval_expr_eval_exprs_eval_stmt_eval_elif.intros
  EvalUnOpVal EvalUnOpAborts EvalBinOpVal EvalBinOpAborts EvalExprsConsVal EvalExprsConsAborts

theorem soundness:
  shows soundness_expr: "eval_expr n \<rho> e = Done r \<Longrightarrow> \<rho>, e \<Rightarrow>\<^sub>e r"
    and soundness_exprs: "eval_exprs n \<rho> es = Done rs \<Longrightarrow> \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs"
proof (induction n \<rho> e and n \<rho> es arbitrary: r and rs rule: eval_expr_eval_exprs.induct)
qed (auto simp: flet_case as_bool_Some as_bool_None
  split: fuelled.splits result.splits option.splits bool.splits val.splits func.splits if_splits
  intro: eval_intros)

(* Every large enough fuel gives the result of a derivation *)
theorem completeness_eventually:
  shows "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<forall>\<^sub>F n in sequentially. eval_expr n \<rho> e = Done r"
    and "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> \<forall>\<^sub>F n in sequentially. eval_exprs n \<rho> es = Done rs"
    and "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> True"
    and "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<Longrightarrow> True"
proof (induction rule: eval_induct)
  case EvalVar
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalVar in \<open>auto split: val.split\<close>)
next
  case EvalVarUnknown
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalVarUnknown in auto)
next
  case EvalVarUnbound
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalVarUnbound in auto)
next
  case EvalLiteral
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalLiteral in auto)
next
  case EvalLambda
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalLambda in auto)
next
  case EvalUnOp
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalUnOp.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalBinOp
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalBinOp.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalBinOpFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalBinOpFail.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalAndFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndFalse.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalAndTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndTrue.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalAndFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndFail.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalOrTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrTrue.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalOrFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrFalse.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalOrFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrFail.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalCondTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondTrue.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalCondFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondFalse.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalCondFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondFail.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalList
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalList.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalListFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalListFail.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalTuple
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalTuple.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalTupleFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalTupleFail.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalCallFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallFail.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalCallFailArgs
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallFailArgs.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalAndNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndNonBool.IH in \<open>eventually_elim, insert EvalAndNonBool.hyps(2),
        auto simp: flet_case as_bool_nonbool split: val.split\<close>)
next
  case EvalOrNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrNonBool.IH in \<open>eventually_elim, insert EvalOrNonBool.hyps(2),
        auto simp: flet_case as_bool_nonbool split: val.split\<close>)
next
  case EvalCondNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondNonBool.IH in \<open>eventually_elim, insert EvalCondNonBool.hyps(2),
        auto simp: flet_case as_bool_nonbool split: val.split\<close>)
next
  case EvalCallLambda
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallLambda.IH in \<open>eventually_elim, insert EvalCallLambda.hyps(3),
        auto simp: flet_case as_bool_nonbool split: val.split\<close>)
next
  case EvalCallLambdaArity
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallLambdaArity.IH in \<open>eventually_elim, insert EvalCallLambdaArity.hyps(3),
        auto simp: flet_case as_bool_nonbool split: val.split\<close>)
next
  case EvalCallNonFun
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallNonFun.IH in \<open>eventually_elim, insert EvalCallNonFun.hyps(3),
        auto simp: flet_case as_bool_nonbool split: val.split\<close>)
next
  case (EvalCallDef \<rho> e \<rho>' ds j f \<alpha>s xps \<psi> s vs es us \<rho>s o)
  (* Needs statement evaluation, and with it completeness for statements *)
  show ?case sorry
next
  case (EvalCallDefArity \<rho> e \<rho>' ds j f \<alpha>s xps \<psi> s es us)
  (* The evaluator is Stuck at an index beyond ds, where the rule applies to whatever ds ! j is *)
  show ?case sorry
next
  case EvalExprsNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalExprsNil in auto)
next
  case EvalExprsCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalExprsCons.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
next
  case EvalExprsFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalExprsFail.IH in \<open>eventually_elim, auto simp: flet_case mlet_case split: result.split\<close>)
qed simp_all

corollary completeness:
  shows completeness_expr: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<exists>n. eval_expr n \<rho> e = Done r"
    and completeness_exprs: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> \<exists>n. eval_exprs n \<rho> es = Done rs"
  using completeness_eventually(1,2)[THEN eventually_happens'[OF sequentially_bot]] by blast+

end
