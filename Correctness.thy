theory Correctness
    imports Eval
begin

inductive_cases VarE: "\<rho> \<turnstile>\<^sub>e Var x \<Rightarrow> v"
inductive_cases LitE: "\<rho> \<turnstile>\<^sub>e Literal l \<Rightarrow> v"
inductive_cases BinOpE: "\<rho> \<turnstile>\<^sub>e BinOp op e1 e2 \<Rightarrow> v"
inductive_cases UnOpE: "\<rho> \<turnstile>\<^sub>e UnOp op e \<Rightarrow> v"
inductive_cases CondExprE: "\<rho> \<turnstile>\<^sub>e CondExpr e1 e2 e3 \<Rightarrow> v"
inductive_cases ListE: "\<rho> \<turnstile>\<^sub>e List es \<Rightarrow> v"
inductive_cases TupleE: "\<rho> \<turnstile>\<^sub>e Tuple es \<Rightarrow> v"
inductive_cases LambdaE: "\<rho> \<turnstile>\<^sub>e Lambda args e \<Rightarrow> v"
(* inductive_cases CallE: "\<rho> \<turnstile>\<^sub>e Call f args \<Rightarrow> v" *)

inductive_cases
  CallE[consumes 1, case_names CallLam CallDef]:
    "\<rho> \<turnstile>\<^sub>e Call e args \<Rightarrow> v" and
  IfE[consumes 1, case_names IfT IfF]:
    "\<rho> \<turnstile>\<^sub>s If e b elifs else' \<Rightarrow> r" and
  ElifConsE[consumes 1, case_names ElT ElF]:
    "\<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f ((e, b) # elifs', else') \<Rightarrow> r"

lemma list_all2_deterministic:
  assumes
    "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vs1"
    "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vs2"
    "\<And>e v1 v2.
       e \<in> set es \<Longrightarrow>
       \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v1 \<Longrightarrow>
       \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v2 \<Longrightarrow>
       v1 = v2"
  shows
    "vs1 = vs2"
using assms
apply (induction arbitrary: vs2 rule: list_all2_induct)
apply blast
apply (metis list.set_intros(1,2) list_all2_Cons1)
done

lemma list_all2_unique:
  assumes "list_all2 (\<lambda>x y. P x y \<and> (\<forall>z. P x z \<longrightarrow> y = z)) xs ys"
      and "list_all2 P xs zs"
    shows "ys = zs"
using assms
proof (induction xs arbitrary: ys zs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  from Cons.prems(1) obtain y ys' where
    ys: "ys = y # ys'" and
    y_prop: "P x y \<and> (\<forall>z. P x z \<longrightarrow> y = z)" and
    rest1: "list_all2 (\<lambda>x y. P x y \<and> (\<forall>z. P x z \<longrightarrow> y = z)) xs ys'"
    by (auto simp: list_all2_Cons1)
  from Cons.prems(2) obtain z zs' where
    zs: "zs = z # zs'" and
    z_prop: "P x z" and
    rest2: "list_all2 P xs zs'"
    by (auto simp: list_all2_Cons1)
  from y_prop z_prop have "y = z" by blast
  moreover from Cons.IH[OF rest1 rest2] have "ys' = zs'" .
  ultimately show ?case using ys zs by simp
qed

lemmas eval_induct = eval_expr_eval_block_eval_stmt_eval_elif.inducts

lemma determinism:
  shows 
      expr_det:  "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v1 \<Longrightarrow> (\<forall>v2. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v2 \<longrightarrow> v1 = v2)"
  and stmt_det:  "\<rho> \<turnstile>\<^sub>b b \<Rightarrow> rb1 \<Longrightarrow> (\<forall>rb2. \<rho> \<turnstile>\<^sub>b b \<Rightarrow> rb2 \<longrightarrow> rb1 = rb2)"
  and block_det: "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> rs1 \<Longrightarrow> (\<forall>rs2. \<rho> \<turnstile>\<^sub>s s \<Rightarrow> rs2 \<longrightarrow> rs1 = rs2)"
  and elif_det:  "\<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f eb \<Rightarrow> re1 \<Longrightarrow> (\<forall>re2. \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f eb \<Rightarrow> re2 \<longrightarrow> re1 = re2)"
proof (induction rule: eval_induct)
  case (EvalVar \<rho> x v)
  then show ?case by (metis VarE option.inject)
next
  case (EvalLit \<rho> l)
  then show ?case using LitE by blast
next
  case (EvalBinOp \<rho> e1 v1 e2 v2 op v')
  then show ?case by (metis BinOpE option.inject)
next
  case (EvalUnOp \<rho> e v op v')
  then show ?case by (metis UnOpE option.inject)
next
  case (EvalCondExprTrue \<rho> c t v e)
  then show ?case by (metis CondExprE literal.inject(2) val.inject(1))
next
  case (EvalCondExprFalse \<rho> c e v t)
  then show ?case using CondExprE by blast
next
  case (EvalList \<rho> es vals)
  from \<open>\<rho> \<turnstile>\<^sub>e List es \<Rightarrow> v2\<close> obtain vals' where
    v2_eq: "v2 = VList vals'" and
    ev: "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals'"
    by (cases rule: eval_expr.cases) auto

  from list_all2_unique[OF \<open>list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<and> (\<forall>x. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> x \<longrightarrow> v = x)) es vals\<close> ev]
  have "vals = vals'" .
  with v2_eq show ?case sorry
next
  case (EvalTuple \<rho> es vals)
  from \<open>\<rho> \<turnstile>\<^sub>e Tuple es \<Rightarrow> v2\<close> obtain vals' where
    v2_eq: "v2 = VTuple vals'" and
    ev: "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals'"
    by (cases rule: eval_expr.cases) auto
  from list_all2_unique[OF \<open>list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<and> (\<forall>x. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> x \<longrightarrow> v = x)) es vals\<close> ev]
  have "vals = vals'" .
  with v2_eq show ?case by simp
next
  case (EvalCallLambda \<rho> e \<rho>' xs e' args u' v)
  from EvalCallLambda.hyps have
    h1: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>', xs, e'\<rangle>\<^sub>\<lambda>" and
    h1u: "\<forall>z. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> z \<longrightarrow> \<langle>\<rho>', xs, e'\<rangle>\<^sub>\<lambda> = z" and
    h2: "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<and> (\<forall>z. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> z \<longrightarrow> v = z)) args u'" and
    h3: "\<rho>'(xs [\<mapsto>] u') \<turnstile>\<^sub>e e' \<Rightarrow> v" and
    h3u: "\<forall>z. \<rho>'(xs [\<mapsto>] u') \<turnstile>\<^sub>e e' \<Rightarrow> z \<longrightarrow> v = z"
    sorry
  from \<open>\<rho> \<turnstile>\<^sub>e Call e args \<Rightarrow> v2\<close> show ?case
  proof (cases rule: CallE)
    case (CallLam \<rho>2 xs2 e2' u2')
    then show ?thesis sorry
  next
    case (CallDef \<rho>' ds j u' r)
    then show ?thesis sorry
  qed
next
  case (EvalCallDef \<rho> e \<rho>' ds j vs fs xs bs args u' r r')
  then show ?case sorry
next
  case (EvalLambda \<rho> args e)
  then show ?case by (metis local.EvalLambda LambdaE)
next
  case (EvalBlock \<rho> s \<rho>' b r r')
  from EvalBlock.hyps have
    h1: "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Assigns \<rho>'" and
    h2: "(\<rho> \<cdot> \<rho>') \<turnstile>\<^sub>b b \<Rightarrow> r" and
    h3: "Assigns \<rho>' \<bullet> r = Some r'"
    by auto

  from \<open>\<rho> \<turnstile>\<^sub>b (s # b) \<Rightarrow> rb2\<close> obtain \<rho>2' r2'' where
    a1: "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Assigns \<rho>2'" and
    a2: "(\<rho> \<cdot> \<rho>2') \<turnstile>\<^sub>b b \<Rightarrow> r2''" and
    a3: "Assigns \<rho>2' \<bullet> r2'' = Some rb2"
    by (cases rule: eval_block.cases) auto

  have step: "Assigns \<rho>' = Assigns \<rho>2'"
    apply (rule EvalBlock.IH(1))
    apply (rule a1)
    done

  from a2 rho_eq have a2': "(\<rho> \<cdot> \<rho>') \<turnstile>\<^sub>b b \<Rightarrow> r2''" by simp

  have r_eq: "r = r2''"
    using EvalBlock.IH(2)[OF a2'] by simp

  from h3 a3 rho_eq r_eq show ?case by simp
next
  case (EvalPass \<rho>)
  then show ?case by (simp add: eval_stmt.simps)
next
  case (EvalAssign \<rho> e v x)
  from EvalAssign.hyps have 
    h1: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v" and 
    h1u: "\<forall>z. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> z \<longrightarrow> v = z" 
    by auto
  from \<open>\<rho> \<turnstile>\<^sub>s Assign x e \<Rightarrow> r2\<close> obtain v2' where
    req: "r2 = Assigns [x \<mapsto> v2']" and ev: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v2'"
    by (cases rule: eval_stmt.cases) auto
  from h1u ev have "v = v2'" by blast
  with req show ?case by simp
next
  case (EvalExpr \<rho> e v)
  then show ?case by (simp add: eval_stmt.simps)
next
  case (EvalAssert \<rho> e v)
  then show ?case using eval_stmt.cases by blast
next
  case (EvalAssertMsg \<rho> e v e')
  then show ?case using eval_stmt.cases by blast
next
  case (EvalReturnNone \<rho>)
  then show ?case by (simp add: eval_stmt.simps)
next
  case (EvalReturn \<rho> e v)
  then show ?case 
  by (smt (verit, best) eval_stmt.simps stmt.distinct(11,25,37,47,55,61,67,69) stmt.inject(5))
next
  case (EvalIfTrue \<rho> e b r elifs else')
  then show ?case 
  using eval_stmt.simps by blast
next
  case (EvalIfFalse \<rho> e elifs else' r b)
  then show ?case 
  using eval_stmt.simps by blast
next
  case (EvalMutual vs \<rho> ds fs)
  then show ?case sorry
next
  case (EvalElifEmpty \<rho> b r)
  then show ?case
  using eval_elif.simps list.distinct(1) by blast
next
  case (EvalElifTrue \<rho> e b r elifs' else')
  then show ?case 
  using eval_elif.simps by blast
next
  case (EvalElifFalse \<rho> e elifs' else' r b)
  then show ?case
  using eval_elif.simps by blast
qed
end