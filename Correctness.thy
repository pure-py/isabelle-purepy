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
  from EvalList.IH have
    h1: "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<and> (\<forall>vres. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> vres \<longrightarrow> v = vres)) es vals"
    by auto
  show ?case
  proof (intro allI impI)
    fix vres
    assume "\<rho> \<turnstile>\<^sub>e List es \<Rightarrow> vres"
    then obtain vals' where
      veq: "vres = VList vals'" and
      ev: "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals'"
      by (cases rule: eval_expr.cases) auto
    from list_all2_unique[OF h1 ev] have "vals = vals'" .
    with veq show "VList vals = vres" by simp
  qed
next
  case (EvalTuple \<rho> es vals)
  from EvalTuple.IH have h1: 
    "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<and> (\<forall>vres. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> vres \<longrightarrow> v = vres)) es vals"
    by auto
  show ?case
  proof (intro allI impI)
    fix vres
    assume "\<rho> \<turnstile>\<^sub>e Tuple es \<Rightarrow> vres"
    then obtain vals' where
      veq: "vres = VTuple vals'" and
      ev: "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) es vals'"
      by (cases rule: eval_expr.cases) auto
    from list_all2_unique[OF h1 ev] have "vals = vals'" .
    with veq show "VTuple vals = vres" by simp
  qed
next
  case (EvalCallLambda \<rho> e \<rho>' xs e' args u' v)
  from EvalCallLambda.hyps have
    h1: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>', xs, e'\<rangle>\<^sub>\<lambda>" and
    h3: "\<rho>'(xs [\<mapsto>] u') \<turnstile>\<^sub>e e' \<Rightarrow> v"
    by auto
  from EvalCallLambda.IH have
    ih1: "\<forall>vres. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> vres \<longrightarrow> \<langle>\<rho>',xs,e'\<rangle>\<^sub>\<lambda> = vres" and
    h2: "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<and> (\<forall>vres. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> vres \<longrightarrow> v = vres)) args u'" and
    ih3: "\<forall>vres. \<rho>'(xs [\<mapsto>] u') \<turnstile>\<^sub>e e' \<Rightarrow> vres \<longrightarrow> v = vres"
    by auto
  show ?case
  proof (intro allI impI)
    fix vres
    assume "\<rho> \<turnstile>\<^sub>e Call e args \<Rightarrow> vres"
    then consider
        (Lam) \<rho>2' xs2 e2' u2' where
          "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>2',xs2,e2'\<rangle>\<^sub>\<lambda>"
          "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) args u2'"
          "\<rho>2'(xs2 [\<mapsto>] u2') \<turnstile>\<^sub>e e2' \<Rightarrow> vres"
      | (Def) \<rho>3' ds3 j3 vs3 fs3 xs3 bs3 u3' r3 where
          "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>3',ds3,j3\<rangle>\<^sub>C"
          "vs3 = map (VDefClosure \<rho>3' ds3) [0..<length ds3]"
          "fs3 = map (\<lambda>d. case d of DefFunc f _ _ \<Rightarrow> f) ds3"
          "xs3 = map (\<lambda>d. case d of DefFunc _ x _ \<Rightarrow> x) ds3"
          "bs3 = map (\<lambda>d. case d of DefFunc _ _ b \<Rightarrow> b) ds3"
          "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) args u3'"
          "\<rho>3'(fs3 [\<mapsto>] vs3, xs3 ! j3 [\<mapsto>] u3') \<turnstile>\<^sub>b bs3 ! j3 \<Rightarrow> r3"
          "unwrap r3 = Some vres"
      by (cases rule: eval_expr.cases) auto
    then show "v = vres"
    proof cases
      case Lam
      from ih1 Lam(1) have "\<langle>\<rho>',xs,e'\<rangle>\<^sub>\<lambda> = \<langle>\<rho>2',xs2,e2'\<rangle>\<^sub>\<lambda>" by blast
      hence eqs: "\<rho>' = \<rho>2'" "xs = xs2" "e' = e2'" by auto
      moreover from list_all2_unique[OF h2 Lam(2)] have "u' = u2'" .
      ultimately have "\<rho>'(xs [\<mapsto>] u') \<turnstile>\<^sub>e e' \<Rightarrow> vres" using Lam(3) by simp
      with ih3 show ?thesis by blast
    next
      case Def
      from ih1 Def(1) have "\<langle>\<rho>',xs,e'\<rangle>\<^sub>\<lambda> = \<langle>\<rho>3',ds3,j3\<rangle>\<^sub>C" by blast
      then show ?thesis by simp
    qed
  qed
next
  case (EvalCallDef \<rho> e \<rho>' ds j vs fs xs bs args u' r r')
  from EvalCallDef.hyps have
    h1: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>',ds,j\<rangle>\<^sub>C" and
    hvs: "vs = map (VDefClosure \<rho>' ds) [0..<length ds]" and
    hfs: "fs = map (\<lambda>d. case d of DefFunc f _ _ \<Rightarrow> f) ds" and
    hxs: "xs = map (\<lambda>d. case d of DefFunc _ x _ \<Rightarrow> x) ds" and
    hbs: "bs = map (\<lambda>d. case d of DefFunc _ _ b \<Rightarrow> b) ds" and
    h3: "\<rho>'(fs [\<mapsto>] vs, xs ! j [\<mapsto>] u') \<turnstile>\<^sub>b bs ! j \<Rightarrow> r" and
    h4: "unwrap r = Some r'"
    by auto
  from EvalCallDef.IH have
    ih1: "\<forall>vres. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> vres \<longrightarrow> \<langle>\<rho>',ds,j\<rangle>\<^sub>C = vres" and
    h2: "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v \<and> (\<forall>vres. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> vres \<longrightarrow> v = vres)) args u'" and
    ih3: "\<forall>rres. \<rho>'(fs [\<mapsto>] vs, xs ! j [\<mapsto>] u') \<turnstile>\<^sub>b bs ! j \<Rightarrow> rres \<longrightarrow> r = rres"
    by auto
  show ?case
  proof (intro allI impI)
    fix vres
    assume "\<rho> \<turnstile>\<^sub>e Call e args \<Rightarrow> vres"
    then consider
        (Lam) \<rho>2' xs2 e2' u2' where
          "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>2',xs2,e2'\<rangle>\<^sub>\<lambda>"
          "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) args u2'"
          "\<rho>2'(xs2 [\<mapsto>] u2') \<turnstile>\<^sub>e e2' \<Rightarrow> vres"
      | (Def) \<rho>3' ds3 j3 vs3 fs3 xs3 bs3 u3' r3 where
          "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> \<langle>\<rho>3',ds3,j3\<rangle>\<^sub>C"
          "vs3 = map (VDefClosure \<rho>3' ds3) [0..<length ds3]"
          "fs3 = map (\<lambda>d. case d of DefFunc f _ _ \<Rightarrow> f) ds3"
          "xs3 = map (\<lambda>d. case d of DefFunc _ x _ \<Rightarrow> x) ds3"
          "bs3 = map (\<lambda>d. case d of DefFunc _ _ b \<Rightarrow> b) ds3"
          "list_all2 (\<lambda>e v. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v) args u3'"
          "\<rho>3'(fs3 [\<mapsto>] vs3, xs3 ! j3 [\<mapsto>] u3') \<turnstile>\<^sub>b bs3 ! j3 \<Rightarrow> r3"
          "unwrap r3 = Some vres"
      by (cases rule: eval_expr.cases) auto
    then show "r' = vres"
    proof cases
      case Lam
      from ih1 Lam(1) have "\<langle>\<rho>',ds,j\<rangle>\<^sub>C = \<langle>\<rho>2',xs2,e2'\<rangle>\<^sub>\<lambda>" by blast
      then show ?thesis by simp
    next
      case Def
      from ih1 Def(1) have "\<langle>\<rho>',ds,j\<rangle>\<^sub>C = \<langle>\<rho>3',ds3,j3\<rangle>\<^sub>C" by blast
      hence eqs: "\<rho>' = \<rho>3'" "ds = ds3" "j = j3" by auto
      from list_all2_unique[OF h2 Def(6)] have equ: "u' = u3'" .
      have vs_eq: "vs3 = vs" using Def(2) hvs eqs by simp
      moreover have fs_eq: "fs3 = fs" using Def(3) hfs eqs by simp
      moreover have xs_eq: "xs3 = xs" using Def(4) hxs eqs by simp
      moreover have bs_eq: "bs3 = bs" using Def(5) hbs eqs by simp
      ultimately have "\<rho>'(fs [\<mapsto>] vs, xs ! j [\<mapsto>] u') \<turnstile>\<^sub>b bs ! j \<Rightarrow> r3"
        using Def(7) eqs equ by simp
      with ih3 have "r = r3" by blast
      with h4 Def(8) show ?thesis by simp
    qed
  qed
next
  case (EvalLambda \<rho> args e)
  then show ?case by (metis local.EvalLambda LambdaE)
next
  case (EvalBlockAssigns \<rho> s \<rho>' b r r')
  from EvalBlockAssigns.hyps have
    h1: "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Assigns \<rho>'" and
    h2: "(\<rho> \<cdot> \<rho>') \<turnstile>\<^sub>b b \<Rightarrow> r" and
    h3: "Assigns \<rho>' \<bullet> r = Some r'"
    by auto
  from EvalBlockAssigns.IH have
    ih1: "\<forall>rres. \<rho> \<turnstile>\<^sub>s s \<Rightarrow> rres \<longrightarrow> Assigns \<rho>' = rres" and
    ih2: "\<forall>rres. (\<rho> \<cdot> \<rho>') \<turnstile>\<^sub>b b \<Rightarrow> rres \<longrightarrow> r = rres"
    by auto
  show ?case
  proof (intro allI impI)
    fix rres
    assume "\<rho> \<turnstile>\<^sub>b (s # b) \<Rightarrow> rres"
    then consider
        (Asn) \<rho>2' r2'' where
          "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Assigns \<rho>2'"
          "(\<rho> \<cdot> \<rho>2') \<turnstile>\<^sub>b b \<Rightarrow> r2''"
          "Assigns \<rho>2' \<bullet> r2'' = Some rres"
      | (Ret) v2 where
          "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Returns v2"
          "rres = Returns v2"
      by (cases rule: eval_block.cases) auto
    then show "r' = rres"
    proof cases
      case Asn
      from ih1 Asn(1) have rho_eq: "\<rho>' = \<rho>2'" by blast
      from Asn(2) rho_eq have a2': "(\<rho> \<cdot> \<rho>') \<turnstile>\<^sub>b b \<Rightarrow> r2''" by simp
      from ih2 a2' have r_eq: "r = r2''" by blast
      from h3 Asn(3) rho_eq r_eq show ?thesis by simp
    next
      case Ret
      from ih1 Ret(1) have "Assigns \<rho>' = Returns v2" by blast
      then show ?thesis by simp
    qed
  qed
next
  case (EvalBlockReturns \<rho> s v b)
  from EvalBlockReturns.hyps have h1: "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Returns v" by auto
  from EvalBlockReturns.IH have ih1: "\<forall>rres. \<rho> \<turnstile>\<^sub>s s \<Rightarrow> rres \<longrightarrow> Returns v = rres" by auto
  show ?case
  proof (intro allI impI)
    fix rres
    assume "\<rho> \<turnstile>\<^sub>b (s # b) \<Rightarrow> rres"
    then consider
        (Asn) \<rho>2' r2'' where
          "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Assigns \<rho>2'"
          "(\<rho> \<cdot> \<rho>2') \<turnstile>\<^sub>b b \<Rightarrow> r2''"
          "Assigns \<rho>2' \<bullet> r2'' = Some rres"
      | (Ret) v2 where
          "\<rho> \<turnstile>\<^sub>s s \<Rightarrow> Returns v2"
          "rres = Returns v2"
      by (cases rule: eval_block.cases) auto
    then show "Returns v = rres"
    proof cases
      case Asn
      from ih1 Asn(1) have "Returns v = Assigns \<rho>2'" by blast
      then show ?thesis by simp
    next
      case Ret
      from ih1 Ret(1) have "Returns v = Returns v2" by blast
      with Ret(2) show ?thesis by simp
    qed
  qed
next
  case (EvalPass \<rho>)
  then show ?case by (simp add: eval_stmt.simps)
next
  case (EvalAssign \<rho> e v x)
  from EvalAssign.hyps have h1: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v" by auto
  from EvalAssign.IH have ih1: "\<forall>vres. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> vres \<longrightarrow> v = vres" by auto
  show ?case
  proof (intro allI impI)
    fix rres
    assume "\<rho> \<turnstile>\<^sub>s Assign x e \<Rightarrow> rres"
    then obtain v2' where
      req: "rres = Assigns [x \<mapsto> v2']" and ev: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v2'"
      by (cases rule: eval_stmt.cases) auto
    from ih1 ev have "v = v2'" by blast
    with req show "Assigns [x \<mapsto> v] = rres" by simp
  qed
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
  from EvalReturn.hyps have h1: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v" by auto
  from EvalReturn.IH have ih1: "\<forall>vres. \<rho> \<turnstile>\<^sub>e e \<Rightarrow> vres \<longrightarrow> v = vres" by auto
  show ?case
  proof (intro allI impI)
    fix rres
    assume "\<rho> \<turnstile>\<^sub>s Return e \<Rightarrow> rres"
    then obtain v2' where
      req: "rres = Returns v2'" and ev: "\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v2'"
      by (cases rule: eval_stmt.cases) auto
    from ih1 ev have "v = v2'" by blast
    with req show "Returns v = rres" by simp
  qed
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
  show ?case
  proof (intro allI impI)
    fix rres
    assume "\<rho> \<turnstile>\<^sub>s MutualRegion ds \<Rightarrow> rres"
    then show "Assigns (\<epsilon>(fs [\<mapsto>] vs)) = rres"
      using EvalMutual.hyps by (cases rule: eval_stmt.cases) auto
  qed
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

lemma expr_determinism: "\<lbrakk>\<rho> \<turnstile>\<^sub>e e \<Rightarrow> v1; \<rho> \<turnstile>\<^sub>e e \<Rightarrow> v2\<rbrakk> \<Longrightarrow> v1 = v2"
  using determinism(1) by blast

lemma stmt_determinism: "\<lbrakk>\<rho> \<turnstile>\<^sub>b b \<Rightarrow> r1; \<rho> \<turnstile>\<^sub>b b \<Rightarrow> r2\<rbrakk> \<Longrightarrow> r1 = r2"
  using determinism(2) by blast

lemma block_determinism: "\<lbrakk>\<rho> \<turnstile>\<^sub>s s \<Rightarrow> r1; \<rho> \<turnstile>\<^sub>s s \<Rightarrow> r2\<rbrakk> \<Longrightarrow> r1 = r2"
  using determinism(3) by blast

lemma elif_determinism: "\<lbrakk>\<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f eb \<Rightarrow> r1; \<rho> \<turnstile>\<^sub>e\<^sub>l\<^sub>i\<^sub>f eb \<Rightarrow> r2\<rbrakk> \<Longrightarrow> r1 = r2"
  using determinism(4) by blast


end