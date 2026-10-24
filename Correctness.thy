theory Correctness
    imports Eval
begin

lemma flet_case:
  "flet m f =
    (case m of Done (Val v) \<Rightarrow> f v | Done (Aborts \<kappa>) \<Rightarrow> Done (Aborts \<kappa>) | Stuck \<Rightarrow> Stuck | OutOfFuel \<Rightarrow> OutOfFuel)"
  by (cases "(m, f)" rule: flet.cases) simp_all

lemma mlet_case: "mlet_result r f = (case r of Val v \<Rightarrow> f v | Aborts \<kappa> \<Rightarrow> Aborts \<kappa>)"
  by (cases r) simp_all

lemma flet_outcome_case:
  "flet_outcome m f =
    (case m of Done (Val v) \<Rightarrow> f v | Done (Aborts \<kappa>) \<Rightarrow> Done (Aborts\<^sub>o \<kappa>) | Stuck \<Rightarrow> Stuck | OutOfFuel \<Rightarrow> OutOfFuel)"
  by (cases "(m, f)" rule: flet_outcome.cases) simp_all

lemma mlet_outcome_case: "mlet_outcome r f = (case r of Val v \<Rightarrow> f v | Aborts \<kappa> \<Rightarrow> Aborts\<^sub>o \<kappa>)"
  by (cases r) simp_all

lemma fseq_case:
  "fseq m f =
    (case m of
      Done o \<Rightarrow> (case o of Assigns \<rho>' \<Rightarrow> map_fuelled (\<lambda>o'. Assigns \<rho>' \<otimes>\<^sub>o o') (f \<rho>') | _ \<Rightarrow> Done o)
    | Stuck \<Rightarrow> Stuck
    | OutOfFuel \<Rightarrow> OutOfFuel)"
  by (cases "(m, f)" rule: fseq.cases) simp_all

lemma map_fuelled_Done: "map_fuelled f m = Done r \<longleftrightarrow> (\<exists>x. m = Done x \<and> r = f x)"
  by (cases m) auto

lemmas eval_simps = flet_case flet_outcome_case mlet_case mlet_outcome_case fseq_case

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

lemma EvalSubscriptVal:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, e' \<Rightarrow>\<^sub>e Val v' \<rbrakk> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e getitem v v'"
  using EvalSubscript by fastforce

lemma EvalSubscriptAborts:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e Aborts \<kappa>"
  using EvalSubscript by fastforce

lemma EvalBinOpAborts:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e Aborts \<kappa>"
  using EvalBinOp by fastforce

lemma EvalExprsConsVal:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val vs \<rbrakk> \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s Val (v # vs)"
  using EvalExprsCons by fastforce

lemma EvalExprsConsAborts:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa>"
  using EvalExprsCons by fastforce

lemma EvalAssignVal: "\<rho>, e \<Rightarrow>\<^sub>e Val v \<Longrightarrow> \<rho>, StmtAssign x \<pi> e \<Rightarrow>\<^sub>s Assigns (fmupd x v \<epsilon>)"
  using EvalAssign by fastforce

lemma EvalAssignAborts: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssign x \<pi> e \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>"
  using EvalAssign by fastforce

lemma EvalExprStmtVal: "\<rho>, e \<Rightarrow>\<^sub>e Val v \<Longrightarrow> \<rho>, StmtExpr e \<Rightarrow>\<^sub>s Assigns \<epsilon>"
  using EvalExprStmt by fastforce

lemma EvalExprStmtAborts: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtExpr e \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>"
  using EvalExprStmt by fastforce

lemma EvalReturnVal: "\<rho>, e \<Rightarrow>\<^sub>e Val v \<Longrightarrow> \<rho>, StmtReturn (Some e) \<Rightarrow>\<^sub>s Returns v"
  using EvalReturn by fastforce

lemma EvalReturnAborts: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtReturn (Some e) \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>"
  using EvalReturn by fastforce

lemmas eval_intros =
  eval_expr_eval_exprs_eval_stmt_eval_elif.intros
  EvalUnOpVal EvalUnOpAborts EvalBinOpVal EvalBinOpAborts EvalSubscriptVal EvalSubscriptAborts
  EvalExprsConsVal EvalExprsConsAborts
  EvalAssignVal EvalAssignAborts EvalExprStmtVal EvalExprStmtAborts EvalReturnVal EvalReturnAborts

theorem soundness:
  shows soundness_expr: "eval_expr n \<rho> e = Done r \<Longrightarrow> \<rho>, e \<Rightarrow>\<^sub>e r"
    and soundness_exprs: "eval_exprs n \<rho> es = Done rs \<Longrightarrow> \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs"
    and soundness_stmt: "eval_stmt n \<rho> s = Done o \<Longrightarrow> \<rho>, s \<Rightarrow>\<^sub>s o"
    and soundness_elif: "eval_elif n \<rho> eb = Done o \<Longrightarrow> \<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o"
proof (induction n \<rho> e and n \<rho> es and n \<rho> s and n \<rho> eb arbitrary: r and rs and o and o
    rule: eval_expr_eval_exprs_eval_stmt_eval_elif.induct)
qed (auto simp: eval_simps map_fuelled_Done as_bool_Some as_bool_None
  split: fuelled.splits result.splits outcome.splits option.splits bool.splits val.splits lit.splits
    func.splits if_splits
  intro: eval_intros)

(* Every large enough fuel gives the outcome of a derivation *)
theorem completeness_eventually:
  shows "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<forall>\<^sub>F n in sequentially. eval_expr n \<rho> e = Done r"
    and "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> \<forall>\<^sub>F n in sequentially. eval_exprs n \<rho> es = Done rs"
    and "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<forall>\<^sub>F n in sequentially. eval_stmt n \<rho> s = Done o"
    and "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<Longrightarrow> \<forall>\<^sub>F n in sequentially. eval_elif n \<rho> eb = Done o"
proof (induction rule: eval_induct)
  case EvalVar
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalVar in \<open>auto split: val.split\<close>)
next
  case EvalVarUnknown
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalVarUnknown in \<open>auto split: val.split\<close>)
next
  case EvalVarUnbound
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalVarUnbound in \<open>auto split: val.split\<close>)
next
  case EvalLiteral
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalLiteral in \<open>auto split: val.split\<close>)
next
  case EvalLambda
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalLambda in \<open>auto split: val.split\<close>)
next
  case EvalUnOp
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalUnOp.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalBinOp
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalBinOp.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalBinOpFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalBinOpFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAndFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAndTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAndFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAndNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndNonBool.IH in \<open>eventually_elim, insert EvalAndNonBool.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalOrTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalOrFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalOrFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalOrNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrNonBool.IH in \<open>eventually_elim, insert EvalOrNonBool.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalCondTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalCondFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalCondFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalCondNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondNonBool.IH in \<open>eventually_elim, insert EvalCondNonBool.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalList
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalList.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalListFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalListFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalTuple
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalTuple.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalTupleFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalTupleFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalDict
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDict.IH in \<open>eventually_elim, insert EvalDict.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalDictFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDictFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalDictNonStr
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDictNonStr.IH in \<open>eventually_elim, insert EvalDictNonStr.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalSubscript
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSubscript.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalSubscriptFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSubscriptFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalCallLambda
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallLambda.IH in \<open>eventually_elim, insert EvalCallLambda.hyps(3),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalCallLambdaArity
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallLambdaArity.IH in \<open>eventually_elim, insert EvalCallLambdaArity.hyps(3),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalCallDef
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallDef.IH in \<open>eventually_elim, insert EvalCallDef.hyps(2,3,5,6,8),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalCallDefArity
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallDefArity.IH in \<open>eventually_elim, insert EvalCallDefArity.hyps(2,4,5),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalCallNonFun
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallNonFun.IH in \<open>eventually_elim, insert EvalCallNonFun.hyps(3),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalCallFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalCallFailArgs
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallFailArgs.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalExprsNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalExprsNil in \<open>auto split: val.split\<close>)
next
  case EvalExprsCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalExprsCons.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalExprsFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalExprsFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalPass
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalPass in \<open>auto split: val.split\<close>)
next
  case EvalDeclare
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalDeclare in \<open>auto split: val.split\<close>)
next
  case EvalAssign
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssign.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalExprStmt
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalExprStmt.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalReturn
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalReturn.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalReturnNone
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalReturnNone in \<open>auto split: val.split\<close>)
next
  case EvalDefs
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalDefs in \<open>auto split: val.split\<close>)
next
  case EvalAssert
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssert.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAssertFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAssertFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAssertNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertNonBool.IH in \<open>eventually_elim, insert EvalAssertNonBool.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalAssertMsg
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertMsg.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAssertMsgFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertMsgFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAssertMsgFalseFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertMsgFalseFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAssertMsgFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertMsgFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAssertMsgNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertMsgNonBool.IH in \<open>eventually_elim, insert EvalAssertMsgNonBool.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalAssertMsgNonStr
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertMsgNonStr.IH in \<open>eventually_elim, insert EvalAssertMsgNonStr.hyps(3),
        auto simp: eval_simps as_bool_nonbool split: val.split lit.split\<close>)
next
  case EvalIfTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalIfTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalIfFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalIfFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalIfFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalIfFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalIfNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalIfNonBool.IH in \<open>eventually_elim, insert EvalIfNonBool.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalSeq
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSeq.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalSeqReturn
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSeqReturn.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalSeqFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSeqFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalIfNone
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalIfNone in \<open>auto split: val.split\<close>)
next
  case EvalElse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalElse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalElifTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalElifTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalElifFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalElifFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalElifFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalElifFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalElifNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalElifNonBool.IH in \<open>eventually_elim, insert EvalElifNonBool.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
qed

corollary completeness:
  shows completeness_expr: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<exists>n. eval_expr n \<rho> e = Done r"
    and completeness_exprs: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> \<exists>n. eval_exprs n \<rho> es = Done rs"
    and completeness_stmt: "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<exists>n. eval_stmt n \<rho> s = Done o"
    and completeness_elif: "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<Longrightarrow> \<exists>n. eval_elif n \<rho> eb = Done o"
  using completeness_eventually[THEN eventually_happens'[OF sequentially_bot]] by blast+

end
