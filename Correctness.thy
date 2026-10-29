(* Soundness and completeness of the evaluator against the evaluation judgements *)
theory Correctness
    imports Eval
begin

context evaluation
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

lemma class_of_Some: "class_of v = Some C \<longleftrightarrow> v = VClass C"
  by (cases v) auto

lemma class_of_None: "class_of v = None \<longleftrightarrow> \<not> is_class v"
  by (cases v) auto

lemma class_of_nonclass: "\<not> is_class v \<Longrightarrow> class_of v = None"
  by (simp add: class_of_None)

lemma fields_of_Some: "fields_of v = Some xvs \<longleftrightarrow> (\<exists>C. v = VObject C xvs)"
  by (cases v) auto

lemma fields_of_None: "fields_of v = None \<longleftrightarrow> \<not> is_object v"
  by (cases v) auto

lemma fields_of_nonobject: "\<not> is_object v \<Longrightarrow> fields_of v = None"
  by (simp add: fields_of_None)

lemma module_env_of_Some: "module_env_of v = Some \<rho> \<longleftrightarrow> (\<exists>q. v = VModLoaded q \<rho>)"
  by (cases v) auto

lemma module_env_of_None: "module_env_of v = None \<longleftrightarrow> \<not> is_loaded_module v"
  by (cases v) auto

lemma module_env_of_nonmodule: "\<not> is_loaded_module v \<Longrightarrow> module_env_of v = None"
  by (simp add: module_env_of_None)

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
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<not> is_class v ; \<rho>, e' \<Rightarrow>\<^sub>e Val v' \<rbrakk> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e getitem v v'"
  using EvalSubscript by fastforce

lemma EvalSubscriptAborts:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<not> is_class v ; \<rho>, e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e Aborts \<kappa>"
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

lemma EvalGenConsVal:
  "\<lbrakk> fmupd x u \<rho>, gs \<Rightarrow>\<^sub>q Val \<rho>s ; \<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Val \<rho>ss \<rbrakk> \<Longrightarrow> \<rho>, x, u # us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Val (\<rho>s @ \<rho>ss)"
  using EvalGenCons by fastforce

lemma EvalGenConsAborts:
  "\<lbrakk> fmupd x u \<rho>, gs \<Rightarrow>\<^sub>q Val \<rho>s ; \<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, x, u # us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Aborts \<kappa>"
  using EvalGenCons by fastforce

lemma EvalCompConsVal:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Val vs \<rbrakk> \<Longrightarrow> \<rho> # \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Val (v # vs)"
  using EvalCompCons by fastforce

lemma EvalCompConsAborts:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho> # \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Aborts \<kappa>"
  using EvalCompCons by fastforce

lemma EvalEntriesConsVal:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val (VLit (LitString w)) ; \<rho>, e' \<Rightarrow>\<^sub>e Val v ; \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Val \<delta> \<rbrakk>
  \<Longrightarrow> \<rho> # \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Val ((w, v) # \<delta>)"
  using EvalEntriesCons by fastforce

lemma EvalEntriesConsAborts:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val (VLit (LitString w)) ; \<rho>, e' \<Rightarrow>\<^sub>e Val v ; \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> \<rho> # \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Aborts \<kappa>"
  using EvalEntriesCons by fastforce

lemmas eval_intros =
  eval_rules
  EvalUnOpVal EvalUnOpAborts EvalBinOpVal EvalBinOpAborts EvalSubscriptVal EvalSubscriptAborts
  EvalExprsConsVal EvalExprsConsAborts
  EvalAssignVal EvalAssignAborts EvalExprStmtVal EvalExprStmtAborts EvalReturnVal EvalReturnAborts
  EvalGenConsVal EvalGenConsAborts EvalCompConsVal EvalCompConsAborts EvalEntriesConsVal EvalEntriesConsAborts

theorem soundness:
  shows soundness_expr: "run_expr n \<rho> e = Done r \<Longrightarrow> \<rho>, e \<Rightarrow>\<^sub>e r"
    and soundness_exprs: "run_exprs n \<rho> es = Done rs \<Longrightarrow> \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs"
    and soundness_stmt: "run_stmt n \<rho> s = Done o \<Longrightarrow> \<rho>, s \<Rightarrow>\<^sub>s o"
    and soundness_elif: "run_elif n \<rho> eb = Done o \<Longrightarrow> \<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o"
    and soundness_quals: "run_quals n \<rho> gs = Done q \<Longrightarrow> \<rho>, gs \<Rightarrow>\<^sub>q q"
    and soundness_gen: "run_gen n \<rho> x us gs = Done q \<Longrightarrow> \<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q"
    and soundness_comp: "run_comp n \<rho>s e = Done vr \<Longrightarrow> \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr"
    and soundness_entries: "run_entries n \<rho>s e e' = Done dr \<Longrightarrow> \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr"
proof (induction n \<rho> e and n \<rho> es and n \<rho> s and n \<rho> eb and n \<rho> gs and n \<rho> x us gs and n \<rho>s e
    and n \<rho>s e e' arbitrary: r and rs and o and o and q and q and vr and dr rule: eval_fun_induct)
qed (auto simp: eval_simps map_fuelled_Done as_bool_Some as_bool_None class_of_Some class_of_None fields_of_Some fields_of_None
  module_env_of_Some module_env_of_None
  split: fuelled.splits result.splits outcome.splits option.splits bool.splits val.splits lit.splits if_splits
  intro: eval_intros,
  (fastforce intro: eval_intros simp: map_fuelled_Done split: func.splits if_splits option.splits)+)

(* Every large enough fuel gives the outcome of a derivation *)
theorem completeness_eventually:
  shows "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_expr n \<rho> e = Done r"
    and "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_exprs n \<rho> es = Done rs"
    and "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_stmt n \<rho> s = Done o"
    and "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_elif n \<rho> eb = Done o"
    and "\<rho>, gs \<Rightarrow>\<^sub>q q \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_quals n \<rho> gs = Done q"
    and "\<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_gen n \<rho> x us gs = Done q"
    and "\<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_comp n \<rho>s e = Done vr"
    and "\<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_entries n \<rho>s e e' = Done dr"
proof (induction rule: eval_expr_eval_exprs_eval_stmt_eval_elif_eval_quals_eval_gen_eval_comp_eval_entries.inducts[ih_names])
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
      (use EvalSubscript.IH in \<open>eventually_elim, insert EvalSubscript.hyps(2),
        auto simp: eval_simps class_of_nonclass split: result.split\<close>)
next
  case EvalClassTypeArgs
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalClassTypeArgs.IH in \<open>eventually_elim, insert EvalClassTypeArgs.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalSubscriptFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSubscriptFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalAttrObject
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAttrObject.IH in \<open>eventually_elim, insert EvalAttrObject.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalAttrMissing
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAttrMissing.IH in \<open>eventually_elim, insert EvalAttrMissing.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalAttrModule
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAttrModule.IH in \<open>eventually_elim, insert EvalAttrModule.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalAttrModuleMissing
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAttrModuleMissing.IH in \<open>eventually_elim, insert EvalAttrModuleMissing.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalAttrNonObject
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAttrNonObject.IH in \<open>eventually_elim, insert EvalAttrNonObject.hyps(2,3),
        auto simp: eval_simps fields_of_nonobject module_env_of_nonmodule\<close>)
next
  case EvalAttrFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAttrFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
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
  case EvalCallPrim
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallPrim.IH in \<open>eventually_elim, auto simp: eval_simps\<close>)
next
  case EvalCallNonFun
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallNonFun.IH in \<open>eventually_elim, insert EvalCallNonFun.hyps(3,4,5),
        auto simp: eval_simps as_bool_nonbool class_of_nonclass split: val.split\<close>)
next
  case EvalCallFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalCallFailArgs
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCallFailArgs.IH in \<open>eventually_elim, auto simp: eval_simps class_of_Some split: result.split option.split\<close>)
next
  case EvalConstr
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalConstr.IH in \<open>eventually_elim, insert EvalConstr.hyps(1,3), auto simp: eval_simps\<close>)
next
  case EvalConstrArity
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalConstrArity.IH in \<open>eventually_elim, insert EvalConstrArity.hyps(1,3), auto simp: eval_simps\<close>)
next
  case EvalConstrFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalConstrFail.IH in \<open>eventually_elim, insert EvalConstrFail.hyps(1), auto simp: eval_simps\<close>)
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
  case EvalMatch
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalMatch.IH in \<open>eventually_elim, insert EvalMatch.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalMatchFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalMatchFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalMatchAbort
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalMatchAbort.IH in \<open>eventually_elim, insert EvalMatchAbort.hyps(2), auto simp: eval_simps\<close>)
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
next
  case EvalListComp
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalListComp.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalListCompFailQuals
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalListCompFailQuals.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalListCompFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalListCompFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalDictComp
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDictComp.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalDictCompFailQuals
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDictCompFailQuals.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalDictCompFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDictCompFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalQualsNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalQualsNil in \<open>auto split: val.split\<close>)
next
  case EvalQualGuardTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGuardTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalQualGuardFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGuardFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalQualGuardFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGuardFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalQualGuardNonBool
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGuardNonBool.IH in \<open>eventually_elim, insert EvalQualGuardNonBool.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalQualGenerator
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGenerator.IH in \<open>eventually_elim, insert EvalQualGenerator.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalQualGeneratorFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGeneratorFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalQualGeneratorNonSeq
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGeneratorNonSeq.IH in \<open>eventually_elim, insert EvalQualGeneratorNonSeq.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split\<close>)
next
  case EvalGenNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalGenNil in \<open>auto split: val.split\<close>)
next
  case EvalGenCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalGenCons.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalGenFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalGenFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalCompNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalCompNil in \<open>auto split: val.split\<close>)
next
  case EvalCompCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCompCons.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalCompFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCompFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalEntriesNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalEntriesNil in \<open>auto split: val.split\<close>)
next
  case EvalEntriesCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalEntriesCons.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalEntriesFailKey
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalEntriesFailKey.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
next
  case EvalEntriesNonStr
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalEntriesNonStr.IH in \<open>eventually_elim, insert EvalEntriesNonStr.hyps(2),
        auto simp: eval_simps as_bool_nonbool split: val.split lit.split\<close>)
next
  case EvalEntriesFailValue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalEntriesFailValue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split outcome.split\<close>)
qed

corollary completeness:
  shows completeness_expr: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<exists>n. run_expr n \<rho> e = Done r"
    and completeness_exprs: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> \<exists>n. run_exprs n \<rho> es = Done rs"
    and completeness_stmt: "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<exists>n. run_stmt n \<rho> s = Done o"
    and completeness_elif: "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<Longrightarrow> \<exists>n. run_elif n \<rho> eb = Done o"
    and completeness_quals: "\<rho>, gs \<Rightarrow>\<^sub>q q \<Longrightarrow> \<exists>n. run_quals n \<rho> gs = Done q"
    and completeness_gen: "\<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q \<Longrightarrow> \<exists>n. run_gen n \<rho> x us gs = Done q"
    and completeness_comp: "\<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr \<Longrightarrow> \<exists>n. run_comp n \<rho>s e = Done vr"
    and completeness_entries: "\<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr \<Longrightarrow> \<exists>n. run_entries n \<rho>s e e' = Done dr"
  by (fact completeness_eventually[THEN eventually_happens'[OF sequentially_bot]])+


theorem soundness_top: "run_top n q \<rho> t = Done o \<Longrightarrow> q, \<rho>, t \<Rightarrow>\<^sub>t o"
proof (induction t arbitrary: \<rho> o)
  case (Stmt s)
  then show ?case by (auto intro: EvalTopStmt soundness_stmt)
next
  case (TopSeq t t')
  then show ?case
    by (auto simp: map_fuelled_Done intro: eval_top.intros split: fuelled.splits outcome.splits)
qed (auto intro: EvalTypes)

theorem completeness_top_eventually: "q, \<rho>, t \<Rightarrow>\<^sub>t o \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_top n q \<rho> t = Done o"
proof (induction rule: eval_top.induct[ih_names])
  case EvalTopStmt
  then show ?case by (simp add: completeness_eventually(3))
next
  case EvalTopSeq
  from EvalTopSeq.IH show ?case by eventually_elim simp
next
  case EvalTopSeqFail
  from EvalTopSeqFail.IH show ?case by eventually_elim simp
qed simp

corollary completeness_top: "q, \<rho>, t \<Rightarrow>\<^sub>t o \<Longrightarrow> \<exists>n. run_top n q \<rho> t = Done o"
  by (fact completeness_top_eventually[THEN eventually_happens'[OF sequentially_bot]])

end

context loading
begin

(* The rules whose results are composed by mlet, at a value and at an abort *)
lemma EvalImportVal:
  "\<lbrakk> (x, []) \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> ; (x, []), \<rho>, xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Val \<rho>'' ; q, \<iota>s \<Rightarrow>\<^sub>i Val \<rho>' \<rbrakk>
  \<Longrightarrow> q, Import (x, xs) # \<iota>s \<Rightarrow>\<^sub>i Val (fmupd x (VModLoaded (x, []) \<rho>'') \<epsilon> \<uplus>\<^sub>v \<rho>')"
  using EvalImport by fastforce

lemma EvalImportAborts:
  "\<lbrakk> (x, []) \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> ; (x, []), \<rho>, xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Val \<rho>'' ; q, \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> q, Import (x, xs) # \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa>"
  using EvalImport by fastforce

lemma EvalFromImportVal:
  "\<lbrakk> unique_to q' q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s Val () ; q' \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> ; \<rho>, xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Val vs ; q, \<iota>s \<Rightarrow>\<^sub>i Val \<rho>'' \<rbrakk>
  \<Longrightarrow> q, FromImport q' xs # \<iota>s \<Rightarrow>\<^sub>i Val (fmap_of_list (zip xs vs) \<uplus>\<^sub>v \<rho>'')"
  using EvalFromImport by fastforce

lemma EvalFromImportAborts:
  "\<lbrakk> unique_to q' q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s Val () ; q' \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> ; \<rho>, xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Val vs ; q, \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> q, FromImport q' xs # \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa>"
  using EvalFromImport by fastforce

lemma EvalSubmodulesConsVal:
  "\<lbrakk> snoc q x \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho>' ; snoc q x, \<rho>', xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Val \<rho>'' \<rbrakk>
  \<Longrightarrow> q, \<rho>, x # xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Val (\<rho> \<uplus>\<^sub>v fmupd x (VModLoaded (snoc q x) \<rho>'') \<epsilon>)"
  using EvalSubmodulesCons by fastforce

lemma EvalSubmodulesConsAborts:
  "\<lbrakk> snoc q x \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho>' ; snoc q x, \<rho>', xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Aborts \<kappa> \<rbrakk> \<Longrightarrow> q, \<rho>, x # xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Aborts \<kappa>"
  using EvalSubmodulesCons by fastforce

lemma EvalImpsConsVal:
  "\<lbrakk> \<rho>, x \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p Val v ; \<rho>, xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Val vs \<rbrakk> \<Longrightarrow> \<rho>, x # xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Val (v # vs)"
  using EvalImpsCons by fastforce

lemma EvalImpsConsAborts:
  "\<lbrakk> \<rho>, x \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p Val v ; \<rho>, xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, x # xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Aborts \<kappa>"
  using EvalImpsCons by fastforce

lemmas loading_intros =
  eval_mod_eval_imports_eval_sub_eval_imp_eval_imps_eval_mods.intros
  EvalImportVal EvalImportAborts EvalFromImportVal EvalFromImportAborts
  EvalSubmodulesConsVal EvalSubmodulesConsAborts EvalImpsConsVal EvalImpsConsAborts

(* Soundness of the evaluator *)
theorem loading_soundness:
  shows "run_mod n q = Done r \<Longrightarrow> q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d r"
    and "run_imports n q \<iota>s = Done r \<Longrightarrow> q, \<iota>s \<Rightarrow>\<^sub>i r"
    and "run_sub n q \<rho> xs = Done r \<Longrightarrow> q, \<rho>, xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b r"
    and "run_imp n \<rho> x = Done vr \<Longrightarrow> \<rho>, x \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p vr"
    and "run_imps n \<rho> xs = Done vsr \<Longrightarrow> \<rho>, xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s vsr"
    and "run_mods n qs = Done ur \<Longrightarrow> qs \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s ur"
proof (induction n q and n q \<iota>s and n q \<rho> xs and n \<rho> x and n \<rho> xs and n qs
    arbitrary: r and r and r and vr and vsr and ur rule: run_loading_induct)
  case (2 n q)
  then show ?case
    by (auto simp: flet_case intro: loading_intros soundness_top
      split: option.splits module_body.splits fuelled.splits result.splits outcome.splits)
qed (auto intro: loading_intros simp: flet_case stub_of_Some stub_of_None split: option.splits fuelled.splits result.splits,
  (fastforce intro: loading_intros)+)

theorem program_soundness: "run_program n = Done \<kappa> \<Longrightarrow> eval_program \<kappa>"
  by (auto simp: run_program_def intro: eval_program.intros loading_soundness(1)
    split: fuelled.splits result.splits)

(* Completeness of loading, given that no module of the program is predefined *)
context
  assumes disjoint: "fmdom M |\<inter>| fmdom predefined_env = {||}"
begin

lemma flet_Done_mlet: "flet (Done r) (\<lambda>v. Done (f v)) = Done (mlet r f)"
  by (cases r) simp_all

theorem loading_completeness_eventually:
  shows "q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d r \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_mod n q = Done r"
    and "q, \<iota>s \<Rightarrow>\<^sub>i r \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_imports n q \<iota>s = Done r"
    and "q, \<rho>, xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b r \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_sub n q \<rho> xs = Done r"
    and "\<rho>, x \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p vr \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_imp n \<rho> x = Done vr"
    and "\<rho>, xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s vsr \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_imps n \<rho> xs = Done vsr"
    and "qs \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s ur \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_mods n qs = Done ur"
proof (induction rule: eval_mod_eval_imports_eval_sub_eval_imp_eval_imps_eval_mods.inducts[ih_names])
  case EvalPredefined
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (simp add: EvalPredefined.hyps)
next
  case EvalModule
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalModule.IH completeness_top_eventually[OF EvalModule.hyps(4)] in \<open>eventually_elim,
        simp add: EvalModule.hyps(1,3) module_not_predefined[OF disjoint]\<close>)
next
  case EvalModuleFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalModuleFail.IH in \<open>eventually_elim, simp add: EvalModuleFail.hyps flet_Done_mlet module_not_predefined[OF disjoint]\<close>)
next
  case EvalModuleFailBody
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalModuleFailBody.IH completeness_top_eventually[OF EvalModuleFailBody.hyps(4)] in \<open>eventually_elim,
        simp add: EvalModuleFailBody.hyps(1,3) module_not_predefined[OF disjoint]\<close>)
next
  case EvalImportsNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) simp
next
  case EvalImport
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalImport.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalImportFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalImportFail.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalImportFailChain
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalImportFailChain.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalFromImport
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalFromImport.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalFromImportFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalFromImportFail.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalFromImportFailContaining
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalFromImportFailContaining.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalFromImportFailMember
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalFromImportFailMember.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalSubmodulesNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) simp
next
  case EvalSubmodulesCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSubmodulesCons.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalSubmodulesFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSubmodulesFail.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalImpMember
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (simp add: EvalImpMember.hyps(1) stub_of_None[THEN iffD2, OF EvalImpMember.hyps(2)])
next
  case EvalImpSubmodule
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalImpSubmodule.IH in \<open>eventually_elim, simp add: EvalImpSubmodule.hyps flet_Done_mlet\<close>)
next
  case EvalImpSubmoduleFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalImpSubmoduleFail.IH in \<open>eventually_elim, simp add: EvalImpSubmoduleFail.hyps flet_Done_mlet\<close>)
next
  case EvalImpsNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) simp
next
  case EvalImpsCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalImpsCons.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalImpsFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalImpsFail.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalModsNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) simp
next
  case EvalModsCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalModsCons.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
next
  case EvalModsFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalModsFail.IH in \<open>eventually_elim, simp add: flet_Done_mlet\<close>)
qed

theorem program_completeness: "eval_program \<kappa> \<Longrightarrow> \<exists>n. run_program n = Done \<kappa>"
proof (induction rule: eval_program.induct)
  case (EvalProgram \<rho>)
  then obtain n where "run_mod n main = Done (Val \<rho>)"
    using loading_completeness_eventually(1)[THEN eventually_happens'[OF sequentially_bot]] by blast
  then show ?case by (intro exI[of _ n]) (simp add: run_program_def)
next
  case (EvalProgramAbort \<kappa>)
  then obtain n where "run_mod n main = Done (Aborts \<kappa>)"
    using loading_completeness_eventually(1)[THEN eventually_happens'[OF sequentially_bot]] by blast
  then show ?case by (intro exI[of _ n]) (simp add: run_program_def)
qed

end

end

end
