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
    (case m of Done (Val v) \<Rightarrow> f v | Done (Aborts \<kappa>) \<Rightarrow> Done (aborts\<^sub>o \<kappa>) | Stuck \<Rightarrow> Stuck | OutOfFuel \<Rightarrow> OutOfFuel)"
  by (cases "(m, f)" rule: flet_outcome.cases) simp_all

lemma mlet_outcome_case: "mlet_outcome r f = (case r of Val v \<Rightarrow> f v | Aborts \<kappa> \<Rightarrow> aborts\<^sub>o \<kappa>)"
  by (cases r) simp_all

lemma fseq_case:
  "fseq m f =
    (case m of
      Done (us, \<omega>) \<Rightarrow>
        (case \<omega> of Assigns \<rho>' \<Rightarrow> map_fuelled (\<lambda>o'. (us, Assigns \<rho>') \<otimes> o') (f \<rho>') | _ \<Rightarrow> Done (us, \<omega>))
    | Stuck \<Rightarrow> Stuck
    | OutOfFuel \<Rightarrow> OutOfFuel)"
  by (cases "(m, f)" rule: fseq.cases) simp_all

lemma map_fuelled_Done: "map_fuelled f m = Done r \<longleftrightarrow> (\<exists>x. m = Done x \<and> r = f x)"
  by (cases m) auto

lemma body_result_Done: "body_result m = Done r \<longleftrightarrow> (\<exists>\<omega>. m = Done ([], \<omega>) \<and> r = result_of \<omega>)"
  by (cases m rule: body_result.cases) auto

lemma fbind_Done: "fbind m f = Done r \<longleftrightarrow> (\<exists>x. m = Done x \<and> f x = Done r)"
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
lemma EvalUnOpVal: "\<rho>, node e \<Rightarrow>\<^sub>e Val v \<Longrightarrow> \<rho>, ExprUnOp op e \<Rightarrow>\<^sub>e unop_meaning op v"
  using EvalUnOp by fastforce

lemma EvalUnOpAborts: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprUnOp op e \<Rightarrow>\<^sub>e Aborts \<kappa>"
  using EvalUnOp by fastforce

lemma EvalBinOpVal:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>, node e' \<Rightarrow>\<^sub>e Val v' \<rbrakk> \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e binop_meaning op v v'"
  using EvalBinOp by fastforce

lemma EvalSubscriptVal:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<not> is_class v ; \<rho>, node e' \<Rightarrow>\<^sub>e Val v' \<rbrakk> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e getitem v v'"
  using EvalSubscript by fastforce

lemma EvalSubscriptAborts:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<not> is_class v ; \<rho>, node e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e Aborts \<kappa>"
  using EvalSubscript by fastforce

lemma EvalBinOpAborts:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>, node e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e Aborts \<kappa>"
  using EvalBinOp by fastforce

lemma EvalExprsConsVal:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val vs \<rbrakk> \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s Val (v # vs)"
  using EvalExprsCons by fastforce

lemma EvalExprsConsAborts:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa>"
  using EvalExprsCons by fastforce

lemma EvalAssignVal: "\<rho>, node e \<Rightarrow>\<^sub>e Val v \<Longrightarrow> \<rho>, StmtAssign x \<pi> e \<Rightarrow>\<^sub>s assigns\<^sub>o (fmupd x v \<epsilon>)"
  using EvalAssign by fastforce

lemma EvalAssignAborts: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssign x \<pi> e \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>"
  using EvalAssign by fastforce

lemma EvalExprStmtVal: "\<rho>, node e \<Rightarrow>\<^sub>e Val v \<Longrightarrow> \<rho>, StmtExpr e \<Rightarrow>\<^sub>s assigns\<^sub>o \<epsilon>"
  using EvalExprStmt by fastforce

lemma EvalExprStmtAborts: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtExpr e \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>"
  using EvalExprStmt by fastforce

lemma EvalPrintVal: "\<rho>, node e \<Rightarrow>\<^sub>e Val v \<Longrightarrow> \<rho>, StmtPrint e \<Rightarrow>\<^sub>s ([v], Assigns \<epsilon>)"
  using EvalPrint by fastforce

lemma EvalPrintAborts: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtPrint e \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>"
  using EvalPrint by fastforce

lemma EvalReturnVal: "\<rho>, node e \<Rightarrow>\<^sub>e Val v \<Longrightarrow> \<rho>, StmtReturn (Some e) \<Rightarrow>\<^sub>s returns\<^sub>o v"
  using EvalReturn by fastforce

lemma EvalReturnAborts: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtReturn (Some e) \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>"
  using EvalReturn by fastforce

lemma EvalGenConsVal:
  "\<lbrakk> fmupd x u \<rho>, gs \<Rightarrow>\<^sub>q Val \<rho>s ; \<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Val \<rho>ss \<rbrakk> \<Longrightarrow> \<rho>, x, u # us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Val (\<rho>s @ \<rho>ss)"
  using EvalGenCons by fastforce

lemma EvalGenConsAborts:
  "\<lbrakk> fmupd x u \<rho>, gs \<Rightarrow>\<^sub>q Val \<rho>s ; \<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, x, u # us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Aborts \<kappa>"
  using EvalGenCons by fastforce

lemma EvalCompConsVal:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Val vs \<rbrakk> \<Longrightarrow> \<rho> # \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Val (v # vs)"
  using EvalCompCons by fastforce

lemma EvalCompConsAborts:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho> # \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Aborts \<kappa>"
  using EvalCompCons by fastforce

lemma EvalEntriesConsVal:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VLit (LitString w)) ; \<rho>, node e' \<Rightarrow>\<^sub>e Val v ; \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Val \<delta> \<rbrakk>
  \<Longrightarrow> \<rho> # \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Val ((w, v) # \<delta>)"
  using EvalEntriesCons by fastforce

lemma EvalEntriesConsAborts:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VLit (LitString w)) ; \<rho>, node e' \<Rightarrow>\<^sub>e Val v ; \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> \<rho> # \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Aborts \<kappa>"
  using EvalEntriesCons by fastforce

lemmas eval_intros =
  eval_rules
  EvalUnOpVal EvalUnOpAborts EvalBinOpVal EvalBinOpAborts EvalSubscriptVal EvalSubscriptAborts
  EvalExprsConsVal EvalExprsConsAborts
  EvalAssignVal EvalAssignAborts EvalExprStmtVal EvalExprStmtAborts EvalPrintVal EvalPrintAborts
  EvalReturnVal EvalReturnAborts
  EvalGenConsVal EvalGenConsAborts EvalCompConsVal EvalCompConsAborts EvalEntriesConsVal EvalEntriesConsAborts

theorem soundness:
  shows soundness_expr: "run_expr n \<rho> e = Done r \<Longrightarrow> \<rho>, e \<Rightarrow>\<^sub>e r"
    and soundness_exprs: "run_exprs n \<rho> es = Done rs \<Longrightarrow> \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs"
    and soundness_stmt: "run_stmt n \<rho> s = Done o \<Longrightarrow> \<rho>, s \<Rightarrow>\<^sub>s o"
    and soundness_elif: "run_elif n \<rho> eb = Done o \<Longrightarrow> \<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o"
    and soundness_quals: "run_quals n \<rho> gs = Done q \<Longrightarrow> \<rho>, gs \<Rightarrow>\<^sub>q q"
    and soundness_gen: "run_gen n \<rho> x us gs = Done q \<Longrightarrow> \<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q"
    and soundness_comp: "run_comp n \<rho>s ec = Done vr \<Longrightarrow> \<rho>s, ec \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr"
    and soundness_entries: "run_entries n \<rho>s ec ec' = Done dr \<Longrightarrow> \<rho>s, ec, ec' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr"
proof (induction n \<rho> e and n \<rho> es and n \<rho> s and n \<rho> eb and n \<rho> gs and n \<rho> x us gs and n \<rho>s ec
    and n \<rho>s ec ec' arbitrary: r and rs and o and o and q and q and vr and dr rule: eval_fun_induct)
qed (auto simp: eval_simps map_fuelled_Done body_result_Done as_bool_Some as_bool_None class_of_Some class_of_None
  fields_of_Some fields_of_None module_env_of_Some module_env_of_None
  split: fuelled.splits result.splits completion.splits option.splits bool.splits val.splits lit.splits if_splits
  intro: eval_intros,
  (fastforce intro: eval_intros simp: map_fuelled_Done body_result_Done split: func.splits if_splits option.splits)+)

(* Every large enough fuel gives the outcome of a derivation *)
theorem completeness_eventually:
  shows "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_expr n \<rho> e = Done r"
    and "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_exprs n \<rho> es = Done rs"
    and "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_stmt n \<rho> s = Done o"
    and "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_elif n \<rho> eb = Done o"
    and "\<rho>, gs \<Rightarrow>\<^sub>q q \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_quals n \<rho> gs = Done q"
    and "\<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_gen n \<rho> x us gs = Done q"
    and "\<rho>s, ec \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_comp n \<rho>s ec = Done vr"
    and "\<rho>s, ec, ec' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_entries n \<rho>s ec ec' = Done dr"
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
      (use EvalUnOp.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalBinOp
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalBinOp.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalBinOpFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalBinOpFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalAndFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalAndTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalAndFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAndFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalOrTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalOrFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalOrFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalOrFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalCondTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalCondFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalCondFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCondFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalList.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalListFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalListFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalTuple
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalTuple.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalTupleFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalTupleFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalDict
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDict.IH in \<open>eventually_elim, insert EvalDict.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalDictFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDictFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalSubscriptFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalAttrObject
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAttrObject.IH in \<open>eventually_elim, insert EvalAttrObject.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalAttrObjectMissing
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAttrObjectMissing.IH in \<open>eventually_elim, insert EvalAttrObjectMissing.hyps(2), auto simp: eval_simps\<close>)
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
      (use EvalAttrFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalCallFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalExprsCons.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalExprsFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalExprsFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalAssign.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalExprStmt
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalExprStmt.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalPrint
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalPrint.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalReturn
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalReturn.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalAssert.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalAssertFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalAssertFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalAssertMsg.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalAssertMsgFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertMsgFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalAssertMsgFalseFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertMsgFalseFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalAssertMsgFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalAssertMsgFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalIfTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalIfFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalIfFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalIfFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalIfFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalMatchFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalMatchAbort
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalMatchAbort.IH in \<open>eventually_elim, insert EvalMatchAbort.hyps(2), auto simp: eval_simps\<close>)
next
  case EvalSeq
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSeq.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalSeqReturn
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSeqReturn.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalSeqFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalSeqFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalIfNone
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalIfNone in \<open>auto split: val.split\<close>)
next
  case EvalElse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalElse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalElifTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalElifTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalElifFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalElifFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalElifFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalElifFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalListComp.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalListCompFailQuals
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalListCompFailQuals.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalListCompFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalListCompFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalDictComp
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDictComp.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalDictCompFailQuals
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDictCompFailQuals.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalDictCompFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalDictCompFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalQualsNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalQualsNil in \<open>auto split: val.split\<close>)
next
  case EvalQualGuardTrue
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGuardTrue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalQualGuardFalse
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGuardFalse.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalQualGuardFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalQualGuardFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalQualGeneratorFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalGenCons.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalGenFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalGenFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalCompNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalCompNil in \<open>auto split: val.split\<close>)
next
  case EvalCompCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCompCons.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalCompFail
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalCompFail.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalEntriesNil
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (use EvalEntriesNil in \<open>auto split: val.split\<close>)
next
  case EvalEntriesCons
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalEntriesCons.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
next
  case EvalEntriesFailKey
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1])
      (use EvalEntriesFailKey.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
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
      (use EvalEntriesFailValue.IH in \<open>eventually_elim, auto simp: eval_simps split: result.split completion.split\<close>)
qed

corollary completeness:
  shows completeness_expr: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<exists>n. run_expr n \<rho> e = Done r"
    and completeness_exprs: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> \<exists>n. run_exprs n \<rho> es = Done rs"
    and completeness_stmt: "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<exists>n. run_stmt n \<rho> s = Done o"
    and completeness_elif: "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<Longrightarrow> \<exists>n. run_elif n \<rho> eb = Done o"
    and completeness_quals: "\<rho>, gs \<Rightarrow>\<^sub>q q \<Longrightarrow> \<exists>n. run_quals n \<rho> gs = Done q"
    and completeness_gen: "\<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q \<Longrightarrow> \<exists>n. run_gen n \<rho> x us gs = Done q"
    and completeness_comp: "\<rho>s, ec \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr \<Longrightarrow> \<exists>n. run_comp n \<rho>s ec = Done vr"
    and completeness_entries: "\<rho>s, ec, ec' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr \<Longrightarrow> \<exists>n. run_entries n \<rho>s ec ec' = Done dr"
  by (fact completeness_eventually[THEN eventually_happens'[OF sequentially_bot]])+


theorem soundness_top: "run_top n q \<rho> t = Done o \<Longrightarrow> q, \<rho>, t \<Rightarrow>\<^sub>t o"
proof (induction t arbitrary: \<rho> o)
  case (Stmt s)
  then show ?case by (auto intro: EvalTopStmt soundness_stmt)
next
  case (TopSeq t t')
  obtain us \<omega> where t: "run_top n q \<rho> t = Done (us, \<omega>)"
    using TopSeq.prems by (cases "run_top n q \<rho> t") auto
  then have "q, \<rho>, t \<Rightarrow>\<^sub>t (us, \<omega>)" by (rule TopSeq.IH(1))
  show ?case
  proof (cases \<omega>)
    case (Assigns \<rho>')
    with TopSeq.prems t obtain o' where "run_top n q (\<rho> \<otimes> \<rho>') t' = Done o'" "o = (us, Assigns \<rho>') \<otimes> o'"
      by (auto simp: map_fuelled_Done)
    moreover from this(1) have "q, \<rho> \<otimes> \<rho>', t' \<Rightarrow>\<^sub>t o'" by (cases o') (auto intro: TopSeq.IH(2))
    ultimately show ?thesis using \<open>q, \<rho>, t \<Rightarrow>\<^sub>t (us, \<omega>)\<close> Assigns by (auto intro: EvalTopSeq)
  next
    case (Aborts\<^sub>\<omega> \<kappa>)
    with TopSeq.prems t \<open>q, \<rho>, t \<Rightarrow>\<^sub>t (us, \<omega>)\<close> show ?thesis by (auto intro: EvalTopSeqFail)
  qed (use TopSeq.prems t in simp)
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

abbreviation loads_dom :: "name list \<Rightarrow> name list \<Rightarrow> bool"
where "loads_dom qs qs' \<equiv> loads_submod_loads_imports_loads_import_loads_dom (Inl (Inl (qs, qs')))"

lemmas loads_psimps = loads.psimps submod_loads.psimps imports_loads.psimps import_loads.psimps
lemmas loads_domintros = loads_submod_loads_imports_loads_import_loads.domintros

(* An evaluation of the order of loading terminates, with the order computed by loads *)
theorem loads_soundness:
  shows "run_loads n qs qs' = Done r \<Longrightarrow> loads_dom qs qs' \<and> loads qs qs' = r"
    and "run_submod_loads n qs q xs = Done r \<Longrightarrow>
      loads_submod_loads_imports_loads_import_loads_dom (Inl (Inr (qs, q, xs))) \<and> submod_loads qs q xs = r"
    and "run_imports_loads n qs q \<iota>s = Done r \<Longrightarrow>
      loads_submod_loads_imports_loads_import_loads_dom (Inr (Inl (qs, q, \<iota>s))) \<and> imports_loads qs q \<iota>s = r"
    and "run_import_loads n qs q \<iota> = Done r \<Longrightarrow>
      loads_submod_loads_imports_loads_import_loads_dom (Inr (Inr (qs, q, \<iota>))) \<and> import_loads qs q \<iota> = r"
proof (induction n qs qs' and n qs q xs and n qs q \<iota>s and n qs q \<iota> arbitrary: r and r and r and r
    rule: run_loads_induct)
  case (3 n qs q qs' r)
  show ?case
  proof (cases "q \<in> set qs \<or> q |\<in>| fmdom \<P>")
    case True
    with "3.prems" have "run_loads n qs qs' = Done r" by simp
    with "3.IH"(1) True have IH: "loads_dom qs qs' \<and> loads qs qs' = r" by blast
    then have d: "loads_dom qs (q # qs')" using True by (auto intro: loads_domintros)
    with IH True show ?thesis by (simp add: loads.psimps(2)[OF d])
  next
    case False
    obtain \<iota>s t where body: "the (fmlookup \<M> q) = ModuleBody \<iota>s t" by (cases "the (fmlookup \<M> q)")
    from "3.prems" False body obtain x where a: "run_imports_loads n qs q \<iota>s = Done x"
      and b: "run_loads n (x @ [q]) qs' = Done r"
      by (auto simp: fbind_Done)
    note A = "3.IH"(2)[OF False body a] and B = "3.IH"(3)[OF False body a b]
    have d: "loads_dom qs (q # qs')" using A B False body by (auto intro: loads_domintros)
    with A B False body show ?thesis by (simp add: loads.psimps(2)[OF d])
  qed
next
  case (6 n qs q x xs r)
  show ?case
  proof (cases "Qualified q x |\<in>| fmdom \<M> \<and> x \<notin> set (declares (the (fmlookup \<M> q)))")
    case True
    from "6.prems" True obtain y where a: "run_loads n qs [Qualified q x] = Done y"
      and b: "run_submod_loads n y q xs = Done r"
      by (auto simp: fbind_Done)
    note A = "6.IH"(1)[OF True a] and B = "6.IH"(2)[OF True a b]
    have d: "loads_submod_loads_imports_loads_import_loads_dom (Inl (Inr (qs, q, x # xs)))"
      using A B True by (auto intro: loads_domintros)
    with A B True show ?thesis by (simp add: submod_loads.psimps(2)[OF d])
  next
    case False
    with "6.prems" have b: "run_submod_loads n qs q xs = Done r" by auto
    note B = "6.IH"(3)[OF False b]
    have d: "loads_submod_loads_imports_loads_import_loads_dom (Inl (Inr (qs, q, x # xs)))"
      using B False by (auto intro: loads_domintros)
    with B False show ?thesis by (auto simp: submod_loads.psimps(2)[OF d])
  qed
next
  case (9 n qs q \<iota> \<iota>s r)
  from "9.prems" obtain y where a: "run_import_loads n qs q (node \<iota>) = Done y"
    and b: "run_imports_loads n y q \<iota>s = Done r"
    by (auto simp: fbind_Done)
  note A = "9.IH"(1)[OF a] and B = "9.IH"(2)[OF a b]
  have d: "loads_submod_loads_imports_loads_import_loads_dom (Inr (Inl (qs, q, \<iota> # \<iota>s)))"
    using A B by (auto intro: loads_domintros)
  with A B show ?case by (simp add: imports_loads.psimps(2)[OF d])
next
  case (11 n qs q q' r)
  from "11.prems" have a: "run_loads n qs (proper_prefixes q' @ [q']) = Done r" by simp
  note A = "11.IH"[OF a]
  have d: "loads_submod_loads_imports_loads_import_loads_dom (Inr (Inr (qs, q, Import q')))"
    using A by (auto intro: loads_domintros)
  with A show ?case by (simp add: import_loads.psimps(1)[OF d])
next
  case (12 n qs q q' xs r)
  from "12.prems" obtain y where a: "run_loads n qs (unique_to q' q @ [q']) = Done y"
    and b: "run_submod_loads n y q' xs = Done r"
    by (auto simp: fbind_Done)
  note A = "12.IH"(1)[OF a] and B = "12.IH"(2)[OF a b]
  have d: "loads_submod_loads_imports_loads_import_loads_dom (Inr (Inr (qs, q, FromImport q' xs)))"
    using A B by (auto intro: loads_domintros)
  with A B show ?case by (simp add: import_loads.psimps(2)[OF d])
qed (auto intro: loads_domintros simp: loads_psimps loads_domintros)

theorem loads_completeness_eventually:
  shows "loads_dom qs qs' \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_loads n qs qs' = Done (loads qs qs')"
    and "loads_submod_loads_imports_loads_import_loads_dom (Inl (Inr (qs, q, xs))) \<Longrightarrow>
      \<forall>\<^sub>F n in sequentially. run_submod_loads n qs q xs = Done (submod_loads qs q xs)"
    and "loads_submod_loads_imports_loads_import_loads_dom (Inr (Inl (qs, q, \<iota>s))) \<Longrightarrow>
      \<forall>\<^sub>F n in sequentially. run_imports_loads n qs q \<iota>s = Done (imports_loads qs q \<iota>s)"
    and "loads_submod_loads_imports_loads_import_loads_dom (Inr (Inr (qs, q, \<iota>))) \<Longrightarrow>
      \<forall>\<^sub>F n in sequentially. run_import_loads n qs q \<iota> = Done (import_loads qs q \<iota>)"
proof (induction qs qs' and qs q xs and qs q \<iota>s and qs q \<iota>
    rule: loads_submod_loads_imports_loads_import_loads.pinduct)
  case (1 qs)
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (simp add: 1 loads_psimps)
next
  case (2 qs q qs')
  show ?case
  proof (cases "q \<in> set qs \<or> q |\<in>| fmdom \<P>")
    case True
    from 2 True have "\<forall>\<^sub>F n in sequentially. run_loads n qs qs' = Done (loads qs qs')" by blast
    then have "\<forall>\<^sub>F n in sequentially. run_loads (Suc n) qs (q # qs') = Done (loads qs (q # qs'))"
      by eventually_elim (simp add: 2(1) True loads_psimps)
    then show ?thesis by (rule eventually_sequentially_Suc[THEN iffD1])
  next
    case False
    obtain \<iota>s t where body: "the (fmlookup \<M> q) = ModuleBody \<iota>s t" by (cases "the (fmlookup \<M> q)")
    from 2 False body have
      "\<forall>\<^sub>F n in sequentially. run_imports_loads n qs q \<iota>s = Done (imports_loads qs q \<iota>s)"
      "\<forall>\<^sub>F n in sequentially.
         run_loads n (imports_loads qs q \<iota>s @ [q]) qs' = Done (loads (imports_loads qs q \<iota>s @ [q]) qs')"
      by (blast dest: sym)+
    then have "\<forall>\<^sub>F n in sequentially. run_loads (Suc n) qs (q # qs') = Done (loads qs (q # qs'))"
      by eventually_elim (simp add: 2(1) False body loads_psimps)
    then show ?thesis by (rule eventually_sequentially_Suc[THEN iffD1])
  qed
next
  case (3 qs q)
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (simp add: 3 loads_psimps)
next
  case (4 qs q x xs)
  show ?case
  proof (cases "Qualified q x |\<in>| fmdom \<M> \<and> x \<notin> set (declares (the (fmlookup \<M> q)))")
    case True
    from 4 True have
      "\<forall>\<^sub>F n in sequentially. run_loads n qs [Qualified q x] = Done (loads qs [Qualified q x])"
      "\<forall>\<^sub>F n in sequentially.
         run_submod_loads n (loads qs [Qualified q x]) q xs = Done (submod_loads (loads qs [Qualified q x]) q xs)"
      by blast+
    then have "\<forall>\<^sub>F n in sequentially. run_submod_loads (Suc n) qs q (x # xs) = Done (submod_loads qs q (x # xs))"
      by eventually_elim (simp add: 4(1) True loads_psimps)
    then show ?thesis by (rule eventually_sequentially_Suc[THEN iffD1])
  next
    case False
    from 4 False have "\<forall>\<^sub>F n in sequentially. run_submod_loads n qs q xs = Done (submod_loads qs q xs)"
      by blast
    then have "\<forall>\<^sub>F n in sequentially. run_submod_loads (Suc n) qs q (x # xs) = Done (submod_loads qs q (x # xs))"
      by eventually_elim (use False in \<open>auto simp: 4(1) loads_psimps\<close>)
    then show ?thesis by (rule eventually_sequentially_Suc[THEN iffD1])
  qed
next
  case (5 qs q)
  show ?case
    by (rule eventually_sequentially_Suc[THEN iffD1]) (simp add: 5 loads_psimps)
next
  case (6 qs q \<iota> \<iota>s)
  from 6 have
    "\<forall>\<^sub>F n in sequentially. run_import_loads n qs q (node \<iota>) = Done (import_loads qs q (node \<iota>))"
    "\<forall>\<^sub>F n in sequentially.
       run_imports_loads n (import_loads qs q (node \<iota>)) q \<iota>s = Done (imports_loads (import_loads qs q (node \<iota>)) q \<iota>s)"
    by blast+
  then have "\<forall>\<^sub>F n in sequentially. run_imports_loads (Suc n) qs q (\<iota> # \<iota>s) = Done (imports_loads qs q (\<iota> # \<iota>s))"
    by eventually_elim (simp add: 6(1) loads_psimps)
  then show ?case by (rule eventually_sequentially_Suc[THEN iffD1])
next
  case (7 qs q q')
  from 7 have "\<forall>\<^sub>F n in sequentially.
    run_loads n qs (proper_prefixes q' @ [q']) = Done (loads qs (proper_prefixes q' @ [q']))"
    by blast
  then have "\<forall>\<^sub>F n in sequentially. run_import_loads (Suc n) qs q (Import q') = Done (import_loads qs q (Import q'))"
    by eventually_elim (simp add: 7(1) loads_psimps)
  then show ?case by (rule eventually_sequentially_Suc[THEN iffD1])
next
  case (8 qs q q' xs)
  from 8 have
    "\<forall>\<^sub>F n in sequentially. run_loads n qs (unique_to q' q @ [q']) = Done (loads qs (unique_to q' q @ [q']))"
    "\<forall>\<^sub>F n in sequentially. run_submod_loads n (loads qs (unique_to q' q @ [q'])) q' xs =
       Done (submod_loads (loads qs (unique_to q' q @ [q'])) q' xs)"
    by blast+
  then have "\<forall>\<^sub>F n in sequentially.
    run_import_loads (Suc n) qs q (FromImport q' xs) = Done (import_loads qs q (FromImport q' xs))"
    by eventually_elim (simp add: 8(1) loads_psimps)
  then show ?case by (rule eventually_sequentially_Suc[THEN iffD1])
qed

theorem mod_soundness: "run_mod n q \<L> = Done o \<Longrightarrow> q, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d o"
  by (auto simp: run_mod_def intro: EvalModule soundness_top split: option.splits module_body.splits)

theorem mod_completeness_eventually: "q, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d o \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_mod n q \<L> = Done o"
proof (induction rule: eval_mod.induct)
  case EvalModule
  from completeness_top_eventually[OF EvalModule(3)] show ?case
    by eventually_elim (simp add: run_mod_def EvalModule(1,2))
qed

theorem mods_soundness: "run_mods n qs \<L> = Done o \<Longrightarrow> qs, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s o"
proof (induction qs arbitrary: \<L> o)
  case Nil
  then show ?case by (auto intro: EvalModsNil)
next
  case (Cons q qs)
  then show ?case
    by (auto simp: map_fuelled_Done intro: eval_mods.intros mod_soundness
      split: fuelled.splits completion.splits prod.splits)
qed

theorem mods_completeness_eventually:
  "qs, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s o \<Longrightarrow> \<forall>\<^sub>F n in sequentially. run_mods n qs \<L> = Done o"
proof (induction rule: eval_mods.induct)
  case EvalModsCons
  from mod_completeness_eventually[OF EvalModsCons(1)] EvalModsCons(3) show ?case
    by eventually_elim simp
next
  case EvalModsFail
  from mod_completeness_eventually[OF EvalModsFail] show ?case
    by eventually_elim simp
qed simp

theorem program_soundness:
  assumes "run_program n \<A> = Done (vs, \<kappa>)"
  shows "eval_program \<A> vs \<kappa>"
proof -
  obtain qs where l: "run_loads n [] [main] = Done qs"
    and m: "(case run_mods n qs (\<E> \<A>) of
               Done (vs, Assigns \<rho>) \<Rightarrow> Done (vs, SystemExit 0)
             | Done (vs, Aborts\<^sub>\<omega> \<kappa>) \<Rightarrow> Done (vs, \<kappa>)
             | Done (vs, Returns v) \<Rightarrow> Stuck
             | Stuck \<Rightarrow> Stuck
             | OutOfFuel \<Rightarrow> OutOfFuel) = Done (vs, \<kappa>)"
    using assms by (auto simp: run_program_def fbind_Done)
  have q: "loads [] [main] = qs" using loads_soundness(1)[OF l] by simp
  obtain us \<omega> where r: "run_mods n qs (\<E> \<A>) = Done (us, \<omega>)"
    using m by (cases "run_mods n qs (\<E> \<A>)") auto
  then have d: "loads [] [main], \<E> \<A> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s (us, \<omega>)" unfolding q by (rule mods_soundness)
  show ?thesis
    using m r d by (cases \<omega>) (auto intro: EvalProgram EvalProgramAbort)
qed

(* Completeness, given that loading terminates *)
theorem program_completeness:
  assumes "eval_program \<A> vs \<kappa>" and "loads_dom [] [main]"
  shows "\<exists>n. run_program n \<A> = Done (vs, \<kappa>)"
  using assms(1)
proof (cases rule: eval_program.cases)
  case (EvalProgram \<rho>)
  then have "\<forall>\<^sub>F n in sequentially. run_mods n (loads [] [main]) (\<E> \<A>) = Done (vs, Assigns \<rho>)"
    by (blast intro: mods_completeness_eventually)
  with loads_completeness_eventually(1)[OF assms(2)]
  have "\<forall>\<^sub>F n in sequentially. run_program n \<A> = Done (vs, \<kappa>)"
    by eventually_elim (use EvalProgram in \<open>simp add: run_program_def\<close>)
  then show ?thesis by (fact eventually_happens'[OF sequentially_bot])
next
  case EvalProgramAbort
  then have "\<forall>\<^sub>F n in sequentially. run_mods n (loads [] [main]) (\<E> \<A>) = Done (vs, Aborts\<^sub>\<omega> \<kappa>)"
    by (blast intro: mods_completeness_eventually)
  with loads_completeness_eventually(1)[OF assms(2)]
  have "\<forall>\<^sub>F n in sequentially. run_program n \<A> = Done (vs, \<kappa>)"
    by eventually_elim (simp add: run_program_def)
  then show ?thesis by (fact eventually_happens'[OF sequentially_bot])
qed

end

end
