(* Inversion lemmas and determinism of evaluation *)
theory Determinism
    imports Eval
begin

context evaluation
begin

inductive_cases VarE: "\<rho>, ExprVar x \<Rightarrow>\<^sub>e r"
inductive_cases LiteralE: "\<rho>, ExprLiteral l \<Rightarrow>\<^sub>e r"
inductive_cases LambdaE: "\<rho>, ExprLambda xs e \<Rightarrow>\<^sub>e r"
inductive_cases UnOpE: "\<rho>, ExprUnOp op e \<Rightarrow>\<^sub>e r"
inductive_cases BinOpE: "\<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e r"
inductive_cases AndE: "\<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e r"
inductive_cases OrE: "\<rho>, ExprOr e e' \<Rightarrow>\<^sub>e r"
inductive_cases CondE: "\<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e r"
inductive_cases ListE: "\<rho>, ExprList es \<Rightarrow>\<^sub>e r"
inductive_cases TupleE: "\<rho>, ExprTuple es \<Rightarrow>\<^sub>e r"
inductive_cases DictE: "\<rho>, ExprDict kes \<Rightarrow>\<^sub>e r"
inductive_cases SubscriptE: "\<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e r"
inductive_cases
  CallE[consumes 1, case_names CallLambda CallLambdaArity CallDef CallDefArity CallNonFun CallFail CallFailArgs
    CallConstr CallConstrFail]:
  "\<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e r"
inductive_cases CallKwE: "\<rho>, ExprCall e (es, kws) \<Rightarrow>\<^sub>e r"
inductive_cases ExprsNilE: "\<rho>, [] \<Rightarrow>\<^sub>e\<^sub>s rs"
inductive_cases ExprsConsE: "\<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s rs"
inductive_cases PassE: "\<rho>, StmtPass \<Rightarrow>\<^sub>s o"
inductive_cases DeclareE: "\<rho>, StmtDeclare x \<psi> \<Rightarrow>\<^sub>s o"
inductive_cases AssignE: "\<rho>, StmtAssign x \<pi> e \<Rightarrow>\<^sub>s o"
inductive_cases ExprStmtE: "\<rho>, StmtExpr e \<Rightarrow>\<^sub>s o"
inductive_cases ReturnE: "\<rho>, StmtReturn e \<Rightarrow>\<^sub>s o"
inductive_cases DefsE: "\<rho>, StmtMutualRegion ds \<Rightarrow>\<^sub>s o"
inductive_cases AssertE: "\<rho>, StmtAssert e e' \<Rightarrow>\<^sub>s o"
inductive_cases IfE: "\<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s o"
inductive_cases SeqE: "\<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s o"
inductive_cases MatchE: "\<rho>, StmtMatch e cases \<Rightarrow>\<^sub>s o"
inductive_cases ElifNilE: "\<rho>, ([], else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o"
inductive_cases ElifConsE: "\<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o"
inductive_cases ListCompE: "\<rho>, ExprListComp e gs \<Rightarrow>\<^sub>e r"
inductive_cases DictCompE: "\<rho>, ExprDictComp e e' gs \<Rightarrow>\<^sub>e r"
inductive_cases QualsNilE: "\<rho>, [] \<Rightarrow>\<^sub>q r"
inductive_cases QualGuardE: "\<rho>, Guard e # gs \<Rightarrow>\<^sub>q r"
inductive_cases QualGeneratorE: "\<rho>, Generator x e # gs \<Rightarrow>\<^sub>q r"
inductive_cases GenNilE: "\<rho>, x, [], gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n r"
inductive_cases GenConsE: "\<rho>, x, u # us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n r"
inductive_cases CompNilE: "[], e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p r"
inductive_cases CompConsE: "\<rho> # \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p r"
inductive_cases EntriesNilE: "[], e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s r"
inductive_cases EntriesConsE: "\<rho> # \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s r"

lemma determinism:
  shows
      expr_det: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, e \<Rightarrow>\<^sub>e r' \<Longrightarrow> r = r'"
  and exprs_det: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs' \<Longrightarrow> rs = rs'"
  and stmt_det: "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<rho>, s \<Rightarrow>\<^sub>s o' \<Longrightarrow> o = o'"
  and elif_det: "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o' \<Longrightarrow> \<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o'' \<Longrightarrow> o' = o''"
  and quals_det: "\<rho>, gs \<Rightarrow>\<^sub>q q \<Longrightarrow> \<rho>, gs \<Rightarrow>\<^sub>q q' \<Longrightarrow> q = q'"
  and gen_det: "\<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q \<Longrightarrow> \<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q' \<Longrightarrow> q = q'"
  and comp_det: "\<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr \<Longrightarrow> \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr' \<Longrightarrow> vr = vr'"
  and entries_det: "\<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr \<Longrightarrow> \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr' \<Longrightarrow> dr = dr'"
proof (induction arbitrary: r' and rs' and o' and o'' and q' and q' and vr' and dr' rule: eval_expr_eval_exprs_eval_stmt_eval_elif_eval_quals_eval_gen_eval_comp_eval_entries.inducts[ih_names])
  case EvalVar
  then show ?case by (auto elim!: VarE)
next
  case EvalVarUnknown
  then show ?case by (auto elim!: VarE)
next
  case EvalVarUnbound
  then show ?case by (auto elim!: VarE)
next
  case EvalLiteral
  then show ?case by (auto elim!: LiteralE)
next
  case EvalLambda
  then show ?case by (auto elim!: LambdaE)
next
  case EvalUnOp
  from EvalUnOp.prems EvalUnOp.hyps show ?case
    by (auto elim!: UnOpE dest: EvalUnOp.IH)
next
  case EvalBinOp
  from EvalBinOp.prems EvalBinOp.hyps show ?case
    by (auto elim!: BinOpE dest: EvalBinOp.IH)
next
  case EvalBinOpFail
  from EvalBinOpFail.prems EvalBinOpFail.hyps show ?case
    by (auto elim!: BinOpE dest: EvalBinOpFail.IH)
next
  case EvalAndFalse
  from EvalAndFalse.prems EvalAndFalse.hyps show ?case
    by (auto elim!: AndE dest: EvalAndFalse.IH)
next
  case EvalAndTrue
  from EvalAndTrue.prems EvalAndTrue.hyps show ?case
    by (auto elim!: AndE dest: EvalAndTrue.IH)
next
  case EvalAndFail
  from EvalAndFail.prems EvalAndFail.hyps show ?case
    by (auto elim!: AndE dest: EvalAndFail.IH)
next
  case EvalAndNonBool
  from EvalAndNonBool.prems EvalAndNonBool.hyps show ?case
    by (auto elim!: AndE dest: EvalAndNonBool.IH)
next
  case EvalOrTrue
  from EvalOrTrue.prems EvalOrTrue.hyps show ?case
    by (auto elim!: OrE dest: EvalOrTrue.IH)
next
  case EvalOrFalse
  from EvalOrFalse.prems EvalOrFalse.hyps show ?case
    by (auto elim!: OrE dest: EvalOrFalse.IH)
next
  case EvalOrFail
  from EvalOrFail.prems EvalOrFail.hyps show ?case
    by (auto elim!: OrE dest: EvalOrFail.IH)
next
  case EvalOrNonBool
  from EvalOrNonBool.prems EvalOrNonBool.hyps show ?case
    by (auto elim!: OrE dest: EvalOrNonBool.IH)
next
  case EvalCondTrue
  from EvalCondTrue.prems EvalCondTrue.hyps show ?case
    by (auto elim!: CondE dest: EvalCondTrue.IH)
next
  case EvalCondFalse
  from EvalCondFalse.prems EvalCondFalse.hyps show ?case
    by (auto elim!: CondE dest: EvalCondFalse.IH)
next
  case EvalCondFail
  from EvalCondFail.prems EvalCondFail.hyps show ?case
    by (auto elim!: CondE dest: EvalCondFail.IH)
next
  case EvalCondNonBool
  from EvalCondNonBool.prems EvalCondNonBool.hyps show ?case
    by (auto elim!: CondE dest: EvalCondNonBool.IH)
next
  case EvalList
  from EvalList.prems EvalList.hyps show ?case
    by (auto elim!: ListE dest: EvalList.IH)
next
  case EvalListFail
  from EvalListFail.prems EvalListFail.hyps show ?case
    by (auto elim!: ListE dest: EvalListFail.IH)
next
  case EvalTuple
  from EvalTuple.prems EvalTuple.hyps show ?case
    by (auto elim!: TupleE dest: EvalTuple.IH)
next
  case EvalTupleFail
  from EvalTupleFail.prems EvalTupleFail.hyps show ?case
    by (auto elim!: TupleE dest: EvalTupleFail.IH)
next
  case EvalDict
  from EvalDict.prems EvalDict.hyps show ?case
    by (auto elim!: DictE dest: EvalDict.IH)
next
  case EvalDictFail
  from EvalDictFail.prems EvalDictFail.hyps show ?case
    by (auto elim!: DictE dest: EvalDictFail.IH)
next
  case EvalDictNonStr
  from EvalDictNonStr.prems EvalDictNonStr.hyps show ?case
    by (auto elim!: DictE dest: EvalDictNonStr.IH)
next
  case EvalSubscript
  from EvalSubscript.prems EvalSubscript.hyps show ?case
    by (auto elim!: SubscriptE dest: EvalSubscript.IH)
next
  case EvalClassTypeArgs
  from EvalClassTypeArgs.prems EvalClassTypeArgs.hyps show ?case
    by (auto elim!: SubscriptE dest: EvalClassTypeArgs.IH)
next
  case EvalSubscriptFail
  from EvalSubscriptFail.prems EvalSubscriptFail.hyps show ?case
    by (auto elim!: SubscriptE dest: EvalSubscriptFail.IH)
next
  case EvalCallLambda
  from EvalCallLambda.prems EvalCallLambda.hyps show ?case
    by (auto elim!: CallE dest: EvalCallLambda.IH)
next
  case EvalCallLambdaArity
  from EvalCallLambdaArity.prems EvalCallLambdaArity.hyps show ?case
    by (auto elim!: CallE dest: EvalCallLambdaArity.IH)
next
  case (EvalCallDef \<rho> e \<rho>' ds j f \<alpha>s xps \<psi> s vs es us \<rho>s o)
  from EvalCallDef.prems show ?case
  proof (cases rule: CallE)
    case (CallDef \<rho>'' ds' j' f' \<alpha>s' xps' \<psi>' s' us' \<rho>s' o')
    from EvalCallDef.IH(1)[OF CallDef(2)] have "\<rho>'' = \<rho>'" "ds' = ds" "j' = j" by auto
    with EvalCallDef.hyps(2) CallDef(3) have "xps' = xps" "s' = s" by auto
    moreover from EvalCallDef.IH(2)[OF CallDef(4)] have "us' = us" by simp
    moreover from calculation EvalCallDef.hyps(6) CallDef(6) have "\<rho>s' = \<rho>s" by simp
    ultimately have "o' = o"
      using EvalCallDef.IH(3) CallDef(7) \<open>\<rho>'' = \<rho>'\<close> \<open>ds' = ds\<close> EvalCallDef.hyps(3) by simp
    with CallDef(1) show ?thesis by simp
  next
    case (CallDefArity \<rho>'' ds' j' f' \<alpha>s' xps' \<psi>' s' us')
    from EvalCallDef.IH(1)[OF CallDefArity(2)] have "ds' = ds" "j' = j" by auto
    with EvalCallDef.hyps(2) CallDefArity(3) have "xps' = xps" by auto
    moreover from EvalCallDef.IH(2)[OF CallDefArity(4)] have "us' = us" by simp
    ultimately show ?thesis using CallDefArity(5) EvalCallDef.hyps(5) by simp
  qed (use EvalCallDef.hyps in \<open>auto dest: EvalCallDef.IH\<close>)
next
  case (EvalCallDefArity \<rho> e \<rho>' ds j f \<alpha>s xps \<psi> s es us)
  from EvalCallDefArity.prems show ?case
  proof (cases rule: CallE)
    case (CallDef \<rho>'' ds' j' f' \<alpha>s' xps' \<psi>' s' us' \<rho>s' o')
    from EvalCallDefArity.IH(1)[OF CallDef(2)] have "ds' = ds" "j' = j" by auto
    with EvalCallDefArity.hyps(2) CallDef(3) have "xps' = xps" by auto
    moreover from EvalCallDefArity.IH(2)[OF CallDef(4)] have "us' = us" by simp
    ultimately show ?thesis using CallDef(5) EvalCallDefArity.hyps(4) by simp
  qed (use EvalCallDefArity.hyps in \<open>auto dest: EvalCallDefArity.IH\<close>)
next
  case EvalCallNonFun
  from EvalCallNonFun.prems EvalCallNonFun.hyps show ?case
    by (auto elim!: CallE dest: EvalCallNonFun.IH)
next
  case EvalCallFail
  from EvalCallFail.prems EvalCallFail.hyps show ?case
    by (auto elim!: CallKwE dest: EvalCallFail.IH)
next
  case EvalCallFailArgs
  from EvalCallFailArgs.prems EvalCallFailArgs.hyps show ?case
    by (auto elim!: CallE dest: EvalCallFailArgs.IH)
next
  case (EvalConstr \<rho> e C es kws us xus)
  have callee: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> r = Val (VClass C)" for r using EvalConstr.IH(1) by fastforce
  have args: "\<rho>, es @ map snd kws \<Rightarrow>\<^sub>e\<^sub>s r \<Longrightarrow> r = Val us" for r using EvalConstr.IH(2) by fastforce
  then have args_positional: "kws = [] \<Longrightarrow> \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s r \<Longrightarrow> r = Val us" for r by simp
  have object: "field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) = Some yus \<Longrightarrow> xus = yus"
    for yus
    using EvalConstr.hyps(3) by simp
  from EvalConstr.prems show ?case
    by (auto elim!: CallKwE dest!: callee args args_positional intro: object)
next
  case (EvalConstrFail \<rho> e C es kws \<kappa>)
  have callee: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> r = Val (VClass C)" for r using EvalConstrFail.IH(1) by fastforce
  have args: "\<rho>, es @ map snd kws \<Rightarrow>\<^sub>e\<^sub>s r \<Longrightarrow> r = Aborts \<kappa>" for r using EvalConstrFail.IH(2) by fastforce
  then have args_positional: "kws = [] \<Longrightarrow> \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s r \<Longrightarrow> r = Aborts \<kappa>" for r by simp
  from EvalConstrFail.prems show ?case
    by (auto elim!: CallKwE dest: callee args args_positional)
next
  case EvalExprsNil
  then show ?case by (auto elim!: ExprsNilE)
next
  case EvalExprsCons
  from EvalExprsCons.prems EvalExprsCons.hyps show ?case
    by (auto elim!: ExprsConsE dest: EvalExprsCons.IH)
next
  case EvalExprsFail
  from EvalExprsFail.prems EvalExprsFail.hyps show ?case
    by (auto elim!: ExprsConsE dest: EvalExprsFail.IH)
next
  case EvalPass
  then show ?case by (auto elim!: PassE)
next
  case EvalDeclare
  then show ?case by (auto elim!: DeclareE)
next
  case EvalAssign
  from EvalAssign.prems EvalAssign.hyps show ?case
    by (auto elim!: AssignE dest: EvalAssign.IH)
next
  case EvalExprStmt
  from EvalExprStmt.prems EvalExprStmt.hyps show ?case
    by (auto elim!: ExprStmtE dest: EvalExprStmt.IH)
next
  case EvalReturn
  from EvalReturn.prems EvalReturn.hyps show ?case
    by (auto elim!: ReturnE dest: EvalReturn.IH)
next
  case EvalReturnNone
  then show ?case by (auto elim!: ReturnE)
next
  case EvalDefs
  then show ?case by (auto elim!: DefsE)
next
  case EvalAssert
  from EvalAssert.prems EvalAssert.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssert.IH)
next
  case EvalAssertFalse
  from EvalAssertFalse.prems EvalAssertFalse.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssertFalse.IH)
next
  case EvalAssertFail
  from EvalAssertFail.prems EvalAssertFail.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssertFail.IH)
next
  case EvalAssertNonBool
  from EvalAssertNonBool.prems EvalAssertNonBool.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssertNonBool.IH)
next
  case EvalAssertMsg
  from EvalAssertMsg.prems EvalAssertMsg.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssertMsg.IH)
next
  case EvalAssertMsgFalse
  from EvalAssertMsgFalse.prems EvalAssertMsgFalse.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssertMsgFalse.IH)
next
  case EvalAssertMsgFalseFail
  from EvalAssertMsgFalseFail.prems EvalAssertMsgFalseFail.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssertMsgFalseFail.IH)
next
  case EvalAssertMsgFail
  from EvalAssertMsgFail.prems EvalAssertMsgFail.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssertMsgFail.IH)
next
  case EvalAssertMsgNonBool
  from EvalAssertMsgNonBool.prems EvalAssertMsgNonBool.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssertMsgNonBool.IH)
next
  case EvalAssertMsgNonStr
  from EvalAssertMsgNonStr.prems EvalAssertMsgNonStr.hyps show ?case
    by (auto elim!: AssertE dest: EvalAssertMsgNonStr.IH)
next
  case EvalIfTrue
  from EvalIfTrue.prems EvalIfTrue.hyps show ?case
    by (auto elim!: IfE dest: EvalIfTrue.IH)
next
  case EvalIfFalse
  from EvalIfFalse.prems EvalIfFalse.hyps show ?case
    by (auto elim!: IfE dest: EvalIfFalse.IH)
next
  case EvalIfFail
  from EvalIfFail.prems EvalIfFail.hyps show ?case
    by (auto elim!: IfE dest: EvalIfFail.IH)
next
  case EvalIfNonBool
  from EvalIfNonBool.prems EvalIfNonBool.hyps show ?case
    by (auto elim!: IfE dest: EvalIfNonBool.IH)
next
  case EvalMatch
  from EvalMatch.prems show ?case
    by (auto elim!: MatchE dest!: EvalMatch.IH(1) simp: EvalMatch.hyps(2) dest: EvalMatch.IH(2))
next
  case EvalMatchFail
  from EvalMatchFail.prems EvalMatchFail.hyps show ?case
    by (auto elim!: MatchE dest: EvalMatchFail.IH)
next
  case EvalMatchAbort
  from EvalMatchAbort.prems EvalMatchAbort.hyps show ?case
    by (auto elim!: MatchE dest: EvalMatchAbort.IH)
next
  case EvalSeq
  from EvalSeq.prems EvalSeq.hyps show ?case
    by (auto elim!: SeqE dest: EvalSeq.IH)
next
  case EvalSeqReturn
  from EvalSeqReturn.prems EvalSeqReturn.hyps show ?case
    by (auto elim!: SeqE dest: EvalSeqReturn.IH)
next
  case EvalSeqFail
  from EvalSeqFail.prems EvalSeqFail.hyps show ?case
    by (auto elim!: SeqE dest: EvalSeqFail.IH)
next
  case EvalIfNone
  then show ?case by (auto elim!: ElifNilE)
next
  case EvalElse
  from EvalElse.prems EvalElse.hyps show ?case
    by (auto elim!: ElifNilE dest: EvalElse.IH)
next
  case EvalElifTrue
  from EvalElifTrue.prems EvalElifTrue.hyps show ?case
    by (auto elim!: ElifConsE dest: EvalElifTrue.IH)
next
  case EvalElifFalse
  from EvalElifFalse.prems EvalElifFalse.hyps show ?case
    by (auto elim!: ElifConsE dest: EvalElifFalse.IH)
next
  case EvalElifFail
  from EvalElifFail.prems EvalElifFail.hyps show ?case
    by (auto elim!: ElifConsE dest: EvalElifFail.IH)
next
  case EvalElifNonBool
  from EvalElifNonBool.prems EvalElifNonBool.hyps show ?case
    by (auto elim!: ElifConsE dest: EvalElifNonBool.IH)
next
  case EvalListComp
  from EvalListComp.prems EvalListComp.hyps show ?case
    by (auto elim!: ListCompE dest: EvalListComp.IH)
next
  case EvalListCompFailQuals
  from EvalListCompFailQuals.prems EvalListCompFailQuals.hyps show ?case
    by (auto elim!: ListCompE dest: EvalListCompFailQuals.IH)
next
  case EvalListCompFail
  from EvalListCompFail.prems EvalListCompFail.hyps show ?case
    by (auto elim!: ListCompE dest: EvalListCompFail.IH)
next
  case EvalDictComp
  from EvalDictComp.prems EvalDictComp.hyps show ?case
    by (auto elim!: DictCompE dest: EvalDictComp.IH)
next
  case EvalDictCompFailQuals
  from EvalDictCompFailQuals.prems EvalDictCompFailQuals.hyps show ?case
    by (auto elim!: DictCompE dest: EvalDictCompFailQuals.IH)
next
  case EvalDictCompFail
  from EvalDictCompFail.prems EvalDictCompFail.hyps show ?case
    by (auto elim!: DictCompE dest: EvalDictCompFail.IH)
next
  case EvalQualsNil
  then show ?case by (auto elim!: QualsNilE)
next
  case EvalQualGuardTrue
  from EvalQualGuardTrue.prems EvalQualGuardTrue.hyps show ?case
    by (auto elim!: QualGuardE dest: EvalQualGuardTrue.IH)
next
  case EvalQualGuardFalse
  from EvalQualGuardFalse.prems EvalQualGuardFalse.hyps show ?case
    by (auto elim!: QualGuardE dest: EvalQualGuardFalse.IH)
next
  case EvalQualGuardFail
  from EvalQualGuardFail.prems EvalQualGuardFail.hyps show ?case
    by (auto elim!: QualGuardE dest: EvalQualGuardFail.IH)
next
  case EvalQualGuardNonBool
  from EvalQualGuardNonBool.prems EvalQualGuardNonBool.hyps show ?case
    by (auto elim!: QualGuardE dest: EvalQualGuardNonBool.IH)
next
  case EvalQualGenerator
  from EvalQualGenerator.prems show ?case
    by (auto elim!: QualGeneratorE dest!: EvalQualGenerator.IH(1) simp: EvalQualGenerator.hyps(2)
      dest: EvalQualGenerator.IH(2))
next
  case EvalQualGeneratorFail
  from EvalQualGeneratorFail.prems EvalQualGeneratorFail.hyps show ?case
    by (auto elim!: QualGeneratorE dest: EvalQualGeneratorFail.IH)
next
  case EvalQualGeneratorNonSeq
  from EvalQualGeneratorNonSeq.prems EvalQualGeneratorNonSeq.hyps show ?case
    by (auto elim!: QualGeneratorE dest: EvalQualGeneratorNonSeq.IH)
next
  case EvalGenNil
  then show ?case by (auto elim!: GenNilE)
next
  case EvalGenCons
  from EvalGenCons.prems EvalGenCons.hyps show ?case
    by (auto elim!: GenConsE dest: EvalGenCons.IH)
next
  case EvalGenFail
  from EvalGenFail.prems EvalGenFail.hyps show ?case
    by (auto elim!: GenConsE dest: EvalGenFail.IH)
next
  case EvalCompNil
  then show ?case by (auto elim!: CompNilE)
next
  case EvalCompCons
  from EvalCompCons.prems EvalCompCons.hyps show ?case
    by (auto elim!: CompConsE dest: EvalCompCons.IH)
next
  case EvalCompFail
  from EvalCompFail.prems EvalCompFail.hyps show ?case
    by (auto elim!: CompConsE dest: EvalCompFail.IH)
next
  case EvalEntriesNil
  then show ?case by (auto elim!: EntriesNilE)
next
  case EvalEntriesCons
  from EvalEntriesCons.prems EvalEntriesCons.hyps show ?case
    by (auto elim!: EntriesConsE dest: EvalEntriesCons.IH)
next
  case EvalEntriesFailKey
  from EvalEntriesFailKey.prems EvalEntriesFailKey.hyps show ?case
    by (auto elim!: EntriesConsE dest: EvalEntriesFailKey.IH)
next
  case EvalEntriesNonStr
  from EvalEntriesNonStr.prems EvalEntriesNonStr.hyps show ?case
    by (auto elim!: EntriesConsE dest: EvalEntriesNonStr.IH)
next
  case EvalEntriesFailValue
  from EvalEntriesFailValue.prems EvalEntriesFailValue.hyps show ?case
    by (auto elim!: EntriesConsE dest: EvalEntriesFailValue.IH)
qed

end

end
