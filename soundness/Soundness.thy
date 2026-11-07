(* Type soundness *)
theory Soundness
  imports Expressions Calls Statements
begin

context evaluation
begin

theorem soundness:
  shows
      expr_sound: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> sound_expr \<rho> e r"
  and exprs_sound: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s rs \<Longrightarrow> sound_exprs \<rho> es rs"
  and stmt_sound: "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> sound_stmt \<rho> s o"
  and elif_sound: "\<rho>, eb \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o' \<Longrightarrow> sound_elif \<rho> eb o'"
  and quals_sound: "\<rho>, gs \<Rightarrow>\<^sub>q q \<Longrightarrow> sound_quals \<rho> gs q"
  and gen_sound: "\<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n q \<Longrightarrow> sound_gen \<rho> x us gs q"
  and comp_sound: "\<rho>s, ec \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p vr \<Longrightarrow> sound_comp \<rho>s ec vr"
  and entries_sound: "\<rho>s, ec, ec' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s dr \<Longrightarrow> sound_entries \<rho>s ec ec' dr"
proof (induction
    rule: eval_expr_eval_exprs_eval_stmt_eval_elif_eval_quals_eval_gen_eval_comp_eval_entries.inducts)
  case EvalVar
  then show ?case by (blast intro: var_sound)
next
  case EvalVarUnknown
  then show ?case by (blast intro: var_unknown_sound)
next
  case EvalVarUnbound
  then show ?case by (blast intro: var_unbound_sound)
next
  case EvalLiteral
  show ?case by (rule literal_sound)
next
  case EvalLambda
  show ?case by (rule lambda_sound)
next
  case EvalUnOp
  then show ?case by (blast intro: unop_sound)
next
  case EvalBinOp
  then show ?case by (blast intro: binop_sound)
next
  case EvalBinOpFail
  then show ?case by (blast intro: binop_fail_sound)
next
  case EvalAndFalse
  then show ?case by (blast intro: and_false_sound)
next
  case EvalAndTrue
  then show ?case by (blast intro: and_true_sound)
next
  case EvalAndFail
  then show ?case by (blast intro: and_fail_sound)
next
  case EvalAndNonBool
  then show ?case by (blast intro: and_nonbool_sound)
next
  case EvalOrTrue
  then show ?case by (blast intro: or_true_sound)
next
  case EvalOrFalse
  then show ?case by (blast intro: or_false_sound)
next
  case EvalOrFail
  then show ?case by (blast intro: or_fail_sound)
next
  case EvalOrNonBool
  then show ?case by (blast intro: or_nonbool_sound)
next
  case EvalCondTrue
  then show ?case by (blast intro: cond_true_sound)
next
  case EvalCondFalse
  then show ?case by (blast intro: cond_false_sound)
next
  case EvalCondFail
  then show ?case by (blast intro: cond_fail_sound)
next
  case EvalCondNonBool
  then show ?case by (blast intro: cond_nonbool_sound)
next
  case EvalList
  then show ?case by (blast intro: list_sound)
next
  case EvalListFail
  then show ?case by (blast intro: list_fail_sound)
next
  case EvalTuple
  then show ?case by (blast intro: tuple_sound)
next
  case EvalTupleFail
  then show ?case by (blast intro: tuple_fail_sound)
next
  case EvalDict
  then show ?case by (blast intro: dict_sound)
next
  case EvalDictFail
  then show ?case by (blast intro: dict_fail_sound)
next
  case EvalDictNonStr
  then show ?case by (blast intro: dict_nonstr_sound)
next
  case EvalSubscript
  then show ?case by (blast intro: subscript_sound)
next
  case EvalClassTypeArgs
  then show ?case by (blast intro: class_type_args_sound)
next
  case EvalSubscriptFail
  then show ?case by (blast intro: subscript_fail_sound)
next
  case EvalListComp
  then show ?case by (blast intro: list_comp_sound)
next
  case EvalListCompFailQuals
  then show ?case by (blast intro: list_comp_fail_quals_sound)
next
  case EvalListCompFail
  then show ?case by (blast intro: list_comp_fail_sound)
next
  case EvalDictComp
  then show ?case by (blast intro: dict_comp_sound)
next
  case EvalDictCompFailQuals
  then show ?case by (blast intro: dict_comp_fail_quals_sound)
next
  case EvalDictCompFail
  then show ?case by (blast intro: dict_comp_fail_sound)
next
  case EvalAttrObject
  then show ?case by (blast intro: attr_object_sound)
next
  case EvalAttrObjectMissing
  then show ?case by (blast intro: attr_object_missing_sound)
next
  case EvalAttrModule
  then show ?case by (blast intro: attr_module_sound)
next
  case EvalAttrModuleMissing
  then show ?case by (blast intro: attr_module_missing_sound)
next
  case EvalAttrNonObject
  then show ?case by (blast intro: attr_nonobject_sound)
next
  case EvalAttrFail
  then show ?case by (blast intro: attr_fail_sound)
next
  case EvalCallLambda
  then show ?case by (blast intro: call_lambda_sound)
next
  case EvalCallLambdaArity
  then show ?case by (blast intro: call_lambda_arity_sound)
next
  case EvalCallDef
  then show ?case by (blast intro: call_def_sound)
next
  case EvalCallDefArity
  then show ?case by (blast intro: call_def_arity_sound)
next
  case EvalCallPrim
  then show ?case by (blast intro: call_prim_sound)
next
  case EvalCallNonFun
  then show ?case by (blast intro: call_nonfun_sound)
next
  case EvalCallFail
  then show ?case by (blast intro: call_fail_sound)
next
  case EvalCallFailArgs
  then show ?case by (blast intro: call_fail_args_sound)
next
  case EvalConstr
  then show ?case by (blast intro: constr_sound)
next
  case EvalConstrArity
  then show ?case by (blast intro: constr_arity_sound)
next
  case EvalConstrFail
  then show ?case by (blast intro: constr_fail_sound)
next
  case EvalExprsNil
  show ?case by (rule exprs_nil_sound)
next
  case EvalExprsCons
  then show ?case by (blast intro: exprs_cons_sound)
next
  case EvalExprsFail
  then show ?case by (blast intro: exprs_fail_sound)
next
  case EvalPass
  show ?case by (rule pass_sound)
next
  case EvalDeclare
  show ?case by (rule declare_sound)
next
  case EvalAssign
  then show ?case by (blast intro: assign_sound)
next
  case EvalExprStmt
  then show ?case by (blast intro: expr_stmt_sound)
next
  case EvalPrint
  then show ?case by (blast intro: print_sound)
next
  case EvalReturn
  then show ?case by (blast intro: return_sound)
next
  case EvalReturnNone
  show ?case by (rule return_none_sound)
next
  case EvalDefs
  then show ?case by (blast intro: defs_sound)
next
  case EvalAssert
  then show ?case by (blast intro: assert_sound)
next
  case EvalAssertFalse
  then show ?case by (blast intro: assert_false_sound)
next
  case EvalAssertFail
  then show ?case by (blast intro: assert_fail_sound)
next
  case EvalAssertNonBool
  then show ?case by (blast intro: assert_nonbool_sound)
next
  case EvalAssertMsg
  then show ?case by (blast intro: assert_sound)
next
  case EvalAssertMsgFalse
  then show ?case by (blast intro: assert_false_sound)
next
  case EvalAssertMsgFalseFail
  then show ?case by (blast intro: assert_msg_false_fail_sound)
next
  case EvalAssertMsgFail
  then show ?case by (blast intro: assert_fail_sound)
next
  case EvalAssertMsgNonBool
  then show ?case by (blast intro: assert_nonbool_sound)
next
  case EvalAssertMsgNonStr
  then show ?case by (blast intro: assert_msg_nonstr_sound)
next
  case EvalIfTrue
  then show ?case by (blast intro: if_true_sound)
next
  case EvalIfFalse
  then show ?case by (blast intro: if_false_sound)
next
  case EvalIfFail
  then show ?case by (blast intro: if_fail_sound)
next
  case EvalIfNonBool
  then show ?case by (blast intro: if_nonbool_sound)
next
  case EvalMatch
  then show ?case by (blast intro: match_sound)
next
  case EvalMatchFail
  then show ?case by (blast intro: match_fail_sound)
next
  case EvalMatchAbort
  then show ?case by (blast intro: match_abort_sound)
next
  case EvalSeq
  then show ?case by (blast intro: seq_sound)
next
  case EvalSeqReturn
  then show ?case by (auto intro: seq_exit_sound)
next
  case EvalSeqFail
  then show ?case by (auto intro: seq_exit_sound)
next
  case EvalIfNone
  show ?case by (rule if_none_sound)
next
  case EvalElse
  then show ?case by (blast intro: else_sound)
next
  case EvalElifTrue
  then show ?case by (blast intro: elif_true_sound)
next
  case EvalElifFalse
  then show ?case by (blast intro: elif_false_sound)
next
  case EvalElifFail
  then show ?case by (blast intro: elif_fail_sound)
next
  case EvalElifNonBool
  then show ?case by (blast intro: elif_nonbool_sound)
next
  case EvalQualsNil
  show ?case by (rule quals_nil_sound)
next
  case EvalQualGuardTrue
  then show ?case by (blast intro: qual_guard_true_sound)
next
  case EvalQualGuardFalse
  then show ?case by (blast intro: qual_guard_false_sound)
next
  case EvalQualGuardFail
  then show ?case by (blast intro: qual_guard_fail_sound)
next
  case EvalQualGuardNonBool
  then show ?case by (blast intro: qual_guard_nonbool_sound)
next
  case EvalQualGenerator
  then show ?case by (blast intro: qual_generator_sound)
next
  case EvalQualGeneratorFail
  then show ?case by (blast intro: qual_generator_fail_sound)
next
  case EvalQualGeneratorNonSeq
  then show ?case by (blast intro: qual_generator_nonseq_sound)
next
  case EvalGenNil
  show ?case by (rule gen_nil_sound)
next
  case EvalGenCons
  then show ?case by (blast intro: gen_cons_sound)
next
  case EvalGenFail
  then show ?case by (blast intro: gen_fail_sound)
next
  case EvalCompNil
  show ?case by (rule comp_nil_sound)
next
  case EvalCompCons
  then show ?case by (blast intro: comp_cons_sound)
next
  case EvalCompFail
  then show ?case by (blast intro: comp_fail_sound)
next
  case EvalEntriesNil
  show ?case by (rule entries_nil_sound)
next
  case EvalEntriesCons
  then show ?case by (blast intro: entries_cons_sound)
next
  case EvalEntriesFailKey
  then show ?case by (blast intro: entries_fail_key_sound)
next
  case EvalEntriesNonStr
  then show ?case by (blast intro: entries_nonstr_sound)
next
  case EvalEntriesFailValue
  then show ?case by (blast intro: entries_fail_value_sound)
qed

end

context loading
begin

theorem type_soundness:
  assumes "check_module \<M> [] predefined_classes main main = Ok (\<Gamma>, \<Sigma>)" and "eval_program \<A> vs \<kappa>"
  shows "\<kappa> \<notin> {TypeError, AttributeError, NameError, Excluded}"
  sorry

end

end
