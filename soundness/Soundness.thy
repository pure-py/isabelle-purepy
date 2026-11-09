(* Type soundness *)
theory Soundness
  imports Attributes Comprehensions Calls Statements
begin

context evaluation
begin

(* Soundness of each evaluation rule *)
lemmas rule_sound =
  var_sound var_unknown_sound var_unbound_sound literal_sound lambda_sound unop_sound binop_sound
  binop_fail_sound and_false_sound and_true_sound and_fail_sound and_nonbool_sound or_true_sound
  or_false_sound or_fail_sound or_nonbool_sound cond_true_sound cond_false_sound cond_fail_sound
  cond_nonbool_sound list_sound list_fail_sound tuple_sound tuple_fail_sound dict_sound dict_fail_sound
  dict_nonstr_sound subscript_sound class_type_args_sound subscript_fail_sound list_comp_sound
  list_comp_fail_quals_sound list_comp_fail_sound dict_comp_sound dict_comp_fail_quals_sound
  dict_comp_fail_sound attr_object_sound attr_object_missing_sound attr_module_sound
  attr_module_missing_sound attr_nonobject_sound attr_fail_sound call_lambda_sound call_lambda_arity_sound
  call_def_sound call_def_arity_sound call_prim_sound call_nonfun_sound call_fail_sound call_fail_args_sound
  constr_sound constr_arity_sound constr_fail_sound exprs_nil_sound exprs_cons_sound exprs_fail_sound
  pass_sound declare_sound assign_sound expr_stmt_sound print_sound return_sound return_none_sound defs_sound
  assert_sound assert_false_sound assert_fail_sound assert_nonbool_sound assert_msg_false_fail_sound
  assert_msg_nonstr_sound if_true_sound if_false_sound if_fail_sound if_nonbool_sound match_sound
  match_fail_sound match_abort_sound seq_sound seq_exit_sound if_none_sound else_sound elif_true_sound
  elif_false_sound elif_fail_sound elif_nonbool_sound quals_nil_sound qual_guard_true_sound
  qual_guard_false_sound qual_guard_fail_sound qual_guard_nonbool_sound qual_generator_sound
  qual_generator_fail_sound qual_generator_nonseq_sound gen_nil_sound gen_cons_sound gen_fail_sound
  comp_nil_sound comp_cons_sound comp_fail_sound entries_nil_sound entries_cons_sound entries_fail_key_sound
  entries_nonstr_sound entries_fail_value_sound

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
  by (induction
      rule: eval_expr_eval_exprs_eval_stmt_eval_elif_eval_quals_eval_gen_eval_comp_eval_entries.inducts)
     (auto intro: rule_sound)

end

context loading
begin

theorem type_soundness:
  assumes "check_module \<M> [] predefined_classes main main = Ok (\<Gamma>, \<Sigma>)" and "eval_program \<A> vs \<kappa>"
  shows "\<kappa> \<notin> {TypeError, AttributeError, NameError, Excluded}"
  sorry

end

end
