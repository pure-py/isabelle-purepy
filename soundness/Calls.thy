(* Soundness of call evaluation *)
theory Calls
  imports ResultTyping
begin

context evaluation
begin

lemma entry_of_expr_entry: "entry_of \<Gamma> e = Some \<theta> \<Longrightarrow> expr_entry \<Gamma> e = Some \<theta>"
  by (cases e) (simp_all add: entry_of_def)

lemma constructor_class_entry: "constructor_class \<Sigma> \<Gamma> e = Some m \<Longrightarrow> \<exists>C. expr_entry \<Gamma> (node e) = Some (Type C)"
  by (auto simp: constructor_class_def split: option.splits expr.splits if_splits dest: class_of_name_entry)

lemma callee_entry:
  "callee \<Sigma> \<Gamma> e es = Ok \<sigma> \<Longrightarrow> (\<exists>\<pi>. expr_entry \<Gamma> (node e) = Some (Scheme \<pi>)) \<or> synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
  by (auto simp: callee.simps scheme_of_name_def split: option.splits cxt_entry.splits
      dest!: entry_of_expr_entry)

(* Callee of a call, a lambda or typed as a class name, a name bound at a scheme or by synthesis *)
lemma call_callee_typed:
  assumes "has_type \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau>"
  shows "(\<exists>xs e'. lambda_of (node e) = Some (xs, e')) \<or> (\<exists>C. expr_entry \<Gamma> (node e) = Some (Type C))
    \<or> (\<exists>\<sigma>. callee \<Sigma> \<Gamma> e es = Ok \<sigma>)"
proof (cases "lambda_of (node e)")
  case None
  show ?thesis
  proof (cases "constructor_class \<Sigma> \<Gamma> e")
    case (Some m)
    then show ?thesis by (blast dest: constructor_class_entry)
  next
    case c: None
    with None assms show ?thesis
      by (auto simp: has_type_def check_expr.simps bind_sum_def ensure_def split: sum.splits)
  qed
qed auto

(* Entry of a name in a typed environment *)
lemma wf_env_resolve:
  "\<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; lookup \<Gamma> q = Some \<theta> ; \<theta> \<noteq> TypeVar \<rbrakk> \<Longrightarrow> \<exists>v. resolve \<rho> q = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
proof (induction q arbitrary: \<theta>)
  case (Simple x)
  then show ?case by (auto dest: wf_env_lookup)
next
  case (Qualified q x)
  from Qualified(3) obtain q' \<Gamma>' where q: "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')" and x: "fmlookup \<Gamma>' x = Some \<theta>"
    by (auto split: option.splits cxt_entry.splits)
  have closed: "tyvars \<Gamma>' = {}" using lookup_wf[OF wf_env_wf_cxt[OF Qualified(2)] q] by simp
  from Qualified(1)[OF Qualified(2) q] obtain v where "resolve \<rho> q = Some v" and "\<turnstile> v : ModChecked q' \<Gamma>'"
    by auto
  moreover from this(2) obtain \<rho>' \<eta>' where "v = VModLoaded q' \<rho>'" and "\<eta>' \<turnstile> \<rho>' : \<Gamma>'"
    by (auto dest: wf_mod_checked)
  moreover from module_member[OF this(2) closed x Qualified(4)] obtain v' where "fmlookup \<rho>' x = Some v'"
    and "\<turnstile> v' : \<theta>" and "fv_entry \<theta> = {}"
    by blast
  ultimately show ?case by (simp add: inst_entry_closed)
qed

lemma lookup_scheme:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "lookup \<Gamma> q = Some (Scheme \<pi>)"
  shows "callable_scheme \<pi>"
proof (cases q)
  case (Simple x)
  with assms show ?thesis by (auto dest: wf_env_scheme)
next
  case (Qualified q' x)
  with assms(2) obtain q'' \<Gamma>' where q': "lookup \<Gamma> q' = Some (ModChecked q'' \<Gamma>')"
    and x: "fmlookup \<Gamma>' x = Some (Scheme \<pi>)"
    by (auto split: option.splits cxt_entry.splits)
  from wf_env_resolve[OF assms(1) q'] obtain v where "\<turnstile> v : ModChecked q'' \<Gamma>'" by auto
  then obtain \<rho>' \<eta>' where "\<eta>' \<turnstile> \<rho>' : \<Gamma>'" by (auto dest: wf_mod_checked)
  from wf_env_scheme[OF this x] show ?thesis .
qed

(* Value of the callee of a call, typed by the type of the callee *)
lemma callee_value:
  assumes "sound_expr \<rho> (node e) (Val v)" and env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "callee \<Sigma> \<Gamma> e es = Ok \<sigma>"
  shows "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
proof (cases "scheme_of_name \<Gamma> (node e)")
  case None
  with assms(3) have "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>" by (simp add: callee.simps)
  with sound_expr_synth_at[OF assms(1) env this] show ?thesis by simp
next
  case (Some \<pi>)
  then have entry: "entry_of \<Gamma> (node e) = Some (Scheme \<pi>)"
    by (auto simp: scheme_of_name_def split: option.splits cxt_entry.splits)
  then obtain q where "resolve_name \<Gamma> q = Some (Scheme \<pi>)" by (auto simp: entry_of_def bind_eq_Some_conv)
  from lookup_scheme[OF env resolve_name_lookup[OF this]] obtain \<alpha>s \<sigma>s \<sigma>'
    where \<pi>: "\<pi> = TyScheme \<alpha>s (TyCallable \<sigma>s \<sigma>')"
    by (auto elim: callable_scheme.elims)
  with Some assms(3) obtain \<tau>s where \<tau>s: "inferred_type_args \<Sigma> \<alpha>s \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
    and \<sigma>: "\<sigma> = subst \<tau>s \<alpha>s (TyCallable \<sigma>s \<sigma>')"
    by (auto simp: callee.simps bind_sum_def split: sum.splits)
  from sound_expr_name[OF assms(1) env entry_of_expr_entry[OF entry]] \<pi>
  have v: "\<turnstile> v : Scheme (TyScheme \<alpha>s (inst (shadow \<alpha>s \<eta>) (TyCallable \<sigma>s \<sigma>')))"
    by simp
  have len: "length \<tau>s = length \<alpha>s" using \<tau>s by (rule inferred_type_args_length)
  have "wf_ty \<Sigma> \<tau>'" if "Ok \<tau>' \<in> set (map (synth_expr_at \<Sigma> \<Gamma>) es)" for \<tau>'
  proof -
    from that obtain e' where "synth_expr_at \<Sigma> \<Gamma> e' = Ok \<tau>'" by auto
    with synth_at_wf_ty[OF wf_env_wf_cxt[OF env]] show ?thesis by blast
  qed
  from inferred_type_args_fv[OF \<tau>s, of UNIV] this have wf_\<tau>s: "\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>" by blast
  have closed: "\<forall>\<tau> \<in> set (map (inst \<eta>) \<tau>s). fv \<tau> = {}" by (simp add: inst_closed[OF wf_env_wf_inst[OF env]])
  have wfs: "\<forall>\<tau> \<in> set (map (inst \<eta>) \<tau>s). wf_ty \<Sigma> \<tau>" using wf_\<tau>s wf_env_wf_inst[OF env] by (auto intro: inst_wf)
  from wf_val_wf_env.ValInst[OF v _ closed wfs] len show ?thesis
    unfolding \<sigma> by (simp only: inst_subst[OF wf_env_wf_inst[OF env] len] length_map)
qed

(* Callable typing a callee value at the type of the callee, with the arguments checked against its parameter
   types *)
lemma synth_call_callable:
  "\<lbrakk> synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau> ; \<turnstile> v : Ty (inst \<eta> \<sigma>) \<rbrakk>
  \<Longrightarrow> \<exists>\<sigma>s \<tau>'. \<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>')) \<and> check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok () \<and> \<Sigma> \<turnstile> \<tau>' <: \<tau>"
proof (induction \<sigma> arbitrary: \<tau>)
  case (TyUnion \<sigma> \<sigma>')
  from TyUnion(3) obtain \<tau>' \<tau>'' where \<tau>': "synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau>'"
    and \<tau>'': "synth_call \<Sigma> \<Gamma> e \<sigma>' kws es = Ok \<tau>''" and \<tau>: "\<tau> = \<tau>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>''"
    by (auto simp: bind_sum_def split: sum.splits)
  have wf: "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> \<sigma>'" using wf_ty_inst_inv[OF wf_val_ty[OF TyUnion(4)]] by simp_all
  have wf\<tau>': "wf_ty \<Sigma> \<tau>'" and wf\<tau>'': "wf_ty \<Sigma> \<tau>''"
    using synth_wf(5)[OF wf(1)] synth_wf(5)[OF wf(2)] \<tau>' \<tau>'' by blast+
  from wf_val_union[of v "inst \<eta> \<sigma>" "inst \<eta> \<sigma>'"] TyUnion(4)
  have "\<turnstile> v : Ty (inst \<eta> \<sigma>) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>')" by simp
  then show ?case
  proof
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    from TyUnion(1)[OF \<tau>' this] obtain \<sigma>s \<tau>0 where v: "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>0))"
      and "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()" and sub: "\<Sigma> \<turnstile> \<tau>0 <: \<tau>'"
      by blast
    moreover have "wf_ty \<Sigma> \<tau>0" using wf_ty_inst_inv[OF wf_val_ty[OF v]] by simp
    then have "\<Sigma> \<turnstile> \<tau>0 <: \<tau>" unfolding \<tau> by (rule subty_trans[OF wf_class_table _ wf\<tau>' sub join_upper(1)])
    ultimately show ?case by (intro exI[of _ \<sigma>s] exI[of _ \<tau>0]) auto
  next
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>')"
    from TyUnion(2)[OF \<tau>'' this] obtain \<sigma>s \<tau>0 where v: "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>0))"
      and "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()" and sub: "\<Sigma> \<turnstile> \<tau>0 <: \<tau>''"
      by blast
    moreover have "wf_ty \<Sigma> \<tau>0" using wf_ty_inst_inv[OF wf_val_ty[OF v]] by simp
    then have "\<Sigma> \<turnstile> \<tau>0 <: \<tau>" unfolding \<tau> by (rule subty_trans[OF wf_class_table _ wf\<tau>'' sub join_upper(2)])
    ultimately show ?case by (intro exI[of _ \<sigma>s] exI[of _ \<tau>0]) auto
  qed
next
  case (TyCallable \<sigma>s \<tau>')
  then show ?case by (auto simp: bind_sum_def ensure_def split: sum.splits if_splits intro: SubtyRefl)
qed simp_all

lemma check_call_stmt_callable:
  "\<lbrakk> check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok () ; \<turnstile> v : Ty (inst \<eta> \<sigma>) \<rbrakk>
  \<Longrightarrow> \<exists>\<sigma>s \<tau>'. \<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>')) \<and> check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()"
proof (induction \<sigma>)
  case (TyUnion \<sigma> \<sigma>')
  from TyUnion(3) have a: "check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok ()"
    and b: "check_call_stmt \<Sigma> \<Gamma> e \<sigma>' kws es = Ok ()"
    by (auto simp: bind_sum_def split: sum.splits)
  from wf_val_union[of v "inst \<eta> \<sigma>" "inst \<eta> \<sigma>'"] TyUnion(4)
  have "\<turnstile> v : Ty (inst \<eta> \<sigma>) \<or> \<turnstile> v : Ty (inst \<eta> \<sigma>')" by simp
  then show ?case
  proof
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>)"
    from TyUnion(1)[OF a this] obtain \<sigma>s \<tau>0 where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>0))"
      and "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()"
      by blast
    then show ?case by (intro exI[of _ \<sigma>s] exI[of _ \<tau>0]) auto
  next
    assume "\<turnstile> v : Ty (inst \<eta> \<sigma>')"
    from TyUnion(2)[OF b this] obtain \<sigma>s \<tau>0 where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>0))"
      and "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()"
      by blast
    then show ?case by (intro exI[of _ \<sigma>s] exI[of _ \<tau>0]) auto
  qed
next
  case (TyCallable \<sigma>s \<tau>)
  show ?case
  proof (cases "\<tau> = TyPrim NoneType")
    case True
    with TyCallable show ?thesis by (intro exI[of _ \<sigma>s] exI[of _ \<tau>]) auto
  next
    case False
    from TyCallable(3) have "do { synth_call \<Sigma> \<Gamma> e (TyCallable \<sigma>s \<tau>) kws es; Ok () } = Ok ()"
      by (simp only: check_call_stmt_synth[OF False])
    then obtain \<tau>' where "synth_call \<Sigma> \<Gamma> e (TyCallable \<sigma>s \<tau>) kws es = Ok \<tau>'"
      by (cases "synth_call \<Sigma> \<Gamma> e (TyCallable \<sigma>s \<tau>) kws es") (simp_all add: bind_sum_def)
    from synth_call_callable[OF this TyCallable(4)] show ?thesis by blast
  qed
qed (auto simp: bind_sum_def split: sum.splits)

(* Value typed at a callable type, typed by the rule for its form at a callable type below it *)
lemma wf_callable:
  assumes "\<turnstile> v : Ty (TyCallable \<sigma>s \<tau>)"
  obtains \<sigma>s' \<tau>' where "intro_typed v (TyCallable \<sigma>s' \<tau>')" and "\<Sigma> \<turnstile> \<sigma>s [<:] \<sigma>s'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
proof -
  from wf_val_intro(1)[OF assms] obtain \<sigma> where intro: "intro_typed v \<sigma>" and sub: "\<Sigma> \<turnstile> \<sigma> <: TyCallable \<sigma>s \<tau>"
    by blast
  from subty_callable_inv(1)[OF sub refl] intro_typed_nonunion[OF intro] intro that show thesis by blast
qed

lemma intro_callable_value: "intro_typed v (TyCallable \<sigma>s \<tau>) \<Longrightarrow> is_closure v \<or> is_prim v"
  by (cases v) auto

(* Typing of a call by synthesis, or as a call statement *)
lemma call_typed:
  assumes "has_type \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau>" and "lambda_of (node e) = None"
  obtains (synth) \<tau>' where "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
    | (stmt) \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" and "check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok ()"
      and "\<tau> = TyPrim object"
proof -
  from assms(2) have "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = None" by simp
  with assms(1) show thesis unfolding has_type_def by (auto dest!: check_expr_cases intro: synth stmt SubtyRefl)
qed

(* Call through a typed callee: by synthesis at a subtype, or as a call statement *)
lemma call_typed_callee:
  assumes "has_type \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau>" and "lambda_of (node e) = None"
    and "constructor_class \<Sigma> \<Gamma> e = None"
  obtains (synth) \<sigma> \<tau>' where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" and "synth_call \<Sigma> \<Gamma> e \<sigma> kws es = Ok \<tau>'"
      and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
    | (stmt) \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" and "check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = Ok ()"
      and "\<tau> = TyPrim object"
  using assms(1, 2)
proof (cases rule: call_typed)
  case (synth \<tau>')
  with assms(2, 3) show thesis by (auto simp: bind_sum_def split: sum.splits intro: that(1))
next
  case stmt
  then show thesis by (rule that(2))
qed

lemma check_args_typed:
  assumes "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()" and "\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>"
  shows "kws = []" and "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<sigma>s"
proof -
  from assms(1) have kws: "kws = []" and len: "length es = length \<sigma>s"
    and checked: "all_sum (map2 (check_expr_at \<Sigma> \<Gamma>) es \<sigma>s) = Ok ()"
    by (auto simp: check_args.simps bind_sum_def ensure_def split: sum.splits if_splits)
  from all_sum_map2_Ok[OF checked len] have "list_all2 (\<lambda>e \<sigma>. check_expr_at \<Sigma> \<Gamma> e \<sigma> = Ok ()) es \<sigma>s" .
  then show "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<sigma>s"
    by (rule list.rel_mono_strong) (use assms(2) in \<open>auto intro: has_type_check_at\<close>)
  from kws show "kws = []" .
qed

lemma sound_exprs_typed:
  "\<lbrakk> sound_exprs \<rho> es (Val us) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s \<rbrakk>
  \<Longrightarrow> list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty (inst \<eta> \<tau>)) us \<tau>s"
  by (simp add: sound_exprs_def list.rel_map)

(* Environment of a function body: the environment of the function, with the parameters bound to the
   arguments *)
lemma wf_env_params:
  assumes "\<eta> \<turnstile> \<rho> : \<Gamma>" and "params_cxt xs \<sigma>s = Ok \<Delta>" and "length xs = length \<sigma>s"
    and "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty (inst \<eta> \<sigma>)) vs \<sigma>s"
  shows "\<eta> \<turnstile> \<rho> \<otimes> fmap_of_list (zip xs vs) : \<Gamma> \<otimes> \<Delta>"
proof -
  from assms(2) have \<Delta>: "\<Delta> = fmap_of_list (zip xs (map Ty \<sigma>s))" by (auto simp: params_cxt_def split: if_splits)
  from assms(4) have len: "length vs = length \<sigma>s" by (rule list_all2_lengthD)
  from assms(4) have typed: "list_all2 (\<lambda>v \<theta>. \<turnstile> v : inst_entry \<eta> \<theta>) vs (map Ty \<sigma>s)" by (simp add: list.rel_map)
  show ?thesis
  proof (rule wf_env_add[OF assms(1)])
    have entries: "\<exists>\<sigma> \<in> set \<sigma>s. \<theta> = Ty \<sigma>" if "fmlookup \<Delta> x = Some \<theta>" for x \<theta>
      using that by (auto simp: \<Delta> fmlookup_of_list dest!: map_of_SomeD set_zip_rightD)
    show "fmdom (fmap_of_list (zip xs vs)) |\<subseteq>| fmdom \<Delta>" using assms(3) len by (simp add: \<Delta>)
    show "\<exists>v. fmlookup (\<rho> \<otimes> fmap_of_list (zip xs vs)) x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
      if "fmlookup \<Delta> x = Some \<theta>" and "\<theta> \<noteq> TypeVar" for x \<theta>
    proof -
      from rel_option_map_of_zip[OF typed, of xs x] that(1) obtain v where "map_of (zip xs vs) x = Some v"
        and "\<turnstile> v : inst_entry \<eta> \<theta>"
        by (cases "map_of (zip xs vs) x") (auto simp: \<Delta> fmlookup_of_list)
      then show ?thesis using fmdomI[of "fmap_of_list (zip xs vs)" x v] by (simp add: fmlookup_of_list)
    qed
    show "wf_cxt \<Sigma> \<Delta>"
    proof (rule wf_cxt_iff[THEN iffD2], intro allI impI)
      fix x \<theta>
      assume "fmlookup \<Delta> x = Some \<theta>"
      from entries[OF this] obtain \<sigma> where \<sigma>: "\<sigma> \<in> set \<sigma>s" and \<theta>: "\<theta> = Ty \<sigma>" by blast
      from \<sigma> obtain i where "i < length \<sigma>s" and "\<sigma> = \<sigma>s ! i" by (auto simp: in_set_conv_nth)
      with assms(4) have "\<turnstile> vs ! i : Ty (inst \<eta> \<sigma>)" by (auto simp: list_all2_conv_all_nth)
      from wf_ty_inst_inv[OF wf_val_ty[OF this]] show "wf_entry \<Sigma> \<theta>" by (simp add: \<theta>)
    qed
  qed
qed

lemma constructor_class_Ok_entry:
  "constructor_class \<Sigma> \<Gamma> e = Some (Ok (C, explicit)) \<Longrightarrow> expr_entry \<Gamma> (node e) = Some (Type C)"
  by (drule constructor_class_Ok) (auto intro: class_of_name_entry)

(* Callee of a call, a class, which is not typed by synthesis or at a scheme *)
lemma class_callee: "\<lbrakk> sound_expr \<rho> (node e) (Val (VClass C)) ; \<eta> \<turnstile> \<rho> : \<Gamma> ; callee \<Sigma> \<Gamma> e es = Ok \<sigma> \<rbrakk> \<Longrightarrow> False"
  using callee_value wf_class_ty by blast

(* Callee of a call evaluating to v: a lambda, a class, or a value at a callable type whose parameter types type
   the arguments and whose result type is below the type of the call *)
lemma call_cases:
  assumes "sound_expr \<rho> (node e) (Val v)" and env: "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and typed: "has_type \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau>"
  obtains (lambda) xs e' where "node e = ExprLambda xs e'"
    | (constructor) C \<tau>' where "v = VClass C" and "lambda_of (node e) = None"
        and "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>'"
    | (callable) \<sigma>s \<tau>' where "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" and "kws = []"
        and "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<sigma>s" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
proof (cases "lambda_of (node e)")
  case (Some xe)
  then obtain xs e' where "node e = ExprLambda xs e'" by (cases "node e") auto
  then show thesis by (rule lambda)
next
  case None
  show thesis
  proof (cases "constructor_class \<Sigma> \<Gamma> e")
    case (Some m)
    from constructor_class_entry[OF this] obtain C where "expr_entry \<Gamma> (node e) = Some (Type C)" by blast
    from sound_expr_class[OF assms(1) env this] have C: "v = VClass C" .
    from typed None show thesis
    proof (cases rule: call_typed)
      case (synth \<tau>')
      from C None synth(1) show thesis by (rule constructor)
    next
      case (stmt \<sigma>)
      from class_callee[OF assms(1)[unfolded C] env stmt(1)] show thesis ..
    qed
  next
    case c: None
    from typed None c
    have "\<exists>\<sigma>s \<tau>'. \<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>')) \<and> check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok () \<and> \<Sigma> \<turnstile> \<tau>' <: \<tau>"
    proof (cases rule: call_typed_callee)
      case (synth \<sigma> \<tau>')
      from synth_call_callable[OF synth(2) callee_value[OF assms(1) env synth(1)]] obtain \<sigma>s \<tau>''
        where v: "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>''))" and "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()"
        and sub: "\<Sigma> \<turnstile> \<tau>'' <: \<tau>'"
        by blast
      moreover have "wf_ty \<Sigma> \<tau>''" using wf_ty_inst_inv[OF wf_val_ty[OF v]] by simp
      moreover have "wf_ty \<Sigma> \<tau>'"
        using synth_wf(5)[OF wf_ty_inst_inv[OF wf_val_ty[OF callee_value[OF assms(1) env synth(1)]]]]
          synth(2)
        by blast
      ultimately show ?thesis using synth(1, 3) by (blast intro: subty_trans[OF wf_class_table])
    next
      case (stmt \<sigma>)
      from check_call_stmt_callable[OF stmt(2) callee_value[OF assms(1) env stmt(1)]] stmt(1) show ?thesis
        unfolding stmt(3) by (blast intro: SubtyObject)
    qed
    then obtain \<sigma>s \<tau>' where v: "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))"
      and args: "check_args \<Sigma> \<Gamma> e kws es \<sigma>s = Ok ()" and sub: "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
      by blast
    have wf: "\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>" using wf_ty_inst_inv[OF wf_val_ty[OF v]] by simp
    show thesis by (rule callable[OF v check_args_typed(1)[OF args wf] check_args_typed(2)[OF args wf] sub])
  qed
qed

(* Soundness of a call whose callee evaluates to a value other than a lambda closure or class, given the typing
   of its result from a callable type typing the callee, with the arguments typed at its parameter types *)
lemma call_callable_exprI:
  assumes eval: "\<rho>, node e \<Rightarrow>\<^sub>e Val v" and callee: "sound_expr \<rho> (node e) (Val v)"
    and "\<And>\<rho>' xs e'. v \<noteq> Lam(\<rho>', xs, e')" and "\<not> is_class v"
    and "\<And>\<eta> \<Gamma> \<sigma>s \<tau>. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; \<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>)) ; list_all2 (has_type_at \<Sigma> \<Gamma>) es \<sigma>s \<rbrakk>
       \<Longrightarrow> result_typed r (inst \<eta> \<tau>)"
  shows "sound_expr \<rho> (ExprCall e (es, [])) r"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<Gamma> (ExprCall e (es, [])) \<tau>"
  from callee env typed show "result_typed r (inst \<eta> \<tau>)"
  proof (cases rule: call_cases)
    case lambda
    with eval assms(3) show ?thesis by (auto elim: LambdaE)
  next
    case constructor
    with assms(4) show ?thesis by simp
  next
    case (callable \<sigma>s \<tau>')
    from assms(5)[OF env callable(1, 3)] callable(4) show ?thesis
      by (rule result_typed_sub[OF _ _ has_type_wf[OF wf_env_wf_cxt[OF env] typed] wf_env_wf_inst[OF env]])
  qed
qed simp

(* Callee value at a callable type, with arguments typed at its parameter types: typed by the rule for its form
   at a callable type whose parameter types type the arguments and whose result type is below *)
lemma callable_args:
  assumes "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>))" and "sound_exprs \<rho> es (Val us)" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<sigma>s"
  obtains \<sigma>s' \<tau>' where "intro_typed v (TyCallable \<sigma>s' \<tau>')" and "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s'"
    and "\<Sigma> \<turnstile> \<tau>' <: inst \<eta> \<tau>"
proof -
  from assms(1) obtain \<sigma>s' \<tau>' where intro: "intro_typed v (TyCallable \<sigma>s' \<tau>')"
    and sub: "\<Sigma> \<turnstile> map (inst \<eta>) \<sigma>s [<:] \<sigma>s'" and ret: "\<Sigma> \<turnstile> \<tau>' <: inst \<eta> \<tau>"
    by (auto elim: wf_callable)
  from sound_exprs_typed[OF assms(2-4)] have args: "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us (map (inst \<eta>) \<sigma>s)"
    by (simp add: list.rel_map)
  have wf: "\<forall>\<sigma> \<in> set \<sigma>s'. wf_ty \<Sigma> \<sigma>" using wf_val_ty[OF intro_typed_wf[OF intro]] by simp
  have "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s'"
  proof (rule list_all2_all_nthI)
    show len: "length us = length \<sigma>s'"
      using list_all2_lengthD[OF args] list_all2_lengthD[OF sub[unfolded subtys_list_all2]] by simp
    fix i
    assume i: "i < length us"
    with args sub have "\<turnstile> us ! i : Ty (map (inst \<eta>) \<sigma>s ! i)" and "\<Sigma> \<turnstile> map (inst \<eta>) \<sigma>s ! i <: \<sigma>s' ! i"
      by (auto simp: list_all2_conv_all_nth subtys_list_all2)
    moreover have "wf_ty \<Sigma> (\<sigma>s' ! i)" using wf i len by simp
    ultimately show "\<turnstile> us ! i : Ty (\<sigma>s' ! i)" by (rule ValSub)
  qed
  with intro ret that show thesis by blast
qed

lemma call_nonfun_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val v" and "sound_expr \<rho> (node e) (Val v)" and "\<not> is_closure v" and "\<not> is_prim v"
    and "\<not> is_class v"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (Aborts TypeError)"
proof (rule call_callable_exprI[OF assms(1, 2) _ assms(5)])
  fix \<rho>' xs e'
  show "v \<noteq> Lam(\<rho>', xs, e')" using assms(3) by auto
next
  fix \<eta> \<Gamma> \<sigma>s \<tau>
  assume "\<turnstile> v : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>))"
  then obtain \<sigma>s' \<tau>' where "intro_typed v (TyCallable \<sigma>s' \<tau>')" by (auto elim: wf_callable)
  with assms(3, 4) show "result_typed (Aborts TypeError) (inst \<eta> \<tau>)" by (auto dest: intro_callable_value)
qed

(* Call of a lambda written as the callee, with its arguments typed by synthesis and its body typed under
   them *)
lemma call_lambda_typed:
  assumes "has_type \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau>" and "lambda_of (node e) = Some (xs, e')"
  obtains \<tau>s \<Delta> \<tau>' where "kws = []" and "length xs = length es"
    and "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
    and "params_cxt xs \<tau>s = Ok \<Delta>" and "has_type_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
proof -
  note result = that
  let ?args = "lambda_args e xs kws es (map (synth_expr_at \<Sigma> \<Gamma>) es)"
  have args: "kws = [] \<and> length xs = length es \<and> (\<exists>\<tau>s. those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s
    \<and> params_cxt xs \<tau>s = Ok \<Delta>)" if "?args = Ok \<Delta>" for \<Delta>
    using that by (auto simp: lambda_args_def bind_sum_def ensure_def split: sum.splits if_splits)
  have synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) =
    by_rule RuleCallLambdaSyn (do { \<Delta> \<leftarrow> ?args; synth_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' })"
    using assms(2) by simp
  have check': "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> =
    Some (by_rule RuleCallLambda (do { \<Delta> \<leftarrow> ?args; check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau> }))"
    using assms(2) by simp
  have body: thesis if "?args = Ok \<Delta>" and "has_type_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>" for \<Delta> \<tau>'
    using args[OF that(1)] that(2, 3) by (elim conjE exE) (rule result; assumption)
  have from_synth: thesis if "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>'" and "\<Sigma> \<turnstile> \<tau>' <: \<tau>" for \<tau>'
    using that(1) unfolding synth
    by (auto simp: bind_sum_def split: sum.splits intro: body[OF _ has_type_synth_at that(2)])
  from assms(1) consider (s) "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>"
    | (c) "check_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = Ok ()" and "wf_ty \<Sigma> \<tau>"
    | (stmt) "call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws))"
    unfolding has_type_def by blast
  then show thesis
  proof cases
    case s
    then show thesis by (rule from_synth) (rule SubtyRefl)
  next
    case c
    from check_expr_cases[OF c(1)] show thesis
    proof
      assume "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = Some (Ok ())"
      with check' obtain \<Delta> where "?args = Ok \<Delta>" and "check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau> = Ok ()"
        by (auto simp: bind_sum_def split: sum.splits)
      with c(2) show thesis by (auto intro: body has_type_check_at SubtyRefl)
    next
      assume "\<exists>\<sigma>. synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>"
      then show thesis by (blast intro: from_synth)
    qed
  next
    case stmt
    with assms(2) show thesis by simp
  qed
qed

lemma intro_lambda:
  "intro_typed Lam(\<rho>, xs, e) (TyCallable \<sigma>s \<tau>) \<Longrightarrow>
   \<exists>\<eta> \<Gamma> \<sigma>s' \<tau>' \<Delta>. \<eta> \<turnstile> \<rho> : \<Gamma> \<and> length xs = length \<sigma>s' \<and> params_cxt xs \<sigma>s' = Ok \<Delta>
     \<and> check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau>' = Ok () \<and> wf_ty \<Sigma> (TyCallable \<sigma>s' \<tau>')
     \<and> \<sigma>s = map (inst \<eta>) \<sigma>s' \<and> \<tau> = inst \<eta> \<tau>'"
  by auto

lemma call_lambda_arity_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')" and "sound_expr \<rho> (node e) (Val Lam(\<rho>', xs, e'))"
    and "sound_exprs \<rho> es (Val us)" and "length xs \<noteq> length us"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (Aborts TypeError)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<Gamma> (ExprCall e (es, [])) \<tau>"
  from assms(2) env typed show "result_typed (Aborts TypeError) (inst \<eta> \<tau>)"
  proof (cases rule: call_cases)
    case (lambda xs0 e0)
    then have "lambda_of (node e) = Some (xs0, e0)" by simp
    from typed this obtain \<tau>s where "length xs0 = length es"
      and \<tau>s: "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
      by (rule call_lambda_typed)
    moreover from assms(1) lambda have "xs = xs0" by (auto elim: LambdaE)
    moreover from those_sum_map_Ok[OF \<tau>s] have "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s"
      by (rule list.rel_mono_strong) (auto intro: has_type_synth_at)
    from sound_exprs_typed[OF assms(3) env this] have "length us = length \<tau>s" by (rule list_all2_lengthD)
    moreover have "length \<tau>s = length es" using list_all2_lengthD[OF those_sum_map_Ok[OF \<tau>s]] by simp
    ultimately show ?thesis using assms(4) by simp
  next
    case constructor
    then show ?thesis by simp
  next
    case (callable \<sigma>s \<tau>')
    from callable(1) assms(3) env callable(3) obtain \<sigma>s' \<tau>''
      where "intro_typed Lam(\<rho>', xs, e') (TyCallable \<sigma>s' \<tau>'')" and "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s'"
      by (rule callable_args)
    with intro_lambda[OF this(1)] assms(4) show ?thesis by (auto dest: list_all2_lengthD)
  qed
qed simp

lemma call_lambda_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')" and "sound_expr \<rho> (node e) (Val Lam(\<rho>', xs, e'))"
    and "sound_exprs \<rho> es (Val us)" and "length xs = length us"
    and body: "sound_expr (\<rho>' \<otimes> fmap_of_list (zip xs us)) (node e') r"
  shows "sound_expr \<rho> (ExprCall e (es, [])) r"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<Gamma> (ExprCall e (es, [])) \<tau>"
  (* Call through a callee typed at a callable type *)
  have call: "result_typed r (inst \<eta> \<tau>')"
    if "\<turnstile> Lam(\<rho>', xs, e') : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>'))" and "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<sigma>s"
    for \<sigma>s \<tau>'
  proof -
    from that(1) assms(3) env that(2) obtain \<sigma>s' \<tau>''
      where "intro_typed Lam(\<rho>', xs, e') (TyCallable \<sigma>s' \<tau>'')" and us: "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s'"
      and ret: "\<Sigma> \<turnstile> \<tau>'' <: inst \<eta> \<tau>'"
      by (rule callable_args)
    from intro_lambda[OF this(1)] obtain \<eta>' \<Gamma>' \<sigma>s'' \<tau>b \<Delta> where env': "\<eta>' \<turnstile> \<rho>' : \<Gamma>'"
      and len: "length xs = length \<sigma>s''" and \<Delta>: "params_cxt xs \<sigma>s'' = Ok \<Delta>"
      and checked: "check_expr_at \<Sigma> (\<Gamma>' \<otimes> \<Delta>) e' \<tau>b = Ok ()" and wf: "wf_ty \<Sigma> (TyCallable \<sigma>s'' \<tau>b)"
      and \<sigma>s': "\<sigma>s' = map (inst \<eta>') \<sigma>s''" and \<tau>'': "\<tau>'' = inst \<eta>' \<tau>b"
      by blast
    from us have "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty (inst \<eta>' \<sigma>)) us \<sigma>s''" by (simp add: \<sigma>s' list.rel_map)
    then have "\<eta>' \<turnstile> \<rho>' \<otimes> fmap_of_list (zip xs us) : \<Gamma>' \<otimes> \<Delta>" by (rule wf_env_params[OF env' \<Delta> len])
    moreover from checked wf have "has_type_at \<Sigma> (\<Gamma>' \<otimes> \<Delta>) e' \<tau>b" by (auto intro: has_type_check_at)
    ultimately have "result_typed r (inst \<eta>' \<tau>b)" using body by (auto dest: sound_expr_has_type_at)
    moreover have "wf_ty \<Sigma> (inst \<eta> \<tau>')" using wf_val_ty[OF that(1)] by simp
    ultimately show ?thesis using ret \<tau>'' by (cases r) (auto intro: ValSub)
  qed
  from assms(2) env typed show "result_typed r (inst \<eta> \<tau>)"
  proof (cases rule: call_cases)
    case (lambda xs0 e0)
    then have lam: "lambda_of (node e) = Some (xs0, e0)" by simp
    from assms(1) lambda have \<rho>': "\<rho>' = \<rho>" and xs: "xs = xs0" and e': "e' = e0" by (auto elim: LambdaE)
    from typed lam obtain \<tau>s \<Delta> \<tau>' where "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s"
      and \<Delta>: "params_cxt xs0 \<tau>s = Ok \<Delta>" and body_typed: "has_type_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e0 \<tau>'"
      and sub: "\<Sigma> \<turnstile> \<tau>' <: \<tau>"
      by (rule call_lambda_typed)
    from those_sum_map_Ok[OF this(1)] have synths: "list_all2 (\<lambda>e \<tau>. synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau>) es \<tau>s" .
    then have "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s"
      by (rule list.rel_mono_strong) (auto intro: has_type_synth_at)
    from sound_exprs_typed[OF assms(3) env this] have us: "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty (inst \<eta> \<tau>)) us \<tau>s" .
    have "length xs0 = length \<tau>s" using assms(4) us xs by (auto dest: list_all2_lengthD)
    then have "\<eta> \<turnstile> \<rho> \<otimes> fmap_of_list (zip xs0 us) : \<Gamma> \<otimes> \<Delta>" using wf_env_params[OF env \<Delta> _ us] by blast
    with body body_typed \<rho>' xs e' have "result_typed r (inst \<eta> \<tau>')" by (auto dest: sound_expr_has_type_at)
    then show ?thesis
      using sub
      by (rule result_typed_sub[OF _ _ has_type_wf[OF wf_env_wf_cxt[OF env] typed] wf_env_wf_inst[OF env]])
  next
    case constructor
    then show ?thesis by simp
  next
    case (callable \<sigma>s \<tau>')
    from call[OF callable(1, 3)] callable(4) show ?thesis
      by (rule result_typed_sub[OF _ _ has_type_wf[OF wf_env_wf_cxt[OF env] typed] wf_env_wf_inst[OF env]])
  qed
qed simp

(* Meaning of a primitive function at arguments typed by its parameter types *)
lemma prim_meaning_typed:
  assumes "intro_typed (VPrim f) (TyCallable \<sigma>s \<tau>)" and "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s"
  shows "result_typed (prim_meaning f us) \<tau>"
proof -
  from assms(1) obtain \<A> q \<rho> x \<Gamma> where "fmlookup (\<E> \<A>) q = Some \<rho>" and "fmlookup \<rho> x = Some (VPrim f)"
    and "fmlookup \<P> q = Some \<Gamma>" and "fmlookup \<Gamma> x = Some (Ty (TyCallable \<sigma>s \<tau>))"
    by auto
  from prim_entry_types[OF this] consider
      (len) "f = PrimLen" "\<sigma>s = [TyPrim Sized]" "\<tau> = TyPrim int"
    | (round) "f = PrimRound" "\<sigma>s = [TyPrim float]" "\<tau> = TyPrim int"
    | (exit) "f = PrimExit" "\<sigma>s = [TyPrim int]" "\<tau> = TyPrim Never"
    by auto
  then show ?thesis
  proof cases
    case len
    with assms(2) obtain u where us: "us = [u]" and "\<turnstile> u : Ty (TyPrim Sized)" by (auto simp: list_all2_Cons2)
    from iter_sized[OF this(2) SubtyRefl] obtain vs where "iter u = Some vs" by auto
    with us len show ?thesis by (simp add: wf_int_lit)
  next
    case round
    with assms(2) obtain u where us: "us = [u]" and u: "\<turnstile> u : Ty (TyPrim float)" by (auto simp: list_all2_Cons2)
    from u obtain l where "u = VLit l" and "prim_subtype float (TyLiteral l)"
      by (rule wf_prim_lit[OF _ SubtyRefl]) simp
    with us round show ?thesis
      by (cases l) (auto simp: wf_int_lit split: option.splits ereal.splits)
  next
    case exit
    with assms(2) obtain u where us: "us = [u]" and u: "\<turnstile> u : Ty (TyPrim int)" by (auto simp: list_all2_Cons2)
    from wf_int[OF u SubtyRefl] us exit show ?thesis by auto
  qed
qed

lemma call_prim_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val (VPrim f)" and "sound_expr \<rho> (node e) (Val (VPrim f))"
    and "sound_exprs \<rho> es (Val us)"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (prim_meaning f us)"
proof (rule call_callable_exprI[OF assms(1, 2)])
  fix \<eta> \<Gamma> \<sigma>s \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<turnstile> VPrim f : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>))" and "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<sigma>s"
  from this(2) assms(3) this(1, 3) obtain \<sigma>s' \<tau>' where intro: "intro_typed (VPrim f) (TyCallable \<sigma>s' \<tau>')"
    and us: "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s'" and ret: "\<Sigma> \<turnstile> \<tau>' <: inst \<eta> \<tau>"
    by (rule callable_args)
  have "wf_ty \<Sigma> (inst \<eta> \<tau>)" using wf_val_ty[OF \<open>\<turnstile> VPrim f : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>))\<close>] by simp
  with prim_meaning_typed[OF intro us] ret show "result_typed (prim_meaning f us) (inst \<eta> \<tau>)"
    by (cases "prim_meaning f us") (auto intro: ValSub)
qed simp_all

lemma call_def_arity_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val Def(\<rho>', ds, j)" and "sound_expr \<rho> (node e) (Val Def(\<rho>', ds, j))"
    and "node (ds ! j) = Def f \<alpha>s xps \<psi> s" and "sound_exprs \<rho> es (Val us)" and "length xps \<noteq> length us"
    and "j < length ds"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (Aborts TypeError)"
proof (rule call_callable_exprI[OF assms(1, 2)])
  fix \<eta> \<Gamma> \<sigma>s \<tau>
  assume "\<eta> \<turnstile> \<rho> : \<Gamma>" and "\<turnstile> Def(\<rho>', ds, j) : Ty (inst \<eta> (TyCallable \<sigma>s \<tau>))"
    and "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<sigma>s"
  from this(2) assms(4) this(1, 3) obtain \<sigma>s' \<tau>' where intro: "intro_typed Def(\<rho>', ds, j) (TyCallable \<sigma>s' \<tau>')"
    and us: "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty \<sigma>) us \<sigma>s'"
    by (rule callable_args)
  from intro obtain \<Gamma>' \<pi>s \<alpha>s' \<sigma>sD \<tau>D \<tau>s where
    sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma>' (node d))) ds) = Ok \<pi>s"
    and \<pi>: "\<pi>s ! j = TyScheme \<alpha>s' (TyCallable \<sigma>sD \<tau>D)" and "length \<sigma>s' = length \<sigma>sD"
    by auto
  with def_signatures_arity[OF sigs assms(6, 3) \<pi>] list_all2_lengthD[OF us] assms(5)
  show "result_typed (Aborts TypeError) (inst \<eta> \<tau>)" by simp
qed simp_all

lemma call_fail_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa>" and "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprCall e (es, kws)) (Aborts \<kappa>)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau>"
  from call_callee_typed[OF typed] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)"
  proof (elim disjE exE)
    fix xs e'
    assume "lambda_of (node e) = Some (xs, e')"
    then have "node e = ExprLambda xs e'" by (cases "node e") simp_all
    with assms(1) show ?thesis by (auto elim: LambdaE)
  next
    fix C
    assume "expr_entry \<Gamma> (node e) = Some (Type C)"
    from sound_expr_name[OF assms(2) env this] show ?thesis by simp
  next
    fix \<sigma>
    assume "callee \<Sigma> \<Gamma> e es = Ok \<sigma>"
    from callee_entry[OF this] show ?thesis
      by (auto dest: sound_expr_name[OF assms(2) env] sound_expr_synth_at[OF assms(2) env])
  qed
qed simp

(* Type arguments of a constructor call, supplied by the callee or inferred from the arguments, over the type
   variables bound by \<eta> *)
lemma constr_type_args:
  assumes env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and cc: "constructor_class \<Sigma> \<Gamma> e = Some (Ok (C, explicit))"
    and "explicit = Some \<tau>s \<or> explicit = None
      \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C) \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
  shows "length \<tau>s = length (type_params \<Sigma> C) \<and> (\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>)"
  using assms(3)
proof
  assume "explicit = Some \<tau>s"
  with constructor_class_Ok[OF cc] obtain \<psi> where "resolve_type \<Sigma> \<Gamma> \<psi> = Ok (TyClass C \<tau>s)"
    and len: "length \<tau>s = length (type_params \<Sigma> C)"
    by auto
  from resolve_type_wf[OF wf_env_wf_cxt[OF env] this(1)] len show ?thesis by auto
next
  assume "explicit = None
    \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C) \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
  then have inferred: "inferred_type_args \<Sigma> (type_params \<Sigma> C) \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
    by blast
  have "wf_ty \<Sigma> \<tau>'" if "Ok \<tau>' \<in> set (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es)" for \<tau>'
  proof -
    from that obtain e' where "synth_expr_at \<Sigma> \<Gamma> e' = Ok \<tau>'" by auto
    with synth_at_wf_ty[OF wf_env_wf_cxt[OF env]] show ?thesis by blast
  qed
  with inferred_type_args_length[OF inferred] inferred_type_args_fv[OF inferred, of UNIV] show ?thesis by blast
qed

(* Typing by synthesis of a call of the constructor of class C, at C and type arguments over the type variables
   bound by \<eta>, with each argument typed at the type of its field *)
lemma constr_call_typed:
  assumes callee: "sound_expr \<rho> (node e) (Val (VClass C))" and env: "\<eta> \<turnstile> \<rho> : \<Gamma>"
    and synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>" and nolam: "lambda_of (node e) = None"
  obtains x\<sigma>s \<sigma>es \<tau>s where "C |\<in>| fmdom \<Sigma>" and "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    and "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and "list_all2 (has_type_at \<Sigma> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
    and "\<tau> = TyClass C \<tau>s" and "length \<tau>s = length (type_params \<Sigma> C)" and "\<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>'"
proof (cases "constructor_class \<Sigma> \<Gamma> e")
  case None
  with synth nolam obtain \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" by (auto simp: bind_sum_def split: sum.splits)
  from class_callee[OF callee env this] show thesis ..
next
  case (Some m)
  from synth nolam this obtain C' explicit x\<sigma>s \<sigma>es \<tau>s where m: "m = Ok (C', explicit)"
    and fields: "fields \<Sigma> C' = FieldScheme (type_params \<Sigma> C') x\<sigma>s"
    and args: "constructor_args C' (FieldScheme (type_params \<Sigma> C') x\<sigma>s) es kws = Ok \<sigma>es"
    and checked: "\<forall>(\<sigma>, e') \<in> set \<sigma>es. check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s (type_params \<Sigma> C') \<sigma>) = Ok ()"
    and \<tau>: "\<tau> = TyClass C' \<tau>s"
    and \<tau>s: "explicit = Some \<tau>s \<or> explicit = None
      \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C') (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
    by (rule constr_synth)
  from Some m have cc: "constructor_class \<Sigma> \<Gamma> e = Some (Ok (C', explicit))" by simp
  from sound_expr_class[OF callee env constructor_class_Ok_entry[OF cc]] have C': "C' = C" by simp
  from sound_expr_name[OF callee env constructor_class_Ok_entry[OF cc]] have "\<turnstile> VClass C : Type C'" by simp
  then have dom: "C |\<in>| fmdom \<Sigma>" using C' by (auto dest: wf_class_dom)
  from constr_type_args[OF env cc \<tau>s] C' have len: "length \<tau>s = length (type_params \<Sigma> C)"
    and wf: "\<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>'"
    by simp_all
  note fields = fields[unfolded C'] and args = args[unfolded C'] and checked = checked[unfolded C']
    and \<tau> = \<tau>[unfolded C']
  have wf_field: "wf_ty \<Sigma> \<sigma>" if "\<sigma> \<in> snd ` set x\<sigma>s" for \<sigma>
  proof -
    from that obtain x where x: "(x, \<sigma>) \<in> set x\<sigma>s" by auto
    have "wf_ty \<Sigma> (TyClass C (map TyVar (type_params \<Sigma> C)))" using dom by simp
    from fields_wf[OF wf_class_table this] x fields show ?thesis by simp
  qed
  have "list_all2 (has_type_at \<Sigma> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
    unfolding list_all2_map1 list_all2_map2
  proof (rule list.rel_refl_strong)
    fix z
    assume z: "z \<in> set \<sigma>es"
    obtain \<sigma> e' where z': "z = (\<sigma>, e')" by (cases z)
    from constructor_args_field[OF args z[unfolded z']] have \<sigma>: "\<sigma> \<in> snd ` set x\<sigma>s" .
    have "wf_ty \<Sigma> (subst \<tau>s (type_params \<Sigma> C) \<sigma>)" using wf_field[OF \<sigma>] wf by (rule wf_ty_subst)
    then show "has_type_at \<Sigma> \<Gamma> (snd z) ((subst \<tau>s (type_params \<Sigma> C) \<circ> fst) z)"
      using checked z z' by (auto intro: has_type_check_at)
  qed
  then show thesis by (rule that[OF dom fields args _ \<tau> len wf])
qed

lemma call_fail_args_sound:
  assumes callee: "sound_expr \<rho> (node e) (Val v)" and args: "sound_exprs \<rho> es (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprCall e (es, [])) (Aborts \<kappa>)"
  unfolding sound_expr_def
proof (intro conjI allI impI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and typed: "has_type \<Sigma> \<Gamma> (ExprCall e (es, [])) \<tau>"
  from callee env typed have "\<exists>\<tau>s. list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s"
  proof (cases rule: call_cases)
    case (lambda xs e')
    then have "lambda_of (node e) = Some (xs, e')" by simp
    with typed obtain \<tau>s where "those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es) = Ok \<tau>s" by (rule call_lambda_typed)
    from those_sum_map_Ok[OF this] show ?thesis by (blast intro: list.rel_mono_strong has_type_synth_at)
  next
    case (constructor C \<tau>')
    with callee have cls: "sound_expr \<rho> (node e) (Val (VClass C))" by simp
    obtain x\<sigma>s \<sigma>es \<tau>s where "C |\<in>| fmdom \<Sigma>"
      and "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
      and args: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es [] = Ok \<sigma>es"
      and "list_all2 (has_type_at \<Sigma> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
      and "\<tau>' = TyClass C \<tau>s" and "length \<tau>s = length (type_params \<Sigma> C)"
      and "\<forall>\<tau>'' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>''"
      by (rule constr_call_typed[OF cls env constructor(3, 2)])
    with constructor_args_exprs(1)[OF args] show ?thesis by auto
  next
    case callable
    then show ?thesis by blast
  qed
  then obtain \<tau>s where "list_all2 (has_type_at \<Sigma> \<Gamma>) es \<tau>s" by blast
  from sound_exprs_abort[OF args env this] show "result_typed (Aborts \<kappa>) (inst \<eta> \<tau>)" by simp
qed simp

(* Soundness of a constructor call, given the typing of its result from the typing of the call by synthesis at
   the class and type arguments typing the fields *)
lemma constr_exprI:
  assumes eval: "\<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C)" and callee: "sound_expr \<rho> (node e) (Val (VClass C))"
    and "\<And>\<eta> \<Gamma> x\<sigma>s \<sigma>es \<tau>s. \<lbrakk> \<eta> \<turnstile> \<rho> : \<Gamma> ; C |\<in>| fmdom \<Sigma> ; fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s
       ; constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es
       ; list_all2 (has_type_at \<Sigma> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)
       ; length \<tau>s = length (type_params \<Sigma> C) ; \<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>' \<rbrakk>
       \<Longrightarrow> result_typed r (inst \<eta> (TyClass C \<tau>s))"
  shows "sound_expr \<rho> (ExprCall e (es, kws)) r"
proof (rule sound_exprI)
  fix \<eta> \<Gamma> \<tau>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and synth: "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>"
  show "result_typed r (inst \<eta> \<tau>)"
  proof (rule constr_call_typed[OF callee env synth class_callee_lambda[OF eval]])
    fix x\<sigma>s \<sigma>es \<tau>s
    assume "C |\<in>| fmdom \<Sigma>" and "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
      and "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
      and "list_all2 (has_type_at \<Sigma> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
      and "\<tau> = TyClass C \<tau>s" and "length \<tau>s = length (type_params \<Sigma> C)" and "\<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>'"
    from assms(3)[OF env this(1-4, 6, 7)] this(5) show "result_typed r (inst \<eta> \<tau>)" by simp
  qed
next
  fix \<eta> \<Gamma> \<tau>
  assume "check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> = Some (Ok ())"
  with class_callee_lambda[OF eval] show "result_typed r (inst \<eta> \<tau>)" by simp
next
  fix \<eta> \<Gamma>
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and "call_stmt \<Sigma> \<Gamma> (ExprCall e (es, kws))"
  then obtain \<sigma> where "callee \<Sigma> \<Gamma> e es = Ok \<sigma>" by auto
  from class_callee[OF callee env this] show "result_typed r (inst \<eta> (TyPrim object))" ..
qed simp

lemma constr_sound:
  assumes eval: "\<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C)" and callee: "sound_expr \<rho> (node e) (Val (VClass C))"
    and args: "sound_exprs \<rho> (es @ map snd kws) (Val us)"
    and xus: "field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) = Some xus"
  shows "sound_expr \<rho> (ExprCall e (es, kws)) (Val (VObject C xus))"
proof (rule constr_exprI[OF eval callee])
  fix \<eta> \<Gamma> x\<sigma>s \<sigma>es \<tau>s
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and dom: "C |\<in>| fmdom \<Sigma>"
    and fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    and cargs: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and typed: "list_all2 (has_type_at \<Sigma> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
    and len: "length \<tau>s = length (type_params \<Sigma> C)" and wf: "\<forall>\<tau>' \<in> set \<tau>s. wf_ty \<Sigma> \<tau>'"
  let ?\<alpha>s = "type_params \<Sigma> C" and ?n = "length es" and ?xs = "map fst x\<sigma>s"
  let ?R = "\<lambda>v \<sigma>. \<turnstile> v : Ty (inst \<eta> (subst \<tau>s ?\<alpha>s \<sigma>))"
  have names: "field_names \<Sigma> C = ?xs" using fields by (simp add: field_names_def)
  note n_kws = constructor_args_Ok(1, 2)[OF cargs]
  from sound_exprs_typed[OF args env typed[unfolded constructor_args_exprs(1)[OF cargs]]]
  have "list_all2 ?R us (map fst \<sigma>es)" by (simp add: list_all2_map2)
  then have rel: "list_all2 ?R us (map snd (take ?n x\<sigma>s) @ map (\<lambda>(y, _). the (map_of x\<sigma>s y)) kws)"
    by (simp only: constructor_args_exprs(2)[OF cargs])
  have dist: "distinct ?xs" using wf_class_table_distinct[OF wf_class_table dom] names by simp
  have len_us: "length us = ?n + length kws" using rel n_kws(1) by (auto dest: list_all2_lengthD)
  have xus': "xus = zip (take ?n ?xs) (take ?n us)
    @ map (\<lambda>y. (y, the (map_of (zip (map fst kws) (drop ?n us)) y))) (drop ?n ?xs)"
    using xus names len_us by (simp add: field_map_def Let_def min_def split: if_splits)
  from field_values_rel[OF dist n_kws rel] len_us n_kws(1)
  have rel': "list_all2 ?R (map snd xus) (map snd x\<sigma>s)" by (simp add: xus' comp_def min_def)
  have eq: "inst \<eta> (subst \<tau>s ?\<alpha>s \<sigma>) = subst (map (inst \<eta>) \<tau>s) ?\<alpha>s \<sigma>" if "\<sigma> \<in> set (map snd x\<sigma>s)" for \<sigma>
  proof -
    from that obtain x where x: "(x, \<sigma>) \<in> set x\<sigma>s" by auto
    have "\<forall>(x, \<sigma>) \<in> set x\<sigma>s. fv \<sigma> \<subseteq> set ?\<alpha>s" using fields_fv[OF wf_class_table dom] fields by simp
    from bspec[OF this x] have "fv \<sigma> \<subseteq> set ?\<alpha>s" by simp
    then show ?thesis by (rule inst_subst_closed[OF wf_env_wf_inst[OF env] len])
  qed
  have "list_all2 (\<lambda>v \<sigma>. \<turnstile> v : Ty (subst (map (inst \<eta>) \<tau>s) ?\<alpha>s \<sigma>)) (map snd xus) (map snd x\<sigma>s)"
  proof (rule list.rel_mono_strong[OF rel'])
    fix v \<sigma>
    assume "v \<in> set (map snd xus)" and "\<sigma> \<in> set (map snd x\<sigma>s)" and "?R v \<sigma>"
    with eq show "\<turnstile> v : Ty (subst (map (inst \<eta>) \<tau>s) ?\<alpha>s \<sigma>)" by simp
  qed
  then have "list_all2 (\<lambda>v \<tau>. \<turnstile> v : Ty \<tau>) (map snd xus) (field_types \<Sigma> C (map (inst \<eta>) \<tau>s))"
    by (simp add: field_types_def fields split_def list_all2_map2)
  moreover have "map fst xus = field_names \<Sigma> C" using len_us n_kws(1) by (simp add: xus' names min_def comp_def)
  moreover have "wf_ty \<Sigma> (TyClass C (map (inst \<eta>) \<tau>s))"
    using dom len wf wf_env_wf_inst[OF env] by (auto intro: inst_wf)
  ultimately have "\<turnstile> VObject C xus : Ty (TyClass C (map (inst \<eta>) \<tau>s))" by (blast intro: ValObj)
  then show "result_typed (Val (VObject C xus)) (inst \<eta> (TyClass C \<tau>s))" by simp
qed

lemma constr_arity_sound:
  assumes eval: "\<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C)" and callee: "sound_expr \<rho> (node e) (Val (VClass C))"
    and args: "sound_exprs \<rho> (es @ map snd kws) (Val us)"
    and none: "field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) = None"
  shows "sound_expr \<rho> (ExprCall e (es, kws)) (Aborts TypeError)"
proof (rule constr_exprI[OF eval callee])
  fix \<eta> \<Gamma> x\<sigma>s \<sigma>es \<tau>s
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    and cargs: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and typed: "list_all2 (has_type_at \<Sigma> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
  have names: "field_names \<Sigma> C = map fst x\<sigma>s" using fields by (simp add: field_names_def)
  note n_kws = constructor_args_Ok(1, 2)[OF cargs]
  have "length \<sigma>es = length es + length kws"
    using arg_cong[OF constructor_args_exprs(1)[OF cargs], of length] by simp
  with sound_exprs_typed[OF args env typed[unfolded constructor_args_exprs(1)[OF cargs]]]
  have "length us = length es + length kws" by (auto dest: list_all2_lengthD)
  with none n_kws names show "result_typed (Aborts TypeError) (inst \<eta> (TyClass C \<tau>s))"
    by (simp add: field_map_def Let_def min_def split: if_splits)
qed

lemma constr_fail_sound:
  assumes eval: "\<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C)" and callee: "sound_expr \<rho> (node e) (Val (VClass C))"
    and args: "sound_exprs \<rho> (es @ map snd kws) (Aborts \<kappa>)"
  shows "sound_expr \<rho> (ExprCall e (es, kws)) (Aborts \<kappa>)"
proof (rule constr_exprI[OF eval callee])
  fix \<eta> \<Gamma> x\<sigma>s \<sigma>es \<tau>s
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and cargs: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and typed: "list_all2 (has_type_at \<Sigma> \<Gamma>) (map snd \<sigma>es) (map (subst \<tau>s (type_params \<Sigma> C) \<circ> fst) \<sigma>es)"
  from sound_exprs_abort[OF args env typed[unfolded constructor_args_exprs(1)[OF cargs]]]
  show "result_typed (Aborts \<kappa>) (inst \<eta> (TyClass C \<tau>s))" by simp
qed

end

end
