(* Static outcomes; typing of expressions, statements and type definitions *)
theory Typing
  imports Operators Matching
begin

(* Type at which a variable is bound or declared *)
fun var_ty :: "cxt_entry \<Rightarrow> ty option"
where
"var_ty (Ty \<tau>) = Some \<tau>" |
"var_ty (DU \<tau>) = Some \<tau>" |
"var_ty (PU \<tau> _) = Some \<tau>" |
"var_ty _ = None"

lemma var_ty_Some: "var_ty \<theta> = Some \<sigma> \<Longrightarrow> \<theta> = Ty \<sigma> \<or> \<theta> = DU \<sigma> \<or> (\<exists>b. \<theta> = PU \<sigma> b)"
  by (cases \<theta>) simp_all

(* Type scheme at which a variable is bound or declared *)
fun scheme_of :: "cxt_entry \<Rightarrow> ty_scheme option"
where
"scheme_of (Scheme \<pi>) = Some \<pi>" |
"scheme_of (PUScheme \<pi> _) = Some \<pi>" |
"scheme_of _ = None"

lemma scheme_of_Some: "scheme_of \<theta> = Some \<pi> \<Longrightarrow> \<theta> = Scheme \<pi> \<or> (\<exists>b. \<theta> = PUScheme \<pi> b)"
  by (cases \<theta>) simp_all

(* Merge of the entry of a variable with undefined, recording whether the variable is declared in a branch;
   no merge for other entries *)
fun possibly_unassigned :: "bool \<Rightarrow> cxt_entry \<Rightarrow> cxt_entry option"
where
"possibly_unassigned b (Ty \<tau>) = Some (PU \<tau> b)" |
"possibly_unassigned b (DU \<tau>) = Some (PU \<tau> b)" |
"possibly_unassigned b (PU \<tau> _) = Some (PU \<tau> b)" |
"possibly_unassigned b (Scheme \<pi>) = Some (PUScheme \<pi> b)" |
"possibly_unassigned b (PUScheme \<pi> _) = Some (PUScheme \<pi> b)" |
"possibly_unassigned _ _ = None"

fun merge_cxt_entry :: "class_table \<Rightarrow> bool \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry option"
where
"merge_cxt_entry \<Sigma> b (Some (Ty \<sigma>)) (Some (Ty \<tau>)) = Some (Ty (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>))" |
"merge_cxt_entry \<Sigma> b (Some \<theta>) (Some \<theta>') =
  (if \<theta> = \<theta>' then Some \<theta>
   else case (scheme_of \<theta>, scheme_of \<theta>', var_ty \<theta>, var_ty \<theta>') of
     (Some \<pi>, Some \<pi>', _, _) \<Rightarrow> if \<pi> = \<pi>' then Some (PUScheme \<pi> b) else None
   | (None, None, Some \<sigma>, Some \<tau>) \<Rightarrow> Some (PU (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>) b)
   | _ \<Rightarrow> None)" |
"merge_cxt_entry \<Sigma> b (Some \<theta>) None = possibly_unassigned b \<theta>" |
"merge_cxt_entry \<Sigma> b None (Some \<theta>) = possibly_unassigned b \<theta>" |
"merge_cxt_entry \<Sigma> b None None = None"

(* Merge of two entries, by its cases *)
lemma merge_cxt_entry_cases:
  assumes "merge_cxt_entry \<Sigma> b (Some \<theta>) (Some \<theta>') = Some \<theta>''"
  shows "(\<exists>\<sigma> \<tau>. \<theta> = Ty \<sigma> \<and> \<theta>' = Ty \<tau> \<and> \<theta>'' = Ty (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)) \<or> \<theta>'' = \<theta> \<and> \<theta>' = \<theta>
    \<or> (\<exists>\<pi>. scheme_of \<theta> = Some \<pi> \<and> scheme_of \<theta>' = Some \<pi> \<and> \<theta>'' = PUScheme \<pi> b)
    \<or> (\<exists>\<sigma> \<tau>. var_ty \<theta> = Some \<sigma> \<and> var_ty \<theta>' = Some \<tau> \<and> \<theta>'' = PU (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>) b)"
  using assms by (cases \<theta>; cases \<theta>'; simp split: if_splits option.splits)

(* Merge of the contexts of two branches of a statement, where X holds the variables declared in any of the
   branches; failure at the first variable with incompatible entries *)
definition merge :: "class_table \<Rightarrow> var set \<Rightarrow> cxt \<Rightarrow> cxt \<Rightarrow> cxt may_fail"
where
"merge \<Sigma> X \<Gamma> \<Gamma>' =
  (let entry = \<lambda>x. merge_cxt_entry \<Sigma> (x \<in> X) (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x);
       Y = ffilter (\<lambda>x. entry x = None) (fmdom (\<Gamma> \<otimes> \<Gamma>')) in
   if Y = {||} then Ok (fmmap_keys (\<lambda>x _. the (entry x)) (\<Gamma> \<otimes> \<Gamma>')) else Fail (Redeclaration (Min (fset Y))))"

lemma merge_dom: "merge \<Sigma> X \<Gamma> \<Gamma>' = Ok \<Gamma>'' \<Longrightarrow> fmdom \<Gamma>'' = fmdom (\<Gamma> \<otimes> \<Gamma>')"
  by (auto simp: merge_def Let_def split: if_splits)

lemma merge_lookup:
  assumes "merge \<Sigma> X \<Gamma> \<Gamma>' = Ok \<Gamma>''" and "x |\<in>| fmdom (\<Gamma> \<otimes> \<Gamma>')"
  shows "fmlookup \<Gamma>'' x = merge_cxt_entry \<Sigma> (x \<in> X) (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x)"
proof -
  let ?entry = "\<lambda>x. merge_cxt_entry \<Sigma> (x \<in> X) (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x)"
  from assms(1) have Y: "ffilter (\<lambda>x. ?entry x = None) (fmdom (\<Gamma> \<otimes> \<Gamma>')) = {||}"
    and \<Gamma>'': "\<Gamma>'' = fmmap_keys (\<lambda>x _. the (?entry x)) (\<Gamma> \<otimes> \<Gamma>')"
    by (auto simp: merge_def Let_def split: if_splits)
  have "x |\<notin>| ffilter (\<lambda>x. ?entry x = None) (fmdom (\<Gamma> \<otimes> \<Gamma>'))" unfolding Y by simp
  with assms(2) have "?entry x \<noteq> None" by (simp only: ffmember_filter) simp
  with assms(2) \<Gamma>'' show ?thesis by (auto simp: fmlookup_dom_iff)
qed

(* Assigns\<^sub>R \<Delta> r: the statement can complete normally, adding bindings \<Delta>. If present, r is the error reported
   when a function body ends with a statement which PurePy determines to return or raise but which mypy treats
   as completing normally. *)
datatype static_outcome = Assigns\<^sub>R cxt "reason option" | Returns\<^sub>R

fun bindings_of :: "static_outcome \<Rightarrow> cxt option"
where
"bindings_of (Assigns\<^sub>R \<Delta> _) = Some \<Delta>" |
"bindings_of Returns\<^sub>R = None"

fun merge_outcome ::
  "class_table \<Rightarrow> var set \<Rightarrow> static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome may_fail"
where
"merge_outcome \<Sigma> X (Assigns\<^sub>R \<Delta> r) (Assigns\<^sub>R \<Delta>' r') =
  do { \<Delta>'' \<leftarrow> merge \<Sigma> X \<Delta> \<Delta>'; Ok (Assigns\<^sub>R \<Delta>'' (if r' = None then None else r)) }" |
"merge_outcome \<Sigma> X R Returns\<^sub>R = Ok R" |
"merge_outcome \<Sigma> X Returns\<^sub>R R = Ok R"

lemma merge_outcome_dom:
  assumes "merge_outcome \<Sigma> X R R' = Ok (Assigns\<^sub>R \<Delta> r)" and "x |\<in>| fmdom \<Delta>"
  shows "(\<exists>\<Delta>' r'. R = Assigns\<^sub>R \<Delta>' r' \<and> x |\<in>| fmdom \<Delta>') \<or> (\<exists>\<Delta>' r'. R' = Assigns\<^sub>R \<Delta>' r' \<and> x |\<in>| fmdom \<Delta>')"
  using assms by (cases "(\<Sigma>, X, R, R')" rule: merge_outcome.cases) (auto simp: bind_sum_Ok dest: merge_dom)

definition merges :: "class_table \<Rightarrow> var set \<Rightarrow> static_outcome may_fail list \<Rightarrow> static_outcome may_fail"
where
"merges \<Sigma> X ms =
  do { Rs \<leftarrow> those_sum ms; foldr (\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }) Rs (Ok Returns\<^sub>R) }"

lemma merges_Ok: "merges \<Sigma> X ms = Ok R \<Longrightarrow> \<exists>Rs. those_sum ms = Ok Rs"
  by (auto simp: merges_def bind_sum_def split: sum.splits)

(* Variable bound by a merge of static outcomes, bound by one of them *)
lemma merges_dom:
  assumes "merges \<Sigma> X ms = Ok (Assigns\<^sub>R \<Delta> r)" and "x |\<in>| fmdom \<Delta>"
  obtains \<Delta>' r' where "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set ms" and "x |\<in>| fmdom \<Delta>'"
proof -
  let ?f = "\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }"
  from assms(1) obtain Rs where Rs: "those_sum ms = Ok Rs"
    and fold: "foldr ?f Rs (Ok Returns\<^sub>R) = Ok (Assigns\<^sub>R \<Delta> r)"
    by (auto simp: merges_def bind_sum_Ok)
  have "\<exists>\<Delta>' r'. Assigns\<^sub>R \<Delta>' r' \<in> set Rs \<and> x |\<in>| fmdom \<Delta>'"
    if "foldr ?f Rs (Ok Returns\<^sub>R) = Ok (Assigns\<^sub>R \<Delta> r)" and "x |\<in>| fmdom \<Delta>" for Rs \<Delta> r
    using that
  proof (induction Rs arbitrary: \<Delta> r)
    case (Cons R Rs)
    from Cons.prems(1) obtain R' where R': "foldr ?f Rs (Ok Returns\<^sub>R) = Ok R'"
      and m: "merge_outcome \<Sigma> X R R' = Ok (Assigns\<^sub>R \<Delta> r)"
      by (auto simp: bind_sum_Ok)
    from merge_outcome_dom[OF m Cons.prems(2)] Cons.IH R' show ?case by (cases R') auto
  qed simp
  from this[OF fold assms(2)] obtain \<Delta>' r' where "Assigns\<^sub>R \<Delta>' r' \<in> set Rs" and x: "x |\<in>| fmdom \<Delta>'" by blast
  then obtain i where i: "i < length Rs" and "Rs ! i = Assigns\<^sub>R \<Delta>' r'" by (auto simp: in_set_conv_nth)
  with those_sum_Ok[OF Rs] have "ms ! i = Ok (Assigns\<^sub>R \<Delta>' r')" and "i < length ms"
    by (auto simp: list_all2_conv_all_nth)
  then have "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set ms" by (metis nth_mem)
  with x that show thesis by blast
qed

fun override_outcome :: "static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome"
where
"override_outcome (Assigns\<^sub>R \<Delta> r) (Assigns\<^sub>R \<Delta>' r') = Assigns\<^sub>R (\<Delta> \<otimes> \<Delta>') (if r = None then r' else None)" |
"override_outcome _ _ = Returns\<^sub>R"

adhoc_overloading override \<rightleftharpoons> override_outcome

definition attr_module :: "name \<Rightarrow> cxt \<Rightarrow> var \<Rightarrow> name \<Rightarrow> ty may_fail"
where
"attr_module q \<Gamma> x q' =
  by_rule RuleAttrModule (case fmlookup \<Gamma> x of
     None \<Rightarrow> Fail (SelectsNoRule JudgementResolveName (UnknownMember x q))
   | Some (Ty \<tau>) \<Rightarrow> Ok \<tau>
   | Some (ModStub q'') \<Rightarrow> Fail (Violates RuleQualified (SubmoduleNotImported q''))
   | Some (ModChecked _ _) \<Rightarrow> Fail (ModuleAsValue q')
   | Some (Type _) \<Rightarrow> Fail (ClassAsValue q')
   | Some (TypeAlias _ _ _ _) \<Rightarrow> Fail (TypeAliasAsValue q')
   | Some PredefName \<Rightarrow> Fail (PredefinedNameAsValue q')
   | Some (Scheme _) \<Rightarrow> Fail (TypeSchemeAsValue q')
   | Some TypeVar \<Rightarrow> undefined
   | Some _ \<Rightarrow> Fail (Violates RuleQualified (UnassignedMember x q)))"

(* Type of attribute x of e when e is a dotted name resolving to a module; None otherwise *)
definition module_attribute :: "cxt \<Rightarrow> expr \<Rightarrow> var \<Rightarrow> ty may_fail option"
where
"module_attribute \<Gamma> e x = do {
   q \<leftarrow> dotted_name e;
   case lookup \<Gamma> q of
     Some (ModChecked q' \<Gamma>') \<Rightarrow> Some (attr_module q' \<Gamma>' x (Qualified q x))
   | Some (ModStub q') \<Rightarrow> Some (Fail (Violates RuleQualified (SubmoduleNotImported q')))
   | _ \<Rightarrow> None
 }"

(* Context binding parameters xs at \<tau>s *)
definition params_cxt :: "var list \<Rightarrow> ty list \<Rightarrow> cxt may_fail"
where
"params_cxt xs \<tau>s = (if distinct xs then Ok (fmap_of_list (zip xs (map Ty \<tau>s))) else Fail undefined)"

(* Failure if one of the variables bound by qualifiers gs, with bindings \<Delta>, is in X, the variables captured by
   lambdas, located at the first generator *)
definition captured :: "qualifier located list \<Rightarrow> var set \<Rightarrow> cxt \<Rightarrow> unit may_fail"
where
"captured gs X \<Delta> =
  (let Y = X \<inter> fset (fmdom \<Delta>) in
   if Y = {} then Ok () else Fail (Located (pos_of (hd gs)) (CapturedGeneratorVariable (Min Y))))"

definition lambda_args ::
  "expr located \<Rightarrow> var list \<Rightarrow> (var \<times> expr located) list \<Rightarrow> expr located list \<Rightarrow> ty may_fail list
   \<Rightarrow> cxt may_fail"
where
"lambda_args e xs kws es \<sigma>s = do {
   ensure (kws = []) KeywordArgumentsNotConstructor;
   ensure (length xs = length es) (CallArityMismatch e (length xs) (length es));
   \<tau>s \<leftarrow> those_sum \<sigma>s;
   params_cxt xs \<tau>s
 }"

(* Check of a name bound at a type scheme against \<tau>; None for other expressions *)
definition var_scheme :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> unit may_fail option"
where
"var_scheme \<Sigma> \<Gamma> e \<tau> =
  (case scheme_of_name \<Gamma> e of
     Some (TyScheme \<alpha>s \<sigma>) \<Rightarrow> Some (by_rule RuleVarScheme (do {
       \<tau>s \<leftarrow> type_args_of (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) \<alpha>s;
       let \<sigma>' = subst \<tau>s \<alpha>s \<sigma>;
       ensure (\<Sigma> \<turnstile> \<sigma>' <: \<tau>) (mismatch \<Sigma> \<tau> \<sigma>')
     }))
   | None \<Rightarrow> None)"

lemma var_scheme_None: "dotted_name e = None \<Longrightarrow> var_scheme \<Sigma> \<Gamma> e \<tau> = None"
  by (simp add: var_scheme_def scheme_of_name_def entry_of_def)

(* Type arguments for \<alpha>s inferred from the arguments that synthesise; failing that, the first failure
   of an argument with a synthesis rule *)
definition inferred_type_args :: "class_table \<Rightarrow> var list \<Rightarrow> ty list \<Rightarrow> ty may_fail list \<Rightarrow> ty list may_fail"
where
"inferred_type_args \<Sigma> \<alpha>s \<sigma>s ms =
  (let \<sigma>\<tau>s = filter (Not \<circ> isl \<circ> snd) (zip \<sigma>s ms) in
   map_sum (\<lambda>r. let r' = synth_failure ms in if unlocated (without_rule r') = NotSynthesised then r else r') id
     (type_args_of (type_args_seq \<Sigma> \<alpha>s (map fst \<sigma>\<tau>s) (map (projr \<circ> snd) \<sigma>\<tau>s)) \<alpha>s))"

lemma inferred_type_args_length: "inferred_type_args \<Sigma> \<alpha>s \<sigma>s ms = Ok \<tau>s \<Longrightarrow> length \<tau>s = length \<alpha>s"
  by (auto simp: inferred_type_args_def Let_def dest!: type_args_of_length)

(* Operator resolution extended by elimination of a union among the operand types, left first *)
fun resolve_binop_union :: "class_table \<Rightarrow> bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty option"
where
"resolve_binop_union \<Sigma> op \<sigma> \<sigma>' =
  (case resolve_binop \<Sigma> op \<sigma> \<sigma>' of
     Some \<tau> \<Rightarrow> Some \<tau>
   | None \<Rightarrow>
       (case (\<sigma>, \<sigma>') of
          (TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2, _) \<Rightarrow> do {
            \<tau> \<leftarrow> resolve_binop_union \<Sigma> op \<sigma>\<^sub>1 \<sigma>'; \<tau>' \<leftarrow> resolve_binop_union \<Sigma> op \<sigma>\<^sub>2 \<sigma>'; Some (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>')
          }
        | (_, TyUnion \<sigma>\<^sub>1' \<sigma>\<^sub>2') \<Rightarrow> do {
            \<tau> \<leftarrow> resolve_binop_union \<Sigma> op \<sigma> \<sigma>\<^sub>1'; \<tau>' \<leftarrow> resolve_binop_union \<Sigma> op \<sigma> \<sigma>\<^sub>2'; Some (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>')
          }
        | _ \<Rightarrow> None))"

(* Operator resolution with elimination of unions, by its cases *)
lemma resolve_binop_union_cases:
  assumes "resolve_binop_union \<Sigma> op \<sigma> \<sigma>' = Some \<tau>"
  obtains (overload) "resolve_binop \<Sigma> op \<sigma> \<sigma>' = Some \<tau>"
  | (left) \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2 where "\<sigma> = TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2" and "resolve_binop_union \<Sigma> op \<sigma>\<^sub>1 \<sigma>' = Some \<tau>\<^sub>1"
      and "resolve_binop_union \<Sigma> op \<sigma>\<^sub>2 \<sigma>' = Some \<tau>\<^sub>2" and "\<tau> = \<tau>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>2"
  | (right) \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<tau>\<^sub>1 \<tau>\<^sub>2 where "\<sigma>' = TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2" and "resolve_binop_union \<Sigma> op \<sigma> \<sigma>\<^sub>1 = Some \<tau>\<^sub>1"
      and "resolve_binop_union \<Sigma> op \<sigma> \<sigma>\<^sub>2 = Some \<tau>\<^sub>2" and "\<tau> = \<tau>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>2"
  using assms[unfolded resolve_binop_union.simps[of \<Sigma> op \<sigma> \<sigma>']]
  by (auto simp del: resolve_binop_union.simps simp: bind_eq_Some_conv split: option.splits ty.splits)

function (sequential)
  synth_expr :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty may_fail" and
  synth_expr_at :: "class_table \<Rightarrow> cxt \<Rightarrow> expr located \<Rightarrow> ty may_fail" and
  elements_join :: "class_table \<Rightarrow> cxt \<Rightarrow> expr located list \<Rightarrow> ty may_fail" and
  callee :: "class_table \<Rightarrow> cxt \<Rightarrow> expr located \<Rightarrow> expr located list \<Rightarrow> ty may_fail" and
  synth_call ::
    "class_table \<Rightarrow> cxt \<Rightarrow> expr located \<Rightarrow> ty \<Rightarrow> (var \<times> expr located) list \<Rightarrow> expr located list
     \<Rightarrow> ty may_fail" and
  check_expr :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> unit may_fail" and
  check_expr_at :: "class_table \<Rightarrow> cxt \<Rightarrow> expr located \<Rightarrow> ty \<Rightarrow> unit may_fail" and
  check_expr' :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> unit may_fail option" and
  check_args ::
    "class_table \<Rightarrow> cxt \<Rightarrow> expr located \<Rightarrow> (var \<times> expr located) list \<Rightarrow> expr located list \<Rightarrow> ty list
     \<Rightarrow> unit may_fail" and
  quals :: "class_table \<Rightarrow> cxt \<Rightarrow> qualifier located list \<Rightarrow> cxt may_fail"
where
"synth_expr \<Sigma> \<Gamma> (ExprVar x) =
  by_rule RuleVar (case fmlookup \<Gamma> x of Some (Ty \<tau>) \<Rightarrow> Ok \<tau> | \<theta> \<Rightarrow> Fail (var_reason x \<theta>))" |
"synth_expr \<Sigma> \<Gamma> (ExprLiteral l) = Ok (case l of LitFloat _ \<Rightarrow> TyPrim float | _ \<Rightarrow> TyLiteral l)" |
"synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) =
  (case lambda_of (node e) of
     Some (xs, e') \<Rightarrow> by_rule RuleCallLambdaSyn (do {
       \<Delta> \<leftarrow> lambda_args e xs kws es (map (synth_expr_at \<Sigma> \<Gamma>) es); synth_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e'
     })
   | None \<Rightarrow>
     (case constructor_class \<Sigma> \<Gamma> e of
        Some m \<Rightarrow> do {
          (C, explicit) \<leftarrow> m;
          case fields \<Sigma> C of
            FieldScheme \<alpha>s x\<sigma>s \<Rightarrow>
             by_rule (case explicit of None \<Rightarrow> RuleConstr | Some _ \<Rightarrow> RuleConstrExplicit) (do {
              \<sigma>es \<leftarrow> constructor_args C (FieldScheme \<alpha>s x\<sigma>s) es kws;
              case explicit of
                Some \<tau>s \<Rightarrow> do {
                  those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s \<alpha>s \<sigma>)) \<sigma>es);
                  Ok (TyClass C \<tau>s)
                }
              | None \<Rightarrow> do {
                  \<tau>s \<leftarrow> inferred_type_args \<Sigma> \<alpha>s (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es);
                  those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s \<alpha>s \<sigma>)) \<sigma>es);
                  Ok (TyClass C \<tau>s)
                }
            })
        }
      | None \<Rightarrow> do { \<sigma> \<leftarrow> callee \<Sigma> \<Gamma> e es; synth_call \<Sigma> \<Gamma> e \<sigma> kws es }))" |
"synth_expr \<Sigma> \<Gamma> (ExprBinOp op e e') = by_rule RuleBinop (do {
   \<sigma> \<leftarrow> synth_expr_at \<Sigma> \<Gamma> e;
   \<sigma>' \<leftarrow> synth_expr_at \<Sigma> \<Gamma> e';
   or_else (NoBinaryOverload op \<sigma> \<sigma>') (resolve_binop_union \<Sigma> op \<sigma> \<sigma>')
 })" |
"synth_expr \<Sigma> \<Gamma> (ExprUnOp op e) =
  (if op = UOpNeg \<and> numeric_literal (node e) then Fail undefined
   else by_rule RuleUnop (do {
     \<sigma> \<leftarrow> synth_expr_at \<Sigma> \<Gamma> e;
     or_else (NoUnaryOverload op \<sigma>) (resolve_unop \<Sigma> op \<sigma>)
   }))" |
"synth_expr \<Sigma> \<Gamma> (ExprAnd e e') =
  by_rule RuleAnd
    (do { check_expr_at \<Sigma> \<Gamma> e (TyPrim bool); check_expr_at \<Sigma> \<Gamma> e' (TyPrim bool); Ok (TyPrim bool) })" |
"synth_expr \<Sigma> \<Gamma> (ExprOr e e') =
  by_rule RuleOr
    (do { check_expr_at \<Sigma> \<Gamma> e (TyPrim bool); check_expr_at \<Sigma> \<Gamma> e' (TyPrim bool); Ok (TyPrim bool) })" |
"synth_expr \<Sigma> \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) = by_rule RuleCondSyn (do {
   check_expr_at \<Sigma> \<Gamma> e (TyPrim bool);
   case (synth_expr_at \<Sigma> \<Gamma> e\<^sub>1, synth_expr_at \<Sigma> \<Gamma> e\<^sub>2) of
     (Ok \<sigma>\<^sub>1, Ok \<sigma>\<^sub>2) \<Rightarrow> Ok (\<sigma>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<sigma>\<^sub>2)
   | (Ok \<sigma>\<^sub>1, Fail _) \<Rightarrow> do { check_expr_at \<Sigma> \<Gamma> e\<^sub>2 \<sigma>\<^sub>1; Ok \<sigma>\<^sub>1 }
   | (Fail _, Ok \<sigma>\<^sub>2) \<Rightarrow> do { check_expr_at \<Sigma> \<Gamma> e\<^sub>1 \<sigma>\<^sub>2; Ok \<sigma>\<^sub>2 }
   | (r\<^sub>1, r\<^sub>2) \<Rightarrow> Fail (synth_failure [r\<^sub>1, r\<^sub>2])
 })" |
"synth_expr \<Sigma> \<Gamma> (ExprList es) =
  (if es = [] then Fail (SelectsNoRule JudgementSynth NotSynthesised)
   else by_rule RuleSynList (do { \<tau> \<leftarrow> elements_join \<Sigma> \<Gamma> es; Ok (TyList \<tau>) }))" |
"synth_expr \<Sigma> \<Gamma> (ExprTuple es) = do { \<tau>s \<leftarrow> those_sum (map (synth_expr_at \<Sigma> \<Gamma>) es); Ok (TyTuple \<tau>s) }" |
"synth_expr \<Sigma> \<Gamma> (ExprAttribute e x) =
  (case module_attribute \<Gamma> (node e) x of
     Some m \<Rightarrow> m
   | None \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr_at \<Sigma> \<Gamma> e; attribute_type \<Sigma> \<sigma> x })" |
"synth_expr \<Sigma> \<Gamma> (ExprSubscript e e') = do {
   \<sigma> \<leftarrow> synth_expr_at \<Sigma> \<Gamma> e;
   subscript_type \<Sigma> \<sigma> (check_expr_at \<Sigma> \<Gamma> e' (TyPrim int)) (check_expr_at \<Sigma> \<Gamma> e' (TyPrim str))
     (pos_of e') (synth_expr_at \<Sigma> \<Gamma> e')
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprDict kvs) =
  (if kvs = [] then Fail (SelectsNoRule JudgementSynth NotSynthesised)
   else by_rule RuleSynDict (do {
     all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e (TyPrim str)) (map fst kvs));
     \<tau> \<leftarrow> elements_join \<Sigma> \<Gamma> (map snd kvs);
     Ok (TyDict \<tau>)
   }))" |
"synth_expr \<Sigma> \<Gamma> (ExprListComp e gs) = by_rule RuleSynListComp (do {
   \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs;
   captured gs (captures (node e)) \<Delta>;
   \<tau> \<leftarrow> synth_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e;
   Ok (TyList (base_type \<tau>))
 })" |
"synth_expr \<Sigma> \<Gamma> (ExprDictComp e e' gs) = by_rule RuleSynDictComp (do {
   \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs;
   captured gs (captures (node e) \<union> captures (node e')) \<Delta>;
   check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str);
   \<tau> \<leftarrow> synth_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e';
   Ok (TyDict (base_type \<tau>))
 })" |
"synth_expr \<Sigma> \<Gamma> _ = Fail (SelectsNoRule JudgementSynth NotSynthesised)" |

"synth_expr_at \<Sigma> \<Gamma> (At p e) = locate p (synth_expr \<Sigma> \<Gamma> e)" |

"callee \<Sigma> \<Gamma> e es =
  (case scheme_of_name \<Gamma> (node e) of
     Some (TyScheme \<alpha>s (TyCallable \<sigma>s \<sigma>)) \<Rightarrow> do {
       \<tau>s \<leftarrow> by_rule RuleCalleeScheme (inferred_type_args \<Sigma> \<alpha>s \<sigma>s (map (synth_expr_at \<Sigma> \<Gamma>) es));
       Ok (TyCallable (map (subst \<tau>s \<alpha>s) \<sigma>s) (subst \<tau>s \<alpha>s \<sigma>))
     }
   | Some _ \<Rightarrow> undefined
   | None \<Rightarrow> by_rule RuleCallee (synth_expr_at \<Sigma> \<Gamma> e))" |

"synth_call \<Sigma> \<Gamma> e (TyUnion \<sigma> \<sigma>') kws es =
  do { \<tau> \<leftarrow> synth_call \<Sigma> \<Gamma> e \<sigma> kws es; \<tau>' \<leftarrow> synth_call \<Sigma> \<Gamma> e \<sigma>' kws es; Ok (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') }" |
"synth_call \<Sigma> \<Gamma> e (TyCallable \<sigma>s \<tau>) kws es = by_rule RuleCall (do {
   check_args \<Sigma> \<Gamma> e kws es \<sigma>s;
   ensure (\<tau> \<noteq> TyPrim NoneType) (MypyCompatibility NoneResult);
   Ok \<tau>
 })" |
"synth_call \<Sigma> \<Gamma> e \<sigma> _ _ =
  Fail (if dotted_name (node e) = None then Violates RuleCallee (NotCallable \<sigma>)
        else SelectsNoRule JudgementCallee (NotCallable \<sigma>))" |

"elements_join \<Sigma> \<Gamma> es =
  (let \<sigma>s = map (synth_expr_at \<Sigma> \<Gamma>) es; \<tau> = joins \<Sigma> (map (base_type \<circ> projr) (filter (Not \<circ> isl) \<sigma>s)) in
   if \<not> list_all isl \<sigma>s then do {
     all_sum (map (\<lambda>(e, _). check_expr_at \<Sigma> \<Gamma> e \<tau>) (filter (isl \<circ> snd) (zip es \<sigma>s)));
     Ok \<tau>
   }
   else Fail (synth_failure \<sigma>s))" |

(* Check of e against \<tau> by its checking rule, if any; otherwise (or if the rule fails) by synthesising a subtype
   of \<tau> *)
"check_expr \<Sigma> \<Gamma> e \<tau> =
  (case check_expr' \<Sigma> \<Gamma> e \<tau> of
     Some (Ok ()) \<Rightarrow> Ok ()
   | Some (Fail r) \<Rightarrow> (case synth_expr \<Sigma> \<Gamma> e of Ok \<sigma> \<Rightarrow> if \<Sigma> \<turnstile> \<sigma> <: \<tau> then Ok () else Fail r | Fail _ \<Rightarrow> Fail r)
   | None \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e; ensure (\<Sigma> \<turnstile> \<sigma> <: \<tau>) (mismatch \<Sigma> \<tau> \<sigma>) })" |

"check_expr_at \<Sigma> \<Gamma> (At p e) \<tau> = locate p (check_expr \<Sigma> \<Gamma> e \<tau>)" |

(* Individual cases of expression checking; None for an expression without a checking rule *)
"check_expr' \<Sigma> \<Gamma> (ExprLambda xs e) \<tau> =
  Some (by_rule RuleLambda (case \<tau> of
     TyCallable \<tau>s \<tau>' \<Rightarrow>
       if length xs \<noteq> length \<tau>s
       then Fail (SelectsNoRule JudgementSynth (LambdaTypeMismatch \<tau> (Some (length xs))))
       else do { \<Delta> \<leftarrow> params_cxt xs \<tau>s; check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau>' }
   | _ \<Rightarrow> Fail (SelectsNoRule JudgementSynth (LambdaTypeMismatch \<tau> None))))" |
"check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> =
  (case lambda_of (node e) of
     Some (xs, e') \<Rightarrow> Some (by_rule RuleCallLambda (do {
       \<Delta> \<leftarrow> lambda_args e xs kws es (map (synth_expr_at \<Sigma> \<Gamma>) es); check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau>
     }))
   | None \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprList es) \<tau> =
  (case \<tau> of
     TyList \<tau>' \<Rightarrow> Some (by_rule RuleList (all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e \<tau>') es)))
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprTuple es) \<tau> =
  (case \<tau> of
     TyTuple \<tau>s \<Rightarrow>
       if length es = length \<tau>s then Some (by_rule RuleTuple (all_sum (map2 (check_expr_at \<Sigma> \<Gamma>) es \<tau>s)))
       else None
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) \<tau> =
  Some (by_rule RuleCond (do {
    check_expr_at \<Sigma> \<Gamma> e (TyPrim bool); check_expr_at \<Sigma> \<Gamma> e\<^sub>1 \<tau>; check_expr_at \<Sigma> \<Gamma> e\<^sub>2 \<tau>
  }))" |
"check_expr' \<Sigma> \<Gamma> (ExprDict kvs) \<tau> =
  (case \<tau> of
     TyDict \<tau>' \<Rightarrow> Some (by_rule RuleDict (do {
       all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e (TyPrim str)) (map fst kvs));
       all_sum (map (\<lambda>e. check_expr_at \<Sigma> \<Gamma> e \<tau>') (map snd kvs))
     }))
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprListComp e gs) \<tau> =
  (case \<tau> of
     TyList \<tau>' \<Rightarrow>
       Some (by_rule RuleListComp (do {
         \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs; captured gs (captures (node e)) \<Delta>; check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau>'
       }))
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprDictComp e e' gs) \<tau> =
  (case \<tau> of
     TyDict \<tau>' \<Rightarrow> Some (by_rule RuleDictComp (do {
       \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs;
       captured gs (captures (node e) \<union> captures (node e')) \<Delta>;
       check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str);
       check_expr_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau>'
     }))
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> e \<tau> = var_scheme \<Sigma> \<Gamma> e \<tau>" |

"check_args \<Sigma> \<Gamma> e kws es \<sigma>s = do {
   ensure (kws = []) KeywordArgumentsNotConstructor;
   ensure (length \<sigma>s = length es) (CallArityMismatch e (length \<sigma>s) (length es));
   all_sum (map2 (check_expr_at \<Sigma> \<Gamma>) es \<sigma>s)
 }" |

"quals \<Sigma> \<Gamma> [] = Ok fmempty" |
"quals \<Sigma> \<Gamma> (At _ (Guard e) # gs) =
  do { by_rule RuleQualGuard (check_expr_at \<Sigma> \<Gamma> e (TyPrim bool)); quals \<Sigma> \<Gamma> gs }" |
"quals \<Sigma> \<Gamma> (At p (Generator x e) # gs) = do {
   \<tau> \<leftarrow> by_rule RuleQualGenerator (do {
     \<sigma> \<leftarrow> synth_expr_at \<Sigma> \<Gamma> e;
     \<tau> \<leftarrow> or_else (Located (pos_of e) (NotIterable \<sigma>)) (elem_type \<Sigma> \<sigma>);
     ensure (x \<notin> captures gs) (Located p (CapturedGeneratorVariable x));
     Ok \<tau>
   });
   \<Delta> \<leftarrow> quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs;
   Ok (fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)
 }"
by pat_completeness auto

termination
by (relation "measures [\<lambda>x. case x of
     Inl (Inl (Inl (_, _, e))) \<Rightarrow> size e
   | Inl (Inl (Inr (_, _, e))) \<Rightarrow> Suc (size (node e))
   | Inl (Inr (Inl (_, _, es))) \<Rightarrow> size_list (\<lambda>e. Suc (size (node e))) es
   | Inl (Inr (Inr (Inl (_, _, e, es)))) \<Rightarrow> Suc (size (node e)) + size_list (\<lambda>e. Suc (size (node e))) es
   | Inl (Inr (Inr (Inr (_, _, _, _, kws, es)))) \<Rightarrow>
       size_list (\<lambda>e. Suc (size (node e))) es + size_list (\<lambda>p. Suc (Suc (size (node (snd p))))) kws
   | Inr (Inl (Inl (_, _, e, _))) \<Rightarrow> size e
   | Inr (Inl (Inr (_, _, e, _))) \<Rightarrow> Suc (size (node e))
   | Inr (Inr (Inl (_, _, e, _))) \<Rightarrow> size e
   | Inr (Inr (Inr (Inl (_, _, _, kws, es, _)))) \<Rightarrow>
       size_list (\<lambda>e. Suc (size (node e))) es + size_list (\<lambda>p. Suc (Suc (size (node (snd p))))) kws
   | Inr (Inr (Inr (Inr (_, _, gs)))) \<Rightarrow> size_list (\<lambda>g. Suc (size (node g))) gs,
   \<lambda>x. case x of
     Inl (Inl _) \<Rightarrow> 0
   | Inl (Inr (Inl _)) \<Rightarrow> 1
   | Inl (Inr (Inr _)) \<Rightarrow> 4
   | Inr (Inl (Inl _)) \<Rightarrow> 2
   | Inr (Inl (Inr _)) \<Rightarrow> 0
   | Inr (Inr (Inl _)) \<Rightarrow> 1
   | Inr (Inr (Inr (Inl _))) \<Rightarrow> 3
   | Inr (Inr (Inr (Inr _))) \<Rightarrow> 0,
   \<lambda>x. case x of Inl (Inr (Inr (Inr (_, _, _, \<tau>, _, _)))) \<Rightarrow> size \<tau> | _ \<Rightarrow> 0]")
   (auto dest!: nth_mem constructor_args_elem lambda_of_size elim!: in_set_zipE
     dest: size_node_snd_elem size_node_snd_elem' size_node_elem size_node_pair_fst_elem size_node_pair_snd_elem
     intro: size_list_estimation' size_list_elem
     simp: less_Suc_eq_le size_list_node_fst size_list_node_snd)

(* Context entry for a type scheme, which is a plain type when its parameter list is empty *)
fun signature_entry :: "ty_scheme \<Rightarrow> cxt_entry"
where
"signature_entry (TyScheme [] \<tau>) = Ty \<tau>" |
"signature_entry \<pi> = Scheme \<pi>"

fun def_signature :: "class_table \<Rightarrow> cxt \<Rightarrow> func \<Rightarrow> ty_scheme may_fail"
where
"def_signature \<Sigma> \<Gamma> (Def f \<alpha>s xps \<psi> s) =
   (let \<Gamma>' = \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar in by_rule RuleDefSignature (do {
      (case find (\<lambda>\<alpha>. \<alpha> \<in> tyvars \<Gamma>) \<alpha>s of Some \<alpha> \<Rightarrow> Fail (Redeclaration \<alpha>) | None \<Rightarrow> Ok ());
      \<sigma>s \<leftarrow> those_sum (map (resolve_type \<Sigma> \<Gamma>' \<circ> snd) xps);
      \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma>' \<psi>;
      Ok (TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>))
    }))"

lemma def_signature_disjoint:
  "def_signature \<Sigma> \<Gamma> d = Ok \<pi> \<Longrightarrow> case d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}"
  by (cases d) (auto simp: Let_def bind_sum_def find_None_iff split: sum.splits option.splits)

lemma def_signatures_callable:
  "\<lbrakk> those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s ; i < length ds
   ; \<pi>s ! i = TyScheme \<alpha>s \<tau> \<rbrakk>
  \<Longrightarrow> \<exists>\<sigma>s \<tau>'. \<tau> = TyCallable \<sigma>s \<tau>'"
  by (cases "node (ds ! i)")
     (fastforce dest!: those_sum_map_Ok simp: list_all2_conv_all_nth bind_sum_def Let_def
      split: sum.splits option.splits)

(* Check a call statement with callee type \<sigma>, where a result of None is allowed *)
fun check_call_stmt ::
  "class_table \<Rightarrow> cxt \<Rightarrow> expr located \<Rightarrow> ty \<Rightarrow> (var \<times> expr located) list \<Rightarrow> expr located list
   \<Rightarrow> unit may_fail"
where
"check_call_stmt \<Sigma> \<Gamma> e (TyUnion \<sigma> \<sigma>') kws es =
  do { check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es; check_call_stmt \<Sigma> \<Gamma> e \<sigma>' kws es }" |
"check_call_stmt \<Sigma> \<Gamma> e (TyCallable \<sigma>s (TyPrim NoneType)) kws es =
  by_rule RuleCallStmt (check_args \<Sigma> \<Gamma> e kws es \<sigma>s)" |
"check_call_stmt \<Sigma> \<Gamma> e \<sigma> kws es = do { synth_call \<Sigma> \<Gamma> e \<sigma> kws es; Ok () }"

(* Failure for the first assignment target of xs which isn't in X, declared or a pattern variable of Y, located
   at its assignment *)
definition check_assignments_declared ::
  "var set \<Rightarrow> var located list \<Rightarrow> var list \<Rightarrow> var set \<Rightarrow> unit may_fail"
where
"check_assignments_declared X xs ys Y =
  (case find (\<lambda>x. node x \<notin> X \<and> node x \<notin> set ys \<and> node x \<notin> Y) xs of
     Some x \<Rightarrow> Fail (Located (pos_of x) (Violates RuleAssign (UndeclaredAssignment (node x))))
   | None \<Rightarrow> Ok ())"

(* Bindings of the patterns ps of the cases of a match at remaining type \<tau> and residual L, with the final
   remaining type and residual *)
fun match_cases ::
  "class_table \<Rightarrow> cxt \<Rightarrow> ty \<Rightarrow> shape list \<Rightarrow> pat located list \<Rightarrow> (cxt list \<times> ty \<times> shape list) may_fail"
where
"match_cases \<Sigma> \<Gamma> \<tau> L [] = Ok ([], \<tau>, L)" |
"match_cases \<Sigma> \<Gamma> \<tau> L (p # ps) = do {
   \<Delta> \<leftarrow> check_pat_at \<Sigma> \<Gamma> p \<tau>;
   (_, L') \<leftarrow>
     or_else (Located (pos_of p) (Violates RulePatShapes (UnreachableCase p))) (match_shapes \<Sigma> \<Gamma> L (node p));
   (\<Delta>s, \<tau>', L'') \<leftarrow> match_cases \<Sigma> \<Gamma> (remaining \<Sigma> \<Gamma> \<tau> (node p)) L' ps;
   Ok (fmmap Ty \<Delta> # \<Delta>s, \<tau>', L'')
 }"

lemma match_cases_unbound:
  "\<lbrakk> match_cases \<Sigma> \<Gamma> \<tau> L ps = Ok (\<Delta>s, \<tau>', L') ; \<Delta> \<in> set \<Delta>s ; x |\<in>| fmdom \<Delta> \<rbrakk> \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound"
proof (induction ps arbitrary: \<tau> L \<Delta>s)
  case (Cons p ps)
  from Cons.prems(1) obtain \<Delta>\<^sub>p \<Delta>s' L\<^sub>1 where p: "check_pat_at \<Sigma> \<Gamma> p \<tau> = Ok \<Delta>\<^sub>p"
    and \<Delta>s: "\<Delta>s = fmmap Ty \<Delta>\<^sub>p # \<Delta>s'"
    and ps: "match_cases \<Sigma> \<Gamma> (remaining \<Sigma> \<Gamma> \<tau> (node p)) L\<^sub>1 ps = Ok (\<Delta>s', \<tau>', L')"
    by (auto simp: bind_sum_Ok split: prod.splits)
  from Cons.prems(2) \<Delta>s consider (head) "\<Delta> = fmmap Ty \<Delta>\<^sub>p" | (tail) "\<Delta> \<in> set \<Delta>s'" by auto
  then show ?case
  proof cases
    case head
    with Cons.prems(3) check_pat_unbound(2)[OF p] show ?thesis by simp
  next
    case tail
    from Cons.IH[OF ps this Cons.prems(3)] show ?thesis .
  qed
qed simp

function (sequential) check_stmt :: "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> stmt \<Rightarrow> static_outcome may_fail"
and check_stmt_at :: "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> stmt located \<Rightarrow> static_outcome may_fail"
and check_def :: "class_table \<Rightarrow> cxt \<Rightarrow> func \<Rightarrow> ty_scheme \<Rightarrow> unit may_fail"
and check_def_at :: "class_table \<Rightarrow> cxt \<Rightarrow> func located \<Rightarrow> ty_scheme \<Rightarrow> unit may_fail"
where
"check_stmt \<Sigma> \<Gamma> \<zeta> StmtPass = Ok (Assigns\<^sub>R fmempty None)" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtDeclare x \<psi>) = do {
   check_unbound \<Gamma> x; \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; Ok (Assigns\<^sub>R (fmupd x (DU \<tau>) fmempty) None)
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x None e) =
  by_rule RuleAssign (case fmlookup \<Gamma> x of
     Some (DU \<tau>) \<Rightarrow> do { check_expr_at \<Sigma> \<Gamma> e \<tau>; Ok (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty) None) }
   | \<theta> \<Rightarrow> Fail (assign_reason x \<theta>))" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x (Some \<psi>) e) = by_rule RuleDeclareAssign (do {
   check_unbound \<Gamma> x; \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; check_expr_at \<Sigma> \<Gamma> e \<tau>;
   Ok (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty) None)
 })" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) = do {
   (case node e of
      ExprCall e' (es, kws) \<Rightarrow>
        if lambda_of (node e') = None \<and> class_of_name \<Gamma> (node e') = None
        then do { \<sigma> \<leftarrow> callee \<Sigma> \<Gamma> e' es; check_call_stmt \<Sigma> \<Gamma> e' \<sigma> kws es }
        else do { synth_expr_at \<Sigma> \<Gamma> e; Ok () }
    | _ \<Rightarrow> do { synth_expr_at \<Sigma> \<Gamma> e; Ok () });
   Ok (Assigns\<^sub>R fmempty None)
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtPrint e) =
  do { ensure (\<zeta> = None) PrintInFunction; synth_expr_at \<Sigma> \<Gamma> e; Ok (Assigns\<^sub>R fmempty None) }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') =
  (let false_literal = (node e = ExprLiteral (LitBool False)) in
   by_rule
     (case e' of None \<Rightarrow> RuleAssert | Some _ \<Rightarrow> if false_literal then RuleAssertFalseMsg else RuleAssertMsg)
     (do {
     (if false_literal then Ok () else check_expr_at \<Sigma> \<Gamma> e (TyPrim bool));
     (case e' of Some e'' \<Rightarrow> check_expr_at \<Sigma> \<Gamma> e'' (TyPrim str) | None \<Rightarrow> Ok ());
     Ok (if false_literal then Returns\<^sub>R
          else Assigns\<^sub>R fmempty
            (if \<zeta> \<noteq> None \<and> synth_expr_at \<Sigma> \<Gamma> e = Ok (TyLiteral (LitBool False))
             then Some (MypyCompatibility MissingReturnAssertion) else None))
   }))" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn None) =
  by_rule RuleReturnNone (case \<zeta> of
     Some \<tau> \<Rightarrow>
       if \<Sigma> \<turnstile> \<tau> \<approx> TyPrim NoneType then Ok Returns\<^sub>R
       else Fail (mypy_only_if (\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>) (BareReturn \<tau>))
   | None \<Rightarrow> Fail ReturnOutsideFunction)" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn (Some e)) =
  by_rule RuleReturn (case \<zeta> of
     Some \<tau> \<Rightarrow> do { check_expr_at \<Sigma> \<Gamma> e \<tau>; Ok Returns\<^sub>R }
   | None \<Rightarrow> Fail ReturnOutsideFunction)" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = by_rule (if else' = None then RuleIf else RuleIfElse) (do {
   check_expr_at \<Sigma> \<Gamma> e (TyPrim bool);
   merges \<Sigma> (set (declares (StmtIf e s elifs else'))) (check_stmt_at \<Sigma> \<Gamma> \<zeta> s
           # map (\<lambda>(e', s'). do { check_expr_at \<Sigma> \<Gamma> e' (TyPrim bool); check_stmt_at \<Sigma> \<Gamma> \<zeta> s' }) elifs
           @ [case else' of Some s' \<Rightarrow> check_stmt_at \<Sigma> \<Gamma> \<zeta> s' | None \<Rightarrow> Ok (Assigns\<^sub>R fmempty None)])
 })" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = by_rule RuleSeq (do {
   R \<leftarrow> check_stmt_at \<Sigma> \<Gamma> \<zeta> s;
   case R of
     Assigns\<^sub>R \<Delta> r \<Rightarrow> do { R' \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s'; Ok (Assigns\<^sub>R \<Delta> r \<otimes> R') }
   | Returns\<^sub>R \<Rightarrow> Fail (Located (pos_of s') UnreachableStatement)
 })" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMutualRegion ds) = do {
   (case redeclared node {} (map (\<lambda>d. At (pos_of d) (def_name (node d))) ds) of
      Some f \<Rightarrow> Fail (Located (pos_of f) (Redeclaration (node f)))
    | None \<Rightarrow> Ok ());
   all_sum (map (\<lambda>d. locate (pos_of d) (check_unbound \<Gamma> (def_name (node d)))) ds);
   \<pi>s \<leftarrow> those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds);
   let \<Delta> = fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s));
   all_sum (map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> \<Delta>)) ds \<pi>s);
   Ok (Assigns\<^sub>R \<Delta> None)
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMatch e bs) = do {
   \<sigma> \<leftarrow> synth_expr_at \<Sigma> \<Gamma> e;
   (\<Delta>s, \<tau>, L) \<leftarrow> match_cases \<Sigma> \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst bs);
   merges \<Sigma> (set (declares (StmtMatch e bs)))
     (map2 (\<lambda>\<Delta> (_, s). do { R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) }) \<Delta>s bs
      @ (if \<tau> = TyPrim Never then []
         else [Ok (Assigns\<^sub>R fmempty
                 (if L = [] then
                    Some (MypyCompatibility (Violates RuleMatchPartial (MissingReturnMatchPartial \<tau>)))
                  else None))]))
 }" |

"check_stmt_at \<Sigma> \<Gamma> \<zeta> (At p s) =
  map_sum (locate_reason p)
    (\<lambda>R. case R of Assigns\<^sub>R \<Delta> r \<Rightarrow> Assigns\<^sub>R \<Delta> (map_option (locate_reason p) r) | Returns\<^sub>R \<Rightarrow> Returns\<^sub>R)
    (check_stmt \<Sigma> \<Gamma> \<zeta> s)" |

"check_def \<Sigma> \<Gamma> (Def f \<alpha>s xps \<psi> s) (TyScheme \<alpha>s' (TyCallable \<sigma>s \<tau>)) =
  (let xs = map fst xps in by_rule RuleDefBody (do {
     check_assignments_declared (set xs) (assign_targets s) (declares (node s)) (binds s);
     \<Delta> \<leftarrow> (case scope Unbound xs s of
             Some \<Delta> \<Rightarrow> Ok \<Delta>
           | None \<Rightarrow> Fail (redeclaration xs (declarations s) (pat_bound s)));
     if length xs = length \<sigma>s then do {
       \<Delta>' \<leftarrow> params_cxt xs \<sigma>s;
       R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> \<Delta>' \<otimes> \<Delta>) (Some \<tau>) s;
       case R of
         Assigns\<^sub>R _ r \<Rightarrow>
           if \<Sigma> \<turnstile> \<tau> \<approx> TyPrim NoneType then Ok ()
           else Fail (case r of
                       Some r' \<Rightarrow> r'
                     | None \<Rightarrow> mypy_only_if (\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>) (MissingReturn f \<tau>))
       | Returns\<^sub>R \<Rightarrow> Ok ()
     }
     else Fail undefined
   }))" |
"check_def \<Sigma> \<Gamma> _ _ = undefined" |

"check_def_at \<Sigma> \<Gamma> (At p d) \<pi> = locate p (check_def \<Sigma> \<Gamma> d \<pi>)"
by pat_completeness auto

termination
by (relation "measure (\<lambda>x. case x of
     Inl (Inl (_, _, _, s)) \<Rightarrow> size s
   | Inl (Inr (_, _, _, s)) \<Rightarrow> Suc (size (node s))
   | Inr (Inl (_, _, d, _)) \<Rightarrow> size d
   | Inr (Inr (_, _, d, _)) \<Rightarrow> Suc (size (node d)))")
   (auto elim!: in_set_zipE dest: size_node_snd_elem size_node_elem)

fun check_type_def :: "class_table \<Rightarrow> cxt \<Rightarrow> type_def located \<Rightarrow> unit may_fail"
where
"check_type_def \<Sigma> \<Gamma> (At p (Dataclass c \<alpha>s b \<phi>)) =
  locate p (by_rule (if b = None then RuleClass else RuleClassExtend) (do {
   check_predefined \<Gamma> (var ''dataclass'');
   those_sum (map (resolve_type \<Sigma> \<Gamma> \<circ> snd) \<phi>);
   base_class \<leftarrow>
     (case b of
        None \<Rightarrow> Ok None
      | Some (q', \<psi>s) \<Rightarrow>
          (case resolve_name \<Gamma> q' of
             Some (Type D) \<Rightarrow>
               if D = range_class then Fail (Violates RuleClassExtend RangeBase)
               else do { resolve_type \<Sigma> \<Gamma> (TyExprName q' \<psi>s); Ok (Some D) }
           | None \<Rightarrow> Fail (SelectsNoRule JudgementResolveName (not_type_name \<Gamma> q'))
           | Some _ \<Rightarrow> Fail (Violates RuleClassExtend (not_type_name \<Gamma> q'))));
   (case redeclared id {} (map fst \<phi>) of Some x \<Rightarrow> Fail (DuplicateField x c) | None \<Rightarrow> Ok ());
   (case base_class of
      Some D \<Rightarrow>
        (case find (\<lambda>x. x \<in> set (field_names \<Sigma> D)) (map fst \<phi>) of
           Some x \<Rightarrow> Fail (InheritedField x c (short_name D))
         | None \<Rightarrow> Ok ())
    | None \<Rightarrow> Ok ())
 }))" |
"check_type_def \<Sigma> \<Gamma> (At p (TypeStmt x \<alpha>s \<psi>)) =
  locate p (by_rule RuleTypeAlias (do { resolve_type \<Sigma> \<Gamma> \<psi>; Ok () }))"

fun check_top_stmt :: "class_table \<Rightarrow> name \<Rightarrow> cxt \<Rightarrow> top_stmt \<Rightarrow> (static_outcome \<times> class_table) may_fail"
where
"check_top_stmt \<Sigma> q \<Gamma> (Stmt s) = do { R \<leftarrow> check_stmt_at \<Sigma> \<Gamma> None s; Ok (R, \<Sigma>) }" |
"check_top_stmt \<Sigma> q \<Gamma> (TopSeq t t') = do {
   (R, \<Sigma>') \<leftarrow> check_top_stmt \<Sigma> q \<Gamma> t;
   case R of
     Assigns\<^sub>R \<Delta> r \<Rightarrow> do {
       (R', \<Sigma>'') \<leftarrow> check_top_stmt \<Sigma>' q (\<Gamma> \<otimes> \<Delta>) t';
       Ok (Assigns\<^sub>R \<Delta> r \<otimes> R', \<Sigma>'')
     }
   | Returns\<^sub>R \<Rightarrow> Fail (Located (last_pos t) (Violates RuleTopSeq TopLevelAssertFalse))
 }" |
"check_top_stmt \<Sigma> q \<Gamma> (TypeDefs \<chi>s) =
  (let js = [0..<length \<chi>s];
       \<Delta> = fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_entry \<Gamma> q \<chi>s j)) js);
       \<Sigma>' = fold (\<lambda>j \<Sigma>''. \<Sigma>'' \<otimes> class_table \<Gamma> q \<chi>s j) js \<Sigma> in
   do {
     those_sum (map (\<lambda>j. check_type_def \<Sigma>' (type_context \<Gamma> q \<chi>s j) (\<chi>s ! j)) js);
     Ok (Assigns\<^sub>R \<Delta> None, \<Sigma>')
   })"

(* Checking succeeds by the checking rule of the expression or by synthesising a subtype *)
lemma check_expr_cases:
  assumes "check_expr \<Sigma> \<Gamma> e \<tau> = Ok ()"
  shows "check_expr' \<Sigma> \<Gamma> e \<tau> = Some (Ok ()) \<or> (\<exists>\<sigma>. synth_expr \<Sigma> \<Gamma> e = Ok \<sigma> \<and> \<Sigma> \<turnstile> \<sigma> <: \<tau>)"
  using assms
  by (auto simp: check_expr.simps[of \<Sigma> \<Gamma> e \<tau>] ensure_def bind_sum_def
      split: option.splits sum.splits if_splits)

(* Synthesis of a conditional, from both branches or from one branch checked against the other *)
lemma synth_cond:
  assumes "synth_expr \<Sigma> \<Gamma> (ExprCond e1 e e2) = Ok \<tau>"
  obtains \<sigma>1 \<sigma>2 where "synth_expr_at \<Sigma> \<Gamma> e1 = Ok \<sigma>1" and "synth_expr_at \<Sigma> \<Gamma> e2 = Ok \<sigma>2" and "\<tau> = \<sigma>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<sigma>2"
    | "synth_expr_at \<Sigma> \<Gamma> e1 = Ok \<tau>" and "check_expr_at \<Sigma> \<Gamma> e2 \<tau> = Ok ()"
    | "check_expr_at \<Sigma> \<Gamma> e1 \<tau> = Ok ()" and "synth_expr_at \<Sigma> \<Gamma> e2 = Ok \<tau>"
  using assms by (auto simp: bind_sum_def split: sum.splits)

lemma check_call_stmt_synth:
  "\<tau> \<noteq> TyPrim NoneType
  \<Longrightarrow> check_call_stmt \<Sigma> \<Gamma> e (TyCallable \<sigma>s \<tau>) kws es = do { synth_call \<Sigma> \<Gamma> e (TyCallable \<sigma>s \<tau>) kws es; Ok () }"
  by (cases "(\<Sigma>, \<Gamma>, e, TyCallable \<sigma>s \<tau>, kws, es)" rule: check_call_stmt.cases) auto

lemma def_signatures_arity:
  assumes "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s" and "i < length ds"
    and "node (ds ! i) = Def f \<alpha>s xps \<psi> s" and "\<pi>s ! i = TyScheme \<alpha>s' (TyCallable \<sigma>s \<tau>)"
  shows "length \<sigma>s = length xps"
proof -
  from those_sum_map_Ok[OF assms(1)] assms(2)
  have "locate (pos_of (ds ! i)) (def_signature \<Sigma> \<Gamma> (node (ds ! i))) = Ok (\<pi>s ! i)"
    by (simp add: list_all2_conv_all_nth)
  with assms(3, 4) obtain \<sigma>s'
    where "those_sum (map (resolve_type \<Sigma> (\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar) \<circ> snd) xps) = Ok \<sigma>s'"
    and "\<sigma>s = \<sigma>s'"
    by (cases "pos_of (ds ! i)") (auto simp: Let_def bind_sum_def split: sum.splits option.splits)
  then show ?thesis by (auto dest!: those_sum_map_Ok list_all2_lengthD)
qed

lemma check_seq:
  "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R
  \<Longrightarrow> \<exists>\<Delta> r R'. check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r) \<and> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s' = Ok R'
     \<and> R = Assigns\<^sub>R \<Delta> r \<otimes> R'"
  by (auto simp: bind_sum_def split: sum.splits static_outcome.splits)

lemma check_assert_msg:
  "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R \<Longrightarrow> check_expr_at \<Sigma> \<Gamma> e' (TyPrim str) = Ok ()"
  by (auto simp: Let_def bind_sum_def split: sum.splits if_splits)

(* Synthesis of a constructor call, by checking each argument against the type of its field at the type
   arguments of the class *)
lemma constr_synth:
  assumes "synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) = Ok \<tau>" and "lambda_of (node e) = None"
    and "constructor_class \<Sigma> \<Gamma> e = Some m"
  obtains C explicit x\<sigma>s \<sigma>es \<tau>s where "m = Ok (C, explicit)"
    and "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    and "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and "\<forall>(\<sigma>, e') \<in> set \<sigma>es. check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s (type_params \<Sigma> C) \<sigma>) = Ok ()"
    and "\<tau> = TyClass C \<tau>s"
    and "explicit = Some \<tau>s \<or> explicit = None
      \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C) (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
proof -
  obtain C explicit where m: "m = Ok (C, explicit)"
  proof (cases m)
    case (Inl r)
    with assms show ?thesis by (simp add: bind_sum_def)
  next
    case (Inr p)
    then show ?thesis using that by (cases p) simp
  qed
  obtain x\<sigma>s where fields: "fields \<Sigma> C = FieldScheme (type_params \<Sigma> C) x\<sigma>s"
    by (simp add: fields_ancestor_fields)
  have "\<exists>\<sigma>es \<tau>s \<rho>s. constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es
      \<and> those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s (type_params \<Sigma> C) \<sigma>)) \<sigma>es) = Ok \<rho>s
      \<and> \<tau> = TyClass C \<tau>s
      \<and> (explicit = Some \<tau>s \<or> explicit = None
         \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C) (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s)"
    using assms m fields by (auto simp: bind_sum_def split: sum.splits option.splits)
  then obtain \<sigma>es \<tau>s \<rho>s where args: "constructor_args C (FieldScheme (type_params \<Sigma> C) x\<sigma>s) es kws = Ok \<sigma>es"
    and checked: "those_sum (map (\<lambda>(\<sigma>, e'). check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s (type_params \<Sigma> C) \<sigma>)) \<sigma>es) = Ok \<rho>s"
    and "\<tau> = TyClass C \<tau>s"
    and "explicit = Some \<tau>s \<or> explicit = None
      \<and> inferred_type_args \<Sigma> (type_params \<Sigma> C) (map fst \<sigma>es) (map (synth_expr_at \<Sigma> \<Gamma> \<circ> snd) \<sigma>es) = Ok \<tau>s"
    by blast
  moreover have "\<forall>(\<sigma>, e') \<in> set \<sigma>es. check_expr_at \<Sigma> \<Gamma> e' (subst \<tau>s (type_params \<Sigma> C) \<sigma>) = Ok ()"
    using those_sum_map_Ok[OF checked] by (fastforce simp: list_all2_conv_all_nth in_set_conv_nth)
  ultimately show thesis using that m fields by blast
qed

lemma check_stmt_at_Ok:
  assumes "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R"
  shows "\<exists>R'. check_stmt \<Sigma> \<Gamma> \<zeta> (node s) = Ok R' \<and> bindings_of R' = bindings_of R"
proof (cases s)
  case (At p s')
  then show ?thesis using assms by (cases "check_stmt \<Sigma> \<Gamma> \<zeta> s'") (auto split: static_outcome.splits)
qed

(* Static outcomes of the branches of an elif block, as listed by the if rule *)
fun check_elif :: "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> elif_block \<Rightarrow> static_outcome may_fail list"
where
"check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else') =
  map (\<lambda>(e', s'). do { check_expr_at \<Sigma> \<Gamma> e' (TyPrim bool); check_stmt_at \<Sigma> \<Gamma> \<zeta> s' }) elifs
  @ [case else' of Some s' \<Rightarrow> check_stmt_at \<Sigma> \<Gamma> \<zeta> s' | None \<Rightarrow> Ok (Assigns\<^sub>R fmempty None)]"

lemma check_stmt_if:
  "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = by_rule (if else' = None then RuleIf else RuleIfElse) (do {
     check_expr_at \<Sigma> \<Gamma> e (TyPrim bool);
     merges \<Sigma> (set (declares (StmtIf e s elifs else')))
       (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))
   })"
  by simp

lemma check_if:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  shows "\<exists>Rs. those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs
     \<and> merges \<Sigma> (set (declares (StmtIf e s elifs else')))
         (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R"
  using assms by (auto simp: check_stmt_if bind_sum_def split: sum.splits dest: merges_Ok)

(* Branches of a match statement, each with the bindings of its pattern *)
definition match_branches ::
  "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> cxt list \<Rightarrow> (pat located \<times> stmt located) list \<Rightarrow> ty \<Rightarrow> shape list
   \<Rightarrow> static_outcome may_fail list"
where
"match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L =
  map2 (\<lambda>\<Delta> (_, s). do { R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) }) \<Delta>s bs
  @ (if \<tau> = TyPrim Never then []
     else [Ok (Assigns\<^sub>R fmempty
             (if L = [] then Some (MypyCompatibility (Violates RuleMatchPartial (MissingReturnMatchPartial \<tau>)))
              else None))])"

lemma check_match:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMatch e bs) = Ok R"
  obtains \<sigma> \<Delta>s \<tau> L where "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
    and "match_cases \<Sigma> \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst bs) = Ok (\<Delta>s, \<tau>, L)"
    and "merges \<Sigma> (set (declares (StmtMatch e bs))) (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L) = Ok R"
  using assms by (auto simp: bind_sum_Ok match_branches_def split: prod.splits)

(* Variable bound by a statement, unbound or declared but unassigned beforehand *)
lemma check_stmt_bound:
  "check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r) \<Longrightarrow> x |\<in>| fmdom \<Delta>
    \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))"
  "check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta> r) \<Longrightarrow> x |\<in>| fmdom \<Delta>
    \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound \<or> (\<exists>\<tau>. fmlookup \<Gamma> x = Some (DU \<tau>))"
  "check_def \<Sigma> \<Gamma> d \<pi> = m \<Longrightarrow> True"
  "check_def_at \<Sigma> \<Gamma> d' \<pi> = m \<Longrightarrow> True"
proof (induction \<Sigma> \<Gamma> \<zeta> s and \<Sigma> \<Gamma> \<zeta> s' and \<Sigma> \<Gamma> d \<pi> and \<Sigma> \<Gamma> d' \<pi> arbitrary: \<Delta> r and \<Delta> r
    rule: check_stmt_check_stmt_at_check_def_check_def_at.induct)
  case (10 \<Sigma> \<Gamma> \<zeta> e s elifs else')
  from "10.prems"(1) obtain z where e: "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok z"
    and m: "merges \<Sigma> (set (declares (StmtIf e s elifs else')))
              (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok (Assigns\<^sub>R \<Delta> r)"
    unfolding check_stmt_if by (auto simp: bind_sum_Ok)
  from merges_dom[OF m "10.prems"(2)] obtain \<Delta>' r'
    where mem: "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else'))"
    and x: "x |\<in>| fmdom \<Delta>'"
    by blast
  from mem consider (s) "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta>' r')"
    | (elif) e' s' z' where "(e', s') \<in> set elifs" and "check_expr_at \<Sigma> \<Gamma> e' (TyPrim bool) = Ok z'"
        and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta>' r')"
    | (else) s' where "else' = Some s'" and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s' = Ok (Assigns\<^sub>R \<Delta>' r')"
    | (none) "\<Delta>' = fmempty"
    by (auto simp: Ok_bind_sum split: option.splits)
  then show ?case
  proof cases
    case s
    from "10.IH"(1)[OF e s x] show ?thesis .
  next
    case elif
    from "10.IH"(2)[OF e elif(1) refl elif(2, 3) x] show ?thesis .
  next
    case else
    from "10.IH"(3)[OF e else x] show ?thesis .
  next
    case none
    with x show ?thesis by simp
  qed
next
  case (11 \<Sigma> \<Gamma> \<zeta> s s')
  from check_seq[OF "11.prems"(1)] obtain \<Delta>\<^sub>1 r\<^sub>1 R\<^sub>2 where s: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1)"
    and s': "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>1) \<zeta> s' = Ok R\<^sub>2" and R: "Assigns\<^sub>R \<Delta> r = Assigns\<^sub>R \<Delta>\<^sub>1 r\<^sub>1 \<otimes> R\<^sub>2"
    by blast
  from R obtain \<Delta>\<^sub>2 r\<^sub>2 where R\<^sub>2: "R\<^sub>2 = Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2" and \<Delta>: "\<Delta> = \<Delta>\<^sub>1 \<otimes> \<Delta>\<^sub>2" by (cases R\<^sub>2) auto
  show ?case
  proof (cases "x |\<in>| fmdom \<Delta>\<^sub>1")
    case True
    from "11.IH"(1)[OF s True] show ?thesis .
  next
    case False
    with "11.prems"(2) \<Delta> have "x |\<in>| fmdom \<Delta>\<^sub>2" by simp
    from "11.IH"(2)[OF s refl s'[unfolded R\<^sub>2] this] False show ?thesis by simp
  qed
next
  case (12 \<Sigma> \<Gamma> \<zeta> ds)
  from "12.prems"(1) obtain \<pi>s
    where unb: "all_sum (map (\<lambda>d. locate (pos_of d) (check_unbound \<Gamma> (def_name (node d)))) ds) = Ok ()"
    and \<Delta>: "\<Delta> = fmap_of_list (zip (map (def_name \<circ> node) ds) (map signature_entry \<pi>s))"
    by (auto simp: bind_sum_Ok Let_def)
  from "12.prems"(2) \<Delta> obtain d where "d \<in> set ds" and "def_name (node d) = x"
    by (auto simp: fset_of_list_elem dest!: set_zip_leftD)
  with all_sum_Ok[OF unb, of "locate (pos_of d) (check_unbound \<Gamma> x)"] have "check_unbound \<Gamma> x = Ok ()"
    by auto
  then show ?case by (auto dest: check_unbound_Ok)
next
  case (13 \<Sigma> \<Gamma> \<zeta> e bs)
  from "13.prems"(1) obtain \<sigma> \<Delta>s \<tau> L where \<sigma>: "synth_expr_at \<Sigma> \<Gamma> e = Ok \<sigma>"
    and mc: "match_cases \<Sigma> \<Gamma> \<sigma> (shapes \<Sigma> \<sigma> {}) (map fst bs) = Ok (\<Delta>s, \<tau>, L)"
    and m: "merges \<Sigma> (set (declares (StmtMatch e bs))) (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L) = Ok (Assigns\<^sub>R \<Delta> r)"
    by (rule check_match)
  from merges_dom[OF m "13.prems"(2)] obtain \<Delta>' r'
    where mem: "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set (match_branches \<Sigma> \<Gamma> \<zeta> \<Delta>s bs \<tau> L)" and x: "x |\<in>| fmdom \<Delta>'"
    by blast
  show ?case
  proof (cases "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set (map2 (\<lambda>\<Delta> (_, s). do {
                  R \<leftarrow> check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s; Ok (Assigns\<^sub>R \<Delta> None \<otimes> R) }) \<Delta>s bs)")
    case True
    from Ok_in_set_map2[OF True] obtain \<Delta>\<^sub>p p s R where b: "(\<Delta>\<^sub>p, (p, s)) \<in> set (zip \<Delta>s bs)"
      and R: "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>\<^sub>p) \<zeta> s = Ok R" and \<Delta>': "Assigns\<^sub>R \<Delta>\<^sub>p None \<otimes> R = Assigns\<^sub>R \<Delta>' r'"
      by (auto simp: bind_sum_Ok split: prod.splits)
    from \<Delta>' obtain \<Delta>\<^sub>2 r\<^sub>2 where R\<^sub>2: "R = Assigns\<^sub>R \<Delta>\<^sub>2 r\<^sub>2" and \<Delta>'': "\<Delta>' = \<Delta>\<^sub>p \<otimes> \<Delta>\<^sub>2" by (cases R) auto
    have p: "fmlookup \<Gamma> x = Some Unbound" if "x |\<in>| fmdom \<Delta>\<^sub>p"
      using match_cases_unbound[OF mc set_zip_leftD[OF b] that] .
    show ?thesis
    proof (cases "x |\<in>| fmdom \<Delta>\<^sub>p")
      case True
      with p show ?thesis by simp
    next
      case False
      with x \<Delta>'' have "x |\<in>| fmdom \<Delta>\<^sub>2" by simp
      from "13.IH"[OF \<sigma> mc refl refl b refl refl R[unfolded R\<^sub>2] this] False
      show ?thesis by simp
    qed
  next
    case False
    with mem x show ?thesis by (auto simp: match_branches_def split: if_splits)
  qed
next
  case (14 \<Sigma> \<Gamma> \<zeta> p s)
  then show ?case by (cases "check_stmt \<Sigma> \<Gamma> \<zeta> s") (auto split: static_outcome.splits)
qed (auto simp: bind_sum_Ok check_unbound_def ensure_def Let_def
     split: option.splits cxt_entry.splits if_splits)

end
