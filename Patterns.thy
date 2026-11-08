(* Pattern checking; matched and remaining types of patterns *)
theory Patterns
  imports Subtyping
begin

definition check_pattern_class :: "cxt \<Rightarrow> name \<Rightarrow> name may_fail"
where
"check_pattern_class \<Gamma> q =
  (case resolve_name \<Gamma> q of
     Some (Type C) \<Rightarrow> if C = range_class then Fail (Violates RulePatConstr RangePattern) else Ok C
   | Some PredefName \<Rightarrow> Fail (SelectsNoRule JudgementCheckPattern (PredefinedNameAsPattern q))
   | _ \<Rightarrow> Fail (SelectsNoRule JudgementCheckPattern (NotClass q)))"

definition pattern_class :: "cxt \<Rightarrow> name \<Rightarrow> name"
where
"pattern_class \<Gamma> q = (case resolve_name \<Gamma> q of Some (Type C) \<Rightarrow> C | _ \<Rightarrow> undefined)"

(* Sub-patterns of a constructor pattern for class C with arguments a, in the order of the fields of C *)
fun field_patterns :: "class_table \<Rightarrow> name \<Rightarrow> pat located args \<Rightarrow> pat located list"
where
"field_patterns \<Sigma> C (ps, kps) =
  ps @ concat (map (\<lambda>x. [p. (y, p) \<leftarrow> kps, y = x]) (drop (length ps) (field_names \<Sigma> C)))"

lemma field_patterns_elem: "p \<in> set (field_patterns \<Sigma> C (ps, kps)) \<Longrightarrow> p \<in> set ps \<or> p \<in> set (map snd kps)"
  by (auto simp: image_iff) (metis snd_conv)

fun disjuncts :: "ty \<Rightarrow> ty list"
where
"disjuncts (TyUnion \<sigma> \<tau>) = disjuncts \<sigma> @ disjuncts \<tau>" |
"disjuncts \<tau> = [\<tau>]"

lemma disjuncts_nonempty: "disjuncts \<tau> \<noteq> []"
  by (induction \<tau> rule: disjuncts.induct) simp_all

fun has_values :: "class_table \<Rightarrow> sequence_kind \<Rightarrow> ty \<Rightarrow> bool"
where
"has_values \<Sigma> k (TyUnion \<sigma> \<tau>) = (has_values \<Sigma> k \<sigma> \<or> has_values \<Sigma> k \<tau>)" |
"has_values \<Sigma> k (TyVar _) = True" |
"has_values \<Sigma> TupleKind (TyTuple _) = True" |
"has_values \<Sigma> ListKind (TyList _) = True" |
"has_values \<Sigma> TupleKind \<tau> = (\<Sigma> \<turnstile> TyTuple [] <: \<tau>)" |
"has_values \<Sigma> ListKind \<tau> = (\<Sigma> \<turnstile> TyList (TyPrim object) <: \<tau>)" |
"has_values \<Sigma> RangeKind \<tau> = (\<Sigma> \<turnstile> TyClass range_class [] <: \<tau>)"

(* Type with float values: float, a float literal type or a type variable, or a type above float *)
fun has_float_values :: "class_table \<Rightarrow> ty \<Rightarrow> bool"
where
"has_float_values \<Sigma> (TyUnion \<sigma> \<tau>) = (has_float_values \<Sigma> \<sigma> \<or> has_float_values \<Sigma> \<tau>)" |
"has_float_values \<Sigma> (TyVar _) = True" |
"has_float_values \<Sigma> (TyLiteral (LitFloat _)) = True" |
"has_float_values \<Sigma> \<tau> = (\<Sigma> \<turnstile> TyPrim float <: \<tau>)"

(* Type with dictionary values: a dictionary type or a type variable, or a type above the dictionary types *)
fun has_dict_values :: "class_table \<Rightarrow> ty \<Rightarrow> bool"
where
"has_dict_values \<Sigma> (TyUnion \<sigma> \<tau>) = (has_dict_values \<Sigma> \<sigma> \<or> has_dict_values \<Sigma> \<tau>)" |
"has_dict_values \<Sigma> (TyVar _) = True" |
"has_dict_values \<Sigma> (TyDict _) = True" |
"has_dict_values \<Sigma> \<tau> = (\<Sigma> \<turnstile> TyDict (TyPrim object) <: \<tau>)"

function (sequential) matched_as :: "class_table \<Rightarrow> cxt \<Rightarrow> ty \<Rightarrow> pat \<Rightarrow> ty"
where
"matched_as \<Sigma> \<Gamma> (TyUnion \<sigma> \<tau>) p = matched_as \<Sigma> \<Gamma> \<sigma> p \<squnion>\<^bsub>\<Sigma>\<^esub> matched_as \<Sigma> \<Gamma> \<tau> p" |
"matched_as \<Sigma> \<Gamma> \<tau> (PatVar _) = \<tau>" |
"matched_as \<Sigma> \<Gamma> \<tau> PatWildcard = \<tau>" |
"matched_as \<Sigma> \<Gamma> \<tau> (PatAs p _) = matched_as \<Sigma> \<Gamma> \<tau> (node p)" |
"matched_as \<Sigma> \<Gamma> \<tau> (PatLiteral (LitFloat _)) = meet \<Sigma> (TyPrim float) \<tau>" |
"matched_as \<Sigma> \<Gamma> \<tau> (PatLiteral l) = meet \<Sigma> (TyLiteral l) \<tau>" |
"matched_as \<Sigma> \<Gamma> (TyTuple \<tau>s) (PatTuple ps) =
  (if length \<tau>s = length ps then TyTuple (map2 (\<lambda>\<tau> p. matched_as \<Sigma> \<Gamma> \<tau> (node p)) \<tau>s ps)
   else TyPrim Never)" |
"matched_as \<Sigma> \<Gamma> (TyList \<tau>) (PatList _) = TyList \<tau>" |
"matched_as \<Sigma> \<Gamma> (TyDict \<tau>) (PatDict _) = TyDict \<tau>" |
"matched_as \<Sigma> \<Gamma> \<tau> (PatConstr q _) =
  (let C = pattern_class \<Gamma> q in
   case instance_at \<Sigma> C \<tau> of Instance \<sigma>s \<Rightarrow> meet \<Sigma> \<tau> (TyClass C \<sigma>s) | _ \<Rightarrow> TyPrim Never)" |
"matched_as \<Sigma> \<Gamma> _ _ = TyPrim Never"
by pat_completeness auto

termination
by (relation "measures [\<lambda>(_, _, _, p). size p, \<lambda>(_, _, \<tau>, _). size \<tau>]")
   (auto elim!: in_set_zipE dest: size_node_elem)

function (sequential) remaining :: "class_table \<Rightarrow> cxt \<Rightarrow> ty \<Rightarrow> pat \<Rightarrow> ty"
where
"remaining \<Sigma> \<Gamma> (TyUnion \<sigma> \<tau>) p = remaining \<Sigma> \<Gamma> \<sigma> p \<squnion>\<^bsub>\<Sigma>\<^esub> remaining \<Sigma> \<Gamma> \<tau> p" |
"remaining \<Sigma> \<Gamma> \<tau> (PatVar _) = TyPrim Never" |
"remaining \<Sigma> \<Gamma> \<tau> PatWildcard = TyPrim Never" |
"remaining \<Sigma> \<Gamma> \<tau> (PatAs p _) = remaining \<Sigma> \<Gamma> \<tau> (node p)" |
"remaining \<Sigma> \<Gamma> (TyLiteral l') (PatLiteral l) = (if l' = l then TyPrim Never else TyLiteral l')" |
"remaining \<Sigma> \<Gamma> (TyPrim bool) (PatLiteral (LitBool b)) = TyLiteral (LitBool (\<not> b))" |
"remaining \<Sigma> \<Gamma> (TyPrim NoneType) (PatLiteral LitNone) = TyPrim Never" |
"remaining \<Sigma> \<Gamma> (TyTuple \<tau>s) (PatTuple ps) =
  (if length \<tau>s = length ps then
     (let \<rho>s = map2 (\<lambda>\<tau> p. remaining \<Sigma> \<Gamma> \<tau> (node p)) \<tau>s ps in
      case filter (\<lambda>i. \<rho>s ! i \<noteq> TyPrim Never) [0..<length \<rho>s] of
        [] \<Rightarrow> TyPrim Never
      | [i] \<Rightarrow> TyTuple (\<tau>s[i := \<rho>s ! i])
      | _ \<Rightarrow> TyTuple \<tau>s)
   else TyTuple \<tau>s)" |
"remaining \<Sigma> \<Gamma> (TyDict _) (PatDict []) = TyPrim Never" |
"remaining \<Sigma> \<Gamma> \<tau> (PatConstr q a) =
  (let C = pattern_class \<Gamma> q in
   case instance_at \<Sigma> C \<tau> of
     Instance \<sigma>s \<Rightarrow>
       if \<Sigma> \<turnstile> \<tau> <: TyClass C \<sigma>s
          \<and> (\<forall>(p, \<sigma>) \<in> set (zip (field_patterns \<Sigma> C a) (field_types \<Sigma> C \<sigma>s)).
               remaining \<Sigma> \<Gamma> \<sigma> (node p) = TyPrim Never)
       then TyPrim Never
       else \<tau>
   | _ \<Rightarrow> \<tau>)" |
"remaining \<Sigma> \<Gamma> \<tau> _ = \<tau>"
by pat_completeness auto

termination
by (relation "measures [\<lambda>(_, _, _, p). size p, \<lambda>(_, _, \<tau>, _). size \<tau>]")
   (auto elim!: in_set_zipE dest!: field_patterns_elem
     dest: size_node_elem size_node_snd_elem')

definition check_unbound :: "cxt \<Rightarrow> var \<Rightarrow> unit may_fail"
where
"check_unbound \<Gamma> x = ensure (fmlookup \<Gamma> x = Some Unbound) (Redeclaration x)"

lemma check_unbound_Ok: "check_unbound \<Gamma> x = Ok () \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound"
  by (simp add: check_unbound_def ensure_def split: if_splits)

(* Bindings of pattern p at a type, joined from ms, the bindings at each disjunct. An entry None in ms means
   that p can't match that disjunct, and binds each variable of p at Never, failing at the first variable which
   is not unbound in \<Gamma>. *)
definition bindings_at ::
  "class_table \<Rightarrow> cxt \<Rightarrow> pat \<Rightarrow> (var, ty) fmap may_fail option list \<Rightarrow> (var, ty) fmap may_fail"
where
"bindings_at \<Sigma> \<Gamma> p ms = do {
   \<Delta>s \<leftarrow> those_sum (map (\<lambda>m. case m of
                             Some m' \<Rightarrow> m'
                           | None \<Rightarrow> do {
                               all_sum (map (check_unbound \<Gamma>) (sorted_list_of_set (binds p)));
                               Ok (fmconst (binds p) (TyPrim Never))
                             })
                    ms);
   Ok (fmmap_keys (\<lambda>x _. joins \<Sigma> (map (\<lambda>\<Delta>. the (fmlookup \<Delta> x)) \<Delta>s)) (hd \<Delta>s))
 }"

(* Variable bound by the bindings of a pattern at the disjuncts of a type, unbound in \<Gamma> if unbound when bound
   at a disjunct *)
lemma bindings_at_unbound:
  assumes "bindings_at \<Sigma> \<Gamma> p (map f (disjuncts \<tau>)) = Ok \<Delta>" and "x |\<in>| fmdom \<Delta>"
    and "\<And>\<sigma> \<Delta>'. \<lbrakk> \<sigma> \<in> set (disjuncts \<tau>) ; f \<sigma> = Some (Ok \<Delta>') ; x |\<in>| fmdom \<Delta>' \<rbrakk> \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound"
  shows "fmlookup \<Gamma> x = Some Unbound"
proof -
  let ?g = "\<lambda>m. case m of
                  Some m' \<Rightarrow> m'
                | None \<Rightarrow> do {
                    all_sum (map (check_unbound \<Gamma>) (sorted_list_of_set (binds p)));
                    Ok (fmconst (binds p) (TyPrim Never))
                  }"
  from assms(1) obtain \<Delta>s where \<Delta>s: "those_sum (map ?g (map f (disjuncts \<tau>))) = Ok \<Delta>s"
    and \<Delta>: "\<Delta> = fmmap_keys (\<lambda>x _. joins \<Sigma> (map (\<lambda>\<Delta>. the (fmlookup \<Delta> x)) \<Delta>s)) (hd \<Delta>s)"
    unfolding bindings_at_def bind_sum_Ok by auto
  from assms(2) \<Delta> have x: "x |\<in>| fmdom (hd \<Delta>s)" by simp
  obtain \<sigma> \<sigma>s where ds: "disjuncts \<tau> = \<sigma> # \<sigma>s" using disjuncts_nonempty by (cases "disjuncts \<tau>") auto
  with those_sum_map_Ok[OF \<Delta>s] obtain \<Delta>' \<Delta>s' where "\<Delta>s = \<Delta>' # \<Delta>s'" and g: "?g (f \<sigma>) = Ok \<Delta>'"
    by (auto simp: list_all2_Cons1)
  with x have x': "x |\<in>| fmdom \<Delta>'" by simp
  show ?thesis
  proof (cases "f \<sigma>")
    case None
    with g have "all_sum (map (check_unbound \<Gamma>) (sorted_list_of_set (binds p))) = Ok ()"
      and "\<Delta>' = fmconst (binds p) (TyPrim Never)"
      by (auto simp: bind_sum_Ok)
    with x' finite_binds_pat[of p] show ?thesis
      by (auto simp: fmlookup_dom_iff fmlookup_fmconst dest: all_sum_Ok[where m = "check_unbound \<Gamma> x"]
          intro: check_unbound_Ok split: if_splits)
  next
    case (Some m)
    with g ds x' show ?thesis by (auto intro: assms(3))
  qed
qed

(* Disjoint union of the bindings of sub-patterns *)
definition pattern_bindings :: "(var, ty) fmap may_fail list \<Rightarrow> (var, ty) fmap may_fail"
where
"pattern_bindings ms = do { \<Delta>s \<leftarrow> those_sum ms; Ok (fold (\<otimes>) \<Delta>s fmempty) }"

(* Variable bound by a disjoint union of bindings, bound by one of them *)
lemma pattern_bindings_dom:
  assumes "pattern_bindings ms = Ok \<Delta>" and "x |\<in>| fmdom \<Delta>"
  obtains \<Delta>' where "Ok \<Delta>' \<in> set ms" and "x |\<in>| fmdom \<Delta>'"
proof -
  from assms(1) obtain \<Delta>s where \<Delta>s: "those_sum ms = Ok \<Delta>s" and \<Delta>: "\<Delta> = fold fmadd \<Delta>s fmempty"
    by (auto simp: pattern_bindings_def bind_sum_Ok)
  from fold_fmadd_dom[of x \<Delta>s fmempty] assms(2) \<Delta> obtain \<Delta>' where "\<Delta>' \<in> set \<Delta>s" and x: "x |\<in>| fmdom \<Delta>'"
    by auto
  then obtain i where i: "i < length \<Delta>s" and "\<Delta>' = \<Delta>s ! i" by (auto simp: in_set_conv_nth)
  with those_sum_Ok[OF \<Delta>s] have "ms ! i = Ok \<Delta>'" and "i < length ms" by (auto simp: list_all2_conv_all_nth)
  then have "Ok \<Delta>' \<in> set ms" by (metis nth_mem)
  with x that show thesis by blast
qed

lemma pattern_bindings_map2_dom:
  assumes "pattern_bindings (map2 f ps \<sigma>s) = Ok \<Delta>" and "x |\<in>| fmdom \<Delta>"
  obtains p \<sigma> \<Delta>' where "(p, \<sigma>) \<in> set (zip ps \<sigma>s)" and "f p \<sigma> = Ok \<Delta>'" and "x |\<in>| fmdom \<Delta>'"
proof -
  from pattern_bindings_dom[OF assms] obtain \<Delta>' where "Ok \<Delta>' \<in> set (map2 f ps \<sigma>s)" and "x |\<in>| fmdom \<Delta>'"
    by blast
  with that show thesis by (auto simp: set_zip in_set_conv_nth) (metis nth_mem nth_zip set_zip_leftD)
qed

lemma pattern_bindings_map_dom:
  assumes "pattern_bindings (map f ps) = Ok \<Delta>" and "x |\<in>| fmdom \<Delta>"
  obtains p \<Delta>' where "p \<in> set ps" and "f p = Ok \<Delta>'" and "x |\<in>| fmdom \<Delta>'"
proof -
  from pattern_bindings_dom[OF assms] obtain \<Delta>' where "Ok \<Delta>' \<in> set (map f ps)" and x: "x |\<in>| fmdom \<Delta>'"
    by blast
  then obtain p where p: "p \<in> set ps" and "Ok \<Delta>' = f p" by auto
  from that[OF p this(2)[symmetric] x] show thesis .
qed

function
  check_pat :: "class_table \<Rightarrow> cxt \<Rightarrow> pat \<Rightarrow> ty \<Rightarrow> (var, ty) fmap may_fail" and
  check_pat_at :: "class_table \<Rightarrow> cxt \<Rightarrow> pat located \<Rightarrow> ty \<Rightarrow> (var, ty) fmap may_fail"
where
"check_pat \<Sigma> \<Gamma> PatWildcard \<tau> = Ok fmempty" |
"check_pat \<Sigma> \<Gamma> (PatVar x) \<tau> = by_rule RuleCheckVar (do { check_unbound \<Gamma> x; Ok (fmupd x \<tau> fmempty) })" |
"check_pat \<Sigma> \<Gamma> (PatAs p x) \<tau> =
  by_rule RuleCheckAs (do {
    check_unbound \<Gamma> x; \<Delta> \<leftarrow> check_pat_at \<Sigma> \<Gamma> p \<tau>;
    Ok (\<Delta> \<otimes> fmupd x (matched_as \<Sigma> \<Gamma> \<tau> (node p)) fmempty)
  })" |
"check_pat \<Sigma> \<Gamma> (PatLiteral l) \<tau> =
  by_rule RuleCheckLiteral (do {
    ensure (\<not> (is_int_lit l \<and> has_float_values \<Sigma> \<tau>)) (IntLiteralFloatValues \<tau>); Ok fmempty
  })" |
"check_pat \<Sigma> \<Gamma> (PatTuple ps) \<tau> = do {
   by_rule RuleCheckTupleNone (do {
     ensure (\<not> has_values \<Sigma> ListKind \<tau>) (SequenceKindMismatch TupleKind \<tau> ListKind);
     ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch TupleKind \<tau> RangeKind)
   });
   bindings_at \<Sigma> \<Gamma> (PatTuple ps)
     (map (\<lambda>\<sigma>. case \<sigma> of
                 TyTuple \<sigma>s \<Rightarrow>
                   if length \<sigma>s = length ps then Some (pattern_bindings (map2 (check_pat_at \<Sigma> \<Gamma>) ps \<sigma>s))
                   else None
               | _ \<Rightarrow> None)
       (disjuncts \<tau>))
 }" |
"check_pat \<Sigma> \<Gamma> (PatList ps) \<tau> = do {
   by_rule RuleCheckListNone (do {
     ensure (\<not> has_values \<Sigma> TupleKind \<tau>) (SequenceKindMismatch ListKind \<tau> TupleKind);
     ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch ListKind \<tau> RangeKind)
   });
   bindings_at \<Sigma> \<Gamma> (PatList ps)
     (map (\<lambda>\<sigma>. case \<sigma> of
                 TyList \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p. check_pat_at \<Sigma> \<Gamma> p \<sigma>') ps))
               | _ \<Rightarrow> None)
       (disjuncts \<tau>))
 }" |
"check_pat \<Sigma> \<Gamma> (PatDict kps) \<tau> =
  bindings_at \<Sigma> \<Gamma> (PatDict kps)
    (map (\<lambda>\<sigma>. case \<sigma> of
                TyDict \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p. check_pat_at \<Sigma> \<Gamma> p \<sigma>') (map snd kps)))
              | _ \<Rightarrow>
                  if has_dict_values \<Sigma> \<sigma> then Some (Fail (Violates RuleCheckDictNone (DictPatternDictValues \<sigma>)))
                  else None)
      (disjuncts \<tau>))" |
"check_pat \<Sigma> \<Gamma> (PatConstr q (ps, kps)) \<tau> = by_rule RuleCheckConstr (do {
   C \<leftarrow> check_pattern_class \<Gamma> q;
   check_field_map (PatternArityMismatch (short_name C)) (UnknownFieldInPattern (short_name C))
     (field_names \<Sigma> C) (length ps) (map fst kps);
   bindings_at \<Sigma> \<Gamma> (PatConstr q (ps, kps))
     (map (\<lambda>\<sigma>. case instance_at \<Sigma> C \<sigma> of
                 Instance \<sigma>s \<Rightarrow>
                   Some (pattern_bindings
                     (map2 (check_pat_at \<Sigma> \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s)))
               | NoInstance \<Rightarrow> None
               | Undetermined \<Rightarrow>
                   Some (Fail (Violates
                     (if instance_above \<Sigma> C \<sigma> = Undetermined then RuleInstanceAbove else RuleInstanceBelow)
                     (PatternClassUndetermined (short_name C) \<sigma>))))
       (disjuncts \<tau>))
 })" |

"check_pat_at \<Sigma> \<Gamma> (At p q) \<tau> = locate p (check_pat \<Sigma> \<Gamma> q \<tau>)"
by pat_completeness auto

termination
by (relation "measure (\<lambda>x. case x of Inl (_, _, p, _) \<Rightarrow> size p | Inr (_, _, p, _) \<Rightarrow> size_located size p)")
   (auto elim!: in_set_zipE dest!: field_patterns_elem
     dest: size_node_elem size_node_snd_elem size_node_snd_elem'
     simp del: field_patterns.simps)

lemma check_pat_unbound:
  "check_pat \<Sigma> \<Gamma> p \<tau> = Ok \<Delta> \<Longrightarrow> x |\<in>| fmdom \<Delta> \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound"
  "check_pat_at \<Sigma> \<Gamma> p' \<tau>' = Ok \<Delta>' \<Longrightarrow> x |\<in>| fmdom \<Delta>' \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound"
proof (induction \<Sigma> \<Gamma> p \<tau> and \<Sigma> \<Gamma> p' \<tau>' arbitrary: \<Delta> and \<Delta>' rule: check_pat_check_pat_at.induct)
  case (2 \<Sigma> \<Gamma> y \<tau>)
  then show ?case by (auto simp: bind_sum_Ok dest: check_unbound_Ok split: if_splits)
next
  case (3 \<Sigma> \<Gamma> p y \<tau>)
  then show ?case by (auto simp: bind_sum_Ok dest: check_unbound_Ok)
next
  case (5 \<Sigma> \<Gamma> ps \<tau>)
  from "5.prems"(1) obtain z where z: "by_rule RuleCheckTupleNone
      (ensure (\<not> has_values \<Sigma> ListKind \<tau>) (SequenceKindMismatch TupleKind \<tau> ListKind) \<bind>
       (\<lambda>_. ensure (\<not> has_values \<Sigma> RangeKind \<tau>) (SequenceKindMismatch TupleKind \<tau> RangeKind))) = Ok z"
    by (auto simp: bind_sum_Ok)
  from "5.prems" show ?case
    apply (clarsimp simp: bind_sum_Ok)
    apply (erule bindings_at_unbound, assumption)
    apply (auto split: ty.splits if_splits elim!: pattern_bindings_map2_dom intro: "5.IH"[OF z])
    done
next
  case (6 \<Sigma> \<Gamma> ps \<tau>)
  from "6.prems" show ?case
    apply (clarsimp simp: bind_sum_Ok)
    apply (erule bindings_at_unbound, assumption)
    apply (auto split: ty.splits if_splits elim!: pattern_bindings_map_dom intro: "6.IH")
    done
next
  case (7 \<Sigma> \<Gamma> kps \<tau>)
  have IH: "fmlookup \<Gamma> x = Some Unbound"
    if "TyDict \<sigma> \<in> set (disjuncts \<tau>)" and "(w, p) \<in> set kps" and "check_pat_at \<Sigma> \<Gamma> p \<sigma> = Ok \<Delta>'"
      and "x |\<in>| fmdom \<Delta>'"
    for \<sigma> w p \<Delta>'
  proof -
    from that(2) have "p \<in> set (map snd kps)" by (auto intro: rev_image_eqI)
    from "7.IH"[OF that(1) refl this that(3, 4)] show ?thesis .
  qed
  from "7.prems" show ?case
    apply (clarsimp simp: bind_sum_Ok)
    apply (erule bindings_at_unbound, assumption)
    apply (auto split: ty.splits if_splits elim!: pattern_bindings_map_dom intro: IH)
    done
next
  case (8 \<Sigma> \<Gamma> q ps kps \<tau>)
  from "8.prems" show ?case
    apply (clarsimp simp: bind_sum_Ok)
    apply (erule bindings_at_unbound, assumption)
    apply (auto split: instances.splits if_splits elim!: pattern_bindings_map2_dom intro: "8.IH")
    done
qed (auto simp: bind_sum_Ok)

end
