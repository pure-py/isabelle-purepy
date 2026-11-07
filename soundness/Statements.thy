(* Soundness of statement evaluation *)
theory Statements
  imports SoundExpr
begin

type_synonym elif_block = "(expr located \<times> stmt located) list \<times> stmt located option"

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

(* Return type over the type variables bound by \<eta> *)
fun wf_return :: "(var \<times> ty) list \<Rightarrow> ty option \<Rightarrow> bool"
where
"wf_return \<eta> (Some \<tau>) = (fv \<tau> \<subseteq> fst ` set \<eta>)" |
"wf_return \<eta> None = True"

fun bindings_of :: "static_outcome \<Rightarrow> cxt option"
where
"bindings_of (Assigns\<^sub>R \<Delta> _) = Some \<Delta>" |
"bindings_of Returns\<^sub>R = None"

lemma check_stmt_at_Ok:
  assumes "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R"
  shows "\<exists>R'. check_stmt \<Sigma> \<Gamma> \<zeta> (node s) = Ok R' \<and> bindings_of R' = bindings_of R"
proof (cases s)
  case (At p s')
  then show ?thesis using assms by (cases "check_stmt \<Sigma> \<Gamma> \<zeta> s'") (auto split: static_outcome.splits)
qed

lemma bind_sum_Ok: "bind_sum m f = Ok y \<longleftrightarrow> (\<exists>x. m = Ok x \<and> f x = Ok y)"
  by (cases m) simp_all

lemma fmlookup_fmconst: "finite A \<Longrightarrow> fmlookup (fmconst A u) x = (if x \<in> A then Some u else None)"
proof -
  assume "finite A"
  then obtain xs where A: "A = set xs" using finite_list by blast
  have "fmlookup (fold (\<lambda>x. fmupd x u) xs m) x = (if x \<in> set xs then Some u else fmlookup m x)" for m
    by (induction xs arbitrary: m) auto
  then show ?thesis by (simp add: A fmconst_code)
qed

lemma Ok_bind_sum: "Ok y = bind_sum m f \<longleftrightarrow> (\<exists>x. m = Ok x \<and> f x = Ok y)"
  by (cases m) auto

lemma Ok_in_set_map2: "Ok y \<in> set (map2 f xs zs) \<Longrightarrow> \<exists>x z. (x, z) \<in> set (zip xs zs) \<and> f x z = Ok y"
  by (auto simp: set_zip in_set_conv_nth) (metis)

lemma check_unbound_Ok: "check_unbound \<Gamma> x = Ok () \<Longrightarrow> fmlookup \<Gamma> x = Some Unbound"
  by (simp add: check_unbound_def ensure_def split: if_splits)

lemma finite_binds_pat: "finite (binds_pat p)"
  by (induction p rule: binds_pat.induct) auto

lemma disjuncts_nonempty: "disjuncts \<tau> \<noteq> []"
  by (induction \<tau> rule: disjuncts.induct) simp_all

lemma fold_fmadd_dom: "x |\<in>| fmdom (fold fmadd \<Delta>s \<Delta>) \<Longrightarrow> x |\<in>| fmdom \<Delta> \<or> (\<exists>\<Delta>' \<in> set \<Delta>s. x |\<in>| fmdom \<Delta>')"
proof (induction \<Delta>s arbitrary: \<Delta>)
  case (Cons \<Delta>' \<Delta>s)
  from Cons.IH[of "\<Delta>' \<otimes> \<Delta>"] Cons.prems show ?case by auto
qed simp

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
qed auto

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

lemma merge_dom: "merge \<Sigma> X \<Gamma> \<Gamma>' = Ok \<Gamma>'' \<Longrightarrow> fmdom \<Gamma>'' = fmdom (\<Gamma> \<otimes> \<Gamma>')"
  by (auto simp: merge_def Let_def split: if_splits)

lemma merge_outcome_dom:
  assumes "merge_outcome \<Sigma> X R R' = Ok (Assigns\<^sub>R \<Delta> r)" and "x |\<in>| fmdom \<Delta>"
  shows "(\<exists>\<Delta>' r'. R = Assigns\<^sub>R \<Delta>' r' \<and> x |\<in>| fmdom \<Delta>') \<or> (\<exists>\<Delta>' r'. R' = Assigns\<^sub>R \<Delta>' r' \<and> x |\<in>| fmdom \<Delta>')"
  using assms by (cases "(\<Sigma>, X, R, R')" rule: merge_outcome.cases) (auto simp: bind_sum_Ok dest: merge_dom)

(* Variable bound by a merge of static outcomes, bound by one of them *)
lemma merges_dom:
  assumes "merges \<Sigma> X ms = Ok (Assigns\<^sub>R \<Delta> r)" and "x |\<in>| fmdom \<Delta>"
  obtains \<Delta>' r' where "Ok (Assigns\<^sub>R \<Delta>' r') \<in> set ms" and "x |\<in>| fmdom \<Delta>'"
proof -
  let ?f = "\<lambda>R m. do { R' \<leftarrow> m; merge_outcome \<Sigma> X R R' }"
  from assms(1) obtain Rs where Rs: "those_sum ms = Ok Rs" and fold: "foldr ?f Rs (Ok Returns\<^sub>R) = Ok (Assigns\<^sub>R \<Delta> r)"
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
qed (auto simp: bind_sum_Ok check_unbound_def ensure_def Let_def split: option.splits cxt_entry.splits if_splits)

lemma tyvars_fmconst: "tyvars (fmconst (set \<alpha>s) TypeVar) \<subseteq> set \<alpha>s"
  by (auto simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff fmlookup_fmconst split: if_splits)

lemma redeclared_None: "redeclared f X xs = None \<Longrightarrow> distinct (map f xs) \<and> set (map f xs) \<inter> X = {}"
  by (induction xs arbitrary: X) (auto split: if_splits)

context evaluation
begin

(* Completion of a statement checked at \<Gamma> and return type \<zeta> with static outcome R, run in \<rho> *)
fun wf_completion :: "(var \<times> ty) list \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> completion \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Assigns \<rho>') R =
  (\<exists>\<Delta>. bindings_of R = Some \<Delta> \<and> fmdom \<rho>' |\<subseteq>| fmdom \<Delta> \<and> \<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>)" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Returns v) R = (\<forall>\<tau>. \<zeta> = Some \<tau> \<longrightarrow> \<turnstile> v : Ty (inst \<eta> \<tau>))" |
"wf_completion \<eta> \<rho> \<Gamma> \<zeta> (Aborts\<^sub>\<omega> \<kappa>) R = (\<not> prevented \<kappa>)"

fun wf_outcome :: "(var \<times> ty) list \<Rightarrow> env \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> outcome \<Rightarrow> static_outcome \<Rightarrow> bool"
where
"wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (vs, \<omega>) R = wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R"

lemma wf_completion_bindings:
  "bindings_of R = bindings_of R' \<Longrightarrow> wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R = wf_completion \<eta> \<rho> \<Gamma> \<zeta> \<omega> R'"
  by (cases \<omega>) simp_all

definition sound_stmt :: "env \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_stmt \<rho> s o =
  (\<forall>\<eta> \<Gamma> \<zeta> R. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<eta> \<zeta> \<longrightarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s = Ok R
     \<longrightarrow> wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R)"

definition sound_elif :: "env \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"
where
"sound_elif \<rho> eb o =
  (\<forall>\<eta> \<Gamma> \<zeta> Rs. \<eta> \<turnstile> \<rho> : \<Gamma> \<longrightarrow> wf_return \<eta> \<zeta> \<longrightarrow> those_sum (check_elif \<Sigma> \<Gamma> \<zeta> eb) = Ok Rs
     \<longrightarrow> (\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R))"

lemma sound_stmt_at:
  assumes "sound_stmt \<rho> (node s) o" and "\<eta> \<turnstile> \<rho> : \<Gamma>" and "wf_return \<eta> \<zeta>"
    and "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R"
proof -
  from assms(4) obtain R' where "check_stmt \<Sigma> \<Gamma> \<zeta> (node s) = Ok R'" and R': "bindings_of R' = bindings_of R"
    by (blast dest: check_stmt_at_Ok)
  with assms(1-3) have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'" unfolding sound_stmt_def by simp
  then show ?thesis by (cases o) (simp add: wf_completion_bindings[OF R'])
qed

subsection \<open>Statements\<close>

lemma pass_sound: "sound_stmt \<rho> StmtPass (assigns\<^sub>o \<epsilon>)"
  by (simp add: sound_stmt_def)

lemma declare_sound: "sound_stmt \<rho> (StmtDeclare x \<psi>) (assigns\<^sub>o \<epsilon>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtDeclare x \<psi>) = Ok R"
  from chk obtain \<tau> where \<tau>: "resolve_type \<Sigma> \<Gamma> \<psi> = Ok \<tau>" and R: "R = Assigns\<^sub>R (fmupd x (DU \<tau>) fmempty) None"
    and "fmlookup \<Gamma> x = Some Unbound"
    by (auto simp: bind_sum_def check_unbound_def ensure_def split: sum.splits if_splits)
  with env have "fmlookup \<rho> x = Some VUnbound" by (auto dest!: wf_env_lookup wf_val_unbound wf_val_du)
  moreover have "fv \<tau> \<subseteq> fst ` set \<eta>" using env resolve_type_tyvars[OF \<tau>] by (rule wf_env_fv)
  ultimately have "\<eta> \<turnstile> \<rho> : fmupd x (DU \<tau>) \<Gamma>" using env by (intro wf_env_upd_cxt) (auto intro: ValUnbound)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<epsilon>) R" by (simp add: R)
qed

lemma assign_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtAssign x \<pi> e) (mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>)))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x \<pi> e) = Ok R"
  from chk obtain \<tau> where chk_e: "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()"
    and R: "R = Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty) None" and fv_\<Gamma>: "fv \<tau> \<subseteq> tyvars \<Gamma>"
    by (cases \<pi>)
       (auto simp: bind_sum_def check_unbound_def ensure_def
        split: sum.splits option.splits cxt_entry.splits if_splits dest: tyvars_entry resolve_type_tyvars)
  from env fv_\<Gamma> have fv: "fv \<tau> \<subseteq> fst ` set \<eta>" by (rule wf_env_fv)
  show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>))) R"
  proof (cases r)
    case (Val v)
    with assms env chk_e fv have "\<turnstile> v : Ty (inst \<eta> \<tau>)" by (auto dest: sound_expr_check_at)
    then have "\<eta> \<turnstile> fmupd x v \<rho> : fmupd x (Ty \<tau>) \<Gamma>" using env fv by (intro wf_env_upd) auto
    then show ?thesis by (simp add: Val R)
  next
    case (Aborts \<kappa>)
    with assms env chk_e fv show ?thesis by (auto simp: R dest: sound_expr_check_at)
  qed
qed

(* An expression statement synthesises or is a call statement *)
lemma check_expr_stmt:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) = Ok R"
  shows "R = Assigns\<^sub>R fmempty None \<and> (\<exists>\<tau>. has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>)"
proof (cases e)
  case (At p e')
  show ?thesis
  proof (cases e')
    case (ExprCall e'' a)
    then obtain es kws where a: "a = (es, kws)" by (cases a)
    show ?thesis
      using assms
      by (cases "lambda_of (node e'') = None \<and> class_of_name \<Gamma> (node e'') = None")
         (auto simp: At ExprCall a has_type_def bind_sum_def split: sum.splits)
  qed (use assms in \<open>auto simp: At has_type_def bind_sum_def split: sum.splits\<close>)
qed

lemma expr_stmt_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtExpr e) (mlet r (\<lambda>v. assigns\<^sub>o \<epsilon>))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) = Ok R"
  from check_expr_stmt[OF chk] obtain \<tau> where R: "R = Assigns\<^sub>R fmempty None" and "has_type_at \<Sigma> \<eta> \<Gamma> e \<tau>"
    by blast
  with assms env have "result_typed r (inst \<eta> \<tau>)" by (auto dest: sound_expr_has_type_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. assigns\<^sub>o \<epsilon>)) R" using env by (cases r) (simp_all add: R)
qed

lemma print_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtPrint e) (mlet r (\<lambda>v. ([v], Assigns \<epsilon>)))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtPrint e) = Ok R"
  then obtain \<tau> where R: "R = Assigns\<^sub>R fmempty None" and "synth_expr_at \<Sigma> \<Gamma> e = Ok \<tau>"
    by (auto simp: bind_sum_def ensure_def split: sum.splits if_splits)
  with assms env have "result_typed r (inst \<eta> \<tau>)" by (auto dest: sound_expr_synth_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r (\<lambda>v. ([v], Assigns \<epsilon>))) R" using env by (cases r) (simp_all add: R)
qed

lemma return_sound:
  assumes "sound_expr \<rho> (node e) r"
  shows "sound_stmt \<rho> (StmtReturn (Some e)) (mlet r returns\<^sub>o)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn (Some e)) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with ret have fv: "fv \<tau> \<subseteq> fst ` set \<eta>" by simp
  from chk \<zeta> have "check_expr_at \<Sigma> \<Gamma> e \<tau> = Ok ()" by (auto simp: bind_sum_def split: sum.splits)
  with assms env fv have "result_typed r (inst \<eta> \<tau>)" by (auto dest: sound_expr_check_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (mlet r returns\<^sub>o) R" by (cases r) (simp_all add: \<zeta>)
qed

lemma return_none_sound: "sound_stmt \<rho> (StmtReturn None) (returns\<^sub>o (VLit LitNone))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn None) = Ok R"
  from chk obtain \<tau> where \<zeta>: "\<zeta> = Some \<tau>" by (cases \<zeta>) auto
  with chk have "\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>" by (auto split: if_splits)
  then have "\<turnstile> VLit LitNone : Ty (inst \<eta> \<tau>)"
    by (intro ValSub[OF ValLit] SubtyLiteral)
       (auto dest: subst_subty'[where \<tau>s = "map snd \<eta>" and \<alpha>s = "map fst \<eta>"])
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (returns\<^sub>o (VLit LitNone)) R" by (simp add: \<zeta>)
qed

(* Free type variables of a function signature, among the type variables of the context *)
lemma def_signature_fv:
  assumes "def_signature \<Sigma> \<Gamma> d = Ok \<pi>"
  shows "fv_scheme \<pi> \<subseteq> tyvars \<Gamma>"
proof (cases d)
  case (Def f \<alpha>s xps \<psi> s)
  let ?\<Gamma>' = "\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar"
  from assms Def obtain \<sigma>s \<tau> where \<sigma>s: "those_sum (map (resolve_type \<Sigma> ?\<Gamma>' \<circ> snd) xps) = Ok \<sigma>s"
    and \<tau>: "resolve_type \<Sigma> ?\<Gamma>' \<psi> = Ok \<tau>" and \<pi>: "\<pi> = TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>)"
    by (auto simp: Let_def bind_sum_def split: sum.splits option.splits)
  have \<Gamma>': "tyvars ?\<Gamma>' \<subseteq> tyvars \<Gamma> \<union> set \<alpha>s" using tyvars_add tyvars_fmconst by blast
  have "fv \<sigma> \<subseteq> tyvars ?\<Gamma>'" if "\<sigma> \<in> set \<sigma>s" for \<sigma>
  proof -
    from that obtain i where "i < length \<sigma>s" and "\<sigma> = \<sigma>s ! i" by (auto simp: in_set_conv_nth)
    with those_sum_map_Ok[OF \<sigma>s] have "resolve_type \<Sigma> ?\<Gamma>' (snd (xps ! i)) = Ok \<sigma>"
      by (auto simp: list_all2_conv_all_nth)
    then show ?thesis by (rule resolve_type_tyvars)
  qed
  with resolve_type_tyvars[OF \<tau>] \<Gamma>' show ?thesis by (auto simp: \<pi>)
qed

lemma def_signature_disjoint:
  "def_signature \<Sigma> \<Gamma> d = Ok \<pi> \<Longrightarrow> case d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}"
  by (cases d) (auto simp: Let_def bind_sum_def find_None_iff split: sum.splits option.splits)

lemma defs_sound:
  assumes vs: "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]"
  shows "sound_stmt \<rho> (StmtMutualRegion ds) (assigns\<^sub>o (fmap_of_list (zip (map (def_name \<circ> node) ds) vs)))"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMutualRegion ds) = Ok R"
  let ?xs = "map (def_name \<circ> node) ds"
  from chk obtain \<pi>s where red: "redeclared node {} (map (\<lambda>d. At (pos_of d) (def_name (node d))) ds) = None"
    and sigs: "those_sum (map (\<lambda>d. locate (pos_of d) (def_signature \<Sigma> \<Gamma> (node d))) ds) = Ok \<pi>s"
    and defs: "all_sum (map2 (check_def_at \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip ?xs (map signature_entry \<pi>s)))) ds \<pi>s)
                = Ok ()"
    and R: "R = Assigns\<^sub>R (fmap_of_list (zip ?xs (map signature_entry \<pi>s))) None"
    by (auto simp: Let_def bind_sum_def split: sum.splits option.splits)
  let ?\<Delta> = "fmap_of_list (zip ?xs (map signature_entry \<pi>s))"
  let ?\<rho>' = "fmap_of_list (zip ?xs vs)"
  have sig: "def_signature \<Sigma> \<Gamma> (node (ds ! i)) = Ok (\<pi>s ! i)" if "i < length ds" for i
    using those_sum_map_Ok[OF sigs] that by (simp add: list_all2_conv_all_nth)
  have len: "length \<pi>s = length ds" using those_sum_map_Ok[OF sigs] by (simp add: list_all2_lengthD)
  from redeclared_None[OF red] have distinct: "distinct ?xs" by (simp add: comp_def)
  have fv: "\<forall>\<pi> \<in> set \<pi>s. fv_scheme \<pi> \<subseteq> fst ` set \<eta>"
  proof
    fix \<pi>
    assume "\<pi> \<in> set \<pi>s"
    then obtain i where i: "i < length ds" and \<pi>: "\<pi> = \<pi>s ! i" using len by (auto simp: in_set_conv_nth)
    from def_signature_fv[OF sig[OF i]] \<pi> wf_env_tyvars[OF env] show "fv_scheme \<pi> \<subseteq> fst ` set \<eta>" by blast
  qed
  have disjoint: "\<forall>d \<in> set ds. case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}"
  proof
    fix d
    assume "d \<in> set ds"
    then obtain i where i: "i < length ds" and d: "d = ds ! i" by (auto simp: in_set_conv_nth)
    from sig[OF i] d have "def_signature \<Sigma> \<Gamma> (node d) = Ok (\<pi>s ! i)" by simp
    then show "case node d of Def _ \<alpha>s _ _ _ \<Rightarrow> set \<alpha>s \<inter> tyvars \<Gamma> = {}" by (rule def_signature_disjoint)
  qed
  (* Entry of the i-th definition, typing its closure *)
  have entry: "\<turnstile> Def(\<rho>, ds, i) : inst_entry \<eta> (signature_entry (\<pi>s ! i))" if "i < length ds" for i
  proof -
    obtain \<alpha>s \<tau> where \<pi>: "\<pi>s ! i = TyScheme \<alpha>s \<tau>" by (cases "\<pi>s ! i")
    from ValDef[OF env sigs refl defs fv disjoint that \<pi>] \<pi> show ?thesis by simp
  qed
  have lookup: "\<exists>i < length ds. ?xs ! i = x \<and> \<theta> = signature_entry (\<pi>s ! i)" if "fmlookup ?\<Delta> x = Some \<theta>" for x \<theta>
  proof -
    from that have "(x, \<theta>) \<in> set (zip ?xs (map signature_entry \<pi>s))"
      by (auto simp: fmlookup_of_list dest: map_of_SomeD)
    with len show ?thesis by (force simp: in_set_zip)
  qed
  have "\<eta> \<turnstile> \<rho> \<otimes> ?\<rho>' : \<Gamma> \<otimes> ?\<Delta>"
  proof (rule wf_env_add[OF env])
    have "tyvars ?\<Delta> \<subseteq> \<Union> (fv_scheme ` set \<pi>s)"
    proof
      fix \<alpha>
      assume "\<alpha> \<in> tyvars ?\<Delta>"
      then obtain x \<theta> where look: "fmlookup ?\<Delta> x = Some \<theta>" and \<alpha>: "\<alpha> \<in> fv_entry \<theta> \<or> \<theta> = TypeVar"
        by (auto simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff)
      from lookup[OF look] obtain i where i: "i < length ds" and \<theta>: "\<theta> = signature_entry (\<pi>s ! i)" by blast
      obtain \<alpha>s \<tau> where \<pi>i: "\<pi>s ! i = TyScheme \<alpha>s \<tau>" by (cases "\<pi>s ! i")
      from \<alpha> \<theta> \<pi>i have "\<alpha> \<in> fv_scheme (\<pi>s ! i)" by (cases \<alpha>s) auto
      with i len show "\<alpha> \<in> \<Union> (fv_scheme ` set \<pi>s)" by (metis UN_I nth_mem)
    qed
    with fv show "tyvars ?\<Delta> \<subseteq> fst ` set \<eta>" by blast
    show "fmdom ?\<rho>' |\<subseteq>| fmdom ?\<Delta>" using len by (simp add: vs)
  next
    fix x \<theta>
    assume "fmlookup ?\<Delta> x = Some \<theta>"
    then obtain i where i: "i < length ds" and x: "?xs ! i = x" and \<theta>: "\<theta> = signature_entry (\<pi>s ! i)"
      by (blast dest: lookup)
    have "fmlookup ?\<rho>' x = Some (vs ! i)"
      using map_of_zip_nth[of ?xs vs i] distinct i x by (simp add: vs fmlookup_of_list)
    moreover from fmdomI[OF this] have "x |\<in>| fmdom ?\<rho>'" .
    ultimately have "fmlookup (\<rho> \<otimes> ?\<rho>') x = Some (vs ! i)" by (simp only: fmlookup_add if_True)
    with entry[OF i] i \<theta> show "\<exists>v. fmlookup (\<rho> \<otimes> ?\<rho>') x = Some v \<and> \<turnstile> v : inst_entry \<eta> \<theta>"
      by (simp add: vs)
  next
    fix x \<pi>
    assume "fmlookup ?\<Delta> x = Some (Scheme \<pi>)"
    then obtain i where i: "i < length ds" and \<pi>: "Scheme \<pi> = signature_entry (\<pi>s ! i)" by (blast dest: lookup)
    obtain \<alpha>s \<tau> where \<pi>i: "\<pi>s ! i = TyScheme \<alpha>s \<tau>" by (cases "\<pi>s ! i")
    from def_signatures_callable[OF sigs i \<pi>i] \<pi> \<pi>i show "callable_scheme \<pi>"
      by (cases \<alpha>s) auto
  qed
  moreover have "fmdom ?\<rho>' |\<subseteq>| fmdom ?\<Delta>" using len by (simp add: vs)
  ultimately show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o ?\<rho>') R" by (simp add: R)
qed

(* Static outcome of an assertion whose condition does not evaluate to false: the condition checks as a Boolean
   and nothing is assigned *)
lemma check_assert:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R" and "\<rho>, node e \<Rightarrow>\<^sub>e r" and "r \<noteq> Val false"
  shows "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok () \<and> (\<exists>r'. R = Assigns\<^sub>R fmempty r')"
  using assms by (auto simp: Let_def bind_sum_def split: sum.splits option.splits if_splits dest: literal_false)

lemma assert_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val true"
  shows "sound_stmt \<rho> (StmtAssert e e') (assigns\<^sub>o \<epsilon>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R"
  from check_assert[OF chk assms] obtain r where "R = Assigns\<^sub>R fmempty r" by auto
  with env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (assigns\<^sub>o \<epsilon>) R" by simp
qed

lemma assert_false_sound: "sound_stmt \<rho> (StmtAssert e e') (aborts\<^sub>o (AssertionError w))"
  by (simp add: sound_stmt_def)

lemma assert_fail_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa>" and "sound_expr \<rho> (node e) (Aborts \<kappa>)"
  shows "sound_stmt \<rho> (StmtAssert e e') (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R"
  from check_assert[OF chk assms(1)] have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()" by simp
  with assms(2) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R" by (auto dest: prim_operand)
qed

lemma assert_nonbool_sound:
  assumes "\<rho>, node e \<Rightarrow>\<^sub>e Val v" and "sound_expr \<rho> (node e) (Val v)" and "v \<notin> {true, false}"
  shows "sound_stmt \<rho> (StmtAssert e e') (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = Ok R"
  from check_assert[OF chk assms(1)] assms(3) have "check_expr_at \<Sigma> \<Gamma> e (TyPrim bool) = Ok ()" by simp
  with assms(2, 3) env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o Excluded) R" by (auto dest!: bool_operand)
qed

lemma assert_msg_false_fail_sound:
  assumes "sound_expr \<rho> (node e') (Aborts \<kappa>)"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert_msg[OF chk] assms env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o \<kappa>) R"
    by (auto dest: prim_operand)
qed

lemma assert_msg_nonstr_sound:
  assumes "sound_expr \<rho> (node e') (Val v)" and "\<forall>w. v \<noteq> VLit (LitString w)"
  shows "sound_stmt \<rho> (StmtAssert e (Some e')) (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e (Some e')) = Ok R"
  from check_assert_msg[OF chk] assms env show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (aborts\<^sub>o Excluded) R"
    by (auto dest!: str_operand)
qed

(* Soundness at one branch of an if statement carries to the merge of the branches *)
lemma wf_outcome_merge_if:
  assumes "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" and "R \<in> set Rs"
    and "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and "merges \<Sigma> X (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R'" and "\<eta> \<turnstile> \<rho> : \<Gamma>"
  shows "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
  sorry

lemma check_if:
  assumes "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  shows "\<exists>Rs. those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs
     \<and> merges \<Sigma> (set (declares (StmtIf e s elifs else')))
         (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R"
  using assms by (auto simp: check_stmt_if bind_sum_def split: sum.splits dest: merges_Ok)

lemma if_true_sound:
  assumes "sound_expr \<rho> (node e) (Val true)" and "sound_stmt \<rho> (node s) o"
  shows "sound_stmt \<rho> (StmtIf e s elifs else') o"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  from check_if[OF chk] obtain Rs
    where Rs: "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and R: "merges \<Sigma> (set (declares (StmtIf e s elifs else')))
              (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R"
    by blast
  from Rs obtain R0 where R0: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R0" and "R0 \<in> set Rs"
    by (auto simp: bind_sum_def split: sum.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R0" using assms(2) env ret R0 by (rule sound_stmt_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using \<open>R0 \<in> set Rs\<close> Rs R env by (rule wf_outcome_merge_if)
qed

lemma if_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_elif \<rho> (elifs, else') o"
  shows "sound_stmt \<rho> (StmtIf e s elifs else') o"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = Ok R"
  from check_if[OF chk] obtain Rs
    where Rs: "those_sum (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs"
    and R: "merges \<Sigma> (set (declares (StmtIf e s elifs else')))
              (check_stmt_at \<Sigma> \<Gamma> \<zeta> s # check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok R"
    by blast
  from Rs obtain R0 Rs' where Rs': "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs'" and "Rs = R0 # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  with assms(2) env ret obtain R' where "R' \<in> set Rs'" and "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R'"
    unfolding sound_elif_def by blast
  moreover from this(1) have "R' \<in> set Rs" by (simp add: \<open>Rs = R0 # Rs'\<close>)
  ultimately show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using Rs R env by (blast intro: wf_outcome_merge_if)
qed

lemma if_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def by (auto simp: check_stmt_if bind_sum_def dest: prim_operand split: sum.splits)

lemma if_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtIf e s elifs else') (aborts\<^sub>o Excluded)"
  unfolding sound_stmt_def by (auto simp: check_stmt_if bind_sum_def dest!: bool_operand split: sum.splits)

lemma match_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; dispatch \<rho> v cases = Val (\<rho>', s') ; sound_stmt (\<rho> \<otimes> \<rho>') (node s') o \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (assigns\<^sub>o \<rho>' \<otimes> o)"
  sorry

lemma match_fail_sound: "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
  unfolding sound_stmt_def by (auto simp: bind_sum_def dest: sound_expr_synth_at split: sum.splits)

lemma match_abort_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; dispatch \<rho> v cases = Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> sound_stmt \<rho> (StmtMatch e cases) (aborts\<^sub>o \<kappa>)"
  sorry

lemma seq_sound:
  assumes "sound_stmt \<rho> (node s) (us, Assigns \<rho>')" and "sound_stmt (\<rho> \<otimes> \<rho>') (node s') o"
  shows "sound_stmt \<rho> (StmtSeq s s') ((us, Assigns \<rho>') \<otimes> o)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R"
  from check_seq[OF chk] obtain \<Delta> r R' where chk1: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)"
    and chk2: "check_stmt_at \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s' = Ok R'" and R: "R = Assigns\<^sub>R \<Delta> r \<otimes> R'" by blast
  have o1: "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, Assigns \<rho>') (Assigns\<^sub>R \<Delta> r)"
    using assms(1) env ret chk1 by (rule sound_stmt_at)
  then have env': "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' : \<Gamma> \<otimes> \<Delta>" and dom: "fmdom \<rho>' |\<subseteq>| fmdom \<Delta>" by simp_all
  have o2: "wf_outcome \<eta> (\<rho> \<otimes> \<rho>') (\<Gamma> \<otimes> \<Delta>) \<zeta> o R'" using assms(2) env' ret chk2 by (rule sound_stmt_at)
  obtain vs' \<omega>' where o: "o = (vs', \<omega>')" by (cases o)
  show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> ((us, Assigns \<rho>') \<otimes> o) R"
  proof (cases \<omega>')
    case (Assigns \<rho>'')
    with o2 o obtain \<Delta>' where "bindings_of R' = Some \<Delta>'" and "fmdom \<rho>'' |\<subseteq>| fmdom \<Delta>'"
      and "\<eta> \<turnstile> \<rho> \<otimes> \<rho>' \<otimes> \<rho>'' : \<Gamma> \<otimes> \<Delta> \<otimes> \<Delta>'" by auto
    moreover from this(1) obtain r' where "R' = Assigns\<^sub>R \<Delta>' r'" by (cases R') auto
    ultimately show ?thesis using dom by (auto simp: o Assigns R intro: le_supI1 le_supI2)
  qed (use o2 in \<open>simp_all add: o\<close>)
qed

(* Sequence whose first statement returns or aborts *)
lemma seq_exit_sound:
  assumes "sound_stmt \<rho> (node s) (us, \<omega>)" and "\<And>\<rho>'. \<omega> \<noteq> Assigns \<rho>'"
  shows "sound_stmt \<rho> (StmtSeq s s') (us, \<omega>)"
  unfolding sound_stmt_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> R
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = Ok R"
  from check_seq[OF chk] obtain \<Delta> r where "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok (Assigns\<^sub>R \<Delta> r)" by blast
  with assms(1) env ret have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, \<omega>) (Assigns\<^sub>R \<Delta> r)" by (rule sound_stmt_at)
  then show "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> (us, \<omega>) R" using assms(2) by (cases \<omega>) (simp_all, blast)
qed

lemma if_none_sound: "sound_elif \<rho> ([], None) (assigns\<^sub>o \<epsilon>)"
  by (auto simp: sound_elif_def bind_sum_def)

lemma else_sound:
  assumes "sound_stmt \<rho> (node s) o"
  shows "sound_elif \<rho> ([], Some s) o"
  unfolding sound_elif_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>" and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ([], Some s)) = Ok Rs"
  from chk obtain R where "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R" and "Rs = [R]"
    by (auto simp: bind_sum_def split: sum.splits)
  with assms env ret show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" by (auto intro: sound_stmt_at)
qed

lemma elif_true_sound:
  assumes "sound_expr \<rho> (node e) (Val true)" and "sound_stmt \<rho> (node s) o"
  shows "sound_elif \<rho> ((e, s) # elifs, else') o"
  unfolding sound_elif_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>"
    and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs, else')) = Ok Rs"
  from chk obtain R Rs' where R: "check_stmt_at \<Sigma> \<Gamma> \<zeta> s = Ok R" and Rs: "Rs = R # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  have "wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using assms(2) env ret R by (rule sound_stmt_at)
  then show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" by (auto simp: Rs)
qed

lemma elif_false_sound:
  assumes "sound_expr \<rho> (node e) (Val false)" and "sound_elif \<rho> (elifs, else') o"
  shows "sound_elif \<rho> ((e, s) # elifs, else') o"
  unfolding sound_elif_def
proof (intro allI impI)
  fix \<eta> \<Gamma> \<zeta> Rs
  assume env: "\<eta> \<turnstile> \<rho> : \<Gamma>" and ret: "wf_return \<eta> \<zeta>"
    and chk: "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs, else')) = Ok Rs"
  from chk obtain R Rs' where "those_sum (check_elif \<Sigma> \<Gamma> \<zeta> (elifs, else')) = Ok Rs'" and "Rs = R # Rs'"
    by (auto simp: bind_sum_def split: sum.splits)
  then show "\<exists>R \<in> set Rs. wf_outcome \<eta> \<rho> \<Gamma> \<zeta> o R" using assms(2) env ret unfolding sound_elif_def by auto
qed

lemma elif_fail_sound:
  "sound_expr \<rho> (node e) (Aborts \<kappa>) \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') (aborts\<^sub>o \<kappa>)"
  unfolding sound_elif_def by (auto simp: bind_sum_def dest: prim_operand split: sum.splits)

lemma elif_nonbool_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val v) ; v \<notin> {true, false} \<rbrakk>
  \<Longrightarrow> sound_elif \<rho> ((e, s) # elifs, else') (aborts\<^sub>o Excluded)"
  unfolding sound_elif_def by (auto simp: bind_sum_def dest!: bool_operand split: sum.splits)

subsection \<open>Calls of function definitions\<close>

lemma call_def_sound:
  "\<lbrakk> sound_expr \<rho> (node e) (Val Def(\<rho>', ds, j)) ; node (ds ! j) = Def f \<alpha>s xps \<psi> s
   ; vs = map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds] ; sound_exprs \<rho> es (Val us) ; length xps = length us
   ; scope VUnbound (map fst xps) s = Some \<rho>s
   ; sound_stmt
       (\<rho>' \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) vs) \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s)
       (node s) ([], \<omega>)
   ; j < length ds \<rbrakk>
  \<Longrightarrow> sound_expr \<rho> (ExprCall e (es, [])) (result_of \<omega>)"
  sorry

end

end
