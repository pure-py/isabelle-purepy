theory Patterns
  imports Subtyping
begin

definition pattern_class :: "cxt \<Rightarrow> name \<Rightarrow> reason + name"
where
"pattern_class \<Gamma> q =
  (case resolve_name \<Gamma> q of
     Some (Type C) \<Rightarrow> if C = range_class then Inl RangePattern else Inr C
   | _ \<Rightarrow> Inl (NotClass q))"

(* Sub-patterns of a constructor pattern for class C with arguments a, in the order of the fields of C *)
definition field_patterns :: "class_table \<Rightarrow> name \<Rightarrow> pat args \<Rightarrow> pat list"
where
"field_patterns \<Sigma> C a =
  (case a of (ps, kps) \<Rightarrow> ps @ concat (map (\<lambda>x. [p. (y, p) \<leftarrow> kps, y = x]) (drop (length ps) (field_names \<Sigma> C))))"

lemma field_patterns_elem: "p \<in> set (field_patterns \<Sigma> C (ps, kps)) \<Longrightarrow> p \<in> set ps \<or> p \<in> set (map snd kps)"
  unfolding field_patterns_def by (auto simp: image_iff) (metis snd_conv)

fun disjuncts :: "ty \<Rightarrow> ty list"
where
"disjuncts (TyUnion \<sigma> \<tau>) = disjuncts \<sigma> @ disjuncts \<tau>" |
"disjuncts \<tau> = [\<tau>]"

definition has_list_values :: "class_table \<Rightarrow> ty \<Rightarrow> bool"
where
"has_list_values \<Sigma> \<tau> =
  (\<exists>\<sigma> \<in> set (disjuncts \<tau>). case \<sigma> of TyList _ \<Rightarrow> True | TyVar _ \<Rightarrow> True | _ \<Rightarrow> \<Sigma> \<turnstile> TyList (TyPrim object) <: \<sigma>)"

definition has_tuple_values :: "class_table \<Rightarrow> ty \<Rightarrow> bool"
where
"has_tuple_values \<Sigma> \<tau> =
  (\<exists>\<sigma> \<in> set (disjuncts \<tau>). case \<sigma> of TyTuple _ \<Rightarrow> True | TyVar _ \<Rightarrow> True | _ \<Rightarrow> \<Sigma> \<turnstile> TyTuple [] <: \<sigma>)"

definition has_range_values :: "class_table \<Rightarrow> ty \<Rightarrow> bool"
where
"has_range_values \<Sigma> \<tau> =
  (\<exists>\<sigma> \<in> set (disjuncts \<tau>). case \<sigma> of TyVar _ \<Rightarrow> True | _ \<Rightarrow> \<Sigma> \<turnstile> TyClass range_class [] <: \<sigma>)"

function matched_as :: "class_table \<Rightarrow> cxt \<Rightarrow> ty \<Rightarrow> pat \<Rightarrow> ty"
where
"matched_as \<Sigma> \<Gamma> \<tau> p =
  (case (\<tau>, p) of
     (TyUnion \<sigma> \<sigma>', _) \<Rightarrow> matched_as \<Sigma> \<Gamma> \<sigma> p \<squnion>\<^bsub>\<Sigma>\<^esub> matched_as \<Sigma> \<Gamma> \<sigma>' p
   | (_, PatVar _) \<Rightarrow> \<tau>
   | (_, PatWildcard) \<Rightarrow> \<tau>
   | (_, PatAs p' _) \<Rightarrow> matched_as \<Sigma> \<Gamma> \<tau> p'
   | (_, PatLiteral (LitFloat _)) \<Rightarrow> meet \<Sigma> (TyPrim float) \<tau>
   | (_, PatLiteral l) \<Rightarrow> meet \<Sigma> (TyLiteral l) \<tau>
   | (TyTuple \<tau>s, PatTuple ps) \<Rightarrow>
       if length \<tau>s = length ps then TyTuple (map2 (matched_as \<Sigma> \<Gamma>) \<tau>s ps) else TyPrim Never
   | (TyList _, PatList _) \<Rightarrow> \<tau>
   | (TyDict _, PatDict _) \<Rightarrow> \<tau>
   | (_, PatConstr q _) \<Rightarrow>
       (let C = projr (pattern_class \<Gamma> q) in
        case instance_at \<Sigma> C \<tau> of Instance \<sigma>s \<Rightarrow> meet \<Sigma> \<tau> (TyClass C \<sigma>s) | _ \<Rightarrow> TyPrim Never)
   | _ \<Rightarrow> TyPrim Never)"
by pat_completeness auto

termination
by (relation "measures [\<lambda>(_, _, _, p). size p, \<lambda>(_, _, \<tau>, _). size \<tau>]")
   (auto elim!: in_set_zipE dest: size_list_elem[where f = size])

function remaining :: "class_table \<Rightarrow> cxt \<Rightarrow> ty \<Rightarrow> pat \<Rightarrow> ty"
where
"remaining \<Sigma> \<Gamma> \<tau> p =
  (case (\<tau>, p) of
     (TyUnion \<sigma> \<sigma>', _) \<Rightarrow> remaining \<Sigma> \<Gamma> \<sigma> p \<squnion>\<^bsub>\<Sigma>\<^esub> remaining \<Sigma> \<Gamma> \<sigma>' p
   | (_, PatVar _) \<Rightarrow> TyPrim Never
   | (_, PatWildcard) \<Rightarrow> TyPrim Never
   | (_, PatAs p' _) \<Rightarrow> remaining \<Sigma> \<Gamma> \<tau> p'
   | (_, PatLiteral l) \<Rightarrow>
       if \<tau> = TyLiteral l \<or> (\<tau> = TyPrim NoneType \<and> l = LitNone) then TyPrim Never
       else (case (\<tau>, l) of (TyPrim bool, LitBool b) \<Rightarrow> TyLiteral (LitBool (\<not> b)) | _ \<Rightarrow> \<tau>)
   | (TyTuple \<tau>s, PatTuple ps) \<Rightarrow>
       if length \<tau>s = length ps then
         (let \<rho>s = map2 (remaining \<Sigma> \<Gamma>) \<tau>s ps in
          case filter (\<lambda>i. \<rho>s ! i \<noteq> TyPrim Never) [0..<length \<rho>s] of
            [] \<Rightarrow> TyPrim Never
          | [i] \<Rightarrow> TyTuple (\<tau>s[i := \<rho>s ! i])
          | _ \<Rightarrow> \<tau>)
       else \<tau>
   | (TyDict _, PatDict []) \<Rightarrow> TyPrim Never
   | (_, PatConstr q a) \<Rightarrow>
       (let C = projr (pattern_class \<Gamma> q) in
        case instance_at \<Sigma> C \<tau> of
          Instance \<sigma>s \<Rightarrow>
            if \<Sigma> \<turnstile> \<tau> <: TyClass C \<sigma>s
               \<and> (\<forall>(p', \<sigma>) \<in> set (zip (field_patterns \<Sigma> C a) (field_types \<Sigma> C \<sigma>s)).
                    remaining \<Sigma> \<Gamma> \<sigma> p' = TyPrim Never)
            then TyPrim Never
            else \<tau>
        | _ \<Rightarrow> \<tau>)
   | _ \<Rightarrow> \<tau>)"
by pat_completeness auto

termination
by (relation "measures [\<lambda>(_, _, _, p). size p, \<lambda>(_, _, \<tau>, _). size \<tau>]")
   (auto elim!: in_set_zipE dest!: field_patterns_elem dest: size_list_elem[where f = size] size_list_snd_elem')

definition check_unbound :: "cxt \<Rightarrow> var \<Rightarrow> reason + unit"
where
"check_unbound \<Gamma> x = ensure (fmlookup \<Gamma> x = Some Unbound) (Redeclaration x)"

(* Bindings of pattern p at a type, from its bindings at each disjunct; None for a disjunct that p can't match
   binds the variables of p at Never *)
definition bindings_at :: "class_table \<Rightarrow> pat \<Rightarrow> (reason + (var, ty) fmap) option list \<Rightarrow> reason + (var, ty) fmap"
where
"bindings_at \<Sigma> p ms = do {
   \<Delta>s \<leftarrow> those_sum (map (\<lambda>m. case m of Some m' \<Rightarrow> m' | None \<Rightarrow> Inr (fmconst (binds p) (TyPrim Never))) ms);
   Inr (fmmap_keys (\<lambda>x _. joins \<Sigma> (map (\<lambda>\<Delta>. the (fmlookup \<Delta> x)) \<Delta>s)) (hd \<Delta>s))
 }"

(* Disjoint union of the bindings of sub-patterns *)
definition pattern_bindings :: "(reason + (var, ty) fmap) list \<Rightarrow> reason + (var, ty) fmap"
where
"pattern_bindings ms = do { \<Delta>s \<leftarrow> those_sum ms; Inr (fold (\<otimes>) \<Delta>s fmempty) }"

function check_pat :: "class_table \<Rightarrow> cxt \<Rightarrow> pat \<Rightarrow> ty \<Rightarrow> reason + (var, ty) fmap"
where
"check_pat \<Sigma> \<Gamma> p \<tau> =
  (case p of
     PatWildcard \<Rightarrow> Inr fmempty
   | PatVar x \<Rightarrow> do { check_unbound \<Gamma> x; Inr (fmupd x \<tau> fmempty) }
   | PatAs p' x \<Rightarrow> do {
       check_unbound \<Gamma> x; \<Delta> \<leftarrow> check_pat \<Sigma> \<Gamma> p' \<tau>; Inr (\<Delta> \<otimes> fmupd x (matched_as \<Sigma> \<Gamma> \<tau> p') fmempty)
     }
   | PatLiteral _ \<Rightarrow> Inr fmempty
   | PatTuple ps \<Rightarrow> do {
       ensure (\<not> has_list_values \<Sigma> \<tau>) (SequenceKindMismatch TupleKind \<tau> ListKind);
       ensure (\<not> has_range_values \<Sigma> \<tau>) (SequenceKindMismatch TupleKind \<tau> RangeKind);
       bindings_at \<Sigma> p
         (map (\<lambda>\<sigma>. case \<sigma> of
                     TyTuple \<sigma>s \<Rightarrow>
                       if length \<sigma>s = length ps
                       then Some (pattern_bindings (map2 (check_pat \<Sigma> \<Gamma>) ps \<sigma>s))
                       else None
                   | _ \<Rightarrow> None)
           (disjuncts \<tau>))
     }
   | PatList ps \<Rightarrow> do {
       ensure (\<not> has_tuple_values \<Sigma> \<tau>) (SequenceKindMismatch ListKind \<tau> TupleKind);
       ensure (\<not> has_range_values \<Sigma> \<tau>) (SequenceKindMismatch ListKind \<tau> RangeKind);
       bindings_at \<Sigma> p
         (map (\<lambda>\<sigma>. case \<sigma> of
                     TyList \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p'. check_pat \<Sigma> \<Gamma> p' \<sigma>') ps))
                   | _ \<Rightarrow> None)
           (disjuncts \<tau>))
     }
   | PatDict kps \<Rightarrow>
       bindings_at \<Sigma> p
         (map (\<lambda>\<sigma>. case \<sigma> of
                     TyDict \<sigma>' \<Rightarrow> Some (pattern_bindings (map (\<lambda>p'. check_pat \<Sigma> \<Gamma> p' \<sigma>') (map snd kps)))
                   | _ \<Rightarrow> None)
           (disjuncts \<tau>))
   | PatConstr q (ps, kps) \<Rightarrow> do {
       C \<leftarrow> pattern_class \<Gamma> q;
       check_field_map (PatternArityMismatch (short_name C)) (UnknownFieldInPattern (short_name C))
         (field_names \<Sigma> C) (length ps) (map fst kps);
       bindings_at \<Sigma> p
         (map (\<lambda>\<sigma>. case instance_at \<Sigma> C \<sigma> of
                     Instance \<sigma>s \<Rightarrow>
                       Some (pattern_bindings
                         (map2 (check_pat \<Sigma> \<Gamma>) (field_patterns \<Sigma> C (ps, kps)) (field_types \<Sigma> C \<sigma>s)))
                   | NoInstance \<Rightarrow> None
                   | Undetermined \<Rightarrow> Some (Inl (PatternClassUndetermined (short_name C) \<sigma>)))
           (disjuncts \<tau>))
     })"
by pat_completeness auto

termination
by (relation "measure (\<lambda>(_, _, p, _). size p)")
   (auto elim!: in_set_zipE dest!: field_patterns_elem
     dest: size_list_elem[where f = size] size_list_snd_elem size_list_snd_elem')

end
