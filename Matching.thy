theory Matching
  imports Shapes Patterns
begin

(* Dictionary shape k with keys ws bound to shapes ks *)
definition with_keys :: "shape \<Rightarrow> string list \<Rightarrow> shape list \<Rightarrow> shape"
where
"with_keys k ws ks =
  (case k of
     ShapeDict \<tau> \<beta> W \<Rightarrow> ShapeDict \<tau> (sort_key fst (zip ws ks @ filter (\<lambda>(w, _). w \<notin> set ws) \<beta>)) W
   | _ \<Rightarrow> undefined)"

definition split_class :: "class_table \<Rightarrow> cxt \<Rightarrow> ty \<Rightarrow> head set \<Rightarrow> name \<Rightarrow> (shape list \<times> shape list) option"
where
"split_class \<Sigma> \<Gamma> \<tau> H q =
  (let C = projr (pattern_class \<Gamma> q) in
   if below_excluded \<Sigma> C H then None
   else case instance_at \<Sigma> C \<tau> of
     Instance \<tau>s \<Rightarrow>
       (case meet \<Sigma> \<tau> (TyClass C \<tau>s) of
          TyClass D \<sigma>s \<Rightarrow>
            Some (map (\<lambda>ks. ShapeConstr D \<sigma>s ks (typed_heads \<Sigma> H (TyClass D \<sigma>s)))
                    (shapes_seq \<Sigma> (field_types \<Sigma> D \<sigma>s)),
                  shapes \<Sigma> \<tau> (insert (HeadClass C) H))
        | _ \<Rightarrow> undefined)
   | NoInstance \<Rightarrow> None
   | Undetermined \<Rightarrow> undefined)"

definition split_subclass ::
  "class_table \<Rightarrow> cxt \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> shape list \<Rightarrow> head set \<Rightarrow> name \<Rightarrow> (shape list \<times> shape list) option"
where
"split_subclass \<Sigma> \<Gamma> C \<tau>s ks H q =
  (let D = projr (pattern_class \<Gamma> q) in
   case instance_at \<Sigma> D (TyClass C \<tau>s) of
     Instance \<sigma>s \<Rightarrow>
       if D = C \<or> \<not> \<Sigma> \<turnstile> TyClass D \<sigma>s <: TyClass C \<tau>s \<or> below_excluded \<Sigma> D H then None
       else
         Some (map (\<lambda>ks'. ShapeConstr D \<sigma>s (ks @ ks') (typed_heads \<Sigma> H (TyClass D \<sigma>s)))
                 (shapes_seq \<Sigma> (drop (length ks) (field_types \<Sigma> D \<sigma>s))),
               [ShapeConstr C \<tau>s ks (insert (HeadClass D) H)])
   | NoInstance \<Rightarrow> None
   | Undetermined \<Rightarrow> undefined)"

definition split :: "class_table \<Rightarrow> cxt \<Rightarrow> shape \<Rightarrow> pat \<Rightarrow> (shape list \<times> shape list) option"
where
"split \<Sigma> \<Gamma> k p =
  (case (k, p) of
     (ShapeRest \<tau> H, PatLiteral (LitFloat _)) \<Rightarrow> None
   | (ShapeRest \<tau> H, PatLiteral l) \<Rightarrow>
       if HeadLiteral l \<notin> H \<and> \<Sigma> \<turnstile> TyLiteral l <: \<tau> \<and> \<not> literal_type \<tau>
       then Some ([ShapeRest (TyLiteral l) {}], shapes \<Sigma> \<tau> (insert (HeadLiteral l) H))
       else None
   | (ShapeRest (TyTuple \<tau>s) _, PatTuple ps) \<Rightarrow>
       if length \<tau>s = length ps then Some (map ShapeTuple (shapes_seq \<Sigma> \<tau>s), []) else None
   | (ShapeRest (TyList \<tau>) H, PatList ps) \<Rightarrow>
       if HeadList (length ps) \<in> H then None
       else
         Some (map (ShapeList \<tau>) (shapes_seq \<Sigma> (replicate (length ps) \<tau>)),
               shapes \<Sigma> (TyList \<tau>) (insert (HeadList (length ps)) H))
   | (ShapeDict \<tau> \<beta> W, PatDict kps) \<Rightarrow>
       (case find (\<lambda>w. w \<notin> fst ` set \<beta>) (map fst kps) of
          Some w \<Rightarrow>
            if w \<in> W then None
            else Some (map (\<lambda>k'. with_keys k [w] [k']) (shapes \<Sigma> \<tau> {}), [ShapeDict \<tau> \<beta> (insert w W)])
        | None \<Rightarrow> None)
   | (ShapeRest \<tau> H, PatConstr q _) \<Rightarrow> split_class \<Sigma> \<Gamma> \<tau> H q
   | (ShapeConstr C \<tau>s ks H, PatConstr q _) \<Rightarrow> split_subclass \<Sigma> \<Gamma> C \<tau>s ks H q
   | _ \<Rightarrow> None)"

(* Matched shapes and residual of patterns matching shapes ks position by position, as shapes of form f, from
   the match at each position *)
definition seq_result ::
  "(shape list \<Rightarrow> shape) \<Rightarrow> shape list \<Rightarrow> (shape list \<times> shape list) option list
   \<Rightarrow> (shape list \<times> shape list) option"
where
"seq_result f ks ms = do {
   rs \<leftarrow> those ms;
   let Ks = map fst rs;
   Some (map f (product_lists Ks),
         map f (concat (map (\<lambda>i. [ks' @ [l] @ drop (Suc i) ks.
                                    ks' \<leftarrow> product_lists (take i Ks), l \<leftarrow> snd (rs ! i)])
                            [0..<length rs])))
 }"

(* Matched shapes and residual of a pattern matching shapes L, from the match at each shape of L *)
definition shapes_result ::
  "shape list \<Rightarrow> (shape list \<times> shape list) option list \<Rightarrow> (shape list \<times> shape list) option"
where
"shapes_result L ms =
  (let rs = [r. Some r \<leftarrow> ms] in
   if rs = [] then None else Some (concat (map fst rs), concat (map snd rs) @ [k. (k, None) \<leftarrow> zip L ms]))"

(* Splits of a shape that matching against p may need: one for each key of a dictionary pattern, otherwise
   one *)
fun splits :: "pat \<Rightarrow> nat"
where
"splits (PatDict kps) = length kps" |
"splits _ = 1"

(* n bounds the splits of k that matching against p may make *)
function (sequential)
  match_shape :: "class_table \<Rightarrow> cxt \<Rightarrow> shape \<Rightarrow> pat \<Rightarrow> (shape list \<times> shape list) option" and
  match_shape_upto :: "nat \<Rightarrow> class_table \<Rightarrow> cxt \<Rightarrow> shape \<Rightarrow> pat \<Rightarrow> (shape list \<times> shape list) option" and
  match_directly :: "class_table \<Rightarrow> cxt \<Rightarrow> shape \<Rightarrow> pat \<Rightarrow> (shape list \<times> shape list) option"
where
"match_shape \<Sigma> \<Gamma> k p = match_shape_upto (splits p) \<Sigma> \<Gamma> k p" |
"match_shape_upto n \<Sigma> \<Gamma> k p =
  (case match_directly \<Sigma> \<Gamma> k p of
     Some r \<Rightarrow> Some r
   | None \<Rightarrow>
       (case (split \<Sigma> \<Gamma> k p, n) of
          (Some (K, L), Suc n') \<Rightarrow>
            map_option (\<lambda>(K', L'). (K', L @ L')) (shapes_result K (map (\<lambda>k'. match_shape_upto n' \<Sigma> \<Gamma> k' p) K))
        | _ \<Rightarrow> None))" |
"match_directly \<Sigma> \<Gamma> k (PatVar _) = Some ([k], [])" |
"match_directly \<Sigma> \<Gamma> k PatWildcard = Some ([k], [])" |
"match_directly \<Sigma> \<Gamma> k (PatAs p _) = match_shape \<Sigma> \<Gamma> k p" |
"match_directly \<Sigma> \<Gamma> (ShapeRest \<tau> H) (PatLiteral (LitFloat r)) =
  (if HeadLiteral (LitFloat r) \<notin> H \<and> \<Sigma> \<turnstile> TyPrim float <: \<tau>
   then Some ([ShapeRest \<tau> H], [ShapeRest \<tau> (insert (HeadLiteral (LitFloat r)) H)])
   else None)" |
"match_directly \<Sigma> \<Gamma> (ShapeRest \<tau> H) (PatLiteral l) =
  (if \<tau> = TyLiteral l then Some ([ShapeRest \<tau> H], []) else None)" |
"match_directly \<Sigma> \<Gamma> (ShapeTuple ks) (PatTuple ps) =
  (if length ks = length ps then seq_result ShapeTuple ks (map2 (match_shape \<Sigma> \<Gamma>) ks ps) else None)" |
"match_directly \<Sigma> \<Gamma> (ShapeList \<tau> ks) (PatList ps) =
  (if length ks = length ps then seq_result (ShapeList \<tau>) ks (map2 (match_shape \<Sigma> \<Gamma>) ks ps) else None)" |
"match_directly \<Sigma> \<Gamma> (ShapeDict \<tau> \<beta> W) (PatDict kps) =
  (if \<forall>w \<in> set (map fst kps). w \<in> fst ` set \<beta> then
     (let ks = map (the \<circ> map_of \<beta> \<circ> fst) kps in
      seq_result (with_keys (ShapeDict \<tau> \<beta> W) (map fst kps)) ks (map2 (match_shape \<Sigma> \<Gamma>) ks (map snd kps)))
   else None)" |
"match_directly \<Sigma> \<Gamma> (ShapeConstr C \<tau>s ks H) (PatConstr q a) =
  (let D = projr (pattern_class \<Gamma> q); ps = field_patterns \<Sigma> D a; m = length ps in
   if D \<in> set (ancestors \<Sigma> C)
   then
     seq_result (\<lambda>ks'. ShapeConstr C \<tau>s (ks' @ drop m ks) H) (take m ks) (map2 (match_shape \<Sigma> \<Gamma>) (take m ks) ps)
   else None)" |
"match_directly \<Sigma> \<Gamma> _ _ = None"
by pat_completeness auto

termination
by (relation "measures [
     \<lambda>x. case x of
       Inl (_, _, _, p) \<Rightarrow> size p | Inr (Inl (_, _, _, _, p)) \<Rightarrow> size p | Inr (Inr (_, _, _, p)) \<Rightarrow> size p,
     \<lambda>x. case x of Inl (_, _, _, p) \<Rightarrow> splits p + 2 | Inr (Inl (n, _, _, _, _)) \<Rightarrow> n + 1 | Inr (Inr _) \<Rightarrow> 0]")
   (auto elim!: in_set_zipE dest!: field_patterns_elem dest: size_list_elem[where f = size] size_list_snd_elem')

definition match_shapes :: "class_table \<Rightarrow> cxt \<Rightarrow> shape list \<Rightarrow> pat \<Rightarrow> (shape list \<times> shape list) option"
where
"match_shapes \<Sigma> \<Gamma> L p = shapes_result L (map (\<lambda>k. match_shape \<Sigma> \<Gamma> k p) L)"

end
