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
                    (shapes_seq \<Sigma> (map snd (instantiate (fields \<Sigma> D) \<sigma>s))),
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
                 (shapes_seq \<Sigma> (drop (length ks) (map snd (instantiate (fields \<Sigma> D) \<sigma>s)))),
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

(* Splits of a shape that matching against p may need: one for each key of a dictionary pattern, otherwise
   one *)
fun splits :: "pat \<Rightarrow> nat"
where
"splits (PatDict kps) = length kps" |
"splits _ = 1"

(* Matched shape sequences and residual of patterns matching shapes ks position by position, from the match
   at each position *)
definition seq_result ::
  "shape list \<Rightarrow> (shape list \<times> shape list) option list \<Rightarrow> (shape list list \<times> shape list list) option"
where
"seq_result ks ms = do {
   rs \<leftarrow> those ms;
   let Ks = map fst rs;
   Some (product_lists Ks,
         concat (map (\<lambda>i. [ks' @ [l] @ drop (Suc i) ks. ks' \<leftarrow> product_lists (take i Ks), l \<leftarrow> snd (rs ! i)])
                     [0..<length rs]))
 }"

(* Matched shapes and residual of a pattern matching shapes L, from the match at each shape of L *)
definition shapes_result ::
  "shape list \<Rightarrow> (shape list \<times> shape list) option list \<Rightarrow> (shape list \<times> shape list) option"
where
"shapes_result L ms =
  (let rs = [r. Some r \<leftarrow> ms] in
   if rs = [] then None else Some (concat (map fst rs), concat (map snd rs) @ [k. (k, None) \<leftarrow> zip L ms]))"

definition map_result :: "('a \<Rightarrow> shape) \<Rightarrow> ('a list \<times> 'a list) option \<Rightarrow> (shape list \<times> shape list) option"
where
"map_result f m = map_option (\<lambda>(K, L). (map f K, map f L)) m"

(* n bounds the splits of k that matching against p may make *)
function match_shape :: "class_table \<Rightarrow> cxt \<Rightarrow> nat \<Rightarrow> shape \<Rightarrow> pat \<Rightarrow> (shape list \<times> shape list) option"
where
"match_shape \<Sigma> \<Gamma> n k p =
  (case
     (case p of
        PatVar _ \<Rightarrow> Some ([k], [])
      | PatWildcard \<Rightarrow> Some ([k], [])
      | PatAs p' _ \<Rightarrow> match_shape \<Sigma> \<Gamma> (splits p') k p'
      | PatLiteral l \<Rightarrow>
          (case (k, l) of
             (ShapeRest \<tau> H, LitFloat _) \<Rightarrow>
               if HeadLiteral l \<notin> H \<and> \<Sigma> \<turnstile> TyPrim float <: \<tau>
               then Some ([k], [ShapeRest \<tau> (insert (HeadLiteral l) H)])
               else None
           | (ShapeRest \<tau> _, _) \<Rightarrow> if \<tau> = TyLiteral l then Some ([k], []) else None
           | _ \<Rightarrow> None)
      | PatTuple ps \<Rightarrow>
          (case k of
             ShapeTuple ks \<Rightarrow>
               if length ks = length ps
               then map_result ShapeTuple
                      (seq_result ks (map2 (\<lambda>k' p'. match_shape \<Sigma> \<Gamma> (splits p') k' p') ks ps))
               else None
           | _ \<Rightarrow> None)
      | PatList ps \<Rightarrow>
          (case k of
             ShapeList \<tau> ks \<Rightarrow>
               if length ks = length ps
               then map_result (ShapeList \<tau>)
                      (seq_result ks (map2 (\<lambda>k' p'. match_shape \<Sigma> \<Gamma> (splits p') k' p') ks ps))
               else None
           | _ \<Rightarrow> None)
      | PatDict kps \<Rightarrow>
          (case k of
             ShapeDict \<tau> \<beta> W \<Rightarrow>
               if \<forall>w \<in> set (map fst kps). w \<in> fst ` set \<beta> then
                 (let ks = map (the \<circ> map_of \<beta> \<circ> fst) kps in
                  map_result (with_keys k (map fst kps))
                    (seq_result ks (map2 (\<lambda>k' p'. match_shape \<Sigma> \<Gamma> (splits p') k' p') ks (map snd kps))))
               else None
           | _ \<Rightarrow> None)
      | PatConstr q a \<Rightarrow>
          (case k of
             ShapeConstr C \<tau>s ks H \<Rightarrow>
               (let D = projr (pattern_class \<Gamma> q); ps = field_patterns \<Sigma> D a; m = length ps in
                if D \<in> set (ancestors \<Sigma> C) then
                  map_result (\<lambda>ks'. ShapeConstr C \<tau>s (ks' @ drop m ks) H)
                    (seq_result (take m ks) (map2 (\<lambda>k' p'. match_shape \<Sigma> \<Gamma> (splits p') k' p') (take m ks) ps))
                else None)
           | _ \<Rightarrow> None))
   of
     Some r \<Rightarrow> Some r
   | None \<Rightarrow>
       (case (split \<Sigma> \<Gamma> k p, n) of
          (Some (K, L), Suc n') \<Rightarrow>
            map_option (\<lambda>(K', L'). (K', L @ L')) (shapes_result K (map (\<lambda>k'. match_shape \<Sigma> \<Gamma> n' k' p) K))
        | _ \<Rightarrow> None))"
by pat_completeness auto

termination
by (relation "measures [\<lambda>(_, _, _, _, p). size p, \<lambda>(_, _, n, _, _). n]")
   (auto elim!: in_set_zipE dest!: field_patterns_elem dest: size_list_elem[where f = size] size_list_snd_elem')

definition match_shapes :: "class_table \<Rightarrow> cxt \<Rightarrow> shape list \<Rightarrow> pat \<Rightarrow> (shape list \<times> shape list) option"
where
"match_shapes \<Sigma> \<Gamma> L p = shapes_result L (map (\<lambda>k. match_shape \<Sigma> \<Gamma> (splits p) k p) L)"

end
