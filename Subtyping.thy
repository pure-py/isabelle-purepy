(* Subtyping and its transitivity, join and meet; element, subscript and attribute types *)
theory Subtyping
  imports Types
begin

inductive subty :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ <: _" [51, 51, 51] 50)
and subtys :: "class_table \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> bool" ("_ \<turnstile> _ [<:] _" [51, 51, 51] 50)
for \<Sigma> :: class_table
where
SubtyRefl: "\<Sigma> \<turnstile> \<tau> <: \<tau>" |
SubtyClassExtend:
  "\<lbrakk> base \<Sigma> C = Some (D, \<sigma>s) ; \<Sigma> \<turnstile> TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s) <: \<tau>' \<rbrakk>
  \<Longrightarrow> \<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>'" |
SubtyClass: "\<lbrakk> \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s ; \<Sigma> \<turnstile> \<tau>s [<:] \<sigma>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass C \<tau>s" |
SubtyNever: "\<Sigma> \<turnstile> TyPrim Never <: \<tau>" |
SubtyObject: "\<Sigma> \<turnstile> \<tau> <: TyPrim object" |
SubtyIntFloat: "\<Sigma> \<turnstile> TyPrim int <: TyPrim float" |
SubtySized: "sized \<tau> \<Longrightarrow> \<Sigma> \<turnstile> \<tau> <: TyPrim Sized" |
SubtyList: "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: \<tau> ; \<Sigma> \<turnstile> \<tau> <: \<sigma> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyList \<sigma> <: TyList \<tau>" |
SubtyDict: "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: \<tau> ; \<Sigma> \<turnstile> \<tau> <: \<sigma> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyDict \<sigma> <: TyDict \<tau>" |
SubtyCallable:
  "\<lbrakk> \<Sigma> \<turnstile> \<tau>s [<:] \<sigma>s ; \<Sigma> \<turnstile> \<sigma> <: \<tau> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyCallable \<sigma>s \<sigma> <: TyCallable \<tau>s \<tau>" |
SubtyTuple: "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> \<Sigma> \<turnstile> TyTuple \<sigma>s <: TyTuple \<tau>s" |
SubtyLiteral: "\<Sigma> \<turnstile> base_type_lit l <: \<tau> \<Longrightarrow> \<Sigma> \<turnstile> TyLiteral l <: \<tau>" |
SubtyUnionLeft: "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" |
SubtyUnionRight: "\<Sigma> \<turnstile> \<sigma> <: \<tau>' \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" |
SubtyUnion: "\<lbrakk> \<Sigma> \<turnstile> \<tau> <: \<sigma> ; \<Sigma> \<turnstile> \<tau>' <: \<sigma> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<sigma>" |

SubtysNil: "\<Sigma> \<turnstile> [] [<:] []" |
SubtysCons: "\<lbrakk> \<Sigma> \<turnstile> \<sigma> <: \<tau> ; \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> # \<sigma>s [<:] \<tau> # \<tau>s"

abbreviation equiv :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" ("_ \<turnstile> _ \<approx> _" [51, 51, 51] 50)
where
"\<Sigma> \<turnstile> \<sigma> \<approx> \<tau> \<equiv> \<Sigma> \<turnstile> \<sigma> <: \<tau> \<and> \<Sigma> \<turnstile> \<tau> <: \<sigma>"

definition join :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
where
"join \<Sigma> \<sigma> \<tau> = (if \<Sigma> \<turnstile> \<sigma> <: \<tau> then \<tau> else if \<Sigma> \<turnstile> \<tau> <: \<sigma> then \<sigma> else TyUnion \<sigma> \<tau>)"

syntax "_join" :: "ty \<Rightarrow> class_table \<Rightarrow> ty \<Rightarrow> ty" ("_ \<squnion>\<^bsub>_\<^esub> _" [65, 0, 66] 65)
translations "\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>" \<rightleftharpoons> "CONST join \<Sigma> \<sigma> \<tau>"

definition joins :: "class_table \<Rightarrow> ty list \<Rightarrow> ty"
where
"joins \<Sigma> \<tau>s = foldr (\<lambda>\<sigma> \<tau>. \<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>) \<tau>s (TyPrim Never)"

lemma fv_join: "fv (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>) \<subseteq> fv \<sigma> \<union> fv \<tau>"
  by (auto simp: join_def)

lemma fv_joins: "fv (joins \<Sigma> \<tau>s) \<subseteq> \<Union> (fv ` set \<tau>s)"
  by (induction \<tau>s) (auto simp: joins_def join_def)

lemma join_upper: "\<Sigma> \<turnstile> \<sigma> <: \<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>" "\<Sigma> \<turnstile> \<tau> <: \<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>"
  by (auto simp: join_def intro: SubtyRefl SubtyUnionLeft SubtyUnionRight)

lemma base_type_upper: "\<Sigma> \<turnstile> \<tau> <: base_type \<tau>"
  by (cases \<tau>) (auto intro: SubtyRefl SubtyLiteral)

function (sequential)
  meet :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty" and
  meet_incomparable :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
where
"meet \<Sigma> \<sigma> \<tau> = (if \<Sigma> \<turnstile> \<sigma> <: \<tau> then \<sigma> else if \<Sigma> \<turnstile> \<tau> <: \<sigma> then \<tau> else meet_incomparable \<Sigma> \<sigma> \<tau>)" |

"meet_incomparable \<Sigma> (TyUnion \<sigma> \<sigma>') \<tau> = meet \<Sigma> \<sigma> \<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> meet \<Sigma> \<sigma>' \<tau>" |
"meet_incomparable \<Sigma> \<sigma> (TyUnion \<tau> \<tau>') = meet \<Sigma> \<sigma> \<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> meet \<Sigma> \<sigma> \<tau>'" |
"meet_incomparable \<Sigma> (TyCallable \<sigma>s \<sigma>) (TyCallable \<tau>s \<tau>) =
  (if length \<sigma>s = length \<tau>s then TyCallable (map2 (\<lambda>\<sigma>' \<tau>'. \<sigma>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') \<sigma>s \<tau>s) (meet \<Sigma> \<sigma> \<tau>) else TyPrim Never)" |
"meet_incomparable \<Sigma> (TyTuple \<sigma>s) (TyTuple \<tau>s) =
  (if length \<sigma>s = length \<tau>s then TyTuple (map2 (meet \<Sigma>) \<sigma>s \<tau>s) else TyPrim Never)" |
"meet_incomparable \<Sigma> _ _ = TyPrim Never"
by pat_completeness auto

termination
by (relation "measures [
     \<lambda>x. case x of Inl (_, \<sigma>, \<tau>) \<Rightarrow> size \<sigma> + size \<tau> | Inr (_, \<sigma>, \<tau>) \<Rightarrow> size \<sigma> + size \<tau>,
     \<lambda>x. case x of Inl _ \<Rightarrow> 1 | Inr _ \<Rightarrow> 0]")
   (auto dest: size_list_zip_elem[where f = size and g = size])

fun elem_type :: "class_table \<Rightarrow> ty \<Rightarrow> ty option"
where
"elem_type \<Sigma> (TyList \<tau>) = Some \<tau>" |
"elem_type \<Sigma> (TyPrim str) = Some (TyPrim str)" |
"elem_type \<Sigma> (TyLiteral (LitString _)) = Some (TyPrim str)" |
"elem_type \<Sigma> (TyDict _) = Some (TyPrim str)" |
"elem_type \<Sigma> (TyClass C []) = (if C = range_class then Some (TyPrim int) else None)" |
"elem_type \<Sigma> (TyTuple \<tau>s) = Some (joins \<Sigma> (map base_type \<tau>s))" |
"elem_type \<Sigma> (TyUnion \<sigma> \<tau>) =
  (case (elem_type \<Sigma> \<sigma>, elem_type \<Sigma> \<tau>) of (Some \<sigma>', Some \<tau>') \<Rightarrow> Some (\<sigma>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') | _ \<Rightarrow> None)" |
"elem_type \<Sigma> _ = None"

(* Type of a subscript, by the type of the subscripted value, the checks of the index against int and str,
   and the position and type synthesised by the index *)
fun subscript_type ::
  "class_table \<Rightarrow> ty \<Rightarrow> unit may_fail \<Rightarrow> unit may_fail \<Rightarrow> pos \<Rightarrow> ty may_fail \<Rightarrow> ty may_fail"
where
"subscript_type \<Sigma> (TyUnion \<sigma> \<sigma>') int_ok str_ok p idx = do {
   \<tau> \<leftarrow> subscript_type \<Sigma> \<sigma> int_ok str_ok p idx; \<tau>' \<leftarrow> subscript_type \<Sigma> \<sigma>' int_ok str_ok p idx;
   Ok (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>')
 }" |
"subscript_type \<Sigma> (TyList \<tau>) int_ok _ _ _ = by_rule RuleSubscriptList (do { int_ok; Ok \<tau> })" |
"subscript_type \<Sigma> (TyDict \<tau>) _ str_ok _ _ = by_rule RuleSubscriptDict (do { str_ok; Ok \<tau> })" |
"subscript_type \<Sigma> (TyTuple \<tau>s) _ _ p idx = do {
   \<iota> \<leftarrow> idx;
   case \<iota> of
     TyLiteral (LitInt n) \<Rightarrow>
       let i = (if n < 0 then of_nat (length \<tau>s) + n else n)
       in if 0 \<le> i \<and> i < of_nat (length \<tau>s) then Ok (\<tau>s ! nat i)
          else Fail (Located p (Violates (if n < 0 then RuleSubscriptTupleNeg else RuleSubscriptTuple)
                                   (TupleIndexOutOfRange n (length \<tau>s))))
   | TyPrim int \<Rightarrow> Ok (joins \<Sigma> \<tau>s)
   | _ \<Rightarrow> Fail (Located p (Violates RuleSubscriptTupleInt (TypeMismatch (TyPrim int) \<iota>)))
 }" |
"subscript_type \<Sigma> \<sigma> int_ok _ _ _ =
  (if base_type \<sigma> = TyPrim str then by_rule RuleSubscriptStr (do { int_ok; Ok (TyPrim str) })
   else Fail (SelectsNoRule JudgementSynth (NotSubscriptable \<sigma>)))"

datatype instances = Instance "ty list" | Undetermined | NoInstance

fun instance_above :: "class_table \<Rightarrow> name \<Rightarrow> ty \<Rightarrow> instances"
where
"instance_above \<Sigma> C (TyClass D \<sigma>s) =
  (if C \<in> set (ancestors \<Sigma> D) then Instance (instantiated_ancestor \<Sigma> D \<sigma>s C) else NoInstance)" |
"instance_above \<Sigma> C (TyPrim Never) = (if type_params \<Sigma> C = [] then Instance [] else Undetermined)" |
"instance_above \<Sigma> C _ = NoInstance"

definition instantiation_candidates :: "class_table \<Rightarrow> name \<Rightarrow> ty list \<Rightarrow> ty list list"
where
"instantiation_candidates \<Sigma> C \<sigma>s =
  product_lists
    (replicate (length (type_params \<Sigma> C))
      (map (joins \<Sigma>) (subseqs (remdups (concat (map subterms \<sigma>s) @ [TyPrim object])))))"

fun instance_below :: "class_table \<Rightarrow> name \<Rightarrow> ty \<Rightarrow> instances"
where
"instance_below \<Sigma> C (TyClass D \<sigma>s) =
  (if D \<in> set (ancestors \<Sigma> C) then
     (case
        filter (\<lambda>\<tau>s. list_all2 (\<lambda>\<rho> \<sigma>. \<Sigma> \<turnstile> \<rho> \<approx> \<sigma>) (instantiated_ancestor \<Sigma> C \<tau>s D) \<sigma>s)
          (instantiation_candidates \<Sigma> C \<sigma>s) of
        [] \<Rightarrow> NoInstance
      | \<tau>s # \<tau>ss \<Rightarrow>
          if list_all (list_all2 (\<lambda>\<tau> \<tau>'. \<Sigma> \<turnstile> \<tau> \<approx> \<tau>') \<tau>s) \<tau>ss then Instance \<tau>s else Undetermined)
   else NoInstance)" |
"instance_below \<Sigma> C (TyPrim object) = (if type_params \<Sigma> C = [] then Instance [] else Undetermined)" |
"instance_below \<Sigma> C _ = NoInstance"

definition instance_at :: "class_table \<Rightarrow> name \<Rightarrow> ty \<Rightarrow> instances"
where
"instance_at \<Sigma> C \<tau> = (case instance_above \<Sigma> C \<tau> of NoInstance \<Rightarrow> instance_below \<Sigma> C \<tau> | \<iota> \<Rightarrow> \<iota>)"

(* Pointwise join of contexts binding type variables at types *)
definition join_cxt :: "class_table \<Rightarrow> (var, ty) fmap \<Rightarrow> (var, ty) fmap \<Rightarrow> (var, ty) fmap"
where
"join_cxt \<Sigma> \<gamma> \<gamma>' =
  fmmap_keys (\<lambda>\<alpha> \<tau>. case (fmlookup \<gamma> \<alpha>, fmlookup \<gamma>' \<alpha>) of (Some \<sigma>, Some \<tau>') \<Rightarrow> \<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>' | _ \<Rightarrow> \<tau>) (\<gamma> \<otimes> \<gamma>')"

function (sequential)
  type_args :: "class_table \<Rightarrow> var list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> (var, ty) fmap" and
  type_args_seq :: "class_table \<Rightarrow> var list \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> (var, ty) fmap"
where
"type_args \<Sigma> \<alpha>s (TyVar \<alpha>) \<tau> =
  (if \<alpha> \<in> set \<alpha>s then fmupd \<alpha> (base_type \<tau>) fmempty else fmempty)" |
"type_args \<Sigma> \<alpha>s \<sigma> (TyUnion \<tau> \<tau>') = join_cxt \<Sigma> (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) (type_args \<Sigma> \<alpha>s \<sigma> \<tau>')" |
"type_args \<Sigma> \<alpha>s (TyList \<sigma>) (TyList \<tau>) = type_args \<Sigma> \<alpha>s \<sigma> \<tau>" |
"type_args \<Sigma> \<alpha>s (TyDict \<sigma>) (TyDict \<tau>) = type_args \<Sigma> \<alpha>s \<sigma> \<tau>" |
"type_args \<Sigma> \<alpha>s (TyTuple \<sigma>s) (TyTuple \<tau>s) = type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s" |
"type_args \<Sigma> \<alpha>s (TyCallable \<sigma>s \<sigma>) (TyCallable \<tau>s \<tau>) = type_args_seq \<Sigma> \<alpha>s (\<sigma> # \<sigma>s) (\<tau> # \<tau>s)" |
"type_args \<Sigma> \<alpha>s (TyClass C \<sigma>s) \<tau> =
  (case instance_at \<Sigma> C \<tau> of Instance \<tau>s \<Rightarrow> type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s | _ \<Rightarrow> fmempty)" |
"type_args \<Sigma> \<alpha>s (TyUnion \<sigma> \<sigma>') \<tau> =
  (if (\<Sigma> \<turnstile> \<tau> <: \<sigma> \<and> fv \<sigma> \<inter> set \<alpha>s = {}) \<or> (\<Sigma> \<turnstile> \<tau> <: \<sigma>' \<and> fv \<sigma>' \<inter> set \<alpha>s = {}) then fmempty
   else join_cxt \<Sigma> (type_args \<Sigma> \<alpha>s \<sigma> \<tau>) (type_args \<Sigma> \<alpha>s \<sigma>' \<tau>))" |
"type_args \<Sigma> \<alpha>s _ _ = fmempty" |

"type_args_seq \<Sigma> \<alpha>s \<sigma>s \<tau>s = foldr (join_cxt \<Sigma>) (map2 (type_args \<Sigma> \<alpha>s) \<sigma>s \<tau>s) fmempty"
by pat_completeness auto

termination
by (relation "measures [
     \<lambda>x. case x of Inl (_, _, \<sigma>, _) \<Rightarrow> size \<sigma> | Inr (_, _, \<sigma>s, _) \<Rightarrow> size_list size \<sigma>s,
     \<lambda>x. case x of Inl _ \<Rightarrow> 1 | Inr _ \<Rightarrow> 0,
     \<lambda>x. case x of Inl (_, _, _, \<tau>) \<Rightarrow> size \<tau> | Inr _ \<Rightarrow> 0]")
   (auto dest: set_zip_leftD size_list_elem[where f = size])

(* Types bound to \<alpha>s by \<gamma>; failure if \<gamma> doesn't bind one of them *)
definition type_args_of :: "(var, ty) fmap \<Rightarrow> var list \<Rightarrow> ty list may_fail"
where
"type_args_of \<gamma> \<alpha>s =
  those_sum (map (\<lambda>\<alpha>. or_else (NoTypeArgument \<alpha>) (fmlookup \<gamma> \<alpha>)) \<alpha>s)"

lemma type_args_of_length: "type_args_of \<gamma> \<alpha>s = Ok \<tau>s \<Longrightarrow> length \<tau>s = length \<alpha>s"
  by (auto simp: type_args_of_def dest!: those_sum_Ok list_all2_lengthD)

(* Type of attribute x of a value of type \<sigma>, which isn't a module *)
fun attribute_type :: "class_table \<Rightarrow> ty \<Rightarrow> var \<Rightarrow> ty may_fail"
where
"attribute_type \<Sigma> (TyUnion \<sigma> \<sigma>') x =
  do { \<tau> \<leftarrow> attribute_type \<Sigma> \<sigma> x; \<tau>' \<leftarrow> attribute_type \<Sigma> \<sigma>' x; Ok (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') }" |
"attribute_type \<Sigma> (TyClass C \<sigma>s) x =
  or_else (Violates RuleAttrObject (UnknownField (short_name C) x)) (map_of (instantiate (fields \<Sigma> C) \<sigma>s) x)" |
"attribute_type \<Sigma> \<sigma> x = Fail (SelectsNoRule JudgementSynth (NoAttributes \<sigma> x))"

(* Rule of subtyping, if any, selected by the judgement that \<sigma> is a subtype of \<tau>, taking a literal type as its
   base type unless \<tau> is a literal type *)
fun subtyping_rule :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> rule option"
where
"subtyping_rule \<Sigma> (TyUnion _ _) _ = Some RuleSubtyUnion" |
"subtyping_rule \<Sigma> _ (TyUnion _ _) = None" |
"subtyping_rule \<Sigma> (TyClass C _) (TyClass D _) =
  (if base \<Sigma> C = None then if C = D then Some RuleSubtyClass else None
   else if C = D then None
   else Some RuleSubtyClassExtend)" |
"subtyping_rule \<Sigma> (TyClass C _) _ = (if base \<Sigma> C = None then None else Some RuleSubtyClassExtend)" |
"subtyping_rule \<Sigma> _ (TyPrim Sized) = Some RuleSubtySized" |
"subtyping_rule \<Sigma> (TyList _) (TyList _) = Some RuleSubtyList" |
"subtyping_rule \<Sigma> (TyDict _) (TyDict _) = Some RuleSubtyDict" |
"subtyping_rule \<Sigma> (TyCallable \<sigma>s _) (TyCallable \<tau>s _) =
  (if length \<sigma>s = length \<tau>s then Some RuleSubtyCallable else None)" |
"subtyping_rule \<Sigma> (TyTuple \<sigma>s) (TyTuple \<tau>s) = (if length \<sigma>s = length \<tau>s then Some RuleSubtyTuple else None)" |
"subtyping_rule \<Sigma> (TyLiteral _) (TyLiteral _) = Some RuleSubtyLiteral" |
"subtyping_rule \<Sigma> _ _ = None"

(* Mismatch of type \<sigma> against expected type \<tau>, under the rule of subtyping selected by them, if any *)
definition mismatch :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> reason"
where
"mismatch \<Sigma> \<tau> \<sigma> =
  (case subtyping_rule \<Sigma> \<sigma> \<tau> of Some n \<Rightarrow> Violates n (TypeMismatch \<tau> \<sigma>) | None \<Rightarrow> TypeMismatch \<tau> \<sigma>)"

lemma subtys_list_all2: "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<longleftrightarrow> list_all2 (\<lambda>\<sigma> \<tau>. \<Sigma> \<turnstile> \<sigma> <: \<tau>) \<sigma>s \<tau>s"
proof
  show "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> list_all2 (\<lambda>\<sigma> \<tau>. \<Sigma> \<turnstile> \<sigma> <: \<tau>) \<sigma>s \<tau>s"
    by (induction \<sigma>s arbitrary: \<tau>s) (auto elim: subtys.cases)
  show "list_all2 (\<lambda>\<sigma> \<tau>. \<Sigma> \<turnstile> \<sigma> <: \<tau>) \<sigma>s \<tau>s \<Longrightarrow> \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s"
    by (induction rule: list_all2_induct) (auto intro: subty_subtys.intros)
qed

lemma subtys_Nil: "\<Sigma> \<turnstile> \<sigma>s [<:] [] \<Longrightarrow> \<sigma>s = []"
  by (simp add: subtys_list_all2)

(* Substitution of equivalent types for the same type variables *)
lemma subst_equiv:
  "list_all2 (\<lambda>\<sigma> \<tau>. \<Sigma> \<turnstile> \<sigma> \<approx> \<tau>) \<sigma>s \<tau>s \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma> \<approx> subst \<tau>s \<alpha>s \<sigma>"
proof (induction \<sigma>)
  case (TyVar \<alpha>)
  then show ?case
    using rel_option_map_of_zip[OF TyVar, of \<alpha>s \<alpha>]
    by (auto simp: rel_option_iff SubtyRefl split: option.splits)
qed (auto intro!: SubtyTuple SubtyCallable SubtyClass list.rel_refl_strong intro: subty_subtys.intros
      simp: subtys_list_all2 list_all2_map1 list_all2_map2)

(* Subtyping of a type other than a union by a union, as subtyping by one of its components *)
lemma nonunion_subty_union:
  "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<tau> = TyUnion \<tau>' \<tau>'' \<Longrightarrow> \<not> is_union \<sigma> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>' \<or> \<Sigma> \<turnstile> \<sigma> <: \<tau>''"
  and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s' \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyClassExtend C D \<sigma>s \<tau>s \<tau>)
  then show ?case by (auto intro: subty_subtys.SubtyClassExtend)
next
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) (auto intro: subty_subtys.SubtyLiteral)
qed (auto intro: subty_subtys.SubtyNever)

(* Subtyping by a list type of a type other than a union or Never, as a list type with an equivalent element
   type *)
lemma subty_list_inv:
  "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<tau> = TyList \<tau>' \<Longrightarrow> \<not> is_union \<sigma> \<Longrightarrow> \<sigma> \<noteq> TyPrim Never
    \<Longrightarrow> \<exists>\<sigma>'. \<sigma> = TyList \<sigma>' \<and> \<Sigma> \<turnstile> \<sigma>' <: \<tau>' \<and> \<Sigma> \<turnstile> \<tau>' <: \<sigma>'"
  and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) auto
qed (auto intro: subty_subtys.SubtyRefl)

lemma subty_list_iff:
  "\<lbrakk> \<not> is_union \<sigma> ; \<sigma> \<noteq> TyPrim Never \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyList \<tau> \<longleftrightarrow> (\<exists>\<sigma>'. \<sigma> = TyList \<sigma>' \<and> \<Sigma> \<turnstile> \<sigma>' \<approx> \<tau>)"
  by (auto dest: subty_list_inv(1)[OF _ refl] intro: SubtyList)

lemma subty_dict_inv:
  "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<tau> = TyDict \<tau>' \<Longrightarrow> \<not> is_union \<sigma> \<Longrightarrow> \<sigma> \<noteq> TyPrim Never
    \<Longrightarrow> \<exists>\<sigma>'. \<sigma> = TyDict \<sigma>' \<and> \<Sigma> \<turnstile> \<sigma>' <: \<tau>' \<and> \<Sigma> \<turnstile> \<tau>' <: \<sigma>'"
  and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) auto
qed (auto intro: subty_subtys.SubtyRefl)

lemma subty_tuple_inv:
  "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<tau> = TyTuple \<tau>s \<Longrightarrow> \<not> is_union \<sigma> \<Longrightarrow> \<sigma> \<noteq> TyPrim Never
    \<Longrightarrow> \<exists>\<sigma>s. \<sigma> = TyTuple \<sigma>s \<and> \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s"
  and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s' \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyRefl \<tau>)
  then show ?case by (auto simp: subtys_list_all2 intro: list.rel_refl subty_subtys.SubtyRefl)
next
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) auto
qed auto

(* Subtyping by a literal type of a type other than a union or Never, as the literal type itself *)
lemma subty_literal_inv:
  "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<tau> = TyLiteral l \<Longrightarrow> \<not> is_union \<sigma> \<Longrightarrow> \<sigma> \<noteq> TyPrim Never \<Longrightarrow> \<sigma> = TyLiteral l"
  and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyLiteral l' \<tau>)
  then show ?case by (cases l') auto
qed auto

lemma subty_callable_inv:
  "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<tau> = TyCallable \<tau>s \<tau>' \<Longrightarrow> \<not> is_union \<sigma> \<Longrightarrow> \<sigma> \<noteq> TyPrim Never
    \<Longrightarrow> \<exists>\<sigma>s \<sigma>'. \<sigma> = TyCallable \<sigma>s \<sigma>' \<and> \<Sigma> \<turnstile> \<tau>s [<:] \<sigma>s \<and> \<Sigma> \<turnstile> \<sigma>' <: \<tau>'"
  and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s'' \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyRefl \<tau>)
  then show ?case by (auto simp: subtys_list_all2 intro: list.rel_refl subty_subtys.SubtyRefl)
next
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) auto
qed auto

lemma subty_class_inv:
  "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<tau> = TyClass C \<tau>s \<Longrightarrow> \<not> is_union \<sigma> \<Longrightarrow> \<sigma> \<noteq> TyPrim Never \<Longrightarrow> \<exists>D \<sigma>s. \<sigma> = TyClass D \<sigma>s"
  and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s' \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) auto
qed auto

lemma elem_type_fv: "elem_type \<Sigma> \<sigma> = Some \<tau> \<Longrightarrow> fv \<tau> \<subseteq> fv \<sigma>"
proof (induction \<sigma> arbitrary: \<tau>)
  case (TyTuple \<sigma>s)
  then show ?case using fv_joins[of \<Sigma> "map base_type \<sigma>s"] by auto
next
  case (TyUnion \<sigma> \<sigma>')
  then show ?case by (auto simp: join_def split: option.splits if_splits)
qed (auto elim: elem_type.elims split: if_splits)

lemma lit_subty_base: "\<Sigma> \<turnstile> TyLiteral l <: base_type_lit l"
  by (rule SubtyLiteral) (rule SubtyRefl)

(* Class below range, which has no subclasses *)
lemma subty_range:
  assumes wf: "wf_class_table \<Sigma>"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<sigma> = TyClass C \<sigma>s \<Longrightarrow> \<tau> = TyClass range_class \<tau>s \<Longrightarrow> C |\<in>| fmdom \<Sigma>
    \<Longrightarrow> C = range_class"
    and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s' \<Longrightarrow> True"
proof (induction arbitrary: C \<sigma>s rule: subty_subtys.inducts)
  case (SubtyClassExtend C' D \<rho>s \<tau>s' \<tau>)
  then have "D \<noteq> range_class" and "D |\<in>| fmdom \<Sigma>" using wf_class_table_baseD[OF wf] by auto
  with SubtyClassExtend show ?case by auto
qed auto

(* Subtyping by Sized of a type other than a union or Never *)
lemma subty_sized_inv:
  "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<tau> = TyPrim Sized \<Longrightarrow> \<not> is_union \<sigma> \<Longrightarrow> \<sigma> \<noteq> TyPrim Never
    \<Longrightarrow> sized \<sigma> \<or> \<sigma> = TyPrim Sized \<or> (\<exists>w. \<sigma> = TyLiteral (LitString w))
      \<or> (\<exists>C \<sigma>s. \<sigma> = TyClass C \<sigma>s \<and> \<Sigma> \<turnstile> \<sigma> <: TyClass range_class [])"
  and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s' \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyClassExtend C D \<sigma>s \<tau>s \<tau>)
  let ?\<sigma> = "TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s)"
  from SubtyClassExtend(3, 4)
  have "sized ?\<sigma> \<or> (\<exists>C' \<sigma>s'. ?\<sigma> = TyClass C' \<sigma>s' \<and> \<Sigma> \<turnstile> ?\<sigma> <: TyClass range_class [])"
    by simp
  then have "\<Sigma> \<turnstile> ?\<sigma> <: TyClass range_class []"
  proof
    assume "sized ?\<sigma>"
    then have "D = range_class" and "map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s = []"
      by (cases "map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s"; simp)+
    then show ?thesis by (simp add: subty_subtys.SubtyRefl)
  qed blast
  with SubtyClassExtend(1) show ?case by (blast intro: subty_subtys.SubtyClassExtend)
next
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) auto
qed auto

(* Type built by union from class types and Never; closed downwards under subtyping *)
fun object_type :: "ty \<Rightarrow> bool"
where
"object_type (TyClass _ _) = True" |
"object_type (TyPrim Never) = True" |
"object_type (TyUnion \<sigma> \<tau>) = (object_type \<sigma> \<and> object_type \<tau>)" |
"object_type _ = False"

lemma object_type_subty: "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> object_type \<tau> \<Longrightarrow> object_type \<sigma>" and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) auto
qed auto

lemma object_type_subst: "object_type \<sigma> \<Longrightarrow> object_type (subst \<tau>s \<alpha>s \<sigma>)"
  by (induction \<sigma>) auto

lemma attribute_type_object_type: "attribute_type \<Sigma> \<sigma> x = Ok \<tau> \<Longrightarrow> object_type \<sigma>"
  by (induction \<Sigma> \<sigma> x arbitrary: \<tau> rule: attribute_type.induct) (auto simp: bind_sum_def split: sum.splits)

(* Field of class C at type arguments \<tau>s, equivalent to the field of a class above it *)
lemma subty_class_fields:
  assumes wf: "wf_class_table \<Sigma>"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> \<sigma> = TyClass C \<tau>s \<Longrightarrow> \<tau> = TyClass D \<sigma>s \<Longrightarrow> C |\<in>| fmdom \<Sigma>
    \<Longrightarrow> map_of (instantiate (fields \<Sigma> D) \<sigma>s) x = Some \<sigma>'
    \<Longrightarrow> \<exists>\<tau>'. map_of (instantiate (fields \<Sigma> C) \<tau>s) x = Some \<tau>' \<and> \<Sigma> \<turnstile> \<tau>' \<approx> \<sigma>'"
  and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s' \<Longrightarrow> True"
proof (induction arbitrary: C \<tau>s rule: subty_subtys.inducts)
  case (SubtyRefl \<tau>)
  then show ?case by (auto intro: subty_subtys.SubtyRefl)
next
  case (SubtyClassExtend C' D' \<rho>s \<tau>s' \<tau>)
  from SubtyClassExtend(4) have C': "C' = C" and \<tau>s': "\<tau>s' = \<tau>s" by simp_all
  note base = SubtyClassExtend(1)[unfolded C']
  have D': "D' |\<in>| fmdom \<Sigma>" using wf_class_table_baseD[OF wf SubtyClassExtend(6) base] by simp
  from SubtyClassExtend(3)[OF refl SubtyClassExtend(5) D' SubtyClassExtend(7)] obtain \<tau>' where
    "map_of (instantiate (fields \<Sigma> D') (map (subst \<tau>s' (type_params \<Sigma> C')) \<rho>s)) x = Some \<tau>'"
    and "\<Sigma> \<turnstile> \<tau>' \<approx> \<sigma>'" by blast
  with instantiate_fields_base[OF wf SubtyClassExtend(6) base] show ?case unfolding C' \<tau>s' by auto
next
  case (SubtyClass \<sigma>s' \<tau>s' C')
  from SubtyClass(5, 6) have "\<sigma>s' = \<tau>s" and "\<tau>s' = \<sigma>s" and D: "D = C" by simp_all
  with SubtyClass(1, 3) have equiv: "list_all2 (\<lambda>\<sigma> \<tau>. \<Sigma> \<turnstile> \<sigma> \<approx> \<tau>) \<tau>s \<sigma>s"
    by (auto simp: subtys_list_all2 list_all2_conv_all_nth)
  obtain \<alpha>s x\<sigma>s where fields: "fields \<Sigma> C = FieldScheme \<alpha>s x\<sigma>s" by (cases "fields \<Sigma> C")
  from subst_equiv[OF equiv] SubtyClass(8) fields D show ?case by (auto simp: map_of_map)
qed auto

(* Pair of types \<sigma> and \<tau> with each upper bound of \<tau> an upper bound of \<sigma>, and each lower bound of \<sigma> a lower
   bound of \<tau> *)
definition composable :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"
where
"composable \<Sigma> \<sigma> \<tau> = ((\<forall>\<tau>'. \<Sigma> \<turnstile> \<tau> <: \<tau>' \<longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>') \<and> (\<forall>\<rho>. \<Sigma> \<turnstile> \<rho> <: \<sigma> \<longrightarrow> \<Sigma> \<turnstile> \<rho> <: \<tau>))"

lemma composableI:
  "\<lbrakk> \<And>\<tau>'. \<Sigma> \<turnstile> \<tau> <: \<tau>' \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>' ; \<And>\<sigma>'. \<Sigma> \<turnstile> \<sigma>' <: \<sigma> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma>' <: \<tau> \<rbrakk>
  \<Longrightarrow> composable \<Sigma> \<sigma> \<tau>"
  unfolding composable_def by blast

lemma composable_upper: "\<lbrakk> composable \<Sigma> \<sigma> \<tau> ; \<Sigma> \<turnstile> \<tau> <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  and composable_lower: "\<lbrakk> composable \<Sigma> \<sigma> \<tau> ; \<Sigma> \<turnstile> \<sigma>' <: \<sigma> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma>' <: \<tau>"
  unfolding composable_def by blast+

lemma composable_subty: "composable \<Sigma> \<sigma> \<tau> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>"
  using composable_upper SubtyRefl by blast

lemma composable_upper_list: "\<lbrakk> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s ; \<Sigma> \<turnstile> \<tau>s [<:] \<tau>s' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s'"
  and composable_lower_list: "\<lbrakk> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s ; \<Sigma> \<turnstile> \<sigma>s' [<:] \<sigma>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s"
  unfolding subtys_list_all2 by (blast intro: list_all2_trans composable_upper composable_lower)+

lemma composable_equiv:
  "\<lbrakk> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s ; list_all2 (composable \<Sigma>) \<tau>s \<sigma>s \<rbrakk>
  \<Longrightarrow> list_all2 (\<lambda>\<sigma> \<tau>. \<Sigma> \<turnstile> \<sigma> \<approx> \<tau>) \<sigma>s \<tau>s"
  by (auto simp: list_all2_conv_all_nth composable_subty)

(* Subtyping at a type variable, from substitution of \<tau>s to substitution of \<sigma>s, when each type of \<sigma>s is
   composable with the corresponding type of \<tau>s *)
lemma composable_subst_var:
  assumes "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s"
  shows "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyVar \<alpha>) <: \<tau> \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s (TyVar \<alpha>) <: \<tau>"
    and "\<Sigma> \<turnstile> \<sigma> <: subst \<sigma>s \<alpha>s (TyVar \<alpha>) \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s (TyVar \<alpha>)"
  using rel_option_map_of_zip[OF assms, of \<alpha>s \<alpha>]
  by (auto simp: rel_option_iff split: option.splits intro: composable_upper composable_lower)

(* Substitution of composable types for the same type variables, on either side of a subtyping *)
lemma subst_composable:
  assumes wf: "wf_class_table \<Sigma>"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow>
           \<forall>\<sigma>s \<tau>s. list_all2 (composable \<Sigma>) \<sigma>s \<tau>s \<longrightarrow> list_all2 (composable \<Sigma>) \<tau>s \<sigma>s
             \<longrightarrow> (\<forall>\<sigma>'. wf_ty \<Sigma> \<sigma>' \<longrightarrow> \<sigma> = subst \<tau>s \<alpha>s \<sigma>' \<longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: \<tau>)
               \<and> (\<forall>\<tau>'. wf_ty \<Sigma> \<tau>' \<longrightarrow> \<tau> = subst \<sigma>s \<alpha>s \<tau>' \<longrightarrow> \<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s \<tau>')"
    and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s' \<Longrightarrow>
           \<forall>\<sigma>s \<tau>s. list_all2 (composable \<Sigma>) \<sigma>s \<tau>s \<longrightarrow> list_all2 (composable \<Sigma>) \<tau>s \<sigma>s
             \<longrightarrow> (\<forall>\<sigma>s''. (\<forall>\<sigma> \<in> set \<sigma>s''. wf_ty \<Sigma> \<sigma>) \<longrightarrow> \<sigma>s' = map (subst \<tau>s \<alpha>s) \<sigma>s''
                   \<longrightarrow> \<Sigma> \<turnstile> map (subst \<sigma>s \<alpha>s) \<sigma>s'' [<:] \<tau>s')
               \<and> (\<forall>\<tau>s''. (\<forall>\<tau> \<in> set \<tau>s''. wf_ty \<Sigma> \<tau>) \<longrightarrow> \<tau>s' = map (subst \<sigma>s \<alpha>s) \<tau>s''
                   \<longrightarrow> \<Sigma> \<turnstile> \<sigma>s' [<:] map (subst \<tau>s \<alpha>s) \<tau>s'')"
proof (induction rule: subty_subtys.inducts)
  case (SubtyRefl \<tau>)
  show ?case by (blast dest: composable_equiv subst_equiv[THEN conjunct1])
next
  case (SubtyClassExtend C D \<sigma>s' \<tau>s' \<tau>)
  let ?ps = "type_params \<Sigma> C"
  have sub: "\<Sigma> \<turnstile> TyClass C \<tau>s' <: \<tau>" using SubtyClassExtend(1,2) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<sigma>'
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf': "wf_ty \<Sigma> \<sigma>'" and eq: "TyClass C \<tau>s' = subst \<tau>s \<alpha>s \<sigma>'"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: \<tau>"
    proof (cases \<sigma>')
      case (TyVar \<alpha>)
      show ?thesis using sub unfolding eq TyVar by (rule composable_subst_var(1)[OF comp(1)])
    next
      case (TyClass C' \<tau>s'')
      with eq have [simp]: "C' = C" and \<tau>s': "\<tau>s' = map (subst \<tau>s \<alpha>s) \<tau>s''" by simp_all
      have wf_C: "wf_ty \<Sigma> (TyClass C \<tau>s'')" using wf' by (simp add: TyClass)
      note base = base_subst[OF wf wf_C SubtyClassExtend(1)]
      let ?\<sigma> = "TyClass D (map (subst \<tau>s'' ?ps) \<sigma>s')"
      have "TyClass D (map (subst \<tau>s' ?ps) \<sigma>s') = subst \<tau>s \<alpha>s ?\<sigma>" unfolding \<tau>s' by (rule base)
      with SubtyClassExtend(3) comp wf_class_table_base[OF wf wf_C SubtyClassExtend(1)]
      have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s ?\<sigma> <: \<tau>" by blast
      then have "\<Sigma> \<turnstile> TyClass D (map (subst (map (subst \<sigma>s \<alpha>s) \<tau>s'') ?ps) \<sigma>s') <: \<tau>" by (simp only: base)
      then show ?thesis using SubtyClassExtend(1) by (auto simp: TyClass intro: Subtyping.SubtyClassExtend)
    qed (use eq in simp_all)
  next
    fix \<sigma>s \<tau>s \<tau>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<tau>'"
      and "\<tau> = subst \<sigma>s \<alpha>s \<tau>'"
    with SubtyClassExtend(3) have "\<Sigma> \<turnstile> TyClass D (map (subst \<tau>s' ?ps) \<sigma>s') <: subst \<tau>s \<alpha>s \<tau>'" by blast
    then show "\<Sigma> \<turnstile> TyClass C \<tau>s' <: subst \<tau>s \<alpha>s \<tau>'"
      using SubtyClassExtend(1) by (blast intro: Subtyping.SubtyClassExtend)
  qed
next
  case (SubtyClass \<sigma>s' \<tau>s' C)
  have sub: "\<Sigma> \<turnstile> TyClass C \<sigma>s' <: TyClass C \<tau>s'" using SubtyClass(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<sigma>'
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf': "wf_ty \<Sigma> \<sigma>'" and eq: "TyClass C \<sigma>s' = subst \<tau>s \<alpha>s \<sigma>'"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyClass C \<tau>s'"
    proof (cases \<sigma>')
      case (TyVar \<alpha>)
      show ?thesis using sub unfolding eq TyVar by (rule composable_subst_var(1)[OF comp(1)])
    next
      case (TyClass C' \<sigma>s'')
      with eq wf' have "C' = C" "\<sigma>s' = map (subst \<tau>s \<alpha>s) \<sigma>s''" "\<forall>\<sigma> \<in> set \<sigma>s''. wf_ty \<Sigma> \<sigma>" by simp_all
      with SubtyClass(2,4) comp show ?thesis by (auto simp: TyClass intro!: subty_subtys.intros)
    qed (use eq in simp_all)
  next
    fix \<sigma>s \<tau>s \<tau>'
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf': "wf_ty \<Sigma> \<tau>'" and eq: "TyClass C \<tau>s' = subst \<sigma>s \<alpha>s \<tau>'"
    show "\<Sigma> \<turnstile> TyClass C \<sigma>s' <: subst \<tau>s \<alpha>s \<tau>'"
    proof (cases \<tau>')
      case (TyVar \<alpha>)
      show ?thesis using sub unfolding eq TyVar by (rule composable_subst_var(2)[OF comp(1)])
    next
      case (TyClass C' \<tau>s'')
      with eq wf' have "C' = C" "\<tau>s' = map (subst \<sigma>s \<alpha>s) \<tau>s''" "\<forall>\<tau> \<in> set \<tau>s''. wf_ty \<Sigma> \<tau>" by simp_all
      with SubtyClass(2,4) comp show ?thesis by (auto simp: TyClass intro!: subty_subtys.intros)
    qed (use eq in simp_all)
  qed
next
  case (SubtyNever \<tau>)
  have sub: "\<Sigma> \<turnstile> TyPrim Never <: \<tau>" by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<sigma>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<sigma>'"
    then have "TyPrim Never = subst \<tau>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: \<tau>"
      and "\<tau> = subst \<sigma>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> TyPrim Never <: subst \<tau>s \<alpha>s \<sigma>'"
      using sub by (cases \<sigma>'; auto intro: composable_subst_var[simplified] subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyObject \<tau>)
  have sub: "\<Sigma> \<turnstile> \<tau> <: TyPrim object" by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<sigma>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<sigma>'"
    then have "\<tau> = subst \<tau>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyPrim object"
      and "TyPrim object = subst \<sigma>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> \<tau> <: subst \<tau>s \<alpha>s \<sigma>'"
      using sub by (cases \<sigma>'; auto intro: composable_subst_var[simplified] subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyIntFloat)
  have sub: "\<Sigma> \<turnstile> TyPrim int <: TyPrim float" by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<sigma>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<sigma>'"
    then have "TyPrim int = subst \<tau>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyPrim float"
      and "TyPrim float = subst \<sigma>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> TyPrim int <: subst \<tau>s \<alpha>s \<sigma>'"
      using sub by (cases \<sigma>'; auto intro: composable_subst_var[simplified] subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyList \<sigma> \<tau>)
  have sub: "\<Sigma> \<turnstile> TyList \<sigma> <: TyList \<tau>" using SubtyList(1,3) by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<sigma>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<sigma>'"
    then have "TyList \<sigma> = subst \<tau>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyList \<tau>"
      and "TyList \<tau> = subst \<sigma>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> TyList \<sigma> <: subst \<tau>s \<alpha>s \<sigma>'"
      using sub SubtyList(2,4)
      by (cases \<sigma>'; auto intro: composable_subst_var[simplified] subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyDict \<sigma> \<tau>)
  have sub: "\<Sigma> \<turnstile> TyDict \<sigma> <: TyDict \<tau>" using SubtyDict(1,3) by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<sigma>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<sigma>'"
    then have "TyDict \<sigma> = subst \<tau>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyDict \<tau>"
      and "TyDict \<tau> = subst \<sigma>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> TyDict \<sigma> <: subst \<tau>s \<alpha>s \<sigma>'"
      using sub SubtyDict(2,4)
      by (cases \<sigma>'; auto intro: composable_subst_var[simplified] subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyCallable \<tau>s' \<sigma>s' \<sigma> \<tau>)
  have sub: "\<Sigma> \<turnstile> TyCallable \<sigma>s' \<sigma> <: TyCallable \<tau>s' \<tau>" using SubtyCallable(1,3) by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<sigma>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<sigma>'"
    then have "TyCallable \<sigma>s' \<sigma> = subst \<tau>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyCallable \<tau>s' \<tau>"
      and "TyCallable \<tau>s' \<tau> = subst \<sigma>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> TyCallable \<sigma>s' \<sigma> <: subst \<tau>s \<alpha>s \<sigma>'"
      using sub SubtyCallable(2,4)
      by (cases \<sigma>'; auto intro: composable_subst_var[simplified] subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyTuple \<sigma>s' \<tau>s')
  have sub: "\<Sigma> \<turnstile> TyTuple \<sigma>s' <: TyTuple \<tau>s'" using SubtyTuple(1) by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<sigma>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<sigma>'"
    then have "TyTuple \<sigma>s' = subst \<tau>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyTuple \<tau>s'"
      and "TyTuple \<tau>s' = subst \<sigma>s \<alpha>s \<sigma>' \<Longrightarrow> \<Sigma> \<turnstile> TyTuple \<sigma>s' <: subst \<tau>s \<alpha>s \<sigma>'"
      using sub SubtyTuple(2)
      by (cases \<sigma>'; auto intro: composable_subst_var[simplified] subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtySized \<tau>)
  have sub: "\<Sigma> \<turnstile> \<tau> <: TyPrim Sized" using SubtySized(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<sigma>'
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and eq: "\<tau> = subst \<tau>s \<alpha>s \<sigma>'"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyPrim Sized"
    proof (cases "\<exists>\<alpha>. \<sigma>' = TyVar \<alpha>")
      case True
      then obtain \<alpha> where var: "\<sigma>' = TyVar \<alpha>" ..
      show ?thesis using sub unfolding eq var by (rule composable_subst_var(1)[OF comp(1)])
    next
      case False
      with SubtySized(1) eq have "sized (subst \<sigma>s \<alpha>s \<sigma>')" by (simp add: sized_subst)
      then show ?thesis by (rule subty_subtys.intros)
    qed
  next
    fix \<sigma>s \<tau>s \<tau>'
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and eq: "TyPrim Sized = subst \<sigma>s \<alpha>s \<tau>'"
    show "\<Sigma> \<turnstile> \<tau> <: subst \<tau>s \<alpha>s \<tau>'"
    proof (cases \<tau>')
      case (TyVar \<alpha>)
      show ?thesis using sub unfolding eq TyVar by (rule composable_subst_var(2)[OF comp(1)])
    qed (use eq SubtySized(1) in \<open>auto intro: subty_subtys.intros\<close>)
  qed
next
  case (SubtyLiteral l \<tau>)
  have sub: "\<Sigma> \<turnstile> TyLiteral l <: \<tau>" using SubtyLiteral(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<sigma>'
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and eq: "TyLiteral l = subst \<tau>s \<alpha>s \<sigma>'"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: \<tau>"
    proof (cases \<sigma>')
      case (TyVar \<alpha>)
      show ?thesis using sub unfolding eq TyVar by (rule composable_subst_var(1)[OF comp(1)])
    qed (use eq sub in simp_all)
  next
    fix \<sigma>s \<tau>s \<tau>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<tau>'"
      and "\<tau> = subst \<sigma>s \<alpha>s \<tau>'"
    with SubtyLiteral(2) have "\<Sigma> \<turnstile> base_type_lit l <: subst \<tau>s \<alpha>s \<tau>'" by blast
    then show "\<Sigma> \<turnstile> TyLiteral l <: subst \<tau>s \<alpha>s \<tau>'" by (rule Subtyping.SubtyLiteral)
  qed
next
  case (SubtyUnionLeft \<sigma> \<tau> \<tau>')
  have sub: "\<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" using SubtyUnionLeft(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<sigma>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<sigma>'"
      and "\<sigma> = subst \<tau>s \<alpha>s \<sigma>'"
    with SubtyUnionLeft(2) have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: \<tau>" by blast
    then show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyUnion \<tau> \<tau>'" by (rule Subtyping.SubtyUnionLeft)
  next
    fix \<sigma>s \<tau>s \<tau>''
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf': "wf_ty \<Sigma> \<tau>''" and eq: "TyUnion \<tau> \<tau>' = subst \<sigma>s \<alpha>s \<tau>''"
    show "\<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s \<tau>''"
    proof (cases \<tau>'')
      case (TyVar \<alpha>)
      show ?thesis using sub unfolding eq TyVar by (rule composable_subst_var(2)[OF comp(1)])
    next
      case (TyUnion \<sigma>' \<sigma>'')
      with eq wf' have "\<tau> = subst \<sigma>s \<alpha>s \<sigma>'" "wf_ty \<Sigma> \<sigma>'" by simp_all
      with SubtyUnionLeft(2) comp have "\<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s \<sigma>'" by blast
      then show ?thesis by (simp add: TyUnion Subtyping.SubtyUnionLeft)
    qed (use eq in simp_all)
  qed
next
  case (SubtyUnionRight \<sigma> \<tau>' \<tau>)
  have sub: "\<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" using SubtyUnionRight(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<sigma>'
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<sigma>'"
      and "\<sigma> = subst \<tau>s \<alpha>s \<sigma>'"
    with SubtyUnionRight(2) have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: \<tau>'" by blast
    then show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: TyUnion \<tau> \<tau>'" by (rule Subtyping.SubtyUnionRight)
  next
    fix \<sigma>s \<tau>s \<tau>''
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf': "wf_ty \<Sigma> \<tau>''" and eq: "TyUnion \<tau> \<tau>' = subst \<sigma>s \<alpha>s \<tau>''"
    show "\<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s \<tau>''"
    proof (cases \<tau>'')
      case (TyVar \<alpha>)
      show ?thesis using sub unfolding eq TyVar by (rule composable_subst_var(2)[OF comp(1)])
    next
      case (TyUnion \<sigma>' \<sigma>'')
      with eq wf' have "\<tau>' = subst \<sigma>s \<alpha>s \<sigma>''" "wf_ty \<Sigma> \<sigma>''" by simp_all
      with SubtyUnionRight(2) comp have "\<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s \<sigma>''" by blast
      then show ?thesis by (simp add: TyUnion Subtyping.SubtyUnionRight)
    qed (use eq in simp_all)
  qed
next
  case (SubtyUnion \<tau> \<sigma> \<tau>')
  have sub: "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<sigma>" using SubtyUnion(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<sigma>'
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf': "wf_ty \<Sigma> \<sigma>'" and eq: "TyUnion \<tau> \<tau>' = subst \<tau>s \<alpha>s \<sigma>'"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>' <: \<sigma>"
    proof (cases \<sigma>')
      case (TyVar \<alpha>)
      show ?thesis using sub unfolding eq TyVar by (rule composable_subst_var(1)[OF comp(1)])
    next
      case (TyUnion \<sigma>'' \<tau>'')
      with eq wf' have "\<tau> = subst \<tau>s \<alpha>s \<sigma>''" "\<tau>' = subst \<tau>s \<alpha>s \<tau>''" "wf_ty \<Sigma> \<sigma>''" "wf_ty \<Sigma> \<tau>''"
        by simp_all
      with SubtyUnion(2,4) comp have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<sigma>'' <: \<sigma>" "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<tau>'' <: \<sigma>"
        by blast+
      then show ?thesis by (simp add: TyUnion Subtyping.SubtyUnion)
    qed (use eq in simp_all)
  next
    fix \<sigma>s \<tau>s \<tau>''
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<tau>''"
      and "\<sigma> = subst \<sigma>s \<alpha>s \<tau>''"
    with SubtyUnion(2,4) have "\<Sigma> \<turnstile> \<tau> <: subst \<tau>s \<alpha>s \<tau>''" "\<Sigma> \<turnstile> \<tau>' <: subst \<tau>s \<alpha>s \<tau>''" by blast+
    then show "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: subst \<tau>s \<alpha>s \<tau>''" by (rule Subtyping.SubtyUnion)
  qed
next
  case SubtysNil
  show ?case by (auto intro: subty_subtys.intros)
next
  case (SubtysCons \<sigma> \<tau> \<sigma>s' \<tau>s')
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<sigma>s''
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf': "\<forall>\<sigma> \<in> set \<sigma>s''. wf_ty \<Sigma> \<sigma>" and eq: "\<sigma> # \<sigma>s' = map (subst \<tau>s \<alpha>s) \<sigma>s''"
    then show "\<Sigma> \<turnstile> map (subst \<sigma>s \<alpha>s) \<sigma>s'' [<:] \<tau> # \<tau>s'"
      using SubtysCons(2,4) by (cases \<sigma>s'') (simp_all add: Subtyping.SubtysCons)
  next
    fix \<sigma>s \<tau>s \<tau>s''
    assume comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf': "\<forall>\<tau> \<in> set \<tau>s''. wf_ty \<Sigma> \<tau>" and eq: "\<tau> # \<tau>s' = map (subst \<sigma>s \<alpha>s) \<tau>s''"
    then show "\<Sigma> \<turnstile> \<sigma> # \<sigma>s' [<:] map (subst \<tau>s \<alpha>s) \<tau>s''"
      using SubtysCons(2,4) by (cases \<tau>s'') (simp_all add: Subtyping.SubtysCons)
  qed
qed

(* Subtyping of \<sigma> by \<tau>', from subtyping of \<sigma> by \<tau>, by the last rule of the derivation: each rule which fixes
   the form of \<tau> gives a hypothesis, and the other rules carry over *)
lemma subty_supertype_cases:
  assumes "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    and refl: "\<Sigma> \<turnstile> \<tau> <: \<tau>'"
    and class_args:
      "\<And>C \<sigma>s \<tau>s. \<lbrakk> \<tau> = TyClass C \<tau>s ; \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s ; \<Sigma> \<turnstile> \<tau>s [<:] \<sigma>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyClass C \<sigma>s <: \<tau>'"
    and object: "\<And>\<sigma>. \<tau> = TyPrim object \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and int_float: "\<tau> = TyPrim float \<Longrightarrow> \<Sigma> \<turnstile> TyPrim int <: \<tau>'"
    and sized: "\<And>\<sigma>. \<lbrakk> \<tau> = TyPrim Sized ; sized \<sigma> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and list: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<tau> = TyList \<sigma>' ; \<Sigma> \<turnstile> \<sigma> <: \<sigma>' ; \<Sigma> \<turnstile> \<sigma>' <: \<sigma> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyList \<sigma> <: \<tau>'"
    and dict: "\<And>\<sigma> \<sigma>'. \<lbrakk> \<tau> = TyDict \<sigma>' ; \<Sigma> \<turnstile> \<sigma> <: \<sigma>' ; \<Sigma> \<turnstile> \<sigma>' <: \<sigma> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyDict \<sigma> <: \<tau>'"
    and callable:
      "\<And>\<sigma>s \<sigma> \<tau>s \<sigma>'. \<lbrakk> \<tau> = TyCallable \<tau>s \<sigma>' ; \<Sigma> \<turnstile> \<tau>s [<:] \<sigma>s ; \<Sigma> \<turnstile> \<sigma> <: \<sigma>' \<rbrakk>
                    \<Longrightarrow> \<Sigma> \<turnstile> TyCallable \<sigma>s \<sigma> <: \<tau>'"
    and tuple: "\<And>\<sigma>s \<tau>s. \<lbrakk> \<tau> = TyTuple \<tau>s ; \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyTuple \<sigma>s <: \<tau>'"
    and union_left: "\<And>\<sigma> \<sigma>' \<sigma>''. \<lbrakk> \<tau> = TyUnion \<sigma>' \<sigma>'' ; \<Sigma> \<turnstile> \<sigma> <: \<sigma>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and union_right: "\<And>\<sigma> \<sigma>' \<sigma>''. \<lbrakk> \<tau> = TyUnion \<sigma>' \<sigma>'' ; \<Sigma> \<turnstile> \<sigma> <: \<sigma>'' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau>'"
proof -
  have "\<Sigma> \<turnstile> \<sigma> <: \<sigma>' \<Longrightarrow> \<sigma>' = \<tau> \<longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'" and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> True" for \<sigma> \<sigma>' \<sigma>s \<tau>s
  proof (induction rule: subty_subtys.inducts)
    case SubtyRefl
    then show ?case using refl by blast
  next
    case SubtyClassExtend
    then show ?case by (blast intro: Subtyping.SubtyClassExtend)
  next
    case SubtyClass
    then show ?case using class_args by blast
  next
    case SubtyNever
    show ?case by (blast intro: Subtyping.SubtyNever)
  next
    case SubtyObject
    show ?case using object by blast
  next
    case SubtyIntFloat
    show ?case using int_float by blast
  next
    case SubtySized
    then show ?case using sized by blast
  next
    case SubtyList
    then show ?case using list by blast
  next
    case SubtyDict
    then show ?case using dict by blast
  next
    case SubtyCallable
    then show ?case using callable by blast
  next
    case SubtyTuple
    then show ?case using tuple by blast
  next
    case SubtyLiteral
    then show ?case by (blast intro: Subtyping.SubtyLiteral)
  next
    case SubtyUnionLeft
    then show ?case using union_left by blast
  next
    case SubtyUnionRight
    then show ?case using union_right by blast
  next
    case SubtyUnion
    then show ?case by (blast intro: Subtyping.SubtyUnion)
  qed simp_all
  with assms(1) show ?thesis by blast
qed

(* Subtyping of \<sigma> by \<tau>', from subtyping of \<tau> by \<tau>', by the last rule of the derivation: each rule which fixes
   the form of \<tau> gives a hypothesis, and the other rules carry over *)
lemma subty_subtype_cases:
  assumes "\<Sigma> \<turnstile> \<tau> <: \<tau>'"
    and refl: "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    and class_extend:
      "\<And>C \<tau>s D \<sigma>s \<tau>'. \<lbrakk> \<tau> = TyClass C \<tau>s ; base \<Sigma> C = Some (D, \<sigma>s)
                  ; \<Sigma> \<turnstile> TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s) <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and class_args:
      "\<And>C \<tau>s \<tau>s'. \<lbrakk> \<tau> = TyClass C \<tau>s ; \<Sigma> \<turnstile> \<tau>s [<:] \<tau>s' ; \<Sigma> \<turnstile> \<tau>s' [<:] \<tau>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyClass C \<tau>s'"
    and never: "\<And>\<tau>'. \<tau> = TyPrim Never \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and int_float: "\<tau> = TyPrim int \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyPrim float"
    and sized: "sized \<tau> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyPrim Sized"
    and list: "\<And>\<sigma>' \<tau>'. \<lbrakk> \<tau> = TyList \<sigma>' ; \<Sigma> \<turnstile> \<sigma>' <: \<tau>' ; \<Sigma> \<turnstile> \<tau>' <: \<sigma>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyList \<tau>'"
    and dict: "\<And>\<sigma>' \<tau>'. \<lbrakk> \<tau> = TyDict \<sigma>' ; \<Sigma> \<turnstile> \<sigma>' <: \<tau>' ; \<Sigma> \<turnstile> \<tau>' <: \<sigma>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyDict \<tau>'"
    and callable:
      "\<And>\<tau>s \<sigma>' \<tau>s' \<tau>'. \<lbrakk> \<tau> = TyCallable \<tau>s \<sigma>' ; \<Sigma> \<turnstile> \<tau>s' [<:] \<tau>s ; \<Sigma> \<turnstile> \<sigma>' <: \<tau>' \<rbrakk>
                    \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyCallable \<tau>s' \<tau>'"
    and tuple: "\<And>\<tau>s \<tau>s'. \<lbrakk> \<tau> = TyTuple \<tau>s ; \<Sigma> \<turnstile> \<tau>s [<:] \<tau>s' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyTuple \<tau>s'"
    and literal: "\<And>l \<tau>'. \<lbrakk> \<tau> = TyLiteral l ; \<Sigma> \<turnstile> base_type_lit l <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
    and union:
      "\<And>\<sigma>' \<sigma>'' \<tau>'. \<lbrakk> \<tau> = TyUnion \<sigma>' \<sigma>'' ; \<Sigma> \<turnstile> \<sigma>' <: \<tau>' ; \<Sigma> \<turnstile> \<sigma>'' <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau>'"
proof -
  have "\<Sigma> \<turnstile> \<sigma>' <: \<tau>' \<Longrightarrow> \<sigma>' = \<tau> \<longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'" and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> True" for \<sigma>' \<tau>' \<sigma>s \<tau>s
  proof (induction rule: subty_subtys.inducts)
    case SubtyRefl
    then show ?case using refl by blast
  next
    case SubtyClassExtend
    then show ?case using class_extend by blast
  next
    case SubtyClass
    then show ?case using class_args by blast
  next
    case SubtyNever
    show ?case using never by blast
  next
    case SubtyObject
    show ?case by (blast intro: Subtyping.SubtyObject)
  next
    case SubtyIntFloat
    show ?case using int_float by blast
  next
    case SubtySized
    then show ?case using sized by blast
  next
    case SubtyList
    then show ?case using list by blast
  next
    case SubtyDict
    then show ?case using dict by blast
  next
    case SubtyCallable
    then show ?case using callable by blast
  next
    case SubtyTuple
    then show ?case using tuple by blast
  next
    case SubtyLiteral
    then show ?case using literal by blast
  next
    case SubtyUnionLeft
    then show ?case by (blast intro: Subtyping.SubtyUnionLeft)
  next
    case SubtyUnionRight
    then show ?case by (blast intro: Subtyping.SubtyUnionRight)
  next
    case SubtyUnion
    then show ?case using union by blast
  qed simp_all
  with assms(1) show ?thesis by blast
qed

theorem subty_composable:
  assumes wf: "wf_class_table \<Sigma>"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> wf_ty \<Sigma> \<sigma> \<longrightarrow> wf_ty \<Sigma> \<tau> \<longrightarrow> composable \<Sigma> \<sigma> \<tau>"
    and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s
           \<Longrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>) \<longrightarrow> (\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>) \<longrightarrow> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s"
proof (induction rule: subty_subtys.inducts)
  case (SubtyRefl \<tau>)
  show ?case unfolding composable_def by blast
next
  case (SubtyClassExtend C D \<sigma>s \<tau>s \<tau>)
  let ?\<sigma> = "TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<sigma>s)"
  have sub: "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>" using SubtyClassExtend(1,2) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI)
    assume wf_C: "wf_ty \<Sigma> (TyClass C \<tau>s)" and "wf_ty \<Sigma> \<tau>"
    with SubtyClassExtend(3) wf_class_table_base[OF wf wf_C SubtyClassExtend(1)]
    have comp: "composable \<Sigma> ?\<sigma> \<tau>" by blast
    show "composable \<Sigma> (TyClass C \<tau>s) \<tau>"
    proof (rule composableI)
      fix \<tau>'
      assume "\<Sigma> \<turnstile> \<tau> <: \<tau>'"
      with comp have "\<Sigma> \<turnstile> ?\<sigma> <: \<tau>'" by (rule composable_upper)
      then show "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>'" using SubtyClassExtend(1) by (blast intro: Subtyping.SubtyClassExtend)
    next
      fix \<sigma>'
      assume "\<Sigma> \<turnstile> \<sigma>' <: TyClass C \<tau>s"
      then show "\<Sigma> \<turnstile> \<sigma>' <: \<tau>"
      proof (rule subty_supertype_cases)
        show "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>" by (rule sub)
        fix C' \<sigma>s' \<tau>s'
        assume "TyClass C \<tau>s = TyClass C' \<tau>s'" and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<tau>s'" and "\<Sigma> \<turnstile> \<tau>s' [<:] \<sigma>s'"
        then have "\<Sigma> \<turnstile> TyClass D (map (subst \<sigma>s' (type_params \<Sigma> C)) \<sigma>s) <: ?\<sigma>"
          using subst_equiv[of \<Sigma> \<sigma>s' \<tau>s "type_params \<Sigma> C" "TyClass D \<sigma>s"]
          by (auto simp: subtys_list_all2 list_all2_conv_all_nth)
        with comp have "\<Sigma> \<turnstile> TyClass D (map (subst \<sigma>s' (type_params \<Sigma> C)) \<sigma>s) <: \<tau>" by (rule composable_lower)
        with \<open>TyClass C \<tau>s = TyClass C' \<tau>s'\<close> show "\<Sigma> \<turnstile> TyClass C' \<sigma>s' <: \<tau>"
          using SubtyClassExtend(1) by (auto intro: Subtyping.SubtyClassExtend)
      qed simp_all
    qed
  qed
next
  case (SubtyClass \<sigma>s \<tau>s C)
  have sub: "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass C \<tau>s" using SubtyClass(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI)
    assume "wf_ty \<Sigma> (TyClass C \<sigma>s)" and wf_C: "wf_ty \<Sigma> (TyClass C \<tau>s)"
    with SubtyClass(2,4) have comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      by simp_all
    show "composable \<Sigma> (TyClass C \<sigma>s) (TyClass C \<tau>s)"
    proof (rule composableI)
      fix \<tau>'
      assume "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>'"
      then show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: \<tau>'"
      proof (rule subty_subtype_cases)
        show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass C \<tau>s" by (rule sub)
        fix C' \<tau>s' D \<sigma>s' \<tau>'
        assume eq: "TyClass C \<tau>s = TyClass C' \<tau>s'" and base: "base \<Sigma> C' = Some (D, \<sigma>s')"
          and sub': "\<Sigma> \<turnstile> TyClass D (map (subst \<tau>s' (type_params \<Sigma> C')) \<sigma>s') <: \<tau>'"
        let ?ps = "type_params \<Sigma> C"
        from eq have [simp]: "C' = C" "\<tau>s' = \<tau>s" by simp_all
        have wf_D: "wf_ty \<Sigma> (TyClass D \<sigma>s')" using wf wf_C base unfolding wf_class_table_def by auto
        have "TyClass D (map (subst \<tau>s' (type_params \<Sigma> C')) \<sigma>s') = subst \<tau>s ?ps (TyClass D \<sigma>s')" by simp
        then have "\<Sigma> \<turnstile> subst \<sigma>s ?ps (TyClass D \<sigma>s') <: \<tau>'"
          using subst_composable(1)[OF wf sub', where \<alpha>s = ?ps] comp wf_D by blast
        then show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: \<tau>'" using base by (auto intro: Subtyping.SubtyClassExtend)
      next
        fix C' \<tau>s' \<tau>s''
        assume "TyClass C \<tau>s = TyClass C' \<tau>s'" and "\<Sigma> \<turnstile> \<tau>s' [<:] \<tau>s''" and "\<Sigma> \<turnstile> \<tau>s'' [<:] \<tau>s'"
        with comp show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass C' \<tau>s''"
          by (auto intro: Subtyping.SubtyClass composable_upper_list composable_lower_list)
      next
        assume "sized (TyClass C \<tau>s)"
        with SubtyClass(1) show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyPrim Sized"
          by (auto intro: Subtyping.SubtySized dest: subtys_Nil elim: sized.elims)
      qed simp_all
    next
      fix \<sigma>'
      assume "\<Sigma> \<turnstile> \<sigma>' <: TyClass C \<sigma>s"
      then show "\<Sigma> \<turnstile> \<sigma>' <: TyClass C \<tau>s"
      proof (rule subty_supertype_cases)
        show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass C \<tau>s" by (rule sub)
        fix C' \<sigma>s' \<sigma>s''
        assume "TyClass C \<sigma>s = TyClass C' \<sigma>s''" and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<sigma>s''" and "\<Sigma> \<turnstile> \<sigma>s'' [<:] \<sigma>s'"
        with comp show "\<Sigma> \<turnstile> TyClass C' \<sigma>s' <: TyClass C \<tau>s"
          by (auto intro: Subtyping.SubtyClass composable_upper_list composable_lower_list)
      qed simp_all
    qed
  qed
next
  case (SubtyNever \<tau>)
  show ?case
  proof (intro impI composableI)
    fix \<sigma>
    assume "\<Sigma> \<turnstile> \<sigma> <: TyPrim Never"
    then show "\<Sigma> \<turnstile> \<sigma> <: \<tau>" by (rule subty_supertype_cases) (simp_all add: Subtyping.SubtyNever)
  qed (rule Subtyping.SubtyNever)
next
  case (SubtyObject \<sigma>)
  show ?case
  proof (intro impI composableI)
    fix \<tau>
    assume "\<Sigma> \<turnstile> TyPrim object <: \<tau>"
    then show "\<Sigma> \<turnstile> \<sigma> <: \<tau>" by (rule subty_subtype_cases) (simp_all add: Subtyping.SubtyObject)
  qed (rule Subtyping.SubtyObject)
next
  case SubtyIntFloat
  show ?case
  proof (intro impI composableI)
    fix \<tau>
    assume "\<Sigma> \<turnstile> TyPrim float <: \<tau>"
    then show "\<Sigma> \<turnstile> TyPrim int <: \<tau>" by (rule subty_subtype_cases) (simp_all add: Subtyping.SubtyIntFloat)
  next
    fix \<sigma>
    assume "\<Sigma> \<turnstile> \<sigma> <: TyPrim int"
    then show "\<Sigma> \<turnstile> \<sigma> <: TyPrim float" by (rule subty_supertype_cases) (simp_all add: Subtyping.SubtyIntFloat)
  qed
next
  case (SubtySized \<sigma>)
  have sub: "\<Sigma> \<turnstile> \<sigma> <: TyPrim Sized" using SubtySized(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    fix \<tau>
    assume "\<Sigma> \<turnstile> TyPrim Sized <: \<tau>"
    then show "\<Sigma> \<turnstile> \<sigma> <: \<tau>" by (rule subty_subtype_cases) (simp_all add: sub)
  next
    fix \<sigma>'
    assume "\<Sigma> \<turnstile> \<sigma>' <: \<sigma>"
    then show "\<Sigma> \<turnstile> \<sigma>' <: TyPrim Sized"
      by (rule subty_supertype_cases)
         (insert SubtySized(1) sub, auto intro: Subtyping.SubtySized dest: subtys_Nil elim: sized.elims)
  qed
next
  case (SubtyList \<sigma> \<tau>)
  have sub: "\<Sigma> \<turnstile> TyList \<sigma> <: TyList \<tau>" using SubtyList(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI)
    assume "wf_ty \<Sigma> (TyList \<sigma>)" "wf_ty \<Sigma> (TyList \<tau>)"
    with SubtyList(2,4) have comp: "composable \<Sigma> \<sigma> \<tau>" "composable \<Sigma> \<tau> \<sigma>" by simp_all
    show "composable \<Sigma> (TyList \<sigma>) (TyList \<tau>)"
    proof (rule composableI)
      fix \<tau>'
      assume "\<Sigma> \<turnstile> TyList \<tau> <: \<tau>'"
      then show "\<Sigma> \<turnstile> TyList \<sigma> <: \<tau>'"
        by (rule subty_subtype_cases)
           (auto simp: sub intro: Subtyping.SubtySized Subtyping.SubtyList composable_upper[OF comp(1)]
              composable_lower[OF comp(2)])
    next
      fix \<sigma>'
      assume "\<Sigma> \<turnstile> \<sigma>' <: TyList \<sigma>"
      then show "\<Sigma> \<turnstile> \<sigma>' <: TyList \<tau>"
        by (rule subty_supertype_cases)
           (auto simp: sub intro: Subtyping.SubtyList composable_lower[OF comp(1)] composable_upper[OF comp(2)])
    qed
  qed
next
  case (SubtyDict \<sigma> \<tau>)
  have sub: "\<Sigma> \<turnstile> TyDict \<sigma> <: TyDict \<tau>" using SubtyDict(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI)
    assume "wf_ty \<Sigma> (TyDict \<sigma>)" "wf_ty \<Sigma> (TyDict \<tau>)"
    with SubtyDict(2,4) have comp: "composable \<Sigma> \<sigma> \<tau>" "composable \<Sigma> \<tau> \<sigma>" by simp_all
    show "composable \<Sigma> (TyDict \<sigma>) (TyDict \<tau>)"
    proof (rule composableI)
      fix \<tau>'
      assume "\<Sigma> \<turnstile> TyDict \<tau> <: \<tau>'"
      then show "\<Sigma> \<turnstile> TyDict \<sigma> <: \<tau>'"
        by (rule subty_subtype_cases)
           (auto simp: sub intro: Subtyping.SubtySized Subtyping.SubtyDict composable_upper[OF comp(1)]
              composable_lower[OF comp(2)])
    next
      fix \<sigma>'
      assume "\<Sigma> \<turnstile> \<sigma>' <: TyDict \<sigma>"
      then show "\<Sigma> \<turnstile> \<sigma>' <: TyDict \<tau>"
        by (rule subty_supertype_cases)
           (auto simp: sub intro: Subtyping.SubtyDict composable_lower[OF comp(1)] composable_upper[OF comp(2)])
    qed
  qed
next
  case (SubtyCallable \<tau>s \<sigma>s \<sigma> \<tau>)
  have sub: "\<Sigma> \<turnstile> TyCallable \<sigma>s \<sigma> <: TyCallable \<tau>s \<tau>" using SubtyCallable(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI)
    assume "wf_ty \<Sigma> (TyCallable \<sigma>s \<sigma>)" "wf_ty \<Sigma> (TyCallable \<tau>s \<tau>)"
    with SubtyCallable(2,4) have comp: "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "composable \<Sigma> \<sigma> \<tau>" by simp_all
    show "composable \<Sigma> (TyCallable \<sigma>s \<sigma>) (TyCallable \<tau>s \<tau>)"
    proof (rule composableI)
      fix \<tau>'
      assume "\<Sigma> \<turnstile> TyCallable \<tau>s \<tau> <: \<tau>'"
      then show "\<Sigma> \<turnstile> TyCallable \<sigma>s \<sigma> <: \<tau>'"
        by (rule subty_subtype_cases)
           (auto simp: sub intro: Subtyping.SubtyCallable composable_lower_list[OF comp(1)]
              composable_upper[OF comp(2)])
    next
      fix \<sigma>'
      assume "\<Sigma> \<turnstile> \<sigma>' <: TyCallable \<sigma>s \<sigma>"
      then show "\<Sigma> \<turnstile> \<sigma>' <: TyCallable \<tau>s \<tau>"
        by (rule subty_supertype_cases)
           (auto simp: sub intro: Subtyping.SubtyCallable composable_upper_list[OF comp(1)]
              composable_lower[OF comp(2)])
    qed
  qed
next
  case (SubtyTuple \<sigma>s \<tau>s)
  have sub: "\<Sigma> \<turnstile> TyTuple \<sigma>s <: TyTuple \<tau>s" using SubtyTuple(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI)
    assume "wf_ty \<Sigma> (TyTuple \<sigma>s)" "wf_ty \<Sigma> (TyTuple \<tau>s)"
    with SubtyTuple(2) have comp: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" by simp
    show "composable \<Sigma> (TyTuple \<sigma>s) (TyTuple \<tau>s)"
    proof (rule composableI)
      fix \<tau>'
      assume "\<Sigma> \<turnstile> TyTuple \<tau>s <: \<tau>'"
      then show "\<Sigma> \<turnstile> TyTuple \<sigma>s <: \<tau>'"
        by (rule subty_subtype_cases)
           (auto simp: sub intro: Subtyping.SubtySized Subtyping.SubtyTuple composable_upper_list[OF comp])
    next
      fix \<sigma>'
      assume "\<Sigma> \<turnstile> \<sigma>' <: TyTuple \<sigma>s"
      then show "\<Sigma> \<turnstile> \<sigma>' <: TyTuple \<tau>s"
        by (rule subty_supertype_cases)
           (auto simp: sub intro: Subtyping.SubtyTuple composable_lower_list[OF comp])
    qed
  qed
next
  case (SubtyLiteral l \<tau>)
  have sub: "\<Sigma> \<turnstile> TyLiteral l <: \<tau>" using SubtyLiteral(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume "wf_ty \<Sigma> \<tau>"
    with SubtyLiteral(2) have comp: "composable \<Sigma> (base_type_lit l) \<tau>" by (cases l) simp_all
    fix \<tau>'
    assume "\<Sigma> \<turnstile> \<tau> <: \<tau>'"
    with comp have "\<Sigma> \<turnstile> base_type_lit l <: \<tau>'" by (rule composable_upper)
    then show "\<Sigma> \<turnstile> TyLiteral l <: \<tau>'" by (rule Subtyping.SubtyLiteral)
  next
    fix \<sigma>
    assume "\<Sigma> \<turnstile> \<sigma> <: TyLiteral l"
    then show "\<Sigma> \<turnstile> \<sigma> <: \<tau>" by (rule subty_supertype_cases) (simp_all add: sub)
  qed
next
  case (SubtyUnionLeft \<sigma> \<tau> \<tau>')
  have sub: "\<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" using SubtyUnionLeft(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI)
    assume "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')"
    with SubtyUnionLeft(2) have comp: "composable \<Sigma> \<sigma> \<tau>" by simp
    show "composable \<Sigma> \<sigma> (TyUnion \<tau> \<tau>')"
    proof (rule composableI)
      fix \<tau>''
      assume "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<tau>''"
      then show "\<Sigma> \<turnstile> \<sigma> <: \<tau>''" by (rule subty_subtype_cases) (auto simp: sub intro: composable_upper[OF comp])
    next
      fix \<sigma>'
      assume "\<Sigma> \<turnstile> \<sigma>' <: \<sigma>"
      with comp have "\<Sigma> \<turnstile> \<sigma>' <: \<tau>" by (rule composable_lower)
      then show "\<Sigma> \<turnstile> \<sigma>' <: TyUnion \<tau> \<tau>'" by (rule Subtyping.SubtyUnionLeft)
    qed
  qed
next
  case (SubtyUnionRight \<sigma> \<tau>' \<tau>)
  have sub: "\<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" using SubtyUnionRight(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI)
    assume "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')"
    with SubtyUnionRight(2) have comp: "composable \<Sigma> \<sigma> \<tau>'" by simp
    show "composable \<Sigma> \<sigma> (TyUnion \<tau> \<tau>')"
    proof (rule composableI)
      fix \<tau>''
      assume "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<tau>''"
      then show "\<Sigma> \<turnstile> \<sigma> <: \<tau>''" by (rule subty_subtype_cases) (auto simp: sub intro: composable_upper[OF comp])
    next
      fix \<sigma>'
      assume "\<Sigma> \<turnstile> \<sigma>' <: \<sigma>"
      with comp have "\<Sigma> \<turnstile> \<sigma>' <: \<tau>'" by (rule composable_lower)
      then show "\<Sigma> \<turnstile> \<sigma>' <: TyUnion \<tau> \<tau>'" by (rule Subtyping.SubtyUnionRight)
    qed
  qed
next
  case (SubtyUnion \<tau> \<sigma> \<tau>')
  have sub: "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<sigma>" using SubtyUnion(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI)
    assume "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')" "wf_ty \<Sigma> \<sigma>"
    with SubtyUnion(2,4) have comp: "composable \<Sigma> \<tau> \<sigma>" "composable \<Sigma> \<tau>' \<sigma>" by simp_all
    show "composable \<Sigma> (TyUnion \<tau> \<tau>') \<sigma>"
    proof (rule composableI)
      fix \<tau>''
      assume "\<Sigma> \<turnstile> \<sigma> <: \<tau>''"
      with comp have "\<Sigma> \<turnstile> \<tau> <: \<tau>''" "\<Sigma> \<turnstile> \<tau>' <: \<tau>''" by (blast intro: composable_upper)+
      then show "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<tau>''" by (rule Subtyping.SubtyUnion)
    next
      fix \<sigma>'
      assume "\<Sigma> \<turnstile> \<sigma>' <: TyUnion \<tau> \<tau>'"
      then show "\<Sigma> \<turnstile> \<sigma>' <: \<sigma>"
        by (rule subty_supertype_cases)
           (auto simp: sub intro: composable_lower[OF comp(1)] composable_lower[OF comp(2)])
    qed
  qed
qed simp_all

theorem subty_trans:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> ; \<Sigma> \<turnstile> \<sigma> <: \<tau> ; \<Sigma> \<turnstile> \<tau> <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  by (blast dest: subty_composable(1) composable_upper)

(* Preservation of subtyping by substitution *)
lemma subst_subty:
  assumes wf: "wf_class_table \<Sigma>"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> wf_ty \<Sigma> \<sigma> \<longrightarrow> wf_ty \<Sigma> \<tau> \<longrightarrow> \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: subst \<tau>s \<alpha>s \<tau>"
    and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s' \<Longrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>) \<longrightarrow> (\<forall>\<tau> \<in> set \<tau>s'. wf_ty \<Sigma> \<tau>)
           \<longrightarrow> \<Sigma> \<turnstile> map (subst \<tau>s \<alpha>s) \<sigma>s [<:] map (subst \<tau>s \<alpha>s) \<tau>s'"
proof (induction rule: subty_subtys.inducts)
  case (SubtyClassExtend C D \<sigma>s \<tau>s' \<tau>)
  show ?case
  proof (intro impI)
    assume wf_C: "wf_ty \<Sigma> (TyClass C \<tau>s')" and "wf_ty \<Sigma> \<tau>"
    with SubtyClassExtend(3) wf_class_table_base[OF wf wf_C SubtyClassExtend(1)]
    have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyClass D (map (subst \<tau>s' (type_params \<Sigma> C)) \<sigma>s)) <: subst \<tau>s \<alpha>s \<tau>" by blast
    then show "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyClass C \<tau>s') <: subst \<tau>s \<alpha>s \<tau>"
      unfolding base_subst[OF wf wf_C SubtyClassExtend(1), symmetric]
      using SubtyClassExtend(1) by (simp add: Subtyping.SubtyClassExtend)
  qed
next
  case (SubtySized \<tau>)
  then have "\<nexists>\<alpha>. \<tau> = TyVar \<alpha>" by auto
  with SubtySized show ?case by (simp add: sized_subst Subtyping.SubtySized)
next
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) (auto intro: Subtyping.SubtyLiteral)
qed (auto intro: subty_subtys.intros)

(* Types built by union from the primitive type p and the primitive and literal types below it; for p neither
   object nor Sized, the subtypes of p *)
fun prim_subtype :: "prim_ty \<Rightarrow> ty \<Rightarrow> bool"
where
"prim_subtype p (TyPrim q) = (q = p \<or> q = Never \<or> q = int \<and> p = float)" |
"prim_subtype p (TyLiteral l) = (base_type_lit l = TyPrim p \<or> base_type_lit l = TyPrim int \<and> p = float)" |
"prim_subtype p (TyUnion \<sigma> \<tau>) = (prim_subtype p \<sigma> \<and> prim_subtype p \<tau>)" |
"prim_subtype p _ = False"

lemma prim_subtype_subty:
  assumes "p \<notin> {object, Sized}"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> prim_subtype p \<tau> \<Longrightarrow> prim_subtype p \<sigma>"
    and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> True"
proof (induction rule: subty_subtys.inducts)
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) auto
qed (use assms in \<open>auto elim: sized.elims\<close>)

(* Subtyping by a primitive type other than object and Sized, as primitive subtyping *)
lemma subty_prim_iff:
  assumes "p \<notin> {object, Sized}"
  shows "\<Sigma> \<turnstile> \<sigma> <: TyPrim p \<longleftrightarrow> prim_subtype p \<sigma>"
proof
  assume "\<Sigma> \<turnstile> \<sigma> <: TyPrim p"
  from prim_subtype_subty(1)[OF assms this] show "prim_subtype p \<sigma>" by simp
next
  show "prim_subtype p \<sigma> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyPrim p"
  proof (induction \<sigma>)
    case (TyPrim q)
    then show ?case by (auto intro: SubtyRefl SubtyNever SubtyIntFloat)
  next
    case (TyLiteral l)
    then show ?case by (auto intro!: SubtyLiteral intro: SubtyRefl SubtyIntFloat)
  next
    case (TyUnion \<sigma> \<tau>)
    then show ?case by (auto intro: SubtyUnion)
  qed simp_all
qed

end
