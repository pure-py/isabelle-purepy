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

(* Substitution of equivalent types for the same variables *)
lemma subst_equiv:
  "list_all2 (\<lambda>\<sigma> \<tau>. \<Sigma> \<turnstile> \<sigma> \<approx> \<tau>) \<sigma>s \<tau>s \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> \<approx> subst \<tau>s \<alpha>s \<upsilon>"
proof (induction \<upsilon>)
  case (TyVar \<alpha>)
  show ?case
  proof (cases "map_of (zip \<alpha>s \<sigma>s) \<alpha>")
    case None
    with TyVar show ?thesis by (simp add: SubtyRefl map_of_zip_list_all2_None)
  next
    case (Some \<sigma>)
    with TyVar show ?thesis by (auto dest!: map_of_zip_list_all2)
  qed
next
  case (TyTuple \<upsilon>s)
  then show ?case
    by (auto intro!: SubtyTuple list.rel_refl_strong simp: subtys_list_all2 list_all2_map1 list_all2_map2)
next
  case (TyCallable \<upsilon>s \<upsilon>)
  then show ?case
    by (auto intro!: SubtyCallable list.rel_refl_strong simp: subtys_list_all2 list_all2_map1 list_all2_map2)
next
  case (TyClass C \<upsilon>s)
  then show ?case
    by (auto intro!: SubtyClass list.rel_refl_strong simp: subtys_list_all2 list_all2_map1 list_all2_map2)
qed (auto intro: subty_subtys.intros)

(* Subtyping of \<sigma> by \<tau> which composes with subtyping on either side *)
definition composable :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool"
where
"composable \<Sigma> \<sigma> \<tau> = ((\<forall>\<tau>'. \<Sigma> \<turnstile> \<tau> <: \<tau>' \<longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>') \<and> (\<forall>\<rho>. \<Sigma> \<turnstile> \<rho> <: \<sigma> \<longrightarrow> \<Sigma> \<turnstile> \<rho> <: \<tau>))"

lemma composable_subty: "composable \<Sigma> \<sigma> \<tau> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>"
  unfolding composable_def by (blast intro: SubtyRefl)

lemma composable_equiv:
  "\<lbrakk> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s ; list_all2 (composable \<Sigma>) \<tau>s \<sigma>s \<rbrakk>
  \<Longrightarrow> list_all2 (\<lambda>\<sigma> \<tau>. \<Sigma> \<turnstile> \<sigma> \<approx> \<tau>) \<sigma>s \<tau>s"
  by (auto simp: list_all2_conv_all_nth composable_subty)

(* Substitution for a variable, by composable lists of types: either both leave the variable, or they
   substitute composable types *)
lemma subst_var_composable:
  assumes "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" and "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
  shows "(subst \<sigma>s \<alpha>s (TyVar \<beta>) = TyVar \<beta> \<and> subst \<tau>s \<alpha>s (TyVar \<beta>) = TyVar \<beta>)
     \<or> composable \<Sigma> (subst \<sigma>s \<alpha>s (TyVar \<beta>)) (subst \<tau>s \<alpha>s (TyVar \<beta>))
       \<and> composable \<Sigma> (subst \<tau>s \<alpha>s (TyVar \<beta>)) (subst \<sigma>s \<alpha>s (TyVar \<beta>))"
proof (cases "map_of (zip \<alpha>s \<sigma>s) \<beta>")
  case None
  then show ?thesis using assms by (simp add: map_of_zip_list_all2_None)
next
  case (Some \<sigma>)
  with assms obtain \<tau> where "map_of (zip \<alpha>s \<tau>s) \<beta> = Some \<tau>" and "composable \<Sigma> \<sigma> \<tau>"
    by (blast dest: map_of_zip_list_all2)
  moreover with Some assms(2) have "composable \<Sigma> \<tau> \<sigma>" by (auto dest: map_of_zip_list_all2)
  ultimately show ?thesis using Some by simp
qed

lemma composable_var_L:
  "\<lbrakk> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s ; list_all2 (composable \<Sigma>) \<tau>s \<sigma>s ; X = subst \<tau>s \<alpha>s (TyVar \<beta>) ; \<Sigma> \<turnstile> X <: Y \<rbrakk>
  \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s (TyVar \<beta>) <: Y"
  using subst_var_composable[of \<Sigma> \<sigma>s \<tau>s \<alpha>s \<beta>] unfolding composable_def by auto

lemma composable_var_R:
  "\<lbrakk> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s ; list_all2 (composable \<Sigma>) \<tau>s \<sigma>s ; Y = subst \<sigma>s \<alpha>s (TyVar \<beta>) ; \<Sigma> \<turnstile> X <: Y \<rbrakk>
  \<Longrightarrow> \<Sigma> \<turnstile> X <: subst \<tau>s \<alpha>s (TyVar \<beta>)"
  using subst_var_composable[of \<Sigma> \<sigma>s \<tau>s \<alpha>s \<beta>] unfolding composable_def by auto

(* Substitution of composable types for the same variables, on either side of a subtyping *)
lemma subst_composable:
  assumes wf: "wf_class_table \<Sigma>"
  shows
    "\<Sigma> \<turnstile> X <: Y \<Longrightarrow>
     \<forall>\<sigma>s \<tau>s. list_all2 (composable \<Sigma>) \<sigma>s \<tau>s \<longrightarrow> list_all2 (composable \<Sigma>) \<tau>s \<sigma>s
       \<longrightarrow> (\<forall>\<upsilon>. wf_ty \<Sigma> \<upsilon> \<longrightarrow> X = subst \<tau>s \<alpha>s \<upsilon> \<longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: Y)
        \<and> (\<forall>\<upsilon>. wf_ty \<Sigma> \<upsilon> \<longrightarrow> Y = subst \<sigma>s \<alpha>s \<upsilon> \<longrightarrow> \<Sigma> \<turnstile> X <: subst \<tau>s \<alpha>s \<upsilon>)"
  and
    "\<Sigma> \<turnstile> Xs [<:] Ys \<Longrightarrow>
     \<forall>\<sigma>s \<tau>s. list_all2 (composable \<Sigma>) \<sigma>s \<tau>s \<longrightarrow> list_all2 (composable \<Sigma>) \<tau>s \<sigma>s
       \<longrightarrow> (\<forall>\<upsilon>s. (\<forall>\<upsilon> \<in> set \<upsilon>s. wf_ty \<Sigma> \<upsilon>) \<longrightarrow> Xs = map (subst \<tau>s \<alpha>s) \<upsilon>s
             \<longrightarrow> \<Sigma> \<turnstile> map (subst \<sigma>s \<alpha>s) \<upsilon>s [<:] Ys)
        \<and> (\<forall>\<upsilon>s. (\<forall>\<upsilon> \<in> set \<upsilon>s. wf_ty \<Sigma> \<upsilon>) \<longrightarrow> Ys = map (subst \<sigma>s \<alpha>s) \<upsilon>s
             \<longrightarrow> \<Sigma> \<turnstile> Xs [<:] map (subst \<tau>s \<alpha>s) \<upsilon>s)"
proof (induction rule: subty_subtys.inducts)
  case (SubtyRefl \<tau>)
  show ?case by (blast dest: composable_equiv subst_equiv[THEN conjunct1])
next
  case (SubtyClassExtend C D \<omega>s \<tau>s' \<tau>')
  let ?ps = "type_params \<Sigma> C"
  have XY: "\<Sigma> \<turnstile> TyClass C \<tau>s' <: \<tau>'" using SubtyClassExtend(1,2) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf\<upsilon>: "wf_ty \<Sigma> \<upsilon>" and eq: "TyClass C \<tau>s' = subst \<tau>s \<alpha>s \<upsilon>"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: \<tau>'"
    proof (cases \<upsilon>)
      case (TyVar \<beta>)
      with H eq XY show ?thesis by (blast intro: composable_var_L)
    next
      case (TyClass C' \<upsilon>s)
      with eq have [simp]: "C' = C" and \<tau>s': "\<tau>s' = map (subst \<tau>s \<alpha>s) \<upsilon>s" by simp_all
      let ?\<upsilon> = "TyClass D (map (subst \<upsilon>s ?ps) \<omega>s)"
      have wfC: "wf_ty \<Sigma> (TyClass C \<upsilon>s)" using wf\<upsilon> by (simp add: TyClass)
      have wf\<upsilon>': "wf_ty \<Sigma> ?\<upsilon>" using wf_class_table_base[OF wf wfC SubtyClassExtend(1)] .
      have eq1: "TyClass D (map (subst \<tau>s' ?ps) \<omega>s) = subst \<tau>s \<alpha>s ?\<upsilon>"
        unfolding \<tau>s' by (rule base_subst[OF wf wfC SubtyClassExtend(1)])
      have eq2: "subst \<sigma>s \<alpha>s ?\<upsilon> = TyClass D (map (subst (map (subst \<sigma>s \<alpha>s) \<upsilon>s) ?ps) \<omega>s)"
        by (rule base_subst[OF wf wfC SubtyClassExtend(1), symmetric])
      from SubtyClassExtend(3) H wf\<upsilon>' eq1 have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s ?\<upsilon> <: \<tau>'" by blast
      then have "\<Sigma> \<turnstile> TyClass D (map (subst (map (subst \<sigma>s \<alpha>s) \<upsilon>s) ?ps) \<omega>s) <: \<tau>'" unfolding eq2 .
      then show ?thesis
        using SubtyClassExtend(1) by (simp add: TyClass) (blast intro: Subtyping.SubtyClassExtend)
    qed (use eq in simp_all)
  next
    fix \<sigma>s \<tau>s \<upsilon>
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<upsilon>"
      and "\<tau>' = subst \<sigma>s \<alpha>s \<upsilon>"
    with SubtyClassExtend(3) have "\<Sigma> \<turnstile> TyClass D (map (subst \<tau>s' ?ps) \<omega>s) <: subst \<tau>s \<alpha>s \<upsilon>" by blast
    then show "\<Sigma> \<turnstile> TyClass C \<tau>s' <: subst \<tau>s \<alpha>s \<upsilon>"
      using SubtyClassExtend(1) by (blast intro: Subtyping.SubtyClassExtend)
  qed
next
  case (SubtyClass \<rho>s \<rho>s' C)
  have XY: "\<Sigma> \<turnstile> TyClass C \<rho>s <: TyClass C \<rho>s'" using SubtyClass(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf\<upsilon>: "wf_ty \<Sigma> \<upsilon>" and eq: "TyClass C \<rho>s = subst \<tau>s \<alpha>s \<upsilon>"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: TyClass C \<rho>s'"
    proof (cases \<upsilon>)
      case (TyVar \<beta>)
      with H eq XY show ?thesis by (blast intro: composable_var_L)
    next
      case (TyClass C' \<upsilon>s)
      with eq wf\<upsilon> have "C' = C" "\<rho>s = map (subst \<tau>s \<alpha>s) \<upsilon>s" "\<forall>\<upsilon> \<in> set \<upsilon>s. wf_ty \<Sigma> \<upsilon>" by simp_all
      with SubtyClass(2,4) H show ?thesis by (auto simp: TyClass intro!: subty_subtys.intros)
    qed (use eq in simp_all)
  next
    fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf\<upsilon>: "wf_ty \<Sigma> \<upsilon>" and eq: "TyClass C \<rho>s' = subst \<sigma>s \<alpha>s \<upsilon>"
    show "\<Sigma> \<turnstile> TyClass C \<rho>s <: subst \<tau>s \<alpha>s \<upsilon>"
    proof (cases \<upsilon>)
      case (TyVar \<beta>)
      with H eq XY show ?thesis by (blast intro: composable_var_R)
    next
      case (TyClass C' \<upsilon>s)
      with eq wf\<upsilon> have "C' = C" "\<rho>s' = map (subst \<sigma>s \<alpha>s) \<upsilon>s" "\<forall>\<upsilon> \<in> set \<upsilon>s. wf_ty \<Sigma> \<upsilon>" by simp_all
      with SubtyClass(2,4) H show ?thesis by (auto simp: TyClass intro!: subty_subtys.intros)
    qed (use eq in simp_all)
  qed
next
  case (SubtyNever \<tau>)
  have XY: "\<Sigma> \<turnstile> TyPrim Never <: \<tau>" by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<upsilon>
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "TyPrim Never = subst \<tau>s \<alpha>s \<upsilon>"
    then have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: \<tau>" using XY
      by (cases \<upsilon>) (auto simp del: subst.simps(1) intro: composable_var_L subty_subtys.intros) }
  then show ?case by (blast intro: subty_subtys.intros)
next
  case (SubtyObject \<tau>)
  have XY: "\<Sigma> \<turnstile> \<tau> <: TyPrim object" by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<upsilon>
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      "TyPrim object = subst \<sigma>s \<alpha>s \<upsilon>"
    then have "\<Sigma> \<turnstile> \<tau> <: subst \<tau>s \<alpha>s \<upsilon>" using XY
      by (cases \<upsilon>) (auto simp del: subst.simps(1) intro: composable_var_R subty_subtys.intros) }
  then show ?case by (blast intro: subty_subtys.intros)
next
  case SubtyIntFloat
  have XY: "\<Sigma> \<turnstile> TyPrim int <: TyPrim float" by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<upsilon>
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
    then have "TyPrim int = subst \<tau>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: TyPrim float"
      and "TyPrim float = subst \<sigma>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> TyPrim int <: subst \<tau>s \<alpha>s \<upsilon>" using XY
      by (cases \<upsilon>;
          auto simp del: subst.simps(1) intro: composable_var_L composable_var_R subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtySized \<tau>)
  have XY: "\<Sigma> \<turnstile> \<tau> <: TyPrim Sized" using SubtySized(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" and eq: "\<tau> = subst \<tau>s \<alpha>s \<upsilon>"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: TyPrim Sized"
    proof (cases "\<exists>\<beta>. \<upsilon> = TyVar \<beta>")
      case True
      with H eq XY show ?thesis by (blast intro: composable_var_L)
    next
      case False
      with SubtySized(1) eq have "sized (subst \<sigma>s \<alpha>s \<upsilon>)" by (simp add: sized_subst_iff)
      then show ?thesis by (rule subty_subtys.intros)
    qed
  next
    fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and eq: "TyPrim Sized = subst \<sigma>s \<alpha>s \<upsilon>"
    show "\<Sigma> \<turnstile> \<tau> <: subst \<tau>s \<alpha>s \<upsilon>"
    proof (cases \<upsilon>)
      case (TyVar \<beta>)
      with H eq XY show ?thesis by (blast intro: composable_var_R)
    qed (use eq SubtySized(1) in \<open>auto intro: subty_subtys.intros\<close>)
  qed
next
  case (SubtyList \<rho>0 \<rho>0')
  have XY: "\<Sigma> \<turnstile> TyList \<rho>0 <: TyList \<rho>0'" using SubtyList(1,3) by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" and "wf_ty \<Sigma> \<upsilon>"
    then have "TyList \<rho>0 = subst \<tau>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: TyList \<rho>0'"
      and "TyList \<rho>0' = subst \<sigma>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> TyList \<rho>0 <: subst \<tau>s \<alpha>s \<upsilon>" using XY SubtyList(2,4)
      by (cases \<upsilon>;
          auto simp del: subst.simps(1) intro: composable_var_L composable_var_R subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyDict \<rho>0 \<rho>0')
  have XY: "\<Sigma> \<turnstile> TyDict \<rho>0 <: TyDict \<rho>0'" using SubtyDict(1,3) by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" and "wf_ty \<Sigma> \<upsilon>"
    then have "TyDict \<rho>0 = subst \<tau>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: TyDict \<rho>0'"
      and "TyDict \<rho>0' = subst \<sigma>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> TyDict \<rho>0 <: subst \<tau>s \<alpha>s \<upsilon>" using XY SubtyDict(2,4)
      by (cases \<upsilon>;
          auto simp del: subst.simps(1) intro: composable_var_L composable_var_R subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyCallable \<rho>s' \<rho>s \<rho>0 \<rho>0')
  have XY: "\<Sigma> \<turnstile> TyCallable \<rho>s \<rho>0 <: TyCallable \<rho>s' \<rho>0'" using SubtyCallable(1,3) by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" and "wf_ty \<Sigma> \<upsilon>"
    then have "TyCallable \<rho>s \<rho>0 = subst \<tau>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: TyCallable \<rho>s' \<rho>0'"
      and "TyCallable \<rho>s' \<rho>0' = subst \<sigma>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> TyCallable \<rho>s \<rho>0 <: subst \<tau>s \<alpha>s \<upsilon>"
      using XY SubtyCallable(2,4)
      by (cases \<upsilon>;
          auto simp del: subst.simps(1) intro: composable_var_L composable_var_R subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyTuple \<rho>s \<rho>s')
  have XY: "\<Sigma> \<turnstile> TyTuple \<rho>s <: TyTuple \<rho>s'" using SubtyTuple(1) by (rule subty_subtys.intros)
  { fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" and "wf_ty \<Sigma> \<upsilon>"
    then have "TyTuple \<rho>s = subst \<tau>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: TyTuple \<rho>s'"
      and "TyTuple \<rho>s' = subst \<sigma>s \<alpha>s \<upsilon> \<Longrightarrow> \<Sigma> \<turnstile> TyTuple \<rho>s <: subst \<tau>s \<alpha>s \<upsilon>" using XY SubtyTuple(2)
      by (cases \<upsilon>;
          auto simp del: subst.simps(1) intro: composable_var_L composable_var_R subty_subtys.intros)+ }
  then show ?case by blast
next
  case (SubtyLiteral l \<tau>)
  have XY: "\<Sigma> \<turnstile> TyLiteral l <: \<tau>" using SubtyLiteral(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and eq: "TyLiteral l = subst \<tau>s \<alpha>s \<upsilon>"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: \<tau>"
    proof (cases \<upsilon>)
      case (TyVar \<beta>)
      with H eq XY show ?thesis by (blast intro: composable_var_L)
    qed (use eq XY in simp_all)
  next
    fix \<sigma>s \<tau>s \<upsilon>
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<upsilon>"
      and "\<tau> = subst \<sigma>s \<alpha>s \<upsilon>"
    with SubtyLiteral(2) have "\<Sigma> \<turnstile> base_type_lit l <: subst \<tau>s \<alpha>s \<upsilon>" by blast
    then show "\<Sigma> \<turnstile> TyLiteral l <: subst \<tau>s \<alpha>s \<upsilon>" by (rule Subtyping.SubtyLiteral)
  qed
next
  case (SubtyUnionLeft \<sigma> \<tau> \<tau>')
  have XY: "\<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" using SubtyUnionLeft(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<upsilon>
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<upsilon>"
      and "\<sigma> = subst \<tau>s \<alpha>s \<upsilon>"
    with SubtyUnionLeft(2) have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: \<tau>" by blast
    then show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: TyUnion \<tau> \<tau>'" by (rule Subtyping.SubtyUnionLeft)
  next
    fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf\<upsilon>: "wf_ty \<Sigma> \<upsilon>" and eq: "TyUnion \<tau> \<tau>' = subst \<sigma>s \<alpha>s \<upsilon>"
    show "\<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s \<upsilon>"
    proof (cases \<upsilon>)
      case (TyVar \<beta>)
      with H eq XY show ?thesis by (blast intro: composable_var_R)
    next
      case (TyUnion \<upsilon>1 \<upsilon>2)
      with eq wf\<upsilon> have "\<tau> = subst \<sigma>s \<alpha>s \<upsilon>1" "wf_ty \<Sigma> \<upsilon>1" by simp_all
      with SubtyUnionLeft(2) H have "\<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s \<upsilon>1" by blast
      then show ?thesis by (simp add: TyUnion Subtyping.SubtyUnionLeft)
    qed (use eq in simp_all)
  qed
next
  case (SubtyUnionRight \<sigma> \<tau>' \<tau>)
  have XY: "\<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" using SubtyUnionRight(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<upsilon>
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<upsilon>"
      and "\<sigma> = subst \<tau>s \<alpha>s \<upsilon>"
    with SubtyUnionRight(2) have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: \<tau>'" by blast
    then show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: TyUnion \<tau> \<tau>'" by (rule Subtyping.SubtyUnionRight)
  next
    fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf\<upsilon>: "wf_ty \<Sigma> \<upsilon>" and eq: "TyUnion \<tau> \<tau>' = subst \<sigma>s \<alpha>s \<upsilon>"
    show "\<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s \<upsilon>"
    proof (cases \<upsilon>)
      case (TyVar \<beta>)
      with H eq XY show ?thesis by (blast intro: composable_var_R)
    next
      case (TyUnion \<upsilon>1 \<upsilon>2)
      with eq wf\<upsilon> have "\<tau>' = subst \<sigma>s \<alpha>s \<upsilon>2" "wf_ty \<Sigma> \<upsilon>2" by simp_all
      with SubtyUnionRight(2) H have "\<Sigma> \<turnstile> \<sigma> <: subst \<tau>s \<alpha>s \<upsilon>2" by blast
      then show ?thesis by (simp add: TyUnion Subtyping.SubtyUnionRight)
    qed (use eq in simp_all)
  qed
next
  case (SubtyUnion \<tau> \<sigma> \<tau>')
  have XY: "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<sigma>" using SubtyUnion(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<upsilon>
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf\<upsilon>: "wf_ty \<Sigma> \<upsilon>" and eq: "TyUnion \<tau> \<tau>' = subst \<tau>s \<alpha>s \<upsilon>"
    show "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: \<sigma>"
    proof (cases \<upsilon>)
      case (TyVar \<beta>)
      with H eq XY show ?thesis by (blast intro: composable_var_L)
    next
      case (TyUnion \<upsilon>1 \<upsilon>2)
      with eq wf\<upsilon> have "\<tau> = subst \<tau>s \<alpha>s \<upsilon>1" "\<tau>' = subst \<tau>s \<alpha>s \<upsilon>2" "wf_ty \<Sigma> \<upsilon>1" "wf_ty \<Sigma> \<upsilon>2"
        by simp_all
      with SubtyUnion(2,4) H have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon>1 <: \<sigma>" "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon>2 <: \<sigma>" by blast+
      then show ?thesis by (simp add: TyUnion Subtyping.SubtyUnion)
    qed (use eq in simp_all)
  next
    fix \<sigma>s \<tau>s \<upsilon>
    assume "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "wf_ty \<Sigma> \<upsilon>"
      and "\<sigma> = subst \<sigma>s \<alpha>s \<upsilon>"
    with SubtyUnion(2,4) have "\<Sigma> \<turnstile> \<tau> <: subst \<tau>s \<alpha>s \<upsilon>" "\<Sigma> \<turnstile> \<tau>' <: subst \<tau>s \<alpha>s \<upsilon>" by blast+
    then show "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: subst \<tau>s \<alpha>s \<upsilon>" by (rule Subtyping.SubtyUnion)
  qed
next
  case SubtysNil
  show ?case by (auto intro: subty_subtys.intros)
next
  case (SubtysCons \<rho> \<rho>' \<rho>s \<rho>s')
  show ?case
  proof (intro allI impI conjI)
    fix \<sigma>s \<tau>s \<upsilon>s
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf: "\<forall>\<upsilon> \<in> set \<upsilon>s. wf_ty \<Sigma> \<upsilon>" and eq: "\<rho> # \<rho>s = map (subst \<tau>s \<alpha>s) \<upsilon>s"
    from eq obtain \<upsilon> \<upsilon>s' where \<upsilon>s: "\<upsilon>s = \<upsilon> # \<upsilon>s'" and "\<rho> = subst \<tau>s \<alpha>s \<upsilon>" "\<rho>s = map (subst \<tau>s \<alpha>s) \<upsilon>s'"
      by (cases \<upsilon>s) auto
    moreover have "wf_ty \<Sigma> \<upsilon>" "\<forall>\<upsilon> \<in> set \<upsilon>s'. wf_ty \<Sigma> \<upsilon>" using wf by (simp_all add: \<upsilon>s)
    ultimately have "\<Sigma> \<turnstile> subst \<sigma>s \<alpha>s \<upsilon> <: \<rho>'" "\<Sigma> \<turnstile> map (subst \<sigma>s \<alpha>s) \<upsilon>s' [<:] \<rho>s'"
      using SubtysCons(2,4) H by blast+
    then show "\<Sigma> \<turnstile> map (subst \<sigma>s \<alpha>s) \<upsilon>s [<:] \<rho>' # \<rho>s'" by (simp add: \<upsilon>s Subtyping.SubtysCons)
  next
    fix \<sigma>s \<tau>s \<upsilon>s
    assume H: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s"
      and wf: "\<forall>\<upsilon> \<in> set \<upsilon>s. wf_ty \<Sigma> \<upsilon>" and eq: "\<rho>' # \<rho>s' = map (subst \<sigma>s \<alpha>s) \<upsilon>s"
    from eq obtain \<upsilon> \<upsilon>s' where \<upsilon>s: "\<upsilon>s = \<upsilon> # \<upsilon>s'" and "\<rho>' = subst \<sigma>s \<alpha>s \<upsilon>" "\<rho>s' = map (subst \<sigma>s \<alpha>s) \<upsilon>s'"
      by (cases \<upsilon>s) auto
    moreover have "wf_ty \<Sigma> \<upsilon>" "\<forall>\<upsilon> \<in> set \<upsilon>s'. wf_ty \<Sigma> \<upsilon>" using wf by (simp_all add: \<upsilon>s)
    ultimately have "\<Sigma> \<turnstile> \<rho> <: subst \<tau>s \<alpha>s \<upsilon>" "\<Sigma> \<turnstile> \<rho>s [<:] map (subst \<tau>s \<alpha>s) \<upsilon>s'"
      using SubtysCons(2,4) H by blast+
    then show "\<Sigma> \<turnstile> \<rho> # \<rho>s [<:] map (subst \<tau>s \<alpha>s) \<upsilon>s" by (simp add: \<upsilon>s Subtyping.SubtysCons)
  qed
qed

lemma composableI:
  "\<lbrakk> \<And>\<tau>'. \<Sigma> \<turnstile> \<tau> <: \<tau>' \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>' ; \<And>\<rho>. \<Sigma> \<turnstile> \<rho> <: \<sigma> \<Longrightarrow> \<Sigma> \<turnstile> \<rho> <: \<tau> \<rbrakk> \<Longrightarrow> composable \<Sigma> \<sigma> \<tau>"
  unfolding composable_def by blast

lemma composable_L: "\<lbrakk> composable \<Sigma> \<sigma> \<tau> ; \<Sigma> \<turnstile> \<tau> <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  and composable_R: "\<lbrakk> composable \<Sigma> \<sigma> \<tau> ; \<Sigma> \<turnstile> \<rho> <: \<sigma> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<rho> <: \<tau>"
  unfolding composable_def by blast+

lemma composables_L: "\<lbrakk> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s ; \<Sigma> \<turnstile> \<tau>s [<:] \<tau>s' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s'"
  and composables_R: "\<lbrakk> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s ; \<Sigma> \<turnstile> \<rho>s [<:] \<sigma>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<rho>s [<:] \<tau>s"
  unfolding subtys_list_all2 by (blast intro: list_all2_trans composable_L composable_R)+

lemma subtys_Nil: "\<Sigma> \<turnstile> \<rho>s [<:] [] \<Longrightarrow> \<rho>s = []"
  by (simp add: subtys_list_all2)

(* Subtyping of \<rho> by \<tau>, from subtyping of \<rho> by \<sigma>, by the last rule of the derivation: a rule whose conclusion
   fixes the form of \<sigma> is a hypothesis, and the others carry over *)
lemma subty_left_cases:
  assumes "\<Sigma> \<turnstile> \<rho> <: \<sigma>"
    and refl: "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    and class_args: "\<And>C \<rho>s \<sigma>s. \<lbrakk> \<sigma> = TyClass C \<sigma>s ; \<Sigma> \<turnstile> \<rho>s [<:] \<sigma>s ; \<Sigma> \<turnstile> \<sigma>s [<:] \<rho>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyClass C \<rho>s <: \<tau>"
    and object: "\<And>\<rho>. \<sigma> = TyPrim object \<Longrightarrow> \<Sigma> \<turnstile> \<rho> <: \<tau>"
    and int_float: "\<sigma> = TyPrim float \<Longrightarrow> \<Sigma> \<turnstile> TyPrim int <: \<tau>"
    and sized: "\<And>\<rho>. \<lbrakk> \<sigma> = TyPrim Sized ; sized \<rho> \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<rho> <: \<tau>"
    and list: "\<And>\<rho>' \<sigma>'. \<lbrakk> \<sigma> = TyList \<sigma>' ; \<Sigma> \<turnstile> \<rho>' <: \<sigma>' ; \<Sigma> \<turnstile> \<sigma>' <: \<rho>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyList \<rho>' <: \<tau>"
    and dict: "\<And>\<rho>' \<sigma>'. \<lbrakk> \<sigma> = TyDict \<sigma>' ; \<Sigma> \<turnstile> \<rho>' <: \<sigma>' ; \<Sigma> \<turnstile> \<sigma>' <: \<rho>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyDict \<rho>' <: \<tau>"
    and callable:
      "\<And>\<rho>s \<rho>' \<sigma>s \<sigma>'. \<lbrakk> \<sigma> = TyCallable \<sigma>s \<sigma>' ; \<Sigma> \<turnstile> \<sigma>s [<:] \<rho>s ; \<Sigma> \<turnstile> \<rho>' <: \<sigma>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyCallable \<rho>s \<rho>' <: \<tau>"
    and tuple: "\<And>\<rho>s \<sigma>s. \<lbrakk> \<sigma> = TyTuple \<sigma>s ; \<Sigma> \<turnstile> \<rho>s [<:] \<sigma>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> TyTuple \<rho>s <: \<tau>"
    and union_left: "\<And>\<rho> \<sigma>' \<sigma>''. \<lbrakk> \<sigma> = TyUnion \<sigma>' \<sigma>'' ; \<Sigma> \<turnstile> \<rho> <: \<sigma>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<rho> <: \<tau>"
    and union_right: "\<And>\<rho> \<sigma>' \<sigma>''. \<lbrakk> \<sigma> = TyUnion \<sigma>' \<sigma>'' ; \<Sigma> \<turnstile> \<rho> <: \<sigma>'' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<rho> <: \<tau>"
  shows "\<Sigma> \<turnstile> \<rho> <: \<tau>"
proof -
  have "\<Sigma> \<turnstile> X <: Y \<Longrightarrow> Y = \<sigma> \<longrightarrow> \<Sigma> \<turnstile> X <: \<tau>" and "\<Sigma> \<turnstile> Xs [<:] Ys \<Longrightarrow> True" for X Y Xs Ys
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

(* Subtyping of \<sigma> by \<tau>', from subtyping of \<tau> by \<tau>', by the last rule of the derivation: a rule whose conclusion
   fixes the form of \<tau> is a hypothesis, and the others carry over *)
lemma subty_right_cases:
  assumes "\<Sigma> \<turnstile> \<tau> <: \<tau>'"
    and refl: "\<Sigma> \<turnstile> \<sigma> <: \<tau>"
    and class_extend:
      "\<And>C \<tau>s D \<omega>s Y. \<lbrakk> \<tau> = TyClass C \<tau>s ; base \<Sigma> C = Some (D, \<omega>s)
                  ; \<Sigma> \<turnstile> TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<omega>s) <: Y \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: Y"
    and class_args:
      "\<And>C \<tau>s \<tau>s'. \<lbrakk> \<tau> = TyClass C \<tau>s ; \<Sigma> \<turnstile> \<tau>s [<:] \<tau>s' ; \<Sigma> \<turnstile> \<tau>s' [<:] \<tau>s \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyClass C \<tau>s'"
    and never: "\<And>Y. \<tau> = TyPrim Never \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: Y"
    and int_float: "\<tau> = TyPrim int \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyPrim float"
    and sized: "sized \<tau> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyPrim Sized"
    and list: "\<And>\<tau>0 \<tau>0'. \<lbrakk> \<tau> = TyList \<tau>0 ; \<Sigma> \<turnstile> \<tau>0 <: \<tau>0' ; \<Sigma> \<turnstile> \<tau>0' <: \<tau>0 \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyList \<tau>0'"
    and dict: "\<And>\<tau>0 \<tau>0'. \<lbrakk> \<tau> = TyDict \<tau>0 ; \<Sigma> \<turnstile> \<tau>0 <: \<tau>0' ; \<Sigma> \<turnstile> \<tau>0' <: \<tau>0 \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyDict \<tau>0'"
    and callable:
      "\<And>\<tau>s \<tau>0 \<tau>s' \<tau>0'. \<lbrakk> \<tau> = TyCallable \<tau>s \<tau>0 ; \<Sigma> \<turnstile> \<tau>s' [<:] \<tau>s ; \<Sigma> \<turnstile> \<tau>0 <: \<tau>0' \<rbrakk>
                    \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyCallable \<tau>s' \<tau>0'"
    and tuple: "\<And>\<tau>s \<tau>s'. \<lbrakk> \<tau> = TyTuple \<tau>s ; \<Sigma> \<turnstile> \<tau>s [<:] \<tau>s' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: TyTuple \<tau>s'"
    and literal: "\<And>l Y. \<lbrakk> \<tau> = TyLiteral l ; \<Sigma> \<turnstile> base_type_lit l <: Y \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: Y"
    and union: "\<And>\<tau>1 \<tau>2 Y. \<lbrakk> \<tau> = TyUnion \<tau>1 \<tau>2 ; \<Sigma> \<turnstile> \<tau>1 <: Y ; \<Sigma> \<turnstile> \<tau>2 <: Y \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: Y"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau>'"
proof -
  have "\<Sigma> \<turnstile> X <: Y \<Longrightarrow> X = \<tau> \<longrightarrow> \<Sigma> \<turnstile> \<sigma> <: Y" and "\<Sigma> \<turnstile> Xs [<:] Ys \<Longrightarrow> True" for X Y Xs Ys
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
    and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s \<Longrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>) \<longrightarrow> (\<forall>\<tau> \<in> set \<tau>s. wf_ty \<Sigma> \<tau>) \<longrightarrow> list_all2 (composable \<Sigma>) \<sigma>s \<tau>s"
proof (induction rule: subty_subtys.inducts)
  case (SubtyRefl \<tau>)
  show ?case unfolding composable_def by blast
next
  case (SubtyClassExtend C D \<omega>s \<tau>s \<tau>')
  let ?\<sigma> = "TyClass D (map (subst \<tau>s (type_params \<Sigma> C)) \<omega>s)"
  have XY: "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>'" using SubtyClassExtend(1,2) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume wf\<sigma>: "wf_ty \<Sigma> (TyClass C \<tau>s)" and "wf_ty \<Sigma> \<tau>'"
    with SubtyClassExtend(3) wf_class_table_base[OF wf wf\<sigma> SubtyClassExtend(1)] have c: "composable \<Sigma> ?\<sigma> \<tau>'"
      by blast
    fix \<tau>''
    assume "\<Sigma> \<turnstile> \<tau>' <: \<tau>''"
    with c have "\<Sigma> \<turnstile> ?\<sigma> <: \<tau>''" by (rule composable_L)
    then show "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>''" using SubtyClassExtend(1) by (blast intro: Subtyping.SubtyClassExtend)
  next
    assume wf\<sigma>: "wf_ty \<Sigma> (TyClass C \<tau>s)" and "wf_ty \<Sigma> \<tau>'"
    with SubtyClassExtend(3) wf_class_table_base[OF wf wf\<sigma> SubtyClassExtend(1)] have c: "composable \<Sigma> ?\<sigma> \<tau>'"
      by blast
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyClass C \<tau>s"
    then show "\<Sigma> \<turnstile> \<rho> <: \<tau>'"
    proof (rule subty_left_cases)
      show "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>'" by (rule XY)
      fix C' \<rho>s \<sigma>s
      assume "TyClass C \<tau>s = TyClass C' \<sigma>s" and "\<Sigma> \<turnstile> \<rho>s [<:] \<sigma>s" and "\<Sigma> \<turnstile> \<sigma>s [<:] \<rho>s"
      then have "\<Sigma> \<turnstile> TyClass D (map (subst \<rho>s (type_params \<Sigma> C)) \<omega>s) <: ?\<sigma>"
        using subst_equiv[of \<Sigma> \<rho>s \<tau>s "type_params \<Sigma> C" "TyClass D \<omega>s"]
        by (auto simp: subtys_list_all2 list_all2_conv_all_nth)
      with c have "\<Sigma> \<turnstile> TyClass D (map (subst \<rho>s (type_params \<Sigma> C)) \<omega>s) <: \<tau>'" by (rule composable_R)
      with \<open>TyClass C \<tau>s = TyClass C' \<sigma>s\<close> show "\<Sigma> \<turnstile> TyClass C' \<rho>s <: \<tau>'"
        using SubtyClassExtend(1) by (auto intro: Subtyping.SubtyClassExtend)
    qed simp_all
  qed
next
  case (SubtyClass \<sigma>s \<tau>s C)
  have XY: "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass C \<tau>s" using SubtyClass(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume wf\<sigma>: "wf_ty \<Sigma> (TyClass C \<sigma>s)" and wf\<tau>: "wf_ty \<Sigma> (TyClass C \<tau>s)"
    with SubtyClass(2,4) have c: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" by simp_all
    fix \<tau>'
    assume "\<Sigma> \<turnstile> TyClass C \<tau>s <: \<tau>'"
    then show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: \<tau>'"
    proof (rule subty_right_cases)
      show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass C \<tau>s" by (rule XY)
      fix C' \<tau>s'' D \<omega>s Y
      assume eq: "TyClass C \<tau>s = TyClass C' \<tau>s''" and base: "base \<Sigma> C' = Some (D, \<omega>s)"
        and e: "\<Sigma> \<turnstile> TyClass D (map (subst \<tau>s'' (type_params \<Sigma> C')) \<omega>s) <: Y"
      let ?ps = "type_params \<Sigma> C"
      from eq have [simp]: "C' = C" "\<tau>s'' = \<tau>s" by simp_all
      have base': "base \<Sigma> C = Some (D, \<omega>s)" using base by simp
      have wfD: "wf_ty \<Sigma> (TyClass D \<omega>s)" using wf wf\<tau> base' unfolding wf_class_table_def by auto
      have "TyClass D (map (subst \<tau>s'' (type_params \<Sigma> C')) \<omega>s) = subst \<tau>s ?ps (TyClass D \<omega>s)" by simp
      then have "\<Sigma> \<turnstile> subst \<sigma>s ?ps (TyClass D \<omega>s) <: Y"
        using subst_composable(1)[OF wf e, where \<alpha>s = ?ps] c wfD by blast
      then show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: Y" by (simp add: Subtyping.SubtyClassExtend[OF base'])
    next
      fix C' \<tau>s'' \<tau>s'
      assume "TyClass C \<tau>s = TyClass C' \<tau>s''" and "\<Sigma> \<turnstile> \<tau>s'' [<:] \<tau>s'" and "\<Sigma> \<turnstile> \<tau>s' [<:] \<tau>s''"
      with c show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass C' \<tau>s'"
        by (auto intro: Subtyping.SubtyClass composables_L composables_R)
    next
      assume "sized (TyClass C \<tau>s)"
      with SubtyClass(1) show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyPrim Sized"
        by (auto intro: Subtyping.SubtySized dest: subtys_Nil elim: sized.elims)
    qed simp_all
  next
    assume wf\<sigma>: "wf_ty \<Sigma> (TyClass C \<sigma>s)" and wf\<tau>: "wf_ty \<Sigma> (TyClass C \<tau>s)"
    with SubtyClass(2,4) have c: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" by simp_all
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyClass C \<sigma>s"
    then show "\<Sigma> \<turnstile> \<rho> <: TyClass C \<tau>s"
    proof (rule subty_left_cases)
      show "\<Sigma> \<turnstile> TyClass C \<sigma>s <: TyClass C \<tau>s" by (rule XY)
      fix C' \<rho>s \<sigma>s'
      assume "TyClass C \<sigma>s = TyClass C' \<sigma>s'" and "\<Sigma> \<turnstile> \<rho>s [<:] \<sigma>s'" and "\<Sigma> \<turnstile> \<sigma>s' [<:] \<rho>s"
      with c show "\<Sigma> \<turnstile> TyClass C' \<rho>s <: TyClass C \<tau>s"
        by (auto intro: Subtyping.SubtyClass composables_L composables_R)
    qed simp_all
  qed
next
  case (SubtyNever \<tau>)
  show ?case
  proof (intro impI composableI)
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyPrim Never"
    then show "\<Sigma> \<turnstile> \<rho> <: \<tau>" by (rule subty_left_cases) (simp_all add: Subtyping.SubtyNever)
  qed (rule Subtyping.SubtyNever)
next
  case (SubtyObject \<tau>)
  show ?case
  proof (intro impI composableI)
    fix \<tau>'
    assume "\<Sigma> \<turnstile> TyPrim object <: \<tau>'"
    then show "\<Sigma> \<turnstile> \<tau> <: \<tau>'" by (rule subty_right_cases) (simp_all add: Subtyping.SubtyObject)
  qed (rule Subtyping.SubtyObject)
next
  case SubtyIntFloat
  show ?case
  proof (intro impI composableI)
    fix \<tau>'
    assume "\<Sigma> \<turnstile> TyPrim float <: \<tau>'"
    then show "\<Sigma> \<turnstile> TyPrim int <: \<tau>'" by (rule subty_right_cases) (simp_all add: Subtyping.SubtyIntFloat)
  next
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyPrim int"
    then show "\<Sigma> \<turnstile> \<rho> <: TyPrim float" by (rule subty_left_cases) (simp_all add: Subtyping.SubtyIntFloat)
  qed
next
  case (SubtySized \<tau>)
  have XY: "\<Sigma> \<turnstile> \<tau> <: TyPrim Sized" using SubtySized(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    fix \<tau>'
    assume "\<Sigma> \<turnstile> TyPrim Sized <: \<tau>'"
    then show "\<Sigma> \<turnstile> \<tau> <: \<tau>'" by (rule subty_right_cases) (simp_all add: XY)
  next
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: \<tau>"
    then show "\<Sigma> \<turnstile> \<rho> <: TyPrim Sized"
      by (rule subty_left_cases)
         (insert SubtySized(1) XY, auto intro: Subtyping.SubtySized dest: subtys_Nil elim: sized.elims)
  qed
next
  case (SubtyList \<sigma>0 \<tau>0)
  have XY: "\<Sigma> \<turnstile> TyList \<sigma>0 <: TyList \<tau>0" using SubtyList(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume "wf_ty \<Sigma> (TyList \<sigma>0)" "wf_ty \<Sigma> (TyList \<tau>0)"
    with SubtyList(2,4) have c: "composable \<Sigma> \<sigma>0 \<tau>0" "composable \<Sigma> \<tau>0 \<sigma>0" by simp_all
    fix \<tau>'
    assume "\<Sigma> \<turnstile> TyList \<tau>0 <: \<tau>'"
    then show "\<Sigma> \<turnstile> TyList \<sigma>0 <: \<tau>'"
      by (rule subty_right_cases)
         (auto simp: XY
           intro: Subtyping.SubtySized Subtyping.SubtyList composable_L[OF c(1)] composable_R[OF c(2)])
  next
    assume "wf_ty \<Sigma> (TyList \<sigma>0)" "wf_ty \<Sigma> (TyList \<tau>0)"
    with SubtyList(2,4) have c: "composable \<Sigma> \<sigma>0 \<tau>0" "composable \<Sigma> \<tau>0 \<sigma>0" by simp_all
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyList \<sigma>0"
    then show "\<Sigma> \<turnstile> \<rho> <: TyList \<tau>0"
      by (rule subty_left_cases)
         (auto simp: XY intro: Subtyping.SubtyList composable_R[OF c(1)] composable_L[OF c(2)])
  qed
next
  case (SubtyDict \<sigma>0 \<tau>0)
  have XY: "\<Sigma> \<turnstile> TyDict \<sigma>0 <: TyDict \<tau>0" using SubtyDict(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume "wf_ty \<Sigma> (TyDict \<sigma>0)" "wf_ty \<Sigma> (TyDict \<tau>0)"
    with SubtyDict(2,4) have c: "composable \<Sigma> \<sigma>0 \<tau>0" "composable \<Sigma> \<tau>0 \<sigma>0" by simp_all
    fix \<tau>'
    assume "\<Sigma> \<turnstile> TyDict \<tau>0 <: \<tau>'"
    then show "\<Sigma> \<turnstile> TyDict \<sigma>0 <: \<tau>'"
      by (rule subty_right_cases)
         (auto simp: XY
           intro: Subtyping.SubtySized Subtyping.SubtyDict composable_L[OF c(1)] composable_R[OF c(2)])
  next
    assume "wf_ty \<Sigma> (TyDict \<sigma>0)" "wf_ty \<Sigma> (TyDict \<tau>0)"
    with SubtyDict(2,4) have c: "composable \<Sigma> \<sigma>0 \<tau>0" "composable \<Sigma> \<tau>0 \<sigma>0" by simp_all
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyDict \<sigma>0"
    then show "\<Sigma> \<turnstile> \<rho> <: TyDict \<tau>0"
      by (rule subty_left_cases)
         (auto simp: XY intro: Subtyping.SubtyDict composable_R[OF c(1)] composable_L[OF c(2)])
  qed
next
  case (SubtyCallable \<tau>s \<sigma>s \<sigma>0 \<tau>0)
  have XY: "\<Sigma> \<turnstile> TyCallable \<sigma>s \<sigma>0 <: TyCallable \<tau>s \<tau>0" using SubtyCallable(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume "wf_ty \<Sigma> (TyCallable \<sigma>s \<sigma>0)" "wf_ty \<Sigma> (TyCallable \<tau>s \<tau>0)"
    with SubtyCallable(2,4) have c: "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "composable \<Sigma> \<sigma>0 \<tau>0" by simp_all
    fix \<tau>'
    assume "\<Sigma> \<turnstile> TyCallable \<tau>s \<tau>0 <: \<tau>'"
    then show "\<Sigma> \<turnstile> TyCallable \<sigma>s \<sigma>0 <: \<tau>'"
      by (rule subty_right_cases)
         (auto simp: XY intro: Subtyping.SubtyCallable composables_R[OF c(1)] composable_L[OF c(2)])
  next
    assume "wf_ty \<Sigma> (TyCallable \<sigma>s \<sigma>0)" "wf_ty \<Sigma> (TyCallable \<tau>s \<tau>0)"
    with SubtyCallable(2,4) have c: "list_all2 (composable \<Sigma>) \<tau>s \<sigma>s" "composable \<Sigma> \<sigma>0 \<tau>0" by simp_all
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyCallable \<sigma>s \<sigma>0"
    then show "\<Sigma> \<turnstile> \<rho> <: TyCallable \<tau>s \<tau>0"
      by (rule subty_left_cases)
         (auto simp: XY intro: Subtyping.SubtyCallable composables_L[OF c(1)] composable_R[OF c(2)])
  qed
next
  case (SubtyTuple \<sigma>s \<tau>s)
  have XY: "\<Sigma> \<turnstile> TyTuple \<sigma>s <: TyTuple \<tau>s" using SubtyTuple(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume "wf_ty \<Sigma> (TyTuple \<sigma>s)" "wf_ty \<Sigma> (TyTuple \<tau>s)"
    with SubtyTuple(2) have c: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" by simp
    fix \<tau>'
    assume "\<Sigma> \<turnstile> TyTuple \<tau>s <: \<tau>'"
    then show "\<Sigma> \<turnstile> TyTuple \<sigma>s <: \<tau>'"
      by (rule subty_right_cases)
         (auto simp: XY intro: Subtyping.SubtySized Subtyping.SubtyTuple composables_L[OF c])
  next
    assume "wf_ty \<Sigma> (TyTuple \<sigma>s)" "wf_ty \<Sigma> (TyTuple \<tau>s)"
    with SubtyTuple(2) have c: "list_all2 (composable \<Sigma>) \<sigma>s \<tau>s" by simp
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyTuple \<sigma>s"
    then show "\<Sigma> \<turnstile> \<rho> <: TyTuple \<tau>s"
      by (rule subty_left_cases) (auto simp: XY intro: Subtyping.SubtyTuple composables_R[OF c])
  qed
next
  case (SubtyLiteral l \<tau>)
  have XY: "\<Sigma> \<turnstile> TyLiteral l <: \<tau>" using SubtyLiteral(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume "wf_ty \<Sigma> \<tau>"
    with SubtyLiteral(2) have c: "composable \<Sigma> (base_type_lit l) \<tau>" by (cases l) simp_all
    fix \<tau>'
    assume "\<Sigma> \<turnstile> \<tau> <: \<tau>'"
    with c have "\<Sigma> \<turnstile> base_type_lit l <: \<tau>'" by (rule composable_L)
    then show "\<Sigma> \<turnstile> TyLiteral l <: \<tau>'" by (rule Subtyping.SubtyLiteral)
  next
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyLiteral l"
    then show "\<Sigma> \<turnstile> \<rho> <: \<tau>" by (rule subty_left_cases) (simp_all add: XY)
  qed
next
  case (SubtyUnionLeft \<sigma> \<tau> \<tau>')
  have XY: "\<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" using SubtyUnionLeft(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')"
    with SubtyUnionLeft(2) have c: "composable \<Sigma> \<sigma> \<tau>" by simp
    fix \<tau>''
    assume "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<tau>''"
    then show "\<Sigma> \<turnstile> \<sigma> <: \<tau>''" by (rule subty_right_cases) (auto simp: XY intro: composable_L[OF c])
  next
    assume "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')"
    with SubtyUnionLeft(2) have c: "composable \<Sigma> \<sigma> \<tau>" by simp
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: \<sigma>"
    with c have "\<Sigma> \<turnstile> \<rho> <: \<tau>" by (rule composable_R)
    then show "\<Sigma> \<turnstile> \<rho> <: TyUnion \<tau> \<tau>'" by (rule Subtyping.SubtyUnionLeft)
  qed
next
  case (SubtyUnionRight \<sigma> \<tau>' \<tau>)
  have XY: "\<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau> \<tau>'" using SubtyUnionRight(1) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')"
    with SubtyUnionRight(2) have c: "composable \<Sigma> \<sigma> \<tau>'" by simp
    fix \<tau>''
    assume "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<tau>''"
    then show "\<Sigma> \<turnstile> \<sigma> <: \<tau>''" by (rule subty_right_cases) (auto simp: XY intro: composable_L[OF c])
  next
    assume "wf_ty \<Sigma> \<sigma>" "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')"
    with SubtyUnionRight(2) have c: "composable \<Sigma> \<sigma> \<tau>'" by simp
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: \<sigma>"
    with c have "\<Sigma> \<turnstile> \<rho> <: \<tau>'" by (rule composable_R)
    then show "\<Sigma> \<turnstile> \<rho> <: TyUnion \<tau> \<tau>'" by (rule Subtyping.SubtyUnionRight)
  qed
next
  case (SubtyUnion \<tau> \<sigma> \<tau>')
  have XY: "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<sigma>" using SubtyUnion(1,3) by (rule subty_subtys.intros)
  show ?case
  proof (intro impI composableI)
    assume "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')" "wf_ty \<Sigma> \<sigma>"
    with SubtyUnion(2,4) have c: "composable \<Sigma> \<tau> \<sigma>" "composable \<Sigma> \<tau>' \<sigma>" by simp_all
    fix \<tau>''
    assume "\<Sigma> \<turnstile> \<sigma> <: \<tau>''"
    with c have "\<Sigma> \<turnstile> \<tau> <: \<tau>''" "\<Sigma> \<turnstile> \<tau>' <: \<tau>''" by (blast intro: composable_L)+
    then show "\<Sigma> \<turnstile> TyUnion \<tau> \<tau>' <: \<tau>''" by (rule Subtyping.SubtyUnion)
  next
    assume "wf_ty \<Sigma> (TyUnion \<tau> \<tau>')" "wf_ty \<Sigma> \<sigma>"
    with SubtyUnion(2,4) have c: "composable \<Sigma> \<tau> \<sigma>" "composable \<Sigma> \<tau>' \<sigma>" by simp_all
    fix \<rho>
    assume "\<Sigma> \<turnstile> \<rho> <: TyUnion \<tau> \<tau>'"
    then show "\<Sigma> \<turnstile> \<rho> <: \<sigma>"
      by (rule subty_left_cases) (auto simp: XY intro: composable_R[OF c(1)] composable_R[OF c(2)])
  qed
next
  case SubtysNil
  show ?case by simp
next
  case (SubtysCons \<sigma> \<tau> \<sigma>s \<tau>s)
  then show ?case by simp
qed

theorem subty_trans:
  "\<lbrakk> wf_class_table \<Sigma> ; wf_ty \<Sigma> \<sigma> ; wf_ty \<Sigma> \<tau> ; \<Sigma> \<turnstile> \<sigma> <: \<tau> ; \<Sigma> \<turnstile> \<tau> <: \<tau>' \<rbrakk> \<Longrightarrow> \<Sigma> \<turnstile> \<sigma> <: \<tau>'"
  by (blast dest: subty_composable(1) composable_L)

(* Substitution preserves subtyping *)
lemma subst_subty:
  assumes wf: "wf_class_table \<Sigma>"
  shows "\<Sigma> \<turnstile> \<sigma> <: \<tau> \<Longrightarrow> wf_ty \<Sigma> \<sigma> \<longrightarrow> wf_ty \<Sigma> \<tau> \<longrightarrow> \<Sigma> \<turnstile> subst \<tau>s \<alpha>s \<sigma> <: subst \<tau>s \<alpha>s \<tau>"
    and "\<Sigma> \<turnstile> \<sigma>s [<:] \<tau>s' \<Longrightarrow> (\<forall>\<sigma> \<in> set \<sigma>s. wf_ty \<Sigma> \<sigma>) \<longrightarrow> (\<forall>\<tau> \<in> set \<tau>s'. wf_ty \<Sigma> \<tau>)
           \<longrightarrow> \<Sigma> \<turnstile> map (subst \<tau>s \<alpha>s) \<sigma>s [<:] map (subst \<tau>s \<alpha>s) \<tau>s'"
proof (induction rule: subty_subtys.inducts)
  case (SubtyClassExtend C D \<omega>s \<sigma>s \<tau>)
  show ?case
  proof (intro impI)
    assume wf\<sigma>: "wf_ty \<Sigma> (TyClass C \<sigma>s)" and "wf_ty \<Sigma> \<tau>"
    with SubtyClassExtend(3) wf_class_table_base[OF wf wf\<sigma> SubtyClassExtend(1)]
    have "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyClass D (map (subst \<sigma>s (type_params \<Sigma> C)) \<omega>s)) <: subst \<tau>s \<alpha>s \<tau>" by blast
    then show "\<Sigma> \<turnstile> subst \<tau>s \<alpha>s (TyClass C \<sigma>s) <: subst \<tau>s \<alpha>s \<tau>"
      unfolding base_subst[OF wf wf\<sigma> SubtyClassExtend(1), symmetric]
      using SubtyClassExtend(1) by (simp add: Subtyping.SubtyClassExtend)
  qed
next
  case (SubtyLiteral l \<tau>)
  then show ?case by (cases l) (auto intro: Subtyping.SubtyLiteral)
qed (auto intro: subty_subtys.intros sized_subst)

end
