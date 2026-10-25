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

fun meet :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty"
and meets :: "class_table \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> ty list"
where
"meet \<Sigma> (TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<tau> =
  (if \<Sigma> \<turnstile> TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 <: \<tau> then TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 else if \<Sigma> \<turnstile> \<tau> <: TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 then \<tau>
   else (meet \<Sigma> \<sigma>\<^sub>1 \<tau>) \<squnion>\<^bsub>\<Sigma>\<^esub> (meet \<Sigma> \<sigma>\<^sub>2 \<tau>))" |
"meet \<Sigma> \<sigma> (TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2) =
  (if \<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2 then \<sigma> else if \<Sigma> \<turnstile> TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2 <: \<sigma> then TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2
   else (meet \<Sigma> \<sigma> \<tau>\<^sub>1) \<squnion>\<^bsub>\<Sigma>\<^esub> (meet \<Sigma> \<sigma> \<tau>\<^sub>2))" |
"meet \<Sigma> (TyCallable \<sigma>s \<sigma>) (TyCallable \<tau>s \<tau>) =
  (if \<Sigma> \<turnstile> TyCallable \<sigma>s \<sigma> <: TyCallable \<tau>s \<tau> then TyCallable \<sigma>s \<sigma>
   else if \<Sigma> \<turnstile> TyCallable \<tau>s \<tau> <: TyCallable \<sigma>s \<sigma> then TyCallable \<tau>s \<tau>
   else if length \<sigma>s = length \<tau>s
   then TyCallable (map2 (\<lambda>\<sigma>' \<tau>'. \<sigma>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') \<sigma>s \<tau>s) (meet \<Sigma> \<sigma> \<tau>)
   else TyPrim Never)" |
"meet \<Sigma> (TyTuple \<sigma>s) (TyTuple \<tau>s) =
  (if \<Sigma> \<turnstile> TyTuple \<sigma>s <: TyTuple \<tau>s then TyTuple \<sigma>s else if \<Sigma> \<turnstile> TyTuple \<tau>s <: TyTuple \<sigma>s then TyTuple \<tau>s
   else if length \<sigma>s = length \<tau>s then TyTuple (meets \<Sigma> \<sigma>s \<tau>s) else TyPrim Never)" |
"meet \<Sigma> \<sigma> \<tau> = (if \<Sigma> \<turnstile> \<sigma> <: \<tau> then \<sigma> else if \<Sigma> \<turnstile> \<tau> <: \<sigma> then \<tau> else TyPrim Never)" |

"meets \<Sigma> (\<sigma> # \<sigma>s) (\<tau> # \<tau>s) = meet \<Sigma> \<sigma> \<tau> # meets \<Sigma> \<sigma>s \<tau>s" |
"meets _ _ _ = []"

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
   and the type synthesised by the index *)
fun subscript_type :: "class_table \<Rightarrow> ty \<Rightarrow> reason + unit \<Rightarrow> reason + unit \<Rightarrow> reason + ty \<Rightarrow> reason + ty"
where
"subscript_type \<Sigma> (TyUnion \<sigma> \<sigma>') int_ok str_ok idx = do {
   \<tau> \<leftarrow> subscript_type \<Sigma> \<sigma> int_ok str_ok idx; \<tau>' \<leftarrow> subscript_type \<Sigma> \<sigma>' int_ok str_ok idx; Inr (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>')
 }" |
"subscript_type \<Sigma> (TyList \<tau>) int_ok _ _ = do { int_ok; Inr \<tau> }" |
"subscript_type \<Sigma> (TyDict \<tau>) _ str_ok _ = do { str_ok; Inr \<tau> }" |
"subscript_type \<Sigma> (TyTuple \<tau>s) _ _ idx = do {
   \<iota> \<leftarrow> idx;
   case \<iota> of
     TyLiteral (LitInt n) \<Rightarrow>
       if 0 \<le> n \<and> n < of_nat (length \<tau>s) then Inr (\<tau>s ! nat n)
       else if n < 0 \<and> 0 \<le> of_nat (length \<tau>s) + n then Inr (\<tau>s ! nat (of_nat (length \<tau>s) + n))
       else Inl (TupleIndexOutOfRange n (length \<tau>s))
   | TyPrim int \<Rightarrow> Inr (joins \<Sigma> \<tau>s)
   | _ \<Rightarrow> Inl (TypeMismatch (TyPrim int) \<iota>)
 }" |
"subscript_type \<Sigma> \<sigma> int_ok _ _ =
  (if base_type \<sigma> = TyPrim str then do { int_ok; Inr (TyPrim str) } else Inl (NotSubscriptable \<sigma>))"

(* Type of attribute x of a value of type \<sigma>, which isn't a module *)
fun attribute_type :: "class_table \<Rightarrow> ty \<Rightarrow> var \<Rightarrow> reason + ty"
where
"attribute_type \<Sigma> (TyUnion \<sigma> \<sigma>') x =
  do { \<tau> \<leftarrow> attribute_type \<Sigma> \<sigma> x; \<tau>' \<leftarrow> attribute_type \<Sigma> \<sigma>' x; Inr (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') }" |
"attribute_type \<Sigma> (TyClass C \<sigma>s) x =
  (case map_of (instantiate (fields \<Sigma> C) \<sigma>s) x of
     Some \<sigma> \<Rightarrow> Inr \<sigma>
   | None \<Rightarrow> Inl (UnknownField (short_name C) x))" |
"attribute_type \<Sigma> \<sigma> _ = Inl (NoAttributes \<sigma>)"

end
