theory Operators
  imports Subtyping
begin

(* V holds the classes assumed to be equality classes, those whose fields are being examined, and \<alpha>s the
   type variables assumed to be equality types *)
function (sequential)
  equality_type :: "class_table \<Rightarrow> name list \<Rightarrow> var list \<Rightarrow> ty \<Rightarrow> bool" and
  equality_class :: "class_table \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> bool"
where
"equality_type \<Sigma> V \<alpha>s (TyPrim _) = True" |
"equality_type \<Sigma> V \<alpha>s (TyLiteral _) = True" |
"equality_type \<Sigma> V \<alpha>s (TyVar \<alpha>) = (\<alpha> \<in> set \<alpha>s)" |
"equality_type \<Sigma> V \<alpha>s (TyList \<tau>) = equality_type \<Sigma> V \<alpha>s \<tau>" |
"equality_type \<Sigma> V \<alpha>s (TyDict \<tau>) = equality_type \<Sigma> V \<alpha>s \<tau>" |
"equality_type \<Sigma> V \<alpha>s (TyTuple \<tau>s) = list_all (equality_type \<Sigma> V \<alpha>s) \<tau>s" |
"equality_type \<Sigma> V \<alpha>s (TyUnion \<sigma> \<tau>) = (equality_type \<Sigma> V \<alpha>s \<sigma> \<and> equality_type \<Sigma> V \<alpha>s \<tau>)" |
"equality_type \<Sigma> V \<alpha>s (TyClass C \<sigma>s) =
  (equality_class \<Sigma> V C \<and>
   (case fields \<Sigma> C of
      FieldScheme \<beta>s x\<sigma>s \<Rightarrow>
        list_all (\<lambda>(\<beta>, \<sigma>). \<beta> \<notin> \<Union> (set (map (fv \<circ> snd) x\<sigma>s)) \<or> equality_type \<Sigma> V \<alpha>s \<sigma>) (zip \<beta>s \<sigma>s)))" |
"equality_type \<Sigma> V \<alpha>s _ = False" |

"equality_class \<Sigma> V C =
  (if C \<in> set V then True
   else case fmlookup \<Sigma> C of
     Some _ \<Rightarrow>
       (case fields \<Sigma> C of
          FieldScheme \<alpha>s x\<sigma>s \<Rightarrow> list_all (equality_type \<Sigma> (C # V) \<alpha>s \<circ> snd) x\<sigma>s)
   | None \<Rightarrow> False)"
by pat_completeness auto

termination
by (relation "measures [
     \<lambda>x. case x of Inl (\<Sigma>, V, _, _) \<Rightarrow> card (fmdom' \<Sigma> - set V) | Inr (\<Sigma>, V, _) \<Rightarrow> card (fmdom' \<Sigma> - set V),
     \<lambda>x. case x of Inl (_, _, _, \<tau>) \<Rightarrow> size \<tau> | Inr _ \<Rightarrow> 0]")
   (auto simp: card_fmdom_insert less_Suc_eq dest: set_zip_rightD intro: size_list_elem)

abbreviation comparable :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" where "comparable \<Sigma> \<sigma> \<tau> \<equiv> \<Sigma> \<turnstile> \<sigma> <: \<tau> \<or> \<Sigma> \<turnstile> \<tau> <: \<sigma>"

inductive binop_overload :: "class_table \<Rightarrow> bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> (ty \<times> ty) \<times> ty \<Rightarrow> bool"
for \<Sigma> :: class_table
where
OverloadEq:
  "\<lbrakk> op \<in> {BOpEq, BOpNeq} ; equality_type \<Sigma> [] [] \<sigma>\<^sub>1 ; equality_type \<Sigma> [] [] \<sigma>\<^sub>2 ; comparable \<Sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((\<sigma>\<^sub>1, \<sigma>\<^sub>2), TyPrim bool)" |
OverloadInList:
  "\<lbrakk> op \<in> {BOpIn, BOpNotIn} ; comparable \<Sigma> \<sigma>\<^sub>1 \<tau> \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 (TyList \<tau>) ((\<sigma>\<^sub>1, TyList \<tau>), TyPrim bool)" |
OverloadInTuple:
  "\<lbrakk> op \<in> {BOpIn, BOpNotIn} ; comparable \<Sigma> \<sigma>\<^sub>1 (joins \<Sigma> \<tau>s) \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 (TyTuple \<tau>s) ((\<sigma>\<^sub>1, TyTuple \<tau>s), TyPrim bool)" |
OverloadInStr:
  "\<lbrakk> op \<in> {BOpIn, BOpNotIn} ; \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim str ; \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim str, TyPrim str), TyPrim bool)" |
OverloadInDict:
  "\<lbrakk> op \<in> {BOpIn, BOpNotIn} ; \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 (TyDict \<tau>) ((TyPrim str, TyDict \<tau>), TyPrim bool)" |
OverloadOrderFloat:
  "\<lbrakk> op \<in> {BOpLt, BOpLeq, BOpGt, BOpGeq} ; \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim float ; \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: TyPrim float \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim float, TyPrim float), TyPrim bool)" |
OverloadOrderStr:
  "\<lbrakk> op \<in> {BOpLt, BOpLeq, BOpGt, BOpGeq} ; \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim str ; \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim str, TyPrim str), TyPrim bool)" |
OverloadArithInt:
  "\<lbrakk> op \<in> {BOpAdd, BOpSub, BOpMul, BOpFloorDiv, BOpMod} ; \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim int ; \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: TyPrim int \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim int, TyPrim int), TyPrim int)" |
OverloadArithFloat:
  "\<lbrakk> op \<in> {BOpAdd, BOpSub, BOpMul, BOpFloorDiv, BOpMod, BOpDiv, BOpPow} ; \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim float
   ; \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: TyPrim float \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim float, TyPrim float), TyPrim float)" |
OverloadAddStr:
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim str ; \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> BOpAdd \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim str, TyPrim str), TyPrim str)" |
OverloadAddList: "binop_overload \<Sigma> BOpAdd (TyList \<sigma>) (TyList \<tau>) ((TyList \<sigma>, TyList \<tau>), TyList (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>))" |
OverloadAddTuple:
  "binop_overload \<Sigma> BOpAdd (TyTuple \<sigma>s) (TyTuple \<tau>s) ((TyTuple \<sigma>s, TyTuple \<tau>s), TyTuple (\<sigma>s @ \<tau>s))" |
OverloadMulStrInt:
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim str ; \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: TyPrim int \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> BOpMul \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim str, TyPrim int), TyPrim str)" |
OverloadMulIntStr:
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim int ; \<Sigma> \<turnstile> \<sigma>\<^sub>2 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> BOpMul \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim int, TyPrim str), TyPrim str)" |
OverloadMulListInt:
  "\<Sigma> \<turnstile> \<sigma>\<^sub>2 <: TyPrim int \<Longrightarrow> binop_overload \<Sigma> BOpMul (TyList \<tau>) \<sigma>\<^sub>2 ((TyList \<tau>, TyPrim int), TyList \<tau>)" |
OverloadMulIntList:
  "\<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim int \<Longrightarrow> binop_overload \<Sigma> BOpMul \<sigma>\<^sub>1 (TyList \<tau>) ((TyPrim int, TyList \<tau>), TyList \<tau>)" |
OverloadPowNat:
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim int ; n \<ge> 0 \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> BOpPow \<sigma>\<^sub>1 (TyLiteral (LitInt n)) ((TyPrim int, TyLiteral (LitInt n)), TyPrim int)" |
OverloadPowNeg:
  "\<lbrakk> \<Sigma> \<turnstile> \<sigma>\<^sub>1 <: TyPrim int ; n < 0 \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> BOpPow \<sigma>\<^sub>1 (TyLiteral (LitInt n)) ((TyPrim int, TyLiteral (LitInt n)), TyPrim float)" |
OverloadBase:
  "\<lbrakk> literal_type \<sigma>\<^sub>1 \<or> literal_type \<sigma>\<^sub>2 ; binop_overload \<Sigma> op (base_type \<sigma>\<^sub>1) (base_type \<sigma>\<^sub>2) ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>) \<rbrakk>
  \<Longrightarrow> binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>)"

inductive unop_overload :: "class_table \<Rightarrow> uop \<Rightarrow> ty \<Rightarrow> ty \<times> ty \<Rightarrow> bool"
for \<Sigma> :: class_table
where
UnopOverloadNot: "\<Sigma> \<turnstile> \<sigma> <: TyPrim bool \<Longrightarrow> unop_overload \<Sigma> UOpNot \<sigma> (TyPrim bool, TyPrim bool)" |
UnopOverloadInt:
  "\<lbrakk> op \<in> {UOpPos, UOpNeg} ; \<Sigma> \<turnstile> \<sigma> <: TyPrim int \<rbrakk> \<Longrightarrow> unop_overload \<Sigma> op \<sigma> (TyPrim int, TyPrim int)" |
UnopOverloadFloat:
  "\<lbrakk> op \<in> {UOpPos, UOpNeg} ; \<Sigma> \<turnstile> \<sigma> <: TyPrim float \<rbrakk> \<Longrightarrow> unop_overload \<Sigma> op \<sigma> (TyPrim float, TyPrim float)" |
UnopOverloadBase:
  "\<lbrakk> literal_type \<sigma> ; unop_overload \<Sigma> op (base_type \<sigma>) (\<tau>, \<tau>') \<rbrakk> \<Longrightarrow> unop_overload \<Sigma> op \<sigma> (\<tau>, \<tau>')"

definition binop_overloads :: "class_table \<Rightarrow> bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ((ty \<times> ty) \<times> ty) set"
where
"binop_overloads \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 = {\<omega>. binop_overload \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega>}"

definition unop_overloads :: "class_table \<Rightarrow> uop \<Rightarrow> ty \<Rightarrow> (ty \<times> ty) set"
where
"unop_overloads \<Sigma> op \<sigma> = {\<omega>. unop_overload \<Sigma> op \<sigma> \<omega>}"

definition resolve_binop :: "class_table \<Rightarrow> bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty option"
where
"resolve_binop \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2 =
  (let overloads = binop_overloads \<Sigma> op \<sigma>\<^sub>1 \<sigma>\<^sub>2;
       most_specific =
         Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> overloads. \<Sigma> \<turnstile> \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<Sigma> \<turnstile> \<tau>\<^sub>2 <: \<tau>\<^sub>2') overloads in
   if is_singleton most_specific then Some (snd (the_elem most_specific)) else None)"

definition resolve_unop :: "class_table \<Rightarrow> uop \<Rightarrow> ty \<Rightarrow> ty option"
where
"resolve_unop \<Sigma> op \<sigma> =
  (let overloads = unop_overloads \<Sigma> op \<sigma>;
       most_specific = Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> overloads. \<Sigma> \<turnstile> \<tau> <: \<tau>') overloads in
   if is_singleton most_specific then Some (snd (the_elem most_specific)) else None)"

end
