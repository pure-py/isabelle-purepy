theory Typing
  imports Semantics
begin

datatype cxt_entry =
    Ty ty
  | DU ty
  | PU ty
  | Unbound
  | TypeVar
  | Scheme scheme
  | PUScheme scheme
  | PredefName

type_synonym cxt = "var \<rightharpoonup> cxt_entry"

(* Possibly unassigned at the same type or scheme; the other forms merge only with themselves *)
fun merge_undefined :: "cxt_entry \<Rightarrow> cxt_entry option"
where
"merge_undefined (Ty \<tau>) = Some (PU \<tau>)" |
"merge_undefined (DU \<tau>) = Some (PU \<tau>)" |
"merge_undefined (PU \<tau>) = Some (PU \<tau>)" |
"merge_undefined (Scheme \<pi>) = Some (PUScheme \<pi>)" |
"merge_undefined (PUScheme \<pi>) = Some (PUScheme \<pi>)" |
"merge_undefined _ = None"

definition merge_cxt_entry :: "cxt_entry option \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry option option"
where
"merge_cxt_entry \<theta> \<theta>' =
  (if \<theta> = \<theta>' then Some \<theta>
   else case (map_option merge_undefined \<theta>, map_option merge_undefined \<theta>') of
     (Some (Some \<theta>\<^sub>P\<^sub>U), Some (Some \<theta>\<^sub>P\<^sub>U')) \<Rightarrow> if \<theta>\<^sub>P\<^sub>U = \<theta>\<^sub>P\<^sub>U' then Some (Some \<theta>\<^sub>P\<^sub>U) else None
   | (Some (Some \<theta>\<^sub>P\<^sub>U), None) \<Rightarrow> Some (Some \<theta>\<^sub>P\<^sub>U)
   | (None, Some (Some \<theta>\<^sub>P\<^sub>U')) \<Rightarrow> Some (Some \<theta>\<^sub>P\<^sub>U')
   | _ \<Rightarrow> None)"

definition merge :: "cxt \<Rightarrow> cxt \<Rightarrow> cxt option" (infixl "\<oplus>" 65)
where
"\<Gamma> \<oplus> \<Gamma>' =
  (let m = \<lambda>x. merge_cxt_entry (\<Gamma> x) (\<Gamma>' x) in
   if \<forall>x. \<exists>\<theta>. m x = Some \<theta> then Some (the \<circ> m) else None)"

datatype static_outcome = Assigns\<^sub>R cxt | Returns\<^sub>R

fun merge_outcome :: "static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome option" (infixl "\<oplus>\<^sub>R" 65)
where
"Assigns\<^sub>R \<Delta> \<oplus>\<^sub>R Assigns\<^sub>R \<Delta>' = map_option Assigns\<^sub>R (\<Delta> \<oplus> \<Delta>')" |
"R \<oplus>\<^sub>R Returns\<^sub>R = Some R" |
"Returns\<^sub>R \<oplus>\<^sub>R R = Some R"

fun override_outcome :: "static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome" (infixl "\<otimes>\<^sub>R" 100)
where
"Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R Assigns\<^sub>R \<Delta>' = Assigns\<^sub>R (\<Delta> \<otimes> \<Delta>')" |
"_ \<otimes>\<^sub>R _ = Returns\<^sub>R"

fun base_type_lit :: "lit \<Rightarrow> ty"
where
"base_type_lit (LitInt _) = TyPrim int" |
"base_type_lit (LitFloat _) = TyPrim float" |
"base_type_lit (LitString _) = TyPrim str" |
"base_type_lit (LitBool _) = TyPrim bool" |
"base_type_lit LitNone = TyPrim NoneType"

fun base_type :: "ty \<Rightarrow> ty"
where
"base_type (TyLiteral l) = base_type_lit l" |
"base_type \<tau> = \<tau>"

fun sized :: "ty \<Rightarrow> bool"
where
"sized (TyList _) = True" |
"sized (TyDict _) = True" |
"sized (TyPrim str) = True" |
"sized (TyTuple _) = True" |
"sized _ = False"

inductive subty :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "<:" 50) and subtys :: "ty list \<Rightarrow> ty list \<Rightarrow> bool" (infix "[<:]" 50)
where
SubtyRefl: "\<tau> <: \<tau>" |
SubtyNever: "TyPrim Never <: \<tau>" |
SubtyObject: "\<tau> <: TyPrim object" |
SubtyIntFloat: "TyPrim int <: TyPrim float" |
SubtySized: "sized \<tau> \<Longrightarrow> \<tau> <: TyPrim Sized" |
SubtyList: "\<lbrakk> \<sigma> <: \<tau> ; \<tau> <: \<sigma> \<rbrakk> \<Longrightarrow> TyList \<sigma> <: TyList \<tau>" |
SubtyDict: "\<lbrakk> \<sigma> <: \<tau> ; \<tau> <: \<sigma> \<rbrakk> \<Longrightarrow> TyDict \<sigma> <: TyDict \<tau>" |
SubtyCallable: "\<lbrakk> \<tau>s [<:] \<sigma>s ; \<sigma> <: \<tau> \<rbrakk> \<Longrightarrow> TyCallable \<sigma>s \<sigma> <: TyCallable \<tau>s \<tau>" |
SubtyTuple: "\<sigma>s [<:] \<tau>s \<Longrightarrow> TyTuple \<sigma>s <: TyTuple \<tau>s" |
SubtyLiteral: "base_type_lit l <: \<tau> \<Longrightarrow> TyLiteral l <: \<tau>" |
SubtyUnionLeft: "\<sigma> <: \<tau> \<Longrightarrow> \<sigma> <: TyUnion \<tau> \<tau>'" |
SubtyUnionRight: "\<sigma> <: \<tau>' \<Longrightarrow> \<sigma> <: TyUnion \<tau> \<tau>'" |
SubtyUnion: "\<lbrakk> \<tau> <: \<sigma> ; \<tau>' <: \<sigma> \<rbrakk> \<Longrightarrow> TyUnion \<tau> \<tau>' <: \<sigma>" |

SubtysNil: "[] [<:] []" |
SubtysCons: "\<lbrakk> \<sigma> <: \<tau> ; \<sigma>s [<:] \<tau>s \<rbrakk> \<Longrightarrow> \<sigma> # \<sigma>s [<:] \<tau> # \<tau>s"

abbreviation equiv :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "\<approx>" 50) where "\<sigma> \<approx> \<tau> \<equiv> \<sigma> <: \<tau> \<and> \<tau> <: \<sigma>"

definition join :: "ty \<Rightarrow> ty \<Rightarrow> ty" (infixl "\<squnion>" 65)
where
"\<sigma> \<squnion> \<tau> = (if \<sigma> <: \<tau> then \<tau> else if \<tau> <: \<sigma> then \<sigma> else TyUnion \<sigma> \<tau>)"

definition joins :: "ty list \<Rightarrow> ty"
where
"joins \<tau>s = foldr (\<squnion>) \<tau>s (TyPrim Never)"

fun meet :: "ty \<Rightarrow> ty \<Rightarrow> ty" (infixl "\<sqinter>" 70) and meets :: "ty list \<Rightarrow> ty list \<Rightarrow> ty list"
where
"TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sqinter> \<tau> =
  (if TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 <: \<tau> then TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 else if \<tau> <: TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 then \<tau>
   else (\<sigma>\<^sub>1 \<sqinter> \<tau>) \<squnion> (\<sigma>\<^sub>2 \<sqinter> \<tau>))" |
"\<sigma> \<sqinter> TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2 =
  (if \<sigma> <: TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2 then \<sigma> else if TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2 <: \<sigma> then TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2
   else (\<sigma> \<sqinter> \<tau>\<^sub>1) \<squnion> (\<sigma> \<sqinter> \<tau>\<^sub>2))" |
"TyCallable \<sigma>s \<sigma> \<sqinter> TyCallable \<tau>s \<tau> =
  (if TyCallable \<sigma>s \<sigma> <: TyCallable \<tau>s \<tau> then TyCallable \<sigma>s \<sigma>
   else if TyCallable \<tau>s \<tau> <: TyCallable \<sigma>s \<sigma> then TyCallable \<tau>s \<tau>
   else if length \<sigma>s = length \<tau>s then TyCallable (map2 (\<squnion>) \<sigma>s \<tau>s) (\<sigma> \<sqinter> \<tau>) else TyPrim Never)" |
"TyTuple \<sigma>s \<sqinter> TyTuple \<tau>s =
  (if TyTuple \<sigma>s <: TyTuple \<tau>s then TyTuple \<sigma>s else if TyTuple \<tau>s <: TyTuple \<sigma>s then TyTuple \<tau>s
   else if length \<sigma>s = length \<tau>s then TyTuple (meets \<sigma>s \<tau>s) else TyPrim Never)" |
"\<sigma> \<sqinter> \<tau> = (if \<sigma> <: \<tau> then \<sigma> else if \<tau> <: \<sigma> then \<tau> else TyPrim Never)" |

"meets (\<sigma> # \<sigma>s) (\<tau> # \<tau>s) = (\<sigma> \<sqinter> \<tau>) # meets \<sigma>s \<tau>s" |
"meets _ _ = []"

fun prim_name :: "prim_ty \<Rightarrow> var"
where
"prim_name object = ''object''" |
"prim_name Never = ''Never''" |
"prim_name NoneType = ''None''" |
"prim_name bool = ''bool''" |
"prim_name int = ''int''" |
"prim_name float = ''float''" |
"prim_name str = ''str''" |
"prim_name Sized = ''Sized''"

abbreviation predef :: "cxt \<Rightarrow> var \<Rightarrow> bool" where "predef \<Gamma> x \<equiv> \<Gamma> x = Some PredefName"

fun resolve_type :: "cxt \<Rightarrow> ty_expr \<Rightarrow> ty option"
where
"resolve_type \<Gamma> (TyExprPrim \<nu>) = (if predef \<Gamma> (prim_name \<nu>) then Some (TyPrim \<nu>) else None)" |
"resolve_type \<Gamma> (TyExprName (\<alpha>, []) []) = (if \<Gamma> \<alpha> = Some TypeVar then Some (TyVar \<alpha>) else None)" |
"resolve_type \<Gamma> (TyExprLiteral l) = (if predef \<Gamma> ''Literal'' then Some (TyLiteral l) else None)" |
"resolve_type \<Gamma> (TyExprList \<psi>) = (if predef \<Gamma> ''list'' then map_option TyList (resolve_type \<Gamma> \<psi>) else None)" |
"resolve_type \<Gamma> (TyExprDict \<psi>) =
  (if predef \<Gamma> ''dict'' \<and> predef \<Gamma> ''str'' then map_option TyDict (resolve_type \<Gamma> \<psi>) else None)" |
"resolve_type \<Gamma> (TyExprTuple \<psi>s) =
  (if predef \<Gamma> ''tuple'' then map_option TyTuple (those (map (resolve_type \<Gamma>) \<psi>s)) else None)" |
"resolve_type \<Gamma> (TyExprCallable \<psi>s \<psi>) =
  (if predef \<Gamma> ''Callable''
    then case (those (map (resolve_type \<Gamma>) \<psi>s), resolve_type \<Gamma> \<psi>) of
      (Some \<sigma>s, Some \<tau>) \<Rightarrow> Some (TyCallable \<sigma>s \<tau>) | _ \<Rightarrow> None
   else None)" |
"resolve_type \<Gamma> (TyExprUnion \<psi> \<psi>') =
  (case (resolve_type \<Gamma> \<psi>, resolve_type \<Gamma> \<psi>') of (Some \<sigma>, Some \<tau>) \<Rightarrow> Some (TyUnion \<sigma> \<tau>) | _ \<Rightarrow> None)" |
"resolve_type \<Gamma> _ = None"

fun equality_type :: "ty \<Rightarrow> bool"
where
"equality_type (TyPrim _) = True" |
"equality_type (TyLiteral _) = True" |
"equality_type (TyList \<tau>) = equality_type \<tau>" |
"equality_type (TyDict \<tau>) = equality_type \<tau>" |
"equality_type (TyTuple \<tau>s) = list_all equality_type \<tau>s" |
"equality_type (TyUnion \<sigma> \<tau>) = (equality_type \<sigma> \<and> equality_type \<tau>)" |
"equality_type _ = False"

abbreviation comparable :: "ty \<Rightarrow> ty \<Rightarrow> bool" where "comparable \<sigma> \<tau> \<equiv> \<sigma> <: \<tau> \<or> \<tau> <: \<sigma>"

inductive binop_overload :: "bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> (ty \<times> ty) \<times> ty \<Rightarrow> bool"
where
OverloadEq:
  "\<lbrakk> op \<in> {BOpEq, BOpNeq} ; equality_type \<sigma>\<^sub>1 ; equality_type \<sigma>\<^sub>2 ; comparable \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((\<sigma>\<^sub>1, \<sigma>\<^sub>2), TyPrim bool)" |
OverloadInList:
  "\<lbrakk> op \<in> {BOpIn, BOpNotIn} ; comparable \<sigma>\<^sub>1 \<tau> \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 (TyList \<tau>) ((\<sigma>\<^sub>1, TyList \<tau>), TyPrim bool)" |
OverloadInTuple:
  "\<lbrakk> op \<in> {BOpIn, BOpNotIn} ; comparable \<sigma>\<^sub>1 (joins \<tau>s) \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 (TyTuple \<tau>s) ((\<sigma>\<^sub>1, TyTuple \<tau>s), TyPrim bool)" |
OverloadInStr:
  "\<lbrakk> op \<in> {BOpIn, BOpNotIn} ; \<sigma>\<^sub>1 <: TyPrim str ; \<sigma>\<^sub>2 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim str, TyPrim str), TyPrim bool)" |
OverloadInDict:
  "\<lbrakk> op \<in> {BOpIn, BOpNotIn} ; \<sigma>\<^sub>1 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 (TyDict \<tau>) ((TyPrim str, TyDict \<tau>), TyPrim bool)" |
OverloadOrderFloat:
  "\<lbrakk> op \<in> {BOpLt, BOpLeq, BOpGt, BOpGeq} ; \<sigma>\<^sub>1 <: TyPrim float ; \<sigma>\<^sub>2 <: TyPrim float \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim float, TyPrim float), TyPrim bool)" |
OverloadOrderStr:
  "\<lbrakk> op \<in> {BOpLt, BOpLeq, BOpGt, BOpGeq} ; \<sigma>\<^sub>1 <: TyPrim str ; \<sigma>\<^sub>2 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim str, TyPrim str), TyPrim bool)" |
OverloadArithInt:
  "\<lbrakk> op \<in> {BOpAdd, BOpSub, BOpMul, BOpFloorDiv, BOpMod} ; \<sigma>\<^sub>1 <: TyPrim int ; \<sigma>\<^sub>2 <: TyPrim int \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim int, TyPrim int), TyPrim int)" |
OverloadArithFloat:
  "\<lbrakk> op \<in> {BOpAdd, BOpSub, BOpMul, BOpFloorDiv, BOpMod, BOpDiv, BOpPow} ; \<sigma>\<^sub>1 <: TyPrim float
   ; \<sigma>\<^sub>2 <: TyPrim float \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim float, TyPrim float), TyPrim float)" |
OverloadAddStr:
  "\<lbrakk> \<sigma>\<^sub>1 <: TyPrim str ; \<sigma>\<^sub>2 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload BOpAdd \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim str, TyPrim str), TyPrim str)" |
OverloadAddList: "binop_overload BOpAdd (TyList \<sigma>) (TyList \<tau>) ((TyList \<sigma>, TyList \<tau>), TyList (\<sigma> \<squnion> \<tau>))" |
OverloadAddTuple:
  "binop_overload BOpAdd (TyTuple \<sigma>s) (TyTuple \<tau>s) ((TyTuple \<sigma>s, TyTuple \<tau>s), TyTuple (\<sigma>s @ \<tau>s))" |
OverloadMulStrInt:
  "\<lbrakk> \<sigma>\<^sub>1 <: TyPrim str ; \<sigma>\<^sub>2 <: TyPrim int \<rbrakk>
  \<Longrightarrow> binop_overload BOpMul \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim str, TyPrim int), TyPrim str)" |
OverloadMulIntStr:
  "\<lbrakk> \<sigma>\<^sub>1 <: TyPrim int ; \<sigma>\<^sub>2 <: TyPrim str \<rbrakk>
  \<Longrightarrow> binop_overload BOpMul \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((TyPrim int, TyPrim str), TyPrim str)" |
OverloadMulListInt:
  "\<sigma>\<^sub>2 <: TyPrim int \<Longrightarrow> binop_overload BOpMul (TyList \<tau>) \<sigma>\<^sub>2 ((TyList \<tau>, TyPrim int), TyList \<tau>)" |
OverloadMulIntList:
  "\<sigma>\<^sub>1 <: TyPrim int \<Longrightarrow> binop_overload BOpMul \<sigma>\<^sub>1 (TyList \<tau>) ((TyPrim int, TyList \<tau>), TyList \<tau>)" |
OverloadPowNat:
  "\<lbrakk> \<sigma>\<^sub>1 <: TyPrim int ; n \<ge> 0 \<rbrakk>
  \<Longrightarrow> binop_overload BOpPow \<sigma>\<^sub>1 (TyLiteral (LitInt n)) ((TyPrim int, TyLiteral (LitInt n)), TyPrim int)" |
OverloadPowNeg:
  "\<lbrakk> \<sigma>\<^sub>1 <: TyPrim int ; n < 0 \<rbrakk>
  \<Longrightarrow> binop_overload BOpPow \<sigma>\<^sub>1 (TyLiteral (LitInt n)) ((TyPrim int, TyLiteral (LitInt n)), TyPrim float)" |
OverloadBase:
  "binop_overload op (base_type \<sigma>\<^sub>1) (base_type \<sigma>\<^sub>2) ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>) \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>)"

inductive unop_overload :: "uop \<Rightarrow> ty \<Rightarrow> ty \<times> ty \<Rightarrow> bool"
where
UnopOverloadNot: "\<sigma> <: TyPrim bool \<Longrightarrow> unop_overload UOpNot \<sigma> (TyPrim bool, TyPrim bool)" |
UnopOverloadInt:
  "\<lbrakk> op \<in> {UOpPos, UOpNeg} ; \<sigma> <: TyPrim int \<rbrakk> \<Longrightarrow> unop_overload op \<sigma> (TyPrim int, TyPrim int)" |
UnopOverloadFloat:
  "\<lbrakk> op \<in> {UOpPos, UOpNeg} ; \<sigma> <: TyPrim float \<rbrakk> \<Longrightarrow> unop_overload op \<sigma> (TyPrim float, TyPrim float)" |
UnopOverloadBase: "unop_overload op (base_type \<sigma>) (\<tau>, \<tau>') \<Longrightarrow> unop_overload op \<sigma> (\<tau>, \<tau>')"

definition binop_most_specific :: "bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> (ty \<times> ty) \<times> ty \<Rightarrow> bool"
where
"binop_most_specific op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b \<longleftrightarrow>
  binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b \<and>
  (\<forall>b'. binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b' \<longrightarrow> fst (fst b) <: fst (fst b') \<and> snd (fst b) <: snd (fst b'))"

definition unop_most_specific :: "uop \<Rightarrow> ty \<Rightarrow> ty \<times> ty \<Rightarrow> bool"
where
"unop_most_specific op \<sigma> b \<longleftrightarrow> unop_overload op \<sigma> b \<and> (\<forall>b'. unop_overload op \<sigma> b' \<longrightarrow> fst b <: fst b')"

definition resolve_binop :: "bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty option"
where
"resolve_binop op \<sigma>\<^sub>1 \<sigma>\<^sub>2 =
  (if \<exists>!b. binop_most_specific op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b then Some (snd (THE b. binop_most_specific op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b)) else None)"

definition resolve_unop :: "uop \<Rightarrow> ty \<Rightarrow> ty option"
where
"resolve_unop op \<sigma> =
  (if \<exists>!b. unop_most_specific op \<sigma> b then Some (snd (THE b. unop_most_specific op \<sigma> b)) else None)"

fun numeric_literal :: "expr \<Rightarrow> bool"
where
"numeric_literal (ExprLiteral (LitInt _)) = True" |
"numeric_literal (ExprLiteral (LitFloat _)) = True" |
"numeric_literal _ = False"

function (sequential)
  synth :: "cxt \<Rightarrow> expr \<Rightarrow> ty option" and
  synths :: "cxt \<Rightarrow> expr list \<Rightarrow> ty option list" and
  check :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" and
  check' :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" and
  checks :: "cxt \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool"
where
"synth \<Gamma> (ExprVar x) = (case \<Gamma> x of Some (Ty \<tau>) \<Rightarrow> Some \<tau> | _ \<Rightarrow> None)" |
"synth \<Gamma> (ExprLiteral l) = (case l of LitFloat _ \<Rightarrow> Some (TyPrim float) | _ \<Rightarrow> Some (TyLiteral l))" |
"synth \<Gamma> (ExprCall e (es, kws)) =
  (if kws \<noteq> [] then None
   else case e of
     ExprLambda xs e' \<Rightarrow>
       (case those (synths \<Gamma> es) of
          Some \<tau>s \<Rightarrow> if distinct xs \<and> length xs = length es then synth (\<Gamma>(xs [\<mapsto>] map Ty \<tau>s)) e' else None
        | None \<Rightarrow> None)
   | _ \<Rightarrow>
       (case synth \<Gamma> e of
          Some (TyCallable \<sigma>s \<sigma>) \<Rightarrow> if \<sigma> \<noteq> TyPrim NoneType \<and> checks \<Gamma> es \<sigma>s then Some \<sigma> else None
        | _ \<Rightarrow> None))" |
"synth \<Gamma> (ExprBinOp op e e') =
  (case (synth \<Gamma> e, synth \<Gamma> e') of (Some \<sigma>, Some \<sigma>') \<Rightarrow> resolve_binop op \<sigma> \<sigma>' | _ \<Rightarrow> None)" |
"synth \<Gamma> (ExprUnOp op e) =
  (if op = UOpNeg \<and> numeric_literal e then None
   else case synth \<Gamma> e of Some \<sigma> \<Rightarrow> resolve_unop op \<sigma> | None \<Rightarrow> None)" |
"synth \<Gamma> (ExprAnd e e') =
  (if check \<Gamma> e (TyPrim bool) \<and> check \<Gamma> e' (TyPrim bool) then Some (TyPrim bool) else None)" |
"synth \<Gamma> (ExprOr e e') =
  (if check \<Gamma> e (TyPrim bool) \<and> check \<Gamma> e' (TyPrim bool) then Some (TyPrim bool) else None)" |
"synth \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) =
  (if check \<Gamma> e (TyPrim bool) then
     case (synth \<Gamma> e\<^sub>1, synth \<Gamma> e\<^sub>2) of
       (Some \<sigma>\<^sub>1, Some \<sigma>\<^sub>2) \<Rightarrow> Some (\<sigma>\<^sub>1 \<squnion> \<sigma>\<^sub>2)
     | (Some \<sigma>\<^sub>1, None) \<Rightarrow> if check \<Gamma> e\<^sub>2 \<sigma>\<^sub>1 then Some \<sigma>\<^sub>1 else None
     | (None, Some \<sigma>\<^sub>2) \<Rightarrow> if check \<Gamma> e\<^sub>1 \<sigma>\<^sub>2 then Some \<sigma>\<^sub>2 else None
     | _ \<Rightarrow> None
   else None)" |
"synth \<Gamma> (ExprList es) =
  (let \<sigma>s = synths \<Gamma> es; \<tau> = joins (map base_type (map the (filter (\<lambda>\<sigma>. \<sigma> \<noteq> None) \<sigma>s))) in
   if es \<noteq> [] \<and> (\<exists>\<sigma> \<in> set \<sigma>s. \<sigma> \<noteq> None) \<and> (\<forall>j < length es. \<sigma>s ! j = None \<longrightarrow> check \<Gamma> (es ! j) \<tau>)
   then Some (TyList \<tau>) else None)" |
"synth \<Gamma> (ExprTuple es) = map_option TyTuple (those (synths \<Gamma> es))" |
"synth \<Gamma> _ = None" |

"synths \<Gamma> [] = []" |
"synths \<Gamma> (e # es) = synth \<Gamma> e # synths \<Gamma> es" |

"check \<Gamma> e \<tau> = (check' \<Gamma> e \<tau> \<or> (case synth \<Gamma> e of Some \<sigma> \<Rightarrow> \<sigma> <: \<tau> | None \<Rightarrow> False))" |

"check' \<Gamma> (ExprLambda xs e) \<tau> =
  (case \<tau> of
     TyCallable \<tau>s \<tau>' \<Rightarrow> distinct xs \<and> length xs = length \<tau>s \<and> check (\<Gamma>(xs [\<mapsto>] map Ty \<tau>s)) e \<tau>'
   | _ \<Rightarrow> False)" |
"check' \<Gamma> (ExprCall e (es, kws)) \<tau> =
  (case e of
     ExprLambda xs e' \<Rightarrow>
       kws = [] \<and>
       (case those (synths \<Gamma> es) of
          Some \<tau>s \<Rightarrow> distinct xs \<and> length xs = length es \<and> check (\<Gamma>(xs [\<mapsto>] map Ty \<tau>s)) e' \<tau>
        | None \<Rightarrow> False)
   | _ \<Rightarrow> False)" |
"check' \<Gamma> (ExprList es) \<tau> = (case \<tau> of TyList \<tau>' \<Rightarrow> checks \<Gamma> es (replicate (length es) \<tau>') | _ \<Rightarrow> False)" |
"check' \<Gamma> (ExprTuple es) \<tau> = (case \<tau> of TyTuple \<tau>s \<Rightarrow> checks \<Gamma> es \<tau>s | _ \<Rightarrow> False)" |
"check' \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) \<tau> = (check \<Gamma> e (TyPrim bool) \<and> check \<Gamma> e\<^sub>1 \<tau> \<and> check \<Gamma> e\<^sub>2 \<tau>)" |
"check' \<Gamma> _ _ = False" |

"checks \<Gamma> [] [] = True" |
"checks \<Gamma> (e # es) (\<tau> # \<tau>s) = (check \<Gamma> e \<tau> \<and> checks \<Gamma> es \<tau>s)" |
"checks \<Gamma> _ _ = False"
by pat_completeness auto

termination
by (relation "measure (\<lambda>x. case x of
     Inl (Inl (\<Gamma>, e)) \<Rightarrow> 3 * size e
   | Inl (Inr (Inl (\<Gamma>, es))) \<Rightarrow> 3 * size_list size es
   | Inl (Inr (Inr (\<Gamma>, e, \<tau>))) \<Rightarrow> 3 * size e + 2
   | Inr (Inl (\<Gamma>, e, \<tau>)) \<Rightarrow> 3 * size e + 1
   | Inr (Inr (\<Gamma>, es, \<tau>s)) \<Rightarrow> 3 * size_list size es + 2)")
   (auto dest!: nth_mem intro: size_list_estimation' simp: less_Suc_eq_le)

(* Context entry binding a function name: its type scheme, or its type when there are no type parameters *)
fun scheme_cxt_entry :: "scheme \<Rightarrow> cxt_entry"
where
"scheme_cxt_entry (TyScheme [] \<tau>) = Ty \<tau>" |
"scheme_cxt_entry \<pi> = Scheme \<pi>"

fun def_signature :: "cxt \<Rightarrow> func \<Rightarrow> scheme option"
where
"def_signature \<Gamma> (Def f \<alpha>s xps \<psi> s) =
   (let \<Gamma>' = \<Gamma>(\<alpha>s [\<mapsto>] replicate (length \<alpha>s) TypeVar) in
    case (those (map (resolve_type \<Gamma>' \<circ> snd) xps), resolve_type \<Gamma>' \<psi>) of
     (Some \<sigma>s, Some \<tau>) \<Rightarrow> Some (TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>))
   | _ \<Rightarrow> None)"

(* Call of a callable with result None, which is a statement *)
fun call_none :: "cxt \<Rightarrow> expr \<Rightarrow> bool"
where
"call_none \<Gamma> (ExprCall e (es, [])) =
  (case synth \<Gamma> e of Some (TyCallable \<sigma>s (TyPrim NoneType)) \<Rightarrow> checks \<Gamma> es \<sigma>s | _ \<Rightarrow> False)" |
"call_none \<Gamma> _ = False"

abbreviation false_literal :: expr where "false_literal \<equiv> ExprLiteral (LitBool False)"

fun merges :: "static_outcome option list \<Rightarrow> static_outcome option"
where
"merges [] = Some Returns\<^sub>R" |
"merges (R # Rs) = (case (R, merges Rs) of (Some R, Some R') \<Rightarrow> R \<oplus>\<^sub>R R' | _ \<Rightarrow> None)"

fun stmt_ty :: "cxt \<Rightarrow> ty option \<Rightarrow> stmt \<Rightarrow> static_outcome option"
and elifs_ty :: "cxt \<Rightarrow> ty option \<Rightarrow> (expr \<times> stmt) list \<Rightarrow> static_outcome option list"
and defs_ty :: "cxt \<Rightarrow> func list \<Rightarrow> scheme list \<Rightarrow> bool"
and def_body :: "cxt \<Rightarrow> func \<Rightarrow> scheme \<Rightarrow> bool"
where
"stmt_ty \<Gamma> \<zeta> StmtPass = Some (Assigns\<^sub>R Map.empty)" |
"stmt_ty \<Gamma> \<zeta> (StmtDeclare x \<psi>) = map_option (\<lambda>\<tau>. Assigns\<^sub>R [x \<mapsto> DU \<tau>]) (resolve_type \<Gamma> \<psi>)" |
"stmt_ty \<Gamma> \<zeta> (StmtAssign x None e) =
  (case \<Gamma> x of Some (DU \<tau>) \<Rightarrow> if check \<Gamma> e \<tau> then Some (Assigns\<^sub>R [x \<mapsto> Ty \<tau>]) else None | _ \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtAssign x (Some \<psi>) e) =
  (case resolve_type \<Gamma> \<psi> of Some \<tau> \<Rightarrow> if check \<Gamma> e \<tau> then Some (Assigns\<^sub>R [x \<mapsto> Ty \<tau>]) else None | None \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtExpr e) = (if synth \<Gamma> e \<noteq> None \<or> call_none \<Gamma> e then Some (Assigns\<^sub>R Map.empty) else None)" |
"stmt_ty \<Gamma> \<zeta> (StmtAssert e None) =
  (if e = false_literal then Some Returns\<^sub>R
   else if check \<Gamma> e (TyPrim bool) then Some (Assigns\<^sub>R Map.empty) else None)" |
"stmt_ty \<Gamma> \<zeta> (StmtAssert e (Some e')) =
  (if \<not> check \<Gamma> e' (TyPrim str) then None else if e = false_literal then Some Returns\<^sub>R
   else if check \<Gamma> e (TyPrim bool) then Some (Assigns\<^sub>R Map.empty) else None)" |
"stmt_ty \<Gamma> \<zeta> (StmtReturn None) =
  (case \<zeta> of Some \<tau> \<Rightarrow> if \<tau> \<approx> TyPrim NoneType then Some Returns\<^sub>R else None | None \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtReturn (Some e)) =
  (case \<zeta> of Some \<tau> \<Rightarrow> if check \<Gamma> e \<tau> then Some Returns\<^sub>R else None | None \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtIf e s elifs else') =
  (if check \<Gamma> e (TyPrim bool)
    then merges (stmt_ty \<Gamma> \<zeta> s # elifs_ty \<Gamma> \<zeta> elifs
                 @ [case else' of Some s' \<Rightarrow> stmt_ty \<Gamma> \<zeta> s' | None \<Rightarrow> Some (Assigns\<^sub>R Map.empty)])
   else None)" |
"stmt_ty \<Gamma> \<zeta> (StmtSeq s s') =
  (case stmt_ty \<Gamma> \<zeta> s of
     Some (Assigns\<^sub>R \<Delta>) \<Rightarrow> map_option (\<lambda>R. Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R R) (stmt_ty (\<Gamma> \<otimes> \<Delta>) \<zeta> s')
   | _ \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtMutualRegion ds) =
  (case those (map (def_signature \<Gamma>) ds) of
     Some \<pi>s \<Rightarrow>
       let \<Delta> = map_of (zip (map def_name ds) (map scheme_cxt_entry \<pi>s)) in
       if defs_ty (\<Gamma> \<otimes> \<Delta>) ds \<pi>s then Some (Assigns\<^sub>R \<Delta>) else None
   | None \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtMatch e bs) = None" |

"elifs_ty \<Gamma> \<zeta> [] = []" |
"elifs_ty \<Gamma> \<zeta> ((e, s) # elifs) =
  (if check \<Gamma> e (TyPrim bool) then stmt_ty \<Gamma> \<zeta> s else None) # elifs_ty \<Gamma> \<zeta> elifs" |

"defs_ty \<Gamma> [] [] = True" |
"defs_ty \<Gamma> (d # ds) (\<pi> # \<pi>s) = (def_body \<Gamma> d \<pi> \<and> defs_ty \<Gamma> ds \<pi>s)" |
"defs_ty \<Gamma> _ _ = False" |

"def_body \<Gamma> (Def f \<alpha>s xps \<psi> s) (TyScheme \<alpha>s' (TyCallable \<sigma>s \<tau>)) =
  (distinct (map fst xps) \<and> length xps = length \<sigma>s \<and>
   (case scope Unbound (set (map fst xps)) s of
      Some \<Delta> \<Rightarrow>
        (case stmt_ty (\<Gamma>(\<alpha>s [\<mapsto>] replicate (length \<alpha>s) TypeVar, map fst xps [\<mapsto>] map Ty \<sigma>s) \<otimes> \<Delta>) (Some \<tau>) s of
           Some R \<Rightarrow> R = Returns\<^sub>R \<or> \<tau> \<approx> TyPrim NoneType
         | None \<Rightarrow> False)
    | None \<Rightarrow> False))" |
"def_body \<Gamma> _ _ = False"

end
