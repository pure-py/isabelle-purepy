theory Typing
  imports Semantics
begin

datatype cxt_entry =
    Ty ty
  | DU ty
  | PU ty
  | Unbound
  | ModStub name
  | ModChecked name "(var, cxt_entry) fmap"
  | Type name
  | TypeVar
  | Scheme ty_scheme
  | PUScheme ty_scheme
  | PredefName

type_synonym cxt = "(var, cxt_entry) fmap"

fun prefix_of :: "name \<Rightarrow> name \<Rightarrow> bool" (infix "\<preceq>" 50)
where
"(y, ys) \<preceq> (y', ys') = (y = y' \<and> take (length ys) ys' = ys)"

definition proper_prefix_of :: "name \<Rightarrow> name \<Rightarrow> bool" (infix "\<prec>" 50)
where
"q \<prec> q' = (q \<preceq> q' \<and> q \<noteq> q')"

(* Shortest first *)
fun proper_prefixes :: "name \<Rightarrow> name list"
where
"proper_prefixes (y, ys) = map (\<lambda>i. (y, take i ys)) [0..<length ys]"

definition unique_to :: "name \<Rightarrow> name \<Rightarrow> name list"
where
"unique_to q' q = filter (\<lambda>p. \<not> p \<preceq> q) (proper_prefixes q')"

definition builtins :: name where "builtins = (''builtins'', [])"
definition main :: name where "main = (''__main__'', [])"

(* Entry of a name looked up in a module signature, as resolution of a simple name finds it *)
fun resolve_name :: "cxt \<Rightarrow> var \<Rightarrow> cxt_entry option"
where
"resolve_name \<Gamma> x =
  (case fmlookup \<Gamma> x of
     Some (Ty \<tau>) \<Rightarrow> Some (Ty \<tau>)
   | Some (ModChecked q \<Gamma>') \<Rightarrow> Some (ModChecked q \<Gamma>')
   | Some (Type C) \<Rightarrow> Some (Type C)
   | Some (Scheme \<pi>) \<Rightarrow> Some (Scheme \<pi>)
   | Some PredefName \<Rightarrow> Some PredefName
   | _ \<Rightarrow> None)"


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

fun literal_type :: "ty \<Rightarrow> bool"
where
"literal_type (TyLiteral _) = True" |
"literal_type _ = False"

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

(* Type at which a variable is bound or declared *)
fun var_ty :: "cxt_entry \<Rightarrow> ty option"
where
"var_ty (Ty \<tau>) = Some \<tau>" |
"var_ty (DU \<tau>) = Some \<tau>" |
"var_ty (PU \<tau>) = Some \<tau>" |
"var_ty _ = None"

(* Merge of a context entry with undefined *)
fun possibly_unassigned :: "cxt_entry \<Rightarrow> cxt_entry"
where
"possibly_unassigned (Ty \<tau>) = PU \<tau>" |
"possibly_unassigned (DU \<tau>) = PU \<tau>" |
"possibly_unassigned (PU \<tau>) = PU \<tau>" |
"possibly_unassigned (Scheme \<pi>) = PUScheme \<pi>" |
"possibly_unassigned (PUScheme \<pi>) = PUScheme \<pi>" |
"possibly_unassigned _ = undefined"

fun merge_cxt_entry :: "cxt_entry option \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry"
where
"merge_cxt_entry (Some (Ty \<sigma>)) (Some (Ty \<tau>)) = Ty (\<sigma> \<squnion> \<tau>)" |
"merge_cxt_entry (Some (Scheme \<pi>)) (Some (PUScheme \<pi>')) = (if \<pi> = \<pi>' then PUScheme \<pi> else undefined)" |
"merge_cxt_entry (Some (PUScheme \<pi>)) (Some (Scheme \<pi>')) = (if \<pi> = \<pi>' then PUScheme \<pi> else undefined)" |
"merge_cxt_entry (Some \<theta>) (Some \<theta>') =
  (if \<theta> = \<theta>' then \<theta>
   else case (var_ty \<theta>, var_ty \<theta>') of (Some \<sigma>, Some \<tau>) \<Rightarrow> PU (\<sigma> \<squnion> \<tau>) | _ \<Rightarrow> undefined)" |
"merge_cxt_entry (Some \<theta>) None = possibly_unassigned \<theta>" |
"merge_cxt_entry None (Some \<theta>) = possibly_unassigned \<theta>" |
"merge_cxt_entry None None = undefined"

definition merge :: "cxt \<Rightarrow> cxt \<Rightarrow> cxt" (infixl "\<oplus>" 65)
where
"\<Gamma> \<oplus> \<Gamma>' = fmmap_keys (\<lambda>x _. merge_cxt_entry (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x)) (\<Gamma> \<otimes> \<Gamma>')"

datatype static_outcome = Assigns\<^sub>R cxt | Returns\<^sub>R

fun merge_outcome :: "static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome" (infixl "\<oplus>\<^sub>R" 65)
where
"Assigns\<^sub>R \<Delta> \<oplus>\<^sub>R Assigns\<^sub>R \<Delta>' = Assigns\<^sub>R (\<Delta> \<oplus> \<Delta>')" |
"R \<oplus>\<^sub>R Returns\<^sub>R = R" |
"Returns\<^sub>R \<oplus>\<^sub>R R = R"

fun merges :: "static_outcome option list \<Rightarrow> static_outcome option"
where
"merges [] = Some Returns\<^sub>R" |
"merges (R # Rs) = (case (R, merges Rs) of (Some R, Some R') \<Rightarrow> Some (R \<oplus>\<^sub>R R') | _ \<Rightarrow> None)"

fun override_outcome :: "static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome" (infixl "\<otimes>\<^sub>R" 100)
where
"Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R Assigns\<^sub>R \<Delta>' = Assigns\<^sub>R (\<Delta> \<otimes> \<Delta>')" |
"_ \<otimes>\<^sub>R _ = Returns\<^sub>R"

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

abbreviation predef :: "cxt \<Rightarrow> var \<Rightarrow> bool" where "predef \<Gamma> x \<equiv> fmlookup \<Gamma> x = Some PredefName"

fun resolve_type :: "cxt \<Rightarrow> ty_expr \<Rightarrow> ty option"
where
"resolve_type \<Gamma> (TyExprPrim \<nu>) = (if predef \<Gamma> (prim_name \<nu>) then Some (TyPrim \<nu>) else None)" |
"resolve_type \<Gamma> (TyExprName (\<alpha>, []) []) = (if fmlookup \<Gamma> \<alpha> = Some TypeVar then Some (TyVar \<alpha>) else None)" |
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
  "\<lbrakk> literal_type \<sigma>\<^sub>1 \<or> literal_type \<sigma>\<^sub>2 ; binop_overload op (base_type \<sigma>\<^sub>1) (base_type \<sigma>\<^sub>2) ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>) \<rbrakk>
  \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 ((\<tau>\<^sub>1, \<tau>\<^sub>2), \<tau>)"

inductive unop_overload :: "uop \<Rightarrow> ty \<Rightarrow> ty \<times> ty \<Rightarrow> bool"
where
UnopOverloadNot: "\<sigma> <: TyPrim bool \<Longrightarrow> unop_overload UOpNot \<sigma> (TyPrim bool, TyPrim bool)" |
UnopOverloadInt:
  "\<lbrakk> op \<in> {UOpPos, UOpNeg} ; \<sigma> <: TyPrim int \<rbrakk> \<Longrightarrow> unop_overload op \<sigma> (TyPrim int, TyPrim int)" |
UnopOverloadFloat:
  "\<lbrakk> op \<in> {UOpPos, UOpNeg} ; \<sigma> <: TyPrim float \<rbrakk> \<Longrightarrow> unop_overload op \<sigma> (TyPrim float, TyPrim float)" |
UnopOverloadBase:
  "\<lbrakk> literal_type \<sigma> ; unop_overload op (base_type \<sigma>) (\<tau>, \<tau>') \<rbrakk> \<Longrightarrow> unop_overload op \<sigma> (\<tau>, \<tau>')"

definition binop_overloads :: "bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ((ty \<times> ty) \<times> ty) set"
where
"binop_overloads op \<sigma>\<^sub>1 \<sigma>\<^sub>2 = {\<omega>. binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<omega>}"

definition unop_overloads :: "uop \<Rightarrow> ty \<Rightarrow> (ty \<times> ty) set"
where
"unop_overloads op \<sigma> = {\<omega>. unop_overload op \<sigma> \<omega>}"

definition resolve_binop :: "bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty option"
where
"resolve_binop op \<sigma>\<^sub>1 \<sigma>\<^sub>2 =
  (let overloads = binop_overloads op \<sigma>\<^sub>1 \<sigma>\<^sub>2;
       most_specific =
         Set.filter (\<lambda>((\<tau>\<^sub>1, \<tau>\<^sub>2), _). \<forall>((\<tau>\<^sub>1', \<tau>\<^sub>2'), _) \<in> overloads. \<tau>\<^sub>1 <: \<tau>\<^sub>1' \<and> \<tau>\<^sub>2 <: \<tau>\<^sub>2') overloads in
   if is_singleton most_specific then Some (snd (the_elem most_specific)) else None)"

definition resolve_unop :: "uop \<Rightarrow> ty \<Rightarrow> ty option"
where
"resolve_unop op \<sigma> =
  (let overloads = unop_overloads op \<sigma>;
       most_specific = Set.filter (\<lambda>(\<tau>, _). \<forall>(\<tau>', _) \<in> overloads. \<tau> <: \<tau>') overloads in
   if is_singleton most_specific then Some (snd (the_elem most_specific)) else None)"

fun numeric_literal :: "expr \<Rightarrow> bool"
where
"numeric_literal (ExprLiteral (LitInt _)) = True" |
"numeric_literal (ExprLiteral (LitFloat _)) = True" |
"numeric_literal _ = False"


fun binds_quals :: "qualifier list \<Rightarrow> var set"
where
"binds_quals [] = {}" |
"binds_quals (Guard _ # gs) = binds_quals gs" |
"binds_quals (Generator x _ # gs) = {x} \<union> binds_quals gs"

(* Free variables; the generators of a comprehension bind in the later qualifiers and in its elements *)
fun fv :: "expr \<Rightarrow> var set" and fv_quals :: "qualifier list \<Rightarrow> var set"
where
"fv (ExprVar x) = {x}" |
"fv (ExprLiteral _) = {}" |
"fv (ExprCall e (es, kws)) = fv e \<union> \<Union> (set (map fv es)) \<union> \<Union> (set (map (fv \<circ> snd) kws))" |
"fv (ExprDict kvs) = \<Union> (set (map (fv \<circ> fst) kvs)) \<union> \<Union> (set (map (fv \<circ> snd) kvs))" |
"fv (ExprAttribute e _) = fv e" |
"fv (ExprSubscript e e') = fv e \<union> fv e'" |
"fv (ExprBinOp _ e e') = fv e \<union> fv e'" |
"fv (ExprUnOp _ e) = fv e" |
"fv (ExprAnd e e') = fv e \<union> fv e'" |
"fv (ExprOr e e') = fv e \<union> fv e'" |
"fv (ExprCond e\<^sub>1 e e\<^sub>2) = fv e\<^sub>1 \<union> fv e \<union> fv e\<^sub>2" |
"fv (ExprList es) = \<Union> (set (map fv es))" |
"fv (ExprTuple es) = \<Union> (set (map fv es))" |
"fv (ExprListComp e gs) = fv_quals gs \<union> (fv e - binds_quals gs)" |
"fv (ExprDictComp e e' gs) = fv_quals gs \<union> ((fv e \<union> fv e') - binds_quals gs)" |
"fv (ExprLambda xs e) = fv e - set xs" |

"fv_quals [] = {}" |
"fv_quals (Guard e # gs) = fv e \<union> fv_quals gs" |
"fv_quals (Generator x e # gs) = fv e \<union> (fv_quals gs - {x})"

fun captures :: "expr \<Rightarrow> var set" and captures_quals :: "qualifier list \<Rightarrow> var set"
where
"captures (ExprVar _) = {}" |
"captures (ExprLiteral _) = {}" |
"captures (ExprCall e (es, kws)) =
  captures e \<union> \<Union> (set (map captures es)) \<union> \<Union> (set (map (captures \<circ> snd) kws))" |
"captures (ExprDict kvs) = \<Union> (set (map (captures \<circ> fst) kvs)) \<union> \<Union> (set (map (captures \<circ> snd) kvs))" |
"captures (ExprAttribute e _) = captures e" |
"captures (ExprSubscript e e') = captures e \<union> captures e'" |
"captures (ExprBinOp _ e e') = captures e \<union> captures e'" |
"captures (ExprUnOp _ e) = captures e" |
"captures (ExprAnd e e') = captures e \<union> captures e'" |
"captures (ExprOr e e') = captures e \<union> captures e'" |
"captures (ExprCond e\<^sub>1 e e\<^sub>2) = captures e\<^sub>1 \<union> captures e \<union> captures e\<^sub>2" |
"captures (ExprList es) = \<Union> (set (map captures es))" |
"captures (ExprTuple es) = \<Union> (set (map captures es))" |
"captures (ExprListComp e gs) = captures_quals gs \<union> (captures e - binds_quals gs)" |
"captures (ExprDictComp e e' gs) = captures_quals gs \<union> ((captures e \<union> captures e') - binds_quals gs)" |
"captures (ExprLambda xs e) = fv e - set xs" |

"captures_quals [] = {}" |
"captures_quals (Guard e # gs) = captures e \<union> captures_quals gs" |
"captures_quals (Generator x e # gs) = captures e \<union> (captures_quals gs - {x})"

(* Type of the elements drawn by a generator *)
fun elem_type :: "ty \<Rightarrow> ty option"
where
"elem_type (TyList \<tau>) = Some \<tau>" |
"elem_type (TyPrim str) = Some (TyPrim str)" |
"elem_type (TyLiteral (LitString _)) = Some (TyPrim str)" |
"elem_type (TyDict _) = Some (TyPrim str)" |
"elem_type (TyClass C []) = (if C = snoc builtins ''range'' then Some (TyPrim int) else None)" |
"elem_type (TyTuple \<tau>s) = Some (joins (map base_type \<tau>s))" |
"elem_type (TyUnion \<sigma> \<tau>) =
  (case (elem_type \<sigma>, elem_type \<tau>) of (Some \<sigma>', Some \<tau>') \<Rightarrow> Some (\<sigma>' \<squnion> \<tau>') | _ \<Rightarrow> None)" |
"elem_type _ = None"

(* Type of a subscript of a value of the first type, given whether the index checks against int and
   against str and the type it synthesises; a union is subscripted at each alternative *)
fun subscript_type :: "ty \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ty option \<Rightarrow> ty option"
where
"subscript_type (TyUnion \<sigma> \<sigma>') int_ok str_ok idx =
  (case (subscript_type \<sigma> int_ok str_ok idx, subscript_type \<sigma>' int_ok str_ok idx) of
     (Some \<tau>, Some \<tau>') \<Rightarrow> Some (\<tau> \<squnion> \<tau>') | _ \<Rightarrow> None)" |
"subscript_type (TyList \<tau>) int_ok str_ok idx = (if int_ok then Some \<tau> else None)" |
"subscript_type (TyDict \<tau>) int_ok str_ok idx = (if str_ok then Some \<tau> else None)" |
"subscript_type (TyTuple \<tau>s) int_ok str_ok idx =
  (case idx of
     Some (TyLiteral (LitInt n)) \<Rightarrow>
       if 0 \<le> n \<and> n < of_nat (length \<tau>s) then Some (\<tau>s ! nat n)
       else if - of_nat (length \<tau>s) \<le> n \<and> n < 0 then Some (\<tau>s ! nat (of_nat (length \<tau>s) + n)) else None
   | Some (TyPrim int) \<Rightarrow> Some (joins \<tau>s)
   | _ \<Rightarrow> None)" |
"subscript_type \<sigma> int_ok str_ok idx =
  (if base_type \<sigma> = TyPrim str \<and> int_ok then Some (TyPrim str) else None)"

(* Entry of a qualified name, as resolution finds it in the signatures of checked modules *)
fun resolve_qualified :: "cxt \<Rightarrow> expr \<Rightarrow> cxt_entry option"
where
"resolve_qualified \<Gamma> (ExprVar x) = resolve_name \<Gamma> x" |
"resolve_qualified \<Gamma> (ExprAttribute e x) =
  (case resolve_qualified \<Gamma> e of Some (ModChecked q \<Gamma>') \<Rightarrow> resolve_name \<Gamma>' x | _ \<Rightarrow> None)" |
"resolve_qualified \<Gamma> _ = None"

lemma size_prod_pair [simp]: "size_prod f g p = f (fst p) + g (snd p) + Suc 0"
  by (cases p) simp

lemma size_list_fst: "size_list (size \<circ> fst) kvs \<le> size_list (\<lambda>x. Suc (size (fst x) + size (snd x))) kvs"
  by (rule size_list_pointwise) simp

lemma size_list_snd: "size_list (size \<circ> snd) kvs \<le> size_list (\<lambda>x. Suc (size (fst x) + size (snd x))) kvs"
  by (rule size_list_pointwise) simp

function (sequential)
  synth_expr :: "cxt \<Rightarrow> expr \<Rightarrow> ty option" and
  synth_exprs :: "cxt \<Rightarrow> expr list \<Rightarrow> ty option list" and
  check_expr :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" and
  check_expr' :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" and
  check_exprs :: "cxt \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool" and
  quals :: "cxt \<Rightarrow> qualifier list \<Rightarrow> cxt option"
where
"synth_expr \<Gamma> (ExprVar x) = (case fmlookup \<Gamma> x of Some (Ty \<tau>) \<Rightarrow> Some \<tau> | _ \<Rightarrow> None)" |
"synth_expr \<Gamma> (ExprLiteral l) = (case l of LitFloat _ \<Rightarrow> Some (TyPrim float) | _ \<Rightarrow> Some (TyLiteral l))" |
"synth_expr \<Gamma> (ExprCall e (es, kws)) =
  (if kws \<noteq> [] then None
   else case e of
     ExprLambda xs e' \<Rightarrow>
       (case those (synth_exprs \<Gamma> es) of
          Some \<tau>s \<Rightarrow>
            if distinct xs \<and> length xs = length es then synth_expr (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e'
            else None
        | None \<Rightarrow> None)
   | _ \<Rightarrow>
       (case synth_expr \<Gamma> e of
          Some (TyCallable \<sigma>s \<sigma>) \<Rightarrow> if \<sigma> \<noteq> TyPrim NoneType \<and> check_exprs \<Gamma> es \<sigma>s then Some \<sigma> else None
        | _ \<Rightarrow> None))" |
"synth_expr \<Gamma> (ExprBinOp op e e') =
  (case (synth_expr \<Gamma> e, synth_expr \<Gamma> e') of (Some \<sigma>, Some \<sigma>') \<Rightarrow> resolve_binop op \<sigma> \<sigma>' | _ \<Rightarrow> None)" |
"synth_expr \<Gamma> (ExprUnOp op e) =
  (if op = UOpNeg \<and> numeric_literal e then None
   else case synth_expr \<Gamma> e of Some \<sigma> \<Rightarrow> resolve_unop op \<sigma> | None \<Rightarrow> None)" |
"synth_expr \<Gamma> (ExprAnd e e') =
  (if check_expr \<Gamma> e (TyPrim bool) \<and> check_expr \<Gamma> e' (TyPrim bool) then Some (TyPrim bool) else None)" |
"synth_expr \<Gamma> (ExprOr e e') =
  (if check_expr \<Gamma> e (TyPrim bool) \<and> check_expr \<Gamma> e' (TyPrim bool) then Some (TyPrim bool) else None)" |
"synth_expr \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) =
  (if check_expr \<Gamma> e (TyPrim bool) then
     case (synth_expr \<Gamma> e\<^sub>1, synth_expr \<Gamma> e\<^sub>2) of
       (Some \<sigma>\<^sub>1, Some \<sigma>\<^sub>2) \<Rightarrow> Some (\<sigma>\<^sub>1 \<squnion> \<sigma>\<^sub>2)
     | (Some \<sigma>\<^sub>1, None) \<Rightarrow> if check_expr \<Gamma> e\<^sub>2 \<sigma>\<^sub>1 then Some \<sigma>\<^sub>1 else None
     | (None, Some \<sigma>\<^sub>2) \<Rightarrow> if check_expr \<Gamma> e\<^sub>1 \<sigma>\<^sub>2 then Some \<sigma>\<^sub>2 else None
     | _ \<Rightarrow> None
   else None)" |
"synth_expr \<Gamma> (ExprList es) =
  (let \<sigma>s = synth_exprs \<Gamma> es; \<tau> = joins (map base_type (map the (filter (\<lambda>\<sigma>. \<sigma> \<noteq> None) \<sigma>s))) in
   if es \<noteq> [] \<and> (\<exists>\<sigma> \<in> set \<sigma>s. \<sigma> \<noteq> None) \<and> (\<forall>j < length es. \<sigma>s ! j = None \<longrightarrow> check_expr \<Gamma> (es ! j) \<tau>)
   then Some (TyList \<tau>) else None)" |
"synth_expr \<Gamma> (ExprTuple es) = map_option TyTuple (those (synth_exprs \<Gamma> es))" |
"synth_expr \<Gamma> (ExprAttribute e x) =
  (case resolve_qualified \<Gamma> (ExprAttribute e x) of Some (Ty \<tau>) \<Rightarrow> Some \<tau> | _ \<Rightarrow> None)" |
"synth_expr \<Gamma> (ExprSubscript e e') =
  (case synth_expr \<Gamma> e of
     Some \<sigma> \<Rightarrow>
       subscript_type \<sigma> (check_expr \<Gamma> e' (TyPrim int)) (check_expr \<Gamma> e' (TyPrim str)) (synth_expr \<Gamma> e')
   | None \<Rightarrow> None)" |
"synth_expr \<Gamma> (ExprDict kvs) =
  (let \<sigma>s = synth_exprs \<Gamma> (map snd kvs); \<tau> = joins (map base_type (map the (filter (\<lambda>\<sigma>. \<sigma> \<noteq> None) \<sigma>s))) in
   if kvs \<noteq> [] \<and> check_exprs \<Gamma> (map fst kvs) (replicate (length kvs) (TyPrim str))
      \<and> (\<exists>\<sigma> \<in> set \<sigma>s. \<sigma> \<noteq> None)
      \<and> (\<forall>j < length kvs. \<sigma>s ! j = None \<longrightarrow> check_expr \<Gamma> (snd (kvs ! j)) \<tau>)
   then Some (TyDict \<tau>) else None)" |
"synth_expr \<Gamma> (ExprListComp e gs) =
  (case quals \<Gamma> gs of
     Some \<Delta> \<Rightarrow>
       if fmpred (\<lambda>x _. x \<notin> captures e) \<Delta>
       then map_option (\<lambda>\<tau>. TyList (base_type \<tau>)) (synth_expr (\<Gamma> \<otimes> \<Delta>) e) else None
   | None \<Rightarrow> None)" |
"synth_expr \<Gamma> (ExprDictComp e e' gs) =
  (case quals \<Gamma> gs of
     Some \<Delta> \<Rightarrow>
       if fmpred (\<lambda>x _. x \<notin> captures e \<union> captures e') \<Delta> \<and> check_expr (\<Gamma> \<otimes> \<Delta>) e (TyPrim str)
       then map_option (\<lambda>\<tau>. TyDict (base_type \<tau>)) (synth_expr (\<Gamma> \<otimes> \<Delta>) e') else None
   | None \<Rightarrow> None)" |
"synth_expr \<Gamma> _ = None" |

"synth_exprs \<Gamma> [] = []" |
"synth_exprs \<Gamma> (e # es) = synth_expr \<Gamma> e # synth_exprs \<Gamma> es" |

"check_expr \<Gamma> e \<tau> = (check_expr' \<Gamma> e \<tau> \<or> (case synth_expr \<Gamma> e of Some \<sigma> \<Rightarrow> \<sigma> <: \<tau> | None \<Rightarrow> False))" |

"check_expr' \<Gamma> (ExprLambda xs e) \<tau> =
  (case \<tau> of
     TyCallable \<tau>s \<tau>' \<Rightarrow>
       distinct xs \<and> length xs = length \<tau>s \<and> check_expr (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e \<tau>'
   | _ \<Rightarrow> False)" |
"check_expr' \<Gamma> (ExprCall e (es, kws)) \<tau> =
  (case e of
     ExprLambda xs e' \<Rightarrow>
       kws = [] \<and>
       (case those (synth_exprs \<Gamma> es) of
          Some \<tau>s \<Rightarrow>
            distinct xs \<and> length xs = length es \<and> check_expr (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e' \<tau>
        | None \<Rightarrow> False)
   | _ \<Rightarrow> False)" |
"check_expr' \<Gamma> (ExprList es) \<tau> =
  (case \<tau> of TyList \<tau>' \<Rightarrow> check_exprs \<Gamma> es (replicate (length es) \<tau>') | _ \<Rightarrow> False)" |
"check_expr' \<Gamma> (ExprTuple es) \<tau> = (case \<tau> of TyTuple \<tau>s \<Rightarrow> check_exprs \<Gamma> es \<tau>s | _ \<Rightarrow> False)" |
"check_expr' \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) \<tau> = (check_expr \<Gamma> e (TyPrim bool) \<and> check_expr \<Gamma> e\<^sub>1 \<tau> \<and> check_expr \<Gamma> e\<^sub>2 \<tau>)" |
"check_expr' \<Gamma> (ExprDict kvs) \<tau> =
  (case \<tau> of
     TyDict \<tau>' \<Rightarrow>
       check_exprs \<Gamma> (map fst kvs) (replicate (length kvs) (TyPrim str))
       \<and> check_exprs \<Gamma> (map snd kvs) (replicate (length kvs) \<tau>')
   | _ \<Rightarrow> False)" |
"check_expr' \<Gamma> (ExprListComp e gs) \<tau> =
  (case (\<tau>, quals \<Gamma> gs) of
     (TyList \<tau>', Some \<Delta>) \<Rightarrow> fmpred (\<lambda>x _. x \<notin> captures e) \<Delta> \<and> check_expr (\<Gamma> \<otimes> \<Delta>) e \<tau>'
   | _ \<Rightarrow> False)" |
"check_expr' \<Gamma> (ExprDictComp e e' gs) \<tau> =
  (case (\<tau>, quals \<Gamma> gs) of
     (TyDict \<tau>', Some \<Delta>) \<Rightarrow>
       fmpred (\<lambda>x _. x \<notin> captures e \<union> captures e') \<Delta> \<and> check_expr (\<Gamma> \<otimes> \<Delta>) e (TyPrim str)
       \<and> check_expr (\<Gamma> \<otimes> \<Delta>) e' \<tau>'
   | _ \<Rightarrow> False)" |
"check_expr' \<Gamma> _ _ = False" |

"check_exprs \<Gamma> [] [] = True" |
"check_exprs \<Gamma> (e # es) (\<tau> # \<tau>s) = (check_expr \<Gamma> e \<tau> \<and> check_exprs \<Gamma> es \<tau>s)" |
"check_exprs \<Gamma> _ _ = False" |

"quals \<Gamma> [] = Some fmempty" |
"quals \<Gamma> (Guard e # gs) = (if check_expr \<Gamma> e (TyPrim bool) then quals \<Gamma> gs else None)" |
"quals \<Gamma> (Generator x e # gs) =
  (case map_option elem_type (synth_expr \<Gamma> e) of
     Some (Some \<sigma>) \<Rightarrow>
       if x \<in> captures_quals gs then None
       else map_option (\<lambda>\<Delta>. fmupd x (Ty \<sigma>) fmempty \<otimes> \<Delta>) (quals (\<Gamma> \<otimes> fmupd x (Ty \<sigma>) fmempty) gs)
   | _ \<Rightarrow> None)"
by pat_completeness auto

termination
by (relation "measures [\<lambda>x. case x of
     Inl (Inl (\<Gamma>, e)) \<Rightarrow> size e
   | Inl (Inr (Inl (\<Gamma>, es))) \<Rightarrow> size_list size es
   | Inl (Inr (Inr (\<Gamma>, e, \<tau>))) \<Rightarrow> size e
   | Inr (Inl (\<Gamma>, e, \<tau>)) \<Rightarrow> size e
   | Inr (Inr (Inl (\<Gamma>, es, \<tau>s))) \<Rightarrow> size_list size es
   | Inr (Inr (Inr (\<Gamma>, gs))) \<Rightarrow> size_list size gs,
   \<lambda>x. case x of
     Inl (Inl _) \<Rightarrow> 0
   | Inl (Inr (Inl _)) \<Rightarrow> 0
   | Inl (Inr (Inr _)) \<Rightarrow> 2
   | Inr (Inl _) \<Rightarrow> 1
   | Inr (Inr (Inl _)) \<Rightarrow> 2
   | Inr (Inr (Inr _)) \<Rightarrow> 0]")
   (auto dest!: nth_mem intro: size_list_estimation' simp: less_Suc_eq_le size_list_fst size_list_snd)

(* Context entry for a type scheme, which is a plain type if it has no type parameters *)
fun signature_entry :: "ty_scheme \<Rightarrow> cxt_entry"
where
"signature_entry (TyScheme [] \<tau>) = Ty \<tau>" |
"signature_entry \<pi> = Scheme \<pi>"

fun def_signature :: "cxt \<Rightarrow> func \<Rightarrow> ty_scheme option"
where
"def_signature \<Gamma> (Def f \<alpha>s xps \<psi> s) =
   (let \<Gamma>' = \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar in
    case (those (map (resolve_type \<Gamma>' \<circ> snd) xps), resolve_type \<Gamma>' \<psi>) of
     (Some \<sigma>s, Some \<tau>) \<Rightarrow> Some (TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>))
   | _ \<Rightarrow> None)"

abbreviation false_lit :: expr where "false_lit \<equiv> ExprLiteral (LitBool False)"

fun check_stmt :: "cxt \<Rightarrow> ty option \<Rightarrow> stmt \<Rightarrow> static_outcome option"
and check_elifs :: "cxt \<Rightarrow> ty option \<Rightarrow> (expr \<times> stmt) list \<Rightarrow> static_outcome option list"
and check_defs :: "cxt \<Rightarrow> func list \<Rightarrow> ty_scheme list \<Rightarrow> bool"
and check_def :: "cxt \<Rightarrow> func \<Rightarrow> ty_scheme \<Rightarrow> bool"
where
"check_stmt \<Gamma> \<zeta> StmtPass = Some (Assigns\<^sub>R fmempty)" |
"check_stmt \<Gamma> \<zeta> (StmtDeclare x \<psi>) = map_option (\<lambda>\<tau>. Assigns\<^sub>R (fmupd x (DU \<tau>) fmempty)) (resolve_type \<Gamma> \<psi>)" |
"check_stmt \<Gamma> \<zeta> (StmtAssign x None e) =
  (case fmlookup \<Gamma> x of
     Some (DU \<tau>) \<Rightarrow> if check_expr \<Gamma> e \<tau> then Some (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty)) else None
   | _ \<Rightarrow> None)" |
"check_stmt \<Gamma> \<zeta> (StmtAssign x (Some \<psi>) e) =
  (case resolve_type \<Gamma> \<psi> of
     Some \<tau> \<Rightarrow> if check_expr \<Gamma> e \<tau> then Some (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty)) else None
   | None \<Rightarrow> None)" |
"check_stmt \<Gamma> \<zeta> (StmtExpr e) =
  (if synth_expr \<Gamma> e \<noteq> None \<or>
      (case e of ExprCall e' (es, []) \<Rightarrow>
         (case synth_expr \<Gamma> e' of Some (TyCallable \<sigma>s (TyPrim NoneType)) \<Rightarrow> check_exprs \<Gamma> es \<sigma>s | _ \<Rightarrow> False)
       | _ \<Rightarrow> False)
   then Some (Assigns\<^sub>R fmempty) else None)" |
"check_stmt \<Gamma> \<zeta> (StmtAssert e None) =
  (if e = false_lit then Some Returns\<^sub>R
   else if check_expr \<Gamma> e (TyPrim bool) then Some (Assigns\<^sub>R fmempty) else None)" |
"check_stmt \<Gamma> \<zeta> (StmtAssert e (Some e')) =
  (if \<not> check_expr \<Gamma> e' (TyPrim str) then None else if e = false_lit then Some Returns\<^sub>R
   else if check_expr \<Gamma> e (TyPrim bool) then Some (Assigns\<^sub>R fmempty) else None)" |
"check_stmt \<Gamma> \<zeta> (StmtReturn None) =
  (case \<zeta> of Some \<tau> \<Rightarrow> if \<tau> \<approx> TyPrim NoneType then Some Returns\<^sub>R else None | None \<Rightarrow> None)" |
"check_stmt \<Gamma> \<zeta> (StmtReturn (Some e)) =
  (case \<zeta> of Some \<tau> \<Rightarrow> if check_expr \<Gamma> e \<tau> then Some Returns\<^sub>R else None | None \<Rightarrow> None)" |
"check_stmt \<Gamma> \<zeta> (StmtIf e s elifs else') =
  (if check_expr \<Gamma> e (TyPrim bool)
    then merges (check_stmt \<Gamma> \<zeta> s # check_elifs \<Gamma> \<zeta> elifs
                 @ [case else' of Some s' \<Rightarrow> check_stmt \<Gamma> \<zeta> s' | None \<Rightarrow> Some (Assigns\<^sub>R fmempty)])
   else None)" |
"check_stmt \<Gamma> \<zeta> (StmtSeq s s') =
  (case check_stmt \<Gamma> \<zeta> s of
     Some (Assigns\<^sub>R \<Delta>) \<Rightarrow> map_option (\<lambda>R. Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R R) (check_stmt (\<Gamma> \<otimes> \<Delta>) \<zeta> s')
   | _ \<Rightarrow> None)" |
"check_stmt \<Gamma> \<zeta> (StmtMutualRegion ds) =
  (case those (map (def_signature \<Gamma>) ds) of
     Some \<pi>s \<Rightarrow>
       let \<Delta> = fmap_of_list (zip (map def_name ds) (map signature_entry \<pi>s)) in
       if check_defs (\<Gamma> \<otimes> \<Delta>) ds \<pi>s then Some (Assigns\<^sub>R \<Delta>) else None
   | None \<Rightarrow> None)" |
"check_stmt \<Gamma> \<zeta> (StmtMatch e bs) = None" |

"check_elifs \<Gamma> \<zeta> [] = []" |
"check_elifs \<Gamma> \<zeta> ((e, s) # elifs) =
  (if check_expr \<Gamma> e (TyPrim bool) then check_stmt \<Gamma> \<zeta> s else None) # check_elifs \<Gamma> \<zeta> elifs" |

"check_defs \<Gamma> [] [] = True" |
"check_defs \<Gamma> (d # ds) (\<pi> # \<pi>s) = (check_def \<Gamma> d \<pi> \<and> check_defs \<Gamma> ds \<pi>s)" |
"check_defs \<Gamma> _ _ = False" |

"check_def \<Gamma> (Def f \<alpha>s xps \<psi> s) (TyScheme \<alpha>s' (TyCallable \<sigma>s \<tau>)) =
  (let xs = map fst xps in
   distinct xs \<and> length xs = length \<sigma>s \<and>
   (case scope Unbound (set xs) s of
      Some \<Delta> \<Rightarrow>
        (case check_stmt (\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> fmap_of_list (zip xs (map Ty \<sigma>s)) \<otimes> \<Delta>) (Some \<tau>) s of
           Some R \<Rightarrow> R = Returns\<^sub>R \<or> \<tau> \<approx> TyPrim NoneType
         | None \<Rightarrow> False)
    | None \<Rightarrow> False))" |
"check_def \<Gamma> _ _ = False"

section \<open>Modules\<close>

abbreviation name_entry :: "var \<times> cxt_entry" where "name_entry \<equiv> (''__name__'', Ty (TyPrim str))"

(* Context of a predefined module *)
definition predefined :: "name \<Rightarrow> cxt option"
where
"predefined q =
  (if q = builtins then Some (fmap_of_list
     ([name_entry,
       (''print'', Ty (TyCallable [TyPrim object] (TyPrim NoneType))),
       (''len'', Ty (TyCallable [TyPrim Sized] (TyPrim int))),
       (''range'', Type (snoc builtins ''range'')),
       (''round'', Ty (TyCallable [TyPrim float] (TyPrim int)))]
      @ map (\<lambda>\<nu>. (prim_name \<nu>, PredefName)) [NoneType, object, bool, int, float, str]
      @ [(''list'', PredefName), (''dict'', PredefName), (''tuple'', PredefName)]))
   else if q = (''sys'', []) then Some (fmap_of_list
     [name_entry, (''argv'', Ty (TyList (TyPrim str))), (''exit'', Ty (TyCallable [TyPrim int] (TyPrim Never)))])
   else if q = (''typing'', []) then Some (fmap_of_list
     [name_entry, (''Callable'', PredefName), (''Literal'', PredefName),
      (prim_name Never, PredefName), (prim_name Sized, PredefName)])
   else if q = (''dataclasses'', []) then Some (fmap_of_list [name_entry, (''dataclass'', PredefName)])
   else None)"

(* Pointwise combination of a map of extension functions with a context, over the keys of either *)
definition extend_with :: "(var, cxt_entry option \<Rightarrow> cxt_entry) fmap \<Rightarrow> cxt \<Rightarrow> cxt"
where
"extend_with F \<Gamma>' =
  fmmap_keys (\<lambda>x _. case fmlookup F x of Some f \<Rightarrow> f (fmlookup \<Gamma>' x) | None \<Rightarrow> the (fmlookup \<Gamma>' x))
    (fmmap (\<lambda>_. ()) F \<otimes> fmmap (\<lambda>_. ()) \<Gamma>')"

definition extend_plain :: "cxt_entry \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry"
where
"extend_plain \<theta> \<theta>' = (case \<theta>' of None \<Rightarrow> \<theta> | Some \<theta>'' \<Rightarrow> \<theta>'')"

primrec extend_entry :: "cxt_entry \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry"
where
"extend_entry (Ty \<tau>) = extend_plain (Ty \<tau>)" |
"extend_entry (DU \<tau>) = extend_plain (DU \<tau>)" |
"extend_entry (PU \<tau>) = extend_plain (PU \<tau>)" |
"extend_entry Unbound = extend_plain Unbound" |
"extend_entry (ModStub q) =
  (\<lambda>\<theta>'. case \<theta>' of None \<Rightarrow> ModStub q | Some (ModChecked q' \<Gamma>) \<Rightarrow> ModChecked q' \<Gamma> | Some \<theta> \<Rightarrow> \<theta>)" |
"extend_entry (ModChecked q \<Gamma>) =
  (\<lambda>\<theta>'. case \<theta>' of
     None \<Rightarrow> ModChecked q \<Gamma>
   | Some (ModStub q') \<Rightarrow> if q = q' then ModChecked q \<Gamma> else ModStub q'
   | Some (ModChecked q' \<Gamma>') \<Rightarrow>
       if q = q' then ModChecked q (extend_with (fmmap extend_entry \<Gamma>) \<Gamma>') else ModChecked q' \<Gamma>'
   | Some \<theta> \<Rightarrow> \<theta>)" |
"extend_entry (Type C) = extend_plain (Type C)" |
"extend_entry TypeVar = extend_plain TypeVar" |
"extend_entry (Scheme \<pi>) = extend_plain (Scheme \<pi>)" |
"extend_entry (PUScheme \<pi>) = extend_plain (PUScheme \<pi>)" |
"extend_entry PredefName = extend_plain PredefName"

definition extend :: "cxt \<Rightarrow> cxt \<Rightarrow> cxt" (infixl "\<boxplus>" 65)
where
"\<Gamma> \<boxplus> \<Gamma>' = extend_with (fmmap extend_entry \<Gamma>) \<Gamma>'"

type_synonym module_table = "(name, module_body) fmap"

context includes fmap.lifting
begin

lift_definition submods :: "module_table \<Rightarrow> name \<Rightarrow> cxt"
  is "\<lambda>M q x. if snoc q x \<in> dom M then Some (ModStub (snoc q x)) else None"
proof -
  fix M :: "name \<Rightarrow> module_body option" and q
  assume "finite (dom M)"
  have "dom (\<lambda>x. if snoc q x \<in> dom M then Some (ModStub (snoc q x)) else None)
        \<subseteq> (\<lambda>q'. snd (the (unsnoc q'))) ` dom M"
    by (auto simp: dom_def image_iff intro: rev_image_eqI)
  then show "finite (dom (\<lambda>x. if snoc q x \<in> dom M then Some (ModStub (snoc q x)) else None))"
    using \<open>finite (dom M)\<close> by (blast intro: finite_subset finite_imageI)
qed

end

lemma map_of_submods:
  "map_of (map (\<lambda>(q', _). (snd (the (unsnoc q')), ModStub q'))
             (filter (\<lambda>(q', _). case unsnoc q' of Some (q'', _) \<Rightarrow> q'' = q | None \<Rightarrow> False) m)) x
   = (if snoc q x \<in> dom (map_of m) then Some (ModStub (snoc q x)) else None)"
proof (induction m)
  case Nil
  then show ?case by simp
next
  case (Cons e m)
  obtain q' b where e: "e = (q', b)" by (cases e)
  show ?case
  proof (cases "unsnoc q'")
    case None
    then have "snoc q x \<noteq> q'" by (metis unsnoc_snoc option.distinct(1))
    with Cons.IH e None show ?thesis by (simp add: dom_def)
  next
    case (Some p)
    obtain q'' x' where p: "p = (q'', x')" by (cases p)
    show ?thesis
    proof (cases "q'' = q")
      case True
      with Some p have q': "q' = snoc q x'" by (simp add: snoc_unsnoc)
      show ?thesis
      proof (cases "x = x'")
        case True
        with q' e Some p \<open>q'' = q\<close> show ?thesis by (simp add: dom_def)
      next
        case False
        with q' have "snoc q x \<noteq> q'" by (metis unsnoc_snoc option.inject prod.inject)
        with Cons.IH e Some p \<open>q'' = q\<close> False show ?thesis by (simp add: dom_def)
      qed
    next
      case False
      with Some p have "snoc q x \<noteq> q'" by (metis unsnoc_snoc option.inject prod.inject)
      with Cons.IH e Some p False show ?thesis by (simp add: dom_def)
    qed
  qed
qed

lemma submods_of_list [code]:
  "submods (fmap_of_list m) q
   = fmap_of_list (map (\<lambda>(q', _). (snd (the (unsnoc q')), ModStub q'))
                       (filter (\<lambda>(q', _). case unsnoc q' of Some (q'', _) \<Rightarrow> q'' = q | None \<Rightarrow> False) m))"
  by (rule fmap_ext) (simp add: submods.rep_eq fmlookup_of_list map_of_submods)

fun declares_imports :: "import list \<Rightarrow> var list"
where
"declares_imports [] = []" |
"declares_imports (Import (x, xs) # \<iota>s) =
  (if list_ex (\<lambda>\<iota>. case \<iota> of Import (x', _) \<Rightarrow> x' = x | _ \<Rightarrow> False) \<iota>s then declares_imports \<iota>s
   else x # declares_imports \<iota>s)" |
"declares_imports (FromImport q xs # \<iota>s) = xs @ declares_imports \<iota>s"

fun type_def_name :: "type_def \<Rightarrow> var"
where
"type_def_name (Dataclass c _ _ _) = c" |
"type_def_name (TypeAlias x _ _) = x"

fun declares_top :: "top_stmt \<Rightarrow> var list"
where
"declares_top (Stmt s) = declares s" |
"declares_top (TopSeq t t') = declares_top t @ declares_top t'" |
"declares_top (TypeDefs \<chi>s) = map type_def_name \<chi>s"

fun assigns_top :: "top_stmt \<Rightarrow> var set"
where
"assigns_top (Stmt s) = assigns s" |
"assigns_top (TopSeq t t') = assigns_top t \<union> assigns_top t'" |
"assigns_top (TypeDefs \<chi>s) = set (map type_def_name \<chi>s)"

fun binds_top :: "top_stmt \<Rightarrow> var set"
where
"binds_top (Stmt s) = binds s" |
"binds_top (TopSeq t t') = binds_top t \<union> binds_top t'" |
"binds_top (TypeDefs \<chi>s) = {}"

(* u marks a variable unbound, as for scope *)
definition scope_top :: "'a \<Rightarrow> var list \<Rightarrow> top_stmt \<Rightarrow> (var, 'a) fmap option"
where
"scope_top u ys t =
  (if distinct ys \<and> distinct (declares_top t) \<and> set ys \<inter> set (declares_top t) = {} \<and> set ys \<inter> binds_top t = {}
      \<and> set (declares_top t) \<inter> binds_top t = {}
   then Some (fmconst (assigns_top t - set ys) u)
   else None)"

fun check_top_stmt :: "cxt \<Rightarrow> top_stmt \<Rightarrow> static_outcome option"
where
"check_top_stmt \<Gamma> (Stmt s) = check_stmt \<Gamma> None s" |
"check_top_stmt \<Gamma> (TopSeq t t') =
  (case check_top_stmt \<Gamma> t of
     Some (Assigns\<^sub>R \<Delta>) \<Rightarrow> map_option (\<lambda>R. Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R R) (check_top_stmt (\<Gamma> \<otimes> \<Delta>) t')
   | _ \<Rightarrow> None)" |
"check_top_stmt \<Gamma> (TypeDefs \<chi>s) = None"

(* V holds the modules being checked, so that an import cycle has no derivation *)
function (sequential)
  check_module :: "module_table \<Rightarrow> name set \<Rightarrow> name \<Rightarrow> cxt option" and
  check_imports :: "module_table \<Rightarrow> name set \<Rightarrow> name \<Rightarrow> import list \<Rightarrow> cxt option" and
  submodules :: "module_table \<Rightarrow> name set \<Rightarrow> cxt_entry \<Rightarrow> var list \<Rightarrow> cxt_entry option" and
  imports_entry :: "module_table \<Rightarrow> name set \<Rightarrow> cxt \<Rightarrow> var \<Rightarrow> cxt_entry option" and
  imports_entries :: "module_table \<Rightarrow> name set \<Rightarrow> cxt \<Rightarrow> var list \<Rightarrow> cxt_entry list option" and
  check_modules :: "module_table \<Rightarrow> name set \<Rightarrow> name list \<Rightarrow> bool"
where
"check_module M V q =
  (case predefined q of
     Some \<Gamma> \<Rightarrow> Some \<Gamma>
   | None \<Rightarrow>
     if q \<in> V then None
     else case fmlookup M q of
       None \<Rightarrow> None
     | Some (ModuleBody \<iota>s t) \<Rightarrow>
       (case check_imports M (insert q V) q \<iota>s of
          None \<Rightarrow> None
        | Some \<Gamma>' \<Rightarrow>
          (case scope_top Unbound (declares_imports \<iota>s) t of
             None \<Rightarrow> None
           | Some \<Gamma>\<^sub>s \<Rightarrow>
             (case check_top_stmt (the (predefined builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t of
                Some (Assigns\<^sub>R \<Delta>) \<Rightarrow>
                  let S = submods M q in
                  if fmpred (\<lambda>x _. fmlookup S x = None) \<Gamma>' \<and> fmpred (\<lambda>x _. fmlookup S x = None) \<Delta>
                  then Some (S \<otimes> \<Delta>) else None
              | _ \<Rightarrow> None))))" |
"check_imports M V q [] = Some fmempty" |
"check_imports M V q (Import q' # \<iota>s) =
  (case q' of (x, xs) \<Rightarrow>
   if q \<prec> q' then None
   else case check_module M V (x, []) of
     None \<Rightarrow> None
   | Some \<Delta> \<Rightarrow>
     (case submodules M V (ModChecked (x, []) \<Delta>) xs of
        None \<Rightarrow> None
      | Some \<theta> \<Rightarrow> map_option (\<lambda>\<Gamma>. fmupd x \<theta> fmempty \<boxplus> \<Gamma>) (check_imports M V q \<iota>s)))" |
"check_imports M V q (FromImport q' xs # \<iota>s) =
  (if \<not> distinct xs then None
   else case check_module M V q' of
     None \<Rightarrow> None
   | Some \<Delta> \<Rightarrow>
     if \<not> check_modules M V (unique_to q' q) then None
     else case imports_entries M V \<Delta> xs of
       None \<Rightarrow> None
     | Some \<theta>s \<Rightarrow> map_option (\<lambda>\<Gamma>. fmap_of_list (zip xs \<theta>s) \<boxplus> \<Gamma>) (check_imports M V q \<iota>s))" |
"submodules M V \<theta> [] = Some \<theta>" |
"submodules M V (ModChecked q \<Gamma>) (x # xs) =
  (case check_module M V (snoc q x) of
     None \<Rightarrow> None
   | Some \<Gamma>' \<Rightarrow>
     map_option (\<lambda>\<theta>'. ModChecked q (\<Gamma> \<boxplus> fmupd x \<theta>' fmempty)) (submodules M V (ModChecked (snoc q x) \<Gamma>') xs))" |
"submodules M V _ _ = None" |
"imports_entry M V \<Gamma> x =
  (case fmlookup \<Gamma> x of
     Some (ModStub q) \<Rightarrow> map_option (ModChecked q) (check_module M V q)
   | _ \<Rightarrow> resolve_name \<Gamma> x)" |
"imports_entries M V \<Gamma> [] = Some []" |
"imports_entries M V \<Gamma> (x # xs) =
  (case imports_entry M V \<Gamma> x of
     None \<Rightarrow> None
   | Some \<theta> \<Rightarrow> map_option (\<lambda>\<theta>s. \<theta> # \<theta>s) (imports_entries M V \<Gamma> xs))" |
"check_modules M V [] = True" |
"check_modules M V (q # qs) = (check_module M V q \<noteq> None \<and> check_modules M V qs)"
by pat_completeness auto

lemma card_fmdom_insert:
  assumes "fmlookup M q = Some m" and "q \<notin> V"
  shows "card (fmdom' M - insert q V) < card (fmdom' M - V)"
proof -
  have "q \<in> fmdom' M - V" using assms by (simp add: fmlookup_dom'_iff)
  moreover have "fmdom' M - insert q V = (fmdom' M - V) - {q}" by auto
  ultimately show ?thesis by (metis card_Diff1_less finite_Diff finite_fmdom')
qed

(* Modules still to be checked, then the caller before the callee among the judgements at one V, then the
   list argument *)
termination
by (relation "measures [
     \<lambda>x. case x of
       Inl (Inl (M, V, _)) \<Rightarrow> card (fmdom' M - V)
     | Inl (Inr (Inl (M, V, _, _))) \<Rightarrow> card (fmdom' M - V)
     | Inl (Inr (Inr (M, V, _, _))) \<Rightarrow> card (fmdom' M - V)
     | Inr (Inl (M, V, _, _)) \<Rightarrow> card (fmdom' M - V)
     | Inr (Inr (Inl (M, V, _, _))) \<Rightarrow> card (fmdom' M - V)
     | Inr (Inr (Inr (M, V, _))) \<Rightarrow> card (fmdom' M - V),
     \<lambda>x. case x of
       Inl (Inl _) \<Rightarrow> 0
     | Inl (Inr (Inl _)) \<Rightarrow> 3
     | Inl (Inr (Inr _)) \<Rightarrow> 1
     | Inr (Inl _) \<Rightarrow> 1
     | Inr (Inr (Inl _)) \<Rightarrow> 2
     | Inr (Inr (Inr _)) \<Rightarrow> 1,
     \<lambda>x. case x of
       Inl (Inl _) \<Rightarrow> 0
     | Inl (Inr (Inl (_, _, _, \<iota>s))) \<Rightarrow> length \<iota>s
     | Inl (Inr (Inr (_, _, _, xs))) \<Rightarrow> length xs
     | Inr (Inl _) \<Rightarrow> 0
     | Inr (Inr (Inl (_, _, _, xs))) \<Rightarrow> length xs
     | Inr (Inr (Inr (_, _, qs))) \<Rightarrow> length qs]")
   (auto simp: card_fmdom_insert)

definition check_program :: "module_table \<Rightarrow> bool"
where
"check_program M = (check_module M {} main \<noteq> None)"

end
