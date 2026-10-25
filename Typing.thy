theory Typing
  imports Semantics "HOL-Library.Monad_Syntax" "HOL-Library.List_Lexorder" "HOL-Library.Char_ord"
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

(* Reasons for ill-formedness, refining the single failure of the typing rules *)
datatype reason =
    UndefinedVariable var
  | UnassignedVariable var
  | PossiblyUnassigned var
  | UnboundName var
  | Redeclaration var
  | UndeclaredAssignment var
  | AssignmentBeforeDeclaration var
  | Reassignment var
  | PossibleReassignment var
  | CapturedGeneratorVariable var
  | UnreachableStatement
  | NotPredefinedName var
  | NotClass name
  | DuplicateMember var name
  | SubmoduleNotImported name
  | UnassignedMember var name
  | TopLevelAssertFalse
  | UnknownModule name
  | DuplicateImportedName var
  | UnknownMember var name
  | ModuleAsValue name
  | ImportOfContainedModule name name
  | PredefinedNameAsValue name
  | TypeParameterAsValue var
  | TypeSchemeAsValue name
  | ClassAsValue name
  | NoBinaryOverload bop ty ty
  | NoUnaryOverload uop ty
  | NotCallable ty
  | KeywordArgumentsNotConstructor
  | CallArityMismatch nat nat
  | NoneResult
  | TypeMismatch ty ty
  | LambdaTypeMismatch ty "nat option"
  | NotSubscriptable ty
  | TupleIndexOutOfRange int nat
  | NotIterable ty
  | NotSynthesised
  | NoAttributes ty
  | BareReturn ty
  | MissingReturn var ty
  | ImportCycle "name list"
  | MypyCompatibility reason

fun lookup :: "cxt \<Rightarrow> name \<Rightarrow> cxt_entry option"
where
"lookup \<Gamma> (x, []) = fmlookup \<Gamma> x" |
"lookup \<Gamma> (x, y # ys) = (case fmlookup \<Gamma> x of Some (ModChecked _ \<Gamma>') \<Rightarrow> lookup \<Gamma>' (y, ys) | _ \<Rightarrow> None)"

fun resolve_name :: "cxt \<Rightarrow> name \<Rightarrow> cxt_entry option"
where
"resolve_name \<Gamma> q =
  (case lookup \<Gamma> q of
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

fun merges :: "(reason + static_outcome) list \<Rightarrow> reason + static_outcome"
where
"merges [] = Inr Returns\<^sub>R" |
"merges (m # ms) = do { R \<leftarrow> m; R' \<leftarrow> merges ms; Inr (R \<oplus>\<^sub>R R') }"

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

definition check_predefined :: "cxt \<Rightarrow> var \<Rightarrow> reason + unit"
where
"check_predefined \<Gamma> x = ensure (predef \<Gamma> x) (NotPredefinedName x)"

definition not_type_name :: "cxt \<Rightarrow> name \<Rightarrow> reason"
where
"not_type_name \<Gamma> q = (case lookup \<Gamma> q of Some Unbound \<Rightarrow> UnboundName (fst q) | _ \<Rightarrow> NotClass q)"

fun resolve_type :: "cxt \<Rightarrow> ty_expr \<Rightarrow> reason + ty"
where
"resolve_type \<Gamma> (TyExprPrim \<nu>) = do { check_predefined \<Gamma> (prim_name \<nu>); Inr (TyPrim \<nu>) }" |
"resolve_type \<Gamma> (TyExprName q \<psi>s) =
  (if snd q = [] \<and> \<psi>s = [] \<and> fmlookup \<Gamma> (fst q) = Some TypeVar then Inr (TyVar (fst q))
   else case resolve_name \<Gamma> q of
     Some (Type _) \<Rightarrow> undefined
   | _ \<Rightarrow> Inl (not_type_name \<Gamma> q))" |
"resolve_type \<Gamma> (TyExprLiteral l) = do { check_predefined \<Gamma> ''Literal''; Inr (TyLiteral l) }" |
"resolve_type \<Gamma> (TyExprList \<psi>) = do { check_predefined \<Gamma> ''list''; \<tau> \<leftarrow> resolve_type \<Gamma> \<psi>; Inr (TyList \<tau>) }" |
"resolve_type \<Gamma> (TyExprDict \<psi>) = do {
   check_predefined \<Gamma> ''dict''; check_predefined \<Gamma> ''str''; \<tau> \<leftarrow> resolve_type \<Gamma> \<psi>; Inr (TyDict \<tau>)
 }" |
"resolve_type \<Gamma> (TyExprTuple \<psi>s) = do {
   check_predefined \<Gamma> ''tuple''; \<tau>s \<leftarrow> those_sum (map (resolve_type \<Gamma>) \<psi>s); Inr (TyTuple \<tau>s)
 }" |
"resolve_type \<Gamma> (TyExprCallable \<psi>s \<psi>) = do {
   check_predefined \<Gamma> ''Callable'';
   \<sigma>s \<leftarrow> those_sum (map (resolve_type \<Gamma>) \<psi>s);
   \<tau> \<leftarrow> resolve_type \<Gamma> \<psi>;
   Inr (TyCallable \<sigma>s \<tau>)
 }" |
"resolve_type \<Gamma> (TyExprUnion \<psi> \<psi>') = do {
   \<sigma> \<leftarrow> resolve_type \<Gamma> \<psi>; \<tau> \<leftarrow> resolve_type \<Gamma> \<psi>'; Inr (TyUnion \<sigma> \<tau>)
 }"

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

(* Type of the elements of an iterable type; None otherwise *)
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

(* Type of a subscript, by the type of the subscripted value, the checks of the index against int and str,
   and the type synthesised by the index *)
fun subscript_type :: "ty \<Rightarrow> reason + unit \<Rightarrow> reason + unit \<Rightarrow> reason + ty \<Rightarrow> reason + ty"
where
"subscript_type (TyUnion \<sigma> \<sigma>') int_ok str_ok idx = do {
   \<tau> \<leftarrow> subscript_type \<sigma> int_ok str_ok idx; \<tau>' \<leftarrow> subscript_type \<sigma>' int_ok str_ok idx; Inr (\<tau> \<squnion> \<tau>')
 }" |
"subscript_type (TyList \<tau>) int_ok _ _ = do { int_ok; Inr \<tau> }" |
"subscript_type (TyDict \<tau>) _ str_ok _ = do { str_ok; Inr \<tau> }" |
"subscript_type (TyTuple \<tau>s) _ _ idx = do {
   \<iota> \<leftarrow> idx;
   case \<iota> of
     TyLiteral (LitInt n) \<Rightarrow>
       if 0 \<le> n \<and> n < of_nat (length \<tau>s) then Inr (\<tau>s ! nat n)
       else if n < 0 \<and> 0 \<le> of_nat (length \<tau>s) + n then Inr (\<tau>s ! nat (of_nat (length \<tau>s) + n))
       else Inl (TupleIndexOutOfRange n (length \<tau>s))
   | TyPrim int \<Rightarrow> Inr (joins \<tau>s)
   | _ \<Rightarrow> Inl (TypeMismatch (TyPrim int) \<iota>)
 }" |
"subscript_type \<sigma> int_ok _ _ =
  (if base_type \<sigma> = TyPrim str then do { int_ok; Inr (TyPrim str) } else Inl (NotSubscriptable \<sigma>))"

(* Qualified name of a variable or attribute *)
fun expr_name :: "expr \<Rightarrow> name option"
where
"expr_name (ExprVar x) = Some (x, [])" |
"expr_name (ExprAttribute e x) = map_option (\<lambda>q. snoc q x) (expr_name e)" |
"expr_name _ = None"

(* Failure for variable x, which isn't bound at a type, by its context entry *)
fun var_reason :: "var \<Rightarrow> cxt_entry option \<Rightarrow> reason"
where
"var_reason x (Some (ModStub _)) = ModuleAsValue (x, [])" |
"var_reason x (Some (ModChecked _ _)) = ModuleAsValue (x, [])" |
"var_reason x (Some (Type _)) = ClassAsValue (x, [])" |
"var_reason x (Some PredefName) = PredefinedNameAsValue (x, [])" |
"var_reason x (Some TypeVar) = TypeParameterAsValue x" |
"var_reason x (Some (Scheme _)) = TypeSchemeAsValue (x, [])" |
"var_reason x (Some Unbound) = UnboundName x" |
"var_reason x (Some (DU _)) = UnassignedVariable x" |
"var_reason x (Some (PU _)) = PossiblyUnassigned x" |
"var_reason x (Some (PUScheme _)) = PossiblyUnassigned x" |
"var_reason x (Some (Ty _)) = undefined" |
"var_reason x None = UndefinedVariable x"

(* Type of member x of module q, as attribute q' *)
definition member_type :: "name \<Rightarrow> cxt \<Rightarrow> var \<Rightarrow> name \<Rightarrow> reason + ty"
where
"member_type q \<Gamma> x q' =
  (case fmlookup \<Gamma> x of
     None \<Rightarrow> Inl (UnknownMember x q)
   | Some (Ty \<tau>) \<Rightarrow> Inr \<tau>
   | Some (ModStub q'') \<Rightarrow> Inl (SubmoduleNotImported q'')
   | Some (ModChecked _ _) \<Rightarrow> Inl (ModuleAsValue q')
   | Some (Type _) \<Rightarrow> Inl (ClassAsValue q')
   | Some PredefName \<Rightarrow> Inl (PredefinedNameAsValue q')
   | Some (Scheme _) \<Rightarrow> Inl (TypeSchemeAsValue q')
   | Some TypeVar \<Rightarrow> undefined
   | Some _ \<Rightarrow> Inl (UnassignedMember x q))"

(* Type of attribute x of a value of type \<sigma>, which isn't a module *)
fun attribute_type :: "ty \<Rightarrow> var \<Rightarrow> reason + ty"
where
"attribute_type (TyUnion \<sigma> \<sigma>') x = do { \<tau> \<leftarrow> attribute_type \<sigma> x; \<tau>' \<leftarrow> attribute_type \<sigma>' x; Inr (\<tau> \<squnion> \<tau>') }" |
"attribute_type (TyClass _ _) _ = undefined" |
"attribute_type \<sigma> _ = Inl (NoAttributes \<sigma>)"

(* Reason why none of the elements of a list or dictionary synthesises a type: the first failure of an
   element with a synthesis rule *)
fun synth_failure :: "(reason + 'a) list \<Rightarrow> reason"
where
"synth_failure [] = NotSynthesised" |
"synth_failure (Inl NotSynthesised # ms) = synth_failure ms" |
"synth_failure (Inl r # ms) = r" |
"synth_failure (Inr _ # ms) = synth_failure ms"

(* Failure if one of the variables bound by qualifiers with bindings \<Delta> is in X, the variables captured by
   lambdas *)
definition captured :: "var set \<Rightarrow> cxt \<Rightarrow> reason + unit"
where
"captured X \<Delta> =
  (let Y = X \<inter> fset (fmdom \<Delta>) in if Y = {} then Inr () else Inl (CapturedGeneratorVariable (Min Y)))"

function (sequential)
  synth_expr :: "cxt \<Rightarrow> expr \<Rightarrow> reason + ty" and
  synth_exprs :: "cxt \<Rightarrow> expr list \<Rightarrow> (reason + ty) list" and
  check_expr :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> reason + unit" and
  check_expr' :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> (reason + unit) option" and
  check_exprs :: "cxt \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> reason + unit" and
  quals :: "cxt \<Rightarrow> qualifier list \<Rightarrow> reason + cxt"
where
"synth_expr \<Gamma> (ExprVar x) = (case fmlookup \<Gamma> x of Some (Ty \<tau>) \<Rightarrow> Inr \<tau> | \<theta> \<Rightarrow> Inl (var_reason x \<theta>))" |
"synth_expr \<Gamma> (ExprLiteral l) = Inr (case l of LitFloat _ \<Rightarrow> TyPrim float | _ \<Rightarrow> TyLiteral l)" |
"synth_expr \<Gamma> (ExprCall e (es, kws)) =
  (case e of
     ExprLambda xs e' \<Rightarrow> do {
       ensure (kws = []) KeywordArgumentsNotConstructor;
       ensure (length xs = length es) (CallArityMismatch (length xs) (length es));
       \<tau>s \<leftarrow> those_sum (synth_exprs \<Gamma> es);
       if distinct xs then synth_expr (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e' else Inl undefined
     }
   | _ \<Rightarrow> do {
       \<sigma> \<leftarrow> synth_expr \<Gamma> e;
       case \<sigma> of
         TyCallable \<sigma>s \<tau> \<Rightarrow> do {
           ensure (kws = []) KeywordArgumentsNotConstructor;
           ensure (length \<sigma>s = length es) (CallArityMismatch (length \<sigma>s) (length es));
           check_exprs \<Gamma> es \<sigma>s;
           ensure (\<tau> \<noteq> TyPrim NoneType) (MypyCompatibility NoneResult);
           Inr \<tau>
         }
       | _ \<Rightarrow> Inl (NotCallable \<sigma>)
     })" |
"synth_expr \<Gamma> (ExprBinOp op e e') = do {
   \<sigma> \<leftarrow> synth_expr \<Gamma> e;
   \<sigma>' \<leftarrow> synth_expr \<Gamma> e';
   case resolve_binop op \<sigma> \<sigma>' of Some \<tau> \<Rightarrow> Inr \<tau> | None \<Rightarrow> Inl (NoBinaryOverload op \<sigma> \<sigma>')
 }" |
"synth_expr \<Gamma> (ExprUnOp op e) =
  (if op = UOpNeg \<and> numeric_literal e then Inl undefined
   else do {
     \<sigma> \<leftarrow> synth_expr \<Gamma> e;
     case resolve_unop op \<sigma> of Some \<tau> \<Rightarrow> Inr \<tau> | None \<Rightarrow> Inl (NoUnaryOverload op \<sigma>)
   })" |
"synth_expr \<Gamma> (ExprAnd e e') =
  do { check_expr \<Gamma> e (TyPrim bool); check_expr \<Gamma> e' (TyPrim bool); Inr (TyPrim bool) }" |
"synth_expr \<Gamma> (ExprOr e e') =
  do { check_expr \<Gamma> e (TyPrim bool); check_expr \<Gamma> e' (TyPrim bool); Inr (TyPrim bool) }" |
"synth_expr \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) = do {
   check_expr \<Gamma> e (TyPrim bool);
   case (synth_expr \<Gamma> e\<^sub>1, synth_expr \<Gamma> e\<^sub>2) of
     (Inr \<sigma>\<^sub>1, Inr \<sigma>\<^sub>2) \<Rightarrow> Inr (\<sigma>\<^sub>1 \<squnion> \<sigma>\<^sub>2)
   | (Inr \<sigma>\<^sub>1, Inl _) \<Rightarrow> do { check_expr \<Gamma> e\<^sub>2 \<sigma>\<^sub>1; Inr \<sigma>\<^sub>1 }
   | (Inl _, Inr \<sigma>\<^sub>2) \<Rightarrow> do { check_expr \<Gamma> e\<^sub>1 \<sigma>\<^sub>2; Inr \<sigma>\<^sub>2 }
   | (r\<^sub>1, r\<^sub>2) \<Rightarrow> Inl (synth_failure [r\<^sub>1, r\<^sub>2])
 }" |
"synth_expr \<Gamma> (ExprList es) =
  (let \<sigma>s = synth_exprs \<Gamma> es; \<tau> = joins (map (base_type \<circ> projr) (filter (Not \<circ> isl) \<sigma>s)) in
   if \<not> list_all isl \<sigma>s then do {
     those_sum (map (\<lambda>j. check_expr \<Gamma> (es ! j) \<tau>) (filter (\<lambda>j. isl (\<sigma>s ! j)) [0..<length es]));
     Inr (TyList \<tau>)
   }
   else Inl (synth_failure \<sigma>s))" |
"synth_expr \<Gamma> (ExprTuple es) = do { \<tau>s \<leftarrow> those_sum (synth_exprs \<Gamma> es); Inr (TyTuple \<tau>s) }" |
"synth_expr \<Gamma> (ExprAttribute e x) =
  (case expr_name e of
     Some q \<Rightarrow>
       (case (resolve_name \<Gamma> q, lookup \<Gamma> q) of
          (Some (ModChecked q' \<Gamma>'), _) \<Rightarrow> member_type q' \<Gamma>' x (snoc q x)
        | (_, Some (ModStub q')) \<Rightarrow> Inl (SubmoduleNotImported q')
        | _ \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Gamma> e; attribute_type \<sigma> x })
   | None \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Gamma> e; attribute_type \<sigma> x })" |
"synth_expr \<Gamma> (ExprSubscript e e') = do {
   \<sigma> \<leftarrow> synth_expr \<Gamma> e;
   subscript_type \<sigma> (check_expr \<Gamma> e' (TyPrim int)) (check_expr \<Gamma> e' (TyPrim str)) (synth_expr \<Gamma> e')
 }" |
"synth_expr \<Gamma> (ExprDict kvs) =
  (let \<sigma>s = synth_exprs \<Gamma> (map snd kvs); \<tau> = joins (map (base_type \<circ> projr) (filter (Not \<circ> isl) \<sigma>s)) in do {
     check_exprs \<Gamma> (map fst kvs) (replicate (length kvs) (TyPrim str));
     if \<not> list_all isl \<sigma>s then do {
       those_sum (map (\<lambda>j. check_expr \<Gamma> (snd (kvs ! j)) \<tau>) (filter (\<lambda>j. isl (\<sigma>s ! j)) [0..<length kvs]));
       Inr (TyDict \<tau>)
     }
     else Inl (synth_failure \<sigma>s)
   })" |
"synth_expr \<Gamma> (ExprListComp e gs) = do {
   \<Delta> \<leftarrow> quals \<Gamma> gs;
   captured (captures e) \<Delta>;
   \<tau> \<leftarrow> synth_expr (\<Gamma> \<otimes> \<Delta>) e;
   Inr (TyList (base_type \<tau>))
 }" |
"synth_expr \<Gamma> (ExprDictComp e e' gs) = do {
   \<Delta> \<leftarrow> quals \<Gamma> gs;
   captured (captures e \<union> captures e') \<Delta>;
   check_expr (\<Gamma> \<otimes> \<Delta>) e (TyPrim str);
   \<tau> \<leftarrow> synth_expr (\<Gamma> \<otimes> \<Delta>) e';
   Inr (TyDict (base_type \<tau>))
 }" |
"synth_expr \<Gamma> _ = Inl NotSynthesised" |

"synth_exprs \<Gamma> [] = []" |
"synth_exprs \<Gamma> (e # es) = synth_expr \<Gamma> e # synth_exprs \<Gamma> es" |

"check_expr \<Gamma> e \<tau> =
  (case check_expr' \<Gamma> e \<tau> of
     Some (Inr ()) \<Rightarrow> Inr ()
   | Some (Inl r) \<Rightarrow> (case synth_expr \<Gamma> e of Inr \<sigma> \<Rightarrow> if \<sigma> <: \<tau> then Inr () else Inl r | Inl _ \<Rightarrow> Inl r)
   | None \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Gamma> e; ensure (\<sigma> <: \<tau>) (TypeMismatch \<tau> \<sigma>) })" |

"check_expr' \<Gamma> (ExprLambda xs e) \<tau> =
  Some (case \<tau> of
     TyCallable \<tau>s \<tau>' \<Rightarrow>
       if length xs \<noteq> length \<tau>s then Inl (LambdaTypeMismatch \<tau> (Some (length xs)))
       else if distinct xs then check_expr (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e \<tau>' else Inl undefined
   | _ \<Rightarrow> Inl (LambdaTypeMismatch \<tau> None))" |
"check_expr' \<Gamma> (ExprCall e (es, kws)) \<tau> =
  (case e of
     ExprLambda xs e' \<Rightarrow> Some (do {
       ensure (kws = []) KeywordArgumentsNotConstructor;
       ensure (length xs = length es) (CallArityMismatch (length xs) (length es));
       \<tau>s \<leftarrow> those_sum (synth_exprs \<Gamma> es);
       if distinct xs then check_expr (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e' \<tau> else Inl undefined
     })
   | _ \<Rightarrow> None)" |
"check_expr' \<Gamma> (ExprList es) \<tau> =
  (case \<tau> of TyList \<tau>' \<Rightarrow> Some (check_exprs \<Gamma> es (replicate (length es) \<tau>')) | _ \<Rightarrow> None)" |
"check_expr' \<Gamma> (ExprTuple es) \<tau> =
  (case \<tau> of TyTuple \<tau>s \<Rightarrow> if length es = length \<tau>s then Some (check_exprs \<Gamma> es \<tau>s) else None | _ \<Rightarrow> None)" |
"check_expr' \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) \<tau> =
  Some (do { check_expr \<Gamma> e (TyPrim bool); check_expr \<Gamma> e\<^sub>1 \<tau>; check_expr \<Gamma> e\<^sub>2 \<tau> })" |
"check_expr' \<Gamma> (ExprDict kvs) \<tau> =
  (case \<tau> of
     TyDict \<tau>' \<Rightarrow> Some (do {
       check_exprs \<Gamma> (map fst kvs) (replicate (length kvs) (TyPrim str));
       check_exprs \<Gamma> (map snd kvs) (replicate (length kvs) \<tau>')
     })
   | _ \<Rightarrow> None)" |
"check_expr' \<Gamma> (ExprListComp e gs) \<tau> =
  (case \<tau> of
     TyList \<tau>' \<Rightarrow> Some (do { \<Delta> \<leftarrow> quals \<Gamma> gs; captured (captures e) \<Delta>; check_expr (\<Gamma> \<otimes> \<Delta>) e \<tau>' })
   | _ \<Rightarrow> None)" |
"check_expr' \<Gamma> (ExprDictComp e e' gs) \<tau> =
  (case \<tau> of
     TyDict \<tau>' \<Rightarrow> Some (do {
       \<Delta> \<leftarrow> quals \<Gamma> gs;
       captured (captures e \<union> captures e') \<Delta>;
       check_expr (\<Gamma> \<otimes> \<Delta>) e (TyPrim str);
       check_expr (\<Gamma> \<otimes> \<Delta>) e' \<tau>'
     })
   | _ \<Rightarrow> None)" |
"check_expr' \<Gamma> _ _ = None" |

"check_exprs \<Gamma> [] [] = Inr ()" |
"check_exprs \<Gamma> (e # es) (\<tau> # \<tau>s) = do { check_expr \<Gamma> e \<tau>; check_exprs \<Gamma> es \<tau>s }" |
"check_exprs \<Gamma> _ _ = undefined" |

"quals \<Gamma> [] = Inr fmempty" |
"quals \<Gamma> (Guard e # gs) = do { check_expr \<Gamma> e (TyPrim bool); quals \<Gamma> gs }" |
"quals \<Gamma> (Generator x e # gs) = do {
   \<sigma> \<leftarrow> synth_expr \<Gamma> e;
   \<tau> \<leftarrow> (case elem_type \<sigma> of Some \<tau> \<Rightarrow> Inr \<tau> | None \<Rightarrow> Inl (NotIterable \<sigma>));
   ensure (x \<notin> captures gs) (CapturedGeneratorVariable x);
   \<Delta> \<leftarrow> quals (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs;
   Inr (fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)
 }"
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

(* Context entry for a type scheme, which is a plain type when its parameter list is empty *)
fun signature_entry :: "ty_scheme \<Rightarrow> cxt_entry"
where
"signature_entry (TyScheme [] \<tau>) = Ty \<tau>" |
"signature_entry \<pi> = Scheme \<pi>"

fun def_signature :: "cxt \<Rightarrow> func \<Rightarrow> reason + ty_scheme"
where
"def_signature \<Gamma> (Def f \<alpha>s xps \<psi> s) =
   (let \<Gamma>' = \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar in do {
      \<sigma>s \<leftarrow> those_sum (map (resolve_type \<Gamma>' \<circ> snd) xps);
      \<tau> \<leftarrow> resolve_type \<Gamma>' \<psi>;
      Inr (TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>))
    })"

abbreviation false_lit :: expr where "false_lit \<equiv> ExprLiteral (LitBool False)"

(* Failure for an assignment to x, by its context entry, which isn't a declaration *)
fun assign_reason :: "var \<Rightarrow> cxt_entry option \<Rightarrow> reason"
where
"assign_reason x None = UndeclaredAssignment x" |
"assign_reason x (Some (PU _)) = PossibleReassignment x" |
"assign_reason x (Some (PUScheme _)) = PossibleReassignment x" |
"assign_reason x (Some Unbound) = AssignmentBeforeDeclaration x" |
"assign_reason x (Some (Ty _)) = Reassignment x" |
"assign_reason x (Some (Scheme _)) = Reassignment x" |
"assign_reason x (Some (DU _)) = undefined" |
"assign_reason x _ = Redeclaration x"

(* Failure r, required only for compatibility with mypy if b *)
definition mypy_only_if :: "bool \<Rightarrow> reason \<Rightarrow> reason"
where
"mypy_only_if b r = (if b then MypyCompatibility r else r)"

(* First of xs in S or occurring earlier in xs *)
fun redeclared :: "var set \<Rightarrow> var list \<Rightarrow> var option"
where
"redeclared S [] = None" |
"redeclared S (x # xs) = (if x \<in> S then Some x else redeclared (insert x S) xs)"

(* Failure of the scope with bound names ys, declared names xs and pattern variables B *)
definition scope_reason :: "var list \<Rightarrow> var list \<Rightarrow> var set \<Rightarrow> reason"
where
"scope_reason ys xs B =
  (case redeclared {} ys of
     Some y \<Rightarrow> DuplicateImportedName y
   | None \<Rightarrow>
       (case redeclared (set ys \<union> B) xs of
          Some x \<Rightarrow> Redeclaration x
        | None \<Rightarrow> Redeclaration (Min (set ys \<inter> B))))"

(* Targets of plain assignments, in order *)
fun assign_targets :: "stmt \<Rightarrow> var list"
where
"assign_targets (StmtAssign x None _) = [x]" |
"assign_targets (StmtSeq s s') = assign_targets s @ assign_targets s'" |
"assign_targets (StmtIf _ s elifs else') =
  assign_targets s @ concat (map (\<lambda>(_, s'). assign_targets s') elifs)
  @ (case else' of None \<Rightarrow> [] | Some s' \<Rightarrow> assign_targets s')" |
"assign_targets (StmtMatch _ cases) = concat (map (\<lambda>(_, s). assign_targets s) cases)" |
"assign_targets _ = []"

fun assign_targets_top :: "top_stmt \<Rightarrow> var list"
where
"assign_targets_top (Stmt s) = assign_targets s" |
"assign_targets_top (TopSeq t t') = assign_targets_top t @ assign_targets_top t'" |
"assign_targets_top (TypeDefs _) = []"

(* Failure for the first assignment target of xs which isn't in ys, declared or a pattern variable of B *)
definition check_assignments_declared :: "var set \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> var set \<Rightarrow> reason + unit"
where
"check_assignments_declared ys xs ds B =
  (case find (\<lambda>x. x \<notin> ys \<and> x \<notin> set ds \<and> x \<notin> B) xs of
     Some x \<Rightarrow> Inl (UndeclaredAssignment x)
   | None \<Rightarrow> Inr ())"

fun check_stmt :: "cxt \<Rightarrow> ty option \<Rightarrow> stmt \<Rightarrow> reason + static_outcome"
and check_elifs :: "cxt \<Rightarrow> ty option \<Rightarrow> (expr \<times> stmt) list \<Rightarrow> (reason + static_outcome) list"
and check_defs :: "cxt \<Rightarrow> func list \<Rightarrow> ty_scheme list \<Rightarrow> reason + unit"
and check_def :: "cxt \<Rightarrow> func \<Rightarrow> ty_scheme \<Rightarrow> reason + unit"
where
"check_stmt \<Gamma> \<zeta> StmtPass = Inr (Assigns\<^sub>R fmempty)" |
"check_stmt \<Gamma> \<zeta> (StmtDeclare x \<psi>) = do { \<tau> \<leftarrow> resolve_type \<Gamma> \<psi>; Inr (Assigns\<^sub>R (fmupd x (DU \<tau>) fmempty)) }" |
"check_stmt \<Gamma> \<zeta> (StmtAssign x None e) =
  (case fmlookup \<Gamma> x of
     Some (DU \<tau>) \<Rightarrow> do { check_expr \<Gamma> e \<tau>; Inr (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty)) }
   | \<theta> \<Rightarrow> Inl (assign_reason x \<theta>))" |
"check_stmt \<Gamma> \<zeta> (StmtAssign x (Some \<psi>) e) = do {
   \<tau> \<leftarrow> resolve_type \<Gamma> \<psi>; check_expr \<Gamma> e \<tau>; Inr (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty))
 }" |
"check_stmt \<Gamma> \<zeta> (StmtExpr e) =
  (case synth_expr \<Gamma> e of
     Inr _ \<Rightarrow> Inr (Assigns\<^sub>R fmempty)
   | Inl r \<Rightarrow>
       (case e of
          ExprCall e' (es, kws) \<Rightarrow>
            (case synth_expr \<Gamma> e' of
               Inr (TyCallable \<sigma>s (TyPrim NoneType)) \<Rightarrow> do {
                 ensure (kws = []) KeywordArgumentsNotConstructor;
                 ensure (length \<sigma>s = length es) (CallArityMismatch (length \<sigma>s) (length es));
                 check_exprs \<Gamma> es \<sigma>s;
                 Inr (Assigns\<^sub>R fmempty)
               }
             | _ \<Rightarrow> Inl r)
        | _ \<Rightarrow> Inl r))" |
"check_stmt \<Gamma> \<zeta> (StmtAssert e e') = do {
   (if e = false_lit then Inr () else check_expr \<Gamma> e (TyPrim bool));
   (case e' of Some e'' \<Rightarrow> check_expr \<Gamma> e'' (TyPrim str) | None \<Rightarrow> Inr ());
   Inr (if e = false_lit then Returns\<^sub>R else Assigns\<^sub>R fmempty)
 }" |
"check_stmt \<Gamma> \<zeta> (StmtReturn None) =
  (case \<zeta> of
     Some \<tau> \<Rightarrow>
       if \<tau> \<approx> TyPrim NoneType then Inr Returns\<^sub>R
       else Inl (mypy_only_if (TyPrim NoneType <: \<tau>) (BareReturn \<tau>))
   | None \<Rightarrow> undefined)" |
"check_stmt \<Gamma> \<zeta> (StmtReturn (Some e)) =
  (case \<zeta> of Some \<tau> \<Rightarrow> do { check_expr \<Gamma> e \<tau>; Inr Returns\<^sub>R } | None \<Rightarrow> undefined)" |
"check_stmt \<Gamma> \<zeta> (StmtIf e s elifs else') = do {
   check_expr \<Gamma> e (TyPrim bool);
   merges (check_stmt \<Gamma> \<zeta> s # check_elifs \<Gamma> \<zeta> elifs
           @ [case else' of Some s' \<Rightarrow> check_stmt \<Gamma> \<zeta> s' | None \<Rightarrow> Inr (Assigns\<^sub>R fmempty)])
 }" |
"check_stmt \<Gamma> \<zeta> (StmtSeq s s') = do {
   R \<leftarrow> check_stmt \<Gamma> \<zeta> s;
   case R of
     Assigns\<^sub>R \<Delta> \<Rightarrow> do { R' \<leftarrow> check_stmt (\<Gamma> \<otimes> \<Delta>) \<zeta> s'; Inr (Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R R') }
   | Returns\<^sub>R \<Rightarrow> Inl UnreachableStatement
 }" |
"check_stmt \<Gamma> \<zeta> (StmtMutualRegion ds) = do {
   \<pi>s \<leftarrow> those_sum (map (def_signature \<Gamma>) ds);
   let \<Delta> = fmap_of_list (zip (map def_name ds) (map signature_entry \<pi>s));
   check_defs (\<Gamma> \<otimes> \<Delta>) ds \<pi>s;
   Inr (Assigns\<^sub>R \<Delta>)
 }" |
"check_stmt \<Gamma> \<zeta> (StmtMatch e bs) = undefined" |

"check_elifs \<Gamma> \<zeta> [] = []" |
"check_elifs \<Gamma> \<zeta> ((e, s) # elifs) =
  (do { check_expr \<Gamma> e (TyPrim bool); check_stmt \<Gamma> \<zeta> s }) # check_elifs \<Gamma> \<zeta> elifs" |

"check_defs \<Gamma> [] [] = Inr ()" |
"check_defs \<Gamma> (d # ds) (\<pi> # \<pi>s) = do { check_def \<Gamma> d \<pi>; check_defs \<Gamma> ds \<pi>s }" |
"check_defs \<Gamma> _ _ = undefined" |

"check_def \<Gamma> (Def f \<alpha>s xps \<psi> s) (TyScheme \<alpha>s' (TyCallable \<sigma>s \<tau>)) =
  (let xs = map fst xps in do {
     check_assignments_declared (set xs) (assign_targets s) (declares s) (binds s);
     \<Delta> \<leftarrow> (case scope Unbound xs s of Some \<Delta> \<Rightarrow> Inr \<Delta> | None \<Rightarrow> Inl (scope_reason xs (declares s) (binds s)));
     if length xs = length \<sigma>s then do {
       R \<leftarrow> check_stmt (\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> fmap_of_list (zip xs (map Ty \<sigma>s)) \<otimes> \<Delta>) (Some \<tau>) s;
       if R = Returns\<^sub>R \<or> \<tau> \<approx> TyPrim NoneType then Inr ()
       else Inl (mypy_only_if (TyPrim NoneType <: \<tau>) (MissingReturn f \<tau>))
     }
     else Inl undefined
   })" |
"check_def \<Gamma> _ _ = undefined"

abbreviation name_binding :: "var \<times> cxt_entry" where "name_binding \<equiv> (''__name__'', Ty (TyPrim str))"

definition predefined :: "(name, cxt) fmap"
where
"predefined = fmap_of_list
  [(builtins, fmap_of_list
     ([name_binding,
       (''print'', Ty (TyCallable [TyPrim object] (TyPrim NoneType))),
       (''len'', Ty (TyCallable [TyPrim Sized] (TyPrim int))),
       (''range'', Type (snoc builtins ''range'')),
       (''round'', Ty (TyCallable [TyPrim float] (TyPrim int)))]
      @ map (\<lambda>\<nu>. (prim_name \<nu>, PredefName)) [NoneType, object, bool, int, float, str]
      @ [(''list'', PredefName), (''dict'', PredefName), (''tuple'', PredefName)])),
   ((''sys'', []), fmap_of_list
     [name_binding, (''argv'', Ty (TyList (TyPrim str))),
      (''exit'', Ty (TyCallable [TyPrim int] (TyPrim Never)))]),
   ((''typing'', []), fmap_of_list
     [name_binding, (''Callable'', PredefName), (''Literal'', PredefName),
      (prim_name Never, PredefName), (prim_name Sized, PredefName)]),
   ((''dataclasses'', []), fmap_of_list [name_binding, (''dataclass'', PredefName)])]"

(* Boxed plus of the specification isn't in Isabelle's symbol table *)
function (sequential) extend_entry :: "cxt_entry \<Rightarrow> cxt_entry \<Rightarrow> cxt_entry"
and extend :: "cxt \<Rightarrow> cxt \<Rightarrow> cxt" (infixl "\<uplus>" 65)
where
"extend_entry (ModChecked q \<Gamma>) (ModStub q') = (if q = q' then ModChecked q \<Gamma> else ModStub q')" |
"extend_entry (ModChecked q \<Gamma>) (ModChecked q' \<Gamma>') =
   (if q = q' then ModChecked q (\<Gamma> \<uplus> \<Gamma>') else ModChecked q' \<Gamma>')" |
"extend_entry _ \<theta>' = \<theta>'" |
"\<Gamma> \<uplus> \<Gamma>' =
   \<Gamma> ++\<^sub>f fmmap_keys (\<lambda>x \<theta>'. case fmlookup \<Gamma> x of None \<Rightarrow> \<theta>' | Some \<theta> \<Rightarrow> extend_entry \<theta> \<theta>') \<Gamma>'"
  by pat_completeness auto

termination
  by (relation "measure (\<lambda>p. case p of Inl (\<theta>, _) \<Rightarrow> size \<theta> | Inr (\<Gamma>, _) \<Rightarrow> size_fmap (\<lambda>_. 0) size \<Gamma>)")
     (simp_all add: size_fmap_lookup del: size_fmap_def)

type_synonym program = "(name, module_body) fmap"

context includes fmap.lifting
begin

lift_definition submods :: "program \<Rightarrow> name \<Rightarrow> cxt"
  is "\<lambda>M q x. if snoc q x \<in> dom M then Some (ModStub (snoc q x)) else None"
proof -
  fix M :: "name \<Rightarrow> module_body option" and q
  let ?S = "\<lambda>x. if snoc q x \<in> dom M then Some (ModStub (snoc q x)) else None"
  assume "finite (dom M)"
  have "dom ?S \<subseteq> (\<lambda>q'. snd (the (unsnoc q'))) ` dom M"
    by (auto simp: dom_def image_iff intro: rev_image_eqI)
  then show "finite (dom ?S)"
    using \<open>finite (dom M)\<close> by (blast intro: finite_subset finite_imageI)
qed

end

lemma submods_of_list [code]:
  "submods (fmap_of_list m) q
   = fmap_of_list (map (\<lambda>(q', _). (snd (the (unsnoc q')), ModStub q'))
                       (filter (\<lambda>(q', _). case unsnoc q' of Some (q'', _) \<Rightarrow> q'' = q | None \<Rightarrow> False) m))"
proof (rule fmap_ext)
  fix x
  let ?l = "map (\<lambda>(q', _). (snd (the (unsnoc q')), ModStub q'))
              (filter (\<lambda>(q', _). case unsnoc q' of Some (q'', _) \<Rightarrow> q'' = q | None \<Rightarrow> False) m)"
  have "map_of ?l x = (if snoc q x \<in> dom (map_of m) then Some (ModStub (snoc q x)) else None)"
    by (induction m) (auto simp: dom_def snoc_eq_iff simp del: snoc.simps unsnoc.simps split: option.splits)
  then show "fmlookup (submods (fmap_of_list m) q) x = fmlookup (fmap_of_list ?l) x"
    by (simp add: submods.rep_eq fmlookup_of_list)
qed

fun check_top_stmt :: "cxt \<Rightarrow> top_stmt \<Rightarrow> reason + static_outcome"
where
"check_top_stmt \<Gamma> (Stmt s) = check_stmt \<Gamma> None s" |
"check_top_stmt \<Gamma> (TopSeq t t') = do {
   R \<leftarrow> check_top_stmt \<Gamma> t;
   case R of
     Assigns\<^sub>R \<Delta> \<Rightarrow> do { R' \<leftarrow> check_top_stmt (\<Gamma> \<otimes> \<Delta>) t'; Inr (Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R R') }
   | Returns\<^sub>R \<Rightarrow> Inl TopLevelAssertFalse
 }" |
"check_top_stmt \<Gamma> (TypeDefs \<chi>s) = undefined"

definition known_module :: "program \<Rightarrow> name \<Rightarrow> bool"
where
"known_module M q = (q |\<in>| fmdom M \<or> q |\<in>| fmdom predefined)"

(* V holds the modules being checked, in order, so that an import cycle is rejected; a failure is paired
   with the module in which it occurs *)
function (sequential)
  check_module :: "program \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> (name \<times> reason) + cxt" and
  check_imports :: "program \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> import list \<Rightarrow> (name \<times> reason) + cxt" and
  submodules :: "program \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> cxt_entry \<Rightarrow> var list \<Rightarrow> (name \<times> reason) + cxt_entry" and
  imports_entry :: "program \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> name \<Rightarrow> cxt \<Rightarrow> var \<Rightarrow> (name \<times> reason) + cxt_entry" and
  imports_entries ::
    "program \<Rightarrow> name list \<Rightarrow> name \<Rightarrow> name \<Rightarrow> cxt \<Rightarrow> var list \<Rightarrow> (name \<times> reason) + cxt_entry list" and
  check_modules :: "program \<Rightarrow> name list \<Rightarrow> name list \<Rightarrow> (name \<times> reason) + unit"
where
"check_module M V q =
  (case fmlookup predefined q of
     Some \<Gamma> \<Rightarrow> Inr \<Gamma>
   | None \<Rightarrow>
     if q \<in> set V then Inl (q, ImportCycle (dropWhile (\<lambda>q'. q' \<noteq> q) V @ [q]))
     else case fmlookup M q of
       None \<Rightarrow> undefined
     | Some (ModuleBody \<iota>s t) \<Rightarrow> do {
         \<Gamma>' \<leftarrow> check_imports M (V @ [q]) q \<iota>s;
         \<Gamma>\<^sub>s \<leftarrow> map_sum (Pair q) id
           (case scope Unbound (declares \<iota>s) t of
              Some \<Gamma>\<^sub>s \<Rightarrow> Inr \<Gamma>\<^sub>s
            | None \<Rightarrow> Inl (scope_reason (declares \<iota>s) (declares t) (binds t)));
         map_sum (Pair q) id (check_assignments_declared {} (assign_targets_top t) (declares t) (binds t));
         R \<leftarrow> map_sum (Pair q) id (check_top_stmt (the (fmlookup predefined builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t);
         case R of
           Assigns\<^sub>R \<Delta> \<Rightarrow>
             let S = submods M q; X = (fmdom \<Gamma>' |\<union>| fmdom \<Delta>) |\<inter>| fmdom S in
             if X = {||} then Inr (S \<otimes> \<Delta>) else Inl (q, DuplicateMember (Min (fset X)) q)
         | Returns\<^sub>R \<Rightarrow> Inl (q, TopLevelAssertFalse)
       })" |
"check_imports M V q [] = Inr fmempty" |
"check_imports M V q (Import (x, xs) # \<iota>s) = do {
   ensure (\<not> q \<prec> (x, xs)) (q, ImportOfContainedModule (x, xs) q);
   ensure (known_module M (x, [])) (q, UnknownModule (x, []));
   \<Delta> \<leftarrow> check_module M V (x, []);
   \<theta> \<leftarrow> submodules M V q (ModChecked (x, []) \<Delta>) xs;
   \<Gamma> \<leftarrow> check_imports M V q \<iota>s;
   Inr (fmupd x \<theta> fmempty \<uplus> \<Gamma>)
 }" |
"check_imports M V q (FromImport q' xs # \<iota>s) = do {
   ensure (known_module M q') (q, UnknownModule q');
   \<Delta> \<leftarrow> check_module M V q';
   check_modules M V (unique_to q' q);
   (case redeclared {} xs of Some x \<Rightarrow> Inl (q, DuplicateImportedName x) | None \<Rightarrow> Inr ());
   \<theta>s \<leftarrow> imports_entries M V q q' \<Delta> xs;
   \<Gamma> \<leftarrow> check_imports M V q \<iota>s;
   Inr (fmap_of_list (zip xs \<theta>s) \<uplus> \<Gamma>)
 }" |
"submodules M V q \<theta> [] = Inr \<theta>" |
"submodules M V q (ModChecked q' \<Gamma>) (x # xs) = do {
   ensure (known_module M (snoc q' x)) (q, UnknownModule (snoc q' x));
   \<Gamma>' \<leftarrow> check_module M V (snoc q' x);
   \<theta>' \<leftarrow> submodules M V q (ModChecked (snoc q' x) \<Gamma>') xs;
   Inr (ModChecked q' (\<Gamma> \<uplus> fmupd x \<theta>' fmempty))
 }" |
"submodules M V q _ _ = undefined" |
"imports_entry M V q q' \<Gamma> x =
  (case fmlookup \<Gamma> x of
     Some (ModStub q'') \<Rightarrow> do { \<Gamma>' \<leftarrow> check_module M V q''; Inr (ModChecked q'' \<Gamma>') }
   | \<theta> \<Rightarrow>
       (case resolve_name \<Gamma> (x, []) of
          Some \<theta>' \<Rightarrow> Inr \<theta>'
        | None \<Rightarrow> Inl (q, case \<theta> of None \<Rightarrow> UnknownMember x q' | Some _ \<Rightarrow> UnassignedMember x q')))" |
"imports_entries M V q q' \<Gamma> [] = Inr []" |
"imports_entries M V q q' \<Gamma> (x # xs) = do {
   \<theta> \<leftarrow> imports_entry M V q q' \<Gamma> x;
   \<theta>s \<leftarrow> imports_entries M V q q' \<Gamma> xs;
   Inr (\<theta> # \<theta>s)
 }" |
"check_modules M V [] = Inr ()" |
"check_modules M V (q # qs) = do { check_module M V q; check_modules M V qs }"
by pat_completeness auto

(* Measures: count of modules of M not in V; then a topological rank of the call graph, which is acyclic
   if we remove the call from the module rule to its imports; then the length of the list argument *)
termination
by (relation "measures [
     \<lambda>x. case x of
       Inl (Inl (M, V, _)) \<Rightarrow> card (fmdom' M - set V)
     | Inl (Inr (Inl (M, V, _, _))) \<Rightarrow> card (fmdom' M - set V)
     | Inl (Inr (Inr (M, V, _, _, _))) \<Rightarrow> card (fmdom' M - set V)
     | Inr (Inl (M, V, _, _, _, _)) \<Rightarrow> card (fmdom' M - set V)
     | Inr (Inr (Inl (M, V, _, _, _, _))) \<Rightarrow> card (fmdom' M - set V)
     | Inr (Inr (Inr (M, V, _))) \<Rightarrow> card (fmdom' M - set V),
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
     | Inl (Inr (Inr (_, _, _, _, xs))) \<Rightarrow> length xs
     | Inr (Inl _) \<Rightarrow> 0
     | Inr (Inr (Inl (_, _, _, _, _, xs))) \<Rightarrow> length xs
     | Inr (Inr (Inr (_, _, qs))) \<Rightarrow> length qs]")
   (auto simp: card_fmdom_insert)

definition check_program :: "program \<Rightarrow> (name \<times> reason) option"
where
"check_program M = (case check_module M [] main of Inl f \<Rightarrow> Some f | Inr _ \<Rightarrow> None)"

end
