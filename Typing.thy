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

type_synonym cxt = "(var, cxt_entry) fmap"

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

(* Possibly unassigned at the same type or scheme, the other forms being undefined *)
fun merge_undefined :: "cxt_entry \<Rightarrow> cxt_entry"
where
"merge_undefined (Ty \<tau>) = PU \<tau>" |
"merge_undefined (DU \<tau>) = PU \<tau>" |
"merge_undefined (PU \<tau>) = PU \<tau>" |
"merge_undefined (Scheme \<pi>) = PUScheme \<pi>" |
"merge_undefined (PUScheme \<pi>) = PUScheme \<pi>" |
"merge_undefined _ = undefined"

fun merge_cxt_entry :: "cxt_entry option \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry"
where
"merge_cxt_entry (Some (Ty \<sigma>)) (Some (Ty \<tau>)) = Ty (\<sigma> \<squnion> \<tau>)" |
"merge_cxt_entry (Some (Scheme \<pi>)) (Some (PUScheme \<pi>')) = (if \<pi> = \<pi>' then PUScheme \<pi> else undefined)" |
"merge_cxt_entry (Some (PUScheme \<pi>)) (Some (Scheme \<pi>')) = (if \<pi> = \<pi>' then PUScheme \<pi> else undefined)" |
"merge_cxt_entry (Some \<theta>) (Some \<theta>') =
  (if \<theta> = \<theta>' then \<theta>
   else case (var_ty \<theta>, var_ty \<theta>') of (Some \<sigma>, Some \<tau>) \<Rightarrow> PU (\<sigma> \<squnion> \<tau>) | _ \<Rightarrow> undefined)" |
"merge_cxt_entry (Some \<theta>) None = merge_undefined \<theta>" |
"merge_cxt_entry None (Some \<theta>) = merge_undefined \<theta>" |
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

function (sequential)
  synth_expr :: "cxt \<Rightarrow> expr \<Rightarrow> ty option" and
  synth_exprs :: "cxt \<Rightarrow> expr list \<Rightarrow> ty option list" and
  check_expr :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" and
  check_expr' :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" and
  check_exprs :: "cxt \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool"
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
"check_expr' \<Gamma> _ _ = False" |

"check_exprs \<Gamma> [] [] = True" |
"check_exprs \<Gamma> (e # es) (\<tau> # \<tau>s) = (check_expr \<Gamma> e \<tau> \<and> check_exprs \<Gamma> es \<tau>s)" |
"check_exprs \<Gamma> _ _ = False"
by pat_completeness auto

termination
by (relation "inv_image (less_than <*lex*> less_than) (\<lambda>x. case x of
     Inl (Inl (\<Gamma>, e)) \<Rightarrow> (size e, 0)
   | Inl (Inr (\<Gamma>, es)) \<Rightarrow> (size_list size es, 0)
   | Inr (Inl (\<Gamma>, e, \<tau>)) \<Rightarrow> (size e, 2)
   | Inr (Inr (Inl (\<Gamma>, e, \<tau>))) \<Rightarrow> (size e, 1)
   | Inr (Inr (Inr (\<Gamma>, es, \<tau>s))) \<Rightarrow> (size_list size es, 2))")
   (auto dest!: nth_mem intro: size_list_estimation' simp: less_Suc_eq_le)

(* Signature as a context entry: a type when there are no type parameters, otherwise a scheme *)
fun signature_entry :: "scheme \<Rightarrow> cxt_entry"
where
"signature_entry (TyScheme [] \<tau>) = Ty \<tau>" |
"signature_entry \<pi> = Scheme \<pi>"

fun def_signature :: "cxt \<Rightarrow> func \<Rightarrow> scheme option"
where
"def_signature \<Gamma> (Def f \<alpha>s xps \<psi> s) =
   (let \<Gamma>' = \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar in
    case (those (map (resolve_type \<Gamma>' \<circ> snd) xps), resolve_type \<Gamma>' \<psi>) of
     (Some \<sigma>s, Some \<tau>) \<Rightarrow> Some (TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>))
   | _ \<Rightarrow> None)"

abbreviation false_lit :: expr where "false_lit \<equiv> ExprLiteral (LitBool False)"

fun merges :: "static_outcome option list \<Rightarrow> static_outcome option"
where
"merges [] = Some Returns\<^sub>R" |
"merges (R # Rs) = (case (R, merges Rs) of (Some R, Some R') \<Rightarrow> Some (R \<oplus>\<^sub>R R') | _ \<Rightarrow> None)"

fun check_stmt :: "cxt \<Rightarrow> ty option \<Rightarrow> stmt \<Rightarrow> static_outcome option"
and check_elifs :: "cxt \<Rightarrow> ty option \<Rightarrow> (expr \<times> stmt) list \<Rightarrow> static_outcome option list"
and check_defs :: "cxt \<Rightarrow> func list \<Rightarrow> scheme list \<Rightarrow> bool"
and check_def :: "cxt \<Rightarrow> func \<Rightarrow> scheme \<Rightarrow> bool"
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

end
