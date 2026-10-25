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
  | TypeAlias "(var, cxt_entry) fmap" name "type_def list" nat
  | Type name
  | TypeVar
  | Scheme ty_scheme
  | PUScheme ty_scheme
  | PredefName

type_synonym cxt = "(var, cxt_entry) fmap"

datatype class_entry = ClassDef cxt name "type_def list" nat

type_synonym class_table = "(name, class_entry) fmap"

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
  | ClassArityMismatch name nat nat
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
  | TypeAliasAsValue name
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

definition resolve_name :: "cxt \<Rightarrow> name \<Rightarrow> cxt_entry option"
where
"resolve_name \<Gamma> q =
  (case lookup \<Gamma> q of
     Some (Ty \<tau>) \<Rightarrow> Some (Ty \<tau>)
   | Some (ModChecked q' \<Gamma>') \<Rightarrow> Some (ModChecked q' \<Gamma>')
   | Some (Type C) \<Rightarrow> Some (Type C)
   | Some (TypeAlias \<Gamma>' q' \<chi>s i) \<Rightarrow> Some (TypeAlias \<Gamma>' q' \<chi>s i)
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

definition range_class :: name where "range_class = snoc builtins ''range''"

fun sized :: "ty \<Rightarrow> bool"
where
"sized (TyList _) = True" |
"sized (TyDict _) = True" |
"sized (TyPrim str) = True" |
"sized (TyTuple _) = True" |
"sized (TyClass C []) = (C = range_class)" |
"sized _ = False"

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

definition type_params :: "class_table \<Rightarrow> name \<Rightarrow> var list"
where
"type_params \<Sigma> C =
  (case fmlookup \<Sigma> C of
     Some (ClassDef _ _ \<chi>s i) \<Rightarrow> (case \<chi>s ! i of Dataclass _ \<alpha>s _ _ \<Rightarrow> \<alpha>s | TypeStmt _ _ _ \<Rightarrow> undefined)
   | None \<Rightarrow> undefined)"

fun resolve_type :: "class_table \<Rightarrow> cxt \<Rightarrow> ty_expr \<Rightarrow> reason + ty"
where
"resolve_type \<Sigma> \<Gamma> (TyExprPrim \<nu>) = do { check_predefined \<Gamma> (prim_name \<nu>); Inr (TyPrim \<nu>) }" |
"resolve_type \<Sigma> \<Gamma> (TyExprName q \<psi>s) =
  (if snd q = [] \<and> \<psi>s = [] \<and> fmlookup \<Gamma> (fst q) = Some TypeVar then Inr (TyVar (fst q))
   else case resolve_name \<Gamma> q of
     Some (Type C) \<Rightarrow> do {
       \<tau>s \<leftarrow> those_sum (map (resolve_type \<Sigma> \<Gamma>) \<psi>s);
       let n = length (type_params \<Sigma> C);
       if length \<tau>s = n then Inr (TyClass C \<tau>s) else Inl (ClassArityMismatch q n (length \<tau>s))
     }
   | Some (TypeAlias _ _ _ _) \<Rightarrow> undefined
   | _ \<Rightarrow> Inl (not_type_name \<Gamma> q))" |
"resolve_type \<Sigma> \<Gamma> (TyExprLiteral l) = do { check_predefined \<Gamma> ''Literal''; Inr (TyLiteral l) }" |
"resolve_type \<Sigma> \<Gamma> (TyExprList \<psi>) = do { check_predefined \<Gamma> ''list''; \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; Inr (TyList \<tau>) }" |
"resolve_type \<Sigma> \<Gamma> (TyExprDict \<psi>) = do {
   check_predefined \<Gamma> ''dict''; check_predefined \<Gamma> ''str''; \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; Inr (TyDict \<tau>)
 }" |
"resolve_type \<Sigma> \<Gamma> (TyExprTuple \<psi>s) = do {
   check_predefined \<Gamma> ''tuple''; \<tau>s \<leftarrow> those_sum (map (resolve_type \<Sigma> \<Gamma>) \<psi>s); Inr (TyTuple \<tau>s)
 }" |
"resolve_type \<Sigma> \<Gamma> (TyExprCallable \<psi>s \<psi>) = do {
   check_predefined \<Gamma> ''Callable'';
   \<sigma>s \<leftarrow> those_sum (map (resolve_type \<Sigma> \<Gamma>) \<psi>s);
   \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>;
   Inr (TyCallable \<sigma>s \<tau>)
 }" |
"resolve_type \<Sigma> \<Gamma> (TyExprUnion \<psi> \<psi>') = do {
   \<sigma> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>'; Inr (TyUnion \<sigma> \<tau>)
 }"

definition type_entry :: "cxt \<Rightarrow> name \<Rightarrow> type_def list \<Rightarrow> nat \<Rightarrow> cxt_entry"
where
"type_entry \<Gamma> q \<chi>s i =
  (case \<chi>s ! i of Dataclass c _ _ _ \<Rightarrow> Type (snoc q c) | TypeStmt _ _ _ \<Rightarrow> TypeAlias \<Gamma> q \<chi>s i)"

definition type_context :: "cxt \<Rightarrow> name \<Rightarrow> type_def list \<Rightarrow> nat \<Rightarrow> cxt"
where
"type_context \<Gamma> q \<chi>s i =
  (let entries = \<lambda>js. fmap_of_list (map (\<lambda>j. (type_def_name (\<chi>s ! j), type_entry \<Gamma> q \<chi>s j)) js) in
   case \<chi>s ! i of
     TypeStmt _ \<alpha>s _ \<Rightarrow> \<Gamma> \<otimes> entries [0..<length \<chi>s] \<otimes> fmconst (set \<alpha>s) TypeVar
   | Dataclass _ \<alpha>s _ _ \<Rightarrow> \<Gamma> \<otimes> entries [0..<i] \<otimes> fmconst (set \<alpha>s) TypeVar)"

definition base :: "class_table \<Rightarrow> name \<Rightarrow> (name \<times> ty list) option"
where
"base \<Sigma> C =
  (case fmlookup \<Sigma> C of
     Some (ClassDef \<Gamma> q \<chi>s i) \<Rightarrow>
       (case \<chi>s ! i of
          Dataclass _ _ None _ \<Rightarrow> None
        | Dataclass _ _ (Some (q', \<psi>s)) _ \<Rightarrow>
            (case resolve_type \<Sigma> (type_context \<Gamma> q \<chi>s i) (TyExprName q' \<psi>s) of
               Inr (TyClass D \<sigma>s) \<Rightarrow> Some (D, \<sigma>s)
             | _ \<Rightarrow> undefined)
        | TypeStmt _ _ _ \<Rightarrow> undefined)
   | None \<Rightarrow> undefined)"

fun subst :: "ty list \<Rightarrow> var list \<Rightarrow> ty \<Rightarrow> ty"
where
"subst \<tau>s \<alpha>s (TyVar \<alpha>) = (case map_of (zip \<alpha>s \<tau>s) \<alpha> of Some \<tau> \<Rightarrow> \<tau> | None \<Rightarrow> TyVar \<alpha>)" |
"subst \<tau>s \<alpha>s (TyList \<sigma>) = TyList (subst \<tau>s \<alpha>s \<sigma>)" |
"subst \<tau>s \<alpha>s (TyTuple \<sigma>s) = TyTuple (map (subst \<tau>s \<alpha>s) \<sigma>s)" |
"subst \<tau>s \<alpha>s (TyDict \<sigma>) = TyDict (subst \<tau>s \<alpha>s \<sigma>)" |
"subst \<tau>s \<alpha>s (TyCallable \<sigma>s \<sigma>) = TyCallable (map (subst \<tau>s \<alpha>s) \<sigma>s) (subst \<tau>s \<alpha>s \<sigma>)" |
"subst \<tau>s \<alpha>s (TyClass C \<sigma>s) = TyClass C (map (subst \<tau>s \<alpha>s) \<sigma>s)" |
"subst \<tau>s \<alpha>s (TyUnion \<sigma> \<sigma>') = TyUnion (subst \<tau>s \<alpha>s \<sigma>) (subst \<tau>s \<alpha>s \<sigma>')" |
"subst \<tau>s \<alpha>s \<sigma> = \<sigma>"

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

definition join :: "ty \<Rightarrow> class_table \<Rightarrow> ty \<Rightarrow> ty" ("_ \<squnion>\<^bsub>_\<^esub> _" [65, 0, 66] 65)
where
"\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau> =
  (if \<Sigma> \<turnstile> \<sigma> <: \<tau> then \<tau> else if \<Sigma> \<turnstile> \<tau> <: \<sigma> then \<sigma> else TyUnion \<sigma> \<tau>)"

definition joins :: "class_table \<Rightarrow> ty list \<Rightarrow> ty"
where
"joins \<Sigma> \<tau>s = foldr (\<lambda>\<sigma> \<tau>. \<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>) \<tau>s (TyPrim Never)"

fun meet :: "ty \<Rightarrow> class_table \<Rightarrow> ty \<Rightarrow> ty" ("_ \<sqinter>\<^bsub>_\<^esub> _" [70, 0, 71] 70)
and meets :: "class_table \<Rightarrow> ty list \<Rightarrow> ty list \<Rightarrow> ty list"
where
"TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<sqinter>\<^bsub>\<Sigma>\<^esub> \<tau> =
  (if \<Sigma> \<turnstile> TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 <: \<tau> then TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 else if \<Sigma> \<turnstile> \<tau> <: TyUnion \<sigma>\<^sub>1 \<sigma>\<^sub>2 then \<tau>
   else (\<sigma>\<^sub>1 \<sqinter>\<^bsub>\<Sigma>\<^esub> \<tau>) \<squnion>\<^bsub>\<Sigma>\<^esub> (\<sigma>\<^sub>2 \<sqinter>\<^bsub>\<Sigma>\<^esub> \<tau>))" |
"\<sigma> \<sqinter>\<^bsub>\<Sigma>\<^esub> TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2 =
  (if \<Sigma> \<turnstile> \<sigma> <: TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2 then \<sigma> else if \<Sigma> \<turnstile> TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2 <: \<sigma> then TyUnion \<tau>\<^sub>1 \<tau>\<^sub>2
   else (\<sigma> \<sqinter>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>1) \<squnion>\<^bsub>\<Sigma>\<^esub> (\<sigma> \<sqinter>\<^bsub>\<Sigma>\<^esub> \<tau>\<^sub>2))" |
"TyCallable \<sigma>s \<sigma> \<sqinter>\<^bsub>\<Sigma>\<^esub> TyCallable \<tau>s \<tau> =
  (if \<Sigma> \<turnstile> TyCallable \<sigma>s \<sigma> <: TyCallable \<tau>s \<tau> then TyCallable \<sigma>s \<sigma>
   else if \<Sigma> \<turnstile> TyCallable \<tau>s \<tau> <: TyCallable \<sigma>s \<sigma> then TyCallable \<tau>s \<tau>
   else if length \<sigma>s = length \<tau>s
   then TyCallable (map2 (\<lambda>\<sigma>' \<tau>'. \<sigma>' \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') \<sigma>s \<tau>s) (\<sigma> \<sqinter>\<^bsub>\<Sigma>\<^esub> \<tau>)
   else TyPrim Never)" |
"TyTuple \<sigma>s \<sqinter>\<^bsub>\<Sigma>\<^esub> TyTuple \<tau>s =
  (if \<Sigma> \<turnstile> TyTuple \<sigma>s <: TyTuple \<tau>s then TyTuple \<sigma>s else if \<Sigma> \<turnstile> TyTuple \<tau>s <: TyTuple \<sigma>s then TyTuple \<tau>s
   else if length \<sigma>s = length \<tau>s then TyTuple (meets \<Sigma> \<sigma>s \<tau>s) else TyPrim Never)" |
"\<sigma> \<sqinter>\<^bsub>\<Sigma>\<^esub> \<tau> = (if \<Sigma> \<turnstile> \<sigma> <: \<tau> then \<sigma> else if \<Sigma> \<turnstile> \<tau> <: \<sigma> then \<tau> else TyPrim Never)" |

"meets \<Sigma> (\<sigma> # \<sigma>s) (\<tau> # \<tau>s) = (\<sigma> \<sqinter>\<^bsub>\<Sigma>\<^esub> \<tau>) # meets \<Sigma> \<sigma>s \<tau>s" |
"meets _ _ _ = []"

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

fun merge_cxt_entry :: "class_table \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry"
where
"merge_cxt_entry \<Sigma> (Some (Ty \<sigma>)) (Some (Ty \<tau>)) = Ty (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>)" |
"merge_cxt_entry \<Sigma> (Some (Scheme \<pi>)) (Some (PUScheme \<pi>')) = (if \<pi> = \<pi>' then PUScheme \<pi> else undefined)" |
"merge_cxt_entry \<Sigma> (Some (PUScheme \<pi>)) (Some (Scheme \<pi>')) = (if \<pi> = \<pi>' then PUScheme \<pi> else undefined)" |
"merge_cxt_entry \<Sigma> (Some \<theta>) (Some \<theta>') =
  (if \<theta> = \<theta>' then \<theta>
   else case (var_ty \<theta>, var_ty \<theta>') of (Some \<sigma>, Some \<tau>) \<Rightarrow> PU (\<sigma> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>) | _ \<Rightarrow> undefined)" |
"merge_cxt_entry \<Sigma> (Some \<theta>) None = possibly_unassigned \<theta>" |
"merge_cxt_entry \<Sigma> None (Some \<theta>) = possibly_unassigned \<theta>" |
"merge_cxt_entry \<Sigma> None None = undefined"

definition merge :: "cxt \<Rightarrow> class_table \<Rightarrow> cxt \<Rightarrow> cxt" ("_ \<oplus>\<^bsub>_\<^esub> _" [65, 0, 66] 65)
where
"\<Gamma> \<oplus>\<^bsub>\<Sigma>\<^esub> \<Gamma>' = fmmap_keys (\<lambda>x _. merge_cxt_entry \<Sigma> (fmlookup \<Gamma> x) (fmlookup \<Gamma>' x)) (\<Gamma> \<otimes> \<Gamma>')"

datatype static_outcome = Assigns\<^sub>R cxt | Returns\<^sub>R

fun merge_outcome :: "class_table \<Rightarrow> static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome"
where
"merge_outcome \<Sigma> (Assigns\<^sub>R \<Delta>) (Assigns\<^sub>R \<Delta>') = Assigns\<^sub>R (\<Delta> \<oplus>\<^bsub>\<Sigma>\<^esub> \<Delta>')" |
"merge_outcome \<Sigma> R Returns\<^sub>R = R" |
"merge_outcome \<Sigma> Returns\<^sub>R R = R"

fun merges :: "class_table \<Rightarrow> (reason + static_outcome) list \<Rightarrow> reason + static_outcome"
where
"merges \<Sigma> [] = Inr Returns\<^sub>R" |
"merges \<Sigma> (m # ms) = do { R \<leftarrow> m; R' \<leftarrow> merges \<Sigma> ms; Inr (merge_outcome \<Sigma> R R') }"

fun override_outcome :: "static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome" (infixl "\<otimes>\<^sub>R" 100)
where
"Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R Assigns\<^sub>R \<Delta>' = Assigns\<^sub>R (\<Delta> \<otimes> \<Delta>')" |
"_ \<otimes>\<^sub>R _ = Returns\<^sub>R"

fun equality_type :: "class_table \<Rightarrow> ty \<Rightarrow> bool"
where
"equality_type \<Sigma> (TyPrim _) = True" |
"equality_type \<Sigma> (TyLiteral _) = True" |
"equality_type \<Sigma> (TyList \<tau>) = equality_type \<Sigma> \<tau>" |
"equality_type \<Sigma> (TyDict \<tau>) = equality_type \<Sigma> \<tau>" |
"equality_type \<Sigma> (TyTuple \<tau>s) = list_all (equality_type \<Sigma>) \<tau>s" |
"equality_type \<Sigma> (TyUnion \<sigma> \<tau>) = (equality_type \<Sigma> \<sigma> \<and> equality_type \<Sigma> \<tau>)" |
"equality_type \<Sigma> _ = False"

abbreviation comparable :: "class_table \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" where "comparable \<Sigma> \<sigma> \<tau> \<equiv> \<Sigma> \<turnstile> \<sigma> <: \<tau> \<or> \<Sigma> \<turnstile> \<tau> <: \<sigma>"

inductive binop_overload :: "class_table \<Rightarrow> bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> (ty \<times> ty) \<times> ty \<Rightarrow> bool"
for \<Sigma> :: class_table
where
OverloadEq:
  "\<lbrakk> op \<in> {BOpEq, BOpNeq} ; equality_type \<Sigma> \<sigma>\<^sub>1 ; equality_type \<Sigma> \<sigma>\<^sub>2 ; comparable \<Sigma> \<sigma>\<^sub>1 \<sigma>\<^sub>2 \<rbrakk>
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

fun numeric_literal :: "expr \<Rightarrow> bool"
where
"numeric_literal (ExprLiteral (LitInt _)) = True" |
"numeric_literal (ExprLiteral (LitFloat _)) = True" |
"numeric_literal _ = False"

(* Type of the elements of an iterable type; None otherwise *)
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

fun dotted_name :: "expr \<Rightarrow> name option"
where
"dotted_name (ExprVar x) = Some (x, [])" |
"dotted_name (ExprAttribute e x) = map_option (\<lambda>q. snoc q x) (dotted_name e)" |
"dotted_name _ = None"

(* Failure for variable x, which isn't bound at a type, by its context entry *)
fun var_reason :: "var \<Rightarrow> cxt_entry option \<Rightarrow> reason"
where
"var_reason x (Some (ModStub _)) = ModuleAsValue (x, [])" |
"var_reason x (Some (ModChecked _ _)) = ModuleAsValue (x, [])" |
"var_reason x (Some (Type _)) = ClassAsValue (x, [])" |
"var_reason x (Some (TypeAlias _ _ _ _)) = TypeAliasAsValue (x, [])" |
"var_reason x (Some PredefName) = PredefinedNameAsValue (x, [])" |
"var_reason x (Some TypeVar) = TypeParameterAsValue x" |
"var_reason x (Some (Scheme _)) = TypeSchemeAsValue (x, [])" |
"var_reason x (Some Unbound) = UnboundName x" |
"var_reason x (Some (DU _)) = UnassignedVariable x" |
"var_reason x (Some (PU _)) = PossiblyUnassigned x" |
"var_reason x (Some (PUScheme _)) = PossiblyUnassigned x" |
"var_reason x (Some (Ty _)) = undefined" |
"var_reason x None = UndefinedVariable x"

definition attr_module :: "name \<Rightarrow> cxt \<Rightarrow> var \<Rightarrow> name \<Rightarrow> reason + ty"
where
"attr_module q \<Gamma> x q' =
  (case fmlookup \<Gamma> x of
     None \<Rightarrow> Inl (UnknownMember x q)
   | Some (Ty \<tau>) \<Rightarrow> Inr \<tau>
   | Some (ModStub q'') \<Rightarrow> Inl (SubmoduleNotImported q'')
   | Some (ModChecked _ _) \<Rightarrow> Inl (ModuleAsValue q')
   | Some (Type _) \<Rightarrow> Inl (ClassAsValue q')
   | Some (TypeAlias _ _ _ _) \<Rightarrow> Inl (TypeAliasAsValue q')
   | Some PredefName \<Rightarrow> Inl (PredefinedNameAsValue q')
   | Some (Scheme _) \<Rightarrow> Inl (TypeSchemeAsValue q')
   | Some TypeVar \<Rightarrow> undefined
   | Some _ \<Rightarrow> Inl (UnassignedMember x q))"

(* Type of attribute x of a value of type \<sigma>, which isn't a module *)
fun attribute_type :: "class_table \<Rightarrow> ty \<Rightarrow> var \<Rightarrow> reason + ty"
where
"attribute_type \<Sigma> (TyUnion \<sigma> \<sigma>') x =
  do { \<tau> \<leftarrow> attribute_type \<Sigma> \<sigma> x; \<tau>' \<leftarrow> attribute_type \<Sigma> \<sigma>' x; Inr (\<tau> \<squnion>\<^bsub>\<Sigma>\<^esub> \<tau>') }" |
"attribute_type \<Sigma> (TyClass _ _) _ = undefined" |
"attribute_type \<Sigma> \<sigma> _ = Inl (NoAttributes \<sigma>)"

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

definition class_of_name :: "cxt \<Rightarrow> expr \<Rightarrow> name option"
where
"class_of_name \<Gamma> e = (case Option.bind (dotted_name e) (resolve_name \<Gamma>) of Some (Type C) \<Rightarrow> Some C | _ \<Rightarrow> None)"

function (sequential)
  synth_expr :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> reason + ty" and
  synth_exprs :: "class_table \<Rightarrow> cxt \<Rightarrow> expr list \<Rightarrow> (reason + ty) list" and
  check_expr :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> reason + unit" and
  check_expr' :: "class_table \<Rightarrow> cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> (reason + unit) option" and
  check_exprs :: "class_table \<Rightarrow> cxt \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> reason + unit" and
  quals :: "class_table \<Rightarrow> cxt \<Rightarrow> qualifier list \<Rightarrow> reason + cxt"
where
"synth_expr \<Sigma> \<Gamma> (ExprVar x) = (case fmlookup \<Gamma> x of Some (Ty \<tau>) \<Rightarrow> Inr \<tau> | \<theta> \<Rightarrow> Inl (var_reason x \<theta>))" |
"synth_expr \<Sigma> \<Gamma> (ExprLiteral l) = Inr (case l of LitFloat _ \<Rightarrow> TyPrim float | _ \<Rightarrow> TyLiteral l)" |
"synth_expr \<Sigma> \<Gamma> (ExprCall e (es, kws)) =
  (case e of
     ExprLambda xs e' \<Rightarrow> do {
       ensure (kws = []) KeywordArgumentsNotConstructor;
       ensure (length xs = length es) (CallArityMismatch (length xs) (length es));
       \<tau>s \<leftarrow> those_sum (synth_exprs \<Sigma> \<Gamma> es);
       if distinct xs then synth_expr \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e' else Inl undefined
     }
   | _ \<Rightarrow>
     if class_of_name \<Gamma> e \<noteq> None \<or> (case e of ExprSubscript e' _ \<Rightarrow> class_of_name \<Gamma> e' \<noteq> None | _ \<Rightarrow> False)
     then undefined
     else do {
       \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e;
       case \<sigma> of
         TyCallable \<sigma>s \<tau> \<Rightarrow> do {
           ensure (kws = []) KeywordArgumentsNotConstructor;
           ensure (length \<sigma>s = length es) (CallArityMismatch (length \<sigma>s) (length es));
           check_exprs \<Sigma> \<Gamma> es \<sigma>s;
           ensure (\<tau> \<noteq> TyPrim NoneType) (MypyCompatibility NoneResult);
           Inr \<tau>
         }
       | _ \<Rightarrow> Inl (NotCallable \<sigma>)
     })" |
"synth_expr \<Sigma> \<Gamma> (ExprBinOp op e e') = do {
   \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e;
   \<sigma>' \<leftarrow> synth_expr \<Sigma> \<Gamma> e';
   case resolve_binop \<Sigma> op \<sigma> \<sigma>' of Some \<tau> \<Rightarrow> Inr \<tau> | None \<Rightarrow> Inl (NoBinaryOverload op \<sigma> \<sigma>')
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprUnOp op e) =
  (if op = UOpNeg \<and> numeric_literal e then Inl undefined
   else do {
     \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e;
     case resolve_unop \<Sigma> op \<sigma> of Some \<tau> \<Rightarrow> Inr \<tau> | None \<Rightarrow> Inl (NoUnaryOverload op \<sigma>)
   })" |
"synth_expr \<Sigma> \<Gamma> (ExprAnd e e') =
  do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); check_expr \<Sigma> \<Gamma> e' (TyPrim bool); Inr (TyPrim bool) }" |
"synth_expr \<Sigma> \<Gamma> (ExprOr e e') =
  do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); check_expr \<Sigma> \<Gamma> e' (TyPrim bool); Inr (TyPrim bool) }" |
"synth_expr \<Sigma> \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) = do {
   check_expr \<Sigma> \<Gamma> e (TyPrim bool);
   case (synth_expr \<Sigma> \<Gamma> e\<^sub>1, synth_expr \<Sigma> \<Gamma> e\<^sub>2) of
     (Inr \<sigma>\<^sub>1, Inr \<sigma>\<^sub>2) \<Rightarrow> Inr (\<sigma>\<^sub>1 \<squnion>\<^bsub>\<Sigma>\<^esub> \<sigma>\<^sub>2)
   | (Inr \<sigma>\<^sub>1, Inl _) \<Rightarrow> do { check_expr \<Sigma> \<Gamma> e\<^sub>2 \<sigma>\<^sub>1; Inr \<sigma>\<^sub>1 }
   | (Inl _, Inr \<sigma>\<^sub>2) \<Rightarrow> do { check_expr \<Sigma> \<Gamma> e\<^sub>1 \<sigma>\<^sub>2; Inr \<sigma>\<^sub>2 }
   | (r\<^sub>1, r\<^sub>2) \<Rightarrow> Inl (synth_failure [r\<^sub>1, r\<^sub>2])
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprList es) =
  (let \<sigma>s = synth_exprs \<Sigma> \<Gamma> es; \<tau> = joins \<Sigma> (map (base_type \<circ> projr) (filter (Not \<circ> isl) \<sigma>s)) in
   if \<not> list_all isl \<sigma>s then do {
     those_sum (map (\<lambda>j. check_expr \<Sigma> \<Gamma> (es ! j) \<tau>) (filter (\<lambda>j. isl (\<sigma>s ! j)) [0..<length es]));
     Inr (TyList \<tau>)
   }
   else Inl (synth_failure \<sigma>s))" |
"synth_expr \<Sigma> \<Gamma> (ExprTuple es) = do { \<tau>s \<leftarrow> those_sum (synth_exprs \<Sigma> \<Gamma> es); Inr (TyTuple \<tau>s) }" |
"synth_expr \<Sigma> \<Gamma> (ExprAttribute e x) =
  (case dotted_name e of
     Some q \<Rightarrow>
       (case (resolve_name \<Gamma> q, lookup \<Gamma> q) of
          (Some (ModChecked q' \<Gamma>'), _) \<Rightarrow> attr_module q' \<Gamma>' x (snoc q x)
        | (_, Some (ModStub q')) \<Rightarrow> Inl (SubmoduleNotImported q')
        | _ \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e; attribute_type \<Sigma> \<sigma> x })
   | None \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e; attribute_type \<Sigma> \<sigma> x })" |
"synth_expr \<Sigma> \<Gamma> (ExprSubscript e e') = do {
   \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e;
   subscript_type \<Sigma> \<sigma> (check_expr \<Sigma> \<Gamma> e' (TyPrim int)) (check_expr \<Sigma> \<Gamma> e' (TyPrim str)) (synth_expr \<Sigma> \<Gamma> e')
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprDict kvs) =
  (let \<sigma>s = synth_exprs \<Sigma> \<Gamma> (map snd kvs); \<tau> = joins \<Sigma> (map (base_type \<circ> projr) (filter (Not \<circ> isl) \<sigma>s)) in do {
     check_exprs \<Sigma> \<Gamma> (map fst kvs) (replicate (length kvs) (TyPrim str));
     if \<not> list_all isl \<sigma>s then do {
       those_sum (map (\<lambda>j. check_expr \<Sigma> \<Gamma> (snd (kvs ! j)) \<tau>) (filter (\<lambda>j. isl (\<sigma>s ! j)) [0..<length kvs]));
       Inr (TyDict \<tau>)
     }
     else Inl (synth_failure \<sigma>s)
   })" |
"synth_expr \<Sigma> \<Gamma> (ExprListComp e gs) = do {
   \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs;
   captured (captures e) \<Delta>;
   \<tau> \<leftarrow> synth_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e;
   Inr (TyList (base_type \<tau>))
 }" |
"synth_expr \<Sigma> \<Gamma> (ExprDictComp e e' gs) = do {
   \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs;
   captured (captures e \<union> captures e') \<Delta>;
   check_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str);
   \<tau> \<leftarrow> synth_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e';
   Inr (TyDict (base_type \<tau>))
 }" |
"synth_expr \<Sigma> \<Gamma> _ = Inl NotSynthesised" |

"synth_exprs \<Sigma> \<Gamma> [] = []" |
"synth_exprs \<Sigma> \<Gamma> (e # es) = synth_expr \<Sigma> \<Gamma> e # synth_exprs \<Sigma> \<Gamma> es" |

"check_expr \<Sigma> \<Gamma> e \<tau> =
  (case check_expr' \<Sigma> \<Gamma> e \<tau> of
     Some (Inr ()) \<Rightarrow> Inr ()
   | Some (Inl r) \<Rightarrow> (case synth_expr \<Sigma> \<Gamma> e of Inr \<sigma> \<Rightarrow> if \<Sigma> \<turnstile> \<sigma> <: \<tau> then Inr () else Inl r | Inl _ \<Rightarrow> Inl r)
   | None \<Rightarrow> do { \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e; ensure (\<Sigma> \<turnstile> \<sigma> <: \<tau>) (TypeMismatch \<tau> \<sigma>) })" |

"check_expr' \<Sigma> \<Gamma> (ExprLambda xs e) \<tau> =
  Some (case \<tau> of
     TyCallable \<tau>s \<tau>' \<Rightarrow>
       if length xs \<noteq> length \<tau>s then Inl (LambdaTypeMismatch \<tau> (Some (length xs)))
       else if distinct xs then check_expr \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e \<tau>' else Inl undefined
   | _ \<Rightarrow> Inl (LambdaTypeMismatch \<tau> None))" |
"check_expr' \<Sigma> \<Gamma> (ExprCall e (es, kws)) \<tau> =
  (case e of
     ExprLambda xs e' \<Rightarrow> Some (do {
       ensure (kws = []) KeywordArgumentsNotConstructor;
       ensure (length xs = length es) (CallArityMismatch (length xs) (length es));
       \<tau>s \<leftarrow> those_sum (synth_exprs \<Sigma> \<Gamma> es);
       if distinct xs then check_expr \<Sigma> (\<Gamma> \<otimes> fmap_of_list (zip xs (map Ty \<tau>s))) e' \<tau> else Inl undefined
     })
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprList es) \<tau> =
  (case \<tau> of TyList \<tau>' \<Rightarrow> Some (check_exprs \<Sigma> \<Gamma> es (replicate (length es) \<tau>')) | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprTuple es) \<tau> =
  (case \<tau> of TyTuple \<tau>s \<Rightarrow> if length es = length \<tau>s then Some (check_exprs \<Sigma> \<Gamma> es \<tau>s) else None | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) \<tau> =
  Some (do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); check_expr \<Sigma> \<Gamma> e\<^sub>1 \<tau>; check_expr \<Sigma> \<Gamma> e\<^sub>2 \<tau> })" |
"check_expr' \<Sigma> \<Gamma> (ExprDict kvs) \<tau> =
  (case \<tau> of
     TyDict \<tau>' \<Rightarrow> Some (do {
       check_exprs \<Sigma> \<Gamma> (map fst kvs) (replicate (length kvs) (TyPrim str));
       check_exprs \<Sigma> \<Gamma> (map snd kvs) (replicate (length kvs) \<tau>')
     })
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprListComp e gs) \<tau> =
  (case \<tau> of
     TyList \<tau>' \<Rightarrow> Some (do { \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs; captured (captures e) \<Delta>; check_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e \<tau>' })
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> (ExprDictComp e e' gs) \<tau> =
  (case \<tau> of
     TyDict \<tau>' \<Rightarrow> Some (do {
       \<Delta> \<leftarrow> quals \<Sigma> \<Gamma> gs;
       captured (captures e \<union> captures e') \<Delta>;
       check_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e (TyPrim str);
       check_expr \<Sigma> (\<Gamma> \<otimes> \<Delta>) e' \<tau>'
     })
   | _ \<Rightarrow> None)" |
"check_expr' \<Sigma> \<Gamma> _ _ = None" |

"check_exprs \<Sigma> \<Gamma> [] [] = Inr ()" |
"check_exprs \<Sigma> \<Gamma> (e # es) (\<tau> # \<tau>s) = do { check_expr \<Sigma> \<Gamma> e \<tau>; check_exprs \<Sigma> \<Gamma> es \<tau>s }" |
"check_exprs \<Sigma> \<Gamma> _ _ = undefined" |

"quals \<Sigma> \<Gamma> [] = Inr fmempty" |
"quals \<Sigma> \<Gamma> (Guard e # gs) = do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); quals \<Sigma> \<Gamma> gs }" |
"quals \<Sigma> \<Gamma> (Generator x e # gs) = do {
   \<sigma> \<leftarrow> synth_expr \<Sigma> \<Gamma> e;
   \<tau> \<leftarrow> (case elem_type \<Sigma> \<sigma> of Some \<tau> \<Rightarrow> Inr \<tau> | None \<Rightarrow> Inl (NotIterable \<sigma>));
   ensure (x \<notin> captures gs) (CapturedGeneratorVariable x);
   \<Delta> \<leftarrow> quals \<Sigma> (\<Gamma> \<otimes> fmupd x (Ty \<tau>) fmempty) gs;
   Inr (fmupd x (Ty \<tau>) fmempty \<otimes> \<Delta>)
 }"
by pat_completeness auto

termination
by (relation "measures [\<lambda>x. case x of
     Inl (Inl (_, _, e)) \<Rightarrow> size e
   | Inl (Inr (Inl (_, _, es))) \<Rightarrow> size_list size es
   | Inl (Inr (Inr (_, _, e, _))) \<Rightarrow> size e
   | Inr (Inl (_, _, e, _)) \<Rightarrow> size e
   | Inr (Inr (Inl (_, _, es, _))) \<Rightarrow> size_list size es
   | Inr (Inr (Inr (_, _, gs))) \<Rightarrow> size_list size gs,
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

fun def_signature :: "class_table \<Rightarrow> cxt \<Rightarrow> func \<Rightarrow> reason + ty_scheme"
where
"def_signature \<Sigma> \<Gamma> (Def f \<alpha>s xps \<psi> s) =
   (let \<Gamma>' = \<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar in do {
      \<sigma>s \<leftarrow> those_sum (map (resolve_type \<Sigma> \<Gamma>' \<circ> snd) xps);
      \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma>' \<psi>;
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

(* First of xs in X or occurring earlier in xs *)
fun redeclared :: "var set \<Rightarrow> var list \<Rightarrow> var option"
where
"redeclared X [] = None" |
"redeclared X (x # xs) = (if x \<in> X then Some x else redeclared (insert x X) xs)"

(* Failure of the scope with bound names ys, declared names xs and pattern variables X *)
definition scope_reason :: "var list \<Rightarrow> var list \<Rightarrow> var set \<Rightarrow> reason"
where
"scope_reason ys xs X =
  (case redeclared {} ys of
     Some y \<Rightarrow> DuplicateImportedName y
   | None \<Rightarrow>
       (case redeclared (set ys \<union> X) xs of
          Some x \<Rightarrow> Redeclaration x
        | None \<Rightarrow> Redeclaration (Min (set ys \<inter> X))))"

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

(* Failure for the first assignment target of xs which isn't in X, declared or a pattern variable of Y *)
definition check_assignments_declared :: "var set \<Rightarrow> var list \<Rightarrow> var list \<Rightarrow> var set \<Rightarrow> reason + unit"
where
"check_assignments_declared X xs ys Y =
  (case find (\<lambda>x. x \<notin> X \<and> x \<notin> set ys \<and> x \<notin> Y) xs of
     Some x \<Rightarrow> Inl (UndeclaredAssignment x)
   | None \<Rightarrow> Inr ())"

fun check_stmt :: "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> stmt \<Rightarrow> reason + static_outcome"
and check_elifs :: "class_table \<Rightarrow> cxt \<Rightarrow> ty option \<Rightarrow> (expr \<times> stmt) list \<Rightarrow> (reason + static_outcome) list"
and check_defs :: "class_table \<Rightarrow> cxt \<Rightarrow> func list \<Rightarrow> ty_scheme list \<Rightarrow> reason + unit"
and check_def :: "class_table \<Rightarrow> cxt \<Rightarrow> func \<Rightarrow> ty_scheme \<Rightarrow> reason + unit"
where
"check_stmt \<Sigma> \<Gamma> \<zeta> StmtPass = Inr (Assigns\<^sub>R fmempty)" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtDeclare x \<psi>) = do { \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; Inr (Assigns\<^sub>R (fmupd x (DU \<tau>) fmempty)) }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x None e) =
  (case fmlookup \<Gamma> x of
     Some (DU \<tau>) \<Rightarrow> do { check_expr \<Sigma> \<Gamma> e \<tau>; Inr (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty)) }
   | \<theta> \<Rightarrow> Inl (assign_reason x \<theta>))" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssign x (Some \<psi>) e) = do {
   \<tau> \<leftarrow> resolve_type \<Sigma> \<Gamma> \<psi>; check_expr \<Sigma> \<Gamma> e \<tau>; Inr (Assigns\<^sub>R (fmupd x (Ty \<tau>) fmempty))
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtExpr e) =
  (case synth_expr \<Sigma> \<Gamma> e of
     Inr _ \<Rightarrow> Inr (Assigns\<^sub>R fmempty)
   | Inl r \<Rightarrow>
       (case e of
          ExprCall e' (es, kws) \<Rightarrow>
            (case synth_expr \<Sigma> \<Gamma> e' of
               Inr (TyCallable \<sigma>s (TyPrim NoneType)) \<Rightarrow> do {
                 ensure (kws = []) KeywordArgumentsNotConstructor;
                 ensure (length \<sigma>s = length es) (CallArityMismatch (length \<sigma>s) (length es));
                 check_exprs \<Sigma> \<Gamma> es \<sigma>s;
                 Inr (Assigns\<^sub>R fmempty)
               }
             | _ \<Rightarrow> Inl r)
        | _ \<Rightarrow> Inl r))" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtAssert e e') = do {
   (if e = false_lit then Inr () else check_expr \<Sigma> \<Gamma> e (TyPrim bool));
   (case e' of Some e'' \<Rightarrow> check_expr \<Sigma> \<Gamma> e'' (TyPrim str) | None \<Rightarrow> Inr ());
   Inr (if e = false_lit then Returns\<^sub>R else Assigns\<^sub>R fmempty)
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn None) =
  (case \<zeta> of
     Some \<tau> \<Rightarrow>
       if \<Sigma> \<turnstile> \<tau> \<approx> TyPrim NoneType then Inr Returns\<^sub>R
       else Inl (mypy_only_if (\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>) (BareReturn \<tau>))
   | None \<Rightarrow> undefined)" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtReturn (Some e)) =
  (case \<zeta> of Some \<tau> \<Rightarrow> do { check_expr \<Sigma> \<Gamma> e \<tau>; Inr Returns\<^sub>R } | None \<Rightarrow> undefined)" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtIf e s elifs else') = do {
   check_expr \<Sigma> \<Gamma> e (TyPrim bool);
   merges \<Sigma> (check_stmt \<Sigma> \<Gamma> \<zeta> s # check_elifs \<Sigma> \<Gamma> \<zeta> elifs
           @ [case else' of Some s' \<Rightarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s' | None \<Rightarrow> Inr (Assigns\<^sub>R fmempty)])
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtSeq s s') = do {
   R \<leftarrow> check_stmt \<Sigma> \<Gamma> \<zeta> s;
   case R of
     Assigns\<^sub>R \<Delta> \<Rightarrow> do { R' \<leftarrow> check_stmt \<Sigma> (\<Gamma> \<otimes> \<Delta>) \<zeta> s'; Inr (Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R R') }
   | Returns\<^sub>R \<Rightarrow> Inl UnreachableStatement
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMutualRegion ds) = do {
   \<pi>s \<leftarrow> those_sum (map (def_signature \<Sigma> \<Gamma>) ds);
   let \<Delta> = fmap_of_list (zip (map def_name ds) (map signature_entry \<pi>s));
   check_defs \<Sigma> (\<Gamma> \<otimes> \<Delta>) ds \<pi>s;
   Inr (Assigns\<^sub>R \<Delta>)
 }" |
"check_stmt \<Sigma> \<Gamma> \<zeta> (StmtMatch e bs) = undefined" |

"check_elifs \<Sigma> \<Gamma> \<zeta> [] = []" |
"check_elifs \<Sigma> \<Gamma> \<zeta> ((e, s) # elifs) =
  (do { check_expr \<Sigma> \<Gamma> e (TyPrim bool); check_stmt \<Sigma> \<Gamma> \<zeta> s }) # check_elifs \<Sigma> \<Gamma> \<zeta> elifs" |

"check_defs \<Sigma> \<Gamma> [] [] = Inr ()" |
"check_defs \<Sigma> \<Gamma> (d # ds) (\<pi> # \<pi>s) = do { check_def \<Sigma> \<Gamma> d \<pi>; check_defs \<Sigma> \<Gamma> ds \<pi>s }" |
"check_defs \<Sigma> \<Gamma> _ _ = undefined" |

"check_def \<Sigma> \<Gamma> (Def f \<alpha>s xps \<psi> s) (TyScheme \<alpha>s' (TyCallable \<sigma>s \<tau>)) =
  (let xs = map fst xps in do {
     check_assignments_declared (set xs) (assign_targets s) (declares s) (binds s);
     \<Delta> \<leftarrow> (case scope Unbound xs s of Some \<Delta> \<Rightarrow> Inr \<Delta> | None \<Rightarrow> Inl (scope_reason xs (declares s) (binds s)));
     if length xs = length \<sigma>s then do {
       R \<leftarrow> check_stmt \<Sigma> (\<Gamma> \<otimes> fmconst (set \<alpha>s) TypeVar \<otimes> fmap_of_list (zip xs (map Ty \<sigma>s)) \<otimes> \<Delta>) (Some \<tau>) s;
       if R = Returns\<^sub>R \<or> \<Sigma> \<turnstile> \<tau> \<approx> TyPrim NoneType then Inr ()
       else Inl (mypy_only_if (\<Sigma> \<turnstile> TyPrim NoneType <: \<tau>) (MissingReturn f \<tau>))
     }
     else Inl undefined
   })" |
"check_def \<Sigma> \<Gamma> _ _ = undefined"

abbreviation name_binding :: "var \<times> cxt_entry" where "name_binding \<equiv> (''__name__'', Ty (TyPrim str))"

definition predefined :: "(name, cxt) fmap"
where
"predefined = fmap_of_list
  [(builtins, fmap_of_list
     ([name_binding,
       (''print'', Ty (TyCallable [TyPrim object] (TyPrim NoneType))),
       (''len'', Ty (TyCallable [TyPrim Sized] (TyPrim int))),
       (''range'', Type range_class),
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

fun check_top_stmt :: "class_table \<Rightarrow> cxt \<Rightarrow> top_stmt \<Rightarrow> reason + static_outcome \<times> class_table"
where
"check_top_stmt \<Sigma> \<Gamma> (Stmt s) = do { R \<leftarrow> check_stmt \<Sigma> \<Gamma> None s; Inr (R, \<Sigma>) }" |
"check_top_stmt \<Sigma> \<Gamma> (TopSeq t t') = do {
   (R, \<Sigma>') \<leftarrow> check_top_stmt \<Sigma> \<Gamma> t;
   case R of
     Assigns\<^sub>R \<Delta> \<Rightarrow> do {
       (R', \<Sigma>'') \<leftarrow> check_top_stmt \<Sigma>' (\<Gamma> \<otimes> \<Delta>) t';
       Inr (Assigns\<^sub>R \<Delta> \<otimes>\<^sub>R R', \<Sigma>'')
     }
   | Returns\<^sub>R \<Rightarrow> Inl TopLevelAssertFalse
 }" |
"check_top_stmt \<Sigma> \<Gamma> (TypeDefs \<chi>s) = undefined"

definition known_module :: "program \<Rightarrow> name \<Rightarrow> bool"
where
"known_module M q = (q |\<in>| fmdom M \<or> q |\<in>| fmdom predefined)"

definition predefined_classes :: class_table
where
"predefined_classes =
  fmupd range_class
    (ClassDef (the (fmlookup predefined builtins)) builtins
      [Dataclass ''range'' [] None [(''start'', TyExprPrim int), (''stop'', TyExprPrim int)]] 0)
    fmempty"

(* V holds the modules being checked, in order, so that an import cycle is rejected; a failure is paired
   with the module in which it occurs *)
function (sequential)
  check_module :: "program \<Rightarrow> name list \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> (name \<times> reason) + cxt \<times> class_table" and
  check_imports ::
    "program \<Rightarrow> name list \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> import list \<Rightarrow> (name \<times> reason) + cxt \<times> class_table" and
  submodules ::
    "program \<Rightarrow> name list \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> cxt_entry \<Rightarrow> var list
     \<Rightarrow> (name \<times> reason) + cxt_entry \<times> class_table" and
  imports_entry ::
    "program \<Rightarrow> name list \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> name \<Rightarrow> cxt \<Rightarrow> var
     \<Rightarrow> (name \<times> reason) + cxt_entry \<times> class_table" and
  imports_entries ::
    "program \<Rightarrow> name list \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> name \<Rightarrow> cxt \<Rightarrow> var list
     \<Rightarrow> (name \<times> reason) + cxt_entry list \<times> class_table" and
  check_modules :: "program \<Rightarrow> name list \<Rightarrow> class_table \<Rightarrow> name list \<Rightarrow> (name \<times> reason) + class_table"
where
"check_module M V \<Sigma> q =
  (case fmlookup predefined q of
     Some \<Gamma> \<Rightarrow> Inr (\<Gamma>, \<Sigma>)
   | None \<Rightarrow>
     if q \<in> set V then Inl (q, ImportCycle (dropWhile (\<lambda>q'. q' \<noteq> q) V @ [q]))
     else case fmlookup M q of
       None \<Rightarrow> undefined
     | Some (ModuleBody \<iota>s t) \<Rightarrow> do {
         (\<Gamma>', \<Sigma>') \<leftarrow> check_imports M (V @ [q]) \<Sigma> q \<iota>s;
         \<Gamma>\<^sub>s \<leftarrow> map_sum (Pair q) id
           (case scope Unbound (declares \<iota>s) t of
              Some \<Gamma>\<^sub>s \<Rightarrow> Inr \<Gamma>\<^sub>s
            | None \<Rightarrow> Inl (scope_reason (declares \<iota>s) (declares t) (binds t)));
         map_sum (Pair q) id (check_assignments_declared {} (assign_targets_top t) (declares t) (binds t));
         (R, \<Sigma>'') \<leftarrow> map_sum (Pair q) id (check_top_stmt \<Sigma>' (the (fmlookup predefined builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t);
         case R of
           Assigns\<^sub>R \<Delta> \<Rightarrow>
             let S = submods M q; X = (fmdom \<Gamma>' |\<union>| fmdom \<Delta>) |\<inter>| fmdom S in
             if X = {||} then Inr (S \<otimes> \<Delta>, \<Sigma>'') else Inl (q, DuplicateMember (Min (fset X)) q)
         | Returns\<^sub>R \<Rightarrow> Inl (q, TopLevelAssertFalse)
       })" |
"check_imports M V \<Sigma> q [] = Inr (fmempty, \<Sigma>)" |
"check_imports M V \<Sigma> q (Import (x, xs) # \<iota>s) = do {
   ensure (\<not> q \<prec> (x, xs)) (q, ImportOfContainedModule (x, xs) q);
   ensure (known_module M (x, [])) (q, UnknownModule (x, []));
   (\<Delta>, \<Sigma>\<^sub>1) \<leftarrow> check_module M V \<Sigma> (x, []);
   (\<theta>, \<Sigma>\<^sub>2) \<leftarrow> submodules M V \<Sigma>\<^sub>1 q (ModChecked (x, []) \<Delta>) xs;
   (\<Gamma>, \<Sigma>') \<leftarrow> check_imports M V \<Sigma>\<^sub>2 q \<iota>s;
   Inr (fmupd x \<theta> fmempty \<uplus> \<Gamma>, \<Sigma>')
 }" |
"check_imports M V \<Sigma> q (FromImport q' xs # \<iota>s) = do {
   ensure (known_module M q') (q, UnknownModule q');
   (\<Delta>, \<Sigma>\<^sub>1) \<leftarrow> check_module M V \<Sigma> q';
   \<Sigma>\<^sub>2 \<leftarrow> check_modules M V \<Sigma>\<^sub>1 (unique_to q' q);
   (case redeclared {} xs of Some x \<Rightarrow> Inl (q, DuplicateImportedName x) | None \<Rightarrow> Inr ());
   (\<theta>s, \<Sigma>\<^sub>3) \<leftarrow> imports_entries M V \<Sigma>\<^sub>2 q q' \<Delta> xs;
   (\<Gamma>, \<Sigma>') \<leftarrow> check_imports M V \<Sigma>\<^sub>3 q \<iota>s;
   Inr (fmap_of_list (zip xs \<theta>s) \<uplus> \<Gamma>, \<Sigma>')
 }" |
"submodules M V \<Sigma> q \<theta> [] = Inr (\<theta>, \<Sigma>)" |
"submodules M V \<Sigma> q (ModChecked q' \<Gamma>) (x # xs) = do {
   ensure (known_module M (snoc q' x)) (q, UnknownModule (snoc q' x));
   (\<Gamma>', \<Sigma>\<^sub>1) \<leftarrow> check_module M V \<Sigma> (snoc q' x);
   (\<theta>', \<Sigma>') \<leftarrow> submodules M V \<Sigma>\<^sub>1 q (ModChecked (snoc q' x) \<Gamma>') xs;
   Inr (ModChecked q' (\<Gamma> \<uplus> fmupd x \<theta>' fmempty), \<Sigma>')
 }" |
"submodules M V \<Sigma> q _ _ = undefined" |
"imports_entry M V \<Sigma> q q' \<Gamma> x =
  (case fmlookup \<Gamma> x of
     Some (ModStub q'') \<Rightarrow> do { (\<Gamma>', \<Sigma>') \<leftarrow> check_module M V \<Sigma> q''; Inr (ModChecked q'' \<Gamma>', \<Sigma>') }
   | \<theta> \<Rightarrow>
       (case resolve_name \<Gamma> (x, []) of
          Some \<theta>' \<Rightarrow> Inr (\<theta>', \<Sigma>)
        | None \<Rightarrow> Inl (q, case \<theta> of None \<Rightarrow> UnknownMember x q' | Some _ \<Rightarrow> UnassignedMember x q')))" |
"imports_entries M V \<Sigma> q q' \<Gamma> [] = Inr ([], \<Sigma>)" |
"imports_entries M V \<Sigma> q q' \<Gamma> (x # xs) = do {
   (\<theta>, \<Sigma>\<^sub>1) \<leftarrow> imports_entry M V \<Sigma> q q' \<Gamma> x;
   (\<theta>s, \<Sigma>') \<leftarrow> imports_entries M V \<Sigma>\<^sub>1 q q' \<Gamma> xs;
   Inr (\<theta> # \<theta>s, \<Sigma>')
 }" |
"check_modules M V \<Sigma> [] = Inr \<Sigma>" |
"check_modules M V \<Sigma> (q # qs) = do { (_, \<Sigma>\<^sub>1) \<leftarrow> check_module M V \<Sigma> q; check_modules M V \<Sigma>\<^sub>1 qs }"
by pat_completeness auto

(* Measures: count of modules of M not in V; then a topological rank of the call graph, which is acyclic
   if we remove the call from the module rule to its imports; then the length of the list argument *)
termination
by (relation "measures [
     \<lambda>x. case x of
       Inl (Inl (M, V, _)) \<Rightarrow> card (fmdom' M - set V)
     | Inl (Inr (Inl (M, V, _))) \<Rightarrow> card (fmdom' M - set V)
     | Inl (Inr (Inr (M, V, _))) \<Rightarrow> card (fmdom' M - set V)
     | Inr (Inl (M, V, _)) \<Rightarrow> card (fmdom' M - set V)
     | Inr (Inr (Inl (M, V, _))) \<Rightarrow> card (fmdom' M - set V)
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
     | Inl (Inr (Inl (_, _, _, _, \<iota>s))) \<Rightarrow> length \<iota>s
     | Inl (Inr (Inr (_, _, _, _, _, xs))) \<Rightarrow> length xs
     | Inr (Inl _) \<Rightarrow> 0
     | Inr (Inr (Inl (_, _, _, _, _, _, xs))) \<Rightarrow> length xs
     | Inr (Inr (Inr (_, _, _, qs))) \<Rightarrow> length qs]")
   (auto simp: card_fmdom_insert)

definition check_program :: "program \<Rightarrow> (name \<times> reason) option"
where
"check_program M =
  (case check_module M [] predefined_classes main of Inl f \<Rightarrow> Some f | Inr _ \<Rightarrow> None)"

end
