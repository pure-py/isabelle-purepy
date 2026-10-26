theory Reasons
  imports Contexts
begin

datatype sequence_kind = TupleKind | ListKind | RangeKind

(* Reasons for ill-formedness *)
datatype reason =
    DuplicateField var var
  | InheritedField var var var
  | UndefinedVariable var
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
  | ConstructorArityMismatch var nat nat
  | UnknownConstructorKeyword var "var list"
  | PatternArityMismatch var nat nat
  | UnknownFieldInPattern var "var list"
  | RangePattern
  | PatternClassUndetermined var ty
  | SequenceKindMismatch sequence_kind ty sequence_kind
  | UnreachableCase pat
  | MissingReturnMatchPartial ty
  | MissingReturnAssertion
  | NotPredefinedName var
  | NotClass name
  | ClassArityMismatch name nat nat
  | TypeAliasArityMismatch name nat nat
  | CyclicTypeAlias var
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
  | NoTypeArgument var
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
  | UnknownField var var
  | NoAttributes ty
  | BareReturn ty
  | MissingReturn var ty
  | ImportCycle "name list"
  | MypyCompatibility reason

definition not_type_name :: "cxt \<Rightarrow> name \<Rightarrow> reason"
where
"not_type_name \<Gamma> q = (case lookup \<Gamma> q of Some Unbound \<Rightarrow> UnboundName (fst q) | _ \<Rightarrow> NotClass q)"

(* Failure for variable x, which isn't bound at a type, by context entry *)
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

(* Failure for an assignment to x, by context entry, when x isn't definitely unassigned *)
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

(* Reason why none of the expressions synthesises a type: the first failure of an expression with a synthesis
   rule *)
fun synth_failure :: "(reason + 'a) list \<Rightarrow> reason"
where
"synth_failure [] = NotSynthesised" |
"synth_failure (Inl NotSynthesised # ms) = synth_failure ms" |
"synth_failure (Inl r # ms) = r" |
"synth_failure (Inr _ # ms) = synth_failure ms"

end
