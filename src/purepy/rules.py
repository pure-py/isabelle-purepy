"""Rules of the specification whose premises the reasons of the generated type checker enforce, named as the
conformance suite cites them"""

from .generated import Reasons, Syntax
from .syntax import Reason

# By the reason alone, where one rule raises it
RULES: dict[type, str] = {
    Reasons.DuplicateField: "class",
    Reasons.InheritedField: "class-extend",
    Reasons.UndefinedVariable: "var",
    Reasons.UnassignedVariable: "var",
    Reasons.PossiblyUnassigned: "var",
    Reasons.TypeParameterAsValue: "var",
    Reasons.AssignmentBeforeDeclaration: "assign",
    Reasons.Reassignment: "assign",
    Reasons.PossibleReassignment: "assign",
    Reasons.UnreachableStatement: "seq",
    Reasons.ReturnOutsideFunction: "return",
    Reasons.ConstructorArityMismatch: "constr",
    Reasons.UnknownConstructorKeyword: "constr",
    Reasons.PatternArityMismatch: "check-constr",
    Reasons.UnknownFieldInPattern: "check-constr",
    Reasons.RangePattern: "check-constr",
    Reasons.PatternClassUndetermined: "check-constr",
    Reasons.UnreachableCase: "match-case",
    Reasons.MissingReturnMatchPartial: "match-partial",
    Reasons.MissingReturnAssertion: "assert",
    Reasons.NotTypeExpression: "constr-explicit",
    Reasons.ClassArityMismatch: "ty-class",
    Reasons.TypeAliasArityMismatch: "ty-alias",
    Reasons.CyclicTypeAlias: "ty-alias",
    Reasons.DuplicateMember: "module",
    Reasons.SubmoduleNotImported: "attr-module",
    Reasons.TopLevelAssertFalse: "top-seq",
    Reasons.PrintInFunction: "print",
    Reasons.ImportCycle: "module",
    Reasons.ImportOfContainedModule: "import",
    Reasons.NoBinaryOverload: "binop",
    Reasons.NoUnaryOverload: "unop",
    Reasons.NotCallable: "call",
    Reasons.NoneResult: "call",
    Reasons.LambdaTypeMismatch: "lambda",
    Reasons.NotSubscriptable: "subscript-list",
    Reasons.TupleIndexOutOfRange: "subscript-tuple",
    Reasons.NotIterable: "qual-generator",
    Reasons.NotSynthesised: "check-syn",
    Reasons.UnknownField: "attr-object",
    Reasons.NoAttributes: "attr-object",
    Reasons.BareReturn: "return-none",
    Reasons.MissingReturn: "def-body",
    Reasons.NotPredefinedName: "class",
    Reasons.CapturedGeneratorVariable: "list-comp",
    Reasons.KeywordArgumentsNotConstructor: "call",
    Reasons.CallArityMismatch: "call",
    Reasons.TypeMismatch: "check-syn",
    Reasons.NoTypeArgument: "constr",
    Reasons.ModuleAsValue: "var",
    Reasons.ClassAsValue: "var",
    Reasons.TypeAliasAsValue: "var",
    Reasons.PredefinedNameAsValue: "var",
    Reasons.TypeSchemeAsValue: "var",
    Reasons.UnboundName: "var",
}

# By the judgement wrapped nearest to the reason, which raises it under a rule other than the one above
RULES_UNDER: dict[tuple[type, type], str] = {
    (Reasons.InModuleAttribute, Reasons.ModuleAsValue): "attr-module",
    (Reasons.InModuleAttribute, Reasons.ClassAsValue): "attr-module",
    (Reasons.InModuleAttribute, Reasons.TypeAliasAsValue): "attr-module",
    (Reasons.InModuleAttribute, Reasons.PredefinedNameAsValue): "attr-module",
    (Reasons.InModuleAttribute, Reasons.TypeSchemeAsValue): "attr-module",
    (Reasons.InModuleAttribute, Reasons.UnknownMember): "attr-module",
    (Reasons.InModuleAttribute, Reasons.UnassignedMember): "attr-module",
    (Reasons.InImportedName, Reasons.UnknownMember): "imp-member",
    (Reasons.InImportedName, Reasons.UnassignedMember): "imp-member",
    (Reasons.InImport, Reasons.UnknownModule): "import",
    (Reasons.InImport, Reasons.DuplicateImportedName): "from-import",
    (Reasons.InModule, Reasons.DuplicateImportedName): "module",
    (Reasons.InModule, Reasons.Redeclaration): "module",
    (Reasons.InModule, Reasons.UndeclaredAssignment): "module",
    (Reasons.InModule, Reasons.TopLevelAssertFalse): "module",
    (Reasons.InTypeExpression, Reasons.UnboundName): "ty-class",
    (Reasons.InTypeExpression, Reasons.NotClass): "ty-class",
    (Reasons.InTypeExpression, Reasons.NotPredefinedName): "ty-name",
    (Reasons.InPattern, Reasons.NotClass): "check-constr",
    (Reasons.InIf, Reasons.Redeclaration): "if-else",
    (Reasons.InMatch, Reasons.Redeclaration): "match",
    (Reasons.InSignature, Reasons.Redeclaration): "def-signature",
    (Reasons.InDeclaration, Reasons.Redeclaration): "declare",
    (Reasons.InDefs, Reasons.Redeclaration): "defs",
    (Reasons.InBody, Reasons.Redeclaration): "def-body",
    (Reasons.InBody, Reasons.UndeclaredAssignment): "def-body",
    (Reasons.InAssignment, Reasons.Redeclaration): "assign",
    (Reasons.InAssignment, Reasons.UndeclaredAssignment): "assign",
    (Reasons.InScheme, Reasons.TypeMismatch): "var-scheme",
    (Reasons.InScheme, Reasons.NoTypeArgument): "var-scheme",
    (Reasons.InCallee, Reasons.NoTypeArgument): "callee-scheme",
    (Reasons.InSubscript, Reasons.TypeMismatch): "subscript-tuple",
    (Reasons.InLambdaCall, Reasons.KeywordArgumentsNotConstructor): "call-lambda",
    (Reasons.InLambdaCall, Reasons.CallArityMismatch): "call-lambda",
    (Reasons.InGenerator, Reasons.CapturedGeneratorVariable): "qual-generator",
}

WRAPPERS = {wrapper for wrapper, _ in RULES_UNDER}


def rules_cited() -> set[str]:
    return {*RULES.values(), *RULES_UNDER.values(), "check-tuple", "check-list"}


def spine(r: Reason) -> tuple[list[type], Reason]:
    """Judgements wrapped around r, outermost first, and the reason within them"""
    match r:
        case Reasons.Located(_, r_) | Reasons.MypyCompatibility(r_):
            return spine(r_)
        case _ if type(r) in WRAPPERS:
            wrappers, bare = spine(r.a)
            return ([type(r), *wrappers], bare)
        case _:
            return ([], r)


def rule(r: Reason) -> str:
    wrappers, bare = spine(r)
    match bare:
        case Reasons.SequenceKindMismatch(Syntax.TupleKind(), _, _):
            return "check-tuple"
        case Reasons.SequenceKindMismatch():
            return "check-list"
    for wrapper in reversed(wrappers):
        if (wrapper, type(bare)) in RULES_UNDER:
            return RULES_UNDER[(wrapper, type(bare))]
    return RULES[type(bare)]
