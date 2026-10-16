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

(* Context entry for a variable at \<tau>, or absent *)
fun cxt_entry_at :: "cxt_entry option \<Rightarrow> ty \<Rightarrow> bool"
where
"cxt_entry_at None \<tau> = True" |
"cxt_entry_at (Some (Ty \<tau>')) \<tau> = (\<tau>' = \<tau>)" |
"cxt_entry_at (Some (DU \<tau>')) \<tau> = (\<tau>' = \<tau>)" |
"cxt_entry_at (Some (PU \<tau>')) \<tau> = (\<tau>' = \<tau>)" |
"cxt_entry_at _ _ = False"

fun scheme_cxt_entry_at :: "cxt_entry option \<Rightarrow> scheme \<Rightarrow> bool"
where
"scheme_cxt_entry_at None \<pi> = True" |
"scheme_cxt_entry_at (Some (Scheme \<pi>')) \<pi> = (\<pi>' = \<pi>)" |
"scheme_cxt_entry_at (Some (PUScheme \<pi>')) \<pi> = (\<pi>' = \<pi>)" |
"scheme_cxt_entry_at _ _ = False"

definition merge_cxt_entry :: "cxt_entry option \<Rightarrow> cxt_entry option \<Rightarrow> cxt_entry option option"
where
"merge_cxt_entry \<theta> \<theta>' =
  (if \<theta> = \<theta>' then Some \<theta>
    else if \<exists>\<tau>. cxt_entry_at \<theta> \<tau> \<and> cxt_entry_at \<theta>' \<tau>
    then Some (Some (PU (THE \<tau>. cxt_entry_at \<theta> \<tau> \<and> cxt_entry_at \<theta>' \<tau>)))
   else if \<exists>\<pi>. scheme_cxt_entry_at \<theta> \<pi> \<and> scheme_cxt_entry_at \<theta>' \<pi>
   then Some (Some (PUScheme (THE \<pi>. scheme_cxt_entry_at \<theta> \<pi> \<and> scheme_cxt_entry_at \<theta>' \<pi>)))
   else None)"

definition merge :: "cxt \<Rightarrow> cxt \<Rightarrow> cxt option" (infixl "\<oplus>" 65)
where
"\<Gamma> \<oplus> \<Gamma>' =
  (if \<forall>x. merge_cxt_entry (\<Gamma> x) (\<Gamma>' x) \<noteq> None then Some (\<lambda>x. the (merge_cxt_entry (\<Gamma> x) (\<Gamma>' x))) else None)"

datatype static_outcome = Assigns\<^sub>R cxt | Returns\<^sub>R

fun merge_outcome :: "static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome option" (infixl "\<oplus>\<^sub>R" 65)
where
"Assigns\<^sub>R \<Delta> \<oplus>\<^sub>R Assigns\<^sub>R \<Delta>' = map_option Assigns\<^sub>R (\<Delta> \<oplus> \<Delta>')" |
"R \<oplus>\<^sub>R Returns\<^sub>R = Some R" |
"Returns\<^sub>R \<oplus>\<^sub>R R = Some R"

fun override_outcome :: "static_outcome \<Rightarrow> static_outcome \<Rightarrow> static_outcome" (infixl "++\<^sub>R" 100)
where
"Assigns\<^sub>R \<Delta> ++\<^sub>R Assigns\<^sub>R \<Delta>' = Assigns\<^sub>R (\<Delta> ++ \<Delta>')" |
"_ ++\<^sub>R _ = Returns\<^sub>R"

abbreviation prim :: "prim_ty \<Rightarrow> ty" where "prim \<equiv> TyPrim"

fun base_type_lit :: "lit \<Rightarrow> ty"
where
"base_type_lit (LitInt _) = prim TyInt" |
"base_type_lit (LitFloat _) = prim TyFloat" |
"base_type_lit (LitString _) = prim TyStr" |
"base_type_lit (LitBool _) = prim TyBool" |
"base_type_lit LitNone = prim TyNone"

fun base_type :: "ty \<Rightarrow> ty"
where
"base_type (TyLiteral l) = base_type_lit l" |
"base_type \<tau> = \<tau>"

fun sized :: "ty \<Rightarrow> bool"
where
"sized (TyList _) = True" |
"sized (TyDict _) = True" |
"sized (prim TyStr) = True" |
"sized (TyTuple _) = True" |
"sized _ = False"

inductive subty :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "<:" 50)
where
SubtyRefl: "\<tau> <: \<tau>" |
SubtyNever: "prim TyNever <: \<tau>" |
SubtyObject: "\<tau> <: prim TyObject" |
SubtyIntFloat: "prim TyInt <: prim TyFloat" |
SubtySized: "sized \<tau> \<Longrightarrow> \<tau> <: prim TySized" |
SubtyList: "\<lbrakk> \<sigma> <: \<tau> ; \<tau> <: \<sigma> \<rbrakk> \<Longrightarrow> TyList \<sigma> <: TyList \<tau>" |
SubtyDict: "\<lbrakk> \<sigma> <: \<tau> ; \<tau> <: \<sigma> \<rbrakk> \<Longrightarrow> TyDict \<sigma> <: TyDict \<tau>" |
SubtyCallable: "\<lbrakk> list_all2 (\<lambda>\<tau> \<sigma>. \<tau> <: \<sigma>) \<tau>s \<sigma>s ; \<sigma> <: \<tau> \<rbrakk> \<Longrightarrow> TyCallable \<sigma>s \<sigma> <: TyCallable \<tau>s \<tau>" |
SubtyTuple: "list_all2 (\<lambda>\<sigma> \<tau>. \<sigma> <: \<tau>) \<sigma>s \<tau>s \<Longrightarrow> TyTuple \<sigma>s <: TyTuple \<tau>s" |
SubtyLiteral: "base_type_lit l <: \<tau> \<Longrightarrow> TyLiteral l <: \<tau>" |
SubtyUnionLeft: "\<sigma> <: \<tau> \<Longrightarrow> \<sigma> <: TyUnion \<tau> \<tau>'" |
SubtyUnionRight: "\<sigma> <: \<tau>' \<Longrightarrow> \<sigma> <: TyUnion \<tau> \<tau>'" |
SubtyUnion: "\<lbrakk> \<tau> <: \<sigma> ; \<tau>' <: \<sigma> \<rbrakk> \<Longrightarrow> TyUnion \<tau> \<tau>' <: \<sigma>"

abbreviation equiv :: "ty \<Rightarrow> ty \<Rightarrow> bool" (infix "\<approx>" 50) where "\<sigma> \<approx> \<tau> \<equiv> \<sigma> <: \<tau> \<and> \<tau> <: \<sigma>"

definition join :: "ty \<Rightarrow> ty \<Rightarrow> ty" (infixl "\<squnion>" 65)
where
"\<sigma> \<squnion> \<tau> = (if \<sigma> <: \<tau> then \<tau> else if \<tau> <: \<sigma> then \<sigma> else TyUnion \<sigma> \<tau>)"

definition joins :: "ty list \<Rightarrow> ty"
where
"joins \<tau>s = foldr (\<squnion>) \<tau>s (prim TyNever)"

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
   else if length \<sigma>s = length \<tau>s then TyCallable (map2 (\<squnion>) \<sigma>s \<tau>s) (\<sigma> \<sqinter> \<tau>) else prim TyNever)" |
"TyTuple \<sigma>s \<sqinter> TyTuple \<tau>s =
  (if TyTuple \<sigma>s <: TyTuple \<tau>s then TyTuple \<sigma>s else if TyTuple \<tau>s <: TyTuple \<sigma>s then TyTuple \<tau>s
   else if length \<sigma>s = length \<tau>s then TyTuple (meets \<sigma>s \<tau>s) else prim TyNever)" |
"\<sigma> \<sqinter> \<tau> = (if \<sigma> <: \<tau> then \<sigma> else if \<tau> <: \<sigma> then \<tau> else prim TyNever)" |

"meets (\<sigma> # \<sigma>s) (\<tau> # \<tau>s) = (\<sigma> \<sqinter> \<tau>) # meets \<sigma>s \<tau>s" |
"meets _ _ = []"

fun prim_name :: "prim_ty \<Rightarrow> var"
where
"prim_name TyObject = ''object''" |
"prim_name TyNever = ''Never''" |
"prim_name TyNone = ''None''" |
"prim_name TyBool = ''bool''" |
"prim_name TyInt = ''int''" |
"prim_name TyFloat = ''float''" |
"prim_name TyStr = ''str''" |
"prim_name TySized = ''Sized''"

abbreviation predef :: "cxt \<Rightarrow> var \<Rightarrow> bool" where "predef \<Gamma> x \<equiv> \<Gamma> x = Some PredefName"

fun resolve_type :: "cxt \<Rightarrow> ty_expr \<Rightarrow> ty option"
where
"resolve_type \<Gamma> (TyExprPrim \<nu>) = (if predef \<Gamma> (prim_name \<nu>) then Some (prim \<nu>) else None)" |
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

fun eq_type :: "ty \<Rightarrow> bool"
where
"eq_type (prim _) = True" |
"eq_type (TyLiteral _) = True" |
"eq_type (TyList \<tau>) = eq_type \<tau>" |
"eq_type (TyDict \<tau>) = eq_type \<tau>" |
"eq_type (TyTuple \<tau>s) = list_all eq_type \<tau>s" |
"eq_type (TyUnion \<sigma> \<tau>) = (eq_type \<sigma> \<and> eq_type \<tau>)" |
"eq_type _ = False"

abbreviation comparable :: "ty \<Rightarrow> ty \<Rightarrow> bool" where "comparable \<sigma> \<tau> \<equiv> \<sigma> <: \<tau> \<or> \<tau> <: \<sigma>"

abbreviation bool where "bool \<equiv> prim TyBool"
abbreviation int where "int \<equiv> prim TyInt"
abbreviation float where "float \<equiv> prim TyFloat"
abbreviation str where "str \<equiv> prim TyStr"

fun resolve_binop :: "bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty option"
where
"resolve_binop op \<sigma> \<sigma>' =
  (if op \<in> {BOpEq, BOpNeq} then (if eq_type \<sigma> \<and> eq_type \<sigma>' \<and> comparable \<sigma> \<sigma>' then Some bool else None)
   else if op \<in> {BOpIn, BOpNotIn} then
     (case \<sigma>' of
        TyList \<tau> \<Rightarrow> if comparable \<sigma> \<tau> then Some bool else None
      | TyTuple \<tau>s \<Rightarrow> if comparable \<sigma> (joins \<tau>s) then Some bool else None
      | TyDict _ \<Rightarrow> if \<sigma> <: str then Some bool else None
      | _ \<Rightarrow> if \<sigma> <: str \<and> \<sigma>' <: str then Some bool else None)
   else if op \<in> {BOpLt, BOpLeq, BOpGt, BOpGeq} then
     (if \<sigma> <: float \<and> \<sigma>' <: float \<or> \<sigma> <: str \<and> \<sigma>' <: str then Some bool else None)
   else if op = BOpPow \<and> (\<exists>n. \<sigma>' = TyLiteral (LitInt n)) \<and> \<sigma> <: int then
     Some (if (\<exists>n \<ge> 0. \<sigma>' = TyLiteral (LitInt n)) then int else float)
   else if op \<in> {BOpAdd, BOpSub, BOpMul, BOpFloorDiv, BOpMod} \<and> \<sigma> <: int \<and> \<sigma>' <: int then Some int
   else if op \<in> {BOpAdd, BOpSub, BOpMul, BOpFloorDiv, BOpMod, BOpDiv, BOpPow} \<and> \<sigma> <: float \<and> \<sigma>' <: float
   then Some float
   else if op = BOpAdd \<and> \<sigma> <: str \<and> \<sigma>' <: str then Some str
   else case (op, \<sigma>, \<sigma>') of
     (BOpAdd, TyList \<tau>, TyList \<tau>') \<Rightarrow> Some (TyList (\<tau> \<squnion> \<tau>'))
   | (BOpAdd, TyTuple \<tau>s, TyTuple \<tau>s') \<Rightarrow> Some (TyTuple (\<tau>s @ \<tau>s'))
   | (BOpMul, TyList \<tau>, _) \<Rightarrow> if \<sigma>' <: int then Some (TyList \<tau>) else None
   | (BOpMul, _, TyList \<tau>) \<Rightarrow> if \<sigma> <: int then Some (TyList \<tau>) else None
   | (BOpMul, _, _) \<Rightarrow> if \<sigma> <: str \<and> \<sigma>' <: int \<or> \<sigma> <: int \<and> \<sigma>' <: str then Some str else None
   | _ \<Rightarrow> None)"

fun resolve_unop :: "uop \<Rightarrow> ty \<Rightarrow> ty option"
where
"resolve_unop UOpNot \<sigma> = (if \<sigma> <: bool then Some bool else None)" |
"resolve_unop _ \<sigma> = (if \<sigma> <: int then Some int else if \<sigma> <: float then Some float else None)"

fun number_literal :: "expr \<Rightarrow> bool"
where
"number_literal (ExprLiteral (LitInt _)) = True" |
"number_literal (ExprLiteral (LitFloat _)) = True" |
"number_literal _ = False"

abbreviation bind_params :: "cxt \<Rightarrow> var list \<Rightarrow> ty list \<Rightarrow> cxt"
where "bind_params \<Gamma> xs \<tau>s \<equiv> \<Gamma> ++ map_of (zip xs (map Ty \<tau>s))"


function (sequential)
  synth :: "cxt \<Rightarrow> expr \<Rightarrow> ty option" and
  synths :: "cxt \<Rightarrow> expr list \<Rightarrow> ty option list" and
  check :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" and
  check_intro :: "cxt \<Rightarrow> expr \<Rightarrow> ty \<Rightarrow> bool" and
  checks :: "cxt \<Rightarrow> expr list \<Rightarrow> ty list \<Rightarrow> bool" and
  checks_missing :: "cxt \<Rightarrow> expr list \<Rightarrow> ty option list \<Rightarrow> ty \<Rightarrow> bool"
where
"synth \<Gamma> (ExprVar x) = (case \<Gamma> x of Some (Ty \<tau>) \<Rightarrow> Some \<tau> | _ \<Rightarrow> None)" |
"synth \<Gamma> (ExprLiteral l) = (case l of LitFloat _ \<Rightarrow> Some float | _ \<Rightarrow> Some (TyLiteral l))" |
"synth \<Gamma> (ExprCall e (es, kws)) =
  (if kws \<noteq> [] then None
   else case e of
     ExprLambda xs e' \<Rightarrow>
       (case those (synths \<Gamma> es) of
          Some \<tau>s \<Rightarrow> if distinct xs \<and> length xs = length es then synth (bind_params \<Gamma> xs \<tau>s) e' else None
        | None \<Rightarrow> None)
   | _ \<Rightarrow>
       (case synth \<Gamma> e of
          Some (TyCallable \<sigma>s \<sigma>) \<Rightarrow> if \<sigma> \<noteq> prim TyNone \<and> checks \<Gamma> es \<sigma>s then Some \<sigma> else None
        | _ \<Rightarrow> None))" |
"synth \<Gamma> (ExprBinOp op e e') =
  (case (synth \<Gamma> e, synth \<Gamma> e') of (Some \<sigma>, Some \<sigma>') \<Rightarrow> resolve_binop op \<sigma> \<sigma>' | _ \<Rightarrow> None)" |
"synth \<Gamma> (ExprUnOp op e) =
  (if op = UOpNeg \<and> number_literal e then None
   else case synth \<Gamma> e of Some \<sigma> \<Rightarrow> resolve_unop op \<sigma> | None \<Rightarrow> None)" |
"synth \<Gamma> (ExprAnd e e') = (if check \<Gamma> e bool \<and> check \<Gamma> e' bool then Some bool else None)" |
"synth \<Gamma> (ExprOr e e') = (if check \<Gamma> e bool \<and> check \<Gamma> e' bool then Some bool else None)" |
"synth \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) =
  (if check \<Gamma> e bool then
     case (synth \<Gamma> e\<^sub>1, synth \<Gamma> e\<^sub>2) of
       (Some \<sigma>\<^sub>1, Some \<sigma>\<^sub>2) \<Rightarrow> Some (\<sigma>\<^sub>1 \<squnion> \<sigma>\<^sub>2)
     | (Some \<sigma>\<^sub>1, None) \<Rightarrow> if check \<Gamma> e\<^sub>2 \<sigma>\<^sub>1 then Some \<sigma>\<^sub>1 else None
     | (None, Some \<sigma>\<^sub>2) \<Rightarrow> if check \<Gamma> e\<^sub>1 \<sigma>\<^sub>2 then Some \<sigma>\<^sub>2 else None
     | _ \<Rightarrow> None
   else None)" |
"synth \<Gamma> (ExprList es) =
  (let \<sigma>s = synths \<Gamma> es; \<tau> = joins (map base_type (map the (filter (\<lambda>\<sigma>. \<sigma> \<noteq> None) \<sigma>s))) in
   if es \<noteq> [] \<and> (\<exists>\<sigma> \<in> set \<sigma>s. \<sigma> \<noteq> None) \<and> checks_missing \<Gamma> es \<sigma>s \<tau>
   then Some (TyList \<tau>) else None)" |
"synth \<Gamma> (ExprTuple es) = map_option TyTuple (those (synths \<Gamma> es))" |
"synth \<Gamma> _ = None" |

"synths \<Gamma> [] = []" |
"synths \<Gamma> (e # es) = synth \<Gamma> e # synths \<Gamma> es" |

"check \<Gamma> e \<tau> = (check_intro \<Gamma> e \<tau> \<or> (case synth \<Gamma> e of Some \<sigma> \<Rightarrow> \<sigma> <: \<tau> | None \<Rightarrow> False))" |

"check_intro \<Gamma> (ExprLambda xs e) \<tau> =
  (case \<tau> of
     TyCallable \<tau>s \<tau>' \<Rightarrow> distinct xs \<and> length xs = length \<tau>s \<and> check (bind_params \<Gamma> xs \<tau>s) e \<tau>'
   | _ \<Rightarrow> False)" |
"check_intro \<Gamma> (ExprCall e (es, kws)) \<tau> =
  (case e of
     ExprLambda xs e' \<Rightarrow>
       kws = [] \<and>
       (case those (synths \<Gamma> es) of
          Some \<tau>s \<Rightarrow> distinct xs \<and> length xs = length es \<and> check (bind_params \<Gamma> xs \<tau>s) e' \<tau>
        | None \<Rightarrow> False)
   | _ \<Rightarrow> False)" |
"check_intro \<Gamma> (ExprList es) \<tau> = (case \<tau> of TyList \<tau>' \<Rightarrow> checks \<Gamma> es (replicate (length es) \<tau>') | _ \<Rightarrow> False)" |
"check_intro \<Gamma> (ExprTuple es) \<tau> = (case \<tau> of TyTuple \<tau>s \<Rightarrow> checks \<Gamma> es \<tau>s | _ \<Rightarrow> False)" |
"check_intro \<Gamma> (ExprCond e\<^sub>1 e e\<^sub>2) \<tau> = (check \<Gamma> e bool \<and> check \<Gamma> e\<^sub>1 \<tau> \<and> check \<Gamma> e\<^sub>2 \<tau>)" |
"check_intro \<Gamma> _ _ = False" |

"checks \<Gamma> [] [] = True" |
"checks \<Gamma> (e # es) (\<tau> # \<tau>s) = (check \<Gamma> e \<tau> \<and> checks \<Gamma> es \<tau>s)" |
"checks \<Gamma> _ _ = False" |

"checks_missing \<Gamma> (e # es) (None # \<sigma>s) \<tau> = (check \<Gamma> e \<tau> \<and> checks_missing \<Gamma> es \<sigma>s \<tau>)" |
"checks_missing \<Gamma> (e # es) (Some _ # \<sigma>s) \<tau> = checks_missing \<Gamma> es \<sigma>s \<tau>" |
"checks_missing \<Gamma> _ _ \<tau> = True"
by pat_completeness auto

termination
by (relation "measure (\<lambda>x. case x of
     Inl (Inl (\<Gamma>, e)) \<Rightarrow> 3 * size e
   | Inl (Inr (Inl (\<Gamma>, es))) \<Rightarrow> 3 * size_list size es
   | Inl (Inr (Inr (\<Gamma>, e, \<tau>))) \<Rightarrow> 3 * size e + 2
   | Inr (Inl (\<Gamma>, e, \<tau>)) \<Rightarrow> 3 * size e + 1
   | Inr (Inr (Inl (\<Gamma>, es, \<tau>s))) \<Rightarrow> 3 * size_list size es + 2
   | Inr (Inr (Inr (\<Gamma>, es, \<sigma>s, \<tau>))) \<Rightarrow> 3 * size_list size es + 2)")
   auto

(* Context entry binding a function name: its type scheme, or its type when there are no type parameters *)
fun scheme_cxt_entry :: "scheme \<Rightarrow> cxt_entry"
where
"scheme_cxt_entry (TyScheme [] \<tau>) = Ty \<tau>" |
"scheme_cxt_entry \<pi> = Scheme \<pi>"

abbreviation bind_type_params :: "cxt \<Rightarrow> var list \<Rightarrow> cxt"
where "bind_type_params \<Gamma> \<alpha>s \<equiv> \<Gamma> ++ map_of (map (\<lambda>\<alpha>. (\<alpha>, TypeVar)) \<alpha>s)"

fun def_signature :: "cxt \<Rightarrow> func \<Rightarrow> scheme option"
where
"def_signature \<Gamma> (Def f \<alpha>s xps \<psi> s) =
   (let \<Gamma>' = bind_type_params \<Gamma> \<alpha>s in
    case (those (map (resolve_type \<Gamma>' \<circ> snd) xps), resolve_type \<Gamma>' \<psi>) of
     (Some \<sigma>s, Some \<tau>) \<Rightarrow> Some (TyScheme \<alpha>s (TyCallable \<sigma>s \<tau>))
   | _ \<Rightarrow> None)"

(* Call of a callable with result None, which is a statement *)
fun call_none :: "cxt \<Rightarrow> expr \<Rightarrow> bool"
where
"call_none \<Gamma> (ExprCall e (es, [])) =
  (case synth \<Gamma> e of Some (TyCallable \<sigma>s (prim TyNone)) \<Rightarrow> checks \<Gamma> es \<sigma>s | _ \<Rightarrow> False)" |
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
"stmt_ty \<Gamma> \<zeta> (StmtAssert e) =
  (if e = false_literal then Some Returns\<^sub>R else if check \<Gamma> e bool then Some (Assigns\<^sub>R Map.empty) else None)" |
"stmt_ty \<Gamma> \<zeta> (StmtAssertMsg e e') =
  (if \<not> check \<Gamma> e' str then None else if e = false_literal then Some Returns\<^sub>R
   else if check \<Gamma> e bool then Some (Assigns\<^sub>R Map.empty) else None)" |
"stmt_ty \<Gamma> \<zeta> StmtReturnNone =
  (case \<zeta> of Some \<tau> \<Rightarrow> if \<tau> \<approx> prim TyNone then Some Returns\<^sub>R else None | None \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtReturn e) = (case \<zeta> of Some \<tau> \<Rightarrow> if check \<Gamma> e \<tau> then Some Returns\<^sub>R else None | None \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtIf e s elifs else') =
  (if check \<Gamma> e bool
    then merges (stmt_ty \<Gamma> \<zeta> s # elifs_ty \<Gamma> \<zeta> elifs
                 @ [case else' of Some s' \<Rightarrow> stmt_ty \<Gamma> \<zeta> s' | None \<Rightarrow> Some (Assigns\<^sub>R Map.empty)])
   else None)" |
"stmt_ty \<Gamma> \<zeta> (StmtSeq s s') =
  (case stmt_ty \<Gamma> \<zeta> s of
     Some (Assigns\<^sub>R \<Delta>) \<Rightarrow> map_option (\<lambda>R. Assigns\<^sub>R \<Delta> ++\<^sub>R R) (stmt_ty (\<Gamma> ++ \<Delta>) \<zeta> s')
   | _ \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtMutualRegion ds) =
  (case those (map (def_signature \<Gamma>) ds) of
     Some \<pi>s \<Rightarrow>
       let \<Delta> = map_of (zip (map def_name ds) (map scheme_cxt_entry \<pi>s)) in
       if defs_ty (\<Gamma> ++ \<Delta>) ds \<pi>s then Some (Assigns\<^sub>R \<Delta>) else None
   | None \<Rightarrow> None)" |
"stmt_ty \<Gamma> \<zeta> (StmtMatch e bs) = None" |

"elifs_ty \<Gamma> \<zeta> [] = []" |
"elifs_ty \<Gamma> \<zeta> ((e, s) # elifs) = (if check \<Gamma> e bool then stmt_ty \<Gamma> \<zeta> s else None) # elifs_ty \<Gamma> \<zeta> elifs" |

"defs_ty \<Gamma> [] [] = True" |
"defs_ty \<Gamma> (d # ds) (\<pi> # \<pi>s) = (def_body \<Gamma> d \<pi> \<and> defs_ty \<Gamma> ds \<pi>s)" |
"defs_ty \<Gamma> _ _ = False" |

"def_body \<Gamma> (Def f \<alpha>s xps \<psi> s) (TyScheme \<alpha>s' (TyCallable \<sigma>s \<tau>)) =
  (distinct (map fst xps) \<and> length xps = length \<sigma>s \<and>
   (case scope Unbound (set (map fst xps)) s of
      Some \<Delta> \<Rightarrow>
        (case stmt_ty (bind_params (bind_type_params \<Gamma> \<alpha>s) (map fst xps) \<sigma>s ++ \<Delta>) (Some \<tau>) s of
           Some R \<Rightarrow> R = Returns\<^sub>R \<or> \<tau> \<approx> prim TyNone
         | None \<Rightarrow> False)
    | None \<Rightarrow> False))" |
"def_body \<Gamma> _ _ = False"

end
