(* Evaluation judgements *)
theory Semantics
    imports Values
begin

datatype match_result = Match env | NoMatch | MatchAborts termination_kind

fun seq_compose_match :: "match_result \<Rightarrow> match_result \<Rightarrow> match_result" (infixl "\<otimes>\<^sub>m" 100)
where
"Match \<rho> \<otimes>\<^sub>m Match \<rho>' = Match (\<rho> \<otimes> \<rho>')" |
"Match \<rho> \<otimes>\<^sub>m m = m" |
"NoMatch \<otimes>\<^sub>m m = NoMatch" |
"MatchAborts \<kappa> \<otimes>\<^sub>m m = MatchAborts \<kappa>"

(* Name a case hypothesis IH when it contains an induction predicate, and hyps otherwise, following a rule
   without parameters. The induction method also takes the free variables among the conclusion's arguments for
   predicates, which makes every premise mentioning \<Sigma> an IH. *)
attribute_setup ih_names = \<open>
  let
    fun is_ih t = exists_subterm (fn u => (case strip_comb u of (Var _, _ :: _) => true | _ => false)) t
    fun hyp_name h = if is_ih h then "IH" else Rule_Cases.case_hypsN
  in
    Scan.succeed (Thm.mixed_attribute (fn (context, th) =>
      let
        val (cases, n) = Rule_Cases.get th
        val hyps = map (map hyp_name o Logic.strip_assums_hyp) (drop n (Thm.prems_of th))
      in swap (Thm.apply_attribute (Rule_Cases.cases_hyp_names (map (#1 o #1) cases) hyps) th context) end))
  end
\<close>

context evaluation
begin

definition field_map :: "name \<Rightarrow> 'a list \<Rightarrow> (var \<times> 'a) list \<Rightarrow> (var \<times> 'a) list option"
where
"field_map C us kvs =
  (let xs = field_names \<Sigma> C; n = length us in
   if n + length kvs = length xs \<and> set (map fst kvs) = set (drop n xs)
   then Some (zip (take n xs) us @ map (\<lambda>y. (y, the (map_of kvs y))) (drop n xs))
   else None)"

function (sequential) match :: "env \<Rightarrow> pat \<Rightarrow> val \<Rightarrow> match_result"
  and match_all :: "env \<Rightarrow> pat located list \<Rightarrow> val list \<Rightarrow> match_result"
  and match_dict :: "env \<Rightarrow> (str \<times> pat located) list \<Rightarrow> (str \<times> val) list \<Rightarrow> match_result"
  and match_kws :: "env \<Rightarrow> (var \<times> pat located) list \<Rightarrow> (var \<times> val) list \<Rightarrow> match_result"
  and match_fields ::
    "env \<Rightarrow> name \<Rightarrow> pat located list \<Rightarrow> (var \<times> pat located) list \<Rightarrow> (var \<times> val) list \<Rightarrow> match_result"
where
"match \<rho> (PatLiteral l) v =
  (if is_bool (VLit l) \<and> as_float v \<noteq> None then NoMatch
   else case eq (VLit l) v of Val True \<Rightarrow> Match \<epsilon> | Val False \<Rightarrow> NoMatch | Aborts \<kappa> \<Rightarrow> MatchAborts \<kappa>)" |
"match \<rho> (PatVar x) v = Match (fmupd x v \<epsilon>)" |
"match \<rho> PatWildcard v = Match \<epsilon>" |
"match \<rho> (PatAs p x) v = match \<rho> (node p) v \<otimes>\<^sub>m Match (fmupd x v \<epsilon>)" |
"match \<rho> (PatList ps) (VList vs) = (if length ps = length vs then match_all \<rho> ps vs else NoMatch)" |
"match \<rho> (PatList ps) (VTuple vs) = MatchAborts Excluded" |
"match \<rho> (PatTuple ps) (VTuple vs) = (if length ps = length vs then match_all \<rho> ps vs else NoMatch)" |
"match \<rho> (PatTuple ps) (VList vs) = MatchAborts Excluded" |
"match \<rho> (PatDict kps) (VDict \<delta>) =
  (if set (map fst kps) \<subseteq> set (map fst \<delta>) then match_dict \<rho> kps \<delta> else NoMatch)" |
"match \<rho> (PatConstr q (ps, kps)) v =
  (case do {
      u \<leftarrow> or_else NameError (fmlookup \<rho> (root q));
      ensure (u \<noteq> VUnbound) NameError;
      u' \<leftarrow> or_else AttributeError (resolve \<rho> q);
      ensure (\<not> is_opaque_builtin u') Excluded;
      or_else TypeError (class_of u') }
   of Fail \<kappa> \<Rightarrow> MatchAborts \<kappa>
    | Ok C \<Rightarrow>
        (case v of
           VObject D zvs \<Rightarrow> if C \<in> set (ancestors \<Sigma> D) then match_fields \<rho> C ps kps zvs else NoMatch
         | _ \<Rightarrow> NoMatch))" |
"match \<rho> _ _ = NoMatch" |

"match_all \<rho> (p # ps) (v # vs) = match \<rho> (node p) v \<otimes>\<^sub>m match_all \<rho> ps vs" |
"match_all \<rho> _ _ = Match \<epsilon>" |

"match_dict \<rho> ((w, p) # kps) \<delta> = match \<rho> (node p) (the (map_of \<delta> w)) \<otimes>\<^sub>m match_dict \<rho> kps \<delta>" |
"match_dict \<rho> [] \<delta> = Match \<epsilon>" |

"match_kws \<rho> ((y, p) # kps) zvs = match \<rho> (node p) (the (map_of zvs y)) \<otimes>\<^sub>m match_kws \<rho> kps zvs" |
"match_kws \<rho> [] zvs = Match \<epsilon>" |

"match_fields \<rho> C ps kps zvs =
  (if C = range_class then MatchAborts (if ps = [] then Excluded else TypeError)
   else
     let ys = field_names \<Sigma> C; n = length ps in
     if field_map C ps kps \<noteq> None \<and> set ys \<subseteq> set (map fst zvs)
     then match_all \<rho> ps (map (\<lambda>y. the (map_of zvs y)) (take n ys)) \<otimes>\<^sub>m match_kws \<rho> kps zvs
     else if length ys < n \<or> (\<exists>y \<in> set (map fst kps). y \<in> set (take n ys))
     then MatchAborts TypeError
     else MatchAborts Excluded)"
by pat_completeness auto

termination by size_change

fun dispatch :: "env \<Rightarrow> val \<Rightarrow> (pat located \<times> stmt located) list \<Rightarrow> (env \<times> stmt located) result"
where
"dispatch \<rho> v [] = Val (\<epsilon>, At no_pos StmtPass)" |
"dispatch \<rho> v ((p, s) # cases) =
  (case match \<rho> (node p) v of
     Match \<rho>' \<Rightarrow> Val (\<rho>', s)
   | NoMatch \<Rightarrow> dispatch \<rho> v cases
   | MatchAborts \<kappa> \<Rightarrow> Aborts \<kappa>)"

abbreviation true :: val where "true \<equiv> VLit (LitBool True)"
abbreviation false :: val where "false \<equiv> VLit (LitBool False)"

(* Type arguments of a subscript, read from its index *)
definition type_args_of :: "expr located \<Rightarrow> ty_expr list option"
where
"type_args_of e' = those (map type_expr_of (subscript_args e'))"

type_synonym elif_block = "(expr located \<times> stmt located) list \<times> stmt located option"

inductive
  eval_expr  :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"            ("_, _ \<Rightarrow>\<^sub>e _" [60,0,60] 60) and
  eval_exprs :: "env \<Rightarrow> expr located list \<Rightarrow> val list result \<Rightarrow> bool"  ("_, _ \<Rightarrow>\<^sub>e\<^sub>s _" [60,0,60] 60) and
  eval_stmt  :: "env \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"               ("_, _ \<Rightarrow>\<^sub>s _" [60,0,60] 60) and
  eval_elif  :: "env \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"         ("_, _ \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f _" [60,0,60] 60) and
  eval_quals :: "env \<Rightarrow> qualifier located list \<Rightarrow> env list result \<Rightarrow> bool"  ("_, _ \<Rightarrow>\<^sub>q _" [60,0,60] 60) and
  eval_gen   :: "env \<Rightarrow> var \<Rightarrow> val list \<Rightarrow> qualifier located list \<Rightarrow> env list result \<Rightarrow> bool"
    ("_, _, _, _ \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n _" [60,0,0,0,60] 60) and
  eval_comp  :: "env list \<Rightarrow> expr located \<Rightarrow> val list result \<Rightarrow> bool"       ("_, _ \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p _" [60,0,60] 60) and
  eval_entries :: "env list \<Rightarrow> expr located \<Rightarrow> expr located \<Rightarrow> (str \<times> val) list result \<Rightarrow> bool"
    ("_, _, _ \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s _" [60,0,0,60] 60)
where
EvalVar: "\<lbrakk> fmlookup \<rho> x = Some v ; v \<noteq> VUnbound \<rbrakk> \<Longrightarrow> \<rho>, ExprVar x \<Rightarrow>\<^sub>e Val v" |
EvalVarUnknown: "fmlookup \<rho> x = None \<Longrightarrow> \<rho>, ExprVar x \<Rightarrow>\<^sub>e Aborts NameError" |
EvalVarUnbound: "fmlookup \<rho> x = Some VUnbound \<Longrightarrow> \<rho>, ExprVar x \<Rightarrow>\<^sub>e Aborts NameError" |
EvalLiteral: "\<rho>, ExprLiteral l \<Rightarrow>\<^sub>e Val (VLit l)" |
EvalLambda: "\<rho>, ExprLambda xs e \<Rightarrow>\<^sub>e Val Lam(\<rho>, xs, e)" |
EvalUnOp: "\<rho>, node e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, ExprUnOp op e \<Rightarrow>\<^sub>e mlet r (unop_meaning op)" |
EvalBinOp: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>, node e' \<Rightarrow>\<^sub>e r \<rbrakk>
  \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e mlet r (binop_meaning op v)" |
EvalBinOpFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalAndFalse: "\<rho>, node e \<Rightarrow>\<^sub>e Val false \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e Val false" |
EvalAndTrue: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val true ; \<rho>, node e' \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e r" |
EvalAndFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalAndNonBool: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e Aborts Excluded" |
EvalOrTrue: "\<rho>, node e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e Val true" |
EvalOrFalse: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, node e' \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e r" |
EvalOrFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalOrNonBool: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e Aborts Excluded" |
EvalCondTrue: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val true ; \<rho>, node e1 \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e r" |
EvalCondFalse: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, node e2 \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e r" |
EvalCondFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalCondNonBool: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e Aborts Excluded" |
EvalList: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val vs \<Longrightarrow> \<rho>, ExprList es \<Rightarrow>\<^sub>e Val (VList vs)" |
EvalListFail: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<Longrightarrow> \<rho>, ExprList es \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalTuple: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val vs \<Longrightarrow> \<rho>, ExprTuple es \<Rightarrow>\<^sub>e Val (VTuple vs)" |
EvalTupleFail: "\<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<Longrightarrow> \<rho>, ExprTuple es \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalDict:
  "\<lbrakk> \<rho>, concat (map (\<lambda>(e, e'). [e, e']) kes) \<Rightarrow>\<^sub>e\<^sub>s Val vs ; dict_entries vs = Some \<delta> \<rbrakk>
  \<Longrightarrow> \<rho>, ExprDict kes \<Rightarrow>\<^sub>e Val (VDict (update [] \<delta>))" |
EvalDictFail:
  "\<rho>, concat (map (\<lambda>(e, e'). [e, e']) kes) \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<Longrightarrow> \<rho>, ExprDict kes \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalDictNonStr:
  "\<lbrakk> \<rho>, concat (map (\<lambda>(e, e'). [e, e']) kes) \<Rightarrow>\<^sub>e\<^sub>s Val vs ; dict_entries vs = None \<rbrakk>
  \<Longrightarrow> \<rho>, ExprDict kes \<Rightarrow>\<^sub>e Aborts Excluded" |
EvalSubscript:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<not> is_class v ; \<rho>, node e' \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e mlet r (getitem v)" |
EvalClassTypeArgs:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C) ; type_args_of e' = Some \<psi>s \<rbrakk> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e Val (VClass C)" |
EvalSubscriptFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalListComp:
  "\<lbrakk> \<rho>, gs \<Rightarrow>\<^sub>q Val \<rho>s ; \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Val vs \<rbrakk> \<Longrightarrow> \<rho>, ExprListComp e gs \<Rightarrow>\<^sub>e Val (VList vs)" |
EvalListCompFailQuals: "\<rho>, gs \<Rightarrow>\<^sub>q Aborts \<kappa> \<Longrightarrow> \<rho>, ExprListComp e gs \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalListCompFail:
  "\<lbrakk> \<rho>, gs \<Rightarrow>\<^sub>q Val \<rho>s ; \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprListComp e gs \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalDictComp:
  "\<lbrakk> \<rho>, gs \<Rightarrow>\<^sub>q Val \<rho>s ; \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Val \<delta> \<rbrakk>
  \<Longrightarrow> \<rho>, ExprDictComp e e' gs \<Rightarrow>\<^sub>e Val (VDict (update [] \<delta>))" |
EvalDictCompFailQuals: "\<rho>, gs \<Rightarrow>\<^sub>q Aborts \<kappa> \<Longrightarrow> \<rho>, ExprDictComp e e' gs \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalDictCompFail:
  "\<lbrakk> \<rho>, gs \<Rightarrow>\<^sub>q Val \<rho>s ; \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> \<rho>, ExprDictComp e e' gs \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalAttrObject:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VObject C xvs) ; map_of xvs x = Some v \<rbrakk> \<Longrightarrow> \<rho>, ExprAttribute e x \<Rightarrow>\<^sub>e Val v" |
EvalAttrObjectMissing:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VObject C xvs) ; map_of xvs x = None \<rbrakk> \<Longrightarrow> \<rho>, ExprAttribute e x \<Rightarrow>\<^sub>e Aborts AttributeError" |
EvalAttrModule:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VModLoaded q' \<rho>') ; fmlookup \<rho>' x = Some v \<rbrakk> \<Longrightarrow> \<rho>, ExprAttribute e x \<Rightarrow>\<^sub>e Val v" |
EvalAttrModuleMissing:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VModLoaded q' \<rho>') ; fmlookup \<rho>' x = None \<rbrakk>
  \<Longrightarrow> \<rho>, ExprAttribute e x \<Rightarrow>\<^sub>e Aborts AttributeError" |
EvalAttrNonObject:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<not> is_object v ; \<not> is_loaded_module v \<rbrakk> \<Longrightarrow> \<rho>, ExprAttribute e x \<Rightarrow>\<^sub>e Aborts Excluded" |
EvalAttrFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprAttribute e x \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalCallLambda:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xs = length us
  ; \<rho>' \<otimes> fmap_of_list (zip xs us), node e' \<Rightarrow>\<^sub>e r
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e r" |
EvalCallLambdaArity:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xs \<noteq> length us
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalCallDef:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val Def(\<rho>', ds, j)
  ; node (ds ! j) = Def f \<alpha>s xps \<psi> s
  ; vs = map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds]
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xps = length us
  ; scope VUnbound (map fst xps) s = Some \<rho>s
  ; \<rho>' \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) vs) \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s,
      node s \<Rightarrow>\<^sub>s ([], \<omega>)
  ; j < length ds
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e result_of \<omega>" |
EvalCallDefArity:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val Def(\<rho>', ds, j)
  ; node (ds ! j) = Def f \<alpha>s xps \<psi> s
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xps \<noteq> length us
  ; j < length ds
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalCallPrim:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VPrim f) ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e prim_meaning f us" |
EvalCallNonFun:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us ; \<not> is_closure v ; \<not> is_prim v ; \<not> is_class v \<rbrakk>
  \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalCallFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprCall e (es, kws) \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalCallFailArgs:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalConstr:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C) ; \<rho>, es @ map snd kws \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) = Some xus
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, kws) \<Rightarrow>\<^sub>e Val (VObject C xus)" |
EvalConstrArity:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C) ; \<rho>, es @ map snd kws \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; field_map C (take (length es) us) (zip (map fst kws) (drop (length es) us)) = None
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, kws) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalConstrFail:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VClass C) ; \<rho>, es @ map snd kws \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, kws) \<Rightarrow>\<^sub>e Aborts \<kappa>" |

EvalExprsNil: "\<rho>, [] \<Rightarrow>\<^sub>e\<^sub>s Val []" |
EvalExprsCons: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s r \<rbrakk>
  \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s mlet r (\<lambda>vs. Val (v # vs))" |
EvalExprsFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa>" |

EvalPass: "\<rho>, StmtPass \<Rightarrow>\<^sub>s assigns\<^sub>o \<epsilon>" |
EvalDeclare: "\<rho>, StmtDeclare x \<psi> \<Rightarrow>\<^sub>s assigns\<^sub>o \<epsilon>" |
EvalAssign: "\<rho>, node e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtAssign x \<pi> e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. assigns\<^sub>o (fmupd x v \<epsilon>))" |
EvalExprStmt: "\<rho>, node e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtExpr e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. assigns\<^sub>o \<epsilon>)" |
EvalPrint: "\<rho>, node e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtPrint e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. ([v], Assigns \<epsilon>))" |
EvalReturn: "\<rho>, node e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtReturn (Some e) \<Rightarrow>\<^sub>s mlet r returns\<^sub>o" |
EvalReturnNone: "\<rho>, StmtReturn None \<Rightarrow>\<^sub>s returns\<^sub>o (VLit LitNone)" |
EvalDefs:
  "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]
  \<Longrightarrow> \<rho>, StmtMutualRegion ds \<Rightarrow>\<^sub>s assigns\<^sub>o (fmap_of_list (zip (map (def_name \<circ> node) ds) vs))" |
EvalAssert: "\<rho>, node e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s assigns\<^sub>o \<epsilon>" |
EvalAssertFalse: "\<rho>, node e \<Rightarrow>\<^sub>e Val false \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s aborts\<^sub>o (AssertionError None)" |
EvalAssertFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>" |
EvalAssertNonBool:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s aborts\<^sub>o Excluded" |
EvalAssertMsg: "\<rho>, node e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s assigns\<^sub>o \<epsilon>" |
EvalAssertMsgFalse: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, node e' \<Rightarrow>\<^sub>e Val (VLit (LitString w)) \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s aborts\<^sub>o (AssertionError (Some w))" |
EvalAssertMsgFalseFail: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, node e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>" |
EvalAssertMsgFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>" |
EvalAssertMsgNonBool:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s aborts\<^sub>o Excluded" |
EvalAssertMsgNonStr:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, node e' \<Rightarrow>\<^sub>e Val v ; \<forall>w. v \<noteq> VLit (LitString w) \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s aborts\<^sub>o Excluded" |
EvalIfTrue: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val true ; \<rho>, node s \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s o" |
EvalIfFalse: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, (elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s o" |
EvalIfFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>" |
EvalIfNonBool:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s aborts\<^sub>o Excluded" |
EvalMatch:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; dispatch \<rho> v cases = Val (\<rho>', s') ; \<rho> \<otimes> \<rho>', node s' \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtMatch e cases \<Rightarrow>\<^sub>s assigns\<^sub>o \<rho>' \<otimes>\<^sub>o o" |
EvalMatchFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtMatch e cases \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>" |
EvalMatchAbort:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; dispatch \<rho> v cases = Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, StmtMatch e cases \<Rightarrow>\<^sub>s aborts\<^sub>o \<kappa>" |
EvalSeq: "\<lbrakk> \<rho>, node s \<Rightarrow>\<^sub>s (us, Assigns \<rho>') ; \<rho> \<otimes> \<rho>', node s' \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s (us, Assigns \<rho>') \<otimes>\<^sub>o o" |
EvalSeqReturn: "\<rho>, node s \<Rightarrow>\<^sub>s (us, Returns v) \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s (us, Returns v)" |
EvalSeqFail: "\<rho>, node s \<Rightarrow>\<^sub>s (us, Aborts\<^sub>\<omega> \<kappa>) \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s (us, Aborts\<^sub>\<omega> \<kappa>)" |

EvalIfNone: "\<rho>, ([], None) \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f assigns\<^sub>o \<epsilon>" |
EvalElse: "\<rho>, node s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<rho>, ([], Some s) \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifTrue: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val true ; \<rho>, node s \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifFalse: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, (elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<rbrakk>
  \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f aborts\<^sub>o \<kappa>" |
EvalElifNonBool:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f aborts\<^sub>o Excluded" |

EvalQualsNil: "\<rho>, [] \<Rightarrow>\<^sub>q Val [\<rho>]" |
EvalQualGuardTrue: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val true ; \<rho>, gs \<Rightarrow>\<^sub>q r \<rbrakk> \<Longrightarrow> \<rho>, At p (Guard e) # gs \<Rightarrow>\<^sub>q r" |
EvalQualGuardFalse: "\<rho>, node e \<Rightarrow>\<^sub>e Val false \<Longrightarrow> \<rho>, At p (Guard e) # gs \<Rightarrow>\<^sub>q Val []" |
EvalQualGuardFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, At p (Guard e) # gs \<Rightarrow>\<^sub>q Aborts \<kappa>" |
EvalQualGuardNonBool:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, At p (Guard e) # gs \<Rightarrow>\<^sub>q Aborts Excluded" |
EvalQualGenerator:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; iter v = Some us ; \<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n r \<rbrakk> \<Longrightarrow> \<rho>, At p (Generator x e) # gs \<Rightarrow>\<^sub>q r" |
EvalQualGeneratorFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, At p (Generator x e) # gs \<Rightarrow>\<^sub>q Aborts \<kappa>" |
EvalQualGeneratorNonSeq:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; iter v = None \<rbrakk> \<Longrightarrow> \<rho>, At p (Generator x e) # gs \<Rightarrow>\<^sub>q Aborts TypeError" |

EvalGenNil: "\<rho>, x, [], gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Val []" |
EvalGenCons:
  "\<lbrakk> fmupd x u \<rho>, gs \<Rightarrow>\<^sub>q Val \<rho>s ; \<rho>, x, us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n r \<rbrakk>
  \<Longrightarrow> \<rho>, x, u # us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n mlet r (\<lambda>\<rho>ss. Val (\<rho>s @ \<rho>ss))" |
EvalGenFail: "fmupd x u \<rho>, gs \<Rightarrow>\<^sub>q Aborts \<kappa> \<Longrightarrow> \<rho>, x, u # us, gs \<Rightarrow>\<^sub>g\<^sub>e\<^sub>n Aborts \<kappa>" |

EvalCompNil: "[], e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Val []" |
EvalCompCons:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p r \<rbrakk> \<Longrightarrow> \<rho> # \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p mlet r (\<lambda>vs. Val (v # vs))" |
EvalCompFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho> # \<rho>s, e \<Rightarrow>\<^sub>c\<^sub>o\<^sub>m\<^sub>p Aborts \<kappa>" |

EvalEntriesNil: "[], e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Val []" |
EvalEntriesCons:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VLit (LitString w)) ; \<rho>, node e' \<Rightarrow>\<^sub>e Val v ; \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s r \<rbrakk>
  \<Longrightarrow> \<rho> # \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s mlet r (\<lambda>\<delta>. Val ((w, v) # \<delta>))" |
EvalEntriesFailKey: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho> # \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Aborts \<kappa>" |
EvalEntriesNonStr:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; \<forall>w. v \<noteq> VLit (LitString w) \<rbrakk>
  \<Longrightarrow> \<rho> # \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Aborts Excluded" |
EvalEntriesFailValue:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VLit (LitString w)) ; \<rho>, node e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> \<rho> # \<rho>s, e, e' \<Rightarrow>\<^sub>e\<^sub>n\<^sub>t\<^sub>r\<^sub>i\<^sub>e\<^sub>s Aborts \<kappa>"

lemmas eval_rules = eval_expr_eval_exprs_eval_stmt_eval_elif_eval_quals_eval_gen_eval_comp_eval_entries.intros

(* Value of the name of definition i in a group \<chi>s of mutually recursive type definitions of module q: a class
   for a dataclass, and a type alias for a type statement *)
definition type_value :: "name \<Rightarrow> type_def located list \<Rightarrow> nat \<Rightarrow> val"
where
"type_value q \<chi>s i =
  (case node (\<chi>s ! i) of Dataclass c _ _ _ \<Rightarrow> VClass (Qualified q c) | TypeStmt _ _ _ \<Rightarrow> VTypeAlias q \<chi>s i)"

inductive eval_top :: "name \<Rightarrow> env \<Rightarrow> top_stmt \<Rightarrow> outcome \<Rightarrow> bool"  ("_, _, _ \<Rightarrow>\<^sub>t _" [60,60,0,60] 60)
where
EvalTopStmt: "\<rho>, node s \<Rightarrow>\<^sub>s o \<Longrightarrow> q, \<rho>, Stmt s \<Rightarrow>\<^sub>t o" |
EvalTopSeq:
  "\<lbrakk> q, \<rho>, t \<Rightarrow>\<^sub>t (us, Assigns \<rho>') ; q, \<rho> \<otimes> \<rho>', t' \<Rightarrow>\<^sub>t o \<rbrakk> \<Longrightarrow> q, \<rho>, TopSeq t t' \<Rightarrow>\<^sub>t (us, Assigns \<rho>') \<otimes>\<^sub>o o" |
EvalTopSeqFail: "q, \<rho>, t \<Rightarrow>\<^sub>t (us, Aborts\<^sub>\<omega> \<kappa>) \<Longrightarrow> q, \<rho>, TopSeq t t' \<Rightarrow>\<^sub>t (us, Aborts\<^sub>\<omega> \<kappa>)" |
EvalTypes:
  "q, \<rho>, TypeDefs \<chi>s \<Rightarrow>\<^sub>t
   assigns\<^sub>o (fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_value q \<chi>s j)) [0..<length \<chi>s]))"

end

definition \<E> :: "str list \<Rightarrow> (name, env) fmap"
where
"\<E> \<A> =
  (let name = \<lambda>x. (var ''__name__'', VLit (LitString (str_of x))) in
   fmap_of_list
    [(builtins, fmap_of_list
       ([name ''builtins'', (var ''len'', VPrim PrimLen), (var ''range'', VClass range_class),
         (var ''round'', VPrim PrimRound)]
        @ map (\<lambda>y. (y, VPredef (Qualified builtins y)))
            (map prim_name [NoneType, object, bool, int, float, str]
             @ map var [''list'', ''dict'', ''tuple'']))),
     (Simple (var ''sys''), fmap_of_list
       [name ''sys'', (var ''argv'', VList (map (VLit \<circ> LitString) \<A>)), (var ''exit'', VPrim PrimExit)]),
     (Simple (var ''typing''), fmap_of_list
       (name ''typing'' # map (\<lambda>y. (y, VPredef (Qualified (Simple (var ''typing'')) y)))
          [var ''Callable'', var ''Literal'', prim_name Never, prim_name Sized])),
     (Simple (var ''dataclasses''), fmap_of_list
       [name ''dataclasses'',
        (var ''dataclass'', VPredef (Qualified (Simple (var ''dataclasses'')) (var ''dataclass'')))])])"

function (sequential) extend_val :: "val \<Rightarrow> val \<Rightarrow> val"
and extend_env :: "env \<Rightarrow> env \<Rightarrow> env" (infixl "\<uplus>\<^sub>v" 65)
where
"extend_val (VModLoaded q \<rho>) v' =
   (case v' of
      VModStub q' \<Rightarrow> if q = q' then VModLoaded q \<rho> else v'
    | VModLoaded q' \<rho>' \<Rightarrow> if q = q' then VModLoaded q (\<rho> \<uplus>\<^sub>v \<rho>') else v'
    | _ \<Rightarrow> v')" |
"extend_val _ v' = v'" |
"\<rho> \<uplus>\<^sub>v \<rho>' =
   \<rho> ++\<^sub>f fmmap_keys (\<lambda>x v'. case fmlookup \<rho> x of None \<Rightarrow> v' | Some v \<Rightarrow> extend_val v v') \<rho>'"
by pat_completeness auto

termination
by (relation "measure (\<lambda>p. case p of Inl (v, _) \<Rightarrow> size v | Inr (\<rho>, _) \<Rightarrow> size_fmap (\<lambda>_. 0) size \<rho>)")
   (simp_all add: size_fmap_lookup del: size_fmap_def)

declare extend_env.simps [simp del]

fun member :: "(name, env) fmap \<Rightarrow> env \<Rightarrow> var \<Rightarrow> val"
where
"member \<L> \<rho> x = (case the (fmlookup \<rho> x) of VModStub q \<Rightarrow> VModLoaded q (the (fmlookup \<L> q)) | v \<Rightarrow> v)"

fun submod_env :: "(name, env) fmap \<Rightarrow> name \<Rightarrow> var list \<Rightarrow> env"
where
"submod_env \<L> q [] = the (fmlookup \<L> q)" |
"submod_env \<L> q (x # xs) =
   the (fmlookup \<L> q) \<uplus>\<^sub>v fmupd x (VModLoaded (Qualified q x) (submod_env \<L> (Qualified q x) xs)) \<epsilon>"

fun import_env :: "(name, env) fmap \<Rightarrow> import \<Rightarrow> env"
where
"import_env \<L> (Import q) =
   (case variables q of x # xs \<Rightarrow> fmupd x (VModLoaded (Simple x) (submod_env \<L> (Simple x) xs)) \<epsilon>)" |
"import_env \<L> (FromImport q xs) = fmap_of_list (map (\<lambda>x. (x, member \<L> (the (fmlookup \<L> q)) x)) xs)"

fun imports_env :: "(name, env) fmap \<Rightarrow> import located list \<Rightarrow> env"
where
"imports_env \<L> [] = \<epsilon>" |
"imports_env \<L> (\<iota> # \<iota>s) = import_env \<L> (node \<iota>) \<uplus>\<^sub>v imports_env \<L> \<iota>s"

locale loading = evaluation +
  fixes \<M> :: program
begin

function
  loads :: "name list \<Rightarrow> name list \<Rightarrow> name list" and
  submod_loads :: "name list \<Rightarrow> name \<Rightarrow> var list \<Rightarrow> name list" and
  imports_loads :: "name list \<Rightarrow> name \<Rightarrow> import located list \<Rightarrow> name list" and
  import_loads :: "name list \<Rightarrow> name \<Rightarrow> import \<Rightarrow> name list"
where
"loads qs [] = qs" |
"loads qs (q # qs') =
   (if q \<in> set qs \<or> q |\<in>| fmdom \<P> then loads qs qs'
    else case the (fmlookup \<M> q) of ModuleBody \<iota>s t \<Rightarrow> loads (imports_loads qs q \<iota>s @ [q]) qs')" |

"submod_loads qs q [] = qs" |
"submod_loads qs q (x # xs) =
   (if Qualified q x |\<in>| fmdom \<M> \<and> x \<notin> set (declares (the (fmlookup \<M> q)))
    then submod_loads (loads qs [Qualified q x]) q xs
    else submod_loads qs q xs)" |

"imports_loads qs q [] = qs" |
"imports_loads qs q (\<iota> # \<iota>s) = imports_loads (import_loads qs q (node \<iota>)) q \<iota>s" |

"import_loads qs q (Import q') = loads qs (proper_prefixes q' @ [q'])" |
"import_loads qs q (FromImport q' xs) = submod_loads (loads qs (unique_to q' q @ [q'])) q' xs"
by pat_completeness auto

(* Environment that binds each submodule of q to a stub *)
definition submods_env :: "name \<Rightarrow> env"
where
"submods_env q = fmmap (\<lambda>\<theta>. case \<theta> of ModStub q' \<Rightarrow> VModStub q' | _ \<Rightarrow> VUnbound) (submods \<M> q)"

inductive eval_mod :: "name \<Rightarrow> (name, env) fmap \<Rightarrow> outcome \<Rightarrow> bool"  ("_, _ \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d _" [60,60,60] 60)
where
EvalModule:
  "\<lbrakk> fmlookup \<M> q = Some (ModuleBody \<iota>s t) ; scope VUnbound (declares \<iota>s) t = Some \<rho>s
  ; q, the (fmlookup \<L> builtins) \<otimes> imports_env \<L> \<iota>s \<otimes> \<rho>s, t \<Rightarrow>\<^sub>t o
  \<rbrakk> \<Longrightarrow> q, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d o"

inductive eval_mods :: "name list \<Rightarrow> (name, env) fmap \<Rightarrow> outcome \<Rightarrow> bool"  ("_, _ \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s _" [60,60,60] 60)
where
EvalModsNil: "[], \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s assigns\<^sub>o \<epsilon>" |
EvalModsCons:
  "\<lbrakk> q, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d (vs, Assigns \<rho>) ; qs, fmupd q (submods_env q \<otimes> \<rho>) \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s o \<rbrakk>
  \<Longrightarrow> q # qs, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s (vs, Assigns \<epsilon>) \<otimes>\<^sub>o o" |
EvalModsFail: "q, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d (vs, Aborts\<^sub>\<omega> \<kappa>) \<Longrightarrow> q # qs, \<L> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s (vs, Aborts\<^sub>\<omega> \<kappa>)"

inductive eval_program :: "str list \<Rightarrow> val list \<Rightarrow> termination_kind \<Rightarrow> bool"
where
EvalProgram: "loads [] [main], \<E> \<A> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s (vs, Assigns \<rho>) \<Longrightarrow> eval_program \<A> vs (SystemExit 0)" |
EvalProgramAbort: "loads [] [main], \<E> \<A> \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s (vs, Aborts\<^sub>\<omega> \<kappa>) \<Longrightarrow> eval_program \<A> vs \<kappa>"

end

end
