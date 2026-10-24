theory Semantics
    imports Syntax "HOL-Library.Finite_Map"
begin

(* Free o for outcomes, as in the spec *)
no_notation (ASCII) comp (infixl \<open>o\<close> 55)
notation fmadd (infixl "\<otimes>" 100)

datatype val =
      VLit lit
    | VList "val list"
    | VTuple "val list"
    | VDict "(string \<times> val) list"
    | VLamClosure "(var, val) fmap" "var list" expr  ("Lam'(_, _, _')")
    | VDefClosure "(var, val) fmap" "func list" nat  ("Def'(_, _, _')")
    | VUnbound

type_synonym env = "(var, val) fmap"
abbreviation \<epsilon> :: env where "\<epsilon> \<equiv> fmempty"

datatype termination_kind =
    TypeError
  | IndexError
  | KeyError
  | OverflowError
  | ValueError
  | ZeroDivisionError
  | AssertionError "string option"
  | AttributeError
  | NameError
  | SystemExit int
  | Undef
  | Excluded

datatype 'a result = Val 'a | Aborts termination_kind

datatype outcome = Assigns env | Returns val | Aborts\<^sub>o termination_kind

consts mlet :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"

fun mlet_result :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result"
where
"mlet_result (Val v) f = f v" |
"mlet_result (Aborts \<kappa>) f = Aborts \<kappa>"

fun mlet_outcome :: "'a result \<Rightarrow> ('a \<Rightarrow> outcome) \<Rightarrow> outcome"
where
"mlet_outcome (Val v) f = f v" |
"mlet_outcome (Aborts \<kappa>) f = Aborts\<^sub>o \<kappa>"

adhoc_overloading mlet \<rightleftharpoons> mlet_result mlet_outcome

fun compose :: "outcome \<Rightarrow> outcome \<Rightarrow> outcome" (infixl "\<otimes>\<^sub>o" 100)
where
"Assigns \<rho> \<otimes>\<^sub>o Assigns \<rho>' = Assigns (\<rho> \<otimes> \<rho>')" |
"Assigns \<rho> \<otimes>\<^sub>o o = o" |
"Returns v \<otimes>\<^sub>o o = Returns v" |
"Aborts\<^sub>o \<kappa> \<otimes>\<^sub>o o = Aborts\<^sub>o \<kappa>"

fun call_result :: "outcome \<Rightarrow> val result"
where
"call_result (Returns v) = Val v" |
"call_result (Assigns \<rho>) = Val (VLit LitNone)" |
"call_result (Aborts\<^sub>o \<kappa>) = Aborts \<kappa>"

fun is_closure :: "val \<Rightarrow> bool"
where
"is_closure Lam(_, _, _) = True" |
"is_closure Def(_, _, _) = True" |
"is_closure _ = False"

fun eq :: "val \<Rightarrow> val \<Rightarrow> bool result" and eq_elems :: "val list \<Rightarrow> val list \<Rightarrow> bool result"
where
"eq (VLit (LitInt n)) (VLit (LitInt n')) = Val (n = n')" |
"eq (VLit (LitInt n)) (VLit (LitFloat x')) = Val (real_of_int n = x')" |
"eq (VLit (LitFloat x)) (VLit (LitInt n')) = Val (x = real_of_int n')" |
"eq (VLit (LitFloat x)) (VLit (LitFloat x')) = Val (x = x')" |
"eq (VLit (LitString w)) (VLit (LitString w')) = Val (w = w')" |
"eq (VLit (LitBool b)) (VLit (LitBool b')) = Val (b = b')" |
"eq (VLit LitNone) (VLit LitNone) = Val True" |
"eq (VLit (LitBool _)) (VLit (LitInt _)) = Aborts Undef" |
"eq (VLit (LitBool _)) (VLit (LitFloat _)) = Aborts Undef" |
"eq (VLit (LitInt _)) (VLit (LitBool _)) = Aborts Undef" |
"eq (VLit (LitFloat _)) (VLit (LitBool _)) = Aborts Undef" |
"eq (VList vs) (VList vs') = eq_elems vs vs'" |
"eq (VTuple vs) (VTuple vs') = eq_elems vs vs'" |
"eq (VDict \<delta>) (VDict \<delta>') =
  (if set (map fst \<delta>) = set (map fst \<delta>') then eq_elems (map snd \<delta>) (map (the \<circ> map_of \<delta>') (map fst \<delta>))
   else Val False)" |
"eq Lam(_, _, _) Lam(_, _, _) = Aborts Undef" |
"eq Lam(_, _, _) Def(_, _, _) = Aborts Undef" |
"eq Def(_, _, _) Lam(_, _, _) = Aborts Undef" |
"eq Def(_, _, _) Def(_, _, _) = Aborts Undef" |
"eq _ _ = Val False" |

"eq_elems [] [] = Val True" |
"eq_elems (v # vs) (v' # vs') =
  (if length vs \<noteq> length vs' then Val False
   else if eq v v' = Val True then eq_elems vs vs' else eq v v')" |
"eq_elems _ _ = Val False"

fun contains :: "val \<Rightarrow> val \<Rightarrow> bool result" and contains_elems :: "val list \<Rightarrow> val \<Rightarrow> bool result"
where
"contains (VList vs) v = contains_elems vs v" |
"contains (VTuple vs) v = contains_elems vs v" |
"contains (VDict \<delta>) (VLit (LitString w)) = Val (w \<in> set (map fst \<delta>))" |
"contains (VDict \<delta>) _ = Aborts Excluded" |
"contains (VLit (LitString w')) (VLit (LitString w)) = Val (\<exists>w1 w2. w' = w1 @ w @ w2)" |
"contains _ _ = Aborts TypeError" |

"contains_elems [] v = Val False" |
"contains_elems (v' # vs) v = (if eq v v' = Val False then contains_elems vs v else eq v v')"

fun is_bool :: "val \<Rightarrow> bool"
where
"is_bool (VLit (LitBool _)) = True" |
"is_bool _ = False"

(* Numeric value as a real; None for a non-number *)
fun as_real :: "val \<Rightarrow> real option"
where
"as_real (VLit (LitInt n)) = Some (real_of_int n)" |
"as_real (VLit (LitFloat x)) = Some x" |
"as_real _ = None"

(* Apply g to two numbers as reals; Excluded for a Boolean operand *)
fun real_op :: "(real \<Rightarrow> real \<Rightarrow> val result) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"real_op g v v' =
  (if is_bool v \<or> is_bool v' then Aborts Excluded
   else case (as_real v, as_real v') of
     (Some x, Some x') \<Rightarrow> g x x'
   | _ \<Rightarrow> Aborts TypeError)"

(* Apply f to two integers, g to two numbers otherwise *)
fun arith :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> (real \<Rightarrow> real \<Rightarrow> real) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"arith f g (VLit (LitInt n)) (VLit (LitInt n')) = Val (VLit (LitInt (f n n')))" |
"arith f g v v' = real_op (\<lambda>x x'. Val (VLit (LitFloat (g x x')))) v v'"

(* Compare two numbers as reals *)
fun compare :: "(real \<Rightarrow> real \<Rightarrow> bool) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"compare f v v' = real_op (\<lambda>x x'. Val (VLit (LitBool (f x x')))) v v'"

fun binop_meaning :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"binop_meaning BOpEq v v' = mlet (eq v v') (\<lambda>b. Val (VLit (LitBool b)))" |
"binop_meaning BOpNeq v v' = mlet (eq v v') (\<lambda>b. Val (VLit (LitBool (\<not> b))))" |
"binop_meaning BOpIn v v' = mlet (contains v' v) (\<lambda>b. Val (VLit (LitBool b)))" |
"binop_meaning BOpNotIn v v' = mlet (contains v' v) (\<lambda>b. Val (VLit (LitBool (\<not> b))))" |
"binop_meaning BOpLt v v' = compare (<) v v'" |
"binop_meaning BOpLeq v v' = compare (\<le>) v v'" |
"binop_meaning BOpGt v v' = compare (>) v v'" |
"binop_meaning BOpGeq v v' = compare (\<ge>) v v'" |
"binop_meaning BOpAdd v v' = arith (+) (+) v v'" |
"binop_meaning BOpSub v v' = arith (-) (-) v v'" |
"binop_meaning BOpMul v v' = arith (*) (*) v v'" |
"binop_meaning BOpDiv v v' =
  (if as_real v' = Some 0 then Aborts ZeroDivisionError
   else real_op (\<lambda>x x'. Val (VLit (LitFloat (x / x')))) v v')" |
"binop_meaning BOpFloorDiv v v' =
  (if as_real v' = Some 0 then Aborts ZeroDivisionError
   else arith (div) (\<lambda>x x'. real_of_int \<lfloor>x / x'\<rfloor>) v v')" |
"binop_meaning BOpMod v v' =
  (if as_real v' = Some 0 then Aborts ZeroDivisionError
   else arith (mod) (\<lambda>x x'. x - x' * real_of_int \<lfloor>x / x'\<rfloor>) v v')" |
"binop_meaning BOpPow (VLit (LitInt n)) (VLit (LitInt n')) =
  (if n' \<ge> 0 then Val (VLit (LitInt (n ^ nat n')))
   else if n = 0 then Aborts ZeroDivisionError
   else Val (VLit (LitFloat (inverse (real_of_int n ^ nat (- n'))))))" |
"binop_meaning BOpPow v v' =
  real_op (\<lambda>x x'.
    if x = 0 \<and> x' < 0 then Aborts ZeroDivisionError else Val (VLit (LitFloat (x powr x')))) v v'" |
"binop_meaning _ _ _ = Aborts TypeError"

fun unop_meaning :: "uop \<Rightarrow> val \<Rightarrow> val result"
where
"unop_meaning UOpNot (VLit (LitBool b)) = Val (VLit (LitBool (\<not> b)))" |
"unop_meaning UOpPos (VLit (LitInt n)) = Val (VLit (LitInt n))" |
"unop_meaning UOpPos (VLit (LitFloat x)) = Val (VLit (LitFloat x))" |
"unop_meaning UOpNeg (VLit (LitInt n)) = Val (VLit (LitInt (- n)))" |
"unop_meaning UOpNeg (VLit (LitFloat x)) = Val (VLit (LitFloat (- x)))" |
"unop_meaning UOpNot _ = Aborts Excluded" |
"unop_meaning _ (VLit (LitBool _)) = Aborts Excluded" |
"unop_meaning _ _ = Aborts TypeError"

fun setitem :: "(string \<times> val) list \<Rightarrow> string \<Rightarrow> val \<Rightarrow> (string \<times> val) list"
where
"setitem [] w v = [(w, v)]" |
"setitem ((w', v') # \<delta>) w v = (if w = w' then (w, v) # \<delta> else (w', v') # setitem \<delta> w v)"

fun update :: "(string \<times> val) list \<Rightarrow> (string \<times> val) list \<Rightarrow> (string \<times> val) list"
where
"update \<delta> [] = \<delta>" |
"update \<delta> ((w, v) # \<delta>') = update (setitem \<delta> w v) \<delta>'"

(* Entries from keys and values in alternation; None if a key is not a string *)
fun dict_entries :: "val list \<Rightarrow> (string \<times> val) list option"
where
"dict_entries [] = Some []" |
"dict_entries (VLit (LitString w) # v # vs) = map_option (Cons (w, v)) (dict_entries vs)" |
"dict_entries _ = None"

fun elems :: "val \<Rightarrow> val list option"
where
"elems (VList vs) = Some vs" |
"elems (VTuple vs) = Some vs" |
"elems (VLit (LitString w)) = Some (map (\<lambda>c. VLit (LitString [c])) w)" |
"elems _ = None"

fun getitem :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"getitem (VDict \<delta>) (VLit (LitString w)) = (case map_of \<delta> w of Some v \<Rightarrow> Val v | None \<Rightarrow> Aborts KeyError)" |
"getitem (VDict \<delta>) _ = Aborts Excluded" |
"getitem v v' =
  (case (elems v, v') of
     (Some vs, VLit (LitInt n)) \<Rightarrow>
       let m = of_nat (length vs) :: int in
       if 0 \<le> n \<and> n < m then Val (vs ! nat n)
       else if - m \<le> n \<and> n < 0 then Val (vs ! nat (m + n))
       else Aborts IndexError
   | (Some vs, VLit (LitBool _)) \<Rightarrow> Aborts Excluded
   | _ \<Rightarrow> Aborts TypeError)"

fun def_name :: "func \<Rightarrow> var"
where
"def_name (Def f _ _ _ _) = f"

fun binds_pat :: "pat \<Rightarrow> var set"
where
"binds_pat (PatVar x) = {x}" |
"binds_pat (PatAs p x) = binds_pat p \<union> {x}" |
"binds_pat (PatList ps) = \<Union> (set (map binds_pat ps))" |
"binds_pat (PatTuple ps) = \<Union> (set (map binds_pat ps))" |
"binds_pat (PatConstr q (ps, kps)) = \<Union> (set (map binds_pat ps)) \<union> \<Union> (set (map (binds_pat \<circ> snd) kps))" |
"binds_pat (PatDict kps) = \<Union> (set (map (binds_pat \<circ> snd) kps))" |
"binds_pat _ = {}"

fun binds :: "stmt \<Rightarrow> var set"
where
"binds (StmtSeq s s') = binds s \<union> binds s'" |
"binds (StmtIf _ s elifs else') =
  binds s \<union> \<Union> (set (map (\<lambda>(_, s'). binds s') elifs)) \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> binds s')" |
"binds (StmtMatch _ cases) = \<Union> (set (map (\<lambda>(p, s). binds_pat p \<union> binds s) cases))" |
"binds _ = {}"

fun assigns :: "stmt \<Rightarrow> var set"
where
"assigns (StmtDeclare x _) = {x}" |
"assigns (StmtAssign x _ _) = {x}" |
"assigns (StmtSeq s s') = assigns s \<union> assigns s'" |
"assigns (StmtMutualRegion ds) = set (map def_name ds)" |
"assigns (StmtIf _ s elifs else') =
  assigns s \<union> \<Union> (set (map (\<lambda>(_, s'). assigns s') elifs)) \<union> (case else' of None \<Rightarrow> {} | Some s' \<Rightarrow> assigns s')" |
"assigns (StmtMatch _ cases) = \<Union> (set (map (\<lambda>(p, s). binds_pat p \<union> assigns s) cases))" |
"assigns _ = {}"

fun declares :: "stmt \<Rightarrow> var list"
where
"declares (StmtDeclare x _) = [x]" |
"declares (StmtAssign x (Some _) _) = [x]" |
"declares (StmtSeq s s') = declares s @ declares s'" |
"declares (StmtMutualRegion ds) = map def_name ds" |
"declares (StmtIf _ s elifs else') =
  declares s @ concat (map (\<lambda>(_, s'). declares s') elifs) @ (case else' of None \<Rightarrow> [] | Some s' \<Rightarrow> declares s')" |
"declares (StmtMatch _ cases) = concat (map (\<lambda>(_, s). declares s) cases)" |
"declares _ = []"

definition fmconst :: "'a set \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap"
where
"fmconst A u = Finite_Set.fold (\<lambda>x. fmupd x u) fmempty A"

lemma comp_fun_idem_fmupd: "comp_fun_idem_on UNIV (\<lambda>x. fmupd x u)"
  by unfold_locales (auto simp: fun_eq_iff intro!: fmap_ext)

lemma fmconst_code [code]: "fmconst (set xs) u = fold (\<lambda>x. fmupd x u) xs fmempty"
  unfolding fmconst_def by (rule comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_fmupd subset_UNIV])

(* u marks a variable unbound: the value or the context entry *)
definition scope :: "'a \<Rightarrow> var list \<Rightarrow> stmt \<Rightarrow> (var, 'a) fmap option"
where
"scope u ys s =
  (if distinct ys \<and> distinct (declares s)
     \<and> set ys \<inter> set (declares s) = {} \<and> set ys \<inter> binds s = {} \<and> set (declares s) \<inter> binds s = {}
   then Some (fmconst (assigns s - set ys) u)
   else None)"

abbreviation true :: val where "true \<equiv> VLit (LitBool True)"
abbreviation false :: val where "false \<equiv> VLit (LitBool False)"

type_synonym elif_block = "(expr \<times> stmt) list \<times> stmt option"

inductive
  eval_expr  :: "env \<Rightarrow> expr \<Rightarrow> val result \<Rightarrow> bool"            ("_, _ \<Rightarrow>\<^sub>e _" [60,0,60] 60) and
  eval_exprs :: "env \<Rightarrow> expr list \<Rightarrow> val list result \<Rightarrow> bool"  ("_, _ \<Rightarrow>\<^sub>e\<^sub>s _" [60,0,60] 60) and
  eval_stmt  :: "env \<Rightarrow> stmt \<Rightarrow> outcome \<Rightarrow> bool"               ("_, _ \<Rightarrow>\<^sub>s _" [60,0,60] 60) and
  eval_elif  :: "env \<Rightarrow> elif_block \<Rightarrow> outcome \<Rightarrow> bool"         ("_, _ \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f _" [60,0,60] 60)
where
EvalVar: "\<lbrakk> fmlookup \<rho> x = Some v ; v \<noteq> VUnbound \<rbrakk> \<Longrightarrow> \<rho>, ExprVar x \<Rightarrow>\<^sub>e Val v" |
EvalVarUnknown: "fmlookup \<rho> x = None \<Longrightarrow> \<rho>, ExprVar x \<Rightarrow>\<^sub>e Aborts NameError" |
EvalVarUnbound: "fmlookup \<rho> x = Some VUnbound \<Longrightarrow> \<rho>, ExprVar x \<Rightarrow>\<^sub>e Aborts NameError" |
EvalLiteral: "\<rho>, ExprLiteral l \<Rightarrow>\<^sub>e Val (VLit l)" |
EvalLambda: "\<rho>, ExprLambda xs e \<Rightarrow>\<^sub>e Val Lam(\<rho>, xs, e)" |
EvalUnOp: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, ExprUnOp op e \<Rightarrow>\<^sub>e mlet r (unop_meaning op)" |
EvalBinOp: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, e' \<Rightarrow>\<^sub>e r \<rbrakk>
  \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e mlet r (binop_meaning op v)" |
EvalBinOpFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprBinOp op e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalAndFalse: "\<rho>, e \<Rightarrow>\<^sub>e Val false \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e Val false" |
EvalAndTrue: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val true ; \<rho>, e' \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e r" |
EvalAndFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalAndNonBool: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, ExprAnd e e' \<Rightarrow>\<^sub>e Aborts Excluded" |
EvalOrTrue: "\<rho>, e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e Val true" |
EvalOrFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, e' \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e r" |
EvalOrFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalOrNonBool: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, ExprOr e e' \<Rightarrow>\<^sub>e Aborts Excluded" |
EvalCondTrue: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val true ; \<rho>, e1 \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e r" |
EvalCondFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, e2 \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e r" |
EvalCondFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalCondNonBool: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, ExprCond e1 e e2 \<Rightarrow>\<^sub>e Aborts Excluded" |
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
EvalSubscript: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, e' \<Rightarrow>\<^sub>e r \<rbrakk> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e mlet r (getitem v)" |
EvalSubscriptFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprSubscript e e' \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalCallLambda:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xs = length us
  ; \<rho>' \<otimes> fmap_of_list (zip xs us), e' \<Rightarrow>\<^sub>e r
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e r" |
EvalCallLambdaArity:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val Lam(\<rho>', xs, e')
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xs \<noteq> length us
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalCallDef:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val Def(\<rho>', ds, j)
  ; ds ! j = Def f \<alpha>s xps \<psi> s
  ; vs = map (\<lambda>i. Def(\<rho>', ds, i)) [0..<length ds]
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xps = length us
  ; scope VUnbound (map fst xps) s = Some \<rho>s
  ; \<rho>' \<otimes> fmap_of_list (zip (map def_name ds) vs) \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s, s \<Rightarrow>\<^sub>s o
  ; j < length ds
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e call_result o" |
EvalCallDefArity:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val Def(\<rho>', ds, j)
  ; ds ! j = Def f \<alpha>s xps \<psi> s
  ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us
  ; length xps \<noteq> length us
  ; j < length ds
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalCallNonFun:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Val us ; \<not> is_closure v \<rbrakk>
  \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts TypeError" |
EvalCallFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts \<kappa>" |
EvalCallFailArgs:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e Aborts \<kappa>" |

EvalExprsNil: "\<rho>, [] \<Rightarrow>\<^sub>e\<^sub>s Val []" |
EvalExprsCons: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; \<rho>, es \<Rightarrow>\<^sub>e\<^sub>s r \<rbrakk>
  \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s mlet r (\<lambda>vs. Val (v # vs))" |
EvalExprsFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, e # es \<Rightarrow>\<^sub>e\<^sub>s Aborts \<kappa>" |

EvalPass: "\<rho>, StmtPass \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalDeclare: "\<rho>, StmtDeclare x \<psi> \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalAssign: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtAssign x \<pi> e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. Assigns (fmupd x v \<epsilon>))" |
EvalExprStmt: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtExpr e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. Assigns \<epsilon>)" |
EvalReturn: "\<rho>, e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtReturn (Some e) \<Rightarrow>\<^sub>s mlet r (\<lambda>v. Returns v)" |
EvalReturnNone: "\<rho>, StmtReturn None \<Rightarrow>\<^sub>s Returns (VLit LitNone)" |
EvalDefs:
  "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]
  \<Longrightarrow> \<rho>, StmtMutualRegion ds \<Rightarrow>\<^sub>s Assigns (fmap_of_list (zip (map def_name ds) vs))" |
EvalAssert: "\<rho>, e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalAssertFalse: "\<rho>, e \<Rightarrow>\<^sub>e Val false \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s Aborts\<^sub>o (AssertionError None)" |
EvalAssertFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalAssertNonBool:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s Aborts\<^sub>o Excluded" |
EvalAssertMsg: "\<rho>, e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalAssertMsgFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, e' \<Rightarrow>\<^sub>e Val (VLit (LitString w)) \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o (AssertionError (Some w))" |
EvalAssertMsgFalseFail: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalAssertMsgFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalAssertMsgNonBool:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o Excluded" |
EvalAssertMsgNonStr:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, e' \<Rightarrow>\<^sub>e Val v ; \<forall>w. v \<noteq> VLit (LitString w) \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o Excluded" |
EvalIfTrue: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val true ; \<rho>, s \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s o" |
EvalIfFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, (elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s o" |
EvalIfFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalIfNonBool:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s Aborts\<^sub>o Excluded" |
EvalSeq: "\<lbrakk> \<rho>, s \<Rightarrow>\<^sub>s Assigns \<rho>' ; \<rho> \<otimes> \<rho>', s' \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s Assigns \<rho>' \<otimes>\<^sub>o o" |
EvalSeqReturn: "\<rho>, s \<Rightarrow>\<^sub>s Returns v \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s Returns v" |
EvalSeqFail: "\<rho>, s \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa> \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |

EvalIfNone: "\<rho>, ([], None) \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f Assigns \<epsilon>" |
EvalElse: "\<rho>, s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<rho>, ([], Some s) \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifTrue: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val true ; \<rho>, s \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifFalse: "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val false ; \<rho>, (elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<rbrakk>
  \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifFail: "\<rho>, e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f Aborts\<^sub>o \<kappa>" |
EvalElifNonBool:
  "\<lbrakk> \<rho>, e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f Aborts\<^sub>o Excluded"

lemmas eval_induct = eval_expr_eval_exprs_eval_stmt_eval_elif.inducts

end
