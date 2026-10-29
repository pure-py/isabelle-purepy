(* Values, results and evaluation judgements *)
theory Semantics
    imports Types "HOL-Library.Finite_Map"
begin

(* Free o for outcomes, as in the spec *)
no_notation (ASCII) comp (infixl \<open>o\<close> 55)

(* Free o for outcomes, as in the spec *)
no_notation (ASCII) comp (infixl \<open>o\<close> 55)

(* Predefined functions, each standing for its meaning prim_meaning *)
datatype prim = PrimLen | PrimRound | PrimExit

datatype val =
      VLit lit
    | VList "val list"
    | VTuple "val list"
    | VDict "(str \<times> val) list"
    | VClass name
    | VObject name "(var \<times> val) list"
    | VLamClosure "(var, val) fmap" "var list" "expr located"  ("Lam'(_, _, _')")
    | VDefClosure "(var, val) fmap" "func located list" nat  ("Def'(_, _, _')")
    | VModStub name
    | VModLoaded name "(var, val) fmap"
    | VTypeAlias name "type_def located list" nat
    | VUnbound
    | VPrim prim
    | VOpaque name

type_synonym env = "(var, val) fmap"
abbreviation \<epsilon> :: env where "\<epsilon> \<equiv> fmempty"

datatype termination_kind =
    TypeError
  | IndexError
  | KeyError
  | OverflowError
  | ValueError
  | ZeroDivisionError
  | AssertionError "str option"
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

fun is_class :: "val \<Rightarrow> bool"
where
"is_class (VClass _) = True" |
"is_class _ = False"

fun class_of :: "val \<Rightarrow> name option"
where
"class_of (VClass C) = Some C" |
"class_of _ = None"

fun is_object :: "val \<Rightarrow> bool"
where
"is_object (VObject _ _) = True" |
"is_object _ = False"

fun fields_of :: "val \<Rightarrow> (var \<times> val) list option"
where
"fields_of (VObject _ xvs) = Some xvs" |
"fields_of _ = None"

(* Type arguments of a subscript e[\<psi>s], read from its index *)
definition type_args_of :: "expr located \<Rightarrow> ty_expr list option"
where
"type_args_of e' = those (map type_expr_of (subscript_args e'))"

fun is_closure :: "val \<Rightarrow> bool"
where
"is_closure Lam(_, _, _) = True" |
"is_closure Def(_, _, _) = True" |
"is_closure _ = False"

fun is_prim :: "val \<Rightarrow> bool"
where
"is_prim (VPrim _) = True" |
"is_prim _ = False"

fun is_loaded_module :: "val \<Rightarrow> bool"
where
"is_loaded_module (VModLoaded _ _) = True" |
"is_loaded_module _ = False"

fun module_env_of :: "val \<Rightarrow> (var, val) fmap option"
where
"module_env_of (VModLoaded _ \<rho>) = Some \<rho>" |
"module_env_of _ = None"

(* Opaque value of a predefined class of builtins, such as int, which Python matches by an instance test *)
fun opaque_builtin :: "val \<Rightarrow> bool"
where
"opaque_builtin (VOpaque (x, [y])) = ((x, []) = builtins)" |
"opaque_builtin _ = False"

(* Literals by value; a Boolean and a number, which Python compares numerically, give Undef *)
fun eq_lit :: "lit \<Rightarrow> lit \<Rightarrow> bool result"
where
"eq_lit (LitInt n) (LitInt n') = Val (n = n')" |
"eq_lit (LitInt n) (LitFloat x') = Val (float_value x' = Some (ereal (real_of_int n)))" |
"eq_lit (LitFloat x) (LitInt n') = Val (float_value x = Some (ereal (real_of_int n')))" |
"eq_lit (LitFloat x) (LitFloat x') = (if is_nan x \<and> is_nan x' then Aborts Undef else Val (float_value x = float_value x'))" |
"eq_lit (LitString w) (LitString w') = Val (w = w')" |
"eq_lit (LitBool b) (LitBool b') = Val (b = b')" |
"eq_lit LitNone LitNone = Val True" |
"eq_lit (LitBool _) (LitInt _) = Aborts Undef" |
"eq_lit (LitBool _) (LitFloat _) = Aborts Undef" |
"eq_lit (LitInt _) (LitBool _) = Aborts Undef" |
"eq_lit (LitFloat _) (LitBool _) = Aborts Undef" |
"eq_lit _ _ = Val False"

(* By the form of the first value, then of the second: patterns on both would make pattern completion over the
   values very slow. Undefined between two functions, closures or primitives, which Python compares by identity *)
fun eq :: "val \<Rightarrow> val \<Rightarrow> bool result" and eq_elems :: "val list \<Rightarrow> val list \<Rightarrow> bool result"
where
"eq (VLit l) v' = (case v' of VLit l' \<Rightarrow> eq_lit l l' | _ \<Rightarrow> Val False)" |
"eq (VList vs) v' = (case v' of VList vs' \<Rightarrow> eq_elems vs vs' | _ \<Rightarrow> Val False)" |
"eq (VTuple vs) v' = (case v' of VTuple vs' \<Rightarrow> eq_elems vs vs' | _ \<Rightarrow> Val False)" |
"eq (VDict \<delta>) v' =
  (case v' of
     VDict \<delta>' \<Rightarrow>
       if set (map fst \<delta>) = set (map fst \<delta>') then eq_elems (map snd \<delta>) (map (the \<circ> map_of \<delta>') (map fst \<delta>))
       else Val False
   | _ \<Rightarrow> Val False)" |
"eq (VObject C xvs) v' =
  (case v' of VObject D yvs \<Rightarrow> if C = D then eq_elems (map snd xvs) (map snd yvs) else Val False | _ \<Rightarrow> Val False)" |
"eq v v' = (if (is_closure v \<or> is_prim v) \<and> (is_closure v' \<or> is_prim v') then Aborts Undef else Val False)" |

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
"contains (VLit (LitString w')) (VLit (LitString w)) = Val (substring w w')" |
"contains _ _ = Aborts TypeError" |

"contains_elems [] v = Val False" |
"contains_elems (v' # vs) v = (if eq v v' = Val False then contains_elems vs v else eq v v')"

fun is_bool :: "val \<Rightarrow> bool"
where
"is_bool (VLit (LitBool _)) = True" |
"is_bool _ = False"

fun is_nan_val :: "val \<Rightarrow> bool"
where
"is_nan_val (VLit (LitFloat x)) = is_nan x" |
"is_nan_val _ = False"

(* Float of an int or float value; None otherwise *)
fun as_float :: "val \<Rightarrow> float option"
where
"as_float (VLit (LitInt n)) = Some (float_of_int n)" |
"as_float (VLit (LitFloat x)) = Some x" |
"as_float _ = None"

(* Value of a number as an extended real; None for nan and for a non-number *)
fun number_value :: "val \<Rightarrow> ereal option"
where
"number_value (VLit (LitInt n)) = Some (ereal (real_of_int n))" |
"number_value (VLit (LitFloat x)) = float_value x" |
"number_value _ = None"

(* Apply g to two numbers as floats; Excluded for a Boolean operand *)
fun number_op :: "(float \<Rightarrow> float \<Rightarrow> val result) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"number_op g v v' =
  (if is_bool v \<or> is_bool v' then Aborts Excluded
   else case (as_float v, as_float v') of
     (Some x, Some x') \<Rightarrow> g x x'
   | _ \<Rightarrow> Aborts TypeError)"

(* Apply f to two integers, g to two numbers otherwise *)
fun arith :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> (float \<Rightarrow> float \<Rightarrow> float) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"arith f g (VLit (LitInt n)) (VLit (LitInt n')) = Val (VLit (LitInt (f n n')))" |
"arith f g v v' = number_op (\<lambda>x x'. Val (VLit (LitFloat (g x x')))) v v'"

(* Compare two numbers by value; false if either is nan *)
fun compare :: "(ereal \<Rightarrow> ereal \<Rightarrow> bool) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"compare f v v' =
  number_op (\<lambda>_ _. Val (VLit (LitBool (case (number_value v, number_value v') of
    (Some y, Some y') \<Rightarrow> f y y'
  | _ \<Rightarrow> False)))) v v'"

fun binop_meaning :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"binop_meaning BOpEq v v' =
  (if is_nan_val v \<and> is_nan_val v' then Val (VLit (LitBool False))
   else mlet (eq v v') (\<lambda>b. Val (VLit (LitBool b))))" |
"binop_meaning BOpNeq v v' =
  (if is_nan_val v \<and> is_nan_val v' then Val (VLit (LitBool True))
   else mlet (eq v v') (\<lambda>b. Val (VLit (LitBool (\<not> b)))))" |
"binop_meaning BOpIn v v' = mlet (contains v' v) (\<lambda>b. Val (VLit (LitBool b)))" |
"binop_meaning BOpNotIn v v' = mlet (contains v' v) (\<lambda>b. Val (VLit (LitBool (\<not> b))))" |
"binop_meaning BOpLt v v' = compare (<) v v'" |
"binop_meaning BOpLeq v v' = compare (\<le>) v v'" |
"binop_meaning BOpGt v v' = compare (>) v v'" |
"binop_meaning BOpGeq v v' = compare (\<ge>) v v'" |
"binop_meaning BOpAdd v v' = arith (+) float_add v v'" |
"binop_meaning BOpSub v v' = arith (-) float_sub v v'" |
"binop_meaning BOpMul v v' = arith (*) float_mul v v'" |
"binop_meaning BOpDiv v v' =
  (if number_value v' = Some 0 then Aborts ZeroDivisionError
   else number_op (\<lambda>x x'. Val (VLit (LitFloat (float_div x x')))) v v')" |
"binop_meaning BOpFloorDiv v v' =
  (if number_value v' = Some 0 then Aborts ZeroDivisionError else arith (div) float_floordiv v v')" |
"binop_meaning BOpMod v v' =
  (if number_value v' = Some 0 then Aborts ZeroDivisionError else arith (mod) float_mod v v')" |
"binop_meaning BOpPow (VLit (LitInt n)) (VLit (LitInt n')) =
  (if n' \<ge> 0 then Val (VLit (LitInt (n ^ nat n')))
   else if n = 0 then Aborts ZeroDivisionError
   else Val (VLit (LitFloat (float_pow (float_of_int n) (float_of_int n')))))" |
"binop_meaning BOpPow v v' =
  (if number_value v = Some 0 \<and> (case number_value v' of Some y \<Rightarrow> y < 0 | None \<Rightarrow> False) then Aborts ZeroDivisionError
   else number_op (\<lambda>x x'. Val (VLit (LitFloat (float_pow x x')))) v v')" |
"binop_meaning _ _ _ = Aborts TypeError"

fun unop_meaning :: "uop \<Rightarrow> val \<Rightarrow> val result"
where
"unop_meaning UOpNot (VLit (LitBool b)) = Val (VLit (LitBool (\<not> b)))" |
"unop_meaning UOpPos (VLit (LitInt n)) = Val (VLit (LitInt n))" |
"unop_meaning UOpPos (VLit (LitFloat x)) = Val (VLit (LitFloat x))" |
"unop_meaning UOpNeg (VLit (LitInt n)) = Val (VLit (LitInt (- n)))" |
"unop_meaning UOpNeg (VLit (LitFloat x)) = Val (VLit (LitFloat (float_neg x)))" |
"unop_meaning UOpNot _ = Aborts Excluded" |
"unop_meaning _ (VLit (LitBool _)) = Aborts Excluded" |
"unop_meaning _ _ = Aborts TypeError"

fun setitem :: "(str \<times> val) list \<Rightarrow> str \<Rightarrow> val \<Rightarrow> (str \<times> val) list"
where
"setitem [] w v = [(w, v)]" |
"setitem ((w', v') # \<delta>) w v = (if w = w' then (w, v) # \<delta> else (w', v') # setitem \<delta> w v)"

fun update :: "(str \<times> val) list \<Rightarrow> (str \<times> val) list \<Rightarrow> (str \<times> val) list"
where
"update \<delta> [] = \<delta>" |
"update \<delta> ((w, v) # \<delta>') = update (setitem \<delta> w v) \<delta>'"

(* Entries from keys and values in alternation; None if a key is not a string *)
fun dict_entries :: "val list \<Rightarrow> (str \<times> val) list option"
where
"dict_entries [] = Some []" |
"dict_entries (VLit (LitString w) # v # vs) = map_option (Cons (w, v)) (dict_entries vs)" |
"dict_entries _ = None"

fun elems :: "val \<Rightarrow> val list option"
where
"elems (VList vs) = Some vs" |
"elems (VTuple vs) = Some vs" |
"elems (VLit (LitString w)) = Some (map (\<lambda>c. VLit (LitString c)) (str_chars w))" |
"elems _ = None"

(* Elements drawn by a generator: the keys of a dictionary, and the elements of a sequence otherwise *)
fun iter :: "val \<Rightarrow> val list option"
where
"iter (VDict \<delta>) = Some (map (\<lambda>(w, _). VLit (LitString w)) \<delta>)" |
"iter v = elems v"

(* Nearest integer, ties to even *)
definition round_even :: "real \<Rightarrow> int"
where
"round_even x =
  (let n = \<lfloor>x\<rfloor>; d = x - real_of_int n in
   if d < 1 / 2 then n else if 1 / 2 < d then n + 1 else if even n then n else n + 1)"

(* Meanings of the predefined functions *)
fun prim_meaning :: "prim \<Rightarrow> val list \<Rightarrow> val result"
where
"prim_meaning PrimLen [v] = (case iter v of Some vs \<Rightarrow> Val (VLit (LitInt (of_nat (length vs)))) | None \<Rightarrow> Aborts TypeError)" |
"prim_meaning PrimRound [VLit (LitBool _)] = Aborts Excluded" |
"prim_meaning PrimRound [VLit (LitInt n)] = Val (VLit (LitInt n))" |
"prim_meaning PrimRound [VLit (LitFloat x)] =
  (case float_value x of
     None \<Rightarrow> Aborts ValueError
   | Some (ereal r) \<Rightarrow> Val (VLit (LitInt (round_even r)))
   | Some _ \<Rightarrow> Aborts OverflowError)" |
"prim_meaning PrimRound [v, v'] =
  (if (as_float v \<noteq> None \<or> is_bool v) \<and> (case v' of VLit (LitInt _) \<Rightarrow> True | VLit (LitBool _) \<Rightarrow> True | VLit LitNone \<Rightarrow> True | _ \<Rightarrow> False)
   then Aborts Excluded else Aborts TypeError)" |
"prim_meaning PrimExit [VLit (LitInt n)] = Aborts (SystemExit n)" |
"prim_meaning PrimExit [] = Aborts Excluded" |
"prim_meaning PrimExit [v] = Aborts Excluded" |
"prim_meaning _ _ = Aborts TypeError"

fun getitem :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"getitem (VDict \<delta>) v' =
  (case v' of
     VLit (LitString w) \<Rightarrow> (case map_of \<delta> w of Some v \<Rightarrow> Val v | None \<Rightarrow> Aborts KeyError)
   | _ \<Rightarrow> Aborts Excluded)" |
"getitem v v' =
  (case (elems v, v') of
     (Some vs, VLit (LitInt n)) \<Rightarrow>
       let m = of_nat (length vs) :: int in
       if 0 \<le> n \<and> n < m then Val (vs ! nat n)
       else if - m \<le> n \<and> n < 0 then Val (vs ! nat (m + n))
       else Aborts IndexError
   | (Some vs, VLit (LitBool _)) \<Rightarrow> Aborts Excluded
   | _ \<Rightarrow> Aborts TypeError)"

(* Value denoted by a name: a simple name looked up directly, a qualified name in the environment of the loaded
   module denoted by its prefix; None if the prefix denotes a module stub or a value other than a module *)
fun resolve_path :: "val option \<Rightarrow> var list \<Rightarrow> val option"
where
"resolve_path v [] = v" |
"resolve_path (Some (VModLoaded _ \<rho>')) (y # ys) = resolve_path (fmlookup \<rho>' y) ys" |
"resolve_path _ _ = None"

definition resolve :: "env \<Rightarrow> name \<Rightarrow> val option"
where
"resolve \<rho> q = resolve_path (fmlookup \<rho> (fst q)) (snd q)"

datatype match_result = Match env | NoMatch | MatchAborts termination_kind

fun compose_match :: "match_result \<Rightarrow> match_result \<Rightarrow> match_result" (infixl "\<otimes>\<^sub>m" 100)
where
"Match \<rho> \<otimes>\<^sub>m Match \<rho>' = Match (\<rho> \<otimes> \<rho>')" |
"Match \<rho> \<otimes>\<^sub>m m = m" |
"NoMatch \<otimes>\<^sub>m m = NoMatch" |
"MatchAborts \<kappa> \<otimes>\<^sub>m m = MatchAborts \<kappa>"

(* Names a case hypothesis IH when it contains an induction predicate, and hyps otherwise, as for a rule without
   parameters. The induction method also takes the free variables among the conclusion's arguments for predicates,
   which makes every premise mentioning \<Sigma> an IH. *)
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

(* The class table, ambient in evaluation as in the spec *)
locale evaluation = fixes \<Sigma> :: class_table
begin

(* Argument or sub-pattern for each field of C: positional ones fill the fields in order, keyword ones match by
   name; None unless they cover the fields exactly *)
definition field_map :: "name \<Rightarrow> 'a list \<Rightarrow> (var \<times> 'a) list \<Rightarrow> (var \<times> 'a) list option"
where
"field_map C us kvs =
  (let xs = field_names \<Sigma> C; n = length us in
   if n + length kvs = length xs \<and> set (map fst kvs) = set (drop n xs)
   then Some (zip (take n xs) us @ map (\<lambda>y. (y, the (map_of kvs y))) (drop n xs))
   else None)"

(* The head of a constructor pattern resolves as in Python: NameError if its first name is unbound, AttributeError if
   a later name is not found, Excluded if it denotes a predefined class of builtins, which Python matches by an
   instance test, and TypeError if it denotes any other value which is not a class.
   Sub-patterns of a class C match the fields of an object whose class has C among its ancestors: positional ones in
   field order, then keyword ones as written; TypeError for excess positional sub-patterns, a keyword sub-pattern for
   a field already matched by position, or a positional sub-pattern of range, as in Python; Excluded if they otherwise
   do not cover the fields of C exactly *)
fun match :: "env \<Rightarrow> pat \<Rightarrow> val \<Rightarrow> match_result"
  and match_all :: "env \<Rightarrow> pat located list \<Rightarrow> val list \<Rightarrow> match_result"
  and match_dict :: "env \<Rightarrow> (str \<times> pat located) list \<Rightarrow> (str \<times> val) list \<Rightarrow> match_result"
  and match_kws :: "env \<Rightarrow> (var \<times> pat located) list \<Rightarrow> (var \<times> val) list \<Rightarrow> match_result"
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
"match \<rho> (PatConstr (x, xs) (ps, kps)) v =
  (case fmlookup \<rho> x of
     None \<Rightarrow> MatchAborts NameError
   | Some VUnbound \<Rightarrow> MatchAborts NameError
   | Some _ \<Rightarrow>
       case resolve \<rho> (x, xs) of
         None \<Rightarrow> MatchAborts AttributeError
       | Some u \<Rightarrow>
       if opaque_builtin u then MatchAborts Excluded else
       case class_of u of
         None \<Rightarrow> MatchAborts TypeError
       | Some C \<Rightarrow>
           (case v of
              VObject D zvs \<Rightarrow>
                if C \<notin> set (ancestors \<Sigma> D) then NoMatch
                else if C = range_class then MatchAborts (if ps = [] then Excluded else TypeError)
                else
                  let ys = field_names \<Sigma> C; n = length ps in
                  if field_map C ps kps \<noteq> None \<and> set ys \<subseteq> set (map fst zvs)
                  then match_all \<rho> ps (map (\<lambda>y. the (map_of zvs y)) (take n ys)) \<otimes>\<^sub>m match_kws \<rho> kps zvs
                  else if length ys < n \<or> (\<exists>y \<in> set (map fst kps). y \<in> set (take n ys)) then MatchAborts TypeError
                  else MatchAborts Excluded
            | _ \<Rightarrow> NoMatch))" |
"match \<rho> _ _ = NoMatch" |

"match_all \<rho> (p # ps) (v # vs) = match \<rho> (node p) v \<otimes>\<^sub>m match_all \<rho> ps vs" |
"match_all \<rho> _ _ = Match \<epsilon>" |

"match_dict \<rho> ((w, p) # kps) \<delta> = match \<rho> (node p) (the (map_of \<delta> w)) \<otimes>\<^sub>m match_dict \<rho> kps \<delta>" |
"match_dict \<rho> [] \<delta> = Match \<epsilon>" |

"match_kws \<rho> ((y, p) # kps) zvs = match \<rho> (node p) (the (map_of zvs y)) \<otimes>\<^sub>m match_kws \<rho> kps zvs" |
"match_kws \<rho> [] zvs = Match \<epsilon>"

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
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val (VModLoaded q' \<rho>') ; fmlookup \<rho>' x = None \<rbrakk> \<Longrightarrow> \<rho>, ExprAttribute e x \<Rightarrow>\<^sub>e Aborts AttributeError" |
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
  ; \<rho>' \<otimes> fmap_of_list (zip (map (def_name \<circ> node) ds) vs) \<otimes> fmap_of_list (zip (map fst xps) us) \<otimes> \<rho>s, node s \<Rightarrow>\<^sub>s o
  ; j < length ds
  \<rbrakk> \<Longrightarrow> \<rho>, ExprCall e (es, []) \<Rightarrow>\<^sub>e call_result o" |
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

EvalPass: "\<rho>, StmtPass \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalDeclare: "\<rho>, StmtDeclare x \<psi> \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalAssign: "\<rho>, node e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtAssign x \<pi> e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. Assigns (fmupd x v \<epsilon>))" |
EvalExprStmt: "\<rho>, node e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtExpr e \<Rightarrow>\<^sub>s mlet r (\<lambda>v. Assigns \<epsilon>)" |
EvalReturn: "\<rho>, node e \<Rightarrow>\<^sub>e r \<Longrightarrow> \<rho>, StmtReturn (Some e) \<Rightarrow>\<^sub>s mlet r (\<lambda>v. Returns v)" |
EvalReturnNone: "\<rho>, StmtReturn None \<Rightarrow>\<^sub>s Returns (VLit LitNone)" |
EvalDefs:
  "vs = map (\<lambda>i. Def(\<rho>, ds, i)) [0..<length ds]
  \<Longrightarrow> \<rho>, StmtMutualRegion ds \<Rightarrow>\<^sub>s Assigns (fmap_of_list (zip (map (def_name \<circ> node) ds) vs))" |
EvalAssert: "\<rho>, node e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalAssertFalse: "\<rho>, node e \<Rightarrow>\<^sub>e Val false \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s Aborts\<^sub>o (AssertionError None)" |
EvalAssertFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalAssertNonBool:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, StmtAssert e None \<Rightarrow>\<^sub>s Aborts\<^sub>o Excluded" |
EvalAssertMsg: "\<rho>, node e \<Rightarrow>\<^sub>e Val true \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Assigns \<epsilon>" |
EvalAssertMsgFalse: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, node e' \<Rightarrow>\<^sub>e Val (VLit (LitString w)) \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o (AssertionError (Some w))" |
EvalAssertMsgFalseFail: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, node e' \<Rightarrow>\<^sub>e Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalAssertMsgFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalAssertMsgNonBool:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o Excluded" |
EvalAssertMsgNonStr:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, node e' \<Rightarrow>\<^sub>e Val v ; \<forall>w. v \<noteq> VLit (LitString w) \<rbrakk>
  \<Longrightarrow> \<rho>, StmtAssert e (Some e') \<Rightarrow>\<^sub>s Aborts\<^sub>o Excluded" |
EvalIfTrue: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val true ; \<rho>, node s \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s o" |
EvalIfFalse: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, (elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s o" |
EvalIfFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalIfNonBool:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, StmtIf e s elifs else' \<Rightarrow>\<^sub>s Aborts\<^sub>o Excluded" |
EvalMatch:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; dispatch \<rho> v cases = Val (\<rho>', s') ; \<rho> \<otimes> \<rho>', node s' \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtMatch e cases \<Rightarrow>\<^sub>s Assigns \<rho>' \<otimes>\<^sub>o o" |
EvalMatchFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, StmtMatch e cases \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalMatchAbort:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; dispatch \<rho> v cases = Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, StmtMatch e cases \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |
EvalSeq: "\<lbrakk> \<rho>, node s \<Rightarrow>\<^sub>s Assigns \<rho>' ; \<rho> \<otimes> \<rho>', node s' \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s Assigns \<rho>' \<otimes>\<^sub>o o" |
EvalSeqReturn: "\<rho>, node s \<Rightarrow>\<^sub>s Returns v \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s Returns v" |
EvalSeqFail: "\<rho>, node s \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa> \<Longrightarrow> \<rho>, StmtSeq s s' \<Rightarrow>\<^sub>s Aborts\<^sub>o \<kappa>" |

EvalIfNone: "\<rho>, ([], None) \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f Assigns \<epsilon>" |
EvalElse: "\<rho>, node s \<Rightarrow>\<^sub>s o \<Longrightarrow> \<rho>, ([], Some s) \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifTrue: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val true ; \<rho>, node s \<Rightarrow>\<^sub>s o \<rbrakk>
  \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifFalse: "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val false ; \<rho>, (elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o \<rbrakk>
  \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f o" |
EvalElifFail: "\<rho>, node e \<Rightarrow>\<^sub>e Aborts \<kappa> \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f Aborts\<^sub>o \<kappa>" |
EvalElifNonBool:
  "\<lbrakk> \<rho>, node e \<Rightarrow>\<^sub>e Val v ; v \<notin> {true, false} \<rbrakk> \<Longrightarrow> \<rho>, ((e, s) # elifs, else') \<Rightarrow>\<^sub>e\<^sub>l\<^sub>i\<^sub>f Aborts\<^sub>o Excluded" |

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

(* Value of the name declared by definition i of a mutual type region of module q: as in the spec, the context entry
   of the definition, an alias value recording the region in place of the context entry's context *)
definition type_value :: "name \<Rightarrow> type_def located list \<Rightarrow> nat \<Rightarrow> val"
where
"type_value q \<chi>s i = (case node (\<chi>s ! i) of Dataclass c _ _ _ \<Rightarrow> VClass (snoc q c) | TypeStmt _ _ _ \<Rightarrow> VTypeAlias q \<chi>s i)"

(* Top-level statement t of module q *)
inductive eval_top :: "name \<Rightarrow> env \<Rightarrow> top_stmt \<Rightarrow> outcome \<Rightarrow> bool"  ("_, _, _ \<Rightarrow>\<^sub>t _" [60,60,0,60] 60)
where
EvalTopStmt: "\<rho>, node s \<Rightarrow>\<^sub>s o \<Longrightarrow> q, \<rho>, Stmt s \<Rightarrow>\<^sub>t o" |
EvalTopSeq: "\<lbrakk> q, \<rho>, t \<Rightarrow>\<^sub>t Assigns \<rho>' ; q, \<rho> \<otimes> \<rho>', t' \<Rightarrow>\<^sub>t o \<rbrakk> \<Longrightarrow> q, \<rho>, TopSeq t t' \<Rightarrow>\<^sub>t Assigns \<rho>' \<otimes>\<^sub>o o" |
EvalTopSeqFail: "q, \<rho>, t \<Rightarrow>\<^sub>t Aborts\<^sub>o \<kappa> \<Longrightarrow> q, \<rho>, TopSeq t t' \<Rightarrow>\<^sub>t Aborts\<^sub>o \<kappa>" |
EvalTypes:
  "q, \<rho>, TypeDefs \<chi>s \<Rightarrow>\<^sub>t Assigns (fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_value q \<chi>s j)) [0..<length \<chi>s]))"

end


(* Environments of the predefined modules: each binds __name__ to the name of the module and each member to its
   value; print and sys.argv, which the spec gives no value, are left out *)
definition predefined_env :: "(name, env) fmap"
where
"predefined_env =
  (let name = \<lambda>x. (var ''__name__'', VLit (LitString (str_of x))) in
   fmap_of_list
    [(builtins, fmap_of_list
       ([name ''builtins'', (var ''len'', VPrim PrimLen), (var ''range'', VClass range_class),
         (var ''round'', VPrim PrimRound)]
        @ map (\<lambda>y. (y, VOpaque (snoc builtins y)))
            (map prim_name [NoneType, object, bool, int, float, str] @ map var [''list'', ''dict'', ''tuple'']))),
     ((var ''sys'', []), fmap_of_list [name ''sys'', (var ''exit'', VPrim PrimExit)]),
     ((var ''typing'', []), fmap_of_list
       (name ''typing'' # map (\<lambda>y. (y, VOpaque (var ''typing'', [y])))
          [var ''Callable'', var ''Literal'', prim_name Never, prim_name Sized])),
     ((var ''dataclasses'', []), fmap_of_list
       [name ''dataclasses'', (var ''dataclass'', VOpaque (var ''dataclasses'', [var ''dataclass'']))])])"

(* Extension of environments, with the equations of context extension on values: a loaded module extends a stub
   of itself, and two loads of one module merge *)
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

fun stub_of :: "val \<Rightarrow> name option"
where
"stub_of (VModStub q) = Some q" |
"stub_of _ = None"

fun is_stub :: "val \<Rightarrow> bool"
where
"is_stub (VModStub _) = True" |
"is_stub _ = False"

lemma stub_of_Some: "stub_of v = Some q \<longleftrightarrow> v = VModStub q"
  by (cases v) auto

lemma stub_of_None: "stub_of v = None \<longleftrightarrow> \<not> is_stub v"
  by (cases v) auto

(* The program, ambient in loading as in the spec *)
locale loading = evaluation +
  fixes M :: program
begin

(* Environment that binds each submodule of q to a stub; the predefined modules have no submodules *)
definition submods_env :: "name \<Rightarrow> env"
where
"submods_env q = fmmap (\<lambda>\<theta>. case \<theta> of ModStub q' \<Rightarrow> VModStub q' | _ \<Rightarrow> VUnbound) (submods M q)"

abbreviation builtins_env :: env where "builtins_env \<equiv> the (fmlookup predefined_env builtins)"

(* Loading of a module, an import prefix, a submodule chain and an imported name, with lists of modules loaded for
   their aborts and of imported names, which the spec writes with premises for each element *)
inductive
  eval_mod     :: "name \<Rightarrow> env result \<Rightarrow> bool"                     ("_ \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d _" [60,60] 60) and
  eval_imports :: "name \<Rightarrow> import located list \<Rightarrow> env result \<Rightarrow> bool"       ("_, _ \<Rightarrow>\<^sub>i _" [60,0,60] 60) and
  eval_sub     :: "name \<Rightarrow> env \<Rightarrow> var list \<Rightarrow> env result \<Rightarrow> bool" ("_, _, _ \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b _" [60,60,0,60] 60) and
  eval_imp     :: "env \<Rightarrow> var \<Rightarrow> val result \<Rightarrow> bool"              ("_, _ \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p _" [60,0,60] 60) and
  eval_imps    :: "env \<Rightarrow> var list \<Rightarrow> val list result \<Rightarrow> bool"    ("_, _ \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s _" [60,0,60] 60) and
  eval_mods    :: "name list \<Rightarrow> unit result \<Rightarrow> bool"                ("_ \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s _" [60,60] 60)
where
EvalPredefined: "fmlookup predefined_env q = Some \<rho> \<Longrightarrow> q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho>" |
EvalModule:
  "\<lbrakk> fmlookup M q = Some (ModuleBody \<iota>s t) ; q, \<iota>s \<Rightarrow>\<^sub>i Val \<rho>' ; scope VUnbound (declares \<iota>s) t = Some \<rho>s
  ; q, builtins_env \<otimes> \<rho>' \<otimes> \<rho>s, t \<Rightarrow>\<^sub>t Assigns \<rho>''
  \<rbrakk> \<Longrightarrow> q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val (submods_env q \<otimes> \<rho>'')" |
EvalModuleFail: "\<lbrakk> fmlookup M q = Some (ModuleBody \<iota>s t) ; q, \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa> \<rbrakk> \<Longrightarrow> q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa>" |
EvalModuleFailBody:
  "\<lbrakk> fmlookup M q = Some (ModuleBody \<iota>s t) ; q, \<iota>s \<Rightarrow>\<^sub>i Val \<rho>' ; scope VUnbound (declares \<iota>s) t = Some \<rho>s
  ; q, builtins_env \<otimes> \<rho>' \<otimes> \<rho>s, t \<Rightarrow>\<^sub>t Aborts\<^sub>o \<kappa>
  \<rbrakk> \<Longrightarrow> q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa>" |

EvalImportsNil: "q, [] \<Rightarrow>\<^sub>i Val \<epsilon>" |
EvalImport:
  "\<lbrakk> (x, []) \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> ; (x, []), \<rho>, xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Val \<rho>'' ; q, \<iota>s \<Rightarrow>\<^sub>i r \<rbrakk>
  \<Longrightarrow> q, At p (Import (x, xs)) # \<iota>s \<Rightarrow>\<^sub>i mlet r (\<lambda>\<rho>'. Val (fmupd x (VModLoaded (x, []) \<rho>'') \<epsilon> \<uplus>\<^sub>v \<rho>'))" |
EvalImportFail: "(x, []) \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa> \<Longrightarrow> q, At p (Import (x, xs)) # \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa>" |
EvalImportFailChain:
  "\<lbrakk> (x, []) \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> ; (x, []), \<rho>, xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Aborts \<kappa> \<rbrakk> \<Longrightarrow> q, At p (Import (x, xs)) # \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa>" |
EvalFromImport:
  "\<lbrakk> unique_to q' q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s Val () ; q' \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> ; \<rho>, xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Val vs ; q, \<iota>s \<Rightarrow>\<^sub>i r \<rbrakk>
  \<Longrightarrow> q, At p (FromImport q' xs) # \<iota>s \<Rightarrow>\<^sub>i mlet r (\<lambda>\<rho>''. Val (fmap_of_list (zip xs vs) \<uplus>\<^sub>v \<rho>''))" |
EvalFromImportFail:
  "\<lbrakk> unique_to q' q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s Val () ; q' \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa> \<rbrakk> \<Longrightarrow> q, At p (FromImport q' xs) # \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa>" |
EvalFromImportFailContaining:
  "unique_to q' q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s Aborts \<kappa> \<Longrightarrow> q, At p (FromImport q' xs) # \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa>" |
EvalFromImportFailMember:
  "\<lbrakk> unique_to q' q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s Val () ; q' \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> ; \<rho>, xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Aborts \<kappa> \<rbrakk>
  \<Longrightarrow> q, At p (FromImport q' xs) # \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa>" |

EvalSubmodulesNil: "q, \<rho>, [] \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Val \<rho>" |
EvalSubmodulesCons:
  "\<lbrakk> snoc q x \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho>' ; snoc q x, \<rho>', xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b r \<rbrakk>
  \<Longrightarrow> q, \<rho>, x # xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b mlet r (\<lambda>\<rho>''. Val (\<rho> \<uplus>\<^sub>v fmupd x (VModLoaded (snoc q x) \<rho>'') \<epsilon>))" |
EvalSubmodulesFail: "snoc q x \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa> \<Longrightarrow> q, \<rho>, x # xs \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b Aborts \<kappa>" |

EvalImpMember: "\<lbrakk> fmlookup \<rho> x = Some v ; \<not> is_stub v \<rbrakk> \<Longrightarrow> \<rho>, x \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p Val v" |
EvalImpSubmodule:
  "\<lbrakk> fmlookup \<rho> x = Some (VModStub q') ; q' \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho>' \<rbrakk> \<Longrightarrow> \<rho>, x \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p Val (VModLoaded q' \<rho>')" |
EvalImpSubmoduleFail:
  "\<lbrakk> fmlookup \<rho> x = Some (VModStub q') ; q' \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa> \<rbrakk> \<Longrightarrow> \<rho>, x \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p Aborts \<kappa>" |

EvalImpsNil: "\<rho>, [] \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Val []" |
EvalImpsCons:
  "\<lbrakk> \<rho>, x \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p Val v ; \<rho>, xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s r \<rbrakk> \<Longrightarrow> \<rho>, x # xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s mlet r (\<lambda>vs. Val (v # vs))" |
EvalImpsFail: "\<rho>, x \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p Aborts \<kappa> \<Longrightarrow> \<rho>, x # xs \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s Aborts \<kappa>" |

EvalModsNil: "[] \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s Val ()" |
EvalModsCons: "\<lbrakk> q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> ; qs \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s r \<rbrakk> \<Longrightarrow> q # qs \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s r" |
EvalModsFail: "q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa> \<Longrightarrow> q # qs \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s Aborts \<kappa>"

(* A program exits with 0 if __main__ loads, and otherwise with the termination kind of loading *)
inductive eval_program :: "termination_kind \<Rightarrow> bool"
where
EvalProgram: "main \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> \<Longrightarrow> eval_program (SystemExit 0)" |
EvalProgramAbort: "main \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa> \<Longrightarrow> eval_program \<kappa>"

(* No module of the program is predefined, as well-formedness of programs requires *)
context
  assumes disjoint: "fmdom M |\<inter>| fmdom predefined_env = {||}"
begin

lemma predefined_not_module: "fmlookup predefined_env q = Some \<rho> \<Longrightarrow> fmlookup M q = Some b \<Longrightarrow> False"
  using disjoint by (auto dest!: fmdomI)

lemma module_not_predefined: "fmlookup M q = Some b \<Longrightarrow> fmlookup predefined_env q = None"
  by (cases "fmlookup predefined_env q") (use predefined_not_module[of q _ b] in auto)

end

end

end
