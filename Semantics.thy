(* Values, results and evaluation judgements *)
theory Semantics
    imports Subtyping "HOL-Library.Finite_Map"
begin

(* Free o for outcomes *)
no_notation (ASCII) comp (infixl \<open>o\<close> 55)

(* Predefined functions, each standing for its meaning *)
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
    | VPredef name

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

datatype completion = Assigns env | Returns val | Aborts\<^sub>\<omega> termination_kind

type_synonym outcome = "val list \<times> completion"

abbreviation assigns\<^sub>o :: "env \<Rightarrow> outcome" where "assigns\<^sub>o \<rho> \<equiv> ([], Assigns \<rho>)"
abbreviation returns\<^sub>o :: "val \<Rightarrow> outcome" where "returns\<^sub>o v \<equiv> ([], Returns v)"
abbreviation aborts\<^sub>o :: "termination_kind \<Rightarrow> outcome" where "aborts\<^sub>o \<kappa> \<equiv> ([], Aborts\<^sub>\<omega> \<kappa>)"

consts mlet :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b"

fun mlet_result :: "'a result \<Rightarrow> ('a \<Rightarrow> 'b result) \<Rightarrow> 'b result"
where
"mlet_result (Val v) f = f v" |
"mlet_result (Aborts \<kappa>) f = Aborts \<kappa>"

fun mlet_outcome :: "'a result \<Rightarrow> ('a \<Rightarrow> outcome) \<Rightarrow> outcome"
where
"mlet_outcome (Val v) f = f v" |
"mlet_outcome (Aborts \<kappa>) f = aborts\<^sub>o \<kappa>"

adhoc_overloading mlet \<rightleftharpoons> mlet_result mlet_outcome

fun seq_compose :: "outcome \<Rightarrow> outcome \<Rightarrow> outcome" (infixl "\<otimes>\<^sub>o" 100)
where
"(vs, Returns v) \<otimes>\<^sub>o o = (vs, Returns v)" |
"(vs, Aborts\<^sub>\<omega> \<kappa>) \<otimes>\<^sub>o o = (vs, Aborts\<^sub>\<omega> \<kappa>)" |
"(vs, Assigns \<rho>) \<otimes>\<^sub>o (vs', Assigns \<rho>') = (vs @ vs', Assigns (\<rho> \<otimes> \<rho>'))" |
"(vs, Assigns \<rho>) \<otimes>\<^sub>o (vs', \<omega>) = (vs @ vs', \<omega>)"

fun result_of :: "completion \<Rightarrow> val result"
where
"result_of (Returns v) = Val v" |
"result_of (Assigns \<rho>) = Val (VLit LitNone)" |
"result_of (Aborts\<^sub>\<omega> \<kappa>) = Aborts \<kappa>"

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
fun is_opaque_builtin :: "val \<Rightarrow> bool"
where
"is_opaque_builtin (VPredef (x, [y])) = ((x, []) = builtins)" |
"is_opaque_builtin _ = False"

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

(* Value of a number as an extended real; None for nan or a non-number *)
fun as_number :: "val \<Rightarrow> ereal option"
where
"as_number (VLit (LitInt n)) = Some (ereal (real_of_int n))" |
"as_number (VLit (LitFloat x)) = float_value x" |
"as_number _ = None"

fun type_of :: "val \<Rightarrow> ty"
where
"type_of (VLit (LitFloat _)) = TyPrim float" |
"type_of (VLit l) = TyLiteral l" |
"type_of (VList _) = TyList (TyPrim object)" |
"type_of (VTuple vs) = TyTuple (map (\<lambda>_. TyPrim object) vs)" |
"type_of (VDict _) = TyDict (TyPrim object)" |
"type_of _ = TyPrim object"

fun the_int :: "val \<Rightarrow> int"
where
"the_int (VLit (LitInt n)) = n"

fun the_str :: "val \<Rightarrow> str"
where
"the_str (VLit (LitString w)) = w"

fun the_elems :: "val \<Rightarrow> val list"
where
"the_elems (VList vs) = vs" |
"the_elems (VTuple vs) = vs"

fun eq_lit :: "lit \<Rightarrow> lit \<Rightarrow> bool result"
where
"eq_lit (LitInt n) (LitInt n') = Val (n = n')" |
"eq_lit (LitInt n) (LitFloat x') = Val (float_value x' = Some (ereal (real_of_int n)))" |
"eq_lit (LitFloat x) (LitInt n') = Val (float_value x = Some (ereal (real_of_int n')))" |
"eq_lit (LitFloat x) (LitFloat x') =
  (if is_nan x \<and> is_nan x' then Aborts Undef else Val (float_value x = float_value x'))" |
"eq_lit (LitString w) (LitString w') = Val (w = w')" |
"eq_lit (LitBool b) (LitBool b') = Val (b = b')" |
"eq_lit LitNone LitNone = Val True" |
"eq_lit (LitBool _) (LitInt _) = Aborts Undef" |
"eq_lit (LitBool _) (LitFloat _) = Aborts Undef" |
"eq_lit (LitInt _) (LitBool _) = Aborts Undef" |
"eq_lit (LitFloat _) (LitBool _) = Aborts Undef" |
"eq_lit _ _ = Val False"

(* Cases on the form of the first value, then of the second, since patterns on both make pattern completion over
   the values very slow *)
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
  (case v' of
     VObject D yvs \<Rightarrow> if C = D then eq_elems (map snd xvs) (map snd yvs) else Val False
   | _ \<Rightarrow> Val False)" |
"eq v v' = (if (is_closure v \<or> is_prim v) \<and> (is_closure v' \<or> is_prim v') then Aborts Undef else Val False)" |

"eq_elems [] [] = Val True" |
"eq_elems (v # vs) (v' # vs') =
  (if length vs \<noteq> length vs' then Val False
   else if eq v v' = Val True then eq_elems vs vs' else eq v v')" |
"eq_elems _ _ = Val False"

fun in_op :: "val \<Rightarrow> val \<Rightarrow> bool result" and in_elems :: "val \<Rightarrow> val list \<Rightarrow> bool result"
where
"in_op v (VList vs) = in_elems v vs" |
"in_op v (VTuple vs) = in_elems v vs" |
"in_op (VLit (LitString w)) (VDict \<delta>) = Val (w \<in> set (map fst \<delta>))" |
"in_op _ (VDict \<delta>) = Aborts Excluded" |
"in_op (VLit (LitString w)) (VLit (LitString w')) = Val (substring w w')" |
"in_op _ (VObject C _) = Aborts (if C = range_class then Excluded else TypeError)" |
"in_op _ _ = Aborts TypeError" |

"in_elems v [] = Val False" |
"in_elems v (v' # vs) = (if eq v v' = Val False then in_elems v vs else eq v v')"

fun elems :: "val \<Rightarrow> val list option"
where
"elems (VList vs) = Some vs" |
"elems (VTuple vs) = Some vs" |
"elems (VLit (LitString w)) = Some (map (\<lambda>c. VLit (LitString c)) (str_chars w))" |
"elems _ = None"

fun iter :: "val \<Rightarrow> val list option"
where
"iter (VDict \<delta>) = Some (map (\<lambda>(w, _). VLit (LitString w)) \<delta>)" |
"iter v = elems v"

fun getitem :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"getitem (VDict \<delta>) v' =
  (case v' of
     VLit (LitString w) \<Rightarrow> (case map_of \<delta> w of Some v \<Rightarrow> Val v | None \<Rightarrow> Aborts KeyError)
   | _ \<Rightarrow> Aborts Excluded)" |
"getitem (VObject C _) _ = Aborts (if C = range_class then Excluded else TypeError)" |
"getitem v v' =
  (case (elems v, v') of
     (Some vs, VLit (LitInt n)) \<Rightarrow>
       let m = of_nat (length vs) :: int in
       if 0 \<le> n \<and> n < m then Val (vs ! nat n)
       else if - m \<le> n \<and> n < 0 then Val (vs ! nat (m + n))
       else Aborts IndexError
   | (Some vs, VLit (LitBool _)) \<Rightarrow> Aborts Excluded
   | _ \<Rightarrow> Aborts TypeError)"

fun setitem :: "(str \<times> val) list \<Rightarrow> str \<Rightarrow> val \<Rightarrow> (str \<times> val) list"
where
"setitem [] w v = [(w, v)]" |
"setitem ((w', v') # \<delta>) w v = (if w = w' then (w, v) # \<delta> else (w', v') # setitem \<delta> w v)"

fun update :: "(str \<times> val) list \<Rightarrow> (str \<times> val) list \<Rightarrow> (str \<times> val) list"
where
"update \<delta> [] = \<delta>" |
"update \<delta> ((w, v) # \<delta>') = update (setitem \<delta> w v) \<delta>'"

fun dict_entries :: "val list \<Rightarrow> (str \<times> val) list option"
where
"dict_entries [] = Some []" |
"dict_entries (VLit (LitString w) # v # vs) = map_option (Cons (w, v)) (dict_entries vs)" |
"dict_entries _ = None"

abbreviation bool_val :: "bool result \<Rightarrow> val result"
where "bool_val r \<equiv> mlet r (\<lambda>b. Val (VLit (LitBool b)))"

definition compare_numbers :: "(ereal \<Rightarrow> ereal \<Rightarrow> bool) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"compare_numbers f v v' =
  Val (VLit (LitBool (case (as_number v, as_number v') of (Some y, Some y') \<Rightarrow> f y y' | _ \<Rightarrow> False)))"

definition compare_strings :: "(str \<Rightarrow> str \<Rightarrow> bool) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"compare_strings f v v' = Val (VLit (LitBool (f (the_str v) (the_str v'))))"

definition int_arith :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"int_arith f v v' = Val (VLit (LitInt (f (the_int v) (the_int v'))))"

definition int_division :: "(int \<Rightarrow> int \<Rightarrow> int) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"int_division f v v' = (if the_int v' = 0 then Aborts ZeroDivisionError else int_arith f v v')"

definition float_arith :: "(float \<Rightarrow> float \<Rightarrow> float) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"float_arith g v v' = Val (VLit (LitFloat (g (the (as_float v)) (the (as_float v')))))"

definition float_division :: "(float \<Rightarrow> float \<Rightarrow> float) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"float_division g v v' = (if as_number v' = Some 0 then Aborts ZeroDivisionError else float_arith g v v')"

definition int_power :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"int_power v v' =
  (if the_int v' \<ge> 0 then int_arith (\<lambda>n n'. n ^ nat n') v v'
   else if the_int v = 0 then Aborts ZeroDivisionError
   else float_arith float_pow v v')"

definition float_power :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"float_power v v' =
  (if as_number v = Some 0 \<and> (\<exists>y. as_number v' = Some y \<and> y < 0) then Aborts ZeroDivisionError
   else float_arith float_pow v v')"

definition concat_str :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"concat_str v v' = Val (VLit (LitString (str_append (the_str v) (the_str v'))))"

definition concat_list :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"concat_list v v' = Val (VList (the_elems v @ the_elems v'))"

definition concat_tuple :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"concat_tuple v v' = Val (VTuple (the_elems v @ the_elems v'))"

definition repeat_str :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"repeat_str v v' = Val (VLit (LitString (str_concat (replicate (nat (the_int v')) (the_str v)))))"

definition repeat_list :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"repeat_list v v' = Val (VList (concat (replicate (nat (the_int v')) (the_elems v))))"

fun negate :: "val \<Rightarrow> val"
where
"negate (VLit (LitInt n)) = VLit (LitInt (- n))" |
"negate (VLit (LitFloat x)) = VLit (LitFloat (float_neg x))"

(* Nearest integer, ties to even *)
definition round_even :: "real \<Rightarrow> int"
where
"round_even x =
  (let n = \<lfloor>x\<rfloor>; d = x - real_of_int n in
   if d < 1 / 2 then n else if 1 / 2 < d then n + 1 else if even n then n else n + 1)"

(* Meanings of the predefined functions *)
fun prim_meaning :: "prim \<Rightarrow> val list \<Rightarrow> val result"
where
"prim_meaning PrimLen [v] =
  (case iter v of Some vs \<Rightarrow> Val (VLit (LitInt (of_nat (length vs)))) | None \<Rightarrow> Aborts TypeError)" |
"prim_meaning PrimRound [VLit (LitBool _)] = Aborts Excluded" |
"prim_meaning PrimRound [VLit (LitInt n)] = Val (VLit (LitInt n))" |
"prim_meaning PrimRound [VLit (LitFloat x)] =
  (case float_value x of
     None \<Rightarrow> Aborts ValueError
   | Some (ereal r) \<Rightarrow> Val (VLit (LitInt (round_even r)))
   | Some _ \<Rightarrow> Aborts OverflowError)" |
"prim_meaning PrimRound [v, v'] =
  (if (as_float v \<noteq> None \<or> is_bool v) \<and>
      (case v' of VLit (LitInt _) \<Rightarrow> True | VLit (LitBool _) \<Rightarrow> True | VLit LitNone \<Rightarrow> True | _ \<Rightarrow> False)
   then Aborts Excluded else Aborts TypeError)" |
"prim_meaning PrimExit [VLit (LitInt n)] = Aborts (SystemExit n)" |
"prim_meaning PrimExit [] = Aborts Excluded" |
"prim_meaning PrimExit [v] = Aborts Excluded" |
"prim_meaning _ _ = Aborts TypeError"

fun resolve_path :: "val option \<Rightarrow> var list \<Rightarrow> val option"
where
"resolve_path v [] = v" |
"resolve_path (Some (VModLoaded _ \<rho>')) (y # ys) = resolve_path (fmlookup \<rho>' y) ys" |
"resolve_path _ _ = None"

definition resolve :: "env \<Rightarrow> name \<Rightarrow> val option"
where
"resolve \<rho> q = resolve_path (fmlookup \<rho> (fst q)) (snd q)"

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

locale evaluation = fixes \<Sigma> :: class_table
begin

definition applies :: "ty \<Rightarrow> val \<Rightarrow> bool"
where
"applies \<tau> v = (\<Sigma> \<turnstile> type_of v <: \<tau>)"

type_synonym overload = "(val \<Rightarrow> val \<Rightarrow> bool) \<times> (val \<Rightarrow> val \<Rightarrow> val result)"

definition bounds :: "ty \<Rightarrow> ty \<Rightarrow> (val \<Rightarrow> val \<Rightarrow> val result) \<Rightarrow> overload"
where
"bounds \<tau> \<tau>' f = ((\<lambda>v v'. applies \<tau> v \<and> applies \<tau>' v'), f)"

(* Overload with meaning f at the tuple types of the operands, one for each pair of lengths *)
definition tuple_bounds :: "(val \<Rightarrow> val \<Rightarrow> val result) \<Rightarrow> overload"
where
"tuple_bounds f = ((\<lambda>v v'. case (v, v') of (VTuple _, VTuple _) \<Rightarrow> True | _ \<Rightarrow> False), f)"

(* Run-time overloads of each binary operator, in order of specificity, so that the first which applies is the
   most specific *)
fun overloads :: "bop \<Rightarrow> overload list"
where
"overloads BOpEq =
  [bounds (TyPrim object) (TyPrim object)
    (\<lambda>v v'. if is_nan_val v \<and> is_nan_val v' then Val (VLit (LitBool False)) else bool_val (eq v v'))]" |
"overloads BOpNeq =
  [bounds (TyPrim object) (TyPrim object)
    (\<lambda>v v'. if is_nan_val v \<and> is_nan_val v' then Val (VLit (LitBool True))
             else bool_val (mlet (eq v v') (\<lambda>b. Val (\<not> b))))]" |
"overloads BOpIn = [bounds (TyPrim object) (TyPrim object) (\<lambda>v v'. bool_val (in_op v v'))]" |
"overloads BOpNotIn =
  [bounds (TyPrim object) (TyPrim object) (\<lambda>v v'. bool_val (mlet (in_op v v') (\<lambda>b. Val (\<not> b))))]" |
"overloads BOpLt =
  [bounds (TyPrim float) (TyPrim float) (compare_numbers (<)), bounds (TyPrim str) (TyPrim str) (compare_strings (<))]" |
"overloads BOpLeq =
  [bounds (TyPrim float) (TyPrim float) (compare_numbers (\<le>)), bounds (TyPrim str) (TyPrim str) (compare_strings (\<le>))]" |
"overloads BOpGt =
  [bounds (TyPrim float) (TyPrim float) (compare_numbers (>)), bounds (TyPrim str) (TyPrim str) (compare_strings (>))]" |
"overloads BOpGeq =
  [bounds (TyPrim float) (TyPrim float) (compare_numbers (\<ge>)), bounds (TyPrim str) (TyPrim str) (compare_strings (\<ge>))]" |
"overloads BOpAdd =
  [bounds (TyPrim int) (TyPrim int) (int_arith (+)), bounds (TyPrim float) (TyPrim float) (float_arith float_add),
   bounds (TyPrim str) (TyPrim str) concat_str, bounds (TyList (TyPrim object)) (TyList (TyPrim object)) concat_list,
   tuple_bounds concat_tuple]" |
"overloads BOpSub =
  [bounds (TyPrim int) (TyPrim int) (int_arith (-)), bounds (TyPrim float) (TyPrim float) (float_arith float_sub)]" |
"overloads BOpMul =
  [bounds (TyPrim int) (TyPrim int) (int_arith (*)), bounds (TyPrim float) (TyPrim float) (float_arith float_mul),
   bounds (TyPrim str) (TyPrim int) repeat_str, bounds (TyPrim int) (TyPrim str) (\<lambda>v v'. repeat_str v' v),
   bounds (TyList (TyPrim object)) (TyPrim int) repeat_list,
   bounds (TyPrim int) (TyList (TyPrim object)) (\<lambda>v v'. repeat_list v' v)]" |
"overloads BOpDiv = [bounds (TyPrim float) (TyPrim float) (float_division float_div)]" |
"overloads BOpFloorDiv =
  [bounds (TyPrim int) (TyPrim int) (int_division (div)),
   bounds (TyPrim float) (TyPrim float) (float_division float_floordiv)]" |
"overloads BOpMod =
  [bounds (TyPrim int) (TyPrim int) (int_division (mod)),
   bounds (TyPrim float) (TyPrim float) (float_division float_mod)]" |
"overloads BOpPow = [bounds (TyPrim int) (TyPrim int) int_power, bounds (TyPrim float) (TyPrim float) float_power]" |
"overloads BOpBitOr = []"

fun select :: "overload list \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"select [] v v' = Aborts Excluded" |
"select ((p, f) # fs) v v' = (if p v v' then f v v' else select fs v v')"

definition binop_meaning :: "bop \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"binop_meaning op v v' = select (overloads op) v v'"

fun unop_meaning :: "uop \<Rightarrow> val \<Rightarrow> val result"
where
"unop_meaning UOpNot v =
  (if applies (TyPrim bool) v then Val (VLit (LitBool (v \<noteq> VLit (LitBool True)))) else Aborts Excluded)" |
"unop_meaning UOpPos v = (if applies (TyPrim float) v then Val v else Aborts Excluded)" |
"unop_meaning UOpNeg v = (if applies (TyPrim float) v then Val (negate v) else Aborts Excluded)"

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
"match \<rho> (PatConstr (x, xs) (ps, kps)) v =
  (case do {
      u \<leftarrow> or_else NameError (fmlookup \<rho> x);
      ensure (u \<noteq> VUnbound) NameError;
      u' \<leftarrow> or_else AttributeError (resolve \<rho> (x, xs));
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
  (case node (\<chi>s ! i) of Dataclass c _ _ _ \<Rightarrow> VClass (snoc q c) | TypeStmt _ _ _ \<Rightarrow> VTypeAlias q \<chi>s i)"

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

(* sys.argv is empty until the predefined environments take the command-line arguments as a parameter *)
definition \<P>\<^sub>e\<^sub>n\<^sub>v :: "(name, env) fmap"
where
"\<P>\<^sub>e\<^sub>n\<^sub>v =
  (let name = \<lambda>x. (var ''__name__'', VLit (LitString (str_of x))) in
   fmap_of_list
    [(builtins, fmap_of_list
       ([name ''builtins'', (var ''len'', VPrim PrimLen), (var ''range'', VClass range_class),
         (var ''round'', VPrim PrimRound)]
        @ map (\<lambda>y. (y, VPredef (snoc builtins y)))
            (map prim_name [NoneType, object, bool, int, float, str]
             @ map var [''list'', ''dict'', ''tuple'']))),
     ((var ''sys'', []), fmap_of_list [name ''sys'', (var ''argv'', VList []), (var ''exit'', VPrim PrimExit)]),
     ((var ''typing'', []), fmap_of_list
       (name ''typing'' # map (\<lambda>y. (y, VPredef (var ''typing'', [y])))
          [var ''Callable'', var ''Literal'', prim_name Never, prim_name Sized])),
     ((var ''dataclasses'', []), fmap_of_list
       [name ''dataclasses'', (var ''dataclass'', VPredef (var ''dataclasses'', [var ''dataclass'']))])])"

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

locale loading = evaluation +
  fixes \<M> :: program
begin

(* Environment that binds each submodule of q to a stub; the predefined modules have no submodules *)
definition submods_env :: "name \<Rightarrow> env"
where
"submods_env q = fmmap (\<lambda>\<theta>. case \<theta> of ModStub q' \<Rightarrow> VModStub q' | _ \<Rightarrow> VUnbound) (submods \<M> q)"

abbreviation builtins_env :: env where "builtins_env \<equiv> the (fmlookup \<P>\<^sub>e\<^sub>n\<^sub>v builtins)"

(* Loading of a module, of imports, of a submodule chain, of one or several imported names, and of the modules
   containing the target of a from-import, where only an abort matters *)
inductive
  eval_mod     :: "name \<Rightarrow> env result \<Rightarrow> bool"                     ("_ \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d _" [60,60] 60) and
  eval_imports :: "name \<Rightarrow> import located list \<Rightarrow> env result \<Rightarrow> bool"       ("_, _ \<Rightarrow>\<^sub>i _" [60,0,60] 60) and
  eval_sub     :: "name \<Rightarrow> env \<Rightarrow> var list \<Rightarrow> env result \<Rightarrow> bool" ("_, _, _ \<Rightarrow>\<^sub>s\<^sub>u\<^sub>b _" [60,60,0,60] 60) and
  eval_imp     :: "env \<Rightarrow> var \<Rightarrow> val result \<Rightarrow> bool"              ("_, _ \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p _" [60,0,60] 60) and
  eval_imps    :: "env \<Rightarrow> var list \<Rightarrow> val list result \<Rightarrow> bool"    ("_, _ \<Rightarrow>\<^sub>i\<^sub>m\<^sub>p\<^sub>s _" [60,0,60] 60) and
  eval_mods    :: "name list \<Rightarrow> unit result \<Rightarrow> bool"                ("_ \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d\<^sub>s _" [60,60] 60)
where
EvalPredefined: "fmlookup \<P>\<^sub>e\<^sub>n\<^sub>v q = Some \<rho> \<Longrightarrow> q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho>" |
EvalModule:
  "\<lbrakk> fmlookup \<M> q = Some (ModuleBody \<iota>s t) ; q, \<iota>s \<Rightarrow>\<^sub>i Val \<rho>' ; scope VUnbound (declares \<iota>s) t = Some \<rho>s
  ; q, builtins_env \<otimes> \<rho>' \<otimes> \<rho>s, t \<Rightarrow>\<^sub>t (vs, Assigns \<rho>'')
  \<rbrakk> \<Longrightarrow> q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val (submods_env q \<otimes> \<rho>'')" |
EvalModuleFail: "\<lbrakk> fmlookup \<M> q = Some (ModuleBody \<iota>s t) ; q, \<iota>s \<Rightarrow>\<^sub>i Aborts \<kappa> \<rbrakk> \<Longrightarrow> q \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa>" |
EvalModuleFailBody:
  "\<lbrakk> fmlookup \<M> q = Some (ModuleBody \<iota>s t) ; q, \<iota>s \<Rightarrow>\<^sub>i Val \<rho>' ; scope VUnbound (declares \<iota>s) t = Some \<rho>s
  ; q, builtins_env \<otimes> \<rho>' \<otimes> \<rho>s, t \<Rightarrow>\<^sub>t (vs, Aborts\<^sub>\<omega> \<kappa>)
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

inductive eval_program :: "termination_kind \<Rightarrow> bool"
where
EvalProgram: "main \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Val \<rho> \<Longrightarrow> eval_program (SystemExit 0)" |
EvalProgramAbort: "main \<Rightarrow>\<^sub>m\<^sub>o\<^sub>d Aborts \<kappa> \<Longrightarrow> eval_program \<kappa>"

(* Required by well-formedness of programs *)
context
  assumes disjoint: "fmdom \<M> |\<inter>| fmdom \<P>\<^sub>e\<^sub>n\<^sub>v = {||}"
begin

lemma predefined_not_module: "fmlookup \<P>\<^sub>e\<^sub>n\<^sub>v q = Some \<rho> \<Longrightarrow> fmlookup \<M> q = Some b \<Longrightarrow> False"
  using disjoint by (auto dest!: fmdomI)

lemma module_not_predefined: "fmlookup \<M> q = Some b \<Longrightarrow> fmlookup \<P>\<^sub>e\<^sub>n\<^sub>v q = None"
  by (cases "fmlookup \<P>\<^sub>e\<^sub>n\<^sub>v q") (use predefined_not_module[of q _ b] in auto)

end

end

end
