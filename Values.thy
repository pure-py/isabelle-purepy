(* Values, results and functions on values *)
theory Values
    imports Subtyping
begin

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

fun seq_compose :: "outcome \<Rightarrow> outcome \<Rightarrow> outcome"
where
"seq_compose (vs, Returns v) o = (vs, Returns v)" |
"seq_compose (vs, Aborts\<^sub>\<omega> \<kappa>) o = (vs, Aborts\<^sub>\<omega> \<kappa>)" |
"seq_compose (vs, Assigns \<rho>) (vs', Assigns \<rho>') = (vs @ vs', Assigns (\<rho> \<otimes> \<rho>'))" |
"seq_compose (vs, Assigns \<rho>) (vs', \<omega>) = (vs @ vs', \<omega>)"

adhoc_overloading override \<rightleftharpoons> seq_compose

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
"is_opaque_builtin (VPredef (Qualified q _)) = (q = builtins)" |
"is_opaque_builtin _ = False"

fun is_bool :: "val \<Rightarrow> bool"
where
"is_bool (VLit (LitBool _)) = True" |
"is_bool _ = False"

fun is_nan_val :: "val \<Rightarrow> bool"
where
"is_nan_val (VLit (LitFloat x)) = is_nan x" |
"is_nan_val _ = False"

fun is_number :: "val \<Rightarrow> bool"
where
"is_number (VLit (LitInt _)) = True" |
"is_number (VLit (LitFloat _)) = True" |
"is_number _ = False"

(* Value of a number as an extended real; None for nan or a non-number *)
fun as_number :: "val \<Rightarrow> ereal option"
where
"as_number (VLit (LitInt n)) = Some (ereal (real_of_int n))" |
"as_number (VLit (LitFloat x)) = real_of_float x" |
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
"eq_lit (LitInt n) (LitFloat x') = Val (real_of_float x' = Some (ereal (real_of_int n)))" |
"eq_lit (LitFloat x) (LitInt n') = Val (real_of_float x = Some (ereal (real_of_int n')))" |
"eq_lit (LitFloat x) (LitFloat x') =
  (if is_nan x \<and> is_nan x' then Aborts Undef else Val (real_of_float x = real_of_float x'))" |
"eq_lit (LitString w) (LitString w') = Val (w = w')" |
"eq_lit (LitBool b) (LitBool b') = Val (b = b')" |
"eq_lit LitNone LitNone = Val True" |
"eq_lit (LitBool _) (LitInt _) = Aborts Undef" |
"eq_lit (LitBool _) (LitFloat _) = Aborts Undef" |
"eq_lit (LitInt _) (LitBool _) = Aborts Undef" |
"eq_lit (LitFloat _) (LitBool _) = Aborts Undef" |
"eq_lit _ _ = Val False"

(* Cases on first value, then second; otherwise pattern matching is slow *)
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

lemma set_setitem: "set (setitem \<delta> w v) \<subseteq> insert (w, v) (set \<delta>)"
  by (induction \<delta>) (auto split: if_splits)

lemma fst_setitem: "fst ` set (setitem \<delta> w v) = insert w (fst ` set \<delta>)"
  by (induction \<delta> w v rule: setitem.induct) (simp_all add: insert_commute)

lemma distinct_setitem: "distinct (map fst \<delta>) \<Longrightarrow> distinct (map fst (setitem \<delta> w v))"
  by (induction \<delta> w v rule: setitem.induct) (auto simp: fst_setitem)

lemma set_update: "set (update \<delta> \<delta>') \<subseteq> set \<delta> \<union> set \<delta>'"
  by (induction \<delta> \<delta>' rule: update.induct) (auto dest: set_setitem[THEN subsetD])

lemma distinct_update: "distinct (map fst \<delta>) \<Longrightarrow> distinct (map fst (update \<delta> \<delta>'))"
  by (induction \<delta> \<delta>' rule: update.induct) (auto intro: distinct_setitem)

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

definition float_of :: "ereal \<Rightarrow> float result"
where
"float_of x = (if is_infinite (fl x) then Aborts OverflowError else Val (fl x))"

abbreviation float_val :: "float result \<Rightarrow> val result"
where "float_val r \<equiv> mlet r (\<lambda>x. Val (VLit (LitFloat x)))"

(* Operand of an operator expecting a float, with an integer converted *)
fun to_float :: "val \<Rightarrow> float result"
where
"to_float (VLit (LitInt n)) = float_of (ereal (real_of_int n))" |
"to_float (VLit (LitFloat x)) = Val x"

definition float_operands :: "val \<Rightarrow> val \<Rightarrow> (float \<times> float) result"
where
"float_operands v v' = mlet (to_float v) (\<lambda>x. mlet (to_float v') (\<lambda>x'. Val (x, x')))"

definition float_arith :: "(float \<Rightarrow> float \<Rightarrow> float) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"float_arith g v v' = mlet (float_operands v v') (\<lambda>(x, x'). Val (VLit (LitFloat (g x x'))))"

definition float_division :: "(float \<Rightarrow> float \<Rightarrow> float) \<Rightarrow> val \<Rightarrow> val \<Rightarrow> val result"
where
"float_division g v v' =
  mlet (float_operands v v')
    (\<lambda>(x, x'). if real_of_float x' = Some 0 then Aborts ZeroDivisionError else Val (VLit (LitFloat (g x x'))))"

(* Exact quotient of integers, rounded *)
definition int_quotient :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"int_quotient v v' =
  (if the_int v' = 0 then Aborts ZeroDivisionError
   else float_val (float_of (ereal (real_of_int (the_int v) / real_of_int (the_int v')))))"

(* Exact power of a number by an integer exponent, rounded *)
definition float_power :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"float_power v v' =
  mlet (to_float v)
    (\<lambda>x. let n = the_int v'; y = fl (the (real_of_float x) powi n) in
         if real_of_float x = Some 0 \<and> n < 0 then Aborts ZeroDivisionError
         else if \<not> is_infinite x \<and> is_infinite y then Aborts Undef
         else Val (VLit (LitFloat y)))"

definition int_power :: "val \<Rightarrow> val \<Rightarrow> val result"
where
"int_power v v' =
  (if the_int v' \<ge> 0 then int_arith (\<lambda>n n'. n ^ nat n') v v'
   else if the_int v = 0 then Aborts ZeroDivisionError
   else float_power v v')"

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
  (case real_of_float x of
     None \<Rightarrow> Aborts ValueError
   | Some (ereal r) \<Rightarrow> Val (VLit (LitInt (round_even r)))
   | Some _ \<Rightarrow> Aborts OverflowError)" |
"prim_meaning PrimRound [v, v'] =
  (if (is_number v \<or> is_bool v) \<and>
      (case v' of VLit (LitInt _) \<Rightarrow> True | VLit (LitBool _) \<Rightarrow> True | VLit LitNone \<Rightarrow> True | _ \<Rightarrow> False)
   then Aborts Excluded else Aborts TypeError)" |
"prim_meaning PrimExit [VLit (LitInt n)] = Aborts (SystemExit n)" |
"prim_meaning PrimExit [] = Aborts Excluded" |
"prim_meaning PrimExit [v] = Aborts Excluded" |
"prim_meaning _ _ = Aborts TypeError"

fun resolve :: "env \<Rightarrow> name \<Rightarrow> val option"
where
"resolve \<rho> (Simple x) = fmlookup \<rho> x" |
"resolve \<rho> (Qualified q y) = (case resolve \<rho> q of Some (VModLoaded _ \<rho>') \<Rightarrow> fmlookup \<rho>' y | _ \<Rightarrow> None)"

locale evaluation =
  fixes \<Sigma> :: class_table
  assumes wf_class_table: "wf_class_table \<Sigma>"
begin

type_synonym overload = "(val \<Rightarrow> val \<Rightarrow> bool) \<times> (val \<Rightarrow> val \<Rightarrow> val result)"

definition overload :: "ty \<Rightarrow> ty \<Rightarrow> (val \<Rightarrow> val \<Rightarrow> val result) \<Rightarrow> overload"
where
"overload \<tau> \<tau>' f = ((\<lambda>v v'. \<Sigma> \<turnstile> type_of v <: \<tau> \<and> \<Sigma> \<turnstile> type_of v' <: \<tau>'), f)"

(* Overload for tuple operands of any length, since a tuple type fixes the length *)
definition tuple_overload :: "(val \<Rightarrow> val \<Rightarrow> val result) \<Rightarrow> overload"
where
"tuple_overload f = ((\<lambda>v v'. case (v, v') of (VTuple _, VTuple _) \<Rightarrow> True | _ \<Rightarrow> False), f)"

(* Run-time overloads of each binary operator, most specific first *)
fun overloads :: "bop \<Rightarrow> overload list"
where
"overloads BOpEq =
  [overload (TyPrim object) (TyPrim object)
    (\<lambda>v v'. if is_nan_val v \<and> is_nan_val v' then Val (VLit (LitBool False)) else bool_val (eq v v'))]" |
"overloads BOpNeq =
  [overload (TyPrim object) (TyPrim object)
    (\<lambda>v v'. if is_nan_val v \<and> is_nan_val v' then Val (VLit (LitBool True))
             else bool_val (mlet (eq v v') (\<lambda>b. Val (\<not> b))))]" |
"overloads BOpIn = [overload (TyPrim object) (TyPrim object) (\<lambda>v v'. bool_val (in_op v v'))]" |
"overloads BOpNotIn =
  [overload (TyPrim object) (TyPrim object) (\<lambda>v v'. bool_val (mlet (in_op v v') (\<lambda>b. Val (\<not> b))))]" |
"overloads BOpLt =
  [overload (TyPrim float) (TyPrim float) (compare_numbers (<)),
   overload (TyPrim str) (TyPrim str) (compare_strings (<))]" |
"overloads BOpLeq =
  [overload (TyPrim float) (TyPrim float) (compare_numbers (\<le>)),
   overload (TyPrim str) (TyPrim str) (compare_strings (\<le>))]" |
"overloads BOpGt =
  [overload (TyPrim float) (TyPrim float) (compare_numbers (>)),
   overload (TyPrim str) (TyPrim str) (compare_strings (>))]" |
"overloads BOpGeq =
  [overload (TyPrim float) (TyPrim float) (compare_numbers (\<ge>)),
   overload (TyPrim str) (TyPrim str) (compare_strings (\<ge>))]" |
"overloads BOpAdd =
  [overload (TyPrim int) (TyPrim int) (int_arith (+)),
   overload (TyPrim float) (TyPrim float) (float_arith float_add),
   overload (TyPrim str) (TyPrim str) concat_str,
   overload (TyList (TyPrim object)) (TyList (TyPrim object)) concat_list,
   tuple_overload concat_tuple]" |
"overloads BOpSub =
  [overload (TyPrim int) (TyPrim int) (int_arith (-)),
   overload (TyPrim float) (TyPrim float) (float_arith float_sub)]" |
"overloads BOpMul =
  [overload (TyPrim int) (TyPrim int) (int_arith (*)),
   overload (TyPrim float) (TyPrim float) (float_arith float_mul),
   overload (TyPrim str) (TyPrim int) repeat_str,
   overload (TyPrim int) (TyPrim str) (\<lambda>v v'. repeat_str v' v),
   overload (TyList (TyPrim object)) (TyPrim int) repeat_list,
   overload (TyPrim int) (TyList (TyPrim object)) (\<lambda>v v'. repeat_list v' v)]" |
"overloads BOpDiv =
  [overload (TyPrim int) (TyPrim int) int_quotient,
   overload (TyPrim float) (TyPrim float) (float_division float_div)]" |
"overloads BOpFloorDiv =
  [overload (TyPrim int) (TyPrim int) (int_division (div)),
   overload (TyPrim float) (TyPrim float) (float_division float_floordiv)]" |
"overloads BOpMod =
  [overload (TyPrim int) (TyPrim int) (int_division (mod)),
   overload (TyPrim float) (TyPrim float) (float_division float_mod)]" |
"overloads BOpPow =
  [overload (TyPrim int) (TyPrim int) int_power, overload (TyPrim float) (TyPrim int) float_power]" |
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
  (if \<Sigma> \<turnstile> type_of v <: TyPrim bool then Val (VLit (LitBool (v \<noteq> VLit (LitBool True)))) else Aborts Excluded)" |
"unop_meaning UOpPos v = (if \<Sigma> \<turnstile> type_of v <: TyPrim float then Val v else Aborts Excluded)" |
"unop_meaning UOpNeg v = (if \<Sigma> \<turnstile> type_of v <: TyPrim float then Val (negate v) else Aborts Excluded)"

end

end
