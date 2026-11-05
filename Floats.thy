(* Floats as an abstract type, with rounding and IEEE 754 arithmetic uninterpreted *)
theory Floats
  imports Util
begin

typedecl float

(* Observers and rounding, left uninterpreted since type soundness doesn't depend on the values *)
consts
  (* Extended real denoted by a float; None for nan *)
  real_of_float :: "float \<Rightarrow> ereal option"
  (* Sign bit, which distinguishes the two zeros *)
  negative :: "float \<Rightarrow> bool"
  nan :: float
  (* Extended real rounded by roundTiesToEven; extended since a power is taken on the value of a float *)
  fl :: "ereal \<Rightarrow> float"

(* IEEE 754 arithmetic *)
consts
  float_neg :: "float \<Rightarrow> float"
  float_add :: "float \<Rightarrow> float \<Rightarrow> float"
  float_sub :: "float \<Rightarrow> float \<Rightarrow> float"
  float_mul :: "float \<Rightarrow> float \<Rightarrow> float"
  float_div :: "float \<Rightarrow> float \<Rightarrow> float"

definition is_nan :: "float \<Rightarrow> bool"
where
"is_nan x = (real_of_float x = None)"

definition is_infinite :: "float \<Rightarrow> bool"
where
"is_infinite x = (real_of_float x \<in> {Some \<infinity>, Some (-\<infinity>)})"

abbreviation neg_zero :: float where "neg_zero \<equiv> float_neg (fl 0)"

definition trunc :: "real \<Rightarrow> int"
where
"trunc x = (if x \<ge> 0 then \<lfloor>x\<rfloor> else \<lceil>x\<rceil>)"

(* Floor division of n by a nonzero n', by the algorithm of the Python Language Reference *)
definition float_floordiv :: "float \<Rightarrow> float \<Rightarrow> float"
where
"float_floordiv n n' =
  (case (real_of_float n, real_of_float n') of
     (Some (ereal x), Some (ereal x')) \<Rightarrow>
       (let x\<^sub>1 = x - x' * real_of_int (trunc (x / x'));
            n\<^sub>2 = fl (the (real_of_float (fl (ereal (x - x\<^sub>1)))) / ereal x');
            n\<^sub>3 = if x\<^sub>1 \<noteq> 0 \<and> (x\<^sub>1 < 0) \<noteq> (x' < 0) then fl (the (real_of_float n\<^sub>2) - 1) else n\<^sub>2 in
        case real_of_float n\<^sub>3 of
          Some (ereal y) \<Rightarrow>
            if \<lceil>y - 1 / 2\<rceil> = 0 \<and> negative n \<noteq> negative n' then neg_zero
            else fl (ereal (real_of_int \<lceil>y - 1 / 2\<rceil>))
        | _ \<Rightarrow> n\<^sub>3)
   | (Some (ereal x), Some PInfty) \<Rightarrow> if x < 0 then fl (-1) else if x > 0 \<or> \<not> negative n then fl 0 else neg_zero
   | (Some (ereal x), Some MInfty) \<Rightarrow> if x > 0 then fl (-1) else if x < 0 \<or> negative n then fl 0 else neg_zero
   | _ \<Rightarrow> nan)"

(* Remainder of division of n by a nonzero n', with the sign of n' *)
definition float_mod :: "float \<Rightarrow> float \<Rightarrow> float"
where
"float_mod n n' =
  (case (real_of_float n, real_of_float n') of
     (Some (ereal x), Some (ereal x')) \<Rightarrow>
       (let n\<^sub>1 = fl (ereal (x - x' * real_of_int \<lfloor>x / x'\<rfloor>)) in
        if real_of_float n\<^sub>1 = Some 0 \<and> \<not> negative n\<^sub>1 \<and> x' < 0 then neg_zero else n\<^sub>1)
   | (Some (ereal x), Some PInfty) \<Rightarrow> if x > 0 then n else if x < 0 then n' else fl 0
   | (Some (ereal x), Some MInfty) \<Rightarrow> if x < 0 then n else if x > 0 then n' else neg_zero
   | _ \<Rightarrow> nan)"

instantiation float :: equal
begin

definition equal_float :: "float \<Rightarrow> float \<Rightarrow> bool"
where
"equal_float x x' = (x = x')"

instance
  by standard (simp add: equal_float_def)

end

end
