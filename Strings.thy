(* Strings as lists of Unicode code points *)
theory Strings
  imports "HOL-Library.List_Lexorder"
begin

typedef str = "{ns :: nat list. \<forall>n \<in> set ns. n < 0x110000}"
  morphisms code_points Str
  by (rule exI[of _ "[]"]) simp

setup_lifting type_definition_str

(* Whether w occurs in w' *)
lift_definition substring :: "str \<Rightarrow> str \<Rightarrow> bool"
  is "\<lambda>ns ns'. \<exists>ms ms'. ns' = ms @ ns @ ms'" .

instantiation str :: equal
begin

definition equal_str :: "str \<Rightarrow> str \<Rightarrow> bool"
where
"equal_str w w' = (w = w')"

instance
  by standard (simp add: equal_str_def)

end

instantiation str :: linorder
begin

lift_definition less_eq_str :: "str \<Rightarrow> str \<Rightarrow> bool" is "(\<le>)" .

lift_definition less_str :: "str \<Rightarrow> str \<Rightarrow> bool" is "(<)" .

instance
  by (standard; transfer) (auto simp: less_le_not_le linear intro: order_trans antisym)

end

end
