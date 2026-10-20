theory Util
    imports Main
begin

lemma unique_remdups_filter:
  assumes "\<And>x. P x \<Longrightarrow> x \<in> set xs"
  shows "(if \<exists>!x. P x then Some (f (THE x. P x)) else None) =
         (case remdups (filter P xs) of [x] \<Rightarrow> Some (f x) | _ \<Rightarrow> None)"
proof -
  have P: "set (remdups (filter P xs)) = {x. P x}"
    using assms by auto
  show ?thesis
  proof (cases "remdups (filter P xs)" rule: remdups_adj.cases)
    case 1
    with P show ?thesis by auto
  next
    case (2 x)
    with P have "P = (\<lambda>y. y = x)" by (auto simp: fun_eq_iff)
    with 2 show ?thesis by simp
  next
    case (3 x y ys)
    with P have "P x" "P y" "x \<noteq> y"
      using distinct_remdups[of "filter P xs"] by (auto simp del: distinct_remdups)
    with 3 show ?thesis by auto
  qed
qed

definition the_unique :: "'a set \<Rightarrow> 'a option"
where
"the_unique A = (if \<exists>!x. x \<in> A then Some (THE x. x \<in> A) else None)"

lemma the_unique_code [code]: "the_unique (set xs) = (case remdups xs of [x] \<Rightarrow> Some x | _ \<Rightarrow> None)"
  using unique_remdups_filter[of "\<lambda>x. x \<in> set xs" xs "\<lambda>x. x"] by (simp add: the_unique_def)

end
