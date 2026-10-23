theory Util
  imports "HOL-Library.Finite_Map"
begin

type_synonym 'a nonempty = "'a \<times> 'a list"

fun snoc :: "'a nonempty \<Rightarrow> 'a \<Rightarrow> 'a nonempty"
where
"snoc (y, ys) x = (y, ys @ [x])"

fun unsnoc :: "'a nonempty \<Rightarrow> ('a nonempty \<times> 'a) option"
where
"unsnoc (y, ys) = (if ys = [] then None else Some ((y, butlast ys), last ys))"

lemma unsnoc_snoc [simp]: "unsnoc (snoc q x) = Some (q, x)"
  by (cases q) simp

lemma snoc_unsnoc: "unsnoc q' = Some (q, x) \<Longrightarrow> q' = snoc q x"
  by (cases q') (auto split: if_splits simp: append_butlast_last_id)

lemma snoc_eq_iff:
  "snoc q x = q' \<longleftrightarrow> unsnoc q' = Some (q, x)" "q' = snoc q x \<longleftrightarrow> unsnoc q' = Some (q, x)"
  by (auto dest: snoc_unsnoc)

definition fmconst :: "'a set \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap"
where
"fmconst A u = Finite_Set.fold (\<lambda>x. fmupd x u) fmempty A"

lemma comp_fun_idem_fmupd: "comp_fun_idem_on UNIV (\<lambda>x. fmupd x u)"
  by unfold_locales (auto simp: fun_eq_iff intro!: fmap_ext)

lemma fmconst_code [code]: "fmconst (set xs) u = fold (\<lambda>x. fmupd x u) xs fmempty"
  unfolding fmconst_def by (rule comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_fmupd subset_UNIV])

(* Termination through lists of pairs and finite maps *)
lemma size_prod_pair [simp]: "size_prod f g p = f (fst p) + g (snd p) + Suc 0"
  by (cases p) simp

lemma size_list_fst: "size_list (size \<circ> fst) kvs \<le> size_list (\<lambda>x. Suc (size (fst x) + size (snd x))) kvs"
  by (rule size_list_pointwise) simp

lemma size_list_snd: "size_list (size \<circ> snd) kvs \<le> size_list (\<lambda>x. Suc (size (fst x) + size (snd x))) kvs"
  by (rule size_list_pointwise) simp

lemma fmmap_keys_cong [fundef_cong]:
  assumes "m = m'" and "\<And>x v. fmlookup m' x = Some v \<Longrightarrow> f x v = g x v"
  shows "fmmap_keys f m = fmmap_keys g m'"
proof (rule fmap_ext)
  fix x
  show "fmlookup (fmmap_keys f m) x = fmlookup (fmmap_keys g m') x"
    using assms by (cases "fmlookup m' x") simp_all
qed

lemma size_fmap_lookup: "fmlookup m x = Some v \<Longrightarrow> g v < size_fmap f g m"
  using member_le_sum[of "(x, v)" "fset (fset_of_fmap m)" "\<lambda>(a, b). Suc (f a + g b)"]
  by (simp add: fset_of_fmap_iff' case_prod_unfold)

lemma card_fmdom_insert:
  assumes "fmlookup M q = Some m" and "q \<notin> V"
  shows "card (fmdom' M - insert q V) < card (fmdom' M - V)"
proof -
  have "q \<in> fmdom' M - V" using assms by (simp add: fmlookup_dom'_iff)
  moreover have "fmdom' M - insert q V = (fmdom' M - V) - {q}" by auto
  ultimately show ?thesis by (metis card_Diff1_less finite_Diff finite_fmdom')
qed

end
