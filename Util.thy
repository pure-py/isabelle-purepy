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

definition fmconst :: "'a set \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap"
where
"fmconst A u = Finite_Set.fold (\<lambda>x. fmupd x u) fmempty A"

lemma comp_fun_idem_fmupd: "comp_fun_idem_on UNIV (\<lambda>x. fmupd x u)"
  by unfold_locales (auto simp: fun_eq_iff intro!: fmap_ext)

lemma fmconst_code [code]: "fmconst (set xs) u = fold (\<lambda>x. fmupd x u) xs fmempty"
  unfolding fmconst_def by (rule comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_fmupd subset_UNIV])

end
