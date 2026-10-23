theory Util
  imports Main
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

end
