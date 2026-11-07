(* Shared utilities *)
theory Util
  imports Complex_Main "HOL-Library.Finite_Map" "HOL-Library.Monad_Syntax" "HOL-Library.Extended_Real"
    "HOL-Library.List_Lexorder" "HOL-Library.Char_ord"
begin

consts override :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<otimes>" 100)

(* Boxed plus of the specification isn't in Isabelle's symbol table *)
consts extend :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" (infixl "\<uplus>" 65)

adhoc_overloading override \<rightleftharpoons> fmadd

(* Free o for outcomes; a later library import would restore the notation *)
no_notation (ASCII) comp (infixl \<open>o\<close> 55)

definition fmconst :: "'a set \<Rightarrow> 'b \<Rightarrow> ('a, 'b) fmap"
where
"fmconst A u = Finite_Set.fold (\<lambda>x. fmupd x u) fmempty A"

lemma comp_fun_idem_fmupd: "comp_fun_idem_on UNIV (\<lambda>x. fmupd x u)"
  by unfold_locales (auto simp: fun_eq_iff intro!: fmap_ext)

lemma fmconst_code [code]: "fmconst (set xs) u = fold (\<lambda>x. fmupd x u) xs fmempty"
  unfolding fmconst_def by (rule comp_fun_idem_on.fold_set_fold[OF comp_fun_idem_fmupd subset_UNIV])

lemma map_of_zip_map_snd:
  "length xs = length ys \<Longrightarrow> map_of (zip xs (map f ys)) k = map_option f (map_of (zip xs ys) k)"
  by (induction xs ys rule: list_induct2) auto

lemma map_of_filter_key: "map_of (filter (\<lambda>(k, _). P k) xs) k = (if P k then map_of xs k else None)"
  by (induction xs) auto

lemma map_of_zip_map: "map_of (zip xs (map f xs)) x = (if x \<in> set xs then Some (f x) else None)"
  by (induction xs) auto

lemma list_all2_interleave:
  "list_all2 (\<lambda>(x, x') y. P x z \<and> P x' y) xxs ys
  \<Longrightarrow> list_all2 P (concat (map (\<lambda>(x, x'). [x, x']) xxs)) (concat (map (\<lambda>y. [z, y]) ys))"
  by (induction rule: list_all2_induct) auto

lemma rel_option_map_of_zip:
  "list_all2 P xs ys \<Longrightarrow> rel_option P (map_of (zip ks xs) k) (map_of (zip ks ys) k)"
proof (induction arbitrary: ks rule: list_all2_induct)
  case (Cons x xs y ys)
  then show ?case by (cases ks) auto
qed simp

(* Termination through lists of pairs and finite maps *)
lemma size_prod_pair [simp]: "size_prod f g p = f (fst p) + g (snd p) + Suc 0"
  by (cases p) simp

lemma size_list_elem: "x \<in> set xs \<Longrightarrow> f x < size_list f xs"
  by (induction xs) auto

lemma size_list_zip_elem: "(x, y) \<in> set (zip xs ys) \<Longrightarrow> f x + g y < size_list f xs + size_list g ys"
  by (metis add_strict_mono set_zip_leftD set_zip_rightD size_list_elem)

lemma size_list_snd_elem: "(a, b) \<in> set xs \<Longrightarrow> size b < size_list (\<lambda>x. Suc (size (snd x))) xs"
  by (induction xs) auto

lemma size_list_snd_elem': "b \<in> set (map snd xs) \<Longrightarrow> size b < size_list (\<lambda>x. Suc (size (snd x))) xs"
  by (auto dest: size_list_snd_elem)

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

(* Error monad: failure Fail e or result Ok x *)
abbreviation Fail :: "'e \<Rightarrow> 'e + 'a" where "Fail \<equiv> Inl"
abbreviation Ok :: "'a \<Rightarrow> 'e + 'a" where "Ok \<equiv> Inr"

definition bind_sum :: "'e + 'a \<Rightarrow> ('a \<Rightarrow> 'e + 'b) \<Rightarrow> 'e + 'b"
where
"bind_sum m f = (case m of Fail e \<Rightarrow> Fail e | Ok x \<Rightarrow> f x)"

adhoc_overloading Monad_Syntax.bind \<rightleftharpoons> bind_sum

lemma bind_sum_simps [simp]: "bind_sum (Fail e) f = Fail e" "bind_sum (Ok x) f = f x"
  by (simp_all add: bind_sum_def)

lemma bind_sum_cong [fundef_cong]:
  "\<lbrakk> m = m' ; \<And>x. m' = Ok x \<Longrightarrow> f x = f' x \<rbrakk> \<Longrightarrow> bind_sum m f = bind_sum m' f'"
  by (cases m') simp_all

(* Failure e for None, otherwise the value; e is computed eagerly by generated code *)
definition or_else :: "'e \<Rightarrow> 'a option \<Rightarrow> 'e + 'a"
where
"or_else e m = (case m of Some x \<Rightarrow> Ok x | None \<Rightarrow> Fail e)"

(* Failure e unless b; e is computed eagerly by generated code *)
definition ensure :: "bool \<Rightarrow> 'e \<Rightarrow> 'e + unit"
where
"ensure b e = (if b then Ok () else Fail e)"

(* First failure in the list, otherwise the list of results *)
fun those_sum :: "('e + 'a) list \<Rightarrow> 'e + 'a list"
where
"those_sum [] = Ok []" |
"those_sum (m # ms) = do { x \<leftarrow> m; xs \<leftarrow> those_sum ms; Ok (x # xs) }"

lemma those_sum_Ok: "those_sum ms = Ok xs \<Longrightarrow> list_all2 (\<lambda>m x. m = Ok x) ms xs"
  by (induction ms arbitrary: xs) (auto simp: bind_sum_def split: sum.splits)

lemma those_sum_map_Ok: "those_sum (map f xs) = Ok ys \<Longrightarrow> list_all2 (\<lambda>x y. f x = Ok y) xs ys"
  by (auto dest: those_sum_Ok simp: list_all2_map1)

(* First failure in the list, otherwise success *)
definition all_sum :: "('e + unit) list \<Rightarrow> 'e + unit"
where
"all_sum ms = do { those_sum ms; Ok () }"

lemma all_sum_simps [simp]: "all_sum [] = Ok ()" "all_sum (m # ms) = do { m; all_sum ms }"
  by (simp_all add: all_sum_def bind_sum_def split: sum.splits)

lemma all_sum_Ok: "\<lbrakk> all_sum ms = Ok () ; m \<in> set ms \<rbrakk> \<Longrightarrow> m = Ok ()"
  by (induction ms) (auto simp: bind_sum_def split: sum.splits)

lemma all_sum_map_Ok: "\<lbrakk> all_sum (map f xs) = Ok () ; x \<in> set xs \<rbrakk> \<Longrightarrow> f x = Ok ()"
  using all_sum_Ok[of "map f xs" "f x"] by simp

lemma all_sum_map2_Ok:
  assumes "all_sum (map2 f xs ys) = Ok ()" and "length xs = length ys"
  shows "list_all2 (\<lambda>x y. f x y = Ok ()) xs ys"
proof -
  have "f (xs ! i) (ys ! i) = Ok ()" if "i < length xs" for i
  proof -
    have "map2 f xs ys ! i \<in> set (map2 f xs ys)" using that assms(2) by (intro nth_mem) simp
    from all_sum_Ok[OF assms(1) this] that assms(2) show ?thesis by simp
  qed
  with assms(2) show ?thesis by (simp add: list_all2_conv_all_nth)
qed

end
