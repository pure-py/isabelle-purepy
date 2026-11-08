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

lemma fmlookup_fmconst: "finite A \<Longrightarrow> fmlookup (fmconst A u) x = (if x \<in> A then Some u else None)"
proof -
  assume "finite A"
  then obtain xs where A: "A = set xs" using finite_list by blast
  have "fmlookup (fold (\<lambda>x. fmupd x u) xs m) x = (if x \<in> set xs then Some u else fmlookup m x)" for m
    by (induction xs arbitrary: m) auto
  then show ?thesis by (simp add: A fmconst_code)
qed

lemma fmconst_entry:
  assumes "fmlookup (fmconst A u) x = Some u'"
  shows "u' = u"
proof (cases "finite A")
  case True
  with assms show ?thesis by (simp add: fmlookup_fmconst split: if_splits)
qed (use assms in \<open>simp add: fmconst_def Finite_Set.fold_infinite\<close>)

(* Constant map over A, as a function of the constant *)
lemma fmconst_map: "fmconst A u = fmmap (\<lambda>_. u) (fmconst A u')"
proof (cases "finite A")
  case True
  then show ?thesis by (intro fmap_ext) (simp add: fmlookup_fmconst)
qed (simp add: fmconst_def Finite_Set.fold_infinite)

lemma fold_fmadd_dom: "x |\<in>| fmdom (fold fmadd \<Delta>s \<Delta>) \<Longrightarrow> x |\<in>| fmdom \<Delta> \<or> (\<exists>\<Delta>' \<in> set \<Delta>s. x |\<in>| fmdom \<Delta>')"
proof (induction \<Delta>s arbitrary: \<Delta>)
  case (Cons \<Delta>' \<Delta>s)
  from Cons.IH[of "\<Delta>' \<otimes> \<Delta>"] Cons.prems show ?case by auto
qed simp

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

lemma bind_sum_Ok: "bind_sum m f = Ok y \<longleftrightarrow> (\<exists>x. m = Ok x \<and> f x = Ok y)"
  by (cases m) simp_all

lemma Ok_bind_sum: "Ok y = bind_sum m f \<longleftrightarrow> (\<exists>x. m = Ok x \<and> f x = Ok y)"
  by (cases m) auto

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

lemma those_sum_eq: "those_sum ms = Ok xs \<Longrightarrow> ms = map Ok xs"
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

lemma Ok_in_set_map2: "Ok y \<in> set (map2 f xs zs) \<Longrightarrow> \<exists>x z. (x, z) \<in> set (zip xs zs) \<and> f x z = Ok y"
  by (auto simp: set_zip in_set_conv_nth) (metis)

(* Values of the fields filled by positional and keyword values, related by R to the field types when the
   positional values are related to the types of the first fields and each keyword value to the type of its
   field *)
lemma field_values_rel:
  assumes "distinct (map fst x\<sigma>s)" and "n + length kws = length x\<sigma>s"
    and "set (map fst kws) = set (drop n (map fst x\<sigma>s))"
    and "list_all2 R us (map snd (take n x\<sigma>s) @ map (\<lambda>(y, _). the (map_of x\<sigma>s y)) kws)"
  shows "list_all2 R
           (take n us @ map (\<lambda>y. the (map_of (zip (map fst kws) (drop n us)) y)) (drop n (map fst x\<sigma>s)))
           (map snd x\<sigma>s)"
proof -
  have n: "n \<le> length x\<sigma>s" using assms(2) by simp
  from assms(4) obtain us1 us2 where us: "us = us1 @ us2" and rel1: "list_all2 R us1 (map snd (take n x\<sigma>s))"
    and rel2: "list_all2 R us2 (map (\<lambda>(y, _). the (map_of x\<sigma>s y)) kws)"
    by (auto simp: list_all2_append2)
  have len1: "length us1 = n" using rel1 n by (auto dest: list_all2_lengthD)
  have len2: "length us2 = length kws" using rel2 by (auto dest: list_all2_lengthD)
  have distinct_kws: "distinct (map fst kws)"
  proof (rule card_distinct)
    show "card (set (map fst kws)) = length (map fst kws)"
      using assms(2, 3) distinct_card[OF distinct_drop[OF assms(1)]] by simp
  qed
  have rest: "list_all2 R (map (\<lambda>y. the (map_of (zip (map fst kws) us2) y)) (drop n (map fst x\<sigma>s)))
    (map snd (drop n x\<sigma>s))"
  proof (rule list_all2_all_nthI)
    fix i
    assume "i < length (map (\<lambda>y. the (map_of (zip (map fst kws) us2) y)) (drop n (map fst x\<sigma>s)))"
    then have i: "i < length (drop n x\<sigma>s)" by simp
    let ?x\<sigma> = "drop n x\<sigma>s ! i"
    have "?x\<sigma> \<in> set (drop n x\<sigma>s)" using i by (rule nth_mem)
    then have "fst ?x\<sigma> \<in> set (map fst kws)" using assms(3) by (force simp: drop_map)
    then obtain j where j: "j < length kws" and y: "map fst kws ! j = fst ?x\<sigma>" by (auto simp: in_set_conv_nth)
    have "map_of (zip (map fst kws) us2) (fst ?x\<sigma>) = Some (us2 ! j)"
      using map_of_zip_nth[of "map fst kws" us2 j] distinct_kws len2 j y by simp
    moreover have "the (map_of x\<sigma>s (fst ?x\<sigma>)) = snd ?x\<sigma>"
      using map_of_is_SomeI[OF assms(1), of "fst ?x\<sigma>" "snd ?x\<sigma>"] i by (simp add: in_set_dropD)
    moreover have "R (us2 ! j) (the (map_of x\<sigma>s (fst (kws ! j))))"
      using list_all2_nthD[OF rel2, of j] j len2 by (simp add: split_def)
    ultimately show "R (map (\<lambda>y. the (map_of (zip (map fst kws) us2) y)) (drop n (map fst x\<sigma>s)) ! i)
      (map snd (drop n x\<sigma>s) ! i)"
      using i y j by (simp add: drop_map)
  qed simp
  from list_all2_appendI[OF rel1 rest]
  have "list_all2 R (us1 @ map (\<lambda>y. the (map_of (zip (map fst kws) us2) y)) (drop n (map fst x\<sigma>s)))
    (map snd (take n x\<sigma>s @ drop n x\<sigma>s))"
    by (simp only: map_append)
  with us len1 show ?thesis by simp
qed

end
