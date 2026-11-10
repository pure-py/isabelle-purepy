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

lemma fold_fmadd_lookup:
  "fmlookup (fold (\<otimes>) \<Delta>s \<Delta>) x = Some \<sigma> \<Longrightarrow> fmlookup \<Delta> x = Some \<sigma> \<or> (\<exists>\<Delta>' \<in> set \<Delta>s. fmlookup \<Delta>' x = Some \<sigma>)"
proof (induction \<Delta>s arbitrary: \<Delta>)
  case (Cons a \<Delta>s)
  from Cons.IH[OF Cons.prems[simplified]] show ?case by (auto split: if_splits)
qed simp

lemma fmdom'_fold_fmadd: "fmdom' (fold (\<otimes>) \<Delta>s \<Delta>) = fmdom' \<Delta> \<union> \<Union> (fmdom' ` set \<Delta>s)"
  by (induction \<Delta>s arbitrary: \<Delta>) auto

lemma foldr_fmadd_dom': "fmdom' (foldr fmadd \<Delta>s \<Delta>) = fmdom' \<Delta> \<union> \<Union> (fmdom' ` set \<Delta>s)"
  by (induction \<Delta>s) auto

lemma fold_fmadd_lookup_notin: "x \<notin> \<Union> (fmdom' ` set \<Delta>s) \<Longrightarrow> fmlookup (fold fmadd \<Delta>s \<Delta>) x = fmlookup \<Delta> x"
  by (induction \<Delta>s arbitrary: \<Delta>) (auto simp: fmdom'_alt_def fmlookup_dom_iff)

(* Variable in the domain of one map of a list only: in none of the others *)
lemma notin_others:
  "\<lbrakk> \<forall>j < Suc (length \<Delta>s). j \<noteq> 0 \<longrightarrow> x \<notin> fmdom' ((\<Delta>' # \<Delta>s) ! j) \<rbrakk> \<Longrightarrow> x \<notin> \<Union> (fmdom' ` set \<Delta>s)"
proof
  assume all: "\<forall>j < Suc (length \<Delta>s). j \<noteq> 0 \<longrightarrow> x \<notin> fmdom' ((\<Delta>' # \<Delta>s) ! j)" and "x \<in> \<Union> (fmdom' ` set \<Delta>s)"
  then obtain i where "i < length \<Delta>s" and "x \<in> fmdom' (\<Delta>s ! i)" by (auto simp: in_set_conv_nth)
  with all[rule_format, of "Suc i"] show False by simp
qed

(* Lookup in a fold of maps, at a variable in the domain of one of them only *)
lemma fold_fmadd_lookup_nth:
  "\<lbrakk> i < length \<Delta>s ; x \<in> fmdom' (\<Delta>s ! i) ; \<forall>j < length \<Delta>s. j \<noteq> i \<longrightarrow> x \<notin> fmdom' (\<Delta>s ! j) ; x \<notin> fmdom' \<Delta> \<rbrakk>
  \<Longrightarrow> fmlookup (fold fmadd \<Delta>s \<Delta>) x = fmlookup (\<Delta>s ! i) x"
proof (induction \<Delta>s arbitrary: i \<Delta>)
  case (Cons \<Delta>' \<Delta>s)
  show ?case
  proof (cases i)
    case 0
    with Cons.prems have "x \<notin> \<Union> (fmdom' ` set \<Delta>s)" by (intro notin_others) simp
    with Cons.prems 0 show ?thesis by (simp add: fold_fmadd_lookup_notin fmdom'_alt_def)
  next
    case (Suc i')
    with Cons.prems have "x \<notin> fmdom' \<Delta>'" by fastforce
    with Cons.prems Suc show ?thesis by (auto intro!: Cons.IH simp: fmdom'_alt_def)
  qed
qed simp

(* Lookup in a fold of maps agreeing at a variable *)
lemma foldr_fmadd_lookup_agree:
  "\<lbrakk> j < length \<rho>s ; x \<in> fmdom' (\<rho>s ! j)
   ; \<forall>k < length \<rho>s. x \<in> fmdom' (\<rho>s ! k) \<longrightarrow> fmlookup (\<rho>s ! k) x = fmlookup (\<rho>s ! j) x \<rbrakk>
  \<Longrightarrow> fmlookup (foldr fmadd \<rho>s fmempty) x = fmlookup (\<rho>s ! j) x"
proof (induction \<rho>s arbitrary: j)
  case (Cons \<rho> \<rho>s)
  show ?case
  proof (cases "x \<in> fmdom' (foldr fmadd \<rho>s fmempty)")
    case True
    then obtain k where k: "k < length \<rho>s" and xk: "x \<in> fmdom' (\<rho>s ! k)"
      by (auto simp: foldr_fmadd_dom' in_set_conv_nth)
    have agree: "fmlookup (\<rho>s ! k') x = fmlookup (\<rho>s ! k) x" if "k' < length \<rho>s" and "x \<in> fmdom' (\<rho>s ! k')" for k'
      using Cons.prems(3)[rule_format, of "Suc k'"] Cons.prems(3)[rule_format, of "Suc k"] that k xk by simp
    have "\<forall>k' < length \<rho>s. x \<in> fmdom' (\<rho>s ! k') \<longrightarrow> fmlookup (\<rho>s ! k') x = fmlookup (\<rho>s ! k) x"
      using agree by blast
    then have "fmlookup (foldr fmadd \<rho>s fmempty) x = fmlookup (\<rho>s ! k) x" by (rule Cons.IH[OF k xk])
    moreover have "fmlookup (\<rho>s ! k) x = fmlookup ((\<rho> # \<rho>s) ! j) x"
      using Cons.prems(3)[rule_format, of "Suc k"] k xk by simp
    ultimately show ?thesis using True by (simp add: fmdom'_alt_def)
  next
    case False
    with Cons.prems have "x \<in> fmdom' \<rho>" by (cases j) (auto simp: foldr_fmadd_dom' dest!: nth_mem)
    with False Cons.prems(3) show ?thesis by (auto simp: fmdom'_alt_def)
  qed
qed simp

lemma fmsubset_lookup: "\<lbrakk> \<Sigma> \<subseteq>\<^sub>f \<Sigma>' ; fmlookup \<Sigma> C = Some ce \<rbrakk> \<Longrightarrow> fmlookup \<Sigma>' C = Some ce"
  by (auto simp: fmsubset_alt_def fmpred_iff)

lemma fmsubset_dom: "\<lbrakk> \<Sigma> \<subseteq>\<^sub>f \<Sigma>' ; C |\<in>| fmdom \<Sigma> \<rbrakk> \<Longrightarrow> C |\<in>| fmdom \<Sigma>'"
  by (auto simp: fmlookup_dom_iff dest: fmsubset_lookup)

lemma fcard_fmdom_Suc: "C |\<in>| fmdom \<Sigma> \<Longrightarrow> \<exists>n. fcard (fmdom \<Sigma>) = Suc n"
  by (cases "fcard (fmdom \<Sigma>)") auto

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

lemma map_of_map_snd: "map_of (map (\<lambda>(x, y). (x, f y)) xys) x = map_option f (map_of xys x)"
  by (induction xys) auto

lemma map_of_nth: "\<lbrakk> distinct (map fst xs) ; i < length xs \<rbrakk> \<Longrightarrow> map_of xs (fst (xs ! i)) = Some (snd (xs ! i))"
  by (metis map_of_is_SomeI nth_mem prod.collapse)

(* Lookups in two association lists with the same keys and related values *)
lemma map_of_list_all2:
  "\<lbrakk> map fst xs = map fst ys ; list_all2 R (map snd xs) (map snd ys) ; map_of ys k = Some b \<rbrakk>
  \<Longrightarrow> \<exists>a. map_of xs k = Some a \<and> R a b"
proof (induction xs arbitrary: ys)
  case (Cons x xs)
  then obtain y ys' where "ys = y # ys'" by (cases ys) auto
  with Cons show ?case by (cases "fst x = k") auto
qed simp

lemma map_of_keys: "distinct (map fst kps) \<Longrightarrow> map (\<lambda>x. the (map_of kps x)) (map fst kps) = map snd kps"
  by (intro nth_equalityI) (auto simp: map_of_nth)

lemma distinct_concat_nth:
  "\<lbrakk> distinct (concat xss) ; i < length xss ; j < length xss ; i \<noteq> j \<rbrakk> \<Longrightarrow> set (xss ! i) \<inter> set (xss ! j) = {}"
proof (induction xss arbitrary: i j)
  case (Cons xs xss)
  then show ?case by (cases i; cases j) (auto dest!: nth_mem)
qed simp

lemma UN_set_nth: "\<Union> (f ` set xs) = (\<Union>j \<in> {..<length xs}. f (xs ! j))"
proof (intro set_eqI iffI)
  fix x
  assume "x \<in> \<Union> (f ` set xs)"
  then obtain y where "y \<in> set xs" and "x \<in> f y" by blast
  then obtain j where "j < length xs" and "y = xs ! j" by (auto simp: in_set_conv_nth)
  with \<open>x \<in> f y\<close> show "x \<in> (\<Union>j \<in> {..<length xs}. f (xs ! j))" by auto
next
  fix x
  assume "x \<in> (\<Union>j \<in> {..<length xs}. f (xs ! j))"
  then obtain j where "j < length xs" and "x \<in> f (xs ! j)" by auto
  then show "x \<in> \<Union> (f ` set xs)" using nth_mem by blast
qed

lemma distinct_cover: "\<lbrakk> distinct xs ; n + length ys = length xs ; set ys = set (drop n xs) \<rbrakk> \<Longrightarrow> distinct ys"
proof -
  assume "distinct xs" and "n + length ys = length xs" and "set ys = set (drop n xs)"
  then have "card (set ys) = length ys" using distinct_card[of "drop n xs"] by simp
  then show "distinct ys" by (rule card_distinct)
qed

lemma concat_map_singleton: "(\<And>z. z \<in> set zs \<Longrightarrow> g z = [h z]) \<Longrightarrow> concat (map g zs) = map h zs"
  by (induction zs) auto

lemma map2_replicate: "map2 f xs (replicate (length xs) y) = map (\<lambda>x. f x y) xs"
  by (induction xs) simp_all

lemma length_filter_eq_one: "\<lbrakk> distinct xs ; y \<in> set xs \<rbrakk> \<Longrightarrow> length (filter (\<lambda>x. x = y) xs) = 1"
proof -
  assume "distinct xs" and "y \<in> set xs"
  then have "{x. x = y} \<inter> set xs = {y}" by auto
  with distinct_length_filter[OF \<open>distinct xs\<close>, of "\<lambda>x. x = y"] show ?thesis by simp
qed

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

lemma those_sum_map_Ok_elem: "\<lbrakk> those_sum (map f xs) = Ok ys ; y \<in> set ys \<rbrakk> \<Longrightarrow> \<exists>x \<in> set xs. f x = Ok y"
  by (auto dest!: those_sum_map_Ok simp: list_all2_conv_all_nth in_set_conv_nth) (metis nth_mem)

lemma those_sum_map_Ok_id [simp]: "those_sum (map Ok xs) = Ok xs"
  by (induction xs) simp_all

(* Success of a sequence of results, the sequences of a prefix and a suffix succeed *)
lemma those_sum_append:
  assumes "those_sum (xs @ ys) = Ok zs"
  shows "\<exists>zs'. those_sum xs = Ok zs'" and "\<exists>zs'. those_sum ys = Ok zs'"
  using those_sum_eq[OF assms] by (auto simp: append_eq_map_conv)

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

lemma kw_pattern_single:
  "\<lbrakk> distinct (map fst kps) ; x \<in> set (map fst kps) \<rbrakk>
  \<Longrightarrow> concat (map (\<lambda>(y, p). if y = x then [p] else []) kps) = [the (map_of kps x)]"
proof (induction kps)
  case (Cons kp kps)
  obtain y p where kp: "kp = (y, p)" by (cases kp)
  show ?case
  proof (cases "y = x")
    case True
    with Cons.prems kp have "x \<notin> set (map fst kps)" by simp
    then have "concat (map (\<lambda>(y, p). if y = x then [p] else []) kps) = []" by (induction kps) auto
    with True kp show ?thesis by simp
  next
    case False
    with Cons kp show ?thesis by simp
  qed
qed simp

lemma kw_set:
  assumes "distinct (map fst kps)" and "set (map fst kps) = set zs"
  shows "set (map (\<lambda>(y, p). (p, g y)) kps) = set (map (\<lambda>x. (the (map_of kps x), g x)) zs)"
proof -
  have "set (map (\<lambda>(y, p). (p, g y)) kps) = (\<lambda>y. (the (map_of kps y), g y)) ` set (map fst kps)"
  proof (intro set_eqI iffI)
    fix pu
    assume "pu \<in> set (map (\<lambda>(y, p). (p, g y)) kps)"
    then obtain y p where "(y, p) \<in> set kps" and "pu = (p, g y)" by auto
    with map_of_is_SomeI[OF assms(1)] show "pu \<in> (\<lambda>y. (the (map_of kps y), g y)) ` set (map fst kps)" by force
  next
    fix pu
    assume "pu \<in> (\<lambda>y. (the (map_of kps y), g y)) ` set (map fst kps)"
    then obtain y where "y \<in> set (map fst kps)" and "pu = (the (map_of kps y), g y)" by auto
    then obtain p where "(y, p) \<in> set kps" by auto
    with map_of_is_SomeI[OF assms(1) this] \<open>pu = _\<close> show "pu \<in> set (map (\<lambda>(y, p). (p, g y)) kps)" by force
  qed
  then show ?thesis unfolding assms(2) by auto
qed

(* Sub-patterns of a constructor pattern supplying the fields after the positional ones by keyword: one for each
   such field, and the keyword patterns among them *)
lemma field_patterns_cover:
  assumes "distinct xs" and "n + length kps = length xs" and "set (map fst kps) = set (drop n xs)"
  shows "length (concat (map (\<lambda>x. concat (map (\<lambda>(y, p). if y = x then [p] else []) kps)) (drop n xs)))
         = length kps"
    and "set (concat (map (\<lambda>x. concat (map (\<lambda>(y, p). if y = x then [p] else []) kps)) (drop n xs)))
         = set (map snd kps)"
proof -
  let ?g = "\<lambda>x. concat (map (\<lambda>(y, p). if y = x then [p] else []) kps)"
  have dist': "distinct (drop n xs)" using assms(1) by simp
  have "card (set (map fst kps)) = length (map fst kps)"
    using distinct_card[OF dist'] assms(2, 3) by simp
  then have dist: "distinct (map fst kps)" by (rule card_distinct)
  have g1: "length (?g x) = 1" if "x \<in> set (drop n xs)" for x
  proof -
    have "length (?g x) = length (filter (\<lambda>y. y = x) (map fst kps))" by (induction kps) auto
    with length_filter_eq_one[OF dist that[folded assms(3)]] show ?thesis by simp
  qed
  have "map (length \<circ> ?g) (drop n xs) = map (\<lambda>_. 1) (drop n xs)" by (rule map_cong) (auto simp: g1)
  then show "length (concat (map ?g (drop n xs))) = length kps"
    using assms(2) by (simp add: length_concat map_replicate_const sum_list_replicate)
  show "set (concat (map ?g (drop n xs))) = set (map snd kps)"
  proof
    show "set (concat (map ?g (drop n xs))) \<subseteq> set (map snd kps)" by (force split: if_splits)
    show "set (map snd kps) \<subseteq> set (concat (map ?g (drop n xs)))"
    proof
      fix p
      assume "p \<in> set (map snd kps)"
      then obtain y where yp: "(y, p) \<in> set kps" by auto
      then have "y \<in> set (drop n xs)" using assms(3) by force
      with yp show "p \<in> set (concat (map ?g (drop n xs)))" by force
    qed
  qed
qed

end
