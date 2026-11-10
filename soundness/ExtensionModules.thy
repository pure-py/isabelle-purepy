(* Stability of module checking under extension of the class table; settled class tables *)
theory ExtensionModules
  imports WellFormedModules
begin

subsection \<open>Top-level statements\<close>

(* Class of a type region in the table of the region *)
lemma those_sum_all_Ok: "(\<And>x. x \<in> set xs \<Longrightarrow> f x = Ok ()) \<Longrightarrow> those_sum (map f xs) = Ok (map (\<lambda>_. ()) xs)"
  by (induction xs) (auto simp: bind_sum_def)

lemma region_table_classes:
  assumes "distinct (map (type_def_name \<circ> node) \<chi>s)" and "j < length \<chi>s"
  shows "class_table \<Gamma> q \<chi>s j \<subseteq>\<^sub>f region_table \<Gamma> q \<chi>s \<Sigma>"
proof (cases "node (\<chi>s ! j)")
  case (Dataclass c \<alpha>s b \<phi>)
  have c: "type_def_name (node (\<chi>s ! j)) = c" by (simp add: Dataclass)
  have "\<forall>j' \<in> set [0..<length \<chi>s]. j' \<noteq> j \<longrightarrow> type_def_name (node (\<chi>s ! j')) \<noteq> c"
    using assms c by (auto simp: distinct_conv_nth)
  from fold_class_table_in[OF _ _ Dataclass this, of \<Gamma> q \<Sigma>] assms(2) show ?thesis
    by (auto simp: fmsubset_alt_def fmpred_iff class_table_lookup Dataclass)
qed (simp add: class_table_def fmsubset_alt_def)

(* Top-level statement checked from a well-formed table in which its classes are fresh, checked again from any
   well-formed table containing the result: the same outcome, and the table fixed *)
lemma check_top_stmt_mono:
  assumes "check_top_stmt \<Sigma> q \<Gamma> t = Ok (R, \<Sigma>')" and "wf_class_table \<Sigma>" and "predefined_classes \<subseteq>\<^sub>f \<Sigma>"
    and "wf_cxt \<Sigma> \<Gamma>" and "tyvars \<Gamma> = {}"
    and "\<forall>c \<in> set (declares t). Qualified q c |\<notin>| fmdom \<Sigma>" and "distinct (declares t)"
    and "\<Sigma>' \<subseteq>\<^sub>f \<Sigma>''" and "wf_class_table \<Sigma>''"
  shows "check_top_stmt \<Sigma>'' q \<Gamma> t = Ok (R, \<Sigma>'')"
  using assms
proof (induction t arbitrary: \<Sigma> \<Gamma> R \<Sigma>')
  case (Stmt s)
  from Stmt.prems(1) have R: "check_stmt_at \<Sigma> \<Gamma> None s = Ok R" and \<Sigma>': "\<Sigma>' = \<Sigma>" by (auto simp: bind_sum_Ok)
  have "extension \<Sigma> \<Sigma>''" using Stmt.prems(2, 3, 8) \<Sigma>' by unfold_locales (auto simp: \<Sigma>')
  from check_stmt_mono(2)[OF this Stmt.prems(4), of None s] R show ?case by simp
next
  case (TopSeq t t')
  from TopSeq.prems(1) obtain \<Delta> r \<Sigma>\<^sub>1 R' where t: "check_top_stmt \<Sigma> q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>\<^sub>1)"
    and t': "check_top_stmt \<Sigma>\<^sub>1 q (\<Gamma> \<otimes> \<Delta>) t' = Ok (R', \<Sigma>')" and R: "R = Assigns\<^sub>R \<Delta> r \<otimes> R'"
    by (auto simp: bind_sum_Ok split: static_outcome.splits dest!: not_Returns)
  from TopSeq.prems(6, 7) have fresh: "\<forall>c \<in> set (declares t). Qualified q c |\<notin>| fmdom \<Sigma>"
    and distinct: "distinct (declares t)"
    by auto
  from check_top_stmt_wf[OF t TopSeq.prems(2-5) fresh distinct]
  have sub1: "\<Sigma> \<subseteq>\<^sub>f \<Sigma>\<^sub>1" and wf1: "wf_class_table \<Sigma>\<^sub>1" and \<Delta>: "wf_cxt \<Sigma>\<^sub>1 \<Delta>" "tyvars \<Delta> = {}" by auto
  have fresh': "\<forall>c \<in> set (declares t'). Qualified q c |\<notin>| fmdom \<Sigma>\<^sub>1"
  proof
    fix c
    assume c: "c \<in> set (declares t')"
    with TopSeq.prems(6) have "Qualified q c |\<notin>| fmdom \<Sigma>" by simp
    moreover have "c \<notin> set (declares t)" using TopSeq.prems(7) c by auto
    ultimately show "Qualified q c |\<notin>| fmdom \<Sigma>\<^sub>1" using check_top_stmt_dom[OF t] by blast
  qed
  have cxt: "wf_cxt \<Sigma>\<^sub>1 (\<Gamma> \<otimes> \<Delta>)" using wf_cxt_mono[OF TopSeq.prems(4) sub1] \<Delta>(1) by (rule wf_cxt_add)
  have tyvars: "tyvars (\<Gamma> \<otimes> \<Delta>) = {}" using tyvars_add[of \<Gamma> \<Delta>] TopSeq.prems(5) \<Delta>(2) by blast
  have pre1: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using TopSeq.prems(3) sub1 by (rule fmsubset_trans)
  from check_top_stmt_wf[OF t' wf1 pre1 cxt tyvars fresh'] TopSeq.prems(7) have sub2: "\<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>'" by auto
  have "check_top_stmt \<Sigma>'' q \<Gamma> t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>'')"
    by (rule TopSeq.IH(1)[OF t TopSeq.prems(2-5) fresh distinct fmsubset_trans[OF sub2 TopSeq.prems(8)] TopSeq.prems(9)])
  moreover have "check_top_stmt \<Sigma>'' q (\<Gamma> \<otimes> \<Delta>) t' = Ok (R', \<Sigma>'')"
    using TopSeq.IH(2)[OF t' wf1 pre1 cxt tyvars fresh' _ TopSeq.prems(8, 9)] TopSeq.prems(7) by auto
  ultimately show ?case by (simp add: R)
next
  case (TypeDefs \<chi>s)
  let ?\<Sigma>' = "region_table \<Gamma> q \<chi>s \<Sigma>"
  from TypeDefs.prems(1) have chk: "\<forall>j < length \<chi>s. check_type_def ?\<Sigma>' (type_context \<Gamma> q \<chi>s j) (\<chi>s ! j) = Ok ()"
    and \<Sigma>': "\<Sigma>' = ?\<Sigma>'"
    and R: "R = Assigns\<^sub>R (fmap_of_list (map (\<lambda>j. (type_def_name (node (\<chi>s ! j)), type_entry \<Gamma> q \<chi>s j)) [0..<length \<chi>s])) None"
    by (auto simp: Let_def bind_sum_Ok dest!: those_sum_map_Ok_all)
  have fresh: "\<forall>j < length \<chi>s. \<forall>c. defines_class \<chi>s j c \<longrightarrow> Qualified q c |\<notin>| fmdom \<Sigma>"
    using TypeDefs.prems(6) by (blast intro: defines_class_declares)
  have distinct: "distinct (map (type_def_name \<circ> node) \<chi>s)" using TypeDefs.prems(7) by simp
  have wf': "wf_class_table ?\<Sigma>'" by (rule region_table_wf[OF TypeDefs.prems(2, 3, 4, 5) fresh distinct chk])
  have sub: "\<Sigma> \<subseteq>\<^sub>f ?\<Sigma>'" by (rule region_table_subset[OF fresh])
  have ext: "extension ?\<Sigma>' \<Sigma>''"
    using wf' TypeDefs.prems(8)[unfolded \<Sigma>'] fmsubset_trans[OF TypeDefs.prems(3) sub] by unfold_locales
  have region: "\<forall>\<chi> \<in> set \<chi>s. \<forall>c \<alpha>s b \<phi>. node \<chi> = Dataclass c \<alpha>s b \<phi> \<longrightarrow> Qualified q c |\<in>| fmdom ?\<Sigma>'"
    by (auto simp: fold_class_table_dom in_set_conv_nth)
  have fixed: "region_table \<Gamma> q \<chi>s \<Sigma>'' = \<Sigma>''"
  proof (rule fold_class_table_fixed)
    show "\<forall>j \<in> set [0..<length \<chi>s]. class_table \<Gamma> q \<chi>s j \<subseteq>\<^sub>f \<Sigma>''"
      using fmsubset_trans[OF region_table_classes[OF distinct] TypeDefs.prems(8)[unfolded \<Sigma>']] by auto
  qed
  have "check_type_def \<Sigma>'' (type_context \<Gamma> q \<chi>s j) (\<chi>s ! j) = Ok ()" if "j < length \<chi>s" for j
    using check_type_def_mono[OF ext type_context_wf[OF TypeDefs.prems(5) wf_cxt_mono[OF TypeDefs.prems(4) sub] that region]]
      chk that
    by simp
  then show ?case
    using those_sum_all_Ok[of "[0..<length \<chi>s]" "\<lambda>j. check_type_def \<Sigma>'' (type_context \<Gamma> q \<chi>s j) (\<chi>s ! j)"]
    by (simp add: Let_def fixed R)
qed

subsection \<open>Settled class tables\<close>

(* Module whose checking from any well-formed extension of \<Sigma>, when it succeeds, gives signature \<Gamma> and leaves
   the table fixed, whichever modules are being checked *)
definition stable_module :: "program \<Rightarrow> class_table \<Rightarrow> name \<Rightarrow> cxt \<Rightarrow> bool"
where
"stable_module \<M> \<Sigma> q \<Gamma> =
  (wf_cxt \<Sigma> \<Gamma> \<and> tyvars \<Gamma> = {}
   \<and> (\<forall>V q' \<Sigma>' \<Sigma>''. \<Sigma> \<subseteq>\<^sub>f \<Sigma>' \<longrightarrow> \<Sigma>' \<subseteq>\<^sub>f \<Sigma>'' \<longrightarrow> wf_class_table \<Sigma>' \<longrightarrow> wf_class_table \<Sigma>''
        \<longrightarrow> (\<exists>r. check_module \<M> V \<Sigma>' q' q = Ok r) \<longrightarrow> check_module \<M> V \<Sigma>'' q' q = Ok (\<Gamma>, \<Sigma>'')))"

(* Class table in which every module owning a class is stable *)
definition settled :: "program \<Rightarrow> class_table \<Rightarrow> bool"
where "settled \<M> \<Sigma> = (\<forall>q c. Qualified q c |\<in>| fmdom \<Sigma> \<longrightarrow> (\<exists>\<Gamma>. stable_module \<M> \<Sigma> q \<Gamma>))"

lemma stable_module_mono: "\<lbrakk> stable_module \<M> \<Sigma> q \<Gamma> ; \<Sigma> \<subseteq>\<^sub>f \<Sigma>' \<rbrakk> \<Longrightarrow> stable_module \<M> \<Sigma>' q \<Gamma>"
  unfolding stable_module_def by (blast intro: fmsubset_trans wf_cxt_mono)

lemma settled_predefined: "settled \<M> predefined_classes"
proof -
  have "check_module \<M> V \<Sigma> q' builtins = Ok (the (fmlookup \<P> builtins), \<Sigma>)" for V \<Sigma> q'
    unfolding check_module.simps[of \<M> V \<Sigma> q' builtins]
    by (simp add: \<P>_def fmlookup_of_list builtins_def name_of_def)
  moreover have "wf_cxt predefined_classes (the (fmlookup \<P> builtins))"
    by (auto simp: \<P>_def fmlookup_of_list wf_cxt_iff builtins_def name_of_def predefined_classes_def range_class_def
        type_params_def dest!: map_of_SomeD)
  moreover have "tyvars (the (fmlookup \<P> builtins)) = {}"
    by (rule tyvars_empty) (auto simp: \<P>_def fmlookup_of_list builtins_def name_of_def split: if_splits dest!: map_of_SomeD)
  ultimately have "stable_module \<M> predefined_classes builtins (the (fmlookup \<P> builtins))"
    unfolding stable_module_def by blast
  then show ?thesis
    unfolding settled_def predefined_classes_def range_class_def by (auto simp: name_of_def builtins_def)
qed

(* Contexts of the predefined modules, well-formed in a table containing the predefined classes, and closed *)
lemma predefined_cxt_closed:
  assumes "predefined_classes \<subseteq>\<^sub>f \<Sigma>" and "fmlookup \<P> q = Some \<Gamma>"
  shows "wf_cxt \<Sigma> \<Gamma>" and "tyvars \<Gamma> = {}"
proof -
  have "range_class |\<in>| fmdom \<Sigma>"
    using fmsubset_dom[OF assms(1)] by (simp add: predefined_classes_def fmlookup_dom_iff)
  with assms(2) show "wf_cxt \<Sigma> \<Gamma>" by (auto simp: \<P>_def fmlookup_of_list wf_cxt_iff split: if_splits)
  from assms(2) show "tyvars \<Gamma> = {}"
    by (rule_tac tyvars_empty) (auto simp: \<P>_def fmlookup_of_list split: if_splits dest!: map_of_SomeD)
qed

lemma tyvars_empty_entries:
  "\<lbrakk> tyvars \<Gamma> = {} ; fmlookup \<Gamma> x = Some \<theta> \<rbrakk> \<Longrightarrow> \<theta> \<noteq> TypeVar \<and> fv_entry \<theta> = {}"
  by (force simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff)

(* Extension of well-formed closed contexts and entries *)
lemma extend_wf:
  "\<lbrakk> wf_entry \<Sigma> \<theta> \<and> fv_entry \<theta> = {} \<and> \<theta> \<noteq> TypeVar ; wf_entry \<Sigma> \<theta>' \<and> fv_entry \<theta>' = {} \<and> \<theta>' \<noteq> TypeVar \<rbrakk>
  \<Longrightarrow> wf_entry \<Sigma> (extend_entry \<theta> \<theta>') \<and> fv_entry (extend_entry \<theta> \<theta>') = {} \<and> extend_entry \<theta> \<theta>' \<noteq> TypeVar"
  "\<lbrakk> wf_cxt \<Sigma> \<Gamma> \<and> tyvars \<Gamma> = {} ; wf_cxt \<Sigma> \<Gamma>' \<and> tyvars \<Gamma>' = {} \<rbrakk> \<Longrightarrow> wf_cxt \<Sigma> (\<Gamma> \<uplus> \<Gamma>') \<and> tyvars (\<Gamma> \<uplus> \<Gamma>') = {}"
proof (induction \<theta> \<theta>' and \<Gamma> \<Gamma>' rule: extend_entry_extend_cxt.induct)
  case (4 \<Gamma> \<Gamma>')
  have entry: "wf_entry \<Sigma> \<theta>'' \<and> fv_entry \<theta>'' = {} \<and> \<theta>'' \<noteq> TypeVar" if "fmlookup (\<Gamma> \<uplus> \<Gamma>') x = Some \<theta>''" for x \<theta>''
  proof (cases "fmlookup \<Gamma>' x")
    case None
    with that have "fmlookup \<Gamma> x = Some \<theta>''" by (simp add: fmlookup_dom_iff)
    with "4.prems"(1) show ?thesis by (auto simp: wf_cxt_iff dest: tyvars_empty_entries)
  next
    case (Some \<theta>')
    note look' = Some
    show ?thesis
    proof (cases "fmlookup \<Gamma> x")
      case None
      with look' that have "\<theta>'' = \<theta>'" by (simp add: fmlookup_dom_iff)
      with look' "4.prems"(2) show ?thesis by (auto simp: wf_cxt_iff dest: tyvars_empty_entries)
    next
      case (Some \<theta>)
      with look' that have eq: "\<theta>'' = extend_entry \<theta> \<theta>'" by (simp add: fmlookup_dom_iff)
      have c1: "\<theta> \<noteq> TypeVar \<and> fv_entry \<theta> = {}" by (rule tyvars_empty_entries[OF "4.prems"(1)[THEN conjunct2] Some])
      have c2: "\<theta>' \<noteq> TypeVar \<and> fv_entry \<theta>' = {}" by (rule tyvars_empty_entries[OF "4.prems"(2)[THEN conjunct2] look'])
      from "4.IH"[OF look' Some] c1 c2 Some look' "4.prems" show ?thesis by (auto simp: eq wf_cxt_iff)
    qed
  qed
  have "wf_cxt \<Sigma> (\<Gamma> \<uplus> \<Gamma>')" unfolding wf_cxt_iff using entry by blast
  moreover have "tyvars (\<Gamma> \<uplus> \<Gamma>') = {}" by (rule tyvars_empty) (use entry in blast)
  ultimately show ?case by simp
qed (auto simp: wf_cxt_iff)

subsection \<open>Stability of checking calls\<close>

(* Call f on the modules being checked and the class table, from \<Sigma> with result res and table \<Sigma>': the table
   grows and stays well-formed and settled; from any well-formed table containing \<Sigma>', a call that succeeds
   gives res and leaves a further extension fixed, and the original call gives res and leaves the table fixed *)
definition stable ::
  "program \<Rightarrow> ('v \<Rightarrow> class_table \<Rightarrow> (name \<times> reason) + 'a \<times> class_table) \<Rightarrow> 'v \<Rightarrow> class_table \<Rightarrow> 'a \<Rightarrow> class_table
   \<Rightarrow> bool"
where
"stable \<M> f v \<Sigma> res \<Sigma>' =
  (\<Sigma> \<subseteq>\<^sub>f \<Sigma>' \<and> wf_class_table \<Sigma>' \<and> settled \<M> \<Sigma>'
   \<and> (\<forall>v' \<Sigma>'' \<Sigma>'''. \<Sigma>' \<subseteq>\<^sub>f \<Sigma>'' \<longrightarrow> \<Sigma>'' \<subseteq>\<^sub>f \<Sigma>''' \<longrightarrow> wf_class_table \<Sigma>'' \<longrightarrow> wf_class_table \<Sigma>'''
        \<longrightarrow> (\<exists>r. f v' \<Sigma>'' = Ok r) \<longrightarrow> f v' \<Sigma>''' = Ok (res, \<Sigma>'''))
   \<and> (\<forall>\<Sigma>''. \<Sigma>' \<subseteq>\<^sub>f \<Sigma>'' \<longrightarrow> wf_class_table \<Sigma>'' \<longrightarrow> f v \<Sigma>'' = Ok (res, \<Sigma>'')))"

lemma stableD:
  assumes "stable \<M> f v \<Sigma> res \<Sigma>'"
  shows "\<Sigma> \<subseteq>\<^sub>f \<Sigma>'" and "wf_class_table \<Sigma>'" and "settled \<M> \<Sigma>'"
    and "\<lbrakk> \<Sigma>' \<subseteq>\<^sub>f \<Sigma>'' ; \<Sigma>'' \<subseteq>\<^sub>f \<Sigma>''' ; wf_class_table \<Sigma>'' ; wf_class_table \<Sigma>''' ; f v' \<Sigma>'' = Ok r \<rbrakk>
          \<Longrightarrow> f v' \<Sigma>''' = Ok (res, \<Sigma>''')"
    and "\<lbrakk> \<Sigma>' \<subseteq>\<^sub>f \<Sigma>'' ; wf_class_table \<Sigma>'' \<rbrakk> \<Longrightarrow> f v \<Sigma>'' = Ok (res, \<Sigma>'')"
  using assms unfolding stable_def by blast+

lemma stable_return: "\<lbrakk> wf_class_table \<Sigma> ; settled \<M> \<Sigma> \<rbrakk> \<Longrightarrow> stable \<M> (\<lambda>v \<Sigma>. Ok (a, \<Sigma>)) v \<Sigma> a \<Sigma>"
  unfolding stable_def by simp

lemma stable_wrap:
  "(\<And>m r. (w m = Ok r) = (m = Ok r)) \<Longrightarrow> stable \<M> (\<lambda>v \<Sigma>. w (f v \<Sigma>)) v \<Sigma> a \<Sigma>' = stable \<M> f v \<Sigma> a \<Sigma>'"
  unfolding stable_def by simp

lemma stable_guard: "m = Ok () \<Longrightarrow> stable \<M> (\<lambda>v \<Sigma>. do { m; f v \<Sigma> }) v \<Sigma> a \<Sigma>' = stable \<M> f v \<Sigma> a \<Sigma>'"
  by simp

lemma stable_bind:
  assumes f: "stable \<M> f v \<Sigma> a \<Sigma>\<^sub>1" and g: "stable \<M> (g a) v \<Sigma>\<^sub>1 b \<Sigma>\<^sub>2"
  shows "stable \<M> (\<lambda>v \<Sigma>. do { (a', \<Sigma>') \<leftarrow> f v \<Sigma>; g a' v \<Sigma>' }) v \<Sigma> b \<Sigma>\<^sub>2"
  unfolding stable_def
proof (intro conjI allI impI)
  show "\<Sigma> \<subseteq>\<^sub>f \<Sigma>\<^sub>2" using stableD(1)[OF f] stableD(1)[OF g] by (rule fmsubset_trans)
  show "wf_class_table \<Sigma>\<^sub>2" and "settled \<M> \<Sigma>\<^sub>2" using stableD(2, 3)[OF g] by simp_all
next
  fix v' \<Sigma>'' \<Sigma>'''
  assume sub: "\<Sigma>\<^sub>2 \<subseteq>\<^sub>f \<Sigma>''" "\<Sigma>'' \<subseteq>\<^sub>f \<Sigma>'''" and wf: "wf_class_table \<Sigma>''" "wf_class_table \<Sigma>'''"
    and "\<exists>r. do { (a', \<Sigma>') \<leftarrow> f v' \<Sigma>''; g a' v' \<Sigma>' } = Ok r"
  then obtain a'' \<Sigma>\<^sub>1'' r where f'': "f v' \<Sigma>'' = Ok (a'', \<Sigma>\<^sub>1'')" and g'': "g a'' v' \<Sigma>\<^sub>1'' = Ok r"
    by (auto simp: bind_sum_Ok)
  have sub1: "\<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>''" using stableD(1)[OF g] sub(1) by (rule fmsubset_trans)
  from stableD(4)[OF f sub1 _ wf(1) wf(1) f''] f'' have a'': "a'' = a" and \<Sigma>\<^sub>1'': "\<Sigma>\<^sub>1'' = \<Sigma>''" by auto
  have "f v' \<Sigma>''' = Ok (a, \<Sigma>''')" by (rule stableD(4)[OF f sub1 sub(2) wf f''])
  moreover have "g a v' \<Sigma>''' = Ok (b, \<Sigma>''')"
    by (rule stableD(4)[OF g sub(1) sub(2) wf g''[unfolded a'' \<Sigma>\<^sub>1'']])
  ultimately show "do { (a', \<Sigma>') \<leftarrow> f v' \<Sigma>'''; g a' v' \<Sigma>' } = Ok (b, \<Sigma>''')" by simp
next
  fix \<Sigma>''
  assume sub: "\<Sigma>\<^sub>2 \<subseteq>\<^sub>f \<Sigma>''" and wf: "wf_class_table \<Sigma>''"
  have "f v \<Sigma>'' = Ok (a, \<Sigma>'')" using stableD(5)[OF f fmsubset_trans[OF stableD(1)[OF g] sub] wf] .
  moreover have "g a v \<Sigma>'' = Ok (b, \<Sigma>'')" using stableD(5)[OF g sub wf] .
  ultimately show "do { (a', \<Sigma>') \<leftarrow> f v \<Sigma>''; g a' v \<Sigma>' } = Ok (b, \<Sigma>'')" by simp
qed

(* Table-valued call as a call with a unit result *)
lemma bind_sum_table: "bind_sum m (\<lambda>\<Sigma>'. g \<Sigma>') = bind_sum (map_sum id (Pair ()) m) (\<lambda>(u, \<Sigma>'). g \<Sigma>')"
  by (cases m) simp_all

lemma map_sum_bind: "map_sum id h (bind_sum m f) = bind_sum m (\<lambda>x. map_sum id h (f x))"
  by (cases m) simp_all

lemma map_sum_pair_Ok: "(map_sum id (Pair ()) m = Ok (u, \<Sigma>)) = (m = Ok \<Sigma>)"
  by (cases m) auto


lemma stable_pair: "stable \<M> f (V, q') \<Sigma> a \<Sigma>' \<Longrightarrow> stable \<M> (\<lambda>V \<Sigma>. f (V, q') \<Sigma>) V \<Sigma> a \<Sigma>'"
  unfolding stable_def by blast

lemma stable_check_module_pair:
  "stable \<M> (\<lambda>(V, q') \<Sigma>. check_module \<M> V \<Sigma> q' p) (V, q') \<Sigma> a \<Sigma>'
  \<Longrightarrow> stable \<M> (\<lambda>V \<Sigma>. check_module \<M> V \<Sigma> q' p) V \<Sigma> a \<Sigma>'"
  by (drule stable_pair) simp

lemma stable_locate_in: "stable \<M> (\<lambda>v \<Sigma>. locate_in q p (f v \<Sigma>)) v \<Sigma> a \<Sigma>' = stable \<M> f v \<Sigma> a \<Sigma>'"
  unfolding stable_def by simp

lemma stable_map_sum: "stable \<M> (\<lambda>v \<Sigma>. map_sum g id (f v \<Sigma>)) v \<Sigma> a \<Sigma>' = stable \<M> f v \<Sigma> a \<Sigma>'"
  unfolding stable_def by simp

lemma stable_bind_table:
  assumes f: "stable \<M> (\<lambda>v \<Sigma>. map_sum id (Pair ()) (f v \<Sigma>)) v \<Sigma> () \<Sigma>\<^sub>1" and g: "stable \<M> g v \<Sigma>\<^sub>1 b \<Sigma>\<^sub>2"
  shows "stable \<M> (\<lambda>v \<Sigma>. do { \<Sigma>' \<leftarrow> f v \<Sigma>; g v \<Sigma>' }) v \<Sigma> b \<Sigma>\<^sub>2"
proof -
  have "(\<lambda>v \<Sigma>. do { \<Sigma>' \<leftarrow> f v \<Sigma>; g v \<Sigma>' }) = (\<lambda>v \<Sigma>. do { (u, \<Sigma>') \<leftarrow> map_sum id (Pair ()) (f v \<Sigma>); g v \<Sigma>' })"
    by (intro ext) (rule bind_sum_table)
  with stable_bind[OF f, of "\<lambda>u. g" b \<Sigma>\<^sub>2] g show ?thesis by simp
qed

subsection \<open>Stability of module checking\<close>

(* Entry of a checked module, well-formed and without type variables *)
abbreviation closed_entry :: "class_table \<Rightarrow> cxt_entry \<Rightarrow> bool"
where "closed_entry \<Sigma> \<theta> \<equiv> wf_entry \<Sigma> \<theta> \<and> fv_entry \<theta> = {} \<and> \<theta> \<noteq> TypeVar"

(* Context of a checked module, well-formed and without type variables *)
abbreviation closed_cxt :: "class_table \<Rightarrow> cxt \<Rightarrow> bool"
where "closed_cxt \<Sigma> \<Gamma> \<equiv> wf_cxt \<Sigma> \<Gamma> \<and> tyvars \<Gamma> = {}"

lemma closed_cxt_mono: "\<lbrakk> closed_cxt \<Sigma> \<Gamma> ; \<Sigma> \<subseteq>\<^sub>f \<Sigma>' \<rbrakk> \<Longrightarrow> closed_cxt \<Sigma>' \<Gamma>"
  by (auto intro: wf_cxt_mono)

lemma closed_entry_mono: "\<lbrakk> closed_entry \<Sigma> \<theta> ; \<Sigma> \<subseteq>\<^sub>f \<Sigma>' \<rbrakk> \<Longrightarrow> closed_entry \<Sigma>' \<theta>"
  by (auto intro: wf_entry_mono)

lemma closed_cxt_add: "\<lbrakk> closed_cxt \<Sigma> \<Gamma> ; closed_cxt \<Sigma> \<Delta> \<rbrakk> \<Longrightarrow> closed_cxt \<Sigma> (\<Gamma> \<otimes> \<Delta>)"
  using tyvars_add[of \<Gamma> \<Delta>] by (auto intro: wf_cxt_add)

lemma closed_cxt_single: "closed_entry \<Sigma> \<theta> \<Longrightarrow> closed_cxt \<Sigma> (fmupd x \<theta> fmempty)"
  by (auto simp: wf_cxt_iff tyvars_single)

lemma closed_cxt_submods: "closed_cxt \<Sigma> (submods \<M> q)"
  by (auto simp: wf_cxt_iff submods_lookup intro!: tyvars_empty split: if_splits)

lemma closed_cxt_of_list: "\<forall>\<theta> \<in> set \<theta>s. closed_entry \<Sigma> \<theta> \<Longrightarrow> closed_cxt \<Sigma> (fmap_of_list (zip xs \<theta>s))"
  by (auto simp: wf_cxt_iff fmlookup_of_list intro!: tyvars_empty dest!: map_of_SomeD set_zip_rightD)

lemma closed_cxt_extend: "\<lbrakk> closed_cxt \<Sigma> \<Gamma> ; closed_cxt \<Sigma> \<Gamma>' \<rbrakk> \<Longrightarrow> closed_cxt \<Sigma> (\<Gamma> \<uplus> \<Gamma>')"
  by (rule extend_wf(2)) simp_all

lemma closed_cxt_scope: "scope Unbound ys (t :: top_stmt) = Some \<Gamma>\<^sub>s \<Longrightarrow> closed_cxt \<Sigma> \<Gamma>\<^sub>s"
  by (auto simp: scope_top_def wf_cxt_fmconst intro!: tyvars_empty dest!: fmconst_entry split: if_splits)

lemma builtins_closed: "predefined_classes \<subseteq>\<^sub>f \<Sigma> \<Longrightarrow> closed_cxt \<Sigma> (the (fmlookup \<P> builtins))"
  using predefined_cxt_closed[of \<Sigma> builtins "the (fmlookup \<P> builtins)"]
  by (simp add: \<P>_def fmlookup_of_list builtins_def name_of_def)

(* Checking from a well-formed settled table containing the predefined classes: stable, with a well-formed
   closed result *)
lemma check_module_stable:
  "\<lbrakk> check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>') ; wf_class_table \<Sigma> ; predefined_classes \<subseteq>\<^sub>f \<Sigma> ; settled \<M> \<Sigma> \<rbrakk>
   \<Longrightarrow> stable \<M> (\<lambda>(V, q') \<Sigma>. check_module \<M> V \<Sigma> q' q) (V, q') \<Sigma> \<Gamma> \<Sigma>' \<and> closed_cxt \<Sigma>' \<Gamma>"
  "\<lbrakk> check_imports \<M> V \<Sigma> q \<iota>s = Ok (\<Gamma>, \<Sigma>') ; wf_class_table \<Sigma> ; predefined_classes \<subseteq>\<^sub>f \<Sigma> ; settled \<M> \<Sigma> \<rbrakk>
   \<Longrightarrow> stable \<M> (\<lambda>V \<Sigma>. check_imports \<M> V \<Sigma> q \<iota>s) V \<Sigma> \<Gamma> \<Sigma>' \<and> closed_cxt \<Sigma>' \<Gamma>"
  "\<lbrakk> submodules \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs = Ok (\<Gamma>, \<Sigma>') ; wf_class_table \<Sigma> ; predefined_classes \<subseteq>\<^sub>f \<Sigma> ; settled \<M> \<Sigma>
   ; closed_cxt \<Sigma> \<Gamma>\<^sub>0 \<rbrakk>
   \<Longrightarrow> stable \<M> (\<lambda>V \<Sigma>. submodules \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs) V \<Sigma> \<Gamma> \<Sigma>' \<and> closed_cxt \<Sigma>' \<Gamma>"
  "\<lbrakk> imports_entry \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 x = Ok (\<theta>, \<Sigma>') ; wf_class_table \<Sigma> ; predefined_classes \<subseteq>\<^sub>f \<Sigma> ; settled \<M> \<Sigma>
   ; closed_cxt \<Sigma> \<Gamma>\<^sub>0 \<rbrakk>
   \<Longrightarrow> stable \<M> (\<lambda>V \<Sigma>. imports_entry \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 x) V \<Sigma> \<theta> \<Sigma>' \<and> closed_entry \<Sigma>' \<theta>"
  "\<lbrakk> imports_entries \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs = Ok (\<theta>s, \<Sigma>') ; wf_class_table \<Sigma> ; predefined_classes \<subseteq>\<^sub>f \<Sigma> ; settled \<M> \<Sigma>
   ; closed_cxt \<Sigma> \<Gamma>\<^sub>0 \<rbrakk>
   \<Longrightarrow> stable \<M> (\<lambda>V \<Sigma>. imports_entries \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs) V \<Sigma> \<theta>s \<Sigma>' \<and> (\<forall>\<theta> \<in> set \<theta>s. closed_entry \<Sigma>' \<theta>)"
  "\<lbrakk> check_modules \<M> V \<Sigma> q qs = Ok \<Sigma>' ; wf_class_table \<Sigma> ; predefined_classes \<subseteq>\<^sub>f \<Sigma> ; settled \<M> \<Sigma> \<rbrakk>
   \<Longrightarrow> stable \<M> (\<lambda>V \<Sigma>. map_sum id (Pair ()) (check_modules \<M> V \<Sigma> q qs)) V \<Sigma> () \<Sigma>'"
proof (induction \<M> V \<Sigma> q' q and \<M> V \<Sigma> q \<iota>s and \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs and \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 x
    and \<M> V \<Sigma> q p' \<Gamma>\<^sub>0 xs and \<M> V \<Sigma> q qs
    arbitrary: \<Gamma> \<Sigma>' and \<Gamma> \<Sigma>' and \<Gamma> \<Sigma>' and \<theta> \<Sigma>' and \<theta>s \<Sigma>' and \<Sigma>'
    rule: check_module_check_imports_submodules_imports_entry_imports_entries_check_modules.induct)
  case (1 \<M> V \<Sigma> q' q)
  note prems = "1.prems"
  show ?case
  proof (cases "fmlookup \<P> q")
    case (Some \<Gamma>\<^sub>0)
    have pre: "check_module \<M> V'' \<Sigma>'' q'' q = Ok (\<Gamma>\<^sub>0, \<Sigma>'')" for V'' q'' \<Sigma>''
      by (simp add: check_module.simps[of \<M> V'' \<Sigma>'' q'' q] Some)
    with prems(1) have \<Gamma>: "\<Gamma> = \<Gamma>\<^sub>0" and \<Sigma>': "\<Sigma>' = \<Sigma>" by auto
    show ?thesis
      unfolding stable_def \<Gamma> \<Sigma>'
      using prems(2, 4) predefined_cxt_closed[OF prems(3) Some] by (auto simp: pre split: prod.splits)
  next
    case None
    from check_module_body[OF prems(1) None] obtain \<iota>s t \<Gamma>' \<Sigma>\<^sub>1 \<Gamma>\<^sub>s \<Delta> r
      where M: "fmlookup \<M> q = Some (ModuleBody \<iota>s t)" and V: "q \<notin> set V"
      and imp: "check_imports \<M> (V @ [q]) \<Sigma> q \<iota>s = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
      and red: "redeclared node {} (declarations \<iota>s) = None"
      and sc: "scope Unbound (declares \<iota>s) t = Some \<Gamma>\<^sub>s"
      and cad: "check_assignments_declared {} (assign_targets t) (declares t) (binds t) = Ok ()"
      and top: "check_top_stmt \<Sigma>\<^sub>1 q (the (fmlookup \<P> builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s) t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>')"
      and X: "(fmdom \<Gamma>' |\<union>| fmdom \<Gamma>\<^sub>s) |\<inter>| fmdom (submods \<M> q) = {||}" and \<Gamma>: "\<Gamma> = submods \<M> q \<otimes> \<Delta>" .
    show ?thesis
    proof (cases "\<exists>c. Qualified q c |\<in>| fmdom \<Sigma>")
      case True
      then obtain \<Gamma>\<^sub>q where sm: "stable_module \<M> \<Sigma> q \<Gamma>\<^sub>q" using prems(4) unfolding settled_def by blast
      have fixed: "check_module \<M> V'' \<Sigma>''' q'' q = Ok (\<Gamma>\<^sub>q, \<Sigma>''')"
        if "\<Sigma> \<subseteq>\<^sub>f \<Sigma>''" and "\<Sigma>'' \<subseteq>\<^sub>f \<Sigma>'''" and "wf_class_table \<Sigma>''" and "wf_class_table \<Sigma>'''"
          and "check_module \<M> V'' \<Sigma>'' q'' q = Ok r'"
        for V'' q'' \<Sigma>'' \<Sigma>''' r'
        using sm that unfolding stable_module_def by blast
      from fixed[OF fmsubset_refl fmsubset_refl prems(2) prems(2) prems(1)] prems(1)
      have \<Gamma>: "\<Gamma> = \<Gamma>\<^sub>q" and \<Sigma>': "\<Sigma>' = \<Sigma>" by auto
      show ?thesis
        unfolding stable_def \<Gamma> \<Sigma>'
      proof (intro conjI allI impI)
        fix v' \<Sigma>'' \<Sigma>'''
        assume "\<Sigma> \<subseteq>\<^sub>f \<Sigma>''" and "\<Sigma>'' \<subseteq>\<^sub>f \<Sigma>'''" and "wf_class_table \<Sigma>''" and "wf_class_table \<Sigma>'''"
          and "\<exists>r'. (\<lambda>(V'', q'') \<Sigma>. check_module \<M> V'' \<Sigma> q'' q) v' \<Sigma>'' = Ok r'"
        then show "(\<lambda>(V'', q'') \<Sigma>. check_module \<M> V'' \<Sigma> q'' q) v' \<Sigma>''' = Ok (\<Gamma>\<^sub>q, \<Sigma>''')"
          by (cases v') (auto intro: fixed)
      next
        fix \<Sigma>''
        assume "\<Sigma> \<subseteq>\<^sub>f \<Sigma>''" and "wf_class_table \<Sigma>''"
        from fixed[OF fmsubset_refl this(1) prems(2) this(2) prems(1)]
        show "(\<lambda>(V'', q'') \<Sigma>. check_module \<M> V'' \<Sigma> q'' q) (V, q') \<Sigma>'' = Ok (\<Gamma>\<^sub>q, \<Sigma>'')" by simp
      qed (use prems(2, 4) sm in \<open>simp_all add: stable_module_def\<close>)
    next
      case False
      from "1.IH"[OF None V M refl imp prems(2, 3, 4)]
      have st_imp: "stable \<M> (\<lambda>V \<Sigma>. check_imports \<M> V \<Sigma> q \<iota>s) (V @ [q]) \<Sigma> \<Gamma>' \<Sigma>\<^sub>1" and cl\<Gamma>': "closed_cxt \<Sigma>\<^sub>1 \<Gamma>'"
        by auto
      note sub1 = stableD(1)[OF st_imp] and wf1 = stableD(2)[OF st_imp] and set1 = stableD(3)[OF st_imp]
      have pre1: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using prems(3) sub1 by (rule fmsubset_trans)
      let ?\<Gamma>\<^sub>0 = "the (fmlookup \<P> builtins) \<otimes> \<Gamma>' \<otimes> \<Gamma>\<^sub>s"
      have cl\<Gamma>\<^sub>0: "closed_cxt \<Sigma>\<^sub>1 ?\<Gamma>\<^sub>0"
        using builtins_closed[OF pre1] cl\<Gamma>' closed_cxt_scope[OF sc] by (intro closed_cxt_add)
      have distinct: "distinct (declares t)" using sc by (simp add: scope_top_def split: if_splits)
      have fresh: "\<forall>c \<in> set (declares t). Qualified q c |\<notin>| fmdom \<Sigma>\<^sub>1"
      proof (intro ballI notI)
        fix c
        assume "Qualified q c |\<in>| fmdom \<Sigma>\<^sub>1"
        moreover have "Qualified q c |\<notin>| fmdom \<Sigma>" using False by blast
        ultimately show False using check_module_owners(2)[OF imp] by auto
      qed
      from check_top_stmt_wf[OF top wf1 pre1 cl\<Gamma>\<^sub>0[THEN conjunct1] cl\<Gamma>\<^sub>0[THEN conjunct2] fresh distinct]
      have sub2: "\<Sigma>\<^sub>1 \<subseteq>\<^sub>f \<Sigma>'" and wf': "wf_class_table \<Sigma>'" and cl\<Delta>: "closed_cxt \<Sigma>' \<Delta>" by auto
      have cl\<Gamma>: "closed_cxt \<Sigma>' \<Gamma>" using closed_cxt_submods cl\<Delta> unfolding \<Gamma> by (rule closed_cxt_add)
      (* Checking again from a well-formed table containing the result *)
      have recheck: "check_module \<M> V'' \<Sigma>''' q'' q = Ok (\<Gamma>, \<Sigma>''')"
        if "\<Sigma>' \<subseteq>\<^sub>f \<Sigma>''" and "\<Sigma>'' \<subseteq>\<^sub>f \<Sigma>'''" and "wf_class_table \<Sigma>''" and "wf_class_table \<Sigma>'''"
          and "check_module \<M> V'' \<Sigma>'' q'' q = Ok (\<Gamma>\<^sub>r, \<Sigma>\<^sub>r)"
        for V'' q'' \<Sigma>'' \<Sigma>''' \<Gamma>\<^sub>r \<Sigma>\<^sub>r
      proof -
        note chk'' = that(5)
        obtain \<iota>s'' t'' \<Gamma>'' \<Sigma>\<^sub>1'' where M'': "fmlookup \<M> q = Some (ModuleBody \<iota>s'' t'')" and V'': "q \<notin> set V''"
          and imp0: "check_imports \<M> (V'' @ [q]) \<Sigma>'' q \<iota>s'' = Ok (\<Gamma>'', \<Sigma>\<^sub>1'')"
          by (rule check_module_body[OF chk'' None]) blast
        from M'' M imp0 have imp'': "check_imports \<M> (V'' @ [q]) \<Sigma>'' q \<iota>s = Ok (\<Gamma>'', \<Sigma>\<^sub>1'')" by simp
        have imp''': "check_imports \<M> (V'' @ [q]) \<Sigma>''' q \<iota>s = Ok (\<Gamma>', \<Sigma>''')"
          by (rule stableD(4)[OF st_imp fmsubset_trans[OF sub2 that(1)] that(2, 3, 4) imp''])
        have top''': "check_top_stmt \<Sigma>''' q ?\<Gamma>\<^sub>0 t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>''')"
          by (rule check_top_stmt_mono[OF top wf1 pre1 cl\<Gamma>\<^sub>0[THEN conjunct1] cl\<Gamma>\<^sub>0[THEN conjunct2] fresh distinct
                fmsubset_trans[OF that(1, 2)] that(4)])
        show ?thesis
          using None V'' M imp''' red sc cad top''' X
          by (simp add: check_module.simps[of \<M> V'' \<Sigma>''' q'' q] \<Gamma> Let_def)
      qed
      have same: "check_module \<M> V \<Sigma>'' q' q = Ok (\<Gamma>, \<Sigma>'')" if "\<Sigma>' \<subseteq>\<^sub>f \<Sigma>''" and "wf_class_table \<Sigma>''" for \<Sigma>''
      proof -
        have imp'': "check_imports \<M> (V @ [q]) \<Sigma>'' q \<iota>s = Ok (\<Gamma>', \<Sigma>'')"
          by (rule stableD(5)[OF st_imp fmsubset_trans[OF sub2 that(1)] that(2)])
        have top'': "check_top_stmt \<Sigma>'' q ?\<Gamma>\<^sub>0 t = Ok (Assigns\<^sub>R \<Delta> r, \<Sigma>'')"
          by (rule check_top_stmt_mono[OF top wf1 pre1 cl\<Gamma>\<^sub>0[THEN conjunct1] cl\<Gamma>\<^sub>0[THEN conjunct2] fresh distinct that])
        show ?thesis
          using None V M imp'' red sc cad top'' X by (simp add: check_module.simps[of \<M> V \<Sigma>'' q' q] \<Gamma> Let_def)
      qed
      have settled': "settled \<M> \<Sigma>'"
        unfolding settled_def
      proof (intro allI impI)
        fix p c
        assume pc: "Qualified p c |\<in>| fmdom \<Sigma>'"
        show "\<exists>\<Gamma>''. stable_module \<M> \<Sigma>' p \<Gamma>''"
        proof (cases "Qualified p c |\<in>| fmdom \<Sigma>\<^sub>1")
          case True
          with set1 obtain \<Gamma>'' where "stable_module \<M> \<Sigma>\<^sub>1 p \<Gamma>''" unfolding settled_def by blast
          from stable_module_mono[OF this sub2] show ?thesis by blast
        next
          case False
          with check_top_stmt_dom[OF top pc] have "p = q" by auto
          moreover have "stable_module \<M> \<Sigma>' q \<Gamma>"
            unfolding stable_module_def
          proof (intro conjI allI impI)
            show "wf_cxt \<Sigma>' \<Gamma>" and "tyvars \<Gamma> = {}" using cl\<Gamma> by simp_all
          next
            fix V\<^sub>0 q\<^sub>0 \<Sigma>\<^sub>a \<Sigma>\<^sub>b
            assume sub: "\<Sigma>' \<subseteq>\<^sub>f \<Sigma>\<^sub>a" "\<Sigma>\<^sub>a \<subseteq>\<^sub>f \<Sigma>\<^sub>b"
              and wf: "wf_class_table \<Sigma>\<^sub>a" "wf_class_table \<Sigma>\<^sub>b"
              and "\<exists>r. check_module \<M> V\<^sub>0 \<Sigma>\<^sub>a q\<^sub>0 q = Ok r"
            then obtain \<Gamma>\<^sub>r \<Sigma>\<^sub>r where "check_module \<M> V\<^sub>0 \<Sigma>\<^sub>a q\<^sub>0 q = Ok (\<Gamma>\<^sub>r, \<Sigma>\<^sub>r)" by (metis surj_pair)
            from recheck[OF sub wf this] show "check_module \<M> V\<^sub>0 \<Sigma>\<^sub>b q\<^sub>0 q = Ok (\<Gamma>, \<Sigma>\<^sub>b)" .
          qed
          ultimately show ?thesis by blast
        qed
      qed
      show ?thesis
        unfolding stable_def
      proof (intro conjI allI impI)
        show "\<Sigma> \<subseteq>\<^sub>f \<Sigma>'" using sub1 sub2 by (rule fmsubset_trans)
      next
        fix v' \<Sigma>'' \<Sigma>'''
        assume "\<Sigma>' \<subseteq>\<^sub>f \<Sigma>''" and "\<Sigma>'' \<subseteq>\<^sub>f \<Sigma>'''" and "wf_class_table \<Sigma>''" and "wf_class_table \<Sigma>'''"
          and "\<exists>r'. (\<lambda>(V'', q'') \<Sigma>. check_module \<M> V'' \<Sigma> q'' q) v' \<Sigma>'' = Ok r'"
        then show "(\<lambda>(V'', q'') \<Sigma>. check_module \<M> V'' \<Sigma> q'' q) v' \<Sigma>''' = Ok (\<Gamma>, \<Sigma>''')"
          by (cases v') (auto intro: recheck)
      next
        fix \<Sigma>''
        assume "\<Sigma>' \<subseteq>\<^sub>f \<Sigma>''" and "wf_class_table \<Sigma>''"
        from same[OF this] show "(\<lambda>(V'', q'') \<Sigma>. check_module \<M> V'' \<Sigma> q'' q) (V, q') \<Sigma>'' = Ok (\<Gamma>, \<Sigma>'')"
          by simp
      qed (use wf' settled' cl\<Gamma> in simp_all)
    qed
  qed
next
  case (2 \<M> V \<Sigma> q)
  then show ?case using stable_return[OF "2.prems"(2, 4)] by (simp add: check_imports.simps)
next
  case (3 \<M> V \<Sigma> q p q' \<iota>s)
  note prems = "3.prems"
  obtain y ys where vars: "variables q' = y # ys" using variables_nonempty by (cases "variables q'") auto
  from prems(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Delta>' \<Sigma>\<^sub>2 \<Gamma>'' where ens: "\<not> q \<prec> q'"
    and m: "check_module \<M> V \<Sigma> q (Simple y) = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and sub: "submodules \<M> V \<Sigma>\<^sub>1 q (Simple y) \<Delta> ys = Ok (\<Delta>', \<Sigma>\<^sub>2)"
    and rest: "check_imports \<M> V \<Sigma>\<^sub>2 q \<iota>s = Ok (\<Gamma>'', \<Sigma>')"
    and \<Gamma>: "\<Gamma> = fmupd y (ModChecked (Simple y) \<Delta>') fmempty \<uplus> \<Gamma>''"
    by (auto simp: check_imports.simps vars bind_sum_Ok ensure_def split: if_splits)
  have ens': "ensure (\<not> q \<prec> q') (q, ImportOfContainedModule q' q) = Ok ()" by (simp add: ensure_def ens)
  from "3.IH"(1)[OF vars ens' m prems(2-4)]
  have sm: "stable \<M> (\<lambda>V \<Sigma>. check_module \<M> V \<Sigma> q (Simple y)) V \<Sigma> \<Delta> \<Sigma>\<^sub>1" and cl\<Delta>: "closed_cxt \<Sigma>\<^sub>1 \<Delta>"
    using stable_pair[of \<M> "\<lambda>(V, q') \<Sigma>. check_module \<M> V \<Sigma> q' (Simple y)" V q \<Sigma> \<Delta> \<Sigma>\<^sub>1] by auto
  note sub1 = stableD(1)[OF sm] and wf1 = stableD(2)[OF sm] and set1 = stableD(3)[OF sm]
  have pre1: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using prems(3) sub1 by (rule fmsubset_trans)
  from "3.IH"(2)[OF vars ens' m refl sub wf1 pre1 set1 cl\<Delta>]
  have ss: "stable \<M> (\<lambda>V \<Sigma>. submodules \<M> V \<Sigma> q (Simple y) \<Delta> ys) V \<Sigma>\<^sub>1 \<Delta>' \<Sigma>\<^sub>2" and cl\<Delta>': "closed_cxt \<Sigma>\<^sub>2 \<Delta>'"
    by auto
  note sub2 = stableD(1)[OF ss] and wf2 = stableD(2)[OF ss] and set2 = stableD(3)[OF ss]
  have pre2: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>2" using pre1 sub2 by (rule fmsubset_trans)
  from "3.IH"(3)[OF vars ens' m refl sub refl rest wf2 pre2 set2]
  have si: "stable \<M> (\<lambda>V \<Sigma>. check_imports \<M> V \<Sigma> q \<iota>s) V \<Sigma>\<^sub>2 \<Gamma>'' \<Sigma>'" and cl\<Gamma>'': "closed_cxt \<Sigma>' \<Gamma>''" by auto
  note sub3 = stableD(1)[OF si] and wf3 = stableD(2)[OF si] and set3 = stableD(3)[OF si]
  have st: "stable \<M> (\<lambda>V \<Sigma>. do {
      (\<Delta>, \<Sigma>\<^sub>1) \<leftarrow> check_module \<M> V \<Sigma> q (Simple y);
      (\<Delta>', \<Sigma>\<^sub>2) \<leftarrow> submodules \<M> V \<Sigma>\<^sub>1 q (Simple y) \<Delta> ys;
      (\<Gamma>, \<Sigma>') \<leftarrow> check_imports \<M> V \<Sigma>\<^sub>2 q \<iota>s;
      Ok (fmupd y (ModChecked (Simple y) \<Delta>') fmempty \<uplus> \<Gamma>, \<Sigma>') }) V \<Sigma> \<Gamma> \<Sigma>'"
    unfolding \<Gamma>
    by (rule stable_bind[OF sm], rule stable_bind[OF ss], rule stable_bind[OF si]) (rule stable_return[OF wf3 set3])
  have "closed_entry \<Sigma>' (ModChecked (Simple y) \<Delta>')" using closed_cxt_mono[OF cl\<Delta>' sub3] by simp
  then have "closed_cxt \<Sigma>' \<Gamma>" unfolding \<Gamma> using cl\<Gamma>'' by (intro closed_cxt_extend closed_cxt_single)
  with st show ?case by (simp add: check_imports.simps vars ensure_def ens stable_locate_in stable_map_sum)
next
  case (4 \<M> V \<Sigma> q p q' xs \<iota>s)
  note prems = "4.prems"
  from prems(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Sigma>\<^sub>2 \<theta>s \<Sigma>\<^sub>3 \<Gamma>'' where m: "check_module \<M> V \<Sigma> q q' = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and ms: "check_modules \<M> V \<Sigma>\<^sub>1 q (unique_to q' q) = Ok \<Sigma>\<^sub>2" and red: "redeclared id {} xs = None"
    and ent: "imports_entries \<M> V \<Sigma>\<^sub>2 q q' \<Delta> xs = Ok (\<theta>s, \<Sigma>\<^sub>3)"
    and rest: "check_imports \<M> V \<Sigma>\<^sub>3 q \<iota>s = Ok (\<Gamma>'', \<Sigma>')" and \<Gamma>: "\<Gamma> = fmap_of_list (zip xs \<theta>s) \<uplus> \<Gamma>''"
    by (auto simp: check_imports.simps bind_sum_Ok split: option.splits)
  have red': "(case redeclared id {} xs of None \<Rightarrow> Ok () | Some x \<Rightarrow> Fail (q, DuplicateImportedName x)) = Ok ()"
    by (simp add: red)
  from "4.IH"(1)[OF m prems(2-4)]
  have sm: "stable \<M> (\<lambda>V \<Sigma>. check_module \<M> V \<Sigma> q q') V \<Sigma> \<Delta> \<Sigma>\<^sub>1" and cl\<Delta>: "closed_cxt \<Sigma>\<^sub>1 \<Delta>"
    by (auto dest: stable_check_module_pair)
  note sub1 = stableD(1)[OF sm] and wf1 = stableD(2)[OF sm] and set1 = stableD(3)[OF sm]
  have pre1: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using prems(3) sub1 by (rule fmsubset_trans)
  note sms = "4.IH"(2)[OF m refl ms wf1 pre1 set1]
  note sub2 = stableD(1)[OF sms] and wf2 = stableD(2)[OF sms] and set2 = stableD(3)[OF sms]
  have pre2: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>2" using pre1 sub2 by (rule fmsubset_trans)
  from "4.IH"(3)[OF m refl ms red' ent wf2 pre2 set2 closed_cxt_mono[OF cl\<Delta> sub2]]
  have se: "stable \<M> (\<lambda>V \<Sigma>. imports_entries \<M> V \<Sigma> q q' \<Delta> xs) V \<Sigma>\<^sub>2 \<theta>s \<Sigma>\<^sub>3"
    and cl\<theta>s: "\<forall>\<theta> \<in> set \<theta>s. closed_entry \<Sigma>\<^sub>3 \<theta>"
    by auto
  note sub3 = stableD(1)[OF se] and wf3 = stableD(2)[OF se] and set3 = stableD(3)[OF se]
  have pre3: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>3" using pre2 sub3 by (rule fmsubset_trans)
  from "4.IH"(4)[OF m refl ms red' ent refl rest wf3 pre3 set3]
  have si: "stable \<M> (\<lambda>V \<Sigma>. check_imports \<M> V \<Sigma> q \<iota>s) V \<Sigma>\<^sub>3 \<Gamma>'' \<Sigma>'" and cl\<Gamma>'': "closed_cxt \<Sigma>' \<Gamma>''" by auto
  note sub4 = stableD(1)[OF si] and wf4 = stableD(2)[OF si] and set4 = stableD(3)[OF si]
  have st: "stable \<M> (\<lambda>V \<Sigma>. do {
      (\<Delta>, \<Sigma>\<^sub>1) \<leftarrow> check_module \<M> V \<Sigma> q q';
      \<Sigma>\<^sub>2 \<leftarrow> check_modules \<M> V \<Sigma>\<^sub>1 q (unique_to q' q);
      (\<theta>s, \<Sigma>\<^sub>3) \<leftarrow> imports_entries \<M> V \<Sigma>\<^sub>2 q q' \<Delta> xs;
      (\<Gamma>, \<Sigma>') \<leftarrow> check_imports \<M> V \<Sigma>\<^sub>3 q \<iota>s;
      Ok (fmap_of_list (zip xs \<theta>s) \<uplus> \<Gamma>, \<Sigma>') }) V \<Sigma> \<Gamma> \<Sigma>'"
    unfolding \<Gamma>
    by (rule stable_bind[OF sm], rule stable_bind_table[OF sms], rule stable_bind[OF se], rule stable_bind[OF si])
       (rule stable_return[OF wf4 set4])
  have "closed_cxt \<Sigma>' (fmap_of_list (zip xs \<theta>s))"
    using cl\<theta>s closed_entry_mono[OF _ sub4] by (intro closed_cxt_of_list) blast
  then have "closed_cxt \<Sigma>' \<Gamma>" unfolding \<Gamma> using cl\<Gamma>'' by (rule closed_cxt_extend)
  with st show ?case by (simp add: check_imports.simps red stable_locate_in stable_map_sum)
next
  case (5 \<M> V \<Sigma> q q' \<Gamma>\<^sub>0)
  then show ?case using stable_return[OF "5.prems"(2, 4)] by (simp add: submodules.simps)
next
  case (6 \<M> V \<Sigma> q q' \<Gamma>\<^sub>0 x xs)
  note prems = "6.prems"
  from prems(1) obtain \<Delta> \<Sigma>\<^sub>1 \<Delta>' where m: "check_module \<M> V \<Sigma> q (Qualified q' x) = Ok (\<Delta>, \<Sigma>\<^sub>1)"
    and sub: "submodules \<M> V \<Sigma>\<^sub>1 q (Qualified q' x) \<Delta> xs = Ok (\<Delta>', \<Sigma>')"
    and \<Gamma>: "\<Gamma> = \<Gamma>\<^sub>0 \<uplus> fmupd x (ModChecked (Qualified q' x) \<Delta>') fmempty"
    by (auto simp: submodules.simps bind_sum_Ok)
  from "6.IH"(1)[OF m prems(2-4)]
  have sm: "stable \<M> (\<lambda>V \<Sigma>. check_module \<M> V \<Sigma> q (Qualified q' x)) V \<Sigma> \<Delta> \<Sigma>\<^sub>1" and cl\<Delta>: "closed_cxt \<Sigma>\<^sub>1 \<Delta>"
    by (auto dest: stable_check_module_pair)
  note sub1 = stableD(1)[OF sm] and wf1 = stableD(2)[OF sm] and set1 = stableD(3)[OF sm]
  have pre1: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using prems(3) sub1 by (rule fmsubset_trans)
  from "6.IH"(2)[OF m refl sub wf1 pre1 set1 cl\<Delta>]
  have ss: "stable \<M> (\<lambda>V \<Sigma>. submodules \<M> V \<Sigma> q (Qualified q' x) \<Delta> xs) V \<Sigma>\<^sub>1 \<Delta>' \<Sigma>'" and cl\<Delta>': "closed_cxt \<Sigma>' \<Delta>'"
    by auto
  note sub2 = stableD(1)[OF ss] and wf2 = stableD(2)[OF ss] and set2 = stableD(3)[OF ss]
  have st: "stable \<M> (\<lambda>V \<Sigma>. do {
      (\<Delta>, \<Sigma>\<^sub>1) \<leftarrow> check_module \<M> V \<Sigma> q (Qualified q' x);
      (\<Delta>', \<Sigma>') \<leftarrow> submodules \<M> V \<Sigma>\<^sub>1 q (Qualified q' x) \<Delta> xs;
      Ok (\<Gamma>\<^sub>0 \<uplus> fmupd x (ModChecked (Qualified q' x) \<Delta>') fmempty, \<Sigma>') }) V \<Sigma> \<Gamma> \<Sigma>'"
    unfolding \<Gamma> by (rule stable_bind[OF sm], rule stable_bind[OF ss]) (rule stable_return[OF wf2 set2])
  have "closed_entry \<Sigma>' (ModChecked (Qualified q' x) \<Delta>')" using cl\<Delta>' by simp
  then have "closed_cxt \<Sigma>' \<Gamma>"
    unfolding \<Gamma> using closed_cxt_mono[OF prems(5) fmsubset_trans[OF sub1 sub2]]
    by (intro closed_cxt_extend closed_cxt_single)
  with st show ?case by (simp add: submodules.simps)
next
  case (7 \<M> V \<Sigma> q q' \<Gamma>\<^sub>0 x)
  note prems = "7.prems"
  show ?case
  proof (cases "\<exists>q''. fmlookup \<Gamma>\<^sub>0 x = Some (ModStub q'')")
    case True
    then obtain q'' where look: "fmlookup \<Gamma>\<^sub>0 x = Some (ModStub q'')" by blast
    with prems(1) obtain \<Gamma>' where m: "check_module \<M> V \<Sigma> q q'' = Ok (\<Gamma>', \<Sigma>')"
      and \<theta>: "\<theta> = ModChecked q'' \<Gamma>'"
      by (auto simp: imports_entry.simps bind_sum_Ok)
    from "7.IH"[OF look refl m prems(2-4)]
    have sm: "stable \<M> (\<lambda>V \<Sigma>. check_module \<M> V \<Sigma> q q'') V \<Sigma> \<Gamma>' \<Sigma>'" and cl\<Gamma>': "closed_cxt \<Sigma>' \<Gamma>'"
      by (auto dest: stable_check_module_pair)
    have "stable \<M> (\<lambda>V \<Sigma>. do { (\<Gamma>', \<Sigma>') \<leftarrow> check_module \<M> V \<Sigma> q q''; Ok (ModChecked q'' \<Gamma>', \<Sigma>') }) V \<Sigma> \<theta> \<Sigma>'"
      unfolding \<theta> by (rule stable_bind[OF sm]) (rule stable_return[OF stableD(2, 3)[OF sm]])
    with cl\<Gamma>' show ?thesis by (simp add: imports_entry.simps look \<theta>)
  next
    case False
    with prems(1) have \<theta>: "resolve_name \<Gamma>\<^sub>0 (Simple x) = Some \<theta>" and \<Sigma>': "\<Sigma>' = \<Sigma>"
      by (auto simp: imports_entry.simps split: option.splits cxt_entry.splits)
    have call: "imports_entry \<M> V'' \<Sigma>'' q q' \<Gamma>\<^sub>0 x = Ok (\<theta>, \<Sigma>'')" for V'' \<Sigma>''
      using False \<theta> by (auto simp: imports_entry.simps split: option.splits cxt_entry.splits)
    have "closed_entry \<Sigma> \<theta>"
      using resolve_name_wf[OF prems(5)[THEN conjunct1] \<theta>] resolve_name_TypeVar[OF \<theta>]
        tyvars_empty_entries[OF prems(5)[THEN conjunct2]] \<theta>
      by (auto simp: resolve_name_def split: option.splits cxt_entry.splits)
    with prems(2, 4) show ?thesis unfolding stable_def \<Sigma>' by (simp add: call)
  qed
next
  case (8 \<M> V \<Sigma> q q' \<Gamma>\<^sub>0)
  then show ?case using stable_return[OF "8.prems"(2, 4)] by (simp add: imports_entries.simps)
next
  case (9 \<M> V \<Sigma> q q' \<Gamma>\<^sub>0 x xs)
  note prems = "9.prems"
  from prems(1) obtain \<theta>' \<Sigma>\<^sub>1 \<theta>s' where e: "imports_entry \<M> V \<Sigma> q q' \<Gamma>\<^sub>0 x = Ok (\<theta>', \<Sigma>\<^sub>1)"
    and rest: "imports_entries \<M> V \<Sigma>\<^sub>1 q q' \<Gamma>\<^sub>0 xs = Ok (\<theta>s', \<Sigma>')" and \<theta>s: "\<theta>s = \<theta>' # \<theta>s'"
    by (auto simp: imports_entries.simps bind_sum_Ok)
  from "9.IH"(1)[OF e prems(2-5)]
  have se: "stable \<M> (\<lambda>V \<Sigma>. imports_entry \<M> V \<Sigma> q q' \<Gamma>\<^sub>0 x) V \<Sigma> \<theta>' \<Sigma>\<^sub>1" and cl\<theta>': "closed_entry \<Sigma>\<^sub>1 \<theta>'" by auto
  note sub1 = stableD(1)[OF se] and wf1 = stableD(2)[OF se] and set1 = stableD(3)[OF se]
  have pre1: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using prems(3) sub1 by (rule fmsubset_trans)
  from "9.IH"(2)[OF e refl rest wf1 pre1 set1 closed_cxt_mono[OF prems(5) sub1]]
  have ses: "stable \<M> (\<lambda>V \<Sigma>. imports_entries \<M> V \<Sigma> q q' \<Gamma>\<^sub>0 xs) V \<Sigma>\<^sub>1 \<theta>s' \<Sigma>'"
    and cl\<theta>s': "\<forall>\<theta> \<in> set \<theta>s'. closed_entry \<Sigma>' \<theta>"
    by auto
  have st: "stable \<M> (\<lambda>V \<Sigma>. do {
      (\<theta>, \<Sigma>\<^sub>1) \<leftarrow> imports_entry \<M> V \<Sigma> q q' \<Gamma>\<^sub>0 x;
      (\<theta>s, \<Sigma>') \<leftarrow> imports_entries \<M> V \<Sigma>\<^sub>1 q q' \<Gamma>\<^sub>0 xs;
      Ok (\<theta> # \<theta>s, \<Sigma>') }) V \<Sigma> \<theta>s \<Sigma>'"
    unfolding \<theta>s
    by (rule stable_bind[OF se], rule stable_bind[OF ses]) (rule stable_return[OF stableD(2, 3)[OF ses]])
  with closed_entry_mono[OF cl\<theta>' stableD(1)[OF ses]] cl\<theta>s' show ?case by (simp add: imports_entries.simps \<theta>s)
next
  case (10 \<M> V \<Sigma> q)
  then show ?case using stable_return[OF "10.prems"(2, 4), of "()"] by (simp add: check_modules.simps)
next
  case (11 \<M> V \<Sigma> q q' qs)
  note prems = "11.prems"
  from prems(1) obtain \<Gamma>' \<Sigma>\<^sub>1 where m: "check_module \<M> V \<Sigma> q q' = Ok (\<Gamma>', \<Sigma>\<^sub>1)"
    and rest: "check_modules \<M> V \<Sigma>\<^sub>1 q qs = Ok \<Sigma>'"
    by (auto simp: check_modules.simps bind_sum_Ok)
  from "11.IH"(1)[OF m prems(2-4)]
  have sm: "stable \<M> (\<lambda>V \<Sigma>. check_module \<M> V \<Sigma> q q') V \<Sigma> \<Gamma>' \<Sigma>\<^sub>1" by (auto dest: stable_check_module_pair)
  note sub1 = stableD(1)[OF sm] and wf1 = stableD(2)[OF sm] and set1 = stableD(3)[OF sm]
  have pre1: "predefined_classes \<subseteq>\<^sub>f \<Sigma>\<^sub>1" using prems(3) sub1 by (rule fmsubset_trans)
  note sms = "11.IH"(2)[OF m refl rest wf1 pre1 set1]
  have "stable \<M> (\<lambda>V \<Sigma>. do {
      (\<Gamma>', \<Sigma>\<^sub>1) \<leftarrow> check_module \<M> V \<Sigma> q q';
      map_sum id (Pair ()) (check_modules \<M> V \<Sigma>\<^sub>1 q qs) }) V \<Sigma> () \<Sigma>'"
    by (rule stable_bind[OF sm]) (rule sms)
  then show ?case
    by (simp add: check_modules.simps map_sum_bind[unfolded id_def] id_def split_def
        | simp add: check_modules.simps map_sum_bind split_def)
qed

end
