theory Util
    imports Main
begin

lemma is_singleton_unique: "is_singleton {x. P x} \<longleftrightarrow> (\<exists>!x. P x)"
  by (auto simp: is_singleton_def) (metis mem_Collect_eq singletonI singletonD)+

lemma the_elem_unique: "\<exists>!x. P x \<Longrightarrow> the_elem {x. P x} = (THE x. P x)"
  by (metis (mono_tags, lifting) is_singleton_unique is_singleton_the_elem mem_Collect_eq singletonI
      the1_equality)

end
