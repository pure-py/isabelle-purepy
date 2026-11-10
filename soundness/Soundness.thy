(* Type soundness *)
theory Soundness
  imports TopLevel
begin

context wf_loading
begin

theorem type_soundness:
  assumes "check_module \<M> [] predefined_classes main main = Ok (\<Gamma>, \<Sigma>)" and "eval_program \<A> vs \<kappa>"
  shows "\<kappa> \<notin> {TypeError, AttributeError, NameError, Excluded}"
proof -
  note st = check_module_stable(1)[OF assms(1) wf_class_table_predefined fmsubset_refl settled_predefined, THEN conjunct1]
  have settled: "settled \<M> \<Sigma>" using stableD(3)[OF st] .
  have chk: "check_module \<M> [] \<Sigma> main main = Ok (\<Gamma>, \<Sigma>)" using stableD(5)[OF st fmsubset_refl wf_class_table] by simp
  have main: "loadable main" using check_module_loadable(1)[OF settled chk refl refl refl] .
  have dom: "loads_dom [] [main]" and fresh: "fresh [] (loads [] [main])"
    using loads_list[of "[main]" "[]"] main by auto
  let ?\<eta> = "\<lambda>_. TyPrim int"
  have inst: "wf_inst \<Sigma> ?\<eta>" by (simp add: wf_inst_def)
  have domP: "fmdom \<P> |\<subseteq>| fmdom (\<E> \<A>)" by (auto simp: \<P>_def \<E>_def)
  have loaded: "loaded ?\<eta> (\<E> \<A>)"
    unfolding loaded_def
  proof (intro conjI allI impI domP)
    fix q \<rho>
    assume "fmlookup (\<E> \<A>) q = Some \<rho>"
    from predefined_env[OF this inst] obtain \<Gamma>' where P: "fmlookup \<P> q = Some \<Gamma>'" and env: "?\<eta> \<turnstile> \<rho> : \<Gamma>'"
      and dom: "fmdom \<rho> = fmdom \<Gamma>'"
      by blast
    have "check_module \<M> [] \<Sigma> q q = Ok (\<Gamma>', \<Sigma>)" by (simp add: check_module.simps[of \<M> "[]" \<Sigma> q q] P)
    moreover have "module_env ?\<eta> \<rho> \<Gamma>'"
      using env dom predefined_cxt_closed[OF predefined P] by (intro module_env_full) auto
    ultimately show "\<exists>\<Gamma> V q'. check_module \<M> V \<Sigma> q' q = Ok (\<Gamma>, \<Sigma>) \<and> module_env ?\<eta> \<rho> \<Gamma>" by blast
  qed
  have ord: "ordered (fset (fmdom (\<E> \<A>))) (loads [] [main])"
    using loads_ordered(1)[OF dom] domP by (auto intro: ordered_mono simp: less_eq_fset.rep_eq)
  have mods: "\<forall>q \<in> set (loads [] [main]). q |\<notin>| fmdom \<P> \<and> checked q" using fresh by auto
  from assms(2) show ?thesis
  proof cases
    case EvalProgram
    then show ?thesis by simp
  next
    case EvalProgramAbort
    from mods_sound[OF this loaded settled ord mods] show ?thesis by (cases \<kappa>) auto
  qed
qed

end

end
