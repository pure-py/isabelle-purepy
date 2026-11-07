(* Context entries, class tables, name resolution, predefined modules, programs *)
theory Contexts
  imports Syntax
begin

(* Possibly unassigned entries record whether the variable is declared in a branch, for error messages only *)
datatype cxt_entry =
    Ty ty
  | DU ty
  | PU ty bool
  | Unbound
  | ModStub name
  | ModChecked name "(var, cxt_entry) fmap"
  | TypeAlias "(var, cxt_entry) fmap" name "type_def located list" nat
  | Type name
  | TypeVar
  | Scheme ty_scheme
  | PUScheme ty_scheme bool
  | PredefName

type_synonym cxt = "(var, cxt_entry) fmap"

datatype class_entry = ClassDef cxt name "type_def located list" nat

type_synonym class_table = "(name, class_entry) fmap"

fun fv_scheme :: "ty_scheme \<Rightarrow> var set"
where
"fv_scheme (TyScheme \<alpha>s \<tau>) = fv \<tau> - set \<alpha>s"

fun fv_entry :: "cxt_entry \<Rightarrow> var set"
where
"fv_entry (Ty \<tau>) = fv \<tau>" |
"fv_entry (DU \<tau>) = fv \<tau>" |
"fv_entry (PU \<tau> _) = fv \<tau>" |
"fv_entry (Scheme \<pi>) = fv_scheme \<pi>" |
"fv_entry (PUScheme \<pi> _) = fv_scheme \<pi>" |
"fv_entry _ = {}"

definition tyvars :: "cxt \<Rightarrow> var set"
where
"tyvars \<Gamma> = Set.filter (\<lambda>x. fmlookup \<Gamma> x = Some TypeVar) (fmdom' \<Gamma>) \<union> \<Union> (fv_entry ` fmran' \<Gamma>)"

lemma tyvars_entry: "fmlookup \<Gamma> x = Some \<theta> \<Longrightarrow> fv_entry \<theta> \<subseteq> tyvars \<Gamma>"
  by (force simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff)

lemma tyvars_add: "tyvars (\<Gamma> \<otimes> \<Delta>) \<subseteq> tyvars \<Gamma> \<union> tyvars \<Delta>"
  by (fastforce simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff split: if_splits)

lemma tyvars_single: "\<theta> \<noteq> TypeVar \<Longrightarrow> tyvars (fmupd x \<theta> fmempty) = fv_entry \<theta>"
  by (auto simp: tyvars_def fmlookup_dom'_iff fmlookup_ran'_iff split: if_splits)

fun lookup :: "cxt \<Rightarrow> name \<Rightarrow> cxt_entry option"
where
"lookup \<Gamma> (Simple x) = fmlookup \<Gamma> x" |
"lookup \<Gamma> (Qualified q x) = (case lookup \<Gamma> q of Some (ModChecked _ \<Gamma>') \<Rightarrow> fmlookup \<Gamma>' x | _ \<Rightarrow> None)"

definition resolve_name :: "cxt \<Rightarrow> name \<Rightarrow> cxt_entry option"
where
"resolve_name \<Gamma> q =
  (case lookup \<Gamma> q of
     Some (Ty \<tau>) \<Rightarrow> Some (Ty \<tau>)
   | Some (ModChecked q' \<Gamma>') \<Rightarrow> Some (ModChecked q' \<Gamma>')
   | Some (Type C) \<Rightarrow> Some (Type C)
   | Some (TypeAlias \<Gamma>' q' \<chi>s i) \<Rightarrow> Some (TypeAlias \<Gamma>' q' \<chi>s i)
   | Some (Scheme \<pi>) \<Rightarrow> Some (Scheme \<pi>)
   | Some PredefName \<Rightarrow> Some PredefName
   | _ \<Rightarrow> None)"

lemma resolve_name_TypeVar: "resolve_name \<Gamma> q = Some \<theta> \<Longrightarrow> \<theta> \<noteq> TypeVar"
  by (auto simp: resolve_name_def split: option.splits cxt_entry.splits)

definition range_class :: name where "range_class = name_of [''builtins'', ''range'']"

abbreviation name_binding :: "var \<times> cxt_entry"
where "name_binding \<equiv> (var ''__name__'', Ty (TyPrim str))"

definition \<P> :: "(name, cxt) fmap"
where
"\<P> = fmap_of_list
  [(builtins, fmap_of_list
     ([name_binding,
       (var ''len'', Ty (TyCallable [TyPrim Sized] (TyPrim int))),
       (var ''range'', Type range_class),
       (var ''round'', Ty (TyCallable [TyPrim float] (TyPrim int)))]
      @ map (\<lambda>\<nu>. (prim_name \<nu>, PredefName)) [NoneType, object, bool, int, float, str]
      @ map (\<lambda>x. (var x, PredefName)) [''list'', ''dict'', ''tuple''])),
   (name_of [''sys''], fmap_of_list
     [name_binding, (var ''argv'', Ty (TyList (TyPrim str))),
      (var ''exit'', Ty (TyCallable [TyPrim int] (TyPrim Never)))]),
   (name_of [''typing''], fmap_of_list
     [name_binding, (var ''Callable'', PredefName), (var ''Literal'', PredefName),
      (prim_name Never, PredefName), (prim_name Sized, PredefName)]),
   (name_of [''dataclasses''],
    fmap_of_list [name_binding, (var ''dataclass'', PredefName)])]"

function (sequential) extend_entry :: "cxt_entry \<Rightarrow> cxt_entry \<Rightarrow> cxt_entry"
and extend_cxt :: "cxt \<Rightarrow> cxt \<Rightarrow> cxt"
where
"extend_entry (ModChecked q \<Gamma>) (ModStub q') = (if q = q' then ModChecked q \<Gamma> else ModStub q')" |
"extend_entry (ModChecked q \<Gamma>) (ModChecked q' \<Gamma>') =
   (if q = q' then ModChecked q (extend_cxt \<Gamma> \<Gamma>') else ModChecked q' \<Gamma>')" |
"extend_entry _ \<theta>' = \<theta>'" |
"extend_cxt \<Gamma> \<Gamma>' =
   \<Gamma> ++\<^sub>f fmmap_keys (\<lambda>x \<theta>'. case fmlookup \<Gamma> x of None \<Rightarrow> \<theta>' | Some \<theta> \<Rightarrow> extend_entry \<theta> \<theta>') \<Gamma>'"
by pat_completeness auto

termination
by (relation "measure (\<lambda>p. case p of Inl (\<theta>, _) \<Rightarrow> size \<theta> | Inr (\<Gamma>, _) \<Rightarrow> size_fmap (\<lambda>_. 0) size \<Gamma>)")
   (simp_all add: size_fmap_lookup del: size_fmap_def)

adhoc_overloading extend \<rightleftharpoons> extend_cxt

definition predefined_classes :: class_table
where
"predefined_classes =
  fmupd range_class
    (ClassDef (the (fmlookup \<P> builtins)) builtins
      [At no_pos (Dataclass (var ''range'') [] None
        [(var ''start'', TyExprPrim int), (var ''stop'', TyExprPrim int)])] 0)
    fmempty"

lemma sorted_list_of_fmap_lookup: "(k, v) \<in> set (sorted_list_of_fmap m) \<Longrightarrow> fmlookup m k = Some v"
  unfolding sorted_list_of_fmap_def by (auto simp: fmlookup_dom_iff)

(* Alias definitions reachable from a context, through the contexts of its aliases and checked modules *)
function (sequential) entry_aliases :: "cxt_entry \<Rightarrow> nat" and aliases :: "cxt \<Rightarrow> nat"
where
"entry_aliases (TypeAlias \<Gamma> _ \<chi>s _) =
  length (filter (\<lambda>\<chi>. case node \<chi> of TypeStmt _ _ _ \<Rightarrow> True | _ \<Rightarrow> False) \<chi>s) + aliases \<Gamma>" |
"entry_aliases (ModChecked _ \<Gamma>) = aliases \<Gamma>" |
"entry_aliases _ = 0" |
"aliases \<Gamma> = sum_list (map (entry_aliases \<circ> snd) (sorted_list_of_fmap \<Gamma>))"
by pat_completeness auto

termination
by (relation "measure (\<lambda>p. case p of Inl \<theta> \<Rightarrow> size \<theta> | Inr \<Gamma> \<Rightarrow> size_fmap (\<lambda>_. 0) size \<Gamma>)")
   (auto dest!: sorted_list_of_fmap_lookup simp: size_fmap_lookup simp del: size_fmap_def)

definition entry_of :: "cxt \<Rightarrow> expr \<Rightarrow> cxt_entry option"
where
"entry_of \<Gamma> e = Option.bind (dotted_name e) (resolve_name \<Gamma>)"

lemma resolve_name_lookup: "resolve_name \<Gamma> q = Some \<theta> \<Longrightarrow> lookup \<Gamma> q = Some \<theta>"
  by (auto simp: resolve_name_def split: option.splits cxt_entry.splits)

(* Entry of an attribute name, as a member of the module bound to the name of the object *)
lemma entry_of_attribute:
  assumes "entry_of \<Gamma> (ExprAttribute e x) = Some \<theta>"
  obtains q q' \<Gamma>' where "dotted_name (node e) = Some q" and "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')"
    and "fmlookup \<Gamma>' x = Some \<theta>"
proof -
  from assms obtain q where q: "dotted_name (node e) = Some q" and "lookup \<Gamma> (Qualified q x) = Some \<theta>"
    by (cases "dotted_name (node e)") (auto simp: entry_of_def dest: resolve_name_lookup)
  from this(2) obtain q' \<Gamma>' where "lookup \<Gamma> q = Some (ModChecked q' \<Gamma>')" and "fmlookup \<Gamma>' x = Some \<theta>"
    by (auto split: option.splits cxt_entry.splits)
  with q show thesis by (rule that)
qed

definition class_of_name :: "cxt \<Rightarrow> expr \<Rightarrow> name option"
where
"class_of_name \<Gamma> e = (case entry_of \<Gamma> e of Some (Type C) \<Rightarrow> Some C | _ \<Rightarrow> None)"

definition scheme_of_name :: "cxt \<Rightarrow> expr \<Rightarrow> ty_scheme option"
where
"scheme_of_name \<Gamma> e = (case entry_of \<Gamma> e of Some (Scheme \<pi>) \<Rightarrow> Some \<pi> | _ \<Rightarrow> None)"

type_synonym program = "(name, module_body) fmap"

context includes fmap.lifting
begin
lift_definition submods :: "program \<Rightarrow> name \<Rightarrow> cxt"
  is "\<lambda>\<M> q x. if Qualified q x \<in> dom \<M> then Some (ModStub (Qualified q x)) else None"
proof -
  fix \<M> :: "name \<Rightarrow> module_body option" and q
  let ?S = "\<lambda>x. if Qualified q x \<in> dom \<M> then Some (ModStub (Qualified q x)) else None"
  assume "finite (dom \<M>)"
  have "dom ?S \<subseteq> Qualified q -` dom \<M>" by (auto simp: dom_def)
  moreover have "inj (Qualified q)" by (simp add: inj_def)
  ultimately show "finite (dom ?S)" using \<open>finite (dom \<M>)\<close> by (blast intro: finite_subset finite_vimageI)
qed
end

lemma submods_of_list [code]:
  "submods (fmap_of_list m) q
   = fmap_of_list (map (\<lambda>(q', _). (short_name q', ModStub q'))
                       (filter (\<lambda>(q', _). case q' of Qualified q'' _ \<Rightarrow> q'' = q | Simple _ \<Rightarrow> False) m))"
proof (rule fmap_ext)
  fix x
  let ?l = "map (\<lambda>(q', _). (short_name q', ModStub q'))
              (filter (\<lambda>(q', _). case q' of Qualified q'' _ \<Rightarrow> q'' = q | Simple _ \<Rightarrow> False) m)"
  have "map_of ?l x = (if Qualified q x \<in> dom (map_of m) then Some (ModStub (Qualified q x)) else None)"
    by (induction m) (auto simp: dom_def split: name.splits)
  then show "fmlookup (submods (fmap_of_list m) q) x = fmlookup (fmap_of_list ?l) x"
    by (simp add: submods.rep_eq fmlookup_of_list)
qed

end
