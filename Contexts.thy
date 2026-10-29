(* Context entries, class tables, name resolution, predefined modules, programs *)
theory Contexts
  imports Syntax "HOL-Library.List_Lexorder" "HOL-Library.Char_ord"
begin

datatype cxt_entry =
    Ty ty
  | DU ty
  | PU ty
  | Unbound
  | ModStub name
  | ModChecked name "(var, cxt_entry) fmap"
  | TypeAlias "(var, cxt_entry) fmap" name "type_def list" nat
  | Type name
  | TypeVar
  | Scheme ty_scheme
  | PUScheme ty_scheme
  | PredefName

type_synonym cxt = "(var, cxt_entry) fmap"

datatype class_entry = ClassDef cxt name "type_def list" nat

type_synonym class_table = "(name, class_entry) fmap"

fun lookup :: "cxt \<Rightarrow> name \<Rightarrow> cxt_entry option"
where
"lookup \<Gamma> (x, []) = fmlookup \<Gamma> x" |
"lookup \<Gamma> (x, y # ys) = (case fmlookup \<Gamma> x of Some (ModChecked _ \<Gamma>') \<Rightarrow> lookup \<Gamma>' (y, ys) | _ \<Rightarrow> None)"

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

definition range_class :: name where "range_class = snoc builtins ''range''"

abbreviation name_binding :: "var \<times> cxt_entry" where "name_binding \<equiv> (''__name__'', Ty (TyPrim str))"

definition predefined :: "(name, cxt) fmap"
where
"predefined = fmap_of_list
  [(builtins, fmap_of_list
     ([name_binding,
       (''print'', Ty (TyCallable [TyPrim object] (TyPrim NoneType))),
       (''len'', Ty (TyCallable [TyPrim Sized] (TyPrim int))),
       (''range'', Type range_class),
       (''round'', Ty (TyCallable [TyPrim float] (TyPrim int)))]
      @ map (\<lambda>\<nu>. (prim_name \<nu>, PredefName)) [NoneType, object, bool, int, float, str]
      @ [(''list'', PredefName), (''dict'', PredefName), (''tuple'', PredefName)])),
   ((''sys'', []), fmap_of_list
     [name_binding, (''argv'', Ty (TyList (TyPrim str))),
      (''exit'', Ty (TyCallable [TyPrim int] (TyPrim Never)))]),
   ((''typing'', []), fmap_of_list
     [name_binding, (''Callable'', PredefName), (''Literal'', PredefName),
      (prim_name Never, PredefName), (prim_name Sized, PredefName)]),
   ((''dataclasses'', []), fmap_of_list [name_binding, (''dataclass'', PredefName)])]"

(* Boxed plus of the specification isn't in Isabelle's symbol table *)
function (sequential) extend_entry :: "cxt_entry \<Rightarrow> cxt_entry \<Rightarrow> cxt_entry"
and extend :: "cxt \<Rightarrow> cxt \<Rightarrow> cxt" (infixl "\<uplus>" 65)
where
"extend_entry (ModChecked q \<Gamma>) (ModStub q') = (if q = q' then ModChecked q \<Gamma> else ModStub q')" |
"extend_entry (ModChecked q \<Gamma>) (ModChecked q' \<Gamma>') =
   (if q = q' then ModChecked q (\<Gamma> \<uplus> \<Gamma>') else ModChecked q' \<Gamma>')" |
"extend_entry _ \<theta>' = \<theta>'" |
"\<Gamma> \<uplus> \<Gamma>' =
   \<Gamma> ++\<^sub>f fmmap_keys (\<lambda>x \<theta>'. case fmlookup \<Gamma> x of None \<Rightarrow> \<theta>' | Some \<theta> \<Rightarrow> extend_entry \<theta> \<theta>') \<Gamma>'"
by pat_completeness auto

termination
by (relation "measure (\<lambda>p. case p of Inl (\<theta>, _) \<Rightarrow> size \<theta> | Inr (\<Gamma>, _) \<Rightarrow> size_fmap (\<lambda>_. 0) size \<Gamma>)")
   (simp_all add: size_fmap_lookup del: size_fmap_def)

definition predefined_classes :: class_table
where
"predefined_classes =
  fmupd range_class
    (ClassDef (the (fmlookup predefined builtins)) builtins
      [Dataclass ''range'' [] None [(''start'', TyExprPrim int), (''stop'', TyExprPrim int)]] 0)
    fmempty"

lemma sorted_list_of_fmap_lookup: "(k, v) \<in> set (sorted_list_of_fmap m) \<Longrightarrow> fmlookup m k = Some v"
  unfolding sorted_list_of_fmap_def by (auto simp: fmlookup_dom_iff)

(* Alias definitions reachable from a context, through the contexts of its aliases and checked modules *)
function (sequential) entry_aliases :: "cxt_entry \<Rightarrow> nat" and aliases :: "cxt \<Rightarrow> nat"
where
"entry_aliases (TypeAlias \<Gamma> _ \<chi>s _) =
  length (filter (\<lambda>\<chi>. case \<chi> of TypeStmt _ _ _ \<Rightarrow> True | _ \<Rightarrow> False) \<chi>s) + aliases \<Gamma>" |
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

definition class_of_name :: "cxt \<Rightarrow> expr \<Rightarrow> name option"
where
"class_of_name \<Gamma> e = (case entry_of \<Gamma> e of Some (Type C) \<Rightarrow> Some C | _ \<Rightarrow> None)"

definition scheme_of_name :: "cxt \<Rightarrow> expr \<Rightarrow> ty_scheme option"
where
"scheme_of_name \<Gamma> e = (case entry_of \<Gamma> e of Some (Scheme \<pi>) \<Rightarrow> Some \<pi> | _ \<Rightarrow> None)"


(* Programs, and the stubs of the submodules of a module *)
type_synonym program = "(name, module_body) fmap"

context includes fmap.lifting
begin
lift_definition submods :: "program \<Rightarrow> name \<Rightarrow> cxt"
  is "\<lambda>M q x. if snoc q x \<in> dom M then Some (ModStub (snoc q x)) else None"
proof -
  fix M :: "name \<Rightarrow> module_body option" and q
  let ?S = "\<lambda>x. if snoc q x \<in> dom M then Some (ModStub (snoc q x)) else None"
  assume "finite (dom M)"
  have "dom ?S \<subseteq> (\<lambda>q'. snd (the (unsnoc q'))) ` dom M"
    by (auto simp: dom_def image_iff intro: rev_image_eqI)
  then show "finite (dom ?S)"
    using \<open>finite (dom M)\<close> by (blast intro: finite_subset finite_imageI)
qed
end

lemma submods_of_list [code]:
  "submods (fmap_of_list m) q
   = fmap_of_list (map (\<lambda>(q', _). (snd (the (unsnoc q')), ModStub q'))
                       (filter (\<lambda>(q', _). case unsnoc q' of Some (q'', _) \<Rightarrow> q'' = q | None \<Rightarrow> False) m))"
proof (rule fmap_ext)
  fix x
  let ?l = "map (\<lambda>(q', _). (snd (the (unsnoc q')), ModStub q'))
              (filter (\<lambda>(q', _). case unsnoc q' of Some (q'', _) \<Rightarrow> q'' = q | None \<Rightarrow> False) m)"
  have "map_of ?l x = (if snoc q x \<in> dom (map_of m) then Some (ModStub (snoc q x)) else None)"
    by (induction m) (auto simp: dom_def snoc_eq_iff simp del: snoc.simps unsnoc.simps split: option.splits)
  then show "fmlookup (submods (fmap_of_list m) q) x = fmlookup (fmap_of_list ?l) x"
    by (simp add: submods.rep_eq fmlookup_of_list)
qed

end
