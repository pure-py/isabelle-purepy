theory Executable
  imports Typing
begin

lemma base_type_idem [simp]: "base_type (base_type \<sigma>) = base_type \<sigma>"
proof (cases \<sigma>)
  case (TyLiteral l)
  then show ?thesis by (cases l) simp_all
qed simp_all

(* Overloads for operand types \<sigma>\<^sub>1 and \<sigma>\<^sub>2 by rules other than the base-type rule *)
definition binop_table :: "bop \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ((ty \<times> ty) \<times> ty) list"
where
"binop_table op \<sigma>\<^sub>1 \<sigma>\<^sub>2 =
  [((\<sigma>\<^sub>1, \<sigma>\<^sub>2), TyPrim bool).
     op \<in> {BOpEq, BOpNeq}, equality_type \<sigma>\<^sub>1, equality_type \<sigma>\<^sub>2, comparable \<sigma>\<^sub>1 \<sigma>\<^sub>2] @
  [((\<sigma>\<^sub>1, TyList \<tau>), TyPrim bool). TyList \<tau> \<leftarrow> [\<sigma>\<^sub>2], op \<in> {BOpIn, BOpNotIn}, comparable \<sigma>\<^sub>1 \<tau>] @
  [((\<sigma>\<^sub>1, TyTuple \<tau>s), TyPrim bool).
     TyTuple \<tau>s \<leftarrow> [\<sigma>\<^sub>2], op \<in> {BOpIn, BOpNotIn}, comparable \<sigma>\<^sub>1 (joins \<tau>s)] @
  [((TyPrim str, TyPrim str), TyPrim bool).
     op \<in> {BOpIn, BOpNotIn}, \<sigma>\<^sub>1 <: TyPrim str, \<sigma>\<^sub>2 <: TyPrim str] @
  [((TyPrim str, TyDict \<tau>), TyPrim bool). TyDict \<tau> \<leftarrow> [\<sigma>\<^sub>2], op \<in> {BOpIn, BOpNotIn}, \<sigma>\<^sub>1 <: TyPrim str] @
  [((TyPrim float, TyPrim float), TyPrim bool).
     op \<in> {BOpLt, BOpLeq, BOpGt, BOpGeq}, \<sigma>\<^sub>1 <: TyPrim float, \<sigma>\<^sub>2 <: TyPrim float] @
  [((TyPrim str, TyPrim str), TyPrim bool).
     op \<in> {BOpLt, BOpLeq, BOpGt, BOpGeq}, \<sigma>\<^sub>1 <: TyPrim str, \<sigma>\<^sub>2 <: TyPrim str] @
  [((TyPrim int, TyPrim int), TyPrim int).
     op \<in> {BOpAdd, BOpSub, BOpMul, BOpFloorDiv, BOpMod}, \<sigma>\<^sub>1 <: TyPrim int, \<sigma>\<^sub>2 <: TyPrim int] @
  [((TyPrim float, TyPrim float), TyPrim float).
     op \<in> {BOpAdd, BOpSub, BOpMul, BOpFloorDiv, BOpMod, BOpDiv, BOpPow}, \<sigma>\<^sub>1 <: TyPrim float, \<sigma>\<^sub>2 <: TyPrim float] @
  [((TyPrim str, TyPrim str), TyPrim str). op = BOpAdd, \<sigma>\<^sub>1 <: TyPrim str, \<sigma>\<^sub>2 <: TyPrim str] @
  [((TyList \<sigma>, TyList \<tau>), TyList (\<sigma> \<squnion> \<tau>)). (TyList \<sigma>, TyList \<tau>) \<leftarrow> [(\<sigma>\<^sub>1, \<sigma>\<^sub>2)], op = BOpAdd] @
  [((TyTuple \<sigma>s, TyTuple \<tau>s), TyTuple (\<sigma>s @ \<tau>s)). (TyTuple \<sigma>s, TyTuple \<tau>s) \<leftarrow> [(\<sigma>\<^sub>1, \<sigma>\<^sub>2)], op = BOpAdd] @
  [((TyPrim str, TyPrim int), TyPrim str). op = BOpMul, \<sigma>\<^sub>1 <: TyPrim str, \<sigma>\<^sub>2 <: TyPrim int] @
  [((TyPrim int, TyPrim str), TyPrim str). op = BOpMul, \<sigma>\<^sub>1 <: TyPrim int, \<sigma>\<^sub>2 <: TyPrim str] @
  [((TyList \<tau>, TyPrim int), TyList \<tau>). TyList \<tau> \<leftarrow> [\<sigma>\<^sub>1], op = BOpMul, \<sigma>\<^sub>2 <: TyPrim int] @
  [((TyPrim int, TyList \<tau>), TyList \<tau>). TyList \<tau> \<leftarrow> [\<sigma>\<^sub>2], op = BOpMul, \<sigma>\<^sub>1 <: TyPrim int] @
  [((TyPrim int, TyLiteral (LitInt n)), TyPrim int).
     TyLiteral (LitInt n) \<leftarrow> [\<sigma>\<^sub>2], op = BOpPow, \<sigma>\<^sub>1 <: TyPrim int, n \<ge> 0] @
  [((TyPrim int, TyLiteral (LitInt n)), TyPrim float).
     TyLiteral (LitInt n) \<leftarrow> [\<sigma>\<^sub>2], op = BOpPow, \<sigma>\<^sub>1 <: TyPrim int, n < 0]"

lemma binop_table_overload: "b \<in> set (binop_table op \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<Longrightarrow> binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b"
  by (auto simp: binop_table_def split: ty.splits lit.splits if_splits intro: binop_overload.intros)

lemma binop_overload_table:
  "binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b \<Longrightarrow> b \<in> set (binop_table op \<sigma>\<^sub>1 \<sigma>\<^sub>2 @ binop_table op (base_type \<sigma>\<^sub>1) (base_type \<sigma>\<^sub>2))"
proof (induction rule: binop_overload.induct)
  case OverloadBase
  then show ?case by simp
qed (auto simp: binop_table_def)

lemma binop_overload_iff:
  "binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b \<longleftrightarrow> b \<in> set (binop_table op \<sigma>\<^sub>1 \<sigma>\<^sub>2 @ binop_table op (base_type \<sigma>\<^sub>1) (base_type \<sigma>\<^sub>2))"
proof
  show "binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b \<Longrightarrow>
        b \<in> set (binop_table op \<sigma>\<^sub>1 \<sigma>\<^sub>2 @ binop_table op (base_type \<sigma>\<^sub>1) (base_type \<sigma>\<^sub>2))"
    by (rule binop_overload_table)
  show "b \<in> set (binop_table op \<sigma>\<^sub>1 \<sigma>\<^sub>2 @ binop_table op (base_type \<sigma>\<^sub>1) (base_type \<sigma>\<^sub>2)) \<Longrightarrow>
        binop_overload op \<sigma>\<^sub>1 \<sigma>\<^sub>2 b"
    using binop_table_overload[of b op \<sigma>\<^sub>1 \<sigma>\<^sub>2] binop_table_overload[of b op "base_type \<sigma>\<^sub>1" "base_type \<sigma>\<^sub>2"]
      OverloadBase[of op \<sigma>\<^sub>1 \<sigma>\<^sub>2 "fst (fst b)" "snd (fst b)" "snd b"]
    by auto
qed

(* Overloads for operand type \<sigma> by rules other than the base-type rule *)
definition unop_table :: "uop \<Rightarrow> ty \<Rightarrow> (ty \<times> ty) list"
where
"unop_table op \<sigma> =
  [(TyPrim bool, TyPrim bool). op = UOpNot, \<sigma> <: TyPrim bool] @
  [(TyPrim int, TyPrim int). op \<in> {UOpPos, UOpNeg}, \<sigma> <: TyPrim int] @
  [(TyPrim float, TyPrim float). op \<in> {UOpPos, UOpNeg}, \<sigma> <: TyPrim float]"

lemma unop_table_overload: "b \<in> set (unop_table op \<sigma>) \<Longrightarrow> unop_overload op \<sigma> b"
  by (auto simp: unop_table_def split: if_splits intro: unop_overload.intros)

lemma unop_overload_table: "unop_overload op \<sigma> b \<Longrightarrow> b \<in> set (unop_table op \<sigma> @ unop_table op (base_type \<sigma>))"
proof (induction rule: unop_overload.induct)
  case UnopOverloadBase
  then show ?case by simp
qed (auto simp: unop_table_def)

lemma unop_overload_iff: "unop_overload op \<sigma> b \<longleftrightarrow> b \<in> set (unop_table op \<sigma> @ unop_table op (base_type \<sigma>))"
proof
  show "unop_overload op \<sigma> b \<Longrightarrow> b \<in> set (unop_table op \<sigma> @ unop_table op (base_type \<sigma>))"
    by (rule unop_overload_table)
  show "b \<in> set (unop_table op \<sigma> @ unop_table op (base_type \<sigma>)) \<Longrightarrow> unop_overload op \<sigma> b"
    using unop_table_overload[of b op \<sigma>] unop_table_overload[of b op "base_type \<sigma>"]
      UnopOverloadBase[of op \<sigma> "fst b" "snd b"]
    by auto
qed

lemma unique_remdups_filter:
  assumes "\<And>x. P x \<Longrightarrow> x \<in> set xs"
  shows "(if \<exists>!x. P x then Some (f (THE x. P x)) else None) =
         (case remdups (filter P xs) of [x] \<Rightarrow> Some (f x) | _ \<Rightarrow> None)"
proof -
  have P: "set (remdups (filter P xs)) = {x. P x}"
    using assms by auto
  show ?thesis
  proof (cases "remdups (filter P xs)" rule: remdups_adj.cases)
    case 1
    with P show ?thesis by auto
  next
    case (2 x)
    with P have "P = (\<lambda>y. y = x)" by (auto simp: fun_eq_iff)
    with 2 show ?thesis by simp
  next
    case (3 x y ys)
    with P have "P x" "P y" "x \<noteq> y"
      using distinct_remdups[of "filter P xs"] by (auto simp del: distinct_remdups)
    with 3 show ?thesis by auto
  qed
qed

lemma resolve_binop_code [code]:
  "resolve_binop op \<sigma>\<^sub>1 \<sigma>\<^sub>2 =
    (let bs = binop_table op \<sigma>\<^sub>1 \<sigma>\<^sub>2 @ binop_table op (base_type \<sigma>\<^sub>1) (base_type \<sigma>\<^sub>2) in
     case remdups (filter (\<lambda>b. \<forall>b' \<in> set bs. fst (fst b) <: fst (fst b') \<and> snd (fst b) <: snd (fst b')) bs) of
       [b] \<Rightarrow> Some (snd b)
     | _ \<Rightarrow> None)"
proof -
  let ?bs = "binop_table op \<sigma>\<^sub>1 \<sigma>\<^sub>2 @ binop_table op (base_type \<sigma>\<^sub>1) (base_type \<sigma>\<^sub>2)"
  have "resolve_binop op \<sigma>\<^sub>1 \<sigma>\<^sub>2 =
        (case remdups (filter (binop_most_specific op \<sigma>\<^sub>1 \<sigma>\<^sub>2) ?bs) of [b] \<Rightarrow> Some (snd b) | _ \<Rightarrow> None)"
    unfolding resolve_binop_def by (rule unique_remdups_filter) (simp add: binop_most_specific_def binop_overload_iff)
  moreover have "filter (binop_most_specific op \<sigma>\<^sub>1 \<sigma>\<^sub>2) ?bs =
        filter (\<lambda>b. \<forall>b' \<in> set ?bs. fst (fst b) <: fst (fst b') \<and> snd (fst b) <: snd (fst b')) ?bs"
    by (rule filter_cong) (simp_all add: binop_most_specific_def binop_overload_iff Ball_def)
  ultimately show ?thesis by (simp add: Let_def)
qed

lemma resolve_unop_code [code]:
  "resolve_unop op \<sigma> =
    (let bs = unop_table op \<sigma> @ unop_table op (base_type \<sigma>) in
     case remdups (filter (\<lambda>b. \<forall>b' \<in> set bs. fst b <: fst b') bs) of [b] \<Rightarrow> Some (snd b) | _ \<Rightarrow> None)"
proof -
  let ?bs = "unop_table op \<sigma> @ unop_table op (base_type \<sigma>)"
  have "resolve_unop op \<sigma> = (case remdups (filter (unop_most_specific op \<sigma>) ?bs) of [b] \<Rightarrow> Some (snd b) | _ \<Rightarrow> None)"
    unfolding resolve_unop_def by (rule unique_remdups_filter) (simp add: unop_most_specific_def unop_overload_iff)
  moreover have "filter (unop_most_specific op \<sigma>) ?bs = filter (\<lambda>b. \<forall>b' \<in> set ?bs. fst b <: fst b') ?bs"
    by (rule filter_cong) (simp_all add: unop_most_specific_def unop_overload_iff Ball_def)
  ultimately show ?thesis by (simp add: Let_def)
qed

code_pred subty .

end
