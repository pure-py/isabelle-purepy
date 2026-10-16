theory Util
    imports Main
begin

class partial_monoid =
  fixes one :: "'a" ( "\<one>" )
    and mult :: "'a \<Rightarrow> 'a \<Rightarrow> 'a option" (infixl "\<bullet>" 70)
  assumes left_unit:
    "\<one> \<bullet> x = Some x"
  assumes right_unit:
    "x \<bullet> \<one> = Some x"
  assumes assoc:
    "(case x \<bullet> y of
       None \<Rightarrow> None
     | Some xy \<Rightarrow>
         (case xy \<bullet> z of
            None \<Rightarrow> None
          | Some xyz \<Rightarrow> Some xyz))
     =
     (case y \<bullet> z of
        None \<Rightarrow> None
      | Some yz \<Rightarrow>
          (case x \<bullet> yz of
             None \<Rightarrow> None
           | Some xyz \<Rightarrow> Some xyz))"

end
