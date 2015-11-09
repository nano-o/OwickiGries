theory BExp 
imports AExp 
begin

subsection "Boolean Expressions"

datatype bexp = Bc bool | Not bexp | And bexp bexp | Less aexp aexp

text_raw{*\snip{BExpbvaldef}{1}{2}{% *}
fun bval :: "bexp \<Rightarrow> state \<Rightarrow> bool" where
"bval (Bc v) s = v" |
"bval (Not b) s = (\<not> bval b s)" |
"bval (And b1 b2) s = (bval b1 s \<and> bval b2 s)" |
"bval (Less a1 a2) s = (aval a1 s < aval a2 s)"
text_raw{*}%endsnip*}

value "bval (Less (V ''x'') (Plus (N 3) (V ''y'')))
            <''x'' := 3, ''y'' := 1>"


text{* To improve automation: *}

lemma bval_And_if[simp]:
  "bval (And b1 b2) s = (if bval b1 s then bval b2 s else False)"
by(simp)

declare bval.simps(3)[simp del]  --"remove the original eqn"

subsection "Constant Folding"

text{* Optimizing constructors: *}

text_raw{*\snip{BExplessdef}{0}{2}{% *}
fun less :: "aexp \<Rightarrow> aexp \<Rightarrow> bexp" where
"less (N n1) (N n2) = Bc(n1 < n2)" |
"less a1 a2 = Less a1 a2"
text_raw{*}%endsnip*}

lemma [simp]: "bval (less a1 a2) s = (aval a1 s < aval a2 s)"
apply(induction a1 a2 rule: less.induct)
apply simp_all
done

text_raw{*\snip{BExpanddef}{2}{2}{% *}
fun "and" :: "bexp \<Rightarrow> bexp \<Rightarrow> bexp" where
"and (Bc True) b = b" |
"and b (Bc True) = b" |
"and (Bc False) b = Bc False" |
"and b (Bc False) = Bc False" |
"and b1 b2 = And b1 b2"
text_raw{*}%endsnip*}

lemma bval_and[simp]: "bval (and b1 b2) s = (bval b1 s \<and> bval b2 s)"
apply(induction b1 b2 rule: and.induct)
apply simp_all
done

text_raw{*\snip{BExpnotdef}{2}{2}{% *}
fun not :: "bexp \<Rightarrow> bexp" where
"not (Bc True) = Bc False" |
"not (Bc False) = Bc True" |
"not b = Not b"
text_raw{*}%endsnip*}

lemma bval_not[simp]: "bval (not b) s = (\<not> bval b s)"
apply(induction b rule: not.induct)
apply simp_all
done

text{* Now the overall optimizer: *}

text_raw{*\snip{BExpbsimpdef}{0}{2}{% *}
fun bsimp :: "bexp => bexp" where
"bsimp (Bc v) = Bc v" |
"bsimp (Not b) = not(bsimp b)" |
"bsimp (And b1 b2) = and (bsimp b1) (bsimp b2)" |
"bsimp (Less a1 a2) = less (asimp a1) (asimp a2)"
text_raw{*}%endsnip*}

value "bsimp (And (Less (N 0) (N 1)) b)"

value "bsimp (And (Less (N 1) (N 0)) (Bc True))"

theorem bval_bsimp:"bval (bsimp b) s = bval b s"
apply(induction b)
apply simp_all
done

end