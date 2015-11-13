theory Star
imports Main
begin

inductive
  star :: "('a \<Rightarrow> 'a => bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
for r where
refl:  "star r x x" |
step:  "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

thm star.induct

lemma star_induct_2:
  assumes "star r x y"
  and "\<And> x . P x x" 
  and "\<And> x y z . \<lbrakk>star r x y; P x y; r y z\<rbrakk> \<Longrightarrow> P x z"
  shows "P x y"  sorry

hide_fact (open) refl step  --"names too generic"

lemma star_trans:
  "star r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"
proof(induction rule: star.induct)
  case refl thus ?case .
next
  case step thus ?case by (metis star.step)
qed

lemmas star_induct =
  star.induct[of "r:: 'a*'b \<Rightarrow> 'a*'b \<Rightarrow> bool", split_format(complete)]

declare star.refl[simp,intro]

lemma star_step1[simp, intro]: "r x y \<Longrightarrow> star r x y"
by(metis star.refl star.step)

code_pred star .

end