theory NStep
imports Ann_Com Star
begin

subsubsection {* Traditional version *}

inductive
  small_step :: "(com option) * newstate \<Rightarrow> (com option) * newstate \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Basic:  "(Some(Basic f), s) \<rightarrow> (None, f s)" |

Seq1:   "(Some(c0), s) \<rightarrow> (None, t) \<Longrightarrow> (Some (c0;; c1), s) \<rightarrow> (Some(c1), t)" |
Seq2:   "(Some(c0), s) \<rightarrow> (Some(c2), t) \<Longrightarrow> (Some (c0;; c1), s) \<rightarrow> (Some(c2;; c1), t)" |

IfTrue:  "\<forall>s. b s \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<rightarrow> (Some(c1), s)" |
IfFalse: "\<forall>s. \<not>b s \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<rightarrow> (Some(c2), s)" |

WhileFalse: "\<forall>s. \<not>b s \<Longrightarrow> (Some (WHILE b INV I DO c OD), s) \<rightarrow> (None, s)" |
WhileTrue:"\<forall>s. b s \<Longrightarrow> (Some(WHILE b INV I DO c OD), s) \<rightarrow> (Some(c;; (WHILE b INV I DO c OD)), s)"|

Wait:"\<forall>s. b s \<Longrightarrow> (Some(WAIT b END), s) \<rightarrow> (None, s)"

inductive
  big_step :: "(com option) * newstate \<Rightarrow> newstate \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
BNone:  "(None, t) \<Rightarrow> t"|

Basic:  "(Some(Basic f), s) \<Rightarrow> (f s)" |

Seq:   "\<lbrakk>(Some(c0), s) \<Rightarrow> t; (Some(c1), t) \<Rightarrow> r\<rbrakk> \<Longrightarrow> (Some (c0;; c1), s) \<Rightarrow> r" |

IfTrue:  "\<lbrakk>\<forall>s. b s; (Some(c1), s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<Rightarrow> t" |
IfFalse: "\<lbrakk>\<forall>s. \<not>b s; (Some(c2), s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<Rightarrow> t" |

WhileFalse: "\<forall>s. \<not>b s \<Longrightarrow> (Some (WHILE b INV I DO c OD), s) \<Rightarrow> s" |
WhileTrue:"\<lbrakk>\<forall>s. b s; (Some c, s) \<Rightarrow> s1; (Some(WHILE b INV I DO c OD), s1) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (Some(WHILE b INV I DO c OD), s) \<Rightarrow> t"|

Wait:"\<forall>s. b s \<Longrightarrow> (Some(WAIT b END), s) \<Rightarrow> s"

code_pred big_step.
lemmas big_step_induct = big_step.induct[split_format(complete)]

abbreviation
  small_steps :: "(com option) * newstate \<Rightarrow> (com option) * newstate \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

subsection{* Executability *}

code_pred small_step .

lemmas small_step_induct = small_step.induct[split_format(complete)]

subsection{* Proof automation *}

declare small_step.intros[simp, intro]

text{* Rule inversion: *}

inductive_cases BNoneE[elim!]: "(None, s) \<Rightarrow> t"
inductive_cases BBasicE[elim!]: "(Some (Basic f), s) \<Rightarrow> t"
inductive_cases BSeqE[elim!]: "(Some c1;;c2, s1) \<Rightarrow> t"
inductive_cases BIfE[elim!]: "(Some IF b THEN c1 ELSE c2 FI, s) \<Rightarrow> t"
inductive_cases BWhileE[elim]: "(Some WHILE b INV I DO c OD, s) \<Rightarrow> t"
inductive_cases BWaitE[elim]: "(Some WAIT b END, s) \<Rightarrow> t"

lemma assign_simp:
  "(Some (Basic f), s) \<Rightarrow> s' = (s' = (f s))"
using big_step.Basic by auto
 

text {* An example combining rule inversion and derivations *}
lemma Seq_assoc:
  "(Some (c1;; c2);; c3, s) \<Rightarrow> s' = (Some c1;; (c2;; c3), s) \<Rightarrow> s'"
proof
  assume "(Some (c1;; c2);; c3, s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(Some c1, s) \<Rightarrow> s1" and
    c2: "(Some c2, s1) \<Rightarrow> s2" and
    c3: "(Some c3, s2) \<Rightarrow> s'" by auto
  from c2 c3
  have "(Some c2;; c3, s1) \<Rightarrow> s'" using big_step.Seq by auto 
  with c1
  show "(Some c1;; (c2;; c3), s) \<Rightarrow> s'" by (rule big_step.Seq)
next
  assume "(Some c1;; (c2;; c3), s) \<Rightarrow> s'"
  then obtain s1 s2 where
    c1: "(Some c1, s) \<Rightarrow> s1" and
    c2: "(Some c2, s1) \<Rightarrow> s2" and
    c3: "(Some c3, s2) \<Rightarrow> s'" by auto
  from c1 c2
  have "(Some c1;; c2, s) \<Rightarrow> s2" using big_step.Seq by auto   
  with c3
  show "(Some (c1;; c2);; c3, s) \<Rightarrow> s'" using big_step.Seq by auto 
qed

subsubsection{* Proof automation *}

declare small_step.intros[simp,intro]

text{* Rule inversion: *}

inductive_cases BasicTE[elim!]: "(Some(Basic f), s) \<rightarrow> ct"
inductive_cases SeqTE[elim]: "(Some(c1;; c2), s) \<rightarrow> ct"
inductive_cases IfTE[elim!]: "(Some(IF b THEN c1 ELSE c2 FI), s) \<rightarrow> ct"
inductive_cases WhileTE[elim]: "(Some(WHILE b INV I DO c OD), s) \<rightarrow> ct"
inductive_cases WaitTE[elim]: "(Some(WAIT b END), s) \<rightarrow> ct"

subsection {* Determinism *}

thm big_step.induct

theorem big_step_determ: "\<lbrakk>(c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induct  arbitrary: u rule: big_step.induct) blast+

text{* A simple property: *}
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
apply blast+
done

subsection {* Equivalence between the big step semantics and the small step semantics *}

lemma none_final:
  assumes "(None, s) \<rightarrow>* (c, t)"
  shows "c = None" and "s = t"
proof -
  from assms have "c = None \<and> s = t"
  proof (induction "(None::(com option), s)" "(c, t)" rule:star.induct)
    case (step y)
    from step.hyps(1) have "False"
    by (induct "(None::(com option),s)" y rule:small_step.induct)
    thus ?case by auto
  next
    case refl
    thus ?case by simp
  qed
  thus "c = None" and "s = t" by auto
qed

thm star.induct

lemma final_det:
  assumes "(c,s) \<rightarrow>* (None,t)"
  and "(c,s) \<rightarrow>* (None, t')"
  shows "t = t'"
using assms
proof (induct c s "(None::(com option))" t rule:star_induct)
  case refl thus ?case 
using none_final(2) by blast
next
  case step thus ?case using deterministic
by (metis none_final(2) star.cases star.step)
qed

lemma star_seq2:
  assumes "(Some c1, s) \<rightarrow>* (Some c1', s')"
  shows "(Some(c1;; c2), s) \<rightarrow>* (Some(c1';; c2), s')"
using assms
proof(induction "(Some c1)" s "(Some c1')" "s'" arbitrary:c1 rule: star_induct[where r = small_step])
  case refl thus ?case by simp
next
  case (step s con s' t)
  from none_final step.hyps(1,2) obtain c where 1:"con = Some c" by fastforce
  with step.hyps(3) have 2:"(Some c;; c2, s') \<rightarrow>* (Some c1';; c2, t)" by blast
  from 1 2 step.hyps(1) show ?case by (meson small_step.Seq2 star.simps)
qed

lemma star_seq_none: 
  assumes "(Some c1, s) \<rightarrow>* (None, t)"
  shows "(Some(c1;; c2), s) \<rightarrow>* (Some c2, t)"
using assms
proof(induct "(Some c1)" s "None::com option" t arbitrary:c1 rule: star_induct[where r = small_step])
  case (step s y s' t)
  assume 1:"(Some c1, s) \<rightarrow> (y, s')" and 2:"(y, s') \<rightarrow>* (None, t)"
  {
    assume 3:"y = None"
    have "t = s'" using 2 3 none_final(2) by auto
    hence "(Some(c1;; c2), s) \<rightarrow>* (Some c2, t)" using 1 3 by blast
  }
  moreover
  {
    fix c
    assume "y = Some c" 
    hence "(Some(c1;; c2), s) \<rightarrow>* (Some c2, t)" by (metis 1 small_step.Seq2 star.simps step.hyps(3))
  }
  moreover have "(Some(c1;; c2), s) \<rightarrow>* (Some c2, t)" by (metis (full_types) 1 calculation(1) deterministic prod.inject small_step.Seq2 small_step_Pii_PoiE small_step_Pii_PoiI split_option_ex star.step step.hyps(3)) 
  thus ?case by blast 
qed

lemma seq_comp:
  "\<lbrakk>(Some c1, s1) \<rightarrow>* (None, s2); (Some c2, s2) \<rightarrow>* (None, s3)\<rbrakk>
   \<Longrightarrow> (Some (c1;;c2), s1) \<rightarrow>* (None, s3)"
by (meson star_seq_none star_trans)

lemma big_to_small:
  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (None, t)"
proof (induction rule: big_step.induct)
  case (BNone t) thus ?case by simp
next
  case (Basic f s) thus ?case by blast 
next
  case (Seq c1 s r c2 t)
  assume "(Some c1, s) \<rightarrow>* (None, r)" and "(Some c2, r) \<rightarrow>* (None, t)"
  thus ?case by (rule seq_comp)
next
  case (IfTrue b c1 s t c2)
  assume "\<forall>s. b s"
  hence "(Some IF b THEN c1 ELSE c2 FI, s) \<rightarrow> (Some c1, s)"  by simp
  moreover assume "(Some c1, s) \<rightarrow>* (None, t)"
  ultimately 
  show ?case by (metis star.simps)
next
  case (IfFalse b c2 s t c1)
  assume "\<forall>s. \<not>b s"
  hence "(Some IF b THEN c1 ELSE c2 FI, s) \<rightarrow> (Some c2, s)" by simp
  moreover assume "(Some c2, s) \<rightarrow>* (None, t)"
  ultimately 
  show ?case by (metis star.simps)
next
  case (WhileFalse b I c s)
  assume b: "\<forall>s. \<not>b s"
  show ?case by (simp add: b) 
next
  case (WhileTrue b c s s1 I t)
  let ?w  = "WHILE b INV I DO c OD"
  let ?if = "c;; WHILE b INV I DO c OD"
  assume w: "(Some ?w, s1) \<rightarrow>* (None, t)"
  assume c: "(Some c, s) \<rightarrow>* (None, s1)"
  assume b: "\<forall>s. b s"
  have "(Some ?w, s) \<rightarrow> (Some ?if, s)" using WhileTrue.hyps(3) b by blast 
  moreover have "(Some ?if, s) \<rightarrow>* (None, t)" using c seq_comp w by blast 
  ultimately show ?case 
    by (meson b small_step.WhileTrue star.step) 
next
  case (Wait b s)
  thus ?case by blast 
qed

lemma  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (None, t)"
proof (induction rule: big_step.induct)
  case BNone show ?case by simp
next
  case Basic show ?case by blast
next
  case Seq thus ?case by (blast intro: seq_comp)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case by simp
next
  case WhileTrue
  thus ?case using big_step.WhileTrue big_to_small by blast
next
  case Wait thus ?case by simp
qed

lemma small_big_continue:
  "cs \<rightarrow> cs' \<Longrightarrow> cs' \<Rightarrow> t \<Longrightarrow> cs \<Rightarrow> t"
proof (induction arbitrary: t rule: small_step.induct)
  case (Basic f s t)
  thus ?case using big_step.Basic big_to_small final_det by blast
next
  case (Seq1 c1 s r c2 t)
  thus ?case using big_step.BNone big_step.Seq by blast 
next 
  case (Seq2 c0 s c2 r c1 t)
  thus ?case using big_step.Seq by blast
next
  case (IfTrue b c1 c2 s t)
  thus ?case by (simp add: big_step.IfTrue)
next
  case (IfFalse b c1 c2 s t)
  thus ?case by (simp add: big_step.IfFalse)
next
  case (WhileFalse b I c s t)
  thus ?case using big_step.WhileFalse big_to_small final_det by blast 
next
  case (WhileTrue b I c s t)
  thus ?case using big_step.WhileTrue by blast 
next
  case (Wait b s t)
  thus ?case using big_step.Wait big_to_small final_det by blast
qed


lemma small_to_big: "cs \<rightarrow>* (None, t) \<Longrightarrow> cs \<Rightarrow> t"
apply (induction cs "(None::com option, t)" rule: star.induct)
apply (auto intro: small_big_continue)
apply (simp add: big_step.BNone)
done

theorem big_iff_small:
  "cs \<Rightarrow> t = cs \<rightarrow>* (None, t)"
by(metis big_to_small small_to_big)

end