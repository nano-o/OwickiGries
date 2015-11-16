theory Small_Step
imports Ann_Com Star
begin

inductive
  small_step :: "(acom option) * state \<Rightarrow> (acom option) * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(Some({P} x ::= a), s) \<rightarrow> (None, s(x := aval a s))" |

Seq1:   "(Some(c0), s) \<rightarrow> (None, t) \<Longrightarrow> (Some (c0;; c1), s) \<rightarrow> (Some(c1), t)" |
Seq2:   "(Some(c0), s) \<rightarrow> (Some(c2), t) \<Longrightarrow> (Some (c0;; c1), s) \<rightarrow> (Some(c2;; c1), t)" |

IfTrue:  "bval b s \<Longrightarrow> (Some({P} IF b THEN c1 ELSE c2 FI), s) \<rightarrow> (Some(c1), s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (Some({P} IF b THEN c1 ELSE c2 FI), s) \<rightarrow> (Some(c2), s)" |

WhileTrue: "\<not>bval b s \<Longrightarrow> (Some ({P} WHILE b INV I DO c OD), s) \<rightarrow> (None, s)" |
WhileFalse:"bval b s \<Longrightarrow> (Some({P} WHILE b INV I DO c OD), s) \<rightarrow> (Some(c;; ({I} WHILE b INV I DO c OD)), s)"|

Wait:"bval b s \<Longrightarrow> (Some({P} WAIT b END), s) \<rightarrow> (None, s)"


abbreviation
  small_steps :: "(acom option) * state \<Rightarrow> (acom option) * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

inductive
  small_step_tr :: "(com option) * state \<Rightarrow> (com option) * state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>t\<^sub>r" 55)
where
Assign:  "(Some(x ::= a), s) \<rightarrow>\<^sub>t\<^sub>r (None, s(x := aval a s))" |

Seq1:   "(Some(c0), s) \<rightarrow>\<^sub>t\<^sub>r (None, t) \<Longrightarrow> (Some (c0;; c1), s) \<rightarrow>\<^sub>t\<^sub>r (Some(c1), t)" |
Seq2:   "(Some(c0), s) \<rightarrow>\<^sub>t\<^sub>r (Some(c2), t) \<Longrightarrow> (Some (c0;; c1), s) \<rightarrow>\<^sub>t\<^sub>r (Some(c2;; c1), t)" |

IfTrue:  "bval b s \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<rightarrow>\<^sub>t\<^sub>r (Some(c1), s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<rightarrow>\<^sub>t\<^sub>r (Some(c2), s)" |

WhileFalse: "\<not>bval b s \<Longrightarrow> (Some (WHILE b INV I DO c OD), s) \<rightarrow>\<^sub>t\<^sub>r (None, s)" |
WhileTrue:"bval b s \<Longrightarrow> (Some(WHILE b INV I DO c OD), s) \<rightarrow>\<^sub>t\<^sub>r (Some(c;; (WHILE b INV I DO c OD)), s)"|

Wait:"bval b s \<Longrightarrow> (Some(WAIT b END), s) \<rightarrow>\<^sub>t\<^sub>r (None, s)"

inductive
  big_step_tr :: "(com option) * state \<Rightarrow> (com option) * state \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>t\<^sub>r" 55)
where
Assign:  "(Some(x ::= a), s) \<Rightarrow>\<^sub>t\<^sub>r (None, s(x := aval a s))" |

Seq:   "\<lbrakk>(Some(c0), s) \<Rightarrow>\<^sub>t\<^sub>r (None, t); (Some(c1), t) \<Rightarrow>\<^sub>t\<^sub>r (None, r)\<rbrakk> \<Longrightarrow> (Some (c0;; c1), s) \<Rightarrow>\<^sub>t\<^sub>r (None, r)" |

IfTrue:  "\<lbrakk>bval b s; (Some(c1), s) \<Rightarrow>\<^sub>t\<^sub>r (None, t)\<rbrakk> \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<Rightarrow>\<^sub>t\<^sub>r (None, t)" |
IfFalse: "\<lbrakk>\<not>bval b s; (Some(c2), s) \<Rightarrow>\<^sub>t\<^sub>r (None, t)\<rbrakk> \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<Rightarrow>\<^sub>t\<^sub>r (None, t)" |

WhileFalse: "\<not>bval b s \<Longrightarrow> (Some (WHILE b INV I DO c OD), s) \<Rightarrow>\<^sub>t\<^sub>r (None, s)" |
WhileTrue:"\<lbrakk>bval b s; (Some c, s) \<Rightarrow>\<^sub>t\<^sub>r (None, s1); (Some(WHILE b INV I DO c OD), s1) \<Rightarrow>\<^sub>t\<^sub>r (None, t)\<rbrakk> \<Longrightarrow> (Some(WHILE b INV I DO c OD), s) \<Rightarrow>\<^sub>t\<^sub>r (None, t)"|

Wait:"bval b s \<Longrightarrow> (Some(WAIT b END), s) \<Rightarrow>\<^sub>t\<^sub>r (None, s)"

abbreviation
  small_steps_tr :: "(com option) * state \<Rightarrow> (com option) * state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>t\<^sub>r*" 55)
where "x \<rightarrow>\<^sub>t\<^sub>r* y == star small_step_tr x y"

subsection{* Executability *}

code_pred small_step .

lemmas small_step_induct = small_step.induct[split_format(complete)]

subsubsection{* Proof automation *}

declare small_step.intros[simp, intro]

text{* Rule inversion: *}

inductive_cases AssignE[elim!]: "(Some({P} x ::= a), s) \<rightarrow> ct"
inductive_cases SeqE[elim]: "(Some(c1;; c2), s) \<rightarrow> ct"
inductive_cases IfE[elim!]: "(Some({P} IF b THEN c1 ELSE c2 FI), s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(Some({P} WHILE b INV I DO c OD), s) \<rightarrow> ct"
inductive_cases WaitE[elim]: "(Some({P} WAIT b END), s) \<rightarrow> ct"

inductive_cases small_step_cases:
    "(None,s) \<rightarrow> (c', s')"
    "(Some ({P} x ::= a),s) \<rightarrow> (c', s')"
    "(Some (c1;; c2), s) \<rightarrow> (c', s')"
    "(Some ({P} IF b THEN c1 ELSE c2 FI), s) \<rightarrow> (c', s')"
    "(Some ({P} WHILE b INV I DO c OD), s) \<rightarrow> (c', s')"
    "(Some ({P} WAIT b END), s) \<rightarrow> (c', s')"


text{* A simple property: *}
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
apply blast+
done

subsection{* Executability *}

code_pred small_step_tr .

lemmas small_step_tr_induct = small_step_tr.induct[split_format(complete)]

subsubsection{* Proof automation *}

declare small_step_tr.intros[simp,intro]

text{* Rule inversion: *}

inductive_cases AssignTE[elim!]: "(Some(x ::= a), s) \<rightarrow>\<^sub>t\<^sub>r ct"
inductive_cases SeqTE[elim]: "(Some(c1;; c2), s) \<rightarrow>\<^sub>t\<^sub>r ct"
inductive_cases IfTE[elim!]: "(Some(IF b THEN c1 ELSE c2 FI), s) \<rightarrow>\<^sub>t\<^sub>r ct"
inductive_cases WhileTE[elim]: "(Some(WHILE b INV I DO c OD), s) \<rightarrow>\<^sub>t\<^sub>r ct"
inductive_cases WaitTE[elim]: "(Some(WAIT b END), s) \<rightarrow>\<^sub>t\<^sub>r ct"


text{* A simple property: *}
lemma tr_deterministic:
  "cs \<rightarrow>\<^sub>t\<^sub>r cs' \<Longrightarrow> cs \<rightarrow>\<^sub>t\<^sub>r cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step_tr.induct)
apply blast+
done

lemma none_final:
  assumes "(None, s) \<rightarrow>* (c, t)"
  shows "c = None" and "s = t"
proof -
  from assms have "c = None \<and> s = t"
  proof (induction "(None::(acom option), s)" "(c, t)" rule:star.induct)
    case (step y)
    from step.hyps(1) have "False"
    by (induct "(None::(acom option),s)" y rule:small_step.induct)
    thus ?case by auto
  next
    case refl
    thus ?case by simp
  qed
  thus "c = None" and "s = t" by auto
qed

lemma final_det:
  assumes "(c,s) \<rightarrow>* (None,t)"
  and "(c,s) \<rightarrow>* (None, t')"
  shows "t = t'"
using assms
proof (induct "(c,s)" "(None::(acom option), t)" arbitrary:c s rule:star.induct) 
  case refl thus ?case by (simp add: none_final(2))  
next
  case step thus ?case using deterministic
    by (metis (no_types, hide_lams) PairE none_final(2) star.simps)
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
proof(induct "(Some c1)" s "None::acom option" t rule: star_induct[where r = small_step])
  case (step s y s' t)
  assume 1:"(Some c1, s) \<rightarrow> (y, s')" and 2:"(y, s') \<rightarrow>* (None, t)"
  have "(Some(c1;; c2), s) \<rightarrow>* (Some c2, t)"
  proof-
  {
    assume 3:"y = None"
    have "t = s'" using 2 3 none_final(2) by auto
  (*using 1
  proof (induct "(Some c1, s)" "(y, s')" rule:small_step.induct)
    case (Assign P x a)
    thus ?case using 2 none_final(2) by blast 
  next
    case (Seq1 c0 c1')
    thus ?case*)

qed

lemma seq_comp:
  "\<lbrakk>(Some c1, s1) \<rightarrow>* (None, s2); (Some c2, s2) \<rightarrow>* (None, s3)\<rbrakk>
   \<Longrightarrow> (Some (c1;;c2), s1) \<rightarrow>* (None, s3)"
by(blast intro: star.step star_seq2 star_trans)

end