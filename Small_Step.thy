theory Small_Step
imports Ann_Com Star
begin

subsection {* Step definitions *}

inductive
  small_step :: "(acom option) * state \<Rightarrow> (acom option) * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(Some({P} x ::= a), s) \<rightarrow> (None, s(x := aval a s))" |

Seq1:   "(Some(c0), s) \<rightarrow> (None, t) \<Longrightarrow> (Some (c0;; c1), s) \<rightarrow> (Some(c1), t)" |
Seq2:   "(Some(c0), s) \<rightarrow> (Some(c2), t) \<Longrightarrow> (Some (c0;; c1), s) \<rightarrow> (Some(c2;; c1), t)" |

IfTrue:  "bval b s \<Longrightarrow> (Some({P} IF b THEN c1 ELSE c2 FI), s) \<rightarrow> (Some(c1), s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (Some({P} IF b THEN c1 ELSE c2 FI), s) \<rightarrow> (Some(c2), s)" |

WhileFalse: "\<not>bval b s \<Longrightarrow> (Some ({P} WHILE b INV I DO c OD), s) \<rightarrow> (None, s)" |
WhileTrue:"\<lbrakk>bval b s; \<forall>s. P s \<longrightarrow> I s; \<forall>s. I s \<and> bval b s \<longrightarrow> pre(c) s\<rbrakk> \<Longrightarrow> (Some({P} WHILE b INV I DO c OD), s) \<rightarrow> (Some(c;; ({I} WHILE b INV I DO c OD)), s)"|
  --{* TODO: remove the preconditions "\<forall>s. P s \<longrightarrow> I s; \<forall>s. I s \<and> bval b s \<longrightarrow> pre(c) s" *}

Wait:"bval b s \<Longrightarrow> (Some({P} WAIT b END), s) \<rightarrow> (None, s)"

inductive
  big_step :: "(acom option) * state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>" 55)
where
BNone: "(None, t) \<Rightarrow> t"|

Assign:  "(Some({P} x ::= a), s) \<Rightarrow> s(x := aval a s)" |

Seq:   "\<lbrakk>(Some(c0), s) \<Rightarrow> t; (Some(c1), t) \<Rightarrow> r\<rbrakk> \<Longrightarrow> (Some (c0;; c1), s) \<Rightarrow> r" |

IfTrue:  "\<lbrakk>bval b s; (Some(c1), s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (Some({P} IF b THEN c1 ELSE c2 FI), s) \<Rightarrow> t" |
IfFalse: "\<lbrakk>\<not>bval b s; (Some(c2), s) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (Some({P} IF b THEN c1 ELSE c2 FI), s) \<Rightarrow> t" |

WhileFalse: "\<not>bval b s \<Longrightarrow> (Some ({P} WHILE b INV I DO c OD), s) \<Rightarrow> s" |
WhileTrue:"\<lbrakk>bval b s; \<forall>s. P s \<longrightarrow> I s; \<forall>s. I s \<and> bval b s \<longrightarrow> pre(c) s; (Some c, s) \<Rightarrow> s1; (Some({I} WHILE b INV I DO c OD), s1) \<Rightarrow> t\<rbrakk> \<Longrightarrow> (Some({P} WHILE b INV I DO c OD), s) \<Rightarrow> t"|
  --{* TODO: remove the preconditions "\<forall>s. P s \<longrightarrow> I s; \<forall>s. I s \<and> bval b s \<longrightarrow> pre(c) s" *}

Wait:"bval b s \<Longrightarrow> (Some({P} WAIT b END), s) \<Rightarrow> s"

code_pred big_step .
lemmas big_step_induct = big_step.induct[split_format(complete)]

abbreviation
  small_steps :: "(acom option) * state \<Rightarrow> (acom option) * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y == star small_step x y"

subsubsection {* Traditional version *}

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
  big_step_tr :: "(com option) * state \<Rightarrow> state \<Rightarrow> bool" (infix "\<Rightarrow>\<^sub>t\<^sub>r" 55)
where
BNone:  "(None, t) \<Rightarrow>\<^sub>t\<^sub>r t"|

Assign:  "(Some(x ::= a), s) \<Rightarrow>\<^sub>t\<^sub>r s(x := aval a s)" |

Seq:   "\<lbrakk>(Some(c0), s) \<Rightarrow>\<^sub>t\<^sub>r t; (Some(c1), t) \<Rightarrow>\<^sub>t\<^sub>r r\<rbrakk> \<Longrightarrow> (Some (c0;; c1), s) \<Rightarrow>\<^sub>t\<^sub>r r" |

IfTrue:  "\<lbrakk>bval b s; (Some(c1), s) \<Rightarrow>\<^sub>t\<^sub>r t\<rbrakk> \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<Rightarrow>\<^sub>t\<^sub>r t" |
IfFalse: "\<lbrakk>\<not>bval b s; (Some(c2), s) \<Rightarrow>\<^sub>t\<^sub>r t\<rbrakk> \<Longrightarrow> (Some(IF b THEN c1 ELSE c2 FI), s) \<Rightarrow>\<^sub>t\<^sub>r t" |

WhileFalse: "\<not>bval b s \<Longrightarrow> (Some (WHILE b INV I DO c OD), s) \<Rightarrow>\<^sub>t\<^sub>r s" |
WhileTrue:"\<lbrakk>bval b s; (Some c, s) \<Rightarrow>\<^sub>t\<^sub>r s1; (Some(WHILE b INV I DO c OD), s1) \<Rightarrow>\<^sub>t\<^sub>r t\<rbrakk> \<Longrightarrow> (Some(WHILE b INV I DO c OD), s) \<Rightarrow>\<^sub>t\<^sub>r t"|

Wait:"bval b s \<Longrightarrow> (Some(WAIT b END), s) \<Rightarrow>\<^sub>t\<^sub>r s"

code_pred big_step_tr.
lemmas big_step_tr_induct = big_step_tr.induct[split_format(complete)]

abbreviation
  small_steps_tr :: "(com option) * state \<Rightarrow> (com option) * state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>t\<^sub>r*" 55)
where "x \<rightarrow>\<^sub>t\<^sub>r* y == star small_step_tr x y"

subsection{* Executability *}

code_pred small_step .

lemmas small_step_induct = small_step.induct[split_format(complete)]

code_pred small_step_tr .

lemmas small_step_tr_induct = small_step_tr.induct[split_format(complete)]

subsection{* Proof automation *}

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


inductive_cases BNoneE[elim!]: "(None, s) \<Rightarrow> t"
inductive_cases BAssignE[elim!]: "(Some {P} x ::= a, s) \<Rightarrow> t"
inductive_cases BSeqE[elim!]: "(Some c1;;c2, s1) \<Rightarrow> t"
inductive_cases BIfE[elim!]: "(Some {P} IF b THEN c1 ELSE c2 FI, s) \<Rightarrow> t"
inductive_cases BWhileE[elim]: "(Some {P} WHILE b INV I DO c OD, s) \<Rightarrow> t"
inductive_cases BWaitE[elim]: "(Some {P} WAIT b END, s) \<Rightarrow> t"

inductive_cases BTNoneE[elim!]: "(None, s) \<Rightarrow>\<^sub>t\<^sub>r t"
inductive_cases BTAssignE[elim!]: "(Some x ::= a, s) \<Rightarrow>\<^sub>t\<^sub>r t"
inductive_cases BTSeqE[elim!]: "(Some c1;;c2, s1) \<Rightarrow>\<^sub>t\<^sub>r t"
inductive_cases BTIfE[elim!]: "(Some IF b THEN c1 ELSE c2 FI, s) \<Rightarrow>\<^sub>t\<^sub>r t"
inductive_cases BTWhileE[elim]: "(Some WHILE b INV I DO c OD, s) \<Rightarrow>\<^sub>t\<^sub>r t"
inductive_cases BTWaitE[elim]: "(Some WAIT b END, s) \<Rightarrow>\<^sub>t\<^sub>r t"

lemma assign_simp:
  "(Some {P} x ::= a, s) \<Rightarrow> s' <-> (s' = s(x := aval a s))"
using big_step.Assign by auto
 

text {* An example combining rule inversion and derivations *}
lemma Seq_assoc:
  "(Some (c1;; c2);; c3, s) \<Rightarrow> s' <-> (Some c1;; (c2;; c3), s) \<Rightarrow> s'"
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

declare small_step_tr.intros[simp,intro]

text{* Rule inversion: *}

inductive_cases AssignTE[elim!]: "(Some(x ::= a), s) \<rightarrow>\<^sub>t\<^sub>r ct"
inductive_cases SeqTE[elim]: "(Some(c1;; c2), s) \<rightarrow>\<^sub>t\<^sub>r ct"
inductive_cases IfTE[elim!]: "(Some(IF b THEN c1 ELSE c2 FI), s) \<rightarrow>\<^sub>t\<^sub>r ct"
inductive_cases WhileTE[elim]: "(Some(WHILE b INV I DO c OD), s) \<rightarrow>\<^sub>t\<^sub>r ct"
inductive_cases WaitTE[elim]: "(Some(WAIT b END), s) \<rightarrow>\<^sub>t\<^sub>r ct"

subsection {* Determinism *}

theorem big_step_determ: "\<lbrakk>(c,s) \<Rightarrow> t; (c,s) \<Rightarrow> u \<rbrakk> \<Longrightarrow> u = t"
  by (induction arbitrary: u rule: big_step.induct) blast+

text{* A simple property: *}
lemma deterministic:
  "cs \<rightarrow> cs' \<Longrightarrow> cs \<rightarrow> cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step.induct)
apply blast+
done

text{* A simple property: *}
lemma tr_deterministic:
  "cs \<rightarrow>\<^sub>t\<^sub>r cs' \<Longrightarrow> cs \<rightarrow>\<^sub>t\<^sub>r cs'' \<Longrightarrow> cs'' = cs'"
apply(induction arbitrary: cs'' rule: small_step_tr.induct)
apply blast+
done

subsection {* Equivalence between the big step semantics and the small step semantics *}

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
proof(induct "(Some c1)" s "None::acom option" t arbitrary:c1 rule: star_induct[where r = small_step])
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
  case (Assign P x a s) thus ?case by blast 
next
  case (Seq c1 s r c2 t)
  assume "(Some c1, s) \<rightarrow>* (None, r)" and "(Some c2, r) \<rightarrow>* (None, t)"
  thus ?case by (rule seq_comp)
next
  case (IfTrue b s c1 t P c2)
  assume "bval b s"
  hence "(Some {P} IF b THEN c1 ELSE c2 FI, s) \<rightarrow> (Some c1, s)"  by simp
  moreover assume "(Some c1, s) \<rightarrow>* (None, t)"
  ultimately 
  show ?case by (metis star.simps)
next
  case (IfFalse b s c2 t P c1)
  assume "\<not>bval b s"
  hence "(Some {P} IF b THEN c1 ELSE c2 FI, s) \<rightarrow> (Some c2, s)" by simp
  moreover assume "(Some c2, s) \<rightarrow>* (None, t)"
  ultimately 
  show ?case by (metis star.simps)
next
  case (WhileFalse b s P I c)
  assume b: "\<not> bval b s"
  show ?case by (simp add: b) 
next
  case (WhileTrue b s P I c s1 t)
  let ?w  = "{I} WHILE b INV I DO c OD"
  let ?if = "c;; {I} WHILE b INV I DO c OD"
  assume w: "(Some ?w, s1) \<rightarrow>* (None, t)"
  assume c: "(Some c, s) \<rightarrow>* (None, s1)"
  assume b: "bval b s"
  have "(Some ?w, s) \<rightarrow> (Some ?if, s)" using WhileTrue.hyps(3) b by blast 
  moreover have "(Some ?if, s) \<rightarrow>* (None, t)" using c seq_comp w by blast 
  ultimately show ?case by (metis WhileTrue.hyps(2) WhileTrue.hyps(3) b small_step.WhileTrue star.step) 
next
  case (Wait b s P)
  thus ?case by blast 
qed

lemma  "cs \<Rightarrow> t \<Longrightarrow> cs \<rightarrow>* (None, t)"
proof (induction rule: big_step.induct)
  case BNone show ?case by simp
next
  case Assign show ?case by blast
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
  case (Assign P x a s t)
  thus ?case using big_step.Assign big_to_small final_det by blast
next
  case (Seq1 c1 s r c2 t)
  thus ?case using big_step.BNone big_step.Seq by blast 
next 
  case (Seq2 c0 s c2 r c1 t)
  thus ?case using big_step.Seq by blast
next
  case (IfTrue b s P c1 c2 t)
  thus ?case by (simp add: big_step.IfTrue)
next
  case (IfFalse b s P c1 c2 t)
  thus ?case by (simp add: big_step.IfFalse)
next
  case (WhileFalse b s P I c t)
  thus ?case using big_step.WhileFalse big_to_small final_det by blast 
next
  case (WhileTrue b s P I c t)
  thus ?case using big_step.WhileTrue by blast 
next
  case (Wait b s P t)
  thus ?case using big_step.Wait big_to_small final_det by blast
qed


lemma small_to_big: "cs \<rightarrow>* (None, t) \<Longrightarrow> cs \<Rightarrow> t"
apply (induction cs "(None::acom option, t)" rule: star.induct)
apply (auto intro: small_big_continue)
apply (simp add: big_step.BNone)
done

theorem big_iff_small:
  "cs \<Rightarrow> t = cs \<rightarrow>* (None, t)"
by(metis big_to_small small_to_big)

subsubsection {* Traditional version *}

lemma none_final_tr:
  assumes "(None, s) \<rightarrow>\<^sub>t\<^sub>r* (c, t)"
  shows "c = None" and "s = t"
proof -
  from assms have "c = None \<and> s = t"
  proof (induction "(None::(com option), s)" "(c, t)" rule:star.induct)
    case (step y)
    from step.hyps(1) have "False"
    by (induct "(None::(com option),s)" y rule:small_step_tr.induct)
    thus ?case by auto
  next
    case refl
    thus ?case by simp
  qed
  thus "c = None" and "s = t" by auto
qed

lemma final_det_tr:
  assumes "(c,s) \<rightarrow>\<^sub>t\<^sub>r* (None,t)"
  and "(c,s) \<rightarrow>\<^sub>t\<^sub>r* (None, t')"
  shows "t = t'"
using assms
proof (induct "(c,s)" "(None::(com option), t)" arbitrary:c s rule:star.induct) 
  case refl thus ?case using none_final_tr(2) by blast 
next
  case step thus ?case using tr_deterministic by (metis (no_types, lifting) case_prodE none_final_tr(2) split_curry star.simps)
qed

lemma star_seq2_tr:
  assumes "(Some c1, s) \<rightarrow>\<^sub>t\<^sub>r* (Some c1', s')"
  shows "(Some(c1;; c2), s) \<rightarrow>\<^sub>t\<^sub>r* (Some(c1';; c2), s')"
using assms
proof(induction "(Some c1)" s "(Some c1')" "s'" arbitrary:c1 rule: star_induct[where r = small_step_tr])
  case refl thus ?case by simp
next
  case (step s con s' t)
  from none_final_tr step.hyps(1,2) obtain c where 1:"con = Some c" by fastforce
  with step.hyps(3) have 2:"(Some c;; c2, s') \<rightarrow>\<^sub>t\<^sub>r* (Some c1';; c2, t)" by blast
  from 1 2 step.hyps(1) show ?case by (meson small_step_tr.Seq2 star.simps)
qed

lemma star_seq_none_tr: 
  assumes "(Some c1, s) \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
  shows "(Some(c1;; c2), s) \<rightarrow>\<^sub>t\<^sub>r* (Some c2, t)"
using assms
proof(induct "(Some c1)" s "None::com option" t arbitrary:c1 rule: star_induct[where r = small_step_tr])
  case (step s y s' t)
  assume 1:"(Some c1, s) \<rightarrow>\<^sub>t\<^sub>r (y, s')" and 2:"(y, s') \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
  {
    assume 3:"y = None"
    have "t = s'" using 2 3 none_final_tr(2) by auto
    hence "(Some(c1;; c2), s) \<rightarrow>\<^sub>t\<^sub>r* (Some c2, t)" using 1 3 by blast
  }
  moreover
  {
    assume "y = Some c" 
    hence "(Some(c1;; c2), s) \<rightarrow>\<^sub>t\<^sub>r* (Some c2, t)" by (metis 1 small_step_tr.Seq2 star.simps step.hyps(3))
  }
  moreover have "(Some(c1;; c2), s) \<rightarrow>\<^sub>t\<^sub>r* (Some c2, t)" by (metis "1" calculation(1) option.exhaust small_step_tr.Seq2 star.step step.hyps(3))  
  thus ?case by blast 
qed

lemma seq_comp_tr:
  "\<lbrakk>(Some c1, s1) \<rightarrow>\<^sub>t\<^sub>r* (None, s2); (Some c2, s2) \<rightarrow>\<^sub>t\<^sub>r* (None, s3)\<rbrakk>
   \<Longrightarrow> (Some (c1;;c2), s1) \<rightarrow>\<^sub>t\<^sub>r* (None, s3)"
by (meson star_seq_none_tr star_trans)

lemma big_to_small_tr:
  "cs \<Rightarrow>\<^sub>t\<^sub>r t \<Longrightarrow> cs \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
proof (induction rule: big_step_tr.induct)
  case (BNone t) thus ?case by simp
next
  case (Assign x a s) thus ?case by blast 
next
  case (Seq c1 s r c2 t)
  assume "(Some c1, s) \<rightarrow>\<^sub>t\<^sub>r* (None, r)" and "(Some c2, r) \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
  thus ?case by (rule seq_comp_tr)
next
  case (IfTrue b s c1 t c2)
  assume "bval b s"
  hence "(Some IF b THEN c1 ELSE c2 FI, s) \<rightarrow>\<^sub>t\<^sub>r (Some c1, s)"  by simp
  moreover assume "(Some c1, s) \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
  ultimately show ?case by (metis star.simps)
next
  case (IfFalse b s c2 t c1)
  assume "\<not>bval b s"
  hence "(Some IF b THEN c1 ELSE c2 FI, s) \<rightarrow>\<^sub>t\<^sub>r (Some c2, s)" by simp
  moreover assume "(Some c2, s) \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
  ultimately show ?case by (metis star.simps)
next
  case (WhileFalse b s I c)
  assume b: "\<not> bval b s"
  show ?case by (simp add: b) 
next
  case (WhileTrue b s c s1 I t)
  let ?w  = "WHILE b INV I DO c OD"
  let ?if = "c;; WHILE b INV I DO c OD"
  assume w: "(Some ?w, s1) \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
  assume c: "(Some c, s) \<rightarrow>\<^sub>t\<^sub>r* (None, s1)"
  assume b: "bval b s"
  have "(Some ?w, s) \<rightarrow>\<^sub>t\<^sub>r (Some ?if, s)" using WhileTrue.hyps(3) b by blast 
  moreover have "(Some ?if, s) \<rightarrow>\<^sub>t\<^sub>r* (None, t)" using c seq_comp_tr w by blast 
  ultimately show ?case by (metis WhileTrue.hyps(2) WhileTrue.hyps(3) b small_step_tr.WhileTrue star.step) 
next
  case (Wait b s) thus ?case by blast 
qed

lemma  "cs \<Rightarrow>\<^sub>t\<^sub>r t \<Longrightarrow> cs \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
proof (induction rule: big_step_tr.induct)
  case BNone show ?case by simp
next
  case Assign show ?case by blast
next
  case Seq thus ?case by (blast intro: seq_comp_tr)
next
  case IfTrue thus ?case by (blast intro: star.step)
next
  case IfFalse thus ?case by (blast intro: star.step)
next
  case WhileFalse thus ?case by simp
next
  case WhileTrue
  thus ?case using big_step_tr.WhileTrue big_to_small_tr by blast
next
  case Wait thus ?case by simp
qed

lemma small_big_continue_tr:
  "cs \<rightarrow>\<^sub>t\<^sub>r cs' \<Longrightarrow> cs' \<Rightarrow>\<^sub>t\<^sub>r t \<Longrightarrow> cs \<Rightarrow>\<^sub>t\<^sub>r t"
proof (induction arbitrary: t rule: small_step_tr.induct)
  case (Assign x a s t)
  thus ?case using big_step_tr.Assign big_to_small_tr final_det_tr by blast
next
  case (Seq1 c1 s r c2 t)
  thus ?case using BNone big_step_tr.Seq by blast
next 
  case (Seq2 c0 s c2 r c1 t)
  thus ?case using big_step_tr.Seq by blast
next
  case (IfTrue b s c1 c2 t)
  thus ?case by (simp add: big_step_tr.IfTrue)
next
  case (IfFalse b s c1 c2 t)
  thus ?case by (simp add: big_step_tr.IfFalse)
next
  case (WhileFalse b s I c t)
  thus ?case using big_step_tr.WhileFalse big_to_small_tr final_det_tr by blast 
next
  case (WhileTrue b s I c t)
  thus ?case using big_step_tr.WhileTrue by blast 
next
  case (Wait b s t)
  thus ?case using big_step_tr.Wait big_to_small_tr final_det_tr by blast
qed


lemma small_to_big_tr: "cs \<rightarrow>\<^sub>t\<^sub>r* (None, t) \<Longrightarrow> cs \<Rightarrow>\<^sub>t\<^sub>r t"
apply (induction cs "(None::com option, t)" rule: star.induct)
apply (auto intro: small_big_continue_tr)
apply (simp add: BNone)
done

theorem big_iff_small_tr:
  "cs \<Rightarrow>\<^sub>t\<^sub>r t = cs \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
by(metis big_to_small_tr small_to_big_tr)

subsection {* Equivalence between the traditional definitions and the new ones *}

lemma big_equal_tr:"(Some C, s) \<Rightarrow> t \<Longrightarrow> (Some (strip C), s) \<Rightarrow>\<^sub>t\<^sub>r t"
proof(induct "(Some C, s)" t arbitrary:C s rule:big_step.induct)
  case (Assign P x a s) 
    thus ?case using big_step_tr.Assign by auto
next
  case (Seq c0 s t c1 r) thus ?case using big_step_tr.Seq by auto
next
  case (IfTrue b s c1 t P c2)
    thus ?case by (simp add: big_step_tr.IfTrue)
next
  case (IfFalse b s c2 t P c1)
    thus ?case by (simp add: big_step_tr.IfFalse)
next
  case (WhileFalse b s P I c)
    thus ?case by (simp add: big_step_tr.WhileFalse)
next
  case (WhileTrue b s P I c s1 t)
    thus ?case using big_step_tr.WhileTrue by auto
next
  case (Wait b s P)
    thus ?case by (simp add: big_step_tr.Wait) 
qed

(*lemma tr_big_equal:"(Some c, s) \<Rightarrow>\<^sub>t\<^sub>r t \<Longrightarrow> \<exists>C. (strip C = c) \<and> (Some C, s) \<Rightarrow> t"
proof(induct "(Some c, s)" t arbitrary:c s rule:big_step_tr.induct)
  case (Assign x a s) 
    thus ?case using big_step.Assign strip.simps(1) by blast 
next
  case (Seq c1 s t c2 r) 
  obtain C1 where 1:"strip C1 = c1" and 2:"(Some C1, s) \<Rightarrow> t" using Seq.hyps(2) by blast
  obtain C2 where 3:"strip C2 = c2" and 4:"(Some C2, t) \<Rightarrow> r" using Seq.hyps(4) by blast
  obtain C where "C = C1;; C2" by simp
  hence "strip C = c1;; c2 \<and> (Some C, s) \<Rightarrow> r" using 1 2 3 4 big_step.Seq by auto
  thus ?case by blast
next
  case (IfTrue b s c1 t c2)
    obtain C1 where 1:"strip C1 = c1 \<and> (Some C1, s) \<Rightarrow> t" using IfTrue.hyps(3) by blast
    obtain C where "strip C = IF b THEN c1 ELSE c2 FI"
    thus ?case by (simp add: big_step.IfTrue)
next
  case (IfFalse b s c2 t P c1)
    thus ?case by (simp add: big_step_tr.IfFalse)
next
  case (WhileFalse b s P I c)
    thus ?case by (simp add: big_step_tr.WhileFalse)
next
  case (WhileTrue b s P I c s1 t)
    thus ?case using big_step_tr.WhileTrue by auto
next
  case (Wait b s P)
    thus ?case by (simp add: big_step_tr.Wait) 
qed*)

end