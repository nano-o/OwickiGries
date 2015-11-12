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

declare small_step.intros[simp,intro]

text{* Rule inversion: *}

inductive_cases AssignE[elim!]: "(Some({P} x ::= a), s) \<rightarrow> ct"
inductive_cases SeqE[elim]: "(Some(c1;; c2), s) \<rightarrow> ct"
inductive_cases IfE[elim!]: "(Some({P} IF b THEN c1 ELSE c2 FI), s) \<rightarrow> ct"
inductive_cases WhileE[elim]: "(Some({P} WHILE b INV I DO c OD), s) \<rightarrow> ct"
inductive_cases WaitE[elim]: "(Some({P} WAIT b END), s) \<rightarrow> ct"


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

end