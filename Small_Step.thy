theory Small_Step
imports Ann_Com Star
begin

inductive
  small_step :: "(acom option) * state \<Rightarrow> (acom option) * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Basic:  "(Some({P} x ::= a), s) \<rightarrow> (None, s(x := aval a s))" |

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

end