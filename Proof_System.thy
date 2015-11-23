theory Proof_System
imports Par_Com
begin

section {* Definition of the proof rules *}

definition
hoare_valid :: "acom \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> (_)/ {(1_)}" 50) where
"\<Turnstile> c {Q} \<equiv> (\<forall>s t. ((pre c) s \<and> (Some(c), s) \<rightarrow>* (None, t))  \<longrightarrow>  Q t)"

definition
hoare_valid_tr :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>t\<^sub>r {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>t\<^sub>r {P} c {Q} \<equiv> (\<forall>s t. (P s \<and> (Some(c), s) \<rightarrow>\<^sub>t\<^sub>r* (None, t))  \<longrightarrow>  Q t)"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive
  hoare :: "acom \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ((_)/ {(1_)})" 50)
where
Assign: "\<lbrakk>\<forall>s. P s \<longrightarrow> Q (s[a/x])\<rbrakk> \<Longrightarrow> \<turnstile> ({P} x ::= a) {Q}"  |

Seq: "\<lbrakk> \<turnstile> c0 {pre(c1)}; \<turnstile> c1 {Q} \<rbrakk> \<Longrightarrow> \<turnstile> (c0;; c1) {Q}"  |

If: "\<lbrakk> \<turnstile> c1 {Q}; \<forall>s. P s \<and> bval b s \<longrightarrow> pre c1 s; 
      \<turnstile> c2 {Q}; \<forall>s. P s \<and> \<not> bval b s \<longrightarrow> pre c2 s\<rbrakk>
    \<Longrightarrow> \<turnstile> ({P} IF b THEN c1 ELSE c2 FI) {Q}"  |

While: "\<lbrakk>\<forall>s. P s \<longrightarrow> I s; \<forall>s. I s \<and> bval b s \<longrightarrow> pre(c) s;
         \<turnstile> c {I}; \<forall>s. I s \<and> \<not>bval b s \<longrightarrow> Q s\<rbrakk> \<Longrightarrow>
        \<turnstile> ({P} WHILE b INV I DO c OD) {Q}"  |

Wait: "\<lbrakk>\<And> s . P s \<and> bval b s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<turnstile> ({P} WAIT b END) {Q}"|

Conseq:"\<lbrakk>\<turnstile> c {Q}; \<forall>s. Q s \<longrightarrow> Q' s\<rbrakk> \<Longrightarrow> \<turnstile> c {Q'}"

lemmas [simp] = hoare.Assign hoare.Seq hoare.If

lemmas [intro!] = hoare.Assign hoare.Seq hoare.If

inductive
  hoare_tr :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>\<^sub>t\<^sub>r ({(1_)}/ (_)/ {(1_)})" 50)
where
Assign:  "\<lbrakk>\<forall>s. P s \<longrightarrow> Q (s[a/x])\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P} x ::= a {Q}"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>t\<^sub>r {P} c1 {Q};  \<turnstile>\<^sub>t\<^sub>r {Q} c2 {R} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P} c1;;c2 {R}"  |

If: "\<lbrakk> \<turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> bval b s} c1 {Q};  \<turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> \<not> bval b s} c2 {Q}\<rbrakk>
    \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P} IF b THEN c1 ELSE c2 FI {Q}"  |

While: "\<lbrakk>\<forall>s. P s \<longrightarrow> I s; \<turnstile>\<^sub>t\<^sub>r {\<lambda>s. I s \<and> bval b s} c {I}; \<forall>s. I s \<and> \<not>bval b s \<longrightarrow> Q s\<rbrakk> \<Longrightarrow>
        \<turnstile>\<^sub>t\<^sub>r {P} WHILE b INV I DO c OD {Q}"  |

Wait:"\<lbrakk>\<forall>s. P s \<and> bval b s \<longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P} (WAIT b END) {Q}"|

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t\<^sub>r {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s\<rbrakk>
        \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P'} c {Q'}"

lemmas [simp] = hoare_tr.Assign hoare_tr.Seq hoare_tr.If

lemmas [intro!] = hoare_tr.Assign hoare_tr.Seq hoare_tr.If

section {* Equivalence of provability in the new and traditional systems *}

lemma new_implies_tr:
  "\<turnstile> C {Q} \<Longrightarrow> \<exists>c. \<turnstile>\<^sub>t\<^sub>r {pre C} c {Q} \<and> strip C = c"
proof(induction rule:hoare.induct)
  case (Assign P a x)
    show ?case by (simp add: Assign.hyps hoare_tr.Assign) 
next
  case (Seq C0 C1 Q)
    show ?case using Seq.IH(1) Seq.IH(2) hoare_tr.Seq by auto
next
  case (If P b C1 Q C2)
    show ?case using If.IH(1) If.IH(2) If.hyps(2) If.hyps(4) conseq hoare_tr.If by auto 
next
  case (Wait P b)
    show ?case by (smt Wait.hyps conseq hoare_tr.Wait pre.simps(5) strip.simps(5))
next
  case (Conseq  c Q Q')
    show ?case using Conseq.IH Conseq.hyps(2) conseq by metis
next
  case (While P I  b C Q)
    assume 0:" \<forall>s. P s \<longrightarrow> I s" and 1:"\<forall>s. I s \<and> bval b s \<longrightarrow> pre C s"
    obtain c where 3:"strip C = c" and 4:"\<turnstile>\<^sub>t\<^sub>r {pre C} c {I}" using While.IH by auto 
    obtain ca where 6:"ca = WHILE b INV I DO c OD" by simp
    have "\<turnstile>\<^sub>t\<^sub>r {pre {P} WHILE b INV I DO C OD} ca {Q}" by (smt 0 1 4 6 While.hyps(4) conseq hoare_tr.While pre.simps(4)) 
    thus ?case using 3 6 strip.simps(4) by blast 
qed

lemma tr_implies_new:"\<turnstile>\<^sub>t\<^sub>r {P} c {Q} \<Longrightarrow> \<exists>C. (strip C = c) \<and> (\<turnstile> C {Q}) \<and> (\<forall>s. P s \<longrightarrow> pre (C) s)"
proof(induction rule:hoare_tr.induct)
  case (Assign P Q a x)
    obtain C::acom where 1:"C = {P} x ::= a" by simp
    with this have "\<turnstile> C {Q}" by (simp add: Assign.hyps)
    thus ?case using 1 by force
next
  case (Seq P c1 Q c2 R)
    show ?case by (metis Conseq Seq.IH(1) Seq.IH(2) hoare.Seq pre.simps(2) strip.simps(2))
next
  case (If P b c1 Q c2)
    obtain C1::acom where 0:"strip C1 = c1" and 1:"\<turnstile> C1 {Q}" and 2:"(\<forall>s. P s \<and> bval b s \<longrightarrow> pre C1 s)" using If.IH(1) by auto
    obtain C2::acom where 3:"strip C2 = c2" and 4:"\<turnstile> C2 {Q}" and 5:"(\<forall>s. P s \<and> \<not> bval b s \<longrightarrow> pre C2 s)" using If.IH(2) by auto
    obtain C::acom where 6:"C = {P} IF b THEN C1 ELSE C2 FI" by simp
    have "\<turnstile> C {Q}" by (simp add:1 2 4 5 6)
    thus ?case using 0 3 6 by force
next
  case (While P I b c Q)
    assume 0:"\<forall>s. P s \<longrightarrow> I s" and 1:"\<forall>s. I s \<and> \<not> bval b s \<longrightarrow> Q s"
    obtain C::acom where 2:"strip C = c" and 3:"\<turnstile> C {I}" and 4:"(\<forall>s. I s \<and> bval b s \<longrightarrow> pre C s)" using While.IH by auto
    obtain CW::acom where 5:"CW = {P} WHILE b INV I DO C OD" by simp
    have "\<turnstile> CW {Q}" by (simp add: 0 1 3 4 5 hoare.While) 
    thus ?case using 2 5 by force 
next
  case (Wait P b Q)
  obtain C where 1:"C = {P} WAIT b END" by simp
  have "\<turnstile> C {Q}" by (simp add: 1 Wait.hyps hoare.Wait)
  thus ?case using 1 by force 
next
  case (conseq P' P c Q Q')
  assume 0:"\<forall>s. P' s \<longrightarrow> P s" and 1:"\<turnstile>\<^sub>t\<^sub>r {P} c {Q}" and 2:"\<forall>s. Q s \<longrightarrow> Q' s"
  obtain C where 3:"strip C = c" and 4:"\<turnstile> C {Q}" and 5:"(\<forall>s. P s \<longrightarrow> pre C s)" using conseq.IH by blast
  have 6:"(\<forall>s. P' s \<longrightarrow> pre C s)" using 0 5 by blast
  have "\<turnstile> C {Q'}" using 2 4 Conseq by blast
  thus ?case using 3 6 by blast
qed

lemma tr_eq_new:"(\<turnstile>\<^sub>t\<^sub>r {P} c {Q}) = (\<exists>C. (strip C = c) \<and> (\<turnstile> C {Q}) \<and> (\<forall>s. P s \<longrightarrow> pre (C) s))"
using new_implies_tr tr_implies_new
by (metis conseq)

section {* Soundness  *}

lemma hoare_sound_tr: "\<turnstile>\<^sub>t\<^sub>r {P} C {Q} \<Longrightarrow> \<Turnstile>\<^sub>t\<^sub>r {P} C {Q}"
proof(induct rule:hoare_tr.induct)
  case (Assign P Q a x) thus ?case using hoare_valid_tr_def small_to_big_tr by blast
next
  case (Seq P c1 Q c2 R) thus ?case by (smt BTSeqE big_to_small_tr hoare_valid_tr_def small_to_big_tr) 
next
  case (If P b c1 Q c2) thus ?case by (smt BTIfE big_to_small_tr hoare_valid_tr_def small_to_big_tr) 
next
  case (Wait P b Q) thus ?case using hoare_valid_tr_def small_to_big_tr by blast
next
  case (conseq P' P c Q Q')
    assume 0:"\<forall>s. P' s \<longrightarrow> P s" and 1:"\<Turnstile>\<^sub>t\<^sub>r {P} c {Q}" and 2:"\<forall>s. Q s \<longrightarrow> Q' s"
    hence 3:"(\<forall>s t. (P s \<and> (Some(c), s) \<rightarrow>\<^sub>t\<^sub>r* (None, t))  \<longrightarrow>  Q t)" by (simp add: hoare_valid_tr_def) 
    hence "(\<forall>s t. (P' s \<and> (Some(c), s) \<rightarrow>\<^sub>t\<^sub>r* (None, t))  \<longrightarrow>  Q' t)" using 0 2 by blast 
    thus ?case by (simp add: hoare_valid_tr_def)
next
  case (While P I b c Q)
  {
    fix s t
    have "(Some WHILE b INV I DO c OD, s) \<Rightarrow>\<^sub>t\<^sub>r t  \<Longrightarrow> I s  \<Longrightarrow>  I t \<and> \<not> bval b t"
    proof(induction "Some WHILE b INV I DO c OD" s t rule: big_step_tr_induct)
      case WhileFalse thus ?case by (simp add: While.hyps(1)) 
    next
      case WhileTrue thus ?case by (metis (no_types, lifting) While.hyps(3) big_to_small_tr hoare_valid_tr_def) 
    qed
  }
  thus ?case by (metis While.hyps(1) While.hyps(4) hoare_valid_tr_def small_to_big_tr) 
qed

lemma hoare_sound: "\<turnstile> C {Q} \<Longrightarrow> \<Turnstile>\<^sub>t\<^sub>r {pre C} strip C {Q}\<Longrightarrow> \<Turnstile> C {Q}" sorry
(* proof(induct arbitrary:C Q rule:hoare.induct)
  case (Assign P Q a x C Q')
    thus ?case by (metis big_equal_tr big_to_small_tr hoare_valid_def hoare_valid_tr_def small_to_big) 
next
  case (Seq c1 c2 Q C Q')
    thus ?case by (metis big_equal_tr big_to_small_tr hoare_valid_def hoare_valid_tr_def small_to_big) 
next
  case (Wait P b Q C Q')
    thus ?case by (metis big_equal_tr big_to_small_tr hoare_valid_def hoare_valid_tr_def small_to_big) 
next
  case (Conseq c Q Q' C R)
    thus ?case by blast 
next
  case (If c1 Q P b c2 C Q')
  {
    fix s t
    have "(Some {P} IF b THEN c1 ELSE c2 FI, s) \<Rightarrow> t \<Longrightarrow> P s \<Longrightarrow> Q t"
    proof(induction "Some {P} IF b THEN c1 ELSE c2 FI" s t rule: big_step_induct)
      case IfFalse thus ?case by (metis If.hyps(2) If.hyps(4) If.hyps(6) big_to_small hoare_sound_tr hoare_valid_def new_implies_tr) 
    next
      case IfTrue thus ?case using If.hyps(1) If.hyps(2) If.hyps(3) big_to_small hoare_sound_tr hoare_valid_def new_implies_tr 
      by metis
    qed
  }
  thus ?case by (simp add: If.hyps(2) If.prems) 
next
  case (While P I b c Q C Q')
  {
    fix s t
    have "(Some {I} WHILE b INV I DO c OD, s) \<Rightarrow> t  \<Longrightarrow> I s  \<Longrightarrow>  I t \<and> \<not> bval b t"
    proof(induction "Some {I} WHILE b INV I DO c OD" s t rule: big_step_induct)
      case WhileFalse thus ?case by (simp add: While.hyps(1)) 
    next
      case WhileTrue thus ?case using While.hyps(2,3,5) big_equal_tr big_to_small_tr hoare_sound_tr hoare_valid_tr_def new_implies_tr
      sorry
    qed
  }
  thus ?case using While.hyps(4) While.prems 
qed *)
 
lemma soudness: "\<turnstile> C {Q} \<Longrightarrow> \<Turnstile> C {Q}"
using hoare_sound hoare_sound_tr new_implies_tr
by force

section {* Strong soundness *}

text {* At each step, the state reached satisfies the precondition of the current command. *}

lemma strong_sound_1:
  assumes 1:"(Some c, s) \<rightarrow> (ro, t)" and 2:"pre(c) s" and 3:"\<turnstile> c {Q}" 
  shows "case ro of Some r \<Rightarrow> pre(r) t| None \<Rightarrow> Q t" oops

lemma strong_sound_2:
  assumes "(Some c, s) \<rightarrow> (ro, t)" and "pre(c) s" and "\<turnstile> c {Q}" 
  shows "case ro of Some r \<Rightarrow> \<turnstile> r {Q}| None \<Rightarrow> True" sorry

lemma strong_sound:
  assumes "(Some c, s) \<rightarrow>* (ro, t)" and "pre(c) s" and "\<turnstile> c {Q}" 
  shows "case ro of Some r \<Rightarrow> pre(r) t| None \<Rightarrow> Q t" sorry
(* using assms
proof(induct "(Some c, s)" "(ro, t)" arbitrary:c s rule:star.induct)
  case refl
  thus ?case by auto
next
  case (step y c s)
  assume 0:"(Some c, s) \<rightarrow> y" and  1:"y \<rightarrow>* (ro, t)" and 2:"(\<And>c s. y = (Some c, s) \<Longrightarrow>
    pre c s \<Longrightarrow> \<turnstile> c {Q} \<Longrightarrow> case ro of None \<Rightarrow> Q t | Some r \<Rightarrow> pre r t)" and
      3:" pre c s" and 4:"\<turnstile> c {Q}"
  hence 5:"\<Turnstile> c {Q}" using soudness by blast 
  show "case ro of None \<Rightarrow> Q t | Some r \<Rightarrow> pre r t"
  using 0 1 2 3 4 5
  proof(induct "(Some c, s)" y rule:small_step.induct)
    case (Assign P x a) thus ?case
      by (metis assms hoare_sound hoare_sound_tr hoare_valid_def none_final(1) option.simps(4) new_implies_tr)
  next
    case (IfTrue b P c1 c2)
      have "pre c1 s"
      thus ?case
  next
    case (Seq1 c0 s' c1)
      thus ?case
  { 
    fix s'
    assume 0:"y = (None, s')"
    hence 1:"ro = None \<and> t = s'" using none_final(1) none_final(2) step.hyps(2) by blast
    hence "Q t" using assms(1, 2, 3) hoare_sound hoare_sound_tr hoare_valid_def vc_equal by auto
    hence "case ro of None \<Rightarrow> Q t | Some r \<Rightarrow> pre r t" by (simp add:1)
  }
  moreover
  {
    fix c' s'
    assume 0:"y = (Some c', s')"
    hence "case ro of None \<Rightarrow> Q t | Some r \<Rightarrow> pre r t" *)


end
