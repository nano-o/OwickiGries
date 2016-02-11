theory NHoare
imports NStep
begin

definition
hoare_valid :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile> {P} c {Q} \<equiv> (\<forall>s t. (P s \<and> (Some(c), s) \<rightarrow>* (None, t))  \<longrightarrow>  Q t)"

inductive
  hoare :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ({(1_)}/ (_)/ {(1_)})" 50)
where
Basic:  "\<lbrakk>\<forall>s. P s \<longrightarrow> Q (f s)\<rbrakk> \<Longrightarrow> \<turnstile> {P} (Basic f) {Q}"  |

Seq: "\<lbrakk> \<turnstile> {P} c1 {Q};  \<turnstile> {Q} c2 {R} \<rbrakk> \<Longrightarrow> \<turnstile> {P} c1;;c2 {R}"  |

If: "\<lbrakk> \<turnstile> {\<lambda>s. P s \<and> b s} c1 {Q};  \<turnstile> {\<lambda>s. P s \<and> \<not> b s} c2 {Q}\<rbrakk>
    \<Longrightarrow> \<turnstile> {P} IF b THEN c1 ELSE c2 FI {Q}"  |

While: "\<lbrakk>\<forall>s. P s \<longrightarrow> I s; \<turnstile> {\<lambda>s. I s \<and> b s} c {I}; \<forall>s. I s \<and> \<not>b s \<longrightarrow> Q s\<rbrakk> \<Longrightarrow>
        \<turnstile> {P} WHILE b INV I DO c OD {Q}"  |

Wait:"\<lbrakk>\<forall>s. P s \<and> b s \<longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<turnstile> {P} (WAIT b END) {Q}"|

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile> {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s\<rbrakk>
        \<Longrightarrow> \<turnstile> {P'} c {Q'}"

lemmas [simp] = hoare.Basic hoare.Seq hoare.If hoare.While hoare.Wait

lemmas [intro!] = hoare.Basic hoare.Seq hoare.If hoare.While hoare.Wait

section {* Soundness  *}

lemma hoare_sound: "\<turnstile> {P} C {Q} \<Longrightarrow> \<Turnstile> {P} C {Q}"
proof(induct rule:hoare.induct)
  case (Basic P Q f) thus ?case using hoare_valid_def small_to_big by blast
next
  case (Seq P c1 Q c2 R) thus ?case by (smt BSeqE big_to_small hoare_valid_def small_to_big) 
next
  case (If P b c1 Q c2) thus ?case by (smt BIfE big_to_small hoare_valid_def small_to_big) 
next
  case (Wait P b Q) thus ?case using hoare_valid_def small_to_big by fastforce 
next
  case (conseq P' P c Q Q')
    assume 0:"\<forall>s. P' s \<longrightarrow> P s" and 1:"\<Turnstile> {P} c {Q}" and 2:"\<forall>s. Q s \<longrightarrow> Q' s"
    hence 3:"(\<forall>s t. (P s \<and> (Some(c), s) \<rightarrow>* (None, t))  \<longrightarrow>  Q t)" by (simp add: hoare_valid_def) 
    hence "(\<forall>s t. (P' s \<and> (Some(c), s) \<rightarrow>* (None, t))  \<longrightarrow>  Q' t)" using 0 2 by blast 
    thus ?case by (simp add: hoare_valid_def)
next
  case (While P I b c Q)
  {
    fix s t
    have "(Some WHILE b INV I DO c OD, s) \<Rightarrow> t  \<Longrightarrow> I s  \<Longrightarrow>  I t \<and> \<not> b t"
    proof(induction "Some WHILE b INV I DO c OD" s t rule: big_step_induct)
      case WhileFalse thus ?case by (simp add: While.hyps(1)) 
    next
      case WhileTrue thus ?case by (metis (no_types, lifting) While.hyps(3) big_to_small hoare_valid_def) 
    qed
  }
  thus ?case by (metis While.hyps(1) While.hyps(4) hoare_valid_def small_to_big) 
qed

section {* Strong soundness *}

text {* At each step, the state reached satisfies the precondition of the current command. *}

lemma strong_sound_1:
  assumes 1:"(Some c, s) \<rightarrow> (ro, t)" and 2:"pre(c) s" and 3:"\<turnstile> {P} c {Q}"
  shows "case ro of Some r \<Rightarrow> pre(r) t \<and>  \<turnstile> {P} r {Q}| None \<Rightarrow> Q t"
  using assms(3) assms(1,2)
proof (induct c Q arbitrary: ro t s rule:hoare.induct)
  case (ABasic) thus ?case by auto
next
  case (Seq) thus ?case by (smt hoare.Seq is_none_code(2) is_none_simps(1) option.case_eq_if option.sel pre.simps(2) small_step_cases(3))
next
  case (If) thus ?case by auto
next
  case (While) thus ?case
    using hoare.While by auto
next
  case (Wait) thus ?case by auto
next
  case (Conseq) thus ?case by (metis (no_types, lifting) hoare.Conseq option.case_eq_if)
qed

lemma strong_sound:
  assumes "(Some c, s) \<rightarrow>* (ro, t)" and "pre(c) s" and "\<turnstile> {P} c {Q}" 
  shows "case ro of Some r \<Rightarrow> pre(r) t \<and> \<turnstile> r {Q}| None \<Rightarrow> Q t"
using assms
proof (induct "Some c " s ro t arbitrary: Q c rule:star_induct) 
  case (refl) thus ?case by simp
next
  case (step) thus ?case using strong_sound_1
  by (metis (no_types, lifting) case_optionE none_final(1) none_final(2) option.case_eq_if)
qed

end