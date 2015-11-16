theory Proof_System
imports Par_Com
begin

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

If: "\<lbrakk> \<turnstile> c1 {Q}; \<forall>s. P s \<and> bval b s \<longrightarrow> pre c1 s; \<turnstile> c2 {Q}; \<forall>s. P s \<and> \<not> bval b s \<longrightarrow> pre c2 s\<rbrakk>
    \<Longrightarrow> \<turnstile> ({P} IF b THEN c1 ELSE c2 FI) {Q}"  |

While: "\<lbrakk>\<forall>s. P s \<longrightarrow> I s; \<forall>s. I s \<and> bval b s \<longrightarrow> pre(c) s; \<turnstile> c {I}; \<forall>s. I s \<and> \<not>bval b s \<longrightarrow> Q s\<rbrakk> \<Longrightarrow>
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

While: "\<lbrakk>\<forall>s. P s \<longrightarrow> I s; \<turnstile>\<^sub>t\<^sub>r {\<lambda>s. I s \<and> bval b s} c {I}\<rbrakk> \<Longrightarrow>
        \<turnstile>\<^sub>t\<^sub>r {P} WHILE b INV I DO c OD {\<lambda>s. I s \<and> \<not> bval b s}"  |

Wait:"\<lbrakk>\<forall>s. P s \<and> bval b s \<longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P} (WAIT b END) {Q}"|

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t\<^sub>r {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s\<rbrakk>
        \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P'} c {Q'}"

lemma vc_equal:
  "\<turnstile> C {Q} \<Longrightarrow> \<exists>c. \<turnstile>\<^sub>t\<^sub>r {pre C} c {Q} \<and> strip C = c"
proof(induction rule:hoare.induct)
  case (Assign P a x)
    show ?case by (simp add: Assign.hyps hoare_tr.Assign) 
next
  print_cases
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

lemma vc_complete:"\<turnstile>\<^sub>t\<^sub>r {P} c {Q} \<Longrightarrow> \<exists>C. (strip C = c) \<and> (\<turnstile> C {Q}) \<and> (\<forall>s. P s \<longrightarrow> pre (C) s)"
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
  case (While P I b c)
    assume 1:"\<forall>s. P s \<longrightarrow> I s"
    obtain C::acom where 2:"strip C = c" and 3:"\<turnstile> C {I}" and 4:"(\<forall>s. I s \<and> bval b s \<longrightarrow> pre C s)" using While.IH by auto
    obtain CW::acom where 5:"CW = {P} WHILE b INV I DO C OD" by simp
    have "\<turnstile> CW {\<lambda>a. I a \<and> \<not> bval b a}" by (simp add: 1 3 4 5 hoare.While) 
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



(*lemma tr_hoare_sound:
  "\<turnstile>\<^sub>t\<^sub>r {P} c {Q} \<Longrightarrow> \<Turnstile>\<^sub>t\<^sub>r {P} c {Q}" 
proof (induct rule:hoare_tr.induct)
  case (Assign P a x)
  { fix s
    have "(Some (x ::= a), s) \<rightarrow>\<^sub>t\<^sub>r* (None, s[a/x])" by simp }
  note 1 = this
  { fix s t
    assume 1:"P (s[a/x])" and 2:"(Some (x ::= a), s) \<rightarrow>\<^sub>t\<^sub>r* (None, t)"
    from 2 have "(Some (x ::= a), s) \<rightarrow>\<^sub>t\<^sub>r (None, t)" using none_final 
    have "P t"
  thus ?case apply (auto simp add:hoare_valid_tr_def)*)


(*lemma hoare_sound:
  assumes "\<turnstile> C {Q}"
  shows "\<Turnstile> C {Q}"
using assms
proof(induction rule:hoare.induct)
  case (Assign P Q a x)
    {
      fix s t
      assume 1:"P s" and 2:"(Some({P} x ::= a), s) \<rightarrow>* (None, t)" and 3:"\<forall>s. P s \<longrightarrow> Q (s[a/x])"
      have "t = s(x := aval a s)" using 2 final_det by blast 
      hence "Q t" using 1 Assign.hyps by blast
    }
    thus ?case by (metis Assign.hyps hoare_valid_def pre.simps(1)) 
next
  case (Seq c0 c1 Q)
  assume 1:"\<Turnstile> c0 {pre c1}" and 2:"\<Turnstile> c1 {Q}"
  have 3:"(\<forall>s t. ((pre c0) s \<and> (Some(c0), s) \<rightarrow>* (None, t))  \<longrightarrow>  (pre c1) t)" using 1 by (simp add: hoare_valid_def) 
  have 4:"(\<forall>s t. ((pre c1) s \<and> (Some(c1), s) \<rightarrow>* (None, t))  \<longrightarrow>  Q t)" using 2 by (simp add: hoare_valid_def) 
  have 5:"((pre c0) s \<and> (Some(c0), s) \<rightarrow>* (None, t))  \<longrightarrow>  (pre c1) t" using 3 by blast
  have 5:"((pre c1) t \<and> (Some(c1), t) \<rightarrow>* (None, r))  \<longrightarrow>  Q r" using 4 by blast
  hence "((pre c0) s \<and> (Some(c0;; c1), s) \<rightarrow>* (Some(c1), t))  \<longrightarrow>  (pre c1) t"

(*definition
hoare_valid :: "acom \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> (_)/ {(1_)}" 50) where
"\<Turnstile> c {Q} \<equiv> (\<forall>s t. ((pre c) s \<and> (Some(c), s) \<rightarrow>* (None, t))  \<longrightarrow>  Q t)"*)
qed*)


lemma Strong_Soundness: "\<lbrakk>(Some c, s) \<rightarrow>* (co, t); pre c s; \<turnstile> c {q}\<rbrakk>
\<Longrightarrow> if co = None then q t else pre (the co) t"
apply(force )
done

lemma hoare_sound:
  assumes "\<turnstile> C {Q}"
  shows "\<Turnstile> C {Q}"
apply (unfold hoare_valid_def)
apply clarify
apply(drule Strong_Soundness)
apply simp_all
proof-
  show "\<And>s. pre C s \<Longrightarrow> \<turnstile> C {Q} " using assms by simp 
qed

lemma vc_ssound:"\<lbrakk>(Some c, s) \<rightarrow>* (ro, t); pre(c) s; \<turnstile> c {Q}\<rbrakk> \<Longrightarrow> case ro of Some r \<Rightarrow> pre(r) t| None \<Rightarrow> Q t"
using assms
proof(induction "(Some c, s)" "(ro, t)" rule:star.induct)
  case refl
    thus ?case by auto
next
  case (step y)
  thus ?case
  proof(induct "(Some c, s)" y arbitrary:c s t Q rule:small_step.induct)
    case (Assign P x a s t Q)
    assume 0:"(None, s[a/x]) \<rightarrow>* (ro, t)"
    have "ro = None"
qed


lemma vc_ssound:
  assumes "(Some c, s) \<rightarrow>* (ro, t)" and "pre(c) s" and "\<turnstile> c {Q}" 
  shows "case ro of Some r \<Rightarrow> pre(r) t| None \<Rightarrow> Q t" 
using assms
thm star.induct
proof(induct "(Some c, s)" "(ro, t)" arbitrary:c rule:star.induct)
  case refl
  thus ?case by auto
next
  print_cases
  case (step y)
  { assume 1:"fst y = None"
    from 1 have 2:"ro = None" and 3:"snd y = t" 
      using none_final step.hyps(2) by (metis prod.exhaust_sel)+
    have "Q (snd y)" using step.prems step.hyps(1) (* For this we need the soundness of the hoare rules*)
    oops

fun asubst:: "aexp \<Rightarrow> aexp \<Rightarrow> vname\<Rightarrow> aexp" where  
"asubst (N n) a x  = N n"|
"asubst (V v) a x = (if v = x then a else V v)"|
"asubst (Plus a1 a2) a x = Plus (asubst a1 a x) (asubst a2 a x)"

fun post :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
"post ({P} x ::= a) P = (\<lambda>s. \<exists>y. (s x = aval (asubst a y x) s) \<and> P(s[y/x]))" |
"post (C1;; C2) P = post C2 (post C1 P)" |
"post ({P} IF b THEN C1 ELSE C2 FI) P =
  (\<lambda>s. post C1 (\<lambda>s. P s \<and> bval b s) s \<or> post C2 (\<lambda>s. P s \<and> \<not>bval b s) s)"|
"post ({P} WHILE b INV I DO C OD) P = (\<lambda>s. I s \<and> \<not>bval b s)"|
"post ({P} WAIT b END) P = (\<lambda>s. P s \<and> bval b s)"

fun com::"(acom option \<times> assn) \<Rightarrow> acom option" where
"com (Some c, Q) = (Some c)"|
"com (None, Q) = None"


lemma "\<lbrakk>\<forall>i \<in> Index Ts. \<exists>c Q. Ts!i = (Some c, Q) \<and> \<turnstile> c Q; INTERFREE Ts\<rbrakk>
\<Longrightarrow> \<turnstile>\<^sub>P {\<inter>(\<forall>i \<in> Index Ts. pre(the(com(Ts!i))))} (Parallel Ts) {\<inter>(\<forall>i \<in> Index Ts. post(Ts!i)}"

end