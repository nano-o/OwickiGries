theory Proof_System
imports Par_Com
begin

definition
hoare_valid :: "acom \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile> (_)/ {(1_)}" 50) where
"\<Turnstile> c {Q} \<equiv> (\<forall>s t. (pre c) s \<and> (Some(c), s) \<rightarrow>* (None, t)  \<longrightarrow>  Q t)"

definition
hoare_valid_tr :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<Turnstile>\<^sub>t\<^sub>r {(1_)}/ (_)/ {(1_)}" 50) where
"\<Turnstile>\<^sub>t\<^sub>r {P} c {Q} \<equiv> (\<forall>s t. P s \<and> (Some(c), s) \<rightarrow>*\<^sub>t\<^sub>r (None, t)  \<longrightarrow>  Q t)"

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] == s(x := aval a s)"

inductive
  hoare :: "acom \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile> ((_)/ {(1_)})" 50)
where
Assign: "\<turnstile> ({\<lambda>s. P(s[a/x])} x ::= a) {P}"  |

Seq: "\<lbrakk> \<turnstile> c0 {pre(c1)}; \<turnstile> c1 {Q} \<rbrakk> \<Longrightarrow> \<turnstile> (c0;; c1) {Q}"  |

If: "\<lbrakk> \<turnstile> c1 {Q}; \<forall>s. P s \<and> bval b s \<longrightarrow> pre c1 s; \<turnstile> c2 {Q}; \<forall>s. P s \<and> \<not> bval b s \<longrightarrow> pre c2 s\<rbrakk>
    \<Longrightarrow> \<turnstile> ({P} IF b THEN c1 ELSE c2 FI) {Q}"  |

While: "\<lbrakk>\<forall>s. P s \<and> bval b s \<longrightarrow> I s; \<turnstile> c {I}\<rbrakk> \<Longrightarrow>
        \<turnstile> ({P} WHILE b INV I DO c OD) {\<lambda>s. I s \<and> \<not>bval b s}"  |

Wait: "\<lbrakk>\<And> s . P s \<and> bval b s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<turnstile> ({P} WAIT b END) {Q}"|

Conseq:"\<lbrakk> \<turnstile> c {Q}; \<forall>s. Q s \<longrightarrow> Q' s\<rbrakk> \<Longrightarrow> \<turnstile> c {Q'}"

lemmas [simp] = hoare.Assign hoare.Seq hoare.If

lemmas [intro!] = hoare.Assign hoare.Seq hoare.If

inductive
  hoare_tr :: "assn \<Rightarrow> com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>\<^sub>t\<^sub>r ({(1_)}/ (_)/ {(1_)})" 50)
where
Assign:  "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. P(s[a/x])} x ::= a {P}"  |

Seq: "\<lbrakk> \<turnstile>\<^sub>t\<^sub>r {P} c1 {Q};  \<turnstile>\<^sub>t\<^sub>r {Q} c2 {R} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P} c1;;c2 {R}"  |

If: "\<lbrakk> \<turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> bval b s} c1 {Q};  \<turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> \<not> bval b s} c2 {Q}\<rbrakk>
    \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P} IF b THEN c1 ELSE c2 FI {Q}"  |

While: "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> bval b s} c {I} \<Longrightarrow>
        \<turnstile>\<^sub>t\<^sub>r {P} WHILE b INV I DO c OD {\<lambda>s. I s \<and> \<not> bval b s}"  |

Wait:"\<turnstile>\<^sub>t\<^sub>r {P} (WAIT b END) {\<lambda>s. P s \<and> bval b s}"|

conseq: "\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>t\<^sub>r {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s\<rbrakk>
        \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P'} c {Q'}"

lemma tr_sound: "\<turnstile>\<^sub>t\<^sub>r {P} c {Q} \<Longrightarrow> \<Turnstile>\<^sub>t\<^sub>r {P} c {Q}"

lemma While':
assumes "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> bval b s} c {I}" and "\<forall>s. I s \<and> \<not> bval b s \<longrightarrow> Q s"
shows "\<turnstile>\<^sub>t\<^sub>r {P} WHILE b INV I DO c OD {Q}"
by (smt assms(1) assms(2) conseq hoare_tr.While)

lemma vc_equal:
  "\<turnstile> C {Q} \<Longrightarrow> \<exists>c. \<turnstile>\<^sub>t\<^sub>r {pre C} c {Q} \<and> strip C = c"
proof(induction rule:hoare.induct)
  case (Assign P a x)
    show ?case by (metis (no_types, lifting) Assign.hyps conseq hoare_tr.Assign strip.simps(1)) 
next
  case (Seq C0 C1 Q)
    show ?case using Seq.IH(1) Seq.IH(2) hoare_tr.Seq by auto
next
  case (If P b C1 Q C2)
    show ?case using If.IH(1) If.IH(2) by blast 
next
  case (While P b I c)
    show ?case 
    proof(simp, rule While')
    have vc: "\<turnstile> c {I}" and IQ: "\<exists>ca. \<turnstile>\<^sub>t\<^sub>r {pre c} ca {I} \<and> strip c = ca" and pre: "\<forall>s. P s \<and> bval b s \<longrightarrow> I s" using While.hyps While.IH by simp_all  
    have "\<turnstile>\<^sub>t\<^sub>r {pre c} strip c {I}" using While.IH by auto 
    with pre and vc and IQ show "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> bval b s} strip c {I}"
    show "\<forall>s. I s \<and> \<not> bval b s \<longrightarrow> I s \<and> \<not> bval b s" by simp
  qed
next
  case (Wait P b)
    show ?case by (simp add: hoare_tr.Wait) 
next
  case (Conseq c Q Q')
    show ?case using Conseq.IH Conseq.hyps(2) conseq by blast 
qed

lemma vc_complete:"\<turnstile>\<^sub>t\<^sub>r {P} c {Q} \<Longrightarrow> \<exists>C. (strip C = c) \<and> (\<turnstile> C {Q}) \<and> (\<forall>s. P s \<longrightarrow> pre (C) s)"
proof(induction rule:hoare_tr.induct)


lemma vc_ssound:"\<lbrakk>\<turnstile> c {Q}; pre(c) s; (Some c, s) \<rightarrow>* (ro, t)\<rbrakk> \<Longrightarrow> case ro of Some r \<Rightarrow> pre(r) t | None \<Rightarrow> Q t"
proof(induction rule:hoare.induct)

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

fun the::"acom option \<Rightarrow> acom" where
"the (Some c) = c"

fun com::"(acom option \<times> assn) \<Rightarrow> acom option" where
"com (Some c, Q) = (Some c)"|
"com (None, Q) = None"


lemma "\<lbrakk>\<forall>i \<in> Index Ts. \<exists>c Q. Ts!i = (Some c, Q) \<and> \<turnstile> c Q; INTERFREE Ts\<rbrakk>
\<Longrightarrow> \<turnstile>\<^sub>P {\<inter>(\<forall>i \<in> Index Ts. pre(the(com(Ts!i))))} (Parallel Ts) {\<inter>(\<forall>i \<in> Index Ts. post(Ts!i)}"

end