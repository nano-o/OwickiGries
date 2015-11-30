theory VCG
imports Proof_Par
begin

text{* Verification condition for the traditional definition: *}

fun pre_tr :: "com \<Rightarrow> assn \<Rightarrow> assn" where
"pre_tr (Basic f) Q = (\<lambda>s. Q (f s))" |
"pre_tr (c1;; c2) Q = pre_tr c1 (pre_tr c2 Q)" |
"pre_tr (IF b THEN c1 ELSE c2 FI) Q = (\<lambda>s. if bval b s then pre_tr c1 Q s else pre_tr c2 Q s)"|
"pre_tr (WHILE b INV I DO C OD) Q = I"|
"pre_tr (WAIT b END) Q = Q"

fun vc_tr :: "com \<Rightarrow> assn \<Rightarrow> bool" where
"vc_tr (Basic f) Q = True" |
"vc_tr (c1;; c2) Q = ((vc_tr c1 (pre_tr c2 Q)) \<and> (vc_tr c2 Q))" |
"vc_tr (IF b THEN c1 ELSE c2 FI) Q = (vc_tr c1 Q \<and> vc_tr c2 Q)" |
"vc_tr (WHILE b INV I DO c OD) Q =
  ((\<forall>s. (I s \<and> bval b s \<longrightarrow> pre_tr c I s) \<and> (I s \<and> \<not> bval b s \<longrightarrow> Q s)) \<and> vc_tr c I)"|
"vc_tr (WAIT b END) Q = True"

text {* Soundness: *}

lemma vc_sound_tr: "vc_tr c Q \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {pre_tr c Q} c {Q}"
proof(induction c arbitrary: Q)
  case (Basic f Q) thus ?case by simp
next
  case (Seq c1 c2 Q) thus ?case by auto 
next
  case (Cond b c1 c2 Q) 
    thus ?case by (smt conseq hoare_tr.If pre_tr.simps(3) vc_tr.simps(3)) 
next
  case (While b I C Q)
  hence pre:"\<forall>s. (I s \<and> bval b s \<longrightarrow> pre_tr C I s)" and 
  post:"\<forall>s. (I s \<and> \<not> bval b s \<longrightarrow> Q s)" and vc:"vc_tr C I" by simp_all
  hence "\<turnstile>\<^sub>t\<^sub>r {pre_tr C I} C {I}" using While.IH by blast
  hence "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. I s \<and> bval b s} C {I}" using conseq pre by auto
  thus ?case by (simp add: post) 
next
  case (Wait b Q)  thus ?case by simp
qed

corollary vc_sound_tr':
  "\<lbrakk>vc_tr C Q; \<forall>s. P s \<longrightarrow> pre_tr C Q s\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P} C {Q}"
using conseq vc_sound_tr by blast


text{* Completeness: *}

lemma pre_mono_tr:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> pre_tr C P s \<Longrightarrow> pre_tr C P' s"
proof (induction C arbitrary: P P' s)
  case Seq thus ?case by simp metis
qed simp_all

lemma vc_mono_tr:
  "\<forall>s. Q s \<longrightarrow> Q' s \<Longrightarrow> vc_tr C Q \<Longrightarrow> vc_tr C Q'"
proof(induction C arbitrary: Q Q')
  case (Seq C1 C2 Q Q')
  thus ?case by (metis pre_mono_tr vc_tr.simps(2)) 
qed simp_all

(*lemma vc_complete_par:
 "\<turnstile>\<^sub>t\<^sub>r {P} C {Q} \<Longrightarrow> vc_tr C Q \<and> (\<forall>s. P s \<longrightarrow> pre_tr C Q s)"
  (is "_ \<Longrightarrow> ?G P C Q")
proof (induction rule: hoare_tr.induct)
  case (Basic P Q f)
  show ?case (is "?C C") by (simp add: Basic.hyps) 
next
  case (Seq P C1 Q C2 R)
  hence ih1: "?G P C1 Q" by blast
  hence ih2: "?G Q C2 R" using Seq.IH(2) by blast 
  show ?case (is "?C C") using ih1 ih2 pre_mono_tr vc_mono_tr by auto
next
  case conseq thus ?case using vc_mono_tr pre_mono_tr by auto
next
  case (If P b C1 Q C2)
  hence ih1: "?G (\<lambda>s. P s \<and> bval b s) C1 Q" by blast
  hence ih2: "?G (\<lambda>s. P s \<and> \<not>bval b s) C2 Q" by (simp add: If.IH(2)) 
  show ?case by (simp add: ih1 ih2) 
next
  case (While P I b C Q)
  hence ih: "?G (\<lambda>s. I s \<and> bval b s) C I" by blast
  thus ?case by (simp add: While.hyps(1) While.hyps(3)) 
next
  case (Wait P b Q)
  hence "\<forall>s. P s \<longrightarrow> Q s"
  thus ?case
qed*)


text{* Verification condition: *}

fun vc :: "acom \<Rightarrow> assn \<Rightarrow> bool" where
"vc (ABasic P f) Q = (\<forall>s. P s \<longrightarrow> Q (f s))" |
"vc (C1;; C2) Q = ((vc C1 (pre C2)) \<and> (vc C2 Q))" |
"vc ({P} IF b THEN C1 ELSE C2 FI) Q = (vc C1 Q \<and> vc C2 Q \<and> (\<forall>s. P s \<and> bval b s \<longrightarrow> pre C1 s) \<and> (\<forall>s. P s \<and> \<not>bval b s \<longrightarrow> pre C2 s))" |
"vc ({P} WHILE b INV I DO C OD) Q =
  ((\<forall>s. (P s \<longrightarrow> I s) \<and> (I s \<and> bval b s \<longrightarrow> pre C s) \<and> (I s \<and> \<not> bval b s \<longrightarrow> Q s)) \<and> vc C I)"|
"vc ({P} WAIT b END) Q = (\<forall>s. P s \<and> bval b s \<longrightarrow> Q s)"

text {* Soundness: *}

lemma vc_sound: "vc C Q \<Longrightarrow> \<turnstile> C {Q}"
proof(induction C arbitrary: Q)
  case (ABasic P f Q) thus ?case by simp
next
  case (AWhile P b I C Q)
  thus ?case by (simp add: AWhile.IH)
next
  case (ASeq C1 C2 Q) thus ?case by simp
next
  case (AWait P b Q) thus ?case by fastforce
next
  case (ACond P b C1 C2 Q) 
  thus ?case by (simp add: ACond.IH(1) ACond.IH(2)) 
qed

corollary vc_sound':
  "\<lbrakk>vc C Q; \<forall>s. P s \<longrightarrow> pre C s\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>t\<^sub>r {P} strip C {Q}"
using tr_eq_new vc_sound by auto



text{* Completeness: *}

lemma vc_mono:
  "\<forall>s. Q s \<longrightarrow> Q' s \<Longrightarrow> vc C Q \<Longrightarrow> vc C Q'"
proof(induction C arbitrary: Q Q')
  case ASeq thus ?case by auto 
qed simp_all

lemma vc_complete:
 "\<turnstile>\<^sub>t\<^sub>r {P} c {Q} \<Longrightarrow> \<exists>C. strip C = c \<and> vc C Q \<and> (\<forall>s. P s \<longrightarrow> pre C s)"
  (is "_ \<Longrightarrow> \<exists>C. ?G P c Q C")
proof (induction rule: hoare_tr.induct)
  case (Basic P Q f)
  show ?case (is "\<exists>C. ?C C") by (metis Basic.hyps pre.simps(1) strip.simps(1) vc.simps(1))
next
  case (Seq P c1 Q c2 R)
  from Seq.IH obtain C1 where ih1: "?G P c1 Q C1" by blast
  from Seq.IH obtain C2 where ih2: "?G Q c2 R C2" by blast
  show ?case (is "\<exists>C. ?C C")
    by (metis `\<And>thesis. (\<And>C1. strip C1 = c1 \<and> vc C1 Q \<and> (\<forall>s. P s \<longrightarrow> pre C1 s) \<Longrightarrow> thesis) \<Longrightarrow> thesis` `\<And>thesis. (\<And>C2. strip C2 = c2 \<and> vc C2 R \<and> (\<forall>s. Q s \<longrightarrow> pre C2 s) \<Longrightarrow> thesis) \<Longrightarrow> thesis` pre.simps(2) strip.simps(2) vc.simps(2) vc_mono)
next
  case (Wait P b Q)
    thus ?case by (metis pre.simps(5) strip.simps(5) vc.simps(5))
next
  case conseq thus ?case using vc_mono by auto 
next
  case (If P b c1 Q c2)
  from If.IH obtain C1 where ih1: "?G (\<lambda>s. P s \<and> bval b s) c1 Q C1" by blast
  from If.IH obtain C2 where ih2: "?G (\<lambda>s. P s \<and> \<not>bval b s) c2 Q C2" by blast
  from ih1 ih2 obtain C where ih:"C = {P} IF b THEN C1 ELSE C2 FI" by simp
  hence "\<forall>s. P s \<longrightarrow> pre C s" by simp
  hence vc:"vc C Q" by (simp add: ih ih1 ih2)
  show ?case by (metis vc ih ih1 ih2 pre.simps(3) strip.simps(3)) 
next
  case (While P I b c Q)
  from While.IH obtain C where ih: "?G (\<lambda>s. I s \<and> bval b s) c I C" by blast
  from ih obtain CW where 1:"CW = {P} WHILE b INV I DO C OD" by simp
  hence 2:"\<forall>s. P s \<longrightarrow> pre CW s" by simp
  hence 3:"vc CW Q" by (simp add: 1 While.hyps(1) While.hyps(3) ih)
  thus ?case by (metis 1 ih pre.simps(4) strip.simps(4))
qed

text{* Verification condition for Parallel Program: *}

fun pre_par :: "par_com \<Rightarrow> assn \<Rightarrow> assn" where
"pre_par (Parallel Ts) Q = (\<lambda>s. \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s)" |
"pre_par (ParBasic f) Q = (\<lambda>s. Q (f s))" |
"pre_par (C1,, C2) Q = pre_par C1 (pre_par C2 Q)" |
"pre_par (IF b THEN C1 ELSE C2 FI) Q = (\<lambda>s. if bval b s then pre_par C1 Q s else pre_par C2 Q s)"|
"pre_par (WHILE b INV I DO C OD) Q = I"

fun vc_par :: "par_com \<Rightarrow> assn \<Rightarrow> bool" where
"vc_par (Parallel Ts) Q = ((\<forall>i \<in> Index Ts. \<exists>(c::acom) Q. (Ts!i) = (Some c, Q) \<and> (\<turnstile> c {Q})) 
    \<and> INTERFREE Ts \<and> (\<forall>t. (\<lambda>s. \<forall>i \<in> Index Ts. (post (Ts!i)) s) t \<longrightarrow> Q t))" |
"vc_par (ParBasic f) Q = True" |
"vc_par (C1,, C2) Q = ((vc_par C1 (pre_par C2 Q)) \<and> (vc_par C2 Q))" |
"vc_par (IF b THEN C1 ELSE C2 FI) Q = (vc_par C1 Q \<and> vc_par C2 Q)" |
"vc_par (WHILE b INV I DO C OD) Q =
  ((\<forall>s. (I s \<and> bval b s \<longrightarrow> pre_par C I s) \<and> (I s \<and> \<not> bval b s \<longrightarrow> Q s)) \<and> vc_par C I)"

text {* Soundness: *}

lemma vc_sound_par: "vc_par C Q \<Longrightarrow> \<turnstile>\<^sub>P {pre_par C Q} C {Q}"
proof(induction C arbitrary: Q)
  case (ParBasic f Q) thus ?case by simp
next
  case (ParSeq C1 C2 Q) thus ?case by auto 
next
  case (ParCond b C1 C2 Q) 
    thus ?case by (smt ParConseq hoare_par.ParCond pre_par.simps(4) vc_par.simps(4)) 
next
  case (ParWhile b I C Q)
  hence pre:"\<forall>s. (I s \<and> bval b s \<longrightarrow> pre_par C I s)" and 
  post:"\<forall>s. (I s \<and> \<not> bval b s \<longrightarrow> Q s)" and vc:"vc_par C I" by simp_all
  hence "\<turnstile>\<^sub>P {pre_par C I} C {I}" using ParWhile.IH by blast
  hence "\<turnstile>\<^sub>P {\<lambda>s. I s \<and> bval b s} C {I}" using ParConseq pre by auto
  thus ?case by (simp add: post) 
next
  case (Parallel Ts Q)
    assume 0:"vc_par (Parallel Ts) Q"
    hence 1:"(\<forall>i \<in> Index Ts. \<exists>(c::acom) Q. (Ts!i) = (Some c, Q) \<and> (\<turnstile> c {Q}))" using vc_par.simps(1) by blast
    hence 2:"INTERFREE Ts" using 0 INTERFREE_def vc_par.simps(1) by blast
    hence 3:"(\<forall>t. (\<lambda>s. \<forall>i \<in> Index Ts. (post (Ts!i)) s) t \<longrightarrow> Q t)" using Parallel.prems vc_par.simps(1) by blast
    hence "(\<turnstile>\<^sub>P {\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s} (Parallel Ts)
        {\<lambda>s . \<forall>i \<in> Index Ts. (post (Ts!i)) s})" using 1 2 by blast
    hence "(\<turnstile>\<^sub>P {pre_par (Parallel Ts) Q} (Parallel Ts) {\<lambda>s . \<forall>i \<in> Index Ts. (post (Ts!i)) s})" by simp 
    thus ?case using 3 ParConseq by (metis (mono_tags, lifting))
qed

corollary vc_sound_par':
  "\<lbrakk>vc_par C Q; \<forall>s. P s \<longrightarrow> pre_par C Q s\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>P {P} C {Q}"
using ParConseq vc_sound_par by blast


text{* Completeness: *}

lemma pre_mono:
  "\<forall>s. P s \<longrightarrow> P' s \<Longrightarrow> pre_par C P s \<Longrightarrow> pre_par C P' s"
proof (induction C arbitrary: P P' s)
  case ParSeq thus ?case by simp metis
qed simp_all

lemma vc_mono_par:
  "\<forall>s. Q s \<longrightarrow> Q' s \<Longrightarrow> vc_par C Q \<Longrightarrow> vc_par C Q'"
proof(induction C arbitrary: Q Q')
  case (ParSeq C1 C2 Q Q')
  thus ?case by (metis pre_mono vc_par.simps(3)) 
qed simp_all

lemma vc_complete_par:
 "\<turnstile>\<^sub>P {P} C {Q} \<Longrightarrow> vc_par C Q \<and> (\<forall>s. P s \<longrightarrow> pre_par C Q s)"
  (is "_ \<Longrightarrow> ?G P C Q")
proof (induction rule: hoare_par.induct)
  case (ParBasic P Q f)
  show ?case (is "?C C") by (simp add: ParBasic.hyps) 
next
  case (ParSeq P C1 Q C2 R)
  hence ih1: "?G P C1 Q" by blast
  hence ih2: "?G Q C2 R" using ParSeq.IH(2) by blast 
  show ?case (is "?C C") using ih1 ih2 pre_mono vc_mono_par by auto
next
  case ParConseq thus ?case using vc_mono_par pre_mono by auto
next
  case (ParCond P b C1 Q C2)
  hence ih1: "?G (\<lambda>s. P s \<and> bval b s) C1 Q" by blast
  hence ih2: "?G (\<lambda>s. P s \<and> \<not>bval b s) C2 Q" by (simp add: ParCond.IH(2)) 
  show ?case by (simp add: ih1 ih2) 
next
  case (ParWhile P I b C Q)
  hence ih: "?G (\<lambda>s. I s \<and> bval b s) C I" by blast
  thus ?case by (simp add: ParWhile.hyps(1) ParWhile.hyps(3)) 
next
  case (Parallel Ts)
  thus ?case by simp
qed

end