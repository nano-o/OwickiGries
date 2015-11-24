theory Proof_Par
imports Proof_System
begin

section {* Definition of the Owicki and Gries proof rules. *} 

fun asubst:: "aexp \<Rightarrow> aexp \<Rightarrow> vname\<Rightarrow> aexp" where  
"asubst (N n) a x  = N n"|
"asubst (V v) a x = (if v = x then a else V v)"|
"asubst (Plus a1 a2) a x = Plus (asubst a1 a x) (asubst a2 a x)"

fun post :: "(acom option \<times> assn) \<Rightarrow> assn" where
  -- {* Extract the postcondition annotation from a parallel command *}
"post (ap, Q) = Q"

fun com::"(acom option \<times> assn) \<Rightarrow> acom option" where
  -- {* Extracts the command option from a parallel command *}
"com (Some c, Q) = (Some c)"|
"com (None, Q) = None"

fun assertions::"acom \<Rightarrow> assn set" where
"assertions ({P} x ::= a) = {P}"|
"assertions (C1;; C2) = (assertions C1) \<union> (assertions C2)"|
"assertions ({P} IF b THEN C1 ELSE C2 FI) = {P} \<union> (assertions C1) \<union> (assertions C2)"|
"assertions ({P} WHILE b INV I DO C OD) = {P} \<union> {I} \<union> (assertions C)"|
"assertions ({P} WAIT b END) = {P}"

fun atomics::"acom \<Rightarrow> (assn \<times> com) set" where
"atomics ({P} x ::= a) = {(P, x ::= a)}"|
"atomics (C1;; C2) = (atomics C1) \<union> (atomics C2)"|
"atomics ({P} IF b THEN C1 ELSE C2 FI) = (atomics C1) \<union> (atomics C2)"|
"atomics ({P} WHILE b INV I DO C OD) = (atomics C)"|
"atomics ({P} WAIT b END) = {}"

fun interfree::"acom option \<times> assn \<times> acom option \<Rightarrow> bool" where
  -- {* interfree (c1, Q, c2) holds when c2 does not interfere with the annotation of c1 and with Q,
i.e. if R is the precondition of an atomic statement r of c2 then (1) starting in an R and Q state 
and executing r leads to a Q state; (2) if P is an assertion in c1, then starting in an R and P state 
and executing r leads to a P state.*}
"interfree(co, Q, None) = True"|
"interfree(None, Q, Some a) = (\<forall>(R, r) \<in> (atomics a). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q s \<and> R s} r {Q})"|
"interfree(Some c, Q, Some a) = (\<forall>(R, r) \<in> (atomics a). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q s \<and> R s} r {Q} \<and> 
                                 (\<forall>P \<in> (assertions c).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P}))"

definition INTERFREE::"((acom option \<times> assn) list) \<Rightarrow> bool" where
"INTERFREE Ts \<equiv> (\<forall>i \<in> Index Ts. \<forall>j \<in> Index Ts. i \<noteq> j \<longrightarrow> interfree(com(Ts ! i), post(Ts ! i), com(Ts!j)))"

inductive
  hoare_par :: "assn \<Rightarrow> par_com \<Rightarrow> assn \<Rightarrow> bool" ("\<turnstile>\<^sub>P ({(1_)}/ (_)/ {(1_)})" 50)
where
Parallel:  "\<lbrakk>\<forall>i \<in> Index Ts. \<exists>(c::acom) Q. (Ts!i) = (Some c, Q) \<and> (\<turnstile> c {Q}); INTERFREE Ts\<rbrakk> 
    \<Longrightarrow> (\<turnstile>\<^sub>P {\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s} (Parallel Ts)
           {\<lambda> s . \<forall>i \<in> Index Ts. (post (Ts!i)) s})"|

ParAssign: "\<turnstile>\<^sub>P {\<lambda>s. P (s[a/x])} (x ::= a) {Q}"  |

ParSeq: "\<lbrakk> \<turnstile>\<^sub>P {P} c0 {R}; \<turnstile>\<^sub>P {R} c1 {Q} \<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>P {P} (c0,, c1) {Q}"  |

ParCond: "\<lbrakk> \<turnstile>\<^sub>P {\<lambda>s. P s \<and> bval b s} c1 {Q}; \<turnstile>\<^sub>P {\<lambda>s. P s \<and> \<not>bval b s} c2 {Q}\<rbrakk>
    \<Longrightarrow> \<turnstile>\<^sub>P {P} (IF b THEN c1 ELSE c2 FI) {Q}"  |

ParWhile: "\<lbrakk>\<turnstile>\<^sub>P {\<lambda>s. P s \<and> bval b s} c {P}\<rbrakk> \<Longrightarrow>
       \<turnstile>\<^sub>P {P} (WHILE b INV I DO c OD) {\<lambda>s. P s \<and> \<not>bval b s}"  |

ParConseq:"\<lbrakk> \<forall>s. P' s \<longrightarrow> P s; \<turnstile>\<^sub>P {P} c {Q};  \<forall>s. Q s \<longrightarrow> Q' s\<rbrakk> \<Longrightarrow> \<turnstile>\<^sub>P {P'} c {Q'}"

section {* Soundness of the Owicki and Gries proof rules *}

subsection {* INTERFREE is preserved by the small step relation. *}

lemma index_unchanged:
  assumes "(Parallel Ts, s) \<rightarrow>\<^sub>P (Parallel Rs, t)"
  shows "Index Ts = Index Rs"
proof -
  obtain i c Q ro t where 1:"i \<in> Index Ts" and 2:"Ts!i = (Some c, Q)" and 3:"(Some c,s) \<rightarrow> (ro,t)"
  and 4:"(Parallel Rs, t) = (Parallel (Ts[i := (ro, Q)]), t)"
  using assms ParallelE by auto
  have "length Ts = length Rs" using 4 by auto
  thus ?thesis by (auto simp add:Index_def)
qed

lemma post_unchanged:
  assumes "(Parallel Ts, s) \<rightarrow>\<^sub>P (Parallel Rs, t)"
  and "i \<in> Index Ts"
  shows "post (Ts!i) = post (Rs!i)"
proof -
  obtain i c Q ro t where 1:"i \<in> Index Ts" and 2:"Ts!i = (Some c, Q)" and 3:"(Some c, s) \<rightarrow> (ro,t)"
  and 4:"(Parallel Rs, t) = (Parallel (Ts[i := (ro, Q)]), t)"
  using assms ParallelE by auto
  thus ?thesis
  by (metis Index_def mem_Collect_eq nth_list_update_eq nth_list_update_neq par_com.inject(1) post.simps prod.sel(1))  
qed

lemma assertions_decrease:
  assumes "(Some c, s) \<rightarrow> (Some c', t)"
  shows "assertions c' \<subseteq> assertions c" using assms
by (induct "Some c" s "Some c'" t arbitrary: c c' rule:small_step_induct) auto

lemma atomics_decrease:
  assumes "(Some c, s) \<rightarrow> (Some c', t)"
  shows "atomics c' \<subseteq> atomics c"  using assms
by (induct "Some c" s "Some c'" t arbitrary: c c' rule:small_step_induct) auto

lemma interfree_step:
  assumes "interfree(Some c, Q, opt)" and "(Some c, s) \<rightarrow> (ro, t)"
  shows "interfree(ro, Q, opt)"
proof (cases opt)
  case None
  thus "interfree(ro, Q, opt)" by simp
next
  case (Some u)
  thus ?thesis using assms
  proof (induct "(ro, Q, opt)" rule:interfree.induct)
    assume "None = opt" and "opt = Some u"
    hence "False" by simp
    thus "interfree(ro, Q, opt)" by auto
  next
    case (2) thus ?thesis by auto
  next
    case (3) thus ?thesis using assertions_decrease by fastforce
  qed
qed

lemma interfree_step_rev:
  assumes "interfree(opt, Q, Some c)" and "(Some c, s) \<rightarrow> (ro, t)"
  shows "interfree(opt, Q, ro)"
proof (cases opt)
  case None
  thus ?thesis using assms
  proof (induct "(opt, Q, ro)" rule:interfree.induct)
    case 1 thus ?thesis using interfree.simps(1) by blast
  next
    case 2 thus ?thesis by (meson atomics_decrease interfree.simps(2) set_rev_mp)
  next
    case 3 thus ?thesis by blast
  qed
next
  case (Some u)
  thus ?thesis using assms
  proof (induct "(ro, Q, opt)" rule:interfree.induct)
    case 1 thus ?thesis by blast
  next
    case (2) thus ?thesis by auto
  next
    case (3) thus ?thesis by (meson atomics_decrease interfree.simps(3) set_rev_mp)
  qed
qed

lemma interfree_step_post:
  assumes "interfree(opt, Q, Some c)" and "(Some c, s) \<rightarrow> (ro, t)" and "case opt of (Some u) \<Rightarrow> pre u s| None \<Rightarrow> Q s"
  and "pre c s"
  shows "case opt of (Some u) \<Rightarrow> pre u t| None \<Rightarrow> Q t"
  proof(cases opt)
  case None
    have 1:"Q s" using None assms(3) by simp
    from assms(1) None have 2:"\<forall>(R, r) \<in> (atomics c). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q s \<and> R s} r {Q}" by force
    show ?thesis using assms(2) assms(1,3,4)
    proof (induction "Some c" s ro t arbitrary: c rule:small_step_induct)
      case (Assign P x a s) 
      print_cases
      hence 3:"{(P, x ::= a)} = atomics ({P} x ::= a)" by simp
      with Assign.prems(1) have 4:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q s \<and> P s} x ::= a {Q}"
      by (metis (no_types, lifting) None hoare_valid_tr_def interfree.simps(2) singletonI splitD)
      have 5:"Q s \<and> P s" using None Assign.prems(2,3) by auto
      show ?case using 3 4 5
        by (metis (mono_tags, lifting) None hoare_valid_tr_def option.simps(4) small_step_tr.Assign star_step1)
    qed (auto simp add:None) 
  next
  case (Some u)
  
    
    
  hence 1:"(\<forall>s t. \<forall>(R, r) \<in> (atomics c). ((\<lambda>s. Q s \<and> R s) s \<and> (Some(r), s) \<rightarrow>\<^sub>t\<^sub>r* (None, t))  \<longrightarrow>  Q t)" using assms(1) hoare_valid_tr_def by auto
  hence "(\<forall>s t. \<forall>(R, r) \<in> (atomics c). ((\<lambda>s. Q s \<and> R s) s \<and> (Some c, s) \<rightarrow> (ro, t))  \<longrightarrow>  Q t)"
  (*show ?thesis using assms(2) using assms(1, 3)
  proof(induct "Some c" s "ro" t rule:small_step_induct)
    case (Assign P x a s) thus ?case*)
next
  case (Some u)
  thus ?thesis using assms

  qed
qed*)



lemma INTERFREE_Step: assumes "(Parallel Ts, s) \<rightarrow>\<^sub>P (Parallel Rs, t)" and "INTERFREE Ts" shows "INTERFREE Rs"
proof -
  obtain i c Q ro t where 1:"i \<in> Index Ts" and 2:"Ts!i = (Some c, Q)" and 3:"(Some c,s) \<rightarrow> (ro,t)"
  and 41:"(Parallel Rs, t) = (Parallel (Ts[i := (ro, Q)]), t)"
  using assms(1) ParallelE by auto
  have 42:"Rs = Ts[i := (ro, Q)]" using 41 by blast
  have 0:"Index Ts = Index Rs" using assms(1) index_unchanged by auto
  thm INTERFREE_def
  { fix j k
    assume 5:"j \<in> Index Rs" and 6:"k \<in> Index Rs" and 7:"j \<noteq> k"
    have "interfree (com (Rs ! j), post (Rs ! j), com (Rs ! k))"
    proof (cases "i = j \<or> i = k")
      case False thus ?thesis using assms 5 6 7 42 INTERFREE_def 0 by auto
    next
      case True
      note 8 = this
      show ?thesis
      proof (cases "i = j")
        case True 
        hence "interfree (Some c, post (Ts ! j), com (Ts ! k))"
        using assms(2) 8 7 2 5 6 0 INTERFREE_def by auto
        thus ?thesis using interfree_step
        by (smt 2 3 42 5 7 Index_def Proof_Par.com.simps(1) Proof_Par.com.simps(2) True list_update_overwrite list_update_same_conv mem_Collect_eq nth_list_update_neq option.collapse post.simps)
      next
        case False 
        hence "interfree (com (Ts ! j), post (Ts ! j), Some c)" 
        using assms(2) 8 7 2 5 6 0 INTERFREE_def by force
        thus ?thesis using interfree_step_rev 
        by (smt 0 3 42 6 False Index_def True com.elims mem_Collect_eq nth_list_update_eq nth_list_update_neq prod.inject)
      qed
    qed }
  thus ?thesis unfolding INTERFREE_def by blast
qed

subsection {* Strong soundness of the parallel small step. *}

lemma strong_soundness_paral_1:
  fixes Ts Rs s t
  assumes 0:"(Parallel Ts, s) \<rightarrow>\<^sub>P (Parallel Rs, t)"
  and 1:"INTERFREE Ts"
  and 2:"\<forall>i \<in> Index Ts. case (com (Ts!i)) of (Some c) \<Rightarrow> pre c s  \<and> (\<turnstile> c {post (Ts!i)}) | None \<Rightarrow> post (Ts!i) s"
  shows "\<forall> j \<in> Index Rs . case (com (Rs!j)) of (Some c) \<Rightarrow> pre c t  \<and> (\<turnstile> c {post (Rs!j)}) | None \<Rightarrow> post (Rs!j) t"
proof-
  have 3:"INTERFREE Rs" by (metis 0 1 INTERFREE_Step)
  obtain i c Q ro where 4:"i \<in> Index Ts" and 5:"Ts!i = (Some c, Q)" and 6:"(Some c, s) \<rightarrow> (ro, t)"
  and 7:"(Parallel Rs, t) = (Parallel (Ts[i := (ro, Q)]), t)"  using assms ParallelE by auto
  have 8:"Rs = Ts[i := (ro, Q)]" using 7 by blast
  have 9:"Index Ts = Index Rs" using assms(1) index_unchanged by auto
  { 
    fix j
    assume 10:"j \<in> Index Rs"
    have "case (com (Rs!j)) of (Some c) \<Rightarrow> pre c t  \<and> (\<turnstile> c {post (Rs!j)}) | None \<Rightarrow> post (Rs!j) t"
    proof (cases "i = j")
      case True thus ?thesis 
      by (smt 10 2 5 6 8 9 Index_def com.elims fst_conv mem_Collect_eq nth_list_update_eq option.case_eq_if option.distinct(1) option.sel post.simps star_step1 strong_sound)
    next
      case False 
      have 11:"i \<noteq> j" by (metis False) 
      hence 12:"case (com (Rs!j)) of (Some c) \<Rightarrow> pre c s  \<and> (\<turnstile> c {post (Rs!j)}) | None \<Rightarrow> post (Rs!j) s" using 2 8 post_unchanged
      by (metis (no_types, lifting) 10 9 nth_list_update_neq option.case_eq_if)
      have "interfree (com(Rs ! j), post (Rs ! j), Some c)"
      by (metis (no_types, lifting) 1 10 4 5 6 8 9 False INTERFREE_def Proof_Par.com.simps(1) interfree_step_rev nth_list_update_neq)
      thus ?thesis
      by (metis (no_types, lifting) "12" "2" "4" "5" "6" Proof_Par.com.simps(1) interfree_step_post option.case_eq_if option.distinct(1) option.sel) 
    qed
  }
  thus ?thesis by blast
qed

lemma strong_soundness_paral:
  fixes Ts Rs s t
  assumes "(Parallel Ts, s) \<rightarrow>\<^sub>P* (Parallel Rs, t)"
  and "INTERFREE Ts"
  and "\<forall>i \<in> Index Ts. case (com (Ts!i)) of (Some c) \<Rightarrow> pre c s  \<and> (\<turnstile> c {post (Ts!i)}) | None \<Rightarrow> post (Ts!i) s"
  shows "\<forall> j  \<in> Index Rs . case (com (Rs!j)) of (Some c) \<Rightarrow> pre c t  \<and> (\<turnstile> c {post (Rs!j)}) | None \<Rightarrow> post (Rs!j) t"
  using assms 
  proof (induct "Parallel Ts" s "Parallel Rs" t arbitrary: Ts Rs rule:star_induct)
  case (refl) thus ?case by (metis (no_types, lifting)) 
next
  case (step y) thus ?case using strong_soundness_paral_1
  by (smt INTERFREE_Step ParallelE eq_fst_iff option.case_eq_if)
qed

end