theory Proof_Par
imports Proof_System
begin

fun asubst:: "aexp \<Rightarrow> aexp \<Rightarrow> vname\<Rightarrow> aexp" where  
"asubst (N n) a x  = N n"|
"asubst (V v) a x = (if v = x then a else V v)"|
"asubst (Plus a1 a2) a x = Plus (asubst a1 a x) (asubst a2 a x)"

fun strongest_post :: "acom \<Rightarrow> assn \<Rightarrow> assn" where
  -- {* Computes the strongest postcodition of an annotated command. *}
"strongest_post ({P} x ::= a) Q = (\<lambda>s. \<exists>y. (s x = aval (asubst a y x) s) \<and> Q (s[y/x]))" |
"strongest_post (C1;; C2) P = strongest_post C2 (strongest_post C1 P)" |
"strongest_post ({P} IF b THEN C1 ELSE C2 FI) Q =
  (\<lambda>s. strongest_post C1 (\<lambda>s. Q s \<and> bval b s) s \<or> strongest_post C2 (\<lambda>s. Q s \<and> \<not>bval b s) s)"|
"strongest_post ({P} WHILE b INV I DO C OD) Q = (\<lambda>s. I s \<and> \<not>bval b s)"|
"strongest_post ({P} WAIT b END) Q = (\<lambda>s. Q s \<and> bval b s)"

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

thm star_induct[where ?r="par_trans"]

abbreviation P  where "P Ts s Rs t \<equiv> INTERFREE Ts \<longrightarrow> (\<forall> i \<in> Index Ts . \<exists>(c::acom) Q. (Ts!i) = (Some c, Q) \<and> (\<turnstile> c {Q})) \<longrightarrow> 
 (\<forall> i \<in> Index Ts . case (com (Ts!i)) of (Some c) \<Rightarrow> pre c s | None \<Rightarrow> True) \<longrightarrow> 
 (\<forall> j  \<in> Index Rs . case (com (Rs!j)) of (Some c) \<Rightarrow> pre c t | None \<Rightarrow> post (Rs!j) t)"

lemma interfree_step:"\<lbrakk>interfree(Some c, Q, opt); (Some c, s) \<rightarrow> (ro, t)\<rbrakk> \<Longrightarrow> interfree(ro, Q, opt)" sorry

lemma interfree_step_rev:"\<lbrakk>interfree(opt, Q, Some c); (Some c, s) \<rightarrow> (ro, t)\<rbrakk> \<Longrightarrow> interfree(opt, Q, ro)" sorry

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

thm ParallelE

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
        by (smt "2" "3" "42" "5" "7" Index_def Proof_Par.com.simps(1) Proof_Par.com.simps(2) True list_update_overwrite list_update_same_conv mem_Collect_eq nth_list_update_neq option.collapse post.simps)
      next
        case False 
        hence "interfree (com (Ts ! j), post (Ts ! j), Some c)" 
        using assms(2) 8 7 2 5 6 0 INTERFREE_def by force
        thus ?thesis using interfree_step_rev 
        by (smt "0" "3" "42" "6" False Index_def True com.elims mem_Collect_eq nth_list_update_eq nth_list_update_neq prod.inject)
      qed
    qed }
  thus ?thesis unfolding INTERFREE_def by blast
qed

lemma strong_soundness_paral:
  fixes Ts Rs s t
  assumes "(Parallel Ts, s) \<rightarrow>\<^sub>P* (Parallel Rs, t)"
  and "INTERFREE Ts"
  and "\<forall>i \<in> Index Ts. case (com (Ts!i)) of (Some c) \<Rightarrow> pre c s  \<and> (\<turnstile> c {Q}) | None \<Rightarrow> post (Ts!i) s"
  shows "\<forall> j  \<in> Index Rs . case (com (Rs!j)) of (Some c) \<Rightarrow> pre c t | None \<Rightarrow> post (Rs!j) t"
  using assms
proof (induct "(Parallel Ts, s)" "(Parallel Rs, t)" arbitrary:Ts Rs s t  rule:star.induct)
  case (refl) thus ?case by (simp add: option.case_eq_if)
next
  case (step y)
  term ?case
  let ?Ts'="fst y" and ?s'="snd y"
  
end