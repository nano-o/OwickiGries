theory Example
imports VCG
begin

text {* Goal: \<turnstile>\<^sub>P {x = 0} x := x+1 || x:= x+1 {x = 2} *}

text {* 
Annotated program: 
  {x = 0, d1 = false, ...} (x := x+1, d1 := true) {x = x+1} 
  || 
  {x = 0, d2 = false, ...} (x:= x+1, d2 := true) {x = x+1} 

Goal: \<turnstile>\<^sub>P {x = 0, d1 = false, d2 = false} x := x+1 || x:= x+1 {x = 2}
*}

abbreviation pre1 :: "assn" where "pre1 \<equiv> \<lambda>s. s ''d1'' = 0 \<and> (s ''d2'' = 0 \<longrightarrow> s ''x'' = 0) \<and> (s ''d2'' = 1 \<longrightarrow> s ''x'' = 1)"
abbreviation pre2  :: "assn" where "pre2 \<equiv> \<lambda>s. s ''d2'' = 0 \<and> (s ''d1'' = 0 \<longrightarrow> s ''x'' = 0) \<and> (s ''d1'' = 1 \<longrightarrow> s ''x'' = 1)"
abbreviation post1 :: "assn" where "post1 \<equiv> \<lambda>s. s ''d1'' = 1 \<and> (s ''d2'' = 0 \<longrightarrow> s ''x'' = 1) \<and> (s ''d2'' = 1 \<longrightarrow> s ''x'' = 2)"
abbreviation post2  :: "assn" where "post2 \<equiv> \<lambda>s. s ''d2'' = 1 \<and> (s ''d1'' = 0 \<longrightarrow> s ''x'' = 1) \<and> (s ''d1'' = 1 \<longrightarrow> s ''x'' = 2)"

abbreviation plus11  :: "state \<Rightarrow> state" where "plus11 \<equiv> \<lambda>s. s(''x'' := s ''x'' + 1, ''d1'' := 1)"
abbreviation plus12  :: "state \<Rightarrow> state" where "plus12 \<equiv> \<lambda>s. s(''x'' :=  s ''x'' + 1, ''d2'' := 1)"

abbreviation "C2 \<equiv> ABasic pre2 (plus12)"

abbreviation Ts :: "((acom option \<times> assn) list)" where "Ts \<equiv> [((Some (ABasic pre1 (plus11))), post1), ((Some (ABasic pre2 (plus12))), post2)]"

lemma "\<forall>(R, r) \<in> (atomics C2). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> R s} r {post1}"
apply auto oops

subsubsection{* Proof by Hoare Logic *}

(* declare [[show_types]] *)

lemma "\<turnstile>\<^sub>P {\<lambda>s. s ''x'' = 0 \<and> s ''d1'' = 0 \<and> s ''d2'' = 0} Parallel Ts {\<lambda>s. s ''x'' = 2}"
proof -
  have Ind:"Index Ts = {0, Suc 0}"
  proof -
    have "length Ts = 2" by simp
    hence "Index2 Ts = {0, Suc 0}" by auto
    thus ?thesis using Index_Equal by blast
  qed
  obtain C1::acom and Q1::assn where 0:"(Ts!0) = (Some C1, Q1)" by simp
  obtain C2::acom and Q2::assn where 1:"(Ts!1) = (Some C2, Q2)" by simp
  have "\<turnstile> C1 {Q1}" and "\<turnstile> C2 {Q2}" using 0 1 by auto
  hence 3:"(\<forall>i \<in> Index Ts. \<exists>(c::acom) Q. (Ts!i) = (Some c, Q) \<and> (\<turnstile> c {Q}))" by (metis (no_types, lifting) 0 1 Ind One_nat_def insertE singletonD)
  have "INTERFREE Ts"
  proof -
    have "(\<forall>(R, r) \<in> (atomics C2). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q1 s \<and> R s} r {Q1} \<and> (\<forall>P \<in> (assertions C1).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P}))"
    proof -
      have "\<forall>(R, r) \<in> (atomics C2). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q1 s \<and> R s} r {Q1}"
      proof -
        have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q1 s \<and> pre2 s} Basic plus12 {Q1}" using 0 by auto
        hence "\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q1 s \<and> pre2 s} Basic plus12 {Q1}" using hoare_sound_tr by blast
        thus ?thesis using 1 hoare_sound_tr by auto
      qed
      moreover
      have "\<forall>(R, r) \<in> (atomics C2).(\<forall>P \<in> (assertions C1).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P})"
      proof -
        have "vc_tr (Basic plus12) pre1" using vc_tr.simps(1) by blast
        hence "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre1 s \<and> pre2 s} Basic plus12 {pre1}" using 0 by auto
        hence "\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre1 s \<and> pre2 s} Basic plus12 {pre1}" using hoare_sound_tr by blast
        thus ?thesis using 0 1 by auto
      qed
      ultimately show ?thesis by blast
    qed
    hence 5:"interfree(Some C1, Q1, Some C2)" using interfree.simps(3) by presburger
    have "(\<forall>(R, r) \<in> (atomics C1). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q2 s \<and> R s} r {Q2} 
      \<and> (\<forall>P \<in> (assertions C2).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P}))"
    proof -
      have "\<forall>(R, r) \<in> (atomics C1). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q2 s \<and> R s} r {Q2}"
      proof -
        have "vc_tr (Basic plus11) Q2" using vc_tr.simps(1) by blast
        hence "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q2 s \<and> pre1 s} Basic plus11 {Q2}" using 1 by auto
        hence "\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. Q2 s \<and> pre1 s} Basic plus11 {Q2}" using hoare_sound_tr by blast
        thus ?thesis using 0 hoare_sound_tr by auto
      qed
      moreover
      have "\<forall>(R, r) \<in> (atomics C1).(\<forall>P \<in> (assertions C2).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P})"
      proof -
        have "vc_tr (Basic plus11) pre2" using vc_tr.simps(1) by blast
        hence "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre2 s \<and> pre1 s} Basic plus11 {pre2}" using 0 by auto
        hence "\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre2 s \<and> pre1 s} Basic plus11 {pre2}" using hoare_sound_tr by blast
        thus ?thesis using 0 1 by auto
      qed
      ultimately show ?thesis by blast
    qed
    hence "interfree(Some C2, Q2, Some C1)" using interfree.simps(3) by presburger
    hence "\<forall>i \<in> Index Ts. \<forall>j \<in> Index Ts. i \<noteq> j \<longrightarrow> interfree(com(Ts ! i), post(Ts ! i), com(Ts!j))" using Ind 0 1 5
      by (smt One_nat_def Proof_Par.com.simps(1) insertE post.simps singletonD)
    thus ?thesis  using INTERFREE_def by blast
  qed
  hence 7:"vc_par (Parallel Ts) (\<lambda> s . \<forall>i \<in> Index Ts. (post (Ts!i)) s)" using Ind 0 1 3 by simp
  have "\<forall>s. (\<lambda>s. \<forall>i \<in> Index Ts. (post (Ts!i)) s) s \<longrightarrow> (\<lambda>s. s ''x'' = 2) s"
    by (smt Ind insertI1 insert_commute nth_Cons_0 nth_Cons_Suc post.simps) 
  hence 8:"vc_par (Parallel Ts) (\<lambda>s. s ''x'' = 2)" using 7 vc_mono_par by smt
  hence 9:"\<turnstile>\<^sub>P {\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s} (Parallel Ts) {\<lambda>s. s ''x'' = 2}" using pre_par.simps(1) vc_sound_par' by presburger
  have "\<forall>s. (\<lambda>s. s ''x'' = 0 \<and> s ''d1'' = 0 \<and> s ''d2'' = 0) s \<longrightarrow> (\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s) s"
    by (smt Ind Proof_Par.com.simps(1) insertE nth_Cons_0 nth_Cons_Suc option.sel pre.simps(1) singletonD)
  thus ?thesis by (smt 8 9 pre_par.simps(1) vc_sound_par')
qed

end