theory Example2
imports VCG
begin

text {* 
Annotated program: 
  {@{term "flag0 = 0"}} 
  flag0 := 1;; 
  {flag0 = 1}
  turn := 1;; 
  {flag0 = 1 /\ (turn = 0 \/ turn = 1)}
  WAIT turn = 0 \/ flag1 = 0;; 
  {flag0 = 1 /\ (flag1 = 0 \/ turn = 0)}
  skip;; 
  {flag0 = 1 /\ (flag1 = 0 \/ turn = 0)}
  flag0 := 0
  {@{term "flag0 = 0"}} 
  || 
  {@{term "flag1 = 0"}} 
  flag1 := 1;;
  {flag1 = 1}
  turn := 0;;
  {flag1 = 1 /\ (turn = 0 \/ turn = 1)}
  WAIT (flag0 = false || turn = 1) END; 
  {flag1 = 1 /\ (flag0 = 0 \/ turn = 1)} 
  skip; 
  {flag1 = 1 /\ (flag0 = 0 \/ turn = 1)}
  flag1 := 0
  {@{term "flag1 = 0"}}

Goal: \<turnstile>\<^sub>P {True} WHILE True DO flag0 := true; turn := 1; wait (flag1 = false || turn = 0); {flag0 = true /\ (flag1 = false \/ turn = 0)} skip; flag0 := false
  || WHILE True DO flag1 := true; turn := 0; wait (flag0 = false || turn = 1); {flag1 = true /\ (flag0 = false \/ turn = 1)} skip; flag1 := false {True}
*}

definition Or::"bexp \<Rightarrow> bexp \<Rightarrow> bexp" where "Or b1 b2 \<equiv> Not (And (Not b1) (Not b2))"
definition Equal::"aexp \<Rightarrow> aexp \<Rightarrow> bexp" where "Equal a1 a2 \<equiv> And (Not (Less a1 a2)) (Not (Less a2 a1))"

lemma or_bval:"bval (Or b1 b2) s = (bval b1 s \<or> bval b2 s)" by (metis Or_def bval.simps(2) bval_And_if)
lemma equal_bval:"bval (Equal a1 a2) s = (aval a1 s = aval a2 s)" by (smt Equal_def bval.simps(2) bval.simps(4) bval_And_if) 

abbreviation pre10 :: "assn" where "pre10 \<equiv> \<lambda>s. s ''f0'' = 0"
abbreviation pre11 :: "assn" where "pre11 \<equiv> \<lambda>s. s ''f0'' = 1"
abbreviation pre12 :: "assn" where "pre12 \<equiv> \<lambda>s. s ''f0'' = 1 \<and> (s ''t'' = 1 \<or> s ''t'' = 0)"
abbreviation pre13 :: "assn" where "pre13 \<equiv> \<lambda>s. s ''f0'' = 1 \<and> (s ''f1'' = 0 \<or> s ''t'' = 0)"

abbreviation assign11  :: "state \<Rightarrow> state" where "assign11 \<equiv> \<lambda>s. s(''f0'' := 1)"
abbreviation assign12  :: "state \<Rightarrow> state" where "assign12 \<equiv> \<lambda>s. s(''t'' := 1)"
abbreviation assign13  :: "state \<Rightarrow> state" where "assign13 \<equiv> \<lambda>s. s(''f0'' := 0)"

abbreviation p1::"acom" where "p1 \<equiv> (((((ABasic (pre10) assign11);; ABasic (pre11) assign12);;
({pre12} WAIT (Or (Equal (V ''f1'') (N 0)) (Equal (V ''t'') (N 0))) END));; (ABasic (pre13) id));; (ABasic (pre13) assign13))"

lemma atomic_p1:"(atomics p1) = {(pre10, Basic assign11),(pre11, Basic assign12),(pre13, Basic id),(pre13, Basic assign13)}"
by (simp add: insert_commute)

lemma assertion_p1:"(assertions p1) = {pre10, pre11, pre12, pre13, pre13}" by auto

abbreviation pre20 :: "assn" where "pre20 \<equiv> \<lambda>s. s ''f1'' = 0"
abbreviation pre21 :: "assn" where "pre21 \<equiv> \<lambda>s. s ''f1'' = 1"
abbreviation pre22 :: "assn" where "pre22 \<equiv> \<lambda>s. s ''t'' = 0 \<and> s ''f1'' = 1"
abbreviation pre23 :: "assn" where "pre23 \<equiv> \<lambda>s. s ''f1'' = 1 \<and> (s ''f0'' = 0 \<or> s ''t'' = 1)"

abbreviation assign21  :: "state \<Rightarrow> state" where "assign21 \<equiv> \<lambda>s. s(''f1'' := 1)"
abbreviation assign22  :: "state \<Rightarrow> state" where "assign22 \<equiv> \<lambda>s. s(''t'' := 0)"
abbreviation assign23  :: "state \<Rightarrow> state" where "assign23 \<equiv> \<lambda>s. s(''f1'' := 0)"

abbreviation post1 :: "assn" where "post1 \<equiv> \<lambda>s. s ''f0'' = 0"
abbreviation post2 :: "assn" where "post2 \<equiv> \<lambda>s. s ''f1'' = 0"

abbreviation p2::"acom" where "p2 \<equiv> (((((ABasic (pre20) assign21);; ABasic (pre21) assign22);;
({pre22} WAIT (Or (Equal (V ''f0'') (N 0)) (Equal (V ''t'') (N 1))) END));; (ABasic (pre23) id));; (ABasic (pre23) assign23))"

lemma atomic_p2:"(atomics p2) = {(pre20, Basic assign21),(pre21, Basic assign22),(pre23, Basic id),(pre23, Basic assign23)}"
by (simp add: insert_commute)

lemma assertion_p2:"(assertions p2) = {pre20, pre21, pre22, pre23, pre23}" by auto

lemma p1_hoare:"\<turnstile> p1 {post1}"
proof -
  have "vc p1 post1" using equal_bval or_bval by auto
  thus ?thesis by simp
qed

lemma p2_hoare:"\<turnstile> p2 {post2}"
proof -
  have "vc p2 post2" using equal_bval or_bval by auto
  thus ?thesis by simp
qed

lemma interf_21_post:"\<forall>(R, r) \<in> (atomics p2). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> R s} r {post1}"
proof -
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre20 s} Basic assign21 {post1}" by simp
  hence 1:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre20 s} Basic assign21 {post1}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre21 s} Basic assign22 {post1}" by simp
  hence 2:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre21 s} Basic assign22 {post1}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre23 s} Basic id {post1}" by simp
  hence 3:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre23 s} Basic id {post1}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre23 s} Basic assign23 {post1}" by simp
  hence 4:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre23 s} Basic assign23 {post1}" using hoare_sound_tr by blast
  show ?thesis using 1 2 3 4 atomic_p1 by simp
qed

(*lemma atomic_p2:"(atomics p2) = {(pre20, Basic assign21),(pre21, Basic assign22),(pre23, Basic id),(pre23, Basic assign23)}"
by (simp add: insert_commute)*)
(*lemma assertion_p1:"(assertions p1) = {pre0, pre11, pre12, pre13, pre13}" by auto*)
lemma interf_21_pre:"\<forall>(R, r) \<in> (atomics p2).(\<forall>P \<in> (assertions p1).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P})"
proof-
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre20 s} Basic assign21 {pre10}" by simp
  hence 1:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre20 s} Basic assign21 {pre10}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre20 s} Basic assign21 {pre11}" by simp
  hence 2:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre20 s} Basic assign21 {pre11}" using hoare_sound_tr by blast
oops
  

lemma interf_12_post:"\<forall>(R, r) \<in> (atomics p1). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> R s} r {post2}"
proof -
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre10 s} Basic assign11 {post2}" by simp
  hence 1:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre10 s} Basic assign11 {post2}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre11 s} Basic assign12 {post2}" by simp
  hence 2:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre11 s} Basic assign12 {post2}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre13 s} Basic id {post2}" by simp
  hence 3:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre13 s} Basic id {post2}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre13 s} Basic assign13 {post2}" by simp
  hence 4:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre13 s} Basic assign13 {post2}" using hoare_sound_tr by blast
  show ?thesis using 1 2 3 4 atomic_p2 by simp
qed

lemma interf_12_pre:"\<forall>(R, r) \<in> (atomics p1).(\<forall>P \<in> (assertions p2).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P})" sorry

abbreviation Ts::"(acom option \<times> assn) list" where "Ts \<equiv> [(Some p1, post1),(Some p2, post2)]"

lemma "\<turnstile>\<^sub>P {\<lambda>s. \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s} Parallel Ts {\<lambda>s. True}"
proof -
  have Ind:"Index Ts = {0, Suc 0}"
  proof -
    have "length Ts = 2" by simp
    hence "Index2 Ts = {0, Suc 0}" by auto
    thus ?thesis using Index_Equal by blast
  qed
  have 0:"(Ts!0) = (Some p1, post1)" by simp
  have 1:"(Ts!1) = (Some p2, post2)" by simp
  have "\<turnstile>\<^sub>P {\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s} (Parallel Ts) {\<lambda> s . \<forall>i \<in> Index Ts. (post (Ts!i)) s}"
  proof-
    have 2:"(\<forall>i \<in> Index Ts. \<exists>(c::acom) Q. (Ts!i) = (Some c, Q) \<and> (\<turnstile> c {Q}))" using Ind p1_hoare p2_hoare by auto
    have Int:"INTERFREE Ts"
    proof -
      have "(\<forall>(R, r) \<in> (atomics p2). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> R s} r {post1} \<and> (\<forall>P \<in> (assertions p1).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P}))"
      proof -
        have "\<forall>(R, r) \<in> (atomics p2). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> R s} r {post1}" using interf_21_post by blast
        moreover have "\<forall>(R, r) \<in> (atomics p2).(\<forall>P \<in> (assertions p1).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P})" using interf_21_pre by blast
        ultimately show ?thesis by blast
      qed
      hence 3:"interfree(Some p1, post1, Some p2)" using interfree.simps(3) by presburger
      have "(\<forall>(R, r) \<in> (atomics p1). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> R s} r {post2} \<and> (\<forall>P \<in> (assertions p2).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P}))"
      proof -
        have "\<forall>(R, r) \<in> (atomics p1). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> R s} r {post2}" using interf_12_post by blast
        moreover have "\<forall>(R, r) \<in> (atomics p1).(\<forall>P \<in> (assertions p2).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P})" using interf_12_pre by blast
        ultimately show ?thesis by blast
      qed
      hence "interfree(Some p2, post2, Some p1)" using interfree.simps(3) by presburger
      hence "\<forall>i \<in> Index Ts. \<forall>j \<in> Index Ts. i \<noteq> j \<longrightarrow> interfree(com(Ts ! i), post(Ts ! i), com(Ts!j))" using Ind 0 1 3
        by (smt One_nat_def Proof_Par.com.simps(1) insertE post.simps singletonD)
      thus ?thesis  using INTERFREE_def by blast
    qed
    thus ?thesis using Ind 0 1 2 by blast
  qed
  moreover have "\<forall>t. (\<lambda>s. \<forall>i \<in> Index Ts. (post (Ts!i)) s) t \<longrightarrow> (\<lambda>s. True) t" by (smt Ind insertI1 insert_commute nth_Cons_0 nth_Cons_Suc post.simps)
  moreover have "\<forall>t. (\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s) t \<longrightarrow> (\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s) t" by blast
  ultimately show ?thesis using ParConseq by metis
qed

end