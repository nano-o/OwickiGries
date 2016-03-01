theory Example2
imports VCG "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

text {* 
Annotated program: 
  {f0 = 0 /\ d0 = 0 /\  (d1 = 2 --> f1 = 1 /\ t = 0) /\ (d1 = 3 --> f1 = 1 /\ t = 0)} 
  f0 := 1;; d0 := d0 + 1;;
  {f0 = 1 /\ d0 = 1 /\  (d1 = 2 --> f1 = 1 /\ t = 0) /\ (d1 = 3 --> f1 = 1 /\ t = 0)} 
  t := 1;; d0 := d0 + 1;;
  {f0 = 1 /\ d0 = 2 /\ (d1 = 2 --> f1 = 1 /\ (t = 0 \/ t = 1)) /\ (d1 = 3 --> f1 = 1 /\ t = 1)} 
  WAIT (t = 0 \/ f1 = 0) END;; 
  {f0 = 1 /\ d0 = 2 /\ (d1 = 2 --> t = 0) /\ (d1 = 3 --> False)} 
  skip;; d0 := d0 + 1;;
  {f0 = 1 /\ d0 = 3 /\ (d1 = 2 --> t = 0) /\ (d1 = 3 --> False)}
  f0 := 0;; d0 := d0 + 1;;
  {f0 = 0 /\ d0 = 4} 
  || 
  {f1 = 0 /\ d1 = 0 /\ (d0 = 2 --> f0 = 1 /\ t = 1) /\ (d0 = 3 --> f0 = 1 /\ t = 1)} 
  f1 := 1;; d1 := d1 + 1;;
  {f1 = 1 /\ d1 = 1 /\ (d0 = 2 --> f0 = 1 /\ t = 1) /\ (d0 = 3 --> f0 = 1 /\ t = 1)} 
  t := 0;; d1 := d1 + 1;;
  {f1 = 1 /\ d1 = 2 /\ (d0 = 2 --> f0 = 1 /\ (t = 0 \/ t = 1)) /\ (d0 = 3 --> f0 = 1 /\ t = 0)}
  WAIT (f0 = 0 || t = 1) END; 
  {f1 = 1 /\ d1 = 2 /\ (d0 = 2 --> t = 1) /\ (d0 = 3 --> False)}
  skip; d1 := d1 + 1;;
  {f1 = 1 /\ d1 = 3 /\ (d0 = 2 --> t = 1) /\ (d0 = 3 --> False)}
  f1 := 0;; d1 := d1 + 1;;
  {f1 = 0 /\ d1 = 4}

Goal: \<turnstile>\<^sub>P {f0 = 0 /\ f1 = 0 /\ d0 = 0 /\ d1 = 0} Parallel Ts {f0 = 0 /\ f1 = 0 /\ d0 = 4 /\ d1 = 4}
*}

definition Or::"bexp \<Rightarrow> bexp \<Rightarrow> bexp" where "Or b1 b2 \<equiv> Not (And (Not b1) (Not b2))"
definition Equal::"aexp \<Rightarrow> aexp \<Rightarrow> bexp" where "Equal a1 a2 \<equiv> And (Not (Less a1 a2)) (Not (Less a2 a1))"

lemma or_bval:"bval (Or b1 b2) s = (bval b1 s \<or> bval b2 s)"
  by (metis Or_def bval.simps(2) bval_And_if)
lemma equal_bval:"bval (Equal a1 a2) s = (aval a1 s = aval a2 s)"
  using Equal_def by auto 

abbreviation pre10 :: "assn" where "pre10 \<equiv> \<lambda>s. s ''f0'' = 0 \<and> s ''d0'' = 0  \<and> (s ''d1'' = 2 \<longrightarrow> (s ''f1'' = 1 \<and> s ''t'' = 0)) 
  \<and> (s ''d1'' = 3 \<longrightarrow> (s ''f1'' = 1 \<and> s ''t'' = 0))"
abbreviation pre11 :: "assn" where "pre11 \<equiv> \<lambda>s. s ''f0'' = 1 \<and> s ''d0'' = 1  \<and> (s ''d1'' = 2 \<longrightarrow> (s ''f1'' = 1 \<and> s ''t'' = 0)) 
  \<and> (s ''d1'' = 3 \<longrightarrow> (s ''f1'' = 1 \<and> s ''t'' = 0))"
abbreviation pre12 :: "assn" where "pre12 \<equiv> \<lambda>s. s ''f0'' = 1 \<and> s ''d0'' = 2  \<and> (s ''d1'' = 2 \<longrightarrow> (s ''f1'' = 1 \<and> (s ''t'' = 0 \<or> s ''t'' = 1))) 
  \<and> (s ''d1'' = 3 \<longrightarrow> (s ''f1'' = 1 \<and> s ''t'' = 1)) "
abbreviation pre13 :: "assn" where "pre13 \<equiv> \<lambda>s. s ''f0'' = 1 \<and> s ''d0'' = 2  \<and> (s ''d1'' = 2 \<longrightarrow> (s ''t'' = 0)) 
  \<and> (s ''d1'' = 3 \<longrightarrow> False) "
abbreviation pre14 :: "assn" where "pre14 \<equiv> \<lambda>s. s ''f0'' = 1 \<and> s ''d0'' = 3  \<and> (s ''d1'' = 2 \<longrightarrow> (s ''t'' = 0)) 
  \<and> (s ''d1'' = 3 \<longrightarrow> False) "

abbreviation assign11  :: "state \<Rightarrow> state" where "assign11 \<equiv> \<lambda>s. s(''f0'' := 1, ''d0'' := s ''d0'' + 1)"
abbreviation assign12  :: "state \<Rightarrow> state" where "assign12 \<equiv> \<lambda>s. s(''t'' := 1, ''d0'' := s ''d0'' + 1)"
abbreviation assign13  :: "state \<Rightarrow> state" where "assign13 \<equiv> \<lambda>s. s(''d0'' := s ''d0'' + 1)"
abbreviation assign14  :: "state \<Rightarrow> state" where "assign14 \<equiv> \<lambda>s. s(''f0'' := 0, ''d0'' := s ''d0'' + 1)"

abbreviation post1 :: "assn" where "post1 \<equiv> \<lambda>s. s ''f0'' = 0 \<and> s ''d0'' = 4"

abbreviation p1::"acom" where "p1 \<equiv> (((((ABasic (pre10) assign11);; ABasic (pre11) assign12);;
({pre12} WAIT (Or (Equal (V ''f1'') (N 0)) (Equal (V ''t'') (N 0))) END));; (ABasic (pre13) assign13));; (ABasic (pre14) assign14))"

abbreviation pre20 :: "assn" where "pre20 \<equiv> \<lambda>s. s ''f1'' = 0 \<and> s ''d1'' = 0  \<and> (s ''d0'' = 2 \<longrightarrow> (s ''f0'' = 1 \<and> s ''t'' = 1)) 
  \<and> (s ''d0'' = 3 \<longrightarrow> (s ''f0'' = 1 \<and> s ''t'' = 1)) "
abbreviation pre21 :: "assn" where "pre21 \<equiv> \<lambda>s. s ''f1'' = 1 \<and> s ''d1'' = 1  \<and> (s ''d0'' = 2 \<longrightarrow> (s ''f0'' = 1 \<and> s ''t'' = 1)) 
  \<and> (s ''d0'' = 3 \<longrightarrow> (s ''f0'' = 1 \<and> s ''t'' = 1)) "
abbreviation pre22 :: "assn" where "pre22 \<equiv> \<lambda>s. s ''f1'' = 1 \<and> s ''d1'' = 2  \<and> (s ''d0'' = 2 \<longrightarrow> (s ''f0'' = 1 \<and> (s ''t'' = 0 \<or> s ''t'' = 1))) 
  \<and> (s ''d0'' = 3 \<longrightarrow> (s ''f0'' = 1 \<and> s ''t'' = 0))"
abbreviation pre23 :: "assn" where "pre23 \<equiv> \<lambda>s. s ''f1'' = 1 \<and> s ''d1'' = 2  \<and> (s ''d0'' = 2 \<longrightarrow> (s ''t'' = 1)) 
  \<and> (s ''d0'' = 3 \<longrightarrow> False)"
abbreviation pre24 :: "assn" where "pre24 \<equiv> \<lambda>s. s ''f1'' = 1 \<and> s ''d1'' = 3  \<and> (s ''d0'' = 2 \<longrightarrow> (s ''t'' = 1)) 
  \<and> (s ''d0'' = 3 \<longrightarrow> False)"

abbreviation assign21  :: "state \<Rightarrow> state" where "assign21 \<equiv> \<lambda>s. s(''f1'' := 1, ''d1'' := s ''d1'' + 1)"
abbreviation assign22  :: "state \<Rightarrow> state" where "assign22 \<equiv> \<lambda>s. s(''t'' := 0, ''d1'' := s ''d1'' + 1)"
abbreviation assign23  :: "state \<Rightarrow> state" where "assign23 \<equiv> \<lambda>s. s(''d1'' := s ''d1'' + 1)"
abbreviation assign24  :: "state \<Rightarrow> state" where "assign24 \<equiv> \<lambda>s. s(''f1'' := 0, ''d1'' := s ''d1'' + 1)"

abbreviation post2 :: "assn" where "post2 \<equiv> \<lambda>s. s ''f1'' = 0 \<and> s ''d1'' = 4"

abbreviation p2::"acom" where "p2 \<equiv> (((((ABasic (pre20) assign21);; ABasic (pre21) assign22);;
({pre22} WAIT (Or (Equal (V ''f0'') (N 0)) (Equal (V ''t'') (N 1))) END));; (ABasic (pre23) assign23));; (ABasic (pre24) assign24))"

abbreviation Ts::"(acom option \<times> assn) list" where "Ts \<equiv> [(Some p1, post1),(Some p2, post2)]"

lemma atomic_p1:"(atomics p1) = {(pre10, Basic assign11),(pre11, Basic assign12),(pre13, Basic assign13),(pre14, Basic assign14)}"
by (simp add: insert_commute)

lemma assertion_p1:"(assertions p1) = {pre10, pre11, pre12, pre13, pre14}" by auto

lemma atomic_p2:"(atomics p2) = {(pre20, Basic assign21),(pre21, Basic assign22),(pre23, Basic assign23),(pre24, Basic assign24)}"
by (simp add: insert_commute)

lemma assertion_p2:"(assertions p2) = {pre20, pre21, pre22, pre23, pre24}" by auto

lemma p1_hoare:"\<turnstile> p1 {post1}"
proof -
  have "vc p1 post1" using equal_bval or_bval by auto
  thus ?thesis by (meson vc_sound)
qed

lemma p2_hoare:"\<turnstile> p2 {post2}"
proof -
  have "vc p2 post2" using equal_bval or_bval by auto
  thus ?thesis by (meson vc_sound)
qed

lemma interf_21_post:"\<forall>(R, r) \<in> (atomics p2). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> R s} r {post1}"
proof -
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre20 s} Basic assign21 {post1}" by simp
  hence 1:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre20 s} Basic assign21 {post1}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre21 s} Basic assign22 {post1}" by simp
  hence 2:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre21 s} Basic assign22 {post1}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre23 s} Basic assign23 {post1}" by simp
  hence 3:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre23 s} Basic assign23 {post1}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre24 s} Basic assign24 {post1}" by simp
  hence 4:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre24 s} Basic assign24 {post1}" using hoare_sound_tr by blast
  show ?thesis using 1 2 3 4 atomic_p1 by simp
qed

lemma interf_21_pre:"\<forall>(R, r) \<in> (atomics p2).(\<forall>P \<in> (assertions p1).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P})"
proof-
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre20 s} Basic assign21 {pre10}" by simp
  hence 1:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre20 s} Basic assign21 {pre10}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre20 s} Basic assign21 {pre11}" by simp
  hence 2:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre20 s} Basic assign21 {pre11}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre12 s \<and> pre20 s} Basic assign21 {pre12}" by simp
  hence 3:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre12 s \<and> pre20 s} Basic assign21 {pre12}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre13 s \<and> pre20 s} Basic assign21 {pre13}" by simp
  hence 4:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre13 s \<and> pre20 s} Basic assign21 {pre13}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre14 s \<and> pre20 s} Basic assign21 {pre14}" by simp
  hence 5:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre14 s \<and> pre20 s} Basic assign21 {pre14}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre21 s} Basic assign22 {pre10}" by simp
  hence 6:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre21 s} Basic assign22 {pre10}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre21 s} Basic assign22 {pre11}" by simp
  hence 7:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre21 s} Basic assign22 {pre11}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre12 s \<and> pre21 s} Basic assign22 {pre12}" by simp
  hence 8:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre12 s \<and> pre21 s} Basic assign22 {pre12}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre13 s \<and> pre21 s} Basic assign22 {pre13}" by simp
  hence 9:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre13 s \<and> pre21 s} Basic assign22 {pre13}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre14 s \<and> pre21 s} Basic assign22 {pre14}" by simp
  hence 10:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre14 s \<and> pre21 s} Basic assign22 {pre14}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre23 s} Basic assign23 {pre10}" by simp
  hence 11:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre23 s} Basic assign23 {pre10}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre23 s} Basic assign23 {pre11}" by simp
  hence 12:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre23 s} Basic assign23 {pre11}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre12 s \<and> pre23 s} Basic assign23 {pre12}" by simp
  hence 13:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre12 s \<and> pre23 s} Basic assign23 {pre12}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre13 s \<and> pre23 s} Basic assign23 {pre13}" by simp
  hence 14:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre13 s \<and> pre23 s} Basic assign23 {pre13}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre14 s \<and> pre23 s} Basic assign23 {pre14}" by simp
  hence 15:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre14 s \<and> pre23 s} Basic assign23 {pre14}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre24 s} Basic assign24 {pre10}" by simp
  hence 16:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre10 s \<and> pre24 s} Basic assign24 {pre10}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre24 s} Basic assign24 {pre11}" by simp
  hence 17:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre11 s \<and> pre24 s} Basic assign24 {pre11}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre12 s \<and> pre24 s} Basic assign24 {pre12}" by simp
  hence 18:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre12 s \<and> pre24 s} Basic assign24 {pre12}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre13 s \<and> pre24 s} Basic assign24 {pre13}" by simp
  hence 19:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre13 s \<and> pre24 s} Basic assign24 {pre13}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre14 s \<and> pre24 s} Basic assign24 {pre14}" by simp
  hence 20:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre14 s \<and> pre24 s} Basic assign24 {pre14}" using hoare_sound_tr by blast
  show ?thesis using 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 by auto
qed
  
lemma interf_12_post:"\<forall>(R, r) \<in> (atomics p1). \<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> R s} r {post2}"
proof -
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre10 s} Basic assign11 {post2}" by simp
  hence 1:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre10 s} Basic assign11 {post2}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre11 s} Basic assign12 {post2}" by simp
  hence 2:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre11 s} Basic assign12 {post2}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre13 s} Basic assign13 {post2}" by simp
  hence 3:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre13 s} Basic assign13 {post2}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre14 s} Basic assign14 {post2}" by simp
  hence 4:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre14 s} Basic assign14 {post2}" using hoare_sound_tr by blast
  show ?thesis using 1 2 3 4 atomic_p2 by simp
qed

lemma interf_12_pre:"\<forall>(R, r) \<in> (atomics p1).(\<forall>P \<in> (assertions p2).\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. P s \<and> R s} r {P})"
proof -
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre20 s \<and> pre10 s} Basic assign11 {pre20}" by simp
  hence 1:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre20 s \<and> pre10 s} Basic assign11 {pre20}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre21 s \<and> pre10 s} Basic assign11 {pre21}" by simp
  hence 2:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre21 s \<and> pre10 s} Basic assign11 {pre21}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre22 s \<and> pre10 s} Basic assign11 {pre22}" by simp
  hence 3:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre22 s \<and> pre10 s} Basic assign11 {pre22}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre23 s \<and> pre10 s} Basic assign11 {pre23}" by simp
  hence 4:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre23 s \<and> pre10 s} Basic assign11 {pre23}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre24 s \<and> pre10 s} Basic assign11 {pre24}" by simp
  hence 5:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre24 s \<and> pre10 s} Basic assign11 {pre24}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre20 s \<and> pre11 s} Basic assign12 {pre20}" by simp
  hence 6:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre20 s \<and> pre11 s} Basic assign12 {pre20}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre21 s \<and> pre11 s} Basic assign12 {pre21}" by simp
  hence 7:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre21 s \<and> pre11 s} Basic assign12 {pre21}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre22 s \<and> pre11 s} Basic assign12 {pre22}" by simp
  hence 8:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre22 s \<and> pre11 s} Basic assign12 {pre22}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre23 s \<and> pre11 s} Basic assign12 {pre23}" by simp
  hence 9:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre23 s \<and> pre11 s} Basic assign12 {pre23}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre24 s \<and> pre11 s} Basic assign12 {pre24}" by simp
  hence 10:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre24 s \<and> pre11 s} Basic assign12 {pre24}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre20 s \<and> pre13 s} Basic assign13 {pre20}" by simp
  hence 11:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre20 s \<and> pre13 s} Basic assign13 {pre20}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre21 s \<and> pre13 s} Basic assign13 {pre21}" by simp
  hence 12:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre21 s \<and> pre13 s} Basic assign13 {pre21}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre22 s \<and> pre13 s} Basic assign13 {pre22}" by simp
  hence 13:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre22 s \<and> pre13 s} Basic assign13 {pre22}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre23 s \<and> pre13 s} Basic assign13 {pre23}" by simp
  hence 14:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre23 s \<and> pre13 s} Basic assign13 {pre23}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre24 s \<and> pre13 s} Basic assign13 {pre24}" by simp
  hence 15:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre24 s \<and> pre13 s} Basic assign13 {pre24}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre20 s \<and> pre14 s} Basic assign14 {pre20}" by simp
  hence 16:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre20 s \<and> pre14 s} Basic assign14 {pre20}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre21 s \<and> pre14 s} Basic assign14 {pre21}" by simp
  hence 17:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre21 s \<and> pre14 s} Basic assign14 {pre21}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre22 s \<and> pre14 s} Basic assign14 {pre22}" by simp
  hence 18:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre22 s \<and> pre14 s} Basic assign14 {pre22}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre23 s \<and> pre14 s} Basic assign14 {pre23}" by simp
  hence 19:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre23 s \<and> pre14 s} Basic assign14 {pre23}" using hoare_sound_tr by blast
  have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre24 s \<and> pre14 s} Basic assign14 {pre24}" by simp
  hence 20:"\<Turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre24 s \<and> pre14 s} Basic assign14 {pre24}" using hoare_sound_tr by blast
  show ?thesis using 1 2 3 4 5 6 7 8 9 10 11 12 13 14 15 16 17 18 19 20 by auto
qed

lemma "\<turnstile>\<^sub>P {\<lambda>s. s ''f0'' = 0 \<and> s ''d0'' = 0 \<and> s ''f1'' = 0 \<and> s ''d1'' = 0} Parallel Ts {\<lambda>s. s ''f0'' = 0 \<and> s ''d0'' = 4 \<and> s ''f1'' = 0 \<and> s ''d1'' = 4}"
proof -
  have Ind:"Index Ts = {0, Suc 0}"
  proof -
    have "length Ts = 2" by simp
    hence "Index2 Ts = {0, Suc 0}" by auto
    thus ?thesis using Index_Equal by blast
  qed
  have 0:"(Ts!0) = (Some p1, post1)" by simp
  have 1:"(Ts!1) = (Some p2, post2)" by simp
  have pre:"(\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s) = (\<lambda> s . pre10 s \<and> pre20 s)"  using Ind by force 
  have post:"(\<lambda> s . \<forall>i \<in> Index Ts. (post (Ts!i)) s) = (\<lambda>s. post1 s \<and> post2 s)"  using Ind by force 
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
  hence "\<turnstile>\<^sub>P {\<lambda> s . pre10 s \<and> pre20 s} (Parallel Ts) {\<lambda>s. post1 s \<and> post2 s}" using pre post by auto
  thus ?thesis using ParConseq by smt
qed

lemma "\<turnstile>\<^sub>P {\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s} (Parallel Ts) {\<lambda> s . \<forall>i \<in> Index Ts. (post (Ts!i)) s}"
  (is "\<turnstile>\<^sub>P {?P} Parallel ?cs {?Q}")
apply(rule Parallel)
apply(simp_all)
apply(insert equal_bval or_bval Index_Equal[of ?cs])
apply(auto)
apply(simp only:INTERFREE_def)
apply simp
apply(insert insert hoare_sound_tr)
apply(force)
done

end