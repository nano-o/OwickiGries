theory Example
imports VCG  "~~/src/HOL/Eisbach/Eisbach_Tools"
begin

section {* Increment by two example *}

text {* Goal: \<turnstile>\<^sub>P {x = 0} x := x+1 || x:= x+1 {x = 2} *}

text {* 
We add the auxiliary variables d1 and d2 (for done1 and done2).

Annotated program: 
  {@{term "d1 = 0 \<and> (d2 = 0 \<longrightarrow> x = 0) \<and> (d2 = 1 \<longrightarrow> x = 1)"}} 
  (x := x+1, d1 := true) 
  {@{term "d1 = 1 \<and> (d2 = 0 \<longrightarrow> x = 1) \<and> (d2 = 1 \<longrightarrow> x = 2)"}} 
  || 
  {@{term "d2 = 0 \<and> (d1 = 0 \<longrightarrow> x = 0) \<and> (d1 = 1 \<longrightarrow> x = 1)"}} 
  (x:= x+1, d2 := true)
  {@{term "d2 = 1 \<and> (d1 = 0 \<longrightarrow> x = 1) \<and> (d1 = 1 \<longrightarrow> x = 2)"}}

Goal: \<turnstile>\<^sub>P {x = 0, d1 = false, d2 = false} x := x+1 || x:= x+1 {x = 2}
*}

abbreviation pre1 :: "assn" where 
  "pre1 \<equiv> \<lambda>s. s ''d1'' = 0 \<and> (s ''d2'' = 0 \<longrightarrow> s ''x'' = 0) \<and> (s ''d2'' = 1 \<longrightarrow> s ''x'' = 1)"
abbreviation pre2  :: "assn" where 
  "pre2 \<equiv> \<lambda>s. s ''d2'' = 0 \<and> (s ''d1'' = 0 \<longrightarrow> s ''x'' = 0) \<and> (s ''d1'' = 1 \<longrightarrow> s ''x'' = 1)"
abbreviation post1 :: "assn" where 
  "post1 \<equiv> \<lambda>s. s ''d1'' = 1 \<and> (s ''d2'' = 0 \<longrightarrow> s ''x'' = 1) \<and> (s ''d2'' = 1 \<longrightarrow> s ''x'' = 2)"
abbreviation post2  :: "assn" where 
  "post2 \<equiv> \<lambda>s. s ''d2'' = 1 \<and> (s ''d1'' = 0 \<longrightarrow> s ''x'' = 1) \<and> (s ''d1'' = 1 \<longrightarrow> s ''x'' = 2)"

abbreviation plus11  :: "state \<Rightarrow> state" where 
  "plus11 \<equiv> \<lambda>s. s(''x'' := s ''x'' + 1, ''d1'' := 1)"
abbreviation plus12  :: "state \<Rightarrow> state" where 
  "plus12 \<equiv> \<lambda>s. s(''x'' :=  s ''x'' + 1, ''d2'' := 1)"

abbreviation "C2 \<equiv> ABasic pre2 (plus12)"
abbreviation "C1 \<equiv> ABasic pre1 (plus11)"

abbreviation Ts :: "((acom option \<times> assn) list)" where 
  "Ts \<equiv> [(Some C1, post1), (Some C2, post2)]"

subsubsection{* Proof by Hoare Logic *}

lemma "\<turnstile>\<^sub>P {\<lambda>s. s ''x'' = 0 \<and> s ''d1'' = 0 \<and> s ''d2'' = 0} Parallel Ts {\<lambda>s. s ''x'' = 2}"
proof -
  text {* We will use the rule Parallel of the definition of @{term "hoare_par"}} to obtain 
    @{term "\<turnstile>\<^sub>P {\<lambda> s . pre1 s \<and> pre2 s} (Parallel Ts) {\<lambda>s. post1 s \<and> post2 s}"}.
    We will finally reach our goal by strengthening the precondition and weakening the postcondition *}
  text {* An auxiliary lemma *}
  have index:"Index Ts = {0,1::nat}"
  proof -
    have "Index Ts = Index2 Ts" using Index_Equal by blast
    also have "... = {0,1::nat}" by auto
    finally show ?thesis by auto
  qed
  have "\<turnstile>\<^sub>P {\<lambda> s . pre1 s \<and> pre2 s} (Parallel Ts) {\<lambda>s. post1 s \<and> post2 s}"
  proof -
    text {* We establish the two premises of the rule Parallel separately *}
    have premise1:"(\<forall>i \<in> Index Ts. \<exists>(c::acom) Q. (Ts!i) = (Some c, Q) \<and> (\<turnstile> c {Q}))" 
      using index by simp 
    have premise2:"INTERFREE Ts"
    proof -
      have "interfree (com(Ts ! 0), post(Ts ! 0), com(Ts!1))"
      proof -
        have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post1 s \<and> pre2 s} Basic plus12 {post1}" by auto
        moreover have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre1 s \<and> pre2 s} Basic plus12 {pre1}" by auto
        ultimately show ?thesis using hoare_sound_tr by auto
      qed
      moreover
      have "interfree(com(Ts ! 1), post(Ts ! 1), com(Ts!0))"
      proof -
        have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. post2 s \<and> pre1 s} Basic plus11 {post2}" by auto
        moreover have "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. pre2 s \<and> pre1 s} Basic plus11 {pre2}" by auto
        ultimately show ?thesis using hoare_sound_tr  by auto
      qed
      ultimately show ?thesis using index INTERFREE_def by auto
    qed
    text {* Then we establish the pre and post used in the Parallel rule *}
    have pre:"(\<lambda> s . \<forall>i \<in> Index Ts. (pre (the (com(Ts!i)))) s) = (\<lambda> s . pre1 s \<and> pre2 s)" 
      using index by force 
    have post:"(\<lambda> s . \<forall>i \<in> Index Ts. (post (Ts!i)) s) = (\<lambda>s. post1 s \<and> post2 s)"
      using index  by force 
    from premise1 premise2 pre post show ?thesis using Parallel[where ?Ts="Ts"] index by auto
  qed
  thus ?thesis using ParConseq
    by smt
qed

section {* Let's try to automate the proof *}

text {* Note: difference between a goal state of the form "A ==> B" and assumes "A" shows "B",
  i.e. local context vs goal state. This influences how automated methods work (even intro) *}

text {* auto_solve starts by computing the set of indices, then applies ParConseq and Parallel, and 
solves as many goals as possible with simp and force. Only the INTERFREE goal should then remain.
At this point, auto_solve tries to finish by inserting hoare_sound_tr and calling force. *}

method auto_solve = 
(match conclusion in "\<turnstile>\<^sub>P {P} Parallel cs {Q}" for P cs Q \<Rightarrow> 
  \<open>insert Index_Equal[of cs], 
    simp,
    rule ParConseq[where ?P = "\<lambda> s . \<forall>i \<in> Index cs. (pre (the (com(cs!i)))) s" 
    and ?Q="\<lambda> s . \<forall>i \<in> Index cs. (post (cs!i)) s"];
    (rule Parallel)?;
    (simp? | force?)\<close>),
(simp only:INTERFREE_def), 
simp; 
insert hoare_sound_tr,
force

lemma "\<turnstile>\<^sub>P {\<lambda>s. s ''x'' = 0 \<and> s ''d1'' = 0 \<and> s ''d2'' = 0} Parallel Ts {\<lambda>s. s ''x'' = 2}"
by auto_solve

end