theory Seperation
imports VCG
begin

type_synonym active_addrs = "nat \<Rightarrow> bool"

type_synonym sepassn = "active_addrs \<Rightarrow> memory \<Rightarrow> bool"

definition dom::"active_addrs \<Rightarrow> nat set" where "dom bs \<equiv> {addr. bs addr}"

datatype sep =
  Points_to "address" "nat" ("_ \<mapsto> _") |
  Conj sep sep ("_ * _")

definition join :: "active_addrs \<Rightarrow> active_addrs \<Rightarrow> active_addrs" where
  "join bs\<^sub>1 bs\<^sub>2 \<equiv> \<lambda> addr . bs\<^sub>1 addr \<or> bs\<^sub>2 addr"

fun eval_sep :: "sep \<Rightarrow> sepassn" where 
  "eval_sep (Points_to a v) = (\<lambda> bs m . m a = v \<and> bs a \<and> (\<forall> a' . a' \<noteq> a \<longrightarrow> \<not> bs a'))" | 
  "eval_sep (Conj P\<^sub>1 P\<^sub>2) = (\<lambda>bs s. \<exists>bs\<^sub>1 bs\<^sub>2. dom bs\<^sub>1 \<inter> dom bs\<^sub>2 = {} \<and> eval_sep P\<^sub>1 bs\<^sub>1 s \<and> eval_sep P\<^sub>2 bs\<^sub>2 s \<and> bs = join bs\<^sub>1 bs\<^sub>2)"

definition mem_eq :: "memory \<Rightarrow> active_addrs \<Rightarrow> (memory set)" where
  "mem_eq m bits \<equiv> { m' . \<forall> addr \<in> dom bits . m' addr = m addr}"

(*
definition is_true :: "assn \<Rightarrow> newstate \<Rightarrow> active_addrs \<Rightarrow> bool" where
  "is_true P s bs \<equiv> P s \<and> (\<forall> m \<in> mem_eq (mem s) bs . P (State m (vars s)))"
*)

definition to_assn where
  "to_assn sep \<equiv> \<lambda>s. \<exists>bs. eval_sep sep bs (mem s)"

lemma l1:
  assumes "eval_sep P bs m" and  "m' \<in> mem_eq m bs" 
  shows "eval_sep P bs m'" using assms
proof (induct arbitrary:bs rule:eval_sep.induct) 
  case 1 thus ?case
  using Seperation.dom_def mem_eq_def by auto
next
  case (2 P1 P2)
  from "2.prems"(1) obtain bs\<^sub>1 bs\<^sub>2 where 
    1:"Seperation.dom bs\<^sub>1 \<inter> Seperation.dom bs\<^sub>2 = {}" and 2:"eval_sep P1 bs\<^sub>1 m" and 3:"eval_sep P2 bs\<^sub>2 m" and 4:"bs = (\<lambda>addr. bs\<^sub>1 addr \<or> bs\<^sub>2 addr)"
    apply (simp_all add:join_def) apply metis done
  from 2 4 1 and "2.prems"(2) and "2.hyps"(1) have 5:"eval_sep P1 bs\<^sub>1 m'"
    by (smt CollectD CollectI Seperation.dom_def mem_eq_def)
  from 3 4 1 and "2.prems"(2) and "2.hyps"(2) have 6:"eval_sep P2 bs\<^sub>2 m'"
    by (smt CollectD CollectI Seperation.dom_def mem_eq_def)
  show ?case using 5 6 1 4 apply(simp add:join_def) by blast
qed

declare [[unify_search_bound=50]]

lemma l2:"\<turnstile>\<^sub>t\<^sub>r { \<lambda> s .True } BASIC (\<lambda> s . State ((mem s)(addr := v)) (vars s)) { to_assn (addr \<mapsto> v) }"
apply (rule Basic)
apply(simp add:to_assn_def)
by fastforce

lemma "\<turnstile>\<^sub>t\<^sub>r { \<lambda> s . \<exists> v' . to_assn (addr \<mapsto> v') s } BASIC (\<lambda> s . State ((mem s)(addr := v)) (vars s)) { to_assn (addr \<mapsto> v) }"
apply (rule Basic)
apply(auto simp add:to_assn_def)
done 

definition condition :: "sep \<Rightarrow> com \<Rightarrow> bool"
  where "condition r c \<equiv> \<forall> bs s s' . eval_sep r bs (mem s) \<and> (Some c,s) \<Rightarrow>\<^sub>t\<^sub>r s' 
    \<longrightarrow> (mem s' \<in> mem_eq (mem s) bs)"

definition bits_minus where "bits_minus bs\<^sub>1 bs\<^sub>2 \<equiv> \<lambda>a . bs\<^sub>1 a \<and> \<not>bs\<^sub>2 a"

lemma l3:
  assumes 1:"bs' = bits_minus bs1 bs2"
  shows "dom bs' \<inter> dom bs2 = {}"
proof-
  have "dom bs' = {addr. (\<lambda>a . bs1 a \<and> \<not>bs2 a) addr}" using 1 unfolding dom_def bits_minus_def by (metis Collect_cong) 
  thus "dom bs' \<inter> dom bs2 = {}" by (metis CollectD Seperation.dom_def disjoint_iff_not_equal)
qed

lemma l4:
  fixes x R s t c bs\<^sub>1
  assumes "condition R c"
  shows "\<And> s t bs\<^sub>1 . \<lbrakk>eval_sep R bs\<^sub>1 (mem s); (Some c, s) \<Rightarrow>\<^sub>t\<^sub>r t; bs\<^sub>1 x\<rbrakk> \<Longrightarrow> (mem s) x = (mem t) x" 
using assms unfolding condition_def mem_eq_def dom_def by (simp)

lemma l4':
  fixes x R s t c bs\<^sub>1 bs\<^sub>2 bs\<^sub>3
  assumes "eval_sep P bs\<^sub>1 (mem s)" and "eval_sep R bs\<^sub>2 (mem s)"and "(Some c, s) \<Rightarrow>\<^sub>t\<^sub>r t" and 
  "\<turnstile>\<^sub>t\<^sub>r {to_assn P} c {to_assn Q}" and "eval_sep Q bs\<^sub>3 (mem s)"and "dom bs\<^sub>1 \<inter> dom bs\<^sub>2 = {}"
  shows "dom bs\<^sub>3 \<inter> dom bs\<^sub>2 = {}"
using assms
proof(induct c arbitrary:P Q)
  case (Cond b c1 c2) thus ?case
  oops

lemma l5:
  fixes x v Q P R  c
  defines "Q \<equiv> x \<mapsto> v"
  assumes "condition R c"
  and 
    "\<And> s t bs\<^sub>1 bs\<^sub>2 . \<lbrakk>eval_sep P bs\<^sub>1 (mem s); (Some c, s) \<Rightarrow>\<^sub>t\<^sub>r t\<rbrakk> \<Longrightarrow> 
      \<exists> bs\<^sub>3 . eval_sep Q bs\<^sub>3 (mem t)"
  and "eval_sep R bs\<^sub>2 (mem s)" and "eval_sep P bs\<^sub>1 (mem s)"
  and "dom bs\<^sub>1 \<inter> dom bs\<^sub>2 = {}" and "(Some c, s) \<Rightarrow>\<^sub>t\<^sub>r t"
  obtains bs\<^sub>3 and bs\<^sub>4 where
  "eval_sep Q bs\<^sub>3 (mem t)" and "eval_sep R bs\<^sub>4 (mem t)" and "dom bs\<^sub>3 \<inter> dom bs\<^sub>4 = {}"
proof - 
  let ?bs\<^sub>4 = "bs\<^sub>2"
  have 1:"eval_sep R ?bs\<^sub>4 (mem t)" using assms(2,4,7) l1 unfolding condition_def by auto
  obtain bs\<^sub>3' where 2:"eval_sep Q bs\<^sub>3' (mem t)" using assms(3,5,7) by blast
  let ?bs\<^sub>3 = "bits_minus bs\<^sub>3' bs\<^sub>2"
  have "eval_sep Q ?bs\<^sub>3 (mem t)" and  "dom ?bs\<^sub>3 \<inter> dom ?bs\<^sub>4 = {}"
  proof -
    show "dom ?bs\<^sub>3 \<inter> dom ?bs\<^sub>4 = {}" unfolding bits_minus_def dom_def by auto
    show "eval_sep Q ?bs\<^sub>3 (mem t)"
    proof -
      { fix s bs
        assume "eval_sep R bs (mem s)"
        have "\<not> bs x" using assms(2,1,3,6)
        unfolding condition_def mem_eq_def dom_def sorry }
      hence "x \<notin> dom bs\<^sub>2" using assms(4) unfolding dom_def sorry
      thus ?thesis using 2 unfolding dom_def bits_minus_def assms(1) by auto
    qed
  qed  
  with 1 and that show ?thesis by auto
qed

lemma frame_rule_particular_case:
  fixes x v
  defines "Q \<equiv> x \<mapsto> v"
  assumes main:"\<Turnstile>\<^sub>t\<^sub>r {to_assn P} c {to_assn Q}" and  cond:"condition R c" 
  shows "\<Turnstile>\<^sub>t\<^sub>r {to_assn (P * R)} c {to_assn (Q * R)}" using assms
proof -(*
  from main obtain bs\<^sub>1 where "\<Turnstile>\<^sub>t\<^sub>r {\<lambda> s. eval_sep P bs\<^sub>1 (mem s)} c {to_assn Q}" using to_assn_def
  by (metis (mono_tags, lifting) hoare_valid_tr_def) 
  with this obtain bs\<^sub>2 where "\<Turnstile>\<^sub>t\<^sub>r {\<lambda> s. eval_sep P bs\<^sub>1 (mem s)} c {\<lambda> s . eval_sep Q bs\<^sub>2 (mem s)}" sorry
  thm hoare_valid_tr_def *)
  { 
    fix s t 
    assume 1:"to_assn (P * R) s" and 2:"(Some c, s) \<Rightarrow>\<^sub>t\<^sub>r t"
    from 2 have 3:"\<And> bs . eval_sep R bs (mem s) \<Longrightarrow> mem t \<in> mem_eq (mem s) bs" using cond 
      unfolding condition_def by fast
    obtain bs\<^sub>1 bs\<^sub>2 bs where 5:"bs = join bs\<^sub>1 bs\<^sub>2" and 6:"dom bs\<^sub>1 \<inter> dom bs\<^sub>2 = {}" and 7:"eval_sep P bs\<^sub>1 (mem s)"
      and 8:"eval_sep R bs\<^sub>2 (mem s)" using 1 apply(auto simp add:to_assn_def join_def dom_def) done
    with 3 l1 have 4:"eval_sep R bs\<^sub>2 (mem t)" by fast
    have 11:"mem t \<in> mem_eq (mem s) bs\<^sub>2" by (simp add: 3 8)
    obtain bs\<^sub>3 where 9:"eval_sep P bs\<^sub>1 (mem s)  \<longrightarrow> eval_sep Q bs\<^sub>3 (mem t)"
      by (metis 2 big_to_small_tr hoare_valid_tr_def main to_assn_def)
    have "eval_sep Q bs\<^sub>3 (mem t)" by (simp add: 7 9)
    have 10:"\<And> s t bs\<^sub>1 bs\<^sub>2 . \<lbrakk>eval_sep P bs\<^sub>1 (mem s); (Some c, s) \<Rightarrow>\<^sub>t\<^sub>r t\<rbrakk> \<Longrightarrow> \<exists> bs\<^sub>3 . eval_sep Q bs\<^sub>3 (mem t)"
      by (metis big_to_small_tr hoare_valid_tr_def main to_assn_def) 
    obtain bs' bs\<^sub>4 where 12:"eval_sep Q bs\<^sub>4 (mem t)" and "eval_sep R bs' (mem t)" and "dom bs\<^sub>4 \<inter> dom bs' = {}"
      using assms(1) l5 cond 10 8 7 6 2
    obtain bs' where "bs' = join bs\<^sub>4 bs\<^sub>2" by simp
    with 4 12 have "to_assn (Q * R) t" using to_assn_def by auto 
  }
  thus ?thesis by (metis hoare_valid_tr_def small_to_big_tr) 

end