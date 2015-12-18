theory Reversal
imports VCG
begin

locale list_rev_example =
fixes i::string and j::string and k::string and \<alpha>\<^sub>0::"nat list"
assumes a1:"i \<noteq> k" and a2:"i \<noteq> j" and a3:"j \<noteq> k"
begin

abbreviation update_mem
  where "update_mem f s \<equiv> State (f (mem s)) (vars s)"

abbreviation init where
"init \<equiv> BASIC (\<lambda>s. State (mem s) ((vars s)(j := 0)))"

abbreviation all where
"all \<equiv> BASIC (\<lambda>s. State ((mem s)((mem s) (((vars s) i) + 1) := (vars s) j)) ((vars s)(k := (mem s) ((vars s) i + 1), j := (vars s) i, i := (mem s)(((vars s) i) + 1))))"

abbreviation assign1 where
"assign1 \<equiv> BASIC (\<lambda>s. State (mem s) ((vars s)(k := (mem s) ((vars s) i + 1))))"

abbreviation assign2 where
"assign2 \<equiv> BASIC (\<lambda>s. State ((mem s)((mem s) ((vars s) i + 1) := (vars s) j)) (vars s))"

abbreviation assign3 where
"assign3 \<equiv> BASIC (\<lambda>s. State (mem s) ((vars s)(j := (vars s) i)))"

abbreviation assign4 where
"assign4 \<equiv> BASIC (\<lambda>s. State (mem s) ((vars s)(i := (vars s) k)))"

fun list :: "newstate \<Rightarrow> (nat list) \<Rightarrow> nat \<Rightarrow> bool" where 
"list s [] a = (a = 0)"|
"list s (x#xs) a = (odd a \<and> (mem s) a = x \<and> ((mem s) (a + 1)) \<noteq> a \<and>list s xs ((mem s) (a + 1)))"

definition reach1 :: "newstate \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "reach1 s p q \<equiv> ((mem s) (p + 1)) = q"

definition reach :: "newstate \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "reach s x y \<equiv> star (reach1 s) x y"

abbreviation pre0::"assn" where "pre0 \<equiv> \<lambda>s. \<exists>\<alpha> \<beta>. ((vars s) i \<noteq> 0) \<and> ((vars s) j = 0) \<and> (list s  \<alpha>\<^sub>0 ((vars s) i)) \<and>  (list s \<alpha> ((vars s) i)) \<and> 
  (list s \<beta> 0) \<and> (rev \<alpha>\<^sub>0 = (append (rev \<alpha>) \<beta>)) \<and> (\<forall>k::string. (reach s ((vars s) i) ((vars s) k)) \<and> (reach s ((vars s) j) ((vars s) k)) \<longrightarrow> ((vars s) k = 0))"

definition inv::"assn" where "inv \<equiv> \<lambda>s. \<exists>\<alpha> \<beta>. (list s \<alpha> ((vars s) i)) \<and> (list s \<beta> ((vars s) j)) \<and> (rev \<alpha>\<^sub>0 = (append (rev \<alpha>) \<beta>))
  \<and> (\<forall> v . (reach s ((vars s) i) v) \<and> (reach s ((vars s) j) v) \<longrightarrow> v = 0)"

abbreviation post::"assn" where "post \<equiv> \<lambda>s. \<exists>\<alpha> \<beta>. (list s \<alpha> 0) \<and> (list s \<beta> ((vars s) j)) \<and> (rev \<alpha>\<^sub>0 = (append (rev \<alpha>) \<beta>)) \<and> 
  (\<forall>k::string. (reach s 0 ((vars s) k)) \<and> (reach s ((vars s) j) ((vars s) k)) \<longrightarrow> ((vars s) k = 0))"

abbreviation loopcom::com where 
"loopcom \<equiv> init;; WHILE (\<lambda>s. (vars s) i \<noteq> 0) INV inv DO all OD"

lemma l2:
  fixes s s' l v
  assumes "mem s = mem s'"
  shows "list s l v = list s' l v" using assms
by (induct rule: list.induct) simp_all

lemma l3:
  fixes s s'
  assumes "list s l ((vars s) v)" and "mem s = mem s'" and "(vars s) v = ((vars s') v)"
  shows "list s' l ((vars s') v)" using assms
by (metis l2) 

lemma l5:
  fixes s s' v addr
  assumes "mem s = mem s'"
  shows "reach s addr v = reach s' addr v" 
proof - 
  have "\<And> p q . reach1 s p q = reach1 s' p q" unfolding reach1_def using assms by simp
  thus ?thesis unfolding reach_def by presburger
qed

lemma l6:
  fixes s v
  assumes "local.inv s"
  shows "local.inv (State (mem s) ((vars s)(k := v)))"
using assms
by (smt a1 a3 fun_upd_apply l2 l5 local.inv_def newstate.sel(1) newstate.sel(2)) 

lemma l7:
  assumes "list s \<alpha> a1" and "odd a2" and "(mem s) a2 = v" and "(mem s) (a2 + 1) = a1"
  shows "list s (v#\<alpha>) a2" using assms
proof (induct \<alpha>, simp_all)
  assume "a1 = 0" and "mem s (Suc a2) = 0" and "list s \<alpha> 0" and "odd a2"
  thus "0 < a2" by (simp add: odd_pos)
next
  fix a \<alpha>'
  assume "(list s \<alpha>' a1 \<Longrightarrow> a1 \<noteq> a2)" and "odd a1" and "mem s a1 = a" and "mem s (Suc a1) \<noteq> a1" and "list s \<alpha>' (mem s (Suc a1))" and 
    "mem s (Suc a2) = a1" and "list s \<alpha> a1" and "odd a2" and "mem s a2 = v"
  thus "a1 \<noteq> a2" by blast


(*lemma l8:
  assumes "list s \<alpha> addr" and "\<alpha> \<noteq> []"
  shows "(mem s) (addr + 1) \<noteq> addr" using assms
  proof (induct \<alpha>)
    print_cases
    case (Cons x xs) thus ?case nitpick
    apply (induct xs) 
  *)

lemma "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. \<exists>\<alpha> \<beta>. (\<alpha> \<noteq> []) \<and> (list s \<alpha> ((vars s) i)) \<and> (list s \<beta> ((vars s) j)) \<and> (rev \<alpha>\<^sub>0 = (append (rev \<alpha>) \<beta>))
  \<and> (\<forall> v . (reach s ((vars s) i) v) \<and> (reach s ((vars s) j) v) \<longrightarrow> v = 0)} 
  BASIC (\<lambda> s . State (mem s) ((vars s)(k := ((mem s) (((vars s) i) + 1)))))
    {\<lambda>s. \<exists>\<alpha> \<beta>. (\<alpha> \<noteq> []) \<and> (list s \<alpha> ((vars s) i)) \<and> (list s \<beta> ((vars s) j)) \<and> (rev \<alpha>\<^sub>0 = (append (rev \<alpha>) \<beta>))
  \<and> (\<forall> v . (reach s ((vars s) i) v) \<and> (reach s ((vars s) j) v) \<longrightarrow> v = 0) \<and> list s (tl \<alpha>) ((vars s) k) }"
proof (rule Basic, clarify)
    fix s \<alpha> \<beta>
    def s' \<equiv> "State (mem s) ((vars s)(k := ((mem s) (((vars s) i) + 1))))"
    assume 0:"\<alpha> \<noteq> []" and 1:"list s \<alpha> (vars s i)" and 2:"list s \<beta> (vars s j)" and 3:"rev \<alpha>\<^sub>0 = rev \<alpha> @ \<beta>" 
    and 4:"\<forall>v. reach s (vars s i) v \<and> reach s (vars s j) v \<longrightarrow> v = 0"
    hence 5:"(\<alpha> \<noteq> []) \<and> list s' \<alpha> (vars s' i) \<and>
      list s' \<beta> ((vars s') j) \<and> rev \<alpha>\<^sub>0 = rev \<alpha> @ \<beta>" by (simp add: 1 2 a1 a3 l2 s'_def) 
    have 6:"(\<forall>v. reach s' (vars s' i) v \<and>
         reach s' (vars s' j) v \<longrightarrow> v = 0)" by (metis "4" a1 a3 fun_upd_apply l5 newstate.sel(1) newstate.sel(2) s'_def)
    have 7:"list s' (tl \<alpha>) (vars s' k)" unfolding s'_def
      by (metis 0 1 Ann_Com.list.simps(2) fun_upd_apply l2 list.collapse newstate.sel(1) newstate.sel(2))
    show "\<exists>\<alpha> \<beta>. \<alpha> \<noteq> [] \<and> list s' \<alpha> (vars s' i) \<and> list s' \<beta> (vars s' j) \<and> rev \<alpha>\<^sub>0 = rev \<alpha> @ \<beta> \<and>
      (\<forall>v. reach s' (vars s' i) v \<and> reach s' (vars s' j) v \<longrightarrow> v = 0) \<and> list s' (tl \<alpha>) (vars s' k)"
    using 5 6 7 unfolding s'_def by blast
qed

lemma l10:
  assumes  "\<And> v . reach s p v \<Longrightarrow> odd v"
  shows  "\<And> v . reach s ((mem s) (p + 1)) v \<Longrightarrow> odd v"
  using assms 
  proof -
  fix v 
  assume "reach s ((mem s) (p + 1)) v" 
  thus "odd v" using assms unfolding reach_def thm star.induct
  proof (induct "((mem s) (p + 1))" v rule: star.induct[where r="reach1 s"])
    case refl thus ?case
      using reach1_def by blast 
    next
    print_cases
    case step 
    from step.hyps(1,2) step.prems show ?case
      by (meson reach1_def star.simps) 
  qed
qed

lemma l9:
  fixes x s l
  assumes "\<And> v . reach s p v \<Longrightarrow> (v \<noteq> q)" 
  and "s' = State ((mem s)((q + 1) := x)) (vars s)"
  and "list s l p"
  and "odd p" and "odd q"
  and "\<And> v . reach s p v \<Longrightarrow> odd v"
  shows "list s' l p" using assms 
proof (induct l arbitrary: p)
  case Nil thus ?case by auto
next
  case (Cons x xs)
  have "list s' xs ((mem s)(p + 1))"
  proof -
    let ?p'= "(mem s)(p + 1)"
    have "list s xs ?p'" 
      using Cons.prems(3) by auto
    moreover have "\<And> v . reach s ?p' v \<Longrightarrow> (v \<noteq> q)"
      by (metis Cons.prems(1) reach1_def reach_def star.simps) 
    moreover have "odd ?p'" 
      by (metis Cons.prems(6) reach1_def reach_def star.simps) 
    moreover have "\<And> v . reach s ?p' v \<Longrightarrow> odd v" using l10
      using Cons.prems(6) by blast 
    ultimately
    show ?thesis using Cons.hyps assms(2) assms(5) by smt
  qed
  moreover have "((mem s) p) = x"
    by (metis Ann_Com.list.simps(2) Cons.prems(3)) 
  ultimately show ?case
  by (metis (no_types, lifting) Ann_Com.list.simps(2) Cons.prems(1) Cons.prems(4) add_diff_cancel_right' assms(2) assms(5) fun_upd_apply newstate.sel(1) odd_even_add odd_one reach_def star.refl) 
qed

lemma "\<turnstile>\<^sub>t\<^sub>r {\<lambda>s. \<exists>\<alpha> \<beta>. (\<alpha> \<noteq> []) \<and> (list s \<alpha> ((vars s) i)) \<and> (list s \<beta> ((vars s) j)) \<and> (rev \<alpha>\<^sub>0 = (append (rev \<alpha>) \<beta>))
  \<and> (\<forall> v . (reach s ((vars s) i) v) \<and> (reach s ((vars s) j) v) \<longrightarrow> v = 0) \<and> list s (tl \<alpha>) ((vars s) k)} 
  BASIC (\<lambda>s. State ((mem s)(((vars s) i + 1) := (vars s) j)) (vars s)) 
  {\<lambda>s. \<exists>\<alpha> \<beta>. (list s \<alpha> ((vars s) k)) \<and> (list s \<beta> ((vars s) i)) \<and> (rev \<alpha>\<^sub>0 = (append (rev \<alpha>) \<beta>))
  \<and> (\<forall> v . (reach s ((vars s) k) v) \<and> (reach s ((vars s) i) v) \<longrightarrow> v = 0)}"
proof (rule Basic, clarify)
  fix s \<alpha> \<beta>
  def s' \<equiv> "State ((mem s)(((vars s) i + 1) := (vars s) j)) (vars s)"
  assume 0:"\<alpha> \<noteq> []" and 1:"list s \<alpha> (vars s i)" and 2:"list s \<beta> (vars s j)" and 3:"rev \<alpha>\<^sub>0 = rev \<alpha> @ \<beta>"
    and 4:"\<forall>v. reach s ((vars s) i) v \<and> reach s ((vars s) j) v \<longrightarrow> v = 0" and 5:"list s (tl \<alpha>) ((vars s) k)"
  have "odd (vars s i)" using 0 1 using list.elims(2) by blast 
  have "odd (vars s j) \<or> (vars s j) = 0" using 2
  hence 6:"list s' \<beta> (vars s' j)"
  proof-
  {
    assume "odd (
 using 2 4 l9 unfolding s'_def
  have "odd (vars s' i) \<and> (mem s') (vars s' i) = hd(\<alpha>)" unfolding s'_def (*
    by (metis 0 1 even_plus_one_iff fun_upd_other list.elims(2) list.sel(1) newstate.sel(1) newstate.sel(2))
  hence 7:"list s' (hd(\<alpha>)#\<beta>) (vars s' i)" using 6 by (simp add: s'_def)
  have 7:"list s' (tl \<alpha>) (vars s' k)" using 5 unfolding s'_def*)

qed

lemma "\<turnstile>\<^sub>t\<^sub>r {\<lambda> s . \<alpha> \<noteq> [] \<and> ((vars s) i \<noteq> 0) \<and> inv s \<and> list s (tl \<alpha>) ((vars s) k) \<and> list s \<alpha> ((vars s) i) \<and> list s \<beta> ((vars s) j)} 
  BASIC (\<lambda>s. State ((mem s)((mem s) ((vars s) i + 1) := (vars s) j)) (vars s)) 
  {\<lambda> s . \<alpha> \<noteq> [] \<and> ((vars s) i \<noteq> 0) \<and> list s (tl \<alpha>) ((vars s) k) \<and> list s \<beta> ((vars s) j) \<and> list s ((hd \<alpha>)#\<beta>) ((vars s) i)}"
apply (rule Basic) 

lemma "inv s \<Longrightarrow> pre_tr all local.inv s" *)


(*lemma "\<turnstile>\<^sub>t\<^sub>r {pre0} loopcom {post}"
apply(rule Seq[where Q=inv])
apply(rule Basic)
apply (metis fun_upd_triv newstate.collapse)
apply(rule While)
apply simp
prefer 2
apply force
apply(insert vc_sound_tr[where Q="inv" and c="((assgin1;; assgin2);; assign3);; assign4"])
apply(rule conseq[where P="pre_tr ((assgin1;; assgin2);; assign3);; assign4 local.inv" and P'="\<lambda>s. local.inv s \<and> vars s i \<noteq> 0" and Q="inv" and Q'="inv"])
prefer 3




prefer 2
apply(rule While [where P = inv])
apply simp
prefer 2
apply force
prefer 2
apply(rule Basic)
apply simp
apply(smt fun_upd_triv newstate.collapse)
apply (rule Seq [where Q = "\<lambda>s. local.inv s \<and> vars s i \<noteq> 0"])
prefer 2
apply(rule Basic)
apply simp
proof
  fix s
  have "(j = i \<longrightarrow>
         (\<exists>\<alpha>. list s \<alpha> (vars s i) \<and> (\<exists>\<beta>. list s \<beta> (vars s i) \<and> rev \<alpha>\<^sub>0 = rev \<alpha> @ \<beta> \<and> (\<forall>k. reach s (vars s i) (vars s k) \<longrightarrow> vars s k = 0))) \<and> vars s i \<noteq> 0 \<longrightarrow>
         (\<exists>\<alpha>. list (State (mem s) ((vars s)(i := vars s k))) \<alpha> (vars s k) \<and>
               (\<exists>\<beta>. list (State (mem s) ((vars s)(i := vars s k))) \<beta> (vars s k) \<and>
                    rev \<alpha>\<^sub>0 = rev \<alpha> @ \<beta> \<and>
                    (\<forall>ka. (ka = i \<longrightarrow> reach (State (mem s) ((vars s)(i := vars s k))) (vars s k) (vars s k) \<longrightarrow> vars s k = 0) \<and>
                          (ka \<noteq> i \<longrightarrow> reach (State (mem s) ((vars s)(i := vars s k))) (vars s k) (vars s ka) \<longrightarrow> vars s ka = 0)))))"
using reach_def reach_step.simps(1) by blast
  have " j \<noteq> i \<longrightarrow>
          (\<exists>\<alpha>. list s \<alpha> (vars s i) \<and> (\<exists>\<beta>. list s \<beta> (vars s j) \<and> rev \<alpha>\<^sub>0 = rev \<alpha> @ \<beta> \<and> (\<forall>k. reach s (vars s i) (vars s k) \<and> reach s (vars s j) (vars s k) \<longrightarrow> vars s k = 0))) \<and>
          vars s i \<noteq> 0 \<longrightarrow>
          (\<exists>\<alpha>. list (State (mem s) ((vars s)(i := vars s k))) \<alpha> (vars s k) \<and>
                (\<exists>\<beta>. list (State (mem s) ((vars s)(i := vars s k))) \<beta> (vars s j) \<and>
                     rev \<alpha>\<^sub>0 = rev \<alpha> @ \<beta> \<and>
                     (\<forall>ka. (ka = i \<longrightarrow>
                            reach (State (mem s) ((vars s)(i := vars s k))) (vars s k) (vars s k) \<and> reach (State (mem s) ((vars s)(i := vars s k))) (vars s j) (vars s k) \<longrightarrow>
                            vars s k = 0) \<and>
                           (ka \<noteq> i \<longrightarrow>
                            reach (State (mem s) ((vars s)(i := vars s k))) (vars s k) (vars s ka) \<and> reach (State (mem s) ((vars s)(i := vars s k))) (vars s j) (vars s ka) \<longrightarrow>
                            vars s ka = 0))))"
  proof

sorry
*)
end

end