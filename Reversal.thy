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

lemma l4:
  fixes s s' l v
  assumes "mem s = mem s'"
  shows "reach_step s n addr v = reach_step s' n addr v" using assms
apply (induct rule:reach_step.induct) apply auto done

lemma l5:
  fixes s s' l v
  assumes "mem s = mem s'"
  shows "reach s addr v = reach s' addr v" using assms
by (metis l4 reach_def)

lemma l6:
  fixes s v
  assumes "local.inv s"
  shows "local.inv (State (mem s) ((vars s)(k := v)))"
using assms
by (smt a1 a3 fun_upd_apply l2 l5 local.inv_def newstate.sel(1) newstate.sel(2)) 

lemma l7:
  assumes "list s \<alpha> a1" and "(mem s) a2 = v" and "(mem s) (a2 + 1) = a1"
  shows "list s (v#\<alpha>) a2" using assms
by (induct \<alpha>) simp_all

(*lemma l8:
  assumes "list s \<alpha> addr" and "\<alpha> \<noteq> []"
  shows "(mem s) (addr + 1) \<noteq> addr" using assms
  proof (induct \<alpha>)
    print_cases
    case (Cons x xs) thus ?case nitpick
    apply (induct xs) 
  *)

(*lemma "\<turnstile>\<^sub>t\<^sub>r {\<lambda> s . \<alpha> \<noteq> [] \<and> ((vars s) i \<noteq> 0) \<and> inv s \<and> list s \<alpha> ((vars s) i) \<and> list s \<beta> ((vars s) j)} BASIC (\<lambda> s . State (mem s) ((vars s)(k := ((mem s) (((vars s) i) + 1))))) 
  {\<lambda> s . \<alpha> \<noteq> [] \<and> ((vars s) i \<noteq> 0) \<and> inv s \<and> list s (tl \<alpha>) ((vars s) k) \<and> list s \<alpha> ((vars s) i) \<and> list s \<beta> ((vars s) j) \<and> ((vars s) k) \<noteq> ((vars s) i) + 1}" 
apply (rule Basic)
by (smt Ann_Com.list.simps(2) a1 a3 fun_upd_apply l2 l6 list.collapse newstate.sel(1) newstate.sel(2)) 

lemma "\<turnstile>\<^sub>t\<^sub>r {\<lambda> s . \<alpha> \<noteq> [] \<and> ((vars s) i \<noteq> 0) \<and> inv s \<and> list s (tl \<alpha>) ((vars s) k) \<and> list s \<alpha> ((vars s) i) \<and> list s \<beta> ((vars s) j)} 
  BASIC (\<lambda>s. State ((mem s)(((vars s) i + 1) := (vars s) j)) (vars s)) 
  {\<lambda> s . \<alpha> \<noteq> [] \<and> ((vars s) i \<noteq> 0) \<and> list s (tl \<alpha>) ((vars s) k)}"
apply (rule Basic) nitpick[show_consts]

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