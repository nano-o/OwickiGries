theory Reversal
imports VCG
begin

locale list_rev_example =
fixes i::string and j::string and k::string and it::int
begin

abbreviation update_mem
  where "update_mem f s \<equiv> State (f (mem s)) (vars s)"

abbreviation init where
"init \<equiv> BASIC (\<lambda>s. update_mem (\<lambda>m . m((vars s) j := 0, it := (vars s) i)) s)"

abbreviation list_rev where
"list_rev \<equiv> BASIC (\<lambda>s. update_mem (\<lambda>m . m((vars s) k := (mem s) ((vars s) i + 1), (mem s) ((vars s) i + 1) := (vars s) j, (vars s) j := (vars s) i, (vars s) i := (vars s) k)) s)"

abbreviation pre0::"assn" where "pre0 \<equiv> \<lambda>s. \<exists>\<alpha> \<beta>. (list s \<alpha> ((vars s) i)) \<and> (list s \<beta> ((vars s) j)) \<and> (rev \<alpha> = (append (rev \<alpha>) \<beta>)) \<and> 
  (\<forall>k::string. (reach s ((vars s) i) ((vars s) k)) \<and> (reach s ((vars s) j) ((vars s) k)) \<longrightarrow> ((vars s) k = 0))"

abbreviation inv::"assn" where "inv \<equiv> \<lambda>s. \<exists>\<alpha> \<beta> \<alpha>\<^sub>0. (list s \<alpha> ((vars s) i)) \<and> (list s \<beta> ((vars s) j))  \<and> (list s \<alpha>\<^sub>0 it) \<and> (rev \<alpha>\<^sub>0 = (append (rev \<alpha>) \<beta>)) \<and> 
  (\<forall>k::string. (reach s ((vars s) i) ((vars s) k)) \<and> (reach s ((vars s) j) ((vars s) k)) \<longrightarrow> ((vars s) k = 0))"

abbreviation post::"assn" where "post \<equiv> \<lambda>s. \<exists>\<alpha> \<beta> \<alpha>\<^sub>0. (list s \<alpha> ((vars s) i)) \<and> (list s \<beta> ((vars s) j)) \<and> (list s \<alpha>\<^sub>0 it) \<and> (rev \<alpha>\<^sub>0 = (append (rev \<alpha>) \<beta>)) \<and> 
  (\<forall>k::string. (reach s ((vars s) i) ((vars s) k)) \<and> (reach s ((vars s) j) ((vars s) k)) \<longrightarrow> ((vars s) k = 0))"

abbreviation loopcom::com where 
"loopcom \<equiv> init;; WHILE (\<lambda>s. (vars s) i \<noteq> 0) INV inv DO list_rev OD"

lemma "\<turnstile>\<^sub>t\<^sub>r {pre0} loopcom {post}"
apply(rule Seq)
prefer 2
apply(rule While [where P = inv])
apply simp
sorry

end

end