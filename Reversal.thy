theory Reversal
imports VCG
begin

locale list_rev_example =
fixes i::string and j::string and k::string
begin

abbreviation update_mem
  where "update_mem f s \<equiv> State (f (mem s)) (vars s)"

abbreviation list_rev where
"list_rev \<equiv> 
  BASIC (\<lambda> s . let loc_j = (vars s) j in update_mem (\<lambda> m . m(loc_j := 0)) s)"

abbreviation pre0::"assn" where "pre0 \<equiv> \<lambda>s. \<exists>\<alpha> \<beta>. (list s \<alpha> i) \<and> (list s \<beta> j) \<and> (rev \<alpha> = (append (rev \<alpha>) \<beta>))"

abbreviation loopcom::"newstate \<Rightarrow> newstate" where 
"loopcom \<equiv> \<lambda>s. s(k := s (i + 1), s (i + 1) := j, j := i, i := k)"

abbreviation revers::

end
end