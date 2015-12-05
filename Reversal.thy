theory Reversal
imports VCG
begin

abbreviation pre0::"assn" where "pre0 \<equiv> \<lambda>s. \<exists>\<alpha> \<beta>. (list s \<alpha> i) \<and> (list s \<beta> j) \<and> (rev \<alpha> = (append (rev \<alpha>) \<beta>))"

abbreviation loopcom::"newstate \<Rightarrow> newstate" where 
"loopcom \<equiv> \<lambda>s. s(k := s (i + 1), s (i + 1) := j, j := i, i := k)"

abbreviation revers::

abbreviation 

end