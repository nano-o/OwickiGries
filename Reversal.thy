theory Reversal
imports VCG
begin

locale list_rev_example =
fixes i::int and j::int and k::int
begin

abbreviation list_rev where
"list_rev \<equiv> 
  BASIC (\<lambda> s . s(j := 0));;
  WHILE (\<lambda> s . s i \<noteq> 0) 
    INV (\<lambda> s . True)
    DO BASIC (\<lambda>s. s(k := s (i + 1), s (i + 1) := j, j := i, i := k))
    OD"

abbreviation pre0::"assn" where "pre0 \<equiv> \<lambda>s. \<exists>\<alpha> \<beta>. (list s \<alpha> i) \<and> (list s \<beta> j) \<and> (rev \<alpha> = (append (rev \<alpha>) \<beta>))"

abbreviation loopcom::"newstate \<Rightarrow> newstate" where 
"loopcom \<equiv> \<lambda>s. s(k := s (i + 1), s (i + 1) := j, j := i, i := k)"

abbreviation revers::

end
end