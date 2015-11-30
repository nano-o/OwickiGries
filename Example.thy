theory Example
imports Proof_Par
begin

text {* Goal: \<turnstile>\<^sub>P {x = 0} x := x+1 || x:= x+1 {x = 2} *}

text {* 
Annotated program: 
  {x = 0, d1 = false, ...} (x := x+1, d1 := true) {x = x+1} 
  || 
  {x = 0, d2 = false, ...} (x:= x+1, d2 := true) {x = x+1} 

Goal: \<turnstile>\<^sub>P {x = 0, d1 = false, d2 = false} x := x+1 || x:= x+1 {x = 2}
*}

abbreviation "pre1 \<equiv> \<lambda> s . True"
abbreviation "pre2 \<equiv> \<lambda> s . True"
abbreviation "post1 \<equiv> \<lambda> s . True"
abbreviation "post2 \<equiv> \<lambda> s . True"

abbreviation "plus11 \<equiv> \<lambda>s. s(''x'' := s ''x'' + 1, ''d1'' := 1)"

abbreviation "plus12 \<equiv> \<lambda>s. s(''x'' :=  s ''x'' + 1, ''d2'' := 1)"

abbreviation "plus2 ==
  Parallel [((Some (ABasic pre1 (plus11))), post1),
    ((Some (ABasic pre2 (plus12))), post2)]"

subsubsection{* Proof by Hoare Logic *}

lemma "\<turnstile>\<^sub>P {\<lambda>s. s ''x'' = 0} plus2 {\<lambda>s. s ''x'' = 2}"
apply(rule PParallelE)

end