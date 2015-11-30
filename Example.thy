theory Example
imports Proof_Par
begin

abbreviation "wsum ==
  Parallel [((Some (ABasic (\<lambda>s. s ''x'' = (0::int)) (\<lambda>s. s(''x'' := aval (Plus (V ''x'') (N 1)) s)))),(\<lambda>s. s ''x'' = aval (Plus (V ''x'') (N 1)) s)),
    ((Some (ABasic (\<lambda>s. s ''x'' = (0::int)) (\<lambda>s. s(''x'' := aval (Plus (V ''x'') (N 1)) s)))),(\<lambda>s. s ''x'' = aval (Plus (V ''x'') (N 1)) s))]"

subsubsection{* Proof by Hoare Logic *}

text{* Note that we deal with sequences of commands from right to left,
pulling back the postcondition towards the precondition. *}

lemma "\<turnstile>\<^sub>P {\<lambda>s. s x = 0} wsum {\<lambda>s. s x = 2}"
apply(rule PParallelE)

end