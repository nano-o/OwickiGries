theory NFormula
imports NStep
begin

type_synonym assn = "newstate \<Rightarrow> bool"

type_synonym active_addrs = "nat \<Rightarrow> bool"

definition dom::"active_addrs \<Rightarrow> nat set" where "dom bs \<equiv> {addr. bs addr}"

datatype formula = Bc bool | 
  Not formula| 
  And formula formula|
  Or formula formula| 
  Less aexp aexp|
  Greater aexp aexp|
  Equal aexp aexp|
  Imp formula formula|
  Forall vname formula| 
  Exist vname formula|
  Points_to aexp aexp ("_ \<mapsto> _")|
  Conj formula formula ("_ * _")

fun extFree::"aexp \<Rightarrow> vname list" where
"extFree (N n) = []"|
"extFree (V v) = [v]"|
"extFree (Plus a1 a2) = (extFree a1) @ (extFree a2)"

fun extractFree::"formula \<Rightarrow> vname list" where
"extractFree (Bc b) = []"|
"extractFree (Not f) = (extractFree f)"|
"extractFree (And f1 f2) = (extractFree f1) @ (extractFree f2)"|
"extractFree (Or f1 f2) = (extractFree f1) @ (extractFree f2)"|
"extractFree (Less a1 a2) = ((extFree a1) @ (extFree a2))"|
"extractFree (Greater a1 a2) = ((extFree a1) @ (extFree a2))"|
"extractFree (Equal a1 a2) = ((extFree a1) @ (extFree a2))"|
"extractFree (Imp f1 f2) = (extractFree f1) @ (extractFree f2)"|
"extractFree (Forall v f) = (removeAll v (extractFree f))"|
"extractFree (Exist v f) = (removeAll v (extractFree f))"|
"extractFree (Points_to a1 a2) = ((extFree a1) @ (extFree a2))"|
"extractFree (Conj f1 f2) = (extractFree f1) @ (extractFree f2)"

value "extractFree(Or (Forall ''y'' (Less (V ''y'') (V ''z''))) (Less (V ''y'') (V ''x'')))"
value "extractFree(Or (Forall y (Less (V y) (V z))) (Less (V y) (V x)))"

fun replaceA::"aexp \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> aexp" where
"replaceA (N n) v x = (N n)"|
"replaceA (V v) r x = (if v = r then (V x) else (V v))"|
"replaceA (Plus a1 a2) v x = (Plus (replaceA a1 v x) (replaceA a2 v x))"

fun replaceF::"formula \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> formula" where
"replaceF (Bc b) v x = (Bc b)"|
"replaceF (Not f) v x = (Not (replaceF f v x))"|
"replaceF (And f1 f2) v x = (And (replaceF f1 v x) (replaceF f2 v x))"|
"replaceF (Or f1 f2) v x = (Or (replaceF f1 v x) (replaceF f2 v x))"|
"replaceF (Less a1 a2) v x = (Less (replaceA a1 v x) (replaceA a2 v x))"|
"replaceF (Greater a1 a2) v x = (Greater (replaceA a1 v x) (replaceA a2 v x))"|
"replaceF (Equal a1 a2) v x = (Equal (replaceA a1 v x) (replaceA a2 v x))"|
"replaceF (Imp f1 f2) v x = (Imp (replaceF f1 v x) (replaceF f2 v x))"|
"replaceF (Forall s f) v x = (Forall s (replaceF f v x))"|
"replaceF (Exist s f) v x = (Exist s (replaceF f v x))"|
"replaceF (Points_to a1 a2) v x = ((Points_to (replaceA a1 v x) (replaceA a2 v x)))"|
"replaceF (Conj f1 f2) v x = (Conj (replaceF f1 v x) (replaceF f2 v x))"

fun getAddr::"formula \<Rightarrow> newstate \<Rightarrow> nat set" where
"getAddr (Bc b) s = {}"|
"getAddr (Not f) s = (getAddr f s)"|
"getAddr (And f1 f2) s = (getAddr f1 s) \<union> (getAddr f2 s)"|
"getAddr (Or f1 f2) s = (getAddr f1 s) \<union> (getAddr f2 s)"|
"getAddr (Less a1 a2) s = {}"|
"getAddr (Greater a1 a2) s = {}"|
"getAddr (Equal a1 a2) s = {}"|
"getAddr (Imp f1 f2) s = (getAddr f1 s) \<union> (getAddr f2 s)"|
"getAddr (Forall v f) s = (getAddr f s)"|
"getAddr (Exist v f) s = (getAddr f s)"|
"getAddr (Points_to a1 a2) s = {addr. addr = aval a1 (vars s)}"|
"getAddr (Conj f1 f2) s = (getAddr f1 s) \<union> (getAddr f2 s)"

(*fun fVal::"formula \<Rightarrow> active_addrs \<Rightarrow> newstate \<Rightarrow> bool" where
"fVal (Bc v) bs s = v"|
"fVal (Not f) bs s = (\<not>fVal f bs s)"|
"fVal (And f1 f2) bs s = ((fVal f1 bs s) \<and> (fVal f2 bs s))"|
"fVal (Or f1 f2) bs s = ((fVal f1 bs s) \<or> (fVal f2 bs s))"|
"fVal (Less a1 a2) bs s = ((aval a1 (vars s)) < (aval a2 (vars s)))"|
"fVal (Greater a1 a2) bs s = ((aval a1 (vars s)) > (aval a2 (vars s)))"|
"fVal (Equal a1 a2) bs s = ((aval a1 (vars s)) = (aval a2 (vars s)))"|
"fVal (Imp f1 f2) bs s = ((fVal f1 bs s) \<longrightarrow> (fVal f2 bs s))"|
"fVal (Forall v f) bs s = (fVal f bs s)"|
"fVal (Exist v f) bs s = (\<exists>x::vname. fVal (replaceF f v x) bs s)"|
"fVal (Points_to a1 a2) bs s = (((mem s)(aval a1 (vars s)) = (aval a2 (vars s))) \<and> bs (aval a1 (vars s)))"|
"fVal (Conj f1 f2) bs s = ((getAddr f1 s) \<inter> (getAddr f2 s) = {} \<and> 
  (\<forall>addr \<in> (getAddr f1 s). (bs addr)) \<and> (\<forall>addr \<in> (getAddr f2 s). (bs addr)) \<and> (fVal f1 bs s) \<and> (fVal f2 bs s))"

definition condition :: "formula \<Rightarrow> com \<Rightarrow> bool"
  where "condition f c \<equiv> \<forall> bs s s' . fVal f bs s \<and> (Some c, s) \<Rightarrow>\<^sub>t\<^sub>r s' \<longrightarrow> fVal f bs s'"*)

end