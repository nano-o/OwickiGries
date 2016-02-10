theory NFormula
imports Small_Step
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
"extractFree (Bc v) = []"|
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

fun getAddr::"formula \<Rightarrow> newstate \<Rightarrow> nat set" where
"getAddr (Bc v) s = {}"|
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

fun fVal::"formula \<Rightarrow> active_addrs \<Rightarrow> newstate \<Rightarrow> bool" where
"fVal (Bc v) bs s = v"|
"fVal (Not f) bs s = (\<not>fVal f bs s)"|
"fVal (And f1 f2) bs s = ((fVal f1 bs s) \<and> (fVal f2 bs s))"|
"fVal (Or f1 f2) bs s = ((fVal f1 bs s) \<or> (fVal f2 bs s))"|
"fVal (Less a1 a2) bs s = ((aval a1 (vars s)) < (aval a2 (vars s)))"|
"fVal (Greater a1 a2) bs s = ((aval a1 (vars s)) > (aval a2 (vars s)))"|
"fVal (Equal a1 a2) bs s = ((aval a1 (vars s)) = (aval a2 (vars s)))"|
"fVal (Imp f1 f2) bs s = ((fVal f1 bs s) \<longrightarrow> (fVal f2 bs s))"|
"fVal (Forall v f) bs s = (fVal f bs s)"|
"fVal (Exist v f) bs s = (fVal f bs s)"|
"fVal (Points_to a1 a2) bs s = (((mem s)(aval a1 (vars s)) = (aval a2 (vars s))) \<and> bs (aval a1 (vars s)))"|
"fVal (Conj f1 f2) bs s = ((getAddr f1 s) \<inter> (getAddr f2 s) = {} \<and> 
  (\<forall>addr \<in> (getAddr f1 s). (bs addr)) \<and> (\<forall>addr \<in> (getAddr f2 s). (bs addr)) \<and> (fVal f1 bs s) \<and> (fVal f2 bs s))"

definition condition :: "formula \<Rightarrow> com \<Rightarrow> bool"
  where "condition f c \<equiv> \<forall> bs s s' . fVal f bs s \<and> (Some c, s) \<Rightarrow>\<^sub>t\<^sub>r s' \<longrightarrow> fVal f bs s'"

end