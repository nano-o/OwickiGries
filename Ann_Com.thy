theory Ann_Com
imports BExp
begin

type_synonym address = int
type_synonym memory = "address \<Rightarrow> int"
datatype newstate = 
  State (mem: "address \<Rightarrow> int") (vars: "string \<Rightarrow> int")

type_synonym assn = "newstate \<Rightarrow> bool"

datatype com =
  Basic "newstate \<Rightarrow> newstate"   ("BASIC _ ")   |
  Seq   com com          ("_;; _") |
  Cond "newstate \<Rightarrow> bool" com com      ("IF _ THEN _ ELSE _ FI")|
  While "newstate \<Rightarrow> bool" assn com    ("WHILE _ INV _ DO _ OD")|
  Wait "newstate \<Rightarrow> bool"              ("WAIT _ END")

fun list :: "newstate \<Rightarrow> (int list) \<Rightarrow> int \<Rightarrow> bool" where 
"list s [] i = (i = (0::int))"|
"list s (x#xs) i = (\<exists>j. ((mem s) i = j) \<and> ((mem s) (i+1) = x) \<and> list s xs j)"

(* s where "s \<equiv> \<lambda> i . if i = 1 then 3 else (if i = 2 then 42 else (if i = 3 then 0 else 43))"

lemma "list s [42, 43] 1" by force
*)
fun reach_step::"newstate \<Rightarrow> nat \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
"reach_step s 0 i j = (i = j)"|
"reach_step s (Suc n) i j = (\<exists>a k. ((mem s) i = a) \<and> ((mem s) (i + 1) = k) \<and> (reach_step s n k j))"

definition reach::"newstate \<Rightarrow> int \<Rightarrow> int \<Rightarrow> bool" where
  "reach s i j \<equiv> (\<exists>n \<ge> 0. reach_step s n i j)"

datatype acom =
  ABasic assn "newstate \<Rightarrow> newstate"    ("{_} BASIC _ ")   |
  ASeq   acom acom   ("_;; _") |
  ACond assn "newstate \<Rightarrow> bool" acom acom     ("{_} IF _ THEN _ ELSE _ FI")|
  AWhile assn "newstate \<Rightarrow> bool" assn acom    ("{_} WHILE _ INV _ DO _ OD")|
  AWait assn "newstate \<Rightarrow> bool"              ("{_} WAIT _ END")

fun pre :: "acom \<Rightarrow> assn" where
"pre (ABasic P f) = P" |
"pre (c1;; c2) = pre(c1)" |
"pre ({P} IF b THEN c1 ELSE c2 FI) = P"|
"pre ({P} WHILE b INV I DO c OD) = P"|
"pre ({P} WAIT b END) = P"

fun strip::"acom \<Rightarrow> com" where
"strip (ABasic P f) = (Basic f)"|
"strip (C1;; C2) = (strip(C1);; strip(C2))" |
"strip ({P} IF b THEN C1 ELSE C2 FI) = (IF b THEN strip C1 ELSE strip C2 FI)"|
"strip ({P} WHILE b INV I DO C OD) = (WHILE b INV I DO strip C OD)"|
"strip ({P} WAIT b END) = (WAIT b END)"

end