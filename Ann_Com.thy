theory Ann_Com
imports BExp Star
begin

type_synonym address = nat
type_synonym memory = "address \<Rightarrow> nat"
datatype newstate = 
  State (mem: memory) (vars: state)

type_synonym assn = "newstate \<Rightarrow> bool"

datatype com =
  Basic "newstate \<Rightarrow> newstate"   ("BASIC _ ")   |
  Seq   com com          ("_;; _" [61, 60] 1000) |
  Cond "newstate \<Rightarrow> bool" com com      ("IF _ THEN _ ELSE _ FI")|
  While "newstate \<Rightarrow> bool" assn com    ("WHILE _ INV _ DO _ OD")|
  Wait "newstate \<Rightarrow> bool"              ("WAIT _ END")

(*
fun reach_step::"newstate \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
"reach_step s 0 i j = (i = j)"|
"reach_step s (Suc n) i j = (\<exists> k. ((mem s) (i + 1) = k) \<and> (reach_step s n k j))"

definition reach::"newstate \<Rightarrow> address \<Rightarrow> nat \<Rightarrow> bool" where
  "reach s i j \<equiv> (\<exists>n \<ge> 0. reach_step s n i j)"
*)

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