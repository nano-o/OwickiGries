theory Ann_Com
imports BExp
begin

type_synonym assn = "state \<Rightarrow> bool"

datatype com =
  Basic "state \<Rightarrow> state"      |
  Seq   com com          ("_;; _") |
  Cond bexp com com      ("IF _ THEN _ ELSE _ FI")|
  While bexp assn com    ("WHILE _ INV _ DO _ OD")|
  Wait bexp              ("WAIT _ END")

datatype acom =
  ABasic assn "state \<Rightarrow> state"      |
  ASeq   acom acom   ("_;; _") |
  ACond assn bexp acom acom     ("{_} IF _ THEN _ ELSE _ FI")|
  AWhile assn bexp assn acom    ("{_} WHILE _ INV _ DO _ OD")|
  AWait assn bexp              ("{_} WAIT _ END")

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