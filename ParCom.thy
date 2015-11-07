theory ParCom
imports Main BExp
begin

type_synonym assn = "state \<Rightarrow> bool"

datatype com =
  SKIP                           (" SKIP" 61) |
  Assign vname aexp              ("_ ::= _/" [1000, 61] 61) |
  Seq com com                       ("_;;//_"  [60, 61] 60) |
  If bexp com com              ("IF _/ THEN _/ ELSE _"  [0, 0, 0] 61) |
  While bexp com           ("WHILE _// DO _"  [0, 61] 61) |
  Await bexp                     ("AWAIT _" [61] 60)

datatype acom =
  SKIP assn                           (" {_}//SKIP" 61) |
  Assign assn vname aexp              (" {_}//(_ ::= _/)" [0, 1000, 61] 61) |
  Seq acom acom                       ("_,,//_"  [60, 61] 60) |
  If assn bexp acom acom              ("{_}//(IF _/ THEN _/ ELSE _)"  [0, 0, 0, 0] 61) |
  While assn bexp assn acom           ("({_}//WHILE _//DO ({_}//_))"  [0, 0, 0, 61] 61) | 
  Await assn bexp                     ("{_}//(AWAIT _)" [0, 61] 60)

fun strip where
  "strip ({P} SKIP) = SKIP" 
| "strip ({P} x ::= y) = x ::= y"
| "strip (c1,, c2) = (strip c1);; (strip c2)"
| "strip ({P} IF b THEN c1 ELSE c2) = IF b THEN (strip c1) ELSE (strip c2)"
| "strip ({P} WHILE b DO {I} c) = WHILE b DO (strip c)"
| "strip ({P} AWAIT b) = AWAIT b"

term 
"{P} AWAIT (Bc True) ,,
{Q} ''x'' ::= N 3"

datatype par_com =
  Par "acom list" ("|| _")

abbreviation inc where
  "inc P \<equiv> {P} ''x'' ::= Plus (V ''x'') (N 1)"

abbreviation true where 
  "true \<equiv> \<lambda> s . True"

term
"|| [inc true, inc true]"

end