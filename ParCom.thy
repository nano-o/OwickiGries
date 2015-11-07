theory ParCom
imports Main BExp Star
begin

text {* Copied and modified theory files from the book "Concrete Semantics", 
  by Tobias Nipkow and Gerwin Klein, and the paper Owicki/Gries in Isabelle/HOL, 
  by Tobias Nipkow and Leonor Prensa Nieto *}

section {* Commands, annotated commands, and parallel commands *}

type_synonym assn = "state \<Rightarrow> bool"

datatype com =
  SKIP                          (" SKIP" 61) |
  Assign vname aexp             ("_ ::= _/" [1000, 61] 61) |
  Seq com com                   ("_;;//_"  [60, 61] 60) |
  If bexp com com               ("IF _/ THEN _/ ELSE _"  [0, 0, 0] 61) |
  While bexp com                ("WHILE _// DO _"  [0, 61] 61) |
  Await bexp                    ("AWAIT _" [61] 60)

datatype acom =
  -- {* Annotated commands carry a precondition *}
  SKIP assn                           (" {_}//SKIP" 61) |
  Assign assn vname aexp              (" {_}//(_ ::= _/)" [0, 1000, 61] 61) |
  Seq acom acom                       ("_,,//_"  [60, 61] 60) |
  If assn bexp acom acom              ("{_}//(IF _/ THEN _/ ELSE _)"  [0, 0, 0, 0] 61) |
  While assn bexp assn acom           ("({_}//WHILE _//DO ({_}//_))"  [0, 0, 0, 61] 61) |
    -- {* On top of a precondition, loops carry a loop invariant *}
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

datatype par_acom =
  APar "(acom \<times> assn) list" ("|| _")
-- {* An annotated parallel command is a list pairs consisting of 
  an annotated commands and its postcondition *}

datatype par_com =
  Par "com list"

fun strip_acom :: "par_acom \<Rightarrow> par_com" where
  "strip_acom (APar cs) = Par (map (strip o fst) cs)"

subsection {* A trivial example *}

abbreviation inc where
  "inc P \<equiv> {P} ''x'' ::= Plus (V ''x'') (N 1)"

abbreviation true where 
  "true \<equiv> \<lambda> s . True"

term
"|| [(inc true, true), (inc true, true)]"

section {* Small-step semantics *}

inductive
  small_step :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "(x ::= a, s) \<rightarrow> (SKIP, s(x := aval a s))" |

Seq1:    "(SKIP;;c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1;;c\<^sub>2,s) \<rightarrow> (c\<^sub>1';;c\<^sub>2,s')" |

IfTrue:  "bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> (IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "(WHILE b DO c,s) \<rightarrow>
            (IF b THEN c;; WHILE b DO c ELSE SKIP,s)" |

Await:   "bval b s \<Longrightarrow> (AWAIT b, s) \<rightarrow> (SKIP, s)"

abbreviation
  small_steps :: "com * state \<Rightarrow> com * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y \<equiv> star small_step x y"

inductive
  par_small_step :: "par_com \<times> state \<Rightarrow> par_com \<times> state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<parallel>" 55) where
  "\<lbrakk>i \<in> {0..length cs}; (cs!i,s) \<rightarrow> (c,t)\<rbrakk> \<Longrightarrow> (Par cs, s) \<rightarrow>\<^sub>\<parallel> (Par (cs[i := c]), t)"

abbreviation
  par_small_steps :: "par_com * state \<Rightarrow> par_com * state \<Rightarrow> bool" (infix "\<rightarrow>*\<^sub>\<parallel>" 55)
where "x \<rightarrow>*\<^sub>\<parallel> y \<equiv> star par_small_step x y"

section {* Proof system for annotated commands *}


end