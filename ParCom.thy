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

fun pre where 
  "pre ({P} SKIP) = P"
| "pre ({P} x ::= a) = P"
| "pre (c1 ,, c2) = pre c1"
| "pre ({P} IF b THEN c1 ELSE c2) = P"
| "pre ({P} WHILE b DO {I} c) = P"
| "pre ({P} AWAIT b) = P"

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

abbreviation post where "post \<equiv> snd"
abbreviation com where "com \<equiv> fst"

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

locale small_step_com 
begin

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

end

inductive
  small_step :: "acom * state \<Rightarrow> acom * state \<Rightarrow> bool" (infix "\<rightarrow>" 55)
where
Assign:  "({P} x ::= a, s) \<rightarrow> ({P} SKIP, s(x := aval a s))" |

Seq1:    "({P} SKIP,,c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |
Seq2:    "(c\<^sub>1,s) \<rightarrow> (c\<^sub>1',s') \<Longrightarrow> (c\<^sub>1,,c\<^sub>2,s) \<rightarrow> (c\<^sub>1',,c\<^sub>2,s')" |

IfTrue:  "bval b s \<Longrightarrow> ({P} IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>1,s)" |
IfFalse: "\<not>bval b s \<Longrightarrow> ({P} IF b THEN c\<^sub>1 ELSE c\<^sub>2,s) \<rightarrow> (c\<^sub>2,s)" |

While:   "bval b s \<Longrightarrow> ({P} WHILE b DO {I} c,s) \<rightarrow>
            (c,, {I} WHILE b DO {I} c, s)" |

Await:   "bval b s \<Longrightarrow> ({P} AWAIT b, s) \<rightarrow> ({P} SKIP, s)"

abbreviation
  small_steps :: "acom * state \<Rightarrow> acom * state \<Rightarrow> bool" (infix "\<rightarrow>*" 55)
where "x \<rightarrow>* y \<equiv> star small_step x y"

inductive
  par_small_step :: "par_acom \<times> state \<Rightarrow> par_acom \<times> state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>\<parallel>" 55) where
  "\<lbrakk>i \<in> {0..length cs}; (fst (cs!i),s) \<rightarrow> (c,t)\<rbrakk>
    \<Longrightarrow> (APar cs, s) \<rightarrow>\<^sub>\<parallel> (APar (cs[i := (c, snd (cs!i))]), t)"

abbreviation
  par_small_steps :: "par_acom * state \<Rightarrow> par_acom * state \<Rightarrow> bool" (infix "\<rightarrow>*\<^sub>\<parallel>" 55)
where "x \<rightarrow>*\<^sub>\<parallel> y \<equiv> star par_small_step x y"

section {* Proof system for annotated commands *}

abbreviation state_subst :: "state \<Rightarrow> aexp \<Rightarrow> vname \<Rightarrow> state"
  ("_[_'/_]" [1000,0,0] 999)
where "s[a/x] \<equiv> s(x := aval a s)"

inductive acom_rules :: "acom \<Rightarrow> assn \<Rightarrow> bool"  ("\<turnstile> ((_)/ {(1_)})" 50) where
  "\<turnstile> {Q} SKIP {Q}"
| "\<lbrakk>\<And> s . P s \<Longrightarrow> Q (s[a/x])\<rbrakk> \<Longrightarrow> \<turnstile> {P} x ::= a {Q}"
| "\<lbrakk>\<turnstile> c1 {pre c2}; \<turnstile> c2 {Q}\<rbrakk> \<Longrightarrow> \<turnstile> c1,, c2 {Q}"
| "\<lbrakk>\<And> s . P s \<and> bval b s \<Longrightarrow> (pre c1) s; \<And> s . P s \<and> \<not> bval b s \<Longrightarrow> (pre c2) s; \<turnstile> c1 {Q}; \<turnstile> c2 {Q}\<rbrakk>
    \<Longrightarrow> \<turnstile> {P} IF b THEN c1 ELSE c2 {Q}"
| "\<lbrakk>\<And> s . P s \<Longrightarrow> I s; \<turnstile> c {I}; \<And> s . I s \<and> \<not> bval b s \<Longrightarrow> Q s; \<And> s . I s \<and> bval b s \<Longrightarrow> (pre c) s\<rbrakk>
    \<Longrightarrow> \<turnstile> {P} WHILE b DO {I} c {Q}"
| "\<lbrakk>\<And> s . P s \<and> bval b s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<turnstile> {P} AWAIT b {Q}"
| "\<lbrakk>\<turnstile> c {Q}; \<And> s . Q' s \<Longrightarrow> Q s\<rbrakk> \<Longrightarrow> \<turnstile> c{ Q'}"

fun atomics :: "acom \<Rightarrow> (assn \<times> vname \<times> aexp) set" where
  -- {* The set of assignments in a command, described by a tripe (P, x, a)*}
  "atomics ({P} SKIP) = {}"
| "atomics ({P} x ::= a) =  {(P, x, a)}"
| "atomics (c1,, c2) = atomics c1 \<union> atomics c2"
| "atomics ({P} IF b THEN c1 ELSE c2) = atomics c1 \<union> atomics c2"
| "atomics ({P} WHILE b DO {I} c) = atomics c"
| "atomics ({P} AWAIT b) = {}"

fun assertions :: "acom \<Rightarrow> assn set" where
  "assertions ({P} SKIP) = {P}"
| "assertions ({P} x ::= a) =  {P}"
| "assertions (c1,, c2) = assertions c1 \<union> assertions c2"
| "assertions ({P} IF b THEN c1 ELSE c2) = {P} \<union> assertions c1 \<union> assertions c2"
| "assertions ({P} WHILE b DO {I} c) =  {P, I} \<union> assertions c"
| "assertions ({P} AWAIT b) = {P}"

definition interfree where
  -- {* c2 does not interfere with c1 when Q and all the assertions in c1 are invariant under c2 *}
  "interfree c1 Q c2 \<equiv> \<forall> (P,x,a) \<in> atomics c2 . 
      \<turnstile> {\<lambda> s. P s \<and> Q s} x ::= a {Q}
      \<and> (\<forall> R \<in> assertions c1 . \<turnstile> {\<lambda> s. P s \<and> R s} x ::= a {R})"

definition INTERFREE where
  "INTERFREE cs \<equiv> \<forall> i \<in> {0..length cs} . \<forall> j \<in> {0..length cs} . 
    i \<noteq> j \<longrightarrow> interfree (fst (cs!i)) (snd (cs!i)) (fst (cs!j))"

end