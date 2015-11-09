theory Par_Com
imports Small_Step
begin

datatype par_com =
  Parallel   "((acom option \<times> assn) list)"|
  ParAssign  vname aexp              ("_ ::= _")|
  ParSeq     par_com par_com         ("_,, _") |
  ParCond    bexp par_com par_com    ("IF _ THEN _ ELSE _ FI")|
  ParWhile   bexp assn par_com       ("WHILE _ INV _ DO _ OD")

definition Index :: "'a list \<Rightarrow> nat set" where
  "Index xs \<equiv> {i. i < length xs}"

fun Index2 where
  "Index2 [] = {}"
| "Index2 (x#xs) = Index2 xs \<union> {length (xs)}"

lemma "Index xs = Index2 xs"
proof (induct xs)
  case Nil
  show ?case by (simp add:Index_def)
next
  case Cons
  thus ?case apply (simp add:Index_def)
  using Collect_cong less_Suc_eq by auto
qed

definition All_None4 where
  "All_None4 Ts \<equiv> \<forall>i \<in> Index Ts. (case Ts!i of (c, Q) \<Rightarrow> (c = None))"

definition All_None2 where
  "All_None2 Ts \<equiv> \<forall>i \<in> Index Ts. \<forall> c Q . Ts!i = (c,Q) \<longrightarrow> c = None"

fun All_None3 where
  "All_None3 [] = True"|
  "All_None3 (x#xs) = ((fst(x) = None) \<and> All_None3(xs))"
  
definition All_None where
  "All_None Ts \<equiv> \<forall>i \<in> Index Ts. fst(Ts!i) = None"

inductive
  par_trans :: "par_com * state \<Rightarrow> par_com * state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>P" 55)
where
Paral:  "\<lbrakk>i \<in> Index Cs; Cs!i = (Some c, Q); (Some c, s) \<rightarrow> (ro, t)\<rbrakk> \<Longrightarrow>
  (Parallel Cs, s) \<rightarrow>\<^sub>P (Parallel(Cs[i := (ro, Q)]), t)"|

PAssign:  "(x ::= a, s) \<rightarrow>\<^sub>P (Parallel [], s(x := aval a s))" |

PSeq1:   "All_None Ts \<Longrightarrow> ((Parallel Ts,, c), s) \<rightarrow>\<^sub>P (c, s)" |
PSeq2:   "(c0, s) \<rightarrow>\<^sub>P (c2, t) \<Longrightarrow> ((c0,, c1), s) \<rightarrow>\<^sub>P ((c2,, c1), t)" |

PIfTrue:  "bval b s \<Longrightarrow> ((IF b THEN c1 ELSE c2 FI), s) \<rightarrow>\<^sub>P (c1, s)" |
PIfFalse: "\<not>bval b s \<Longrightarrow> ((IF b THEN c1 ELSE c2 FI), s) \<rightarrow>\<^sub>P (c2, s)" |

PWhileTrue: "\<not>bval b s \<Longrightarrow> ((WHILE b INV I DO c OD), s) \<rightarrow>\<^sub>P (Parallel [], s)" |
PWhileFalse:"bval b s \<Longrightarrow> ((WHILE b INV I DO c OD), s) \<rightarrow>\<^sub>P ((c,, (WHILE b INV I DO c OD)), s)"

abbreviation
  par_transs :: "par_com * state \<Rightarrow> par_com * state \<Rightarrow> bool" (infix "\<rightarrow>\<^sub>P*" 55)
where "x \<rightarrow>\<^sub>P* y == star par_trans x y"

subsection{* Executability *}

code_pred small_step .

lemmas small_step_induct = small_step.induct[split_format(complete)]

subsubsection{* Proof automation *}

declare small_step.intros[simp,intro]

text{* Rule inversion: *}

inductive_cases ParallelE[elim]: "((Parallel Cs), s) \<rightarrow>\<^sub>P ct"
inductive_cases PBasicE[elim!]: "(x ::= a, s) \<rightarrow>\<^sub>P ct"
inductive_cases PSeqE[elim]: "((c1,, c2), s) \<rightarrow>\<^sub>P ct"
inductive_cases PIfE[elim!]: "((IF b THEN c1 ELSE c2 FI), s) \<rightarrow>\<^sub>P ct"
inductive_cases PWhileE[elim]: "((WHILE b INV I DO c OD), s) \<rightarrow>\<^sub>P ct"

end