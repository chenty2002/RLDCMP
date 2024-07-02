theory ECMPDSym
  imports Main "HOL-Combinatorics.Permutations"
begin

subsection \<open>Datatypes for variables, values, expressions, and formulas\<close>

text \<open>
  Two kinds of variables are used in the protocols:
  1. simple identifiers to define global variables 
  2. array variables ---- arr[i]
\<close>
datatype varType =
  Ident string | Para string nat | dontCareVar

text \<open>
  Three kinds of values used in the protocols.
  1. enumerating values
  2. natural numbers 
  3. boolean values
\<close>
datatype scalrValueType =
  enum string string | index nat | boolV bool | dontCare | data nat

text \<open>
  Types indicate which kind of value the expression is,
  including enum, index, and bool.
\<close>
datatype typeType =
  enumType | indexType | boolType | anyType|dataType

text \<open>
  An environment is a mapping from variables to types.
\<close>
type_synonym envType = "varType \<Rightarrow> typeType"

text \<open>
  Expressions and formulas are defined mutually recursively.
  Expressions can be simple or compound. 
  A simple expression is either a variable or a constant, 
  while a compound expression is constructed with the ite (if-then-else) form. 
  A formula can be an atomic formula or a compound formula.
  An atomic formula can be a boolean variable or constant, 
  or in the equivalence forms. A formula can also be constructed by 
  using the logic connectives, including negation, conjunction, 
  disjunction, implication.
\<close>
datatype expType =
  IVar varType |
  Const scalrValueType |
  iteForm formula expType expType |
  dontCareExp

and formula =
  eqn expType expType     (infixl "=\<^sub>f" 50) |
  andForm formula formula (infixr "\<and>\<^sub>f" 35) |
  neg formula             ("\<not>\<^sub>f _" [40] 40) |
  orForm formula formula  (infixr "\<or>\<^sub>f" 30) |
  implyForm formula formula  (infixr "\<longrightarrow>\<^sub>f" 25) |
  forallForm "nat \<Rightarrow> formula" nat (binder "\<forall>\<^sub>f" 10) |
  existForm "nat \<Rightarrow> formula" nat (binder "\<exists>\<^sub>f" 10) | 
  forallFormExcl "nat \<Rightarrow> formula" nat nat |
  chaos |
  dontCareForm


subsection \<open>Datatypes for assignments, statements, and rules\<close>

text \<open>
  A statement is just a lists of assignments,
  but these assignments are executed in parallel, 
  \emph{not} in a sequential order
\<close>
type_synonym assignType = "varType \<times> expType"

datatype statement =
  skip |
  assign assignType |
  parallel statement statement (infixr "||" 35) |
  iteStm formula statement statement ("IF _ DO _ ELSE _ FI") |
  forallStm "nat \<Rightarrow> statement" nat |
  forallStmExcl "nat \<Rightarrow> statement" nat nat

text \<open>
  A parameterized statement is just a function from a
  parameter to a statement.
\<close>
type_synonym paraStatement = "nat \<Rightarrow> statement"

text \<open>
  Similarly, a parameterized formula is a function from
  a parameter to a formula.
\<close>
type_synonym paraFormula = "nat \<Rightarrow> formula"


text \<open>
  With the formalizatiion of formula and statement,
  it is natural to define a rule.
\<close>
datatype rule =
  guard formula statement (infix "\<triangleright>" 30)

fun pre :: "rule \<Rightarrow> formula" where
  "pre (guard f a) = f"

fun act :: "rule \<Rightarrow> statement" where
  "act (guard f a) = a"

text \<open>A parameterized rule is just from a natural number to a rule.\<close>
type_synonym paraRule = "nat \<Rightarrow> rule"


subsection \<open>Semantics of a protocol\<close>

text \<open>
  A state of a protocol is an instantaneous snapshot of its
  behaviour given by an assignment of values to variables of
  the protocol.
\<close>
type_synonym state = "varType \<Rightarrow> scalrValueType"

text \<open>
  The formal semantics of an expression and a formula is 
  formalized as follows:
\<close>
primrec expEval :: "expType \<Rightarrow> state \<Rightarrow> scalrValueType" and
        formEval :: "formula \<Rightarrow> state \<Rightarrow> bool" where
  evalVar:    "expEval (IVar ie) s = s ie" |
  evalConst:  "expEval (Const i) s = i" |
  evalITE:    "expEval (iteForm f e1 e2) s = (if formEval f s then expEval e1 s else expEval e2 s)" |
  evalDontCareExp: "expEval (dontCareExp) s = dontCare" |

  evalEqn:    "formEval (eqn e1 e2) s = (expEval e1 s = expEval e2 s)" |
  evalAnd:    "formEval (andForm f1 f2) s = (formEval f1 s \<and> formEval f2 s)" |
  evalNeg:    "formEval (neg f1) s = (\<not>formEval f1 s)" |
  evalOr:     "formEval (orForm f1 f2) s = (formEval f1 s \<or> formEval f2 s)" |
  evalImp:    "formEval (implyForm f1 f2) s = (formEval f1 s \<longrightarrow> formEval f2 s)" |
  evalForall: "formEval (forallForm ffun N) s = (\<forall>i\<le>N. formEval (ffun i) s)" |  
  evalExist: "formEval (existForm ffun N) s = (\<exists>i\<le>N. formEval (ffun i) s)" |
  evalForallExcl: "formEval (forallFormExcl ffun i N) s = (\<forall>j\<le>N. j \<noteq> i \<longrightarrow> formEval (ffun j) s)" |
  evalChaos:  "formEval chaos s = True" |
  evalDontCareForm: "formEval dontCareForm s = True"

text \<open>Set of variables occuring in expressions, forms, and statements\<close>
definition varsOfVar :: "varType \<Rightarrow> varType set" where [simp]:
  "varsOfVar x = {x}" 

primrec varOfExp :: "expType \<Rightarrow> varType set" and
        varOfForm :: "formula \<Rightarrow> varType set" where
  "varOfExp  (IVar v)  = varsOfVar v" |
  "varOfExp  (Const j) = {}" |
  "varOfExp  (iteForm f e1 e2) = varOfForm f \<union> varOfExp e1 \<union> varOfExp  e2" |
  "varOfExp  (dontCareExp) = {} " |
  "varOfForm (eqn e1 e2) = varOfExp e1 \<union> varOfExp  e2" |
  "varOfForm (andForm f1 f2) = varOfForm f1 \<union> varOfForm f2" |
  "varOfForm (neg f1) = varOfForm f1" |
  "varOfForm (orForm f1 f2) = varOfForm f1 \<union> varOfForm f2" |
  "varOfForm (implyForm f1 f2) = varOfForm f1 \<union> varOfForm f2" |
  "varOfForm (chaos) = {}" |
  "varOfForm (forallForm pf N) = \<Union>{S. \<exists>i. i \<le> N \<and> S = varOfForm (pf i)}" |
  "varOfForm (existForm pf N ) = \<Union>{S. \<exists>i. i \<le> N \<and> S = varOfForm (pf i)}" |
  "varOfForm (dontCareForm) = {}" |
  "varOfForm (forallFormExcl pf j N) = \<Union>{S. \<exists>i. i \<le> N \<and> S = varOfForm (pf i)}"


primrec varOfStmt :: "statement \<Rightarrow> varType set" where
  "varOfStmt skip = {}" |
  "varOfStmt (assign a) = {fst a}" |
  "varOfStmt (parallel S1 S2) = varOfStmt S1 \<union> varOfStmt S2" |
  "varOfStmt (iteStm b S1 S2) = varOfStmt S1 \<union> varOfStmt S2" |
  "varOfStmt (forallStm ps N) = \<Union>{S. \<exists>i. i \<le> N \<and> S = varOfStmt (ps i)}" |
  "varOfStmt (forallStmExcl ps j N) = \<Union>{S. \<exists>i. i \<le> N \<and> i \<noteq> j \<and> S = varOfStmt (ps i)}"

declare varOfStmt.simps(5,6) [simp del]
lemma varOfStmtEq:
  "v \<in> varOfStmt (forallStm ps N) \<longleftrightarrow> (\<exists>i. i \<le> N \<and> v \<in> varOfStmt (ps i))"
  by (auto simp add: varOfStmt.simps(5))

lemma varOfStmtEq2:
  "v \<in> varOfStmt (forallStmExcl ps j N) \<longleftrightarrow> (\<exists>i. i \<le> N \<and> i \<noteq> j \<and> v \<in> varOfStmt (ps i))"
  by (auto simp add: varOfStmt.simps(6))

text \<open>Largest index of statements that contain variable v\<close>
primrec largestInd :: "varType \<Rightarrow> nat \<Rightarrow> paraStatement \<Rightarrow> nat option" where
  "largestInd v 0 ps = (if v \<in> varOfStmt (ps 0) then Some 0 else None)" |
  "largestInd v (Suc N) ps = (if v \<in> varOfStmt (ps (Suc N)) then Some (Suc N) else largestInd v N ps)"

lemma largestIndNone:
  "largestInd v N ps = None \<longleftrightarrow> (\<forall>i\<le>N. v \<notin> varOfStmt (ps i))"
  apply (induct N) apply auto
  by (metis le_Suc_eq)

lemma largestIndSome:
  "largestInd v N ps = Some i \<longleftrightarrow> i \<le> N \<and> v \<in> varOfStmt (ps i) \<and> (\<forall>j\<le>N. j > i \<longrightarrow> v \<notin> varOfStmt (ps j))"
proof (induct N)
  case 0
  then show ?case by auto
next
  case (Suc N)
  show ?case
    apply (rule iffI)
     apply (metis Suc.hyps leD le_Suc_eq largestInd.simps(2) option.inject)
    using Suc.hyps antisym_conv2 le_Suc_eq by auto
qed

text \<open>Largest index of statements that contain variable v, excluding j\<close>
primrec largestIndExcl :: "varType \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> paraStatement \<Rightarrow> nat option" where
  "largestIndExcl v j 0 ps = (if v \<in> varOfStmt (ps 0) \<and> j \<noteq> 0 then Some 0 else None)"
| "largestIndExcl v j (Suc N) ps =
   (if v \<in> varOfStmt (ps (Suc N)) \<and> j \<noteq> Suc N then Some (Suc N) else largestIndExcl v j N ps)"

lemma largestIndExclNone:
  "largestIndExcl v j N ps = None \<longleftrightarrow> (\<forall>i\<le>N. i \<noteq> j \<longrightarrow> v \<notin> varOfStmt (ps i))"
  apply (induct N) apply auto
  by (metis le_Suc_eq)

lemma largestIndExclSome:
  "largestIndExcl v j N ps = Some i \<longleftrightarrow> i \<le> N \<and> i \<noteq> j \<and> v \<in> varOfStmt (ps i) \<and>
      (\<forall>k\<le>N. k > i \<and> k \<noteq> j \<longrightarrow> v \<notin> varOfStmt (ps k))"
proof (induct N)
  case 0
  then show ?case by auto
next
  case (Suc N)
  show ?case
    apply (rule iffI)
     apply simp
    apply (cases "v \<in> varOfStmt (ps (Suc N)) \<and> j \<noteq> Suc N")
    subgoal by auto
    subgoal using Suc.hyps le_Suc_eq by auto
    using Suc.hyps antisym_conv2 largestIndExcl.simps(2) le_Suc_eq by auto
qed


text \<open>One step transition of a statement\<close>

primrec trans1 :: "statement \<Rightarrow> state \<Rightarrow> state" where
  "trans1 skip s v = s v" |
  "trans1 (assign as) s v = (if fst as = v then expEval (snd as) s else s v)" |
  "trans1 (parallel S1 S2) s v = (if v \<in> varOfStmt S1 then trans1 S1 s v else trans1 S2 s v)"|
  "trans1 (iteStm b S1 S2) s v = (if formEval b s then trans1 S1 s v else trans1 S2 s v)" |
  "trans1 (forallStm ps N) s v =
    (case largestInd v N ps of None \<Rightarrow> s v | Some i \<Rightarrow> trans1 (ps i) s v)" |
  "trans1 (forallStmExcl ps j N) s v =
    (case largestIndExcl v j N ps of None \<Rightarrow> s v | Some i \<Rightarrow> trans1 (ps i) s v)"

definition mutualDiffVars :: "(nat \<Rightarrow> statement) \<Rightarrow> bool" where
  "mutualDiffVars ps \<longleftrightarrow> (\<forall>i j. i \<noteq> j \<longrightarrow> varOfStmt (ps i) \<inter> varOfStmt (ps j) = {})"

lemma trans1ForallAlt:
  assumes "mutualDiffVars ps"
  shows "trans1 (forallStm ps N) s v =
          (if v \<notin> varOfStmt (forallStm ps N) then s v
           else trans1 (ps (THE i. v \<in> varOfStmt (ps i))) s v)"
proof -
  have a: ?thesis if "v \<notin> varOfStmt (forallStm ps N)"
  proof -
    have "largestInd v N ps = None"
      using largestIndNone that varOfStmtEq by auto
    then show ?thesis
      using that by auto
  qed
  have b: ?thesis if assmb: "v \<in> varOfStmt (forallStm ps N)"
  proof -
    obtain i where b1: "i \<le> N" "v \<in> varOfStmt (ps i)"
      using assmb varOfStmtEq by blast
    have b2: "largestInd v N ps = Some i"
      unfolding largestIndSome
      apply (auto simp add: b1)
      using assms b1 unfolding mutualDiffVars_def
      by (metis IntI empty_iff inf.strict_order_iff)
    have b3: "(THE i. v \<in> varOfStmt (ps i)) = i"
      apply (rule the_equality) apply (rule b1(2))
      using assms b1(2) unfolding mutualDiffVars_def by auto
    show ?thesis
      using assmb b1 b2 b3 by auto
  qed
  show ?thesis
    using a b by auto 
qed

lemma trans1ForallExclAlt:
  assumes "mutualDiffVars ps"
  shows "trans1 (forallStmExcl ps j N) s v =
          (if v \<notin> varOfStmt (forallStmExcl ps j N) then s v
           else trans1 (ps (THE i. i \<noteq> j \<and> v \<in> varOfStmt (ps i))) s v)"
proof -
  have a: ?thesis if "v \<notin> varOfStmt (forallStmExcl ps j N)"
  proof -
    have "largestIndExcl v j N ps = None"
      using largestIndExclNone that varOfStmtEq2 by auto
    then show ?thesis
      using that by auto
  qed
  have b: ?thesis if assmb: "v \<in> varOfStmt (forallStmExcl ps j N)"
  proof -
    obtain i where b1: "i \<le> N" "i \<noteq> j" "v \<in> varOfStmt (ps i)"
      using assmb varOfStmtEq2 by blast
    have b2: "largestIndExcl v j N ps = Some i"
      unfolding largestIndExclSome
      apply (auto simp add: b1)
      using assms b1 unfolding mutualDiffVars_def
      by (metis IntI empty_iff inf.strict_order_iff)
    have b3: "(THE i. i \<noteq> j \<and> v \<in> varOfStmt (ps i)) = i"
      apply (rule the_equality) apply (simp add: b1(2,3))
      using assms b1(2,3) unfolding mutualDiffVars_def by auto
    show ?thesis
      using assmb b1 b2 b3 by auto
  qed
  show ?thesis
    using a b by auto 
qed  

subsection \<open>Permutations\<close>

type_synonym nat2nat = "nat \<Rightarrow> nat"

primrec applySym2Const :: "nat2nat \<Rightarrow> scalrValueType \<Rightarrow> scalrValueType" where
  "applySym2Const f (index n) = index (f n)" |
  "applySym2Const f (boolV b) = boolV b" |
  "applySym2Const f (enum t e) = enum t e" |
  "applySym2Const f (dontCare) = dontCare" |
  "applySym2Const  f (data d) =data d"


primrec applyDSym2Const :: "nat2nat \<Rightarrow> scalrValueType \<Rightarrow> scalrValueType" where
  "applyDSym2Const f (index n) = index (f n)" |
  "applyDSym2Const f (boolV b) = boolV b" |
  "applyDSym2Const f (enum t e) = enum t e" |
  "applyDSym2Const f (dontCare) = dontCare"|
  "applyDSym2Const  f (data d) =data (f d)"

lemma applySym2ConstInv [simp]:
  assumes "bij p"
  shows "applySym2Const p (applySym2Const (inv p) v) = v"
proof (cases v)
  case (index x2)
  then show ?thesis
    using assms bij_is_surj surj_iff_all by fastforce
qed (auto)


lemma applyDSym2ConstInv [simp]:
  assumes "bij p"
  shows "applyDSym2Const p (applyDSym2Const (inv p) v) = v"
proof (cases v)
  case (enum x11 x12)
  then show ?thesis 
     using assms bij_is_surj surj_iff_all by fastforce
next
case (index x2)
  then show ?thesis 
     using assms bij_is_surj surj_iff_all by fastforce
next
  case (boolV x3)
  then show ?thesis 
     using assms bij_is_surj surj_iff_all by fastforce
next
  case dontCare
  then show ?thesis 
   using assms bij_is_surj surj_iff_all by fastforce
next 
  case (data x2)
  then show ?thesis
    using assms bij_is_surj surj_iff_all by fastforce
  
qed  

lemma applySym2ConstInj [simp]:
  assumes "bij p"
  shows "(applySym2Const p a = applySym2Const p b) \<longleftrightarrow> a = b"
  by (metis applySym2ConstInv assms bij_imp_bij_inv inv_inv_eq)

lemma applyDSym2ConstInj [simp]:
  assumes "bij p"
  shows "(applyDSym2Const p a = applyDSym2Const p b) \<longleftrightarrow> a = b"
  by (metis applyDSym2ConstInv assms bij_imp_bij_inv inv_inv_eq)


primrec applySym2Var :: "nat2nat \<Rightarrow> varType \<Rightarrow> varType" where
  "applySym2Var f (Ident n) = Ident n" |
  "applySym2Var f (Para nm i) = Para nm (f i)" |
  "applySym2Var f dontCareVar = dontCareVar"

lemma applySym2VarInv [simp]:
  assumes "bij p"
  shows "applySym2Var p (applySym2Var (inv p) v) = v"
proof (cases v)
  case (Ident nm)
  then show ?thesis
    using assms bij_is_surj surj_iff_all by fastforce
next
  case (Para nm i)
  then show ?thesis
    using assms bij_betw_inv_into_right by fastforce 
qed (auto)


primrec applySym2Exp :: "nat2nat \<Rightarrow> expType \<Rightarrow> expType"
  and
  applySym2Form :: "nat2nat \<Rightarrow> formula \<Rightarrow> formula" where

  "applySym2Exp p (IVar v) = IVar (applySym2Var p v)" |
  "applySym2Exp p (Const c) = Const (applySym2Const p c)" |
  "applySym2Exp p (iteForm f1 e1 e2) = iteForm (applySym2Form p f1) (applySym2Exp p e1) (applySym2Exp p e2)" |
  "applySym2Exp p dontCareExp = dontCareExp" | 
  "applySym2Form p (eqn l r) = eqn (applySym2Exp p l) (applySym2Exp p r)" |
  "applySym2Form p (andForm f1 f2) = andForm (applySym2Form p f1) (applySym2Form p f2)" |
  "applySym2Form p (neg f1) = neg (applySym2Form p f1)" |
  "applySym2Form p (orForm f1 f2) = orForm (applySym2Form p f1) (applySym2Form p f2)" |
  "applySym2Form p (implyForm f1 f2) = implyForm (applySym2Form p f1) (applySym2Form p f2)" |
  "applySym2Form p (forallForm fp N) = forallForm (\<lambda>i. applySym2Form p (fp i)) N" |
  "applySym2Form p (existForm fp N) = existForm (\<lambda>i. applySym2Form p (fp i)) N" |
  "applySym2Form p (forallFormExcl fp i N) = forallFormExcl (\<lambda>j. applySym2Form p (fp j)) i N" |
  "applySym2Form p dontCareForm = dontCareForm" | 
  "applySym2Form p chaos = chaos"



primrec applyDSym2Exp :: "nat2nat \<Rightarrow> expType \<Rightarrow> expType"
  and
  applyDSym2Form :: "nat2nat \<Rightarrow> formula \<Rightarrow> formula" where

  "applyDSym2Exp p (IVar v) = IVar ( v)" |
  "applyDSym2Exp p (Const c) = Const (applyDSym2Const p c)" |
  "applyDSym2Exp p (iteForm f1 e1 e2) = iteForm (applyDSym2Form p f1) (applyDSym2Exp p e1) (applyDSym2Exp p e2)" |
  "applyDSym2Exp p dontCareExp = dontCareExp" | 
  "applyDSym2Form p (eqn l r) = eqn (applyDSym2Exp p l) (applyDSym2Exp p r)" |
  "applyDSym2Form p (andForm f1 f2) = andForm (applyDSym2Form p f1) (applyDSym2Form p f2)" |
  "applyDSym2Form p (neg f1) = neg (applyDSym2Form p f1)" |
  "applyDSym2Form p (orForm f1 f2) = orForm (applyDSym2Form p f1) (applyDSym2Form p f2)" |
  "applyDSym2Form p (implyForm f1 f2) = implyForm (applyDSym2Form p f1) (applyDSym2Form p f2)" |
  "applyDSym2Form p (forallForm fp N) = forallForm (\<lambda>i. applyDSym2Form p (fp i)) N" |
  "applyDSym2Form p (existForm fp N) = existForm (\<lambda>i. applyDSym2Form p (fp i)) N" |
  "applyDSym2Form p (forallFormExcl fp i N) = forallFormExcl (\<lambda>j. applyDSym2Form p (fp j)) i N" |
  "applyDSym2Form p dontCareForm = dontCareForm" | 
  "applyDSym2Form p chaos = chaos"

lemma applySym2ExpFormInv [simp]:
  assumes "bij p"
  shows "applySym2Exp p (applySym2Exp (inv p) e) = e \<and>
         applySym2Form p (applySym2Form (inv p) f) = f"
  apply (induction rule: expType_formula.induct)
  by (auto simp add: assms)


lemma applyDSym2ExpFormInv [simp]:
  assumes "bij p"
  shows "applyDSym2Exp p (applyDSym2Exp (inv p) e) = e \<and>
         applyDSym2Form p (applyDSym2Form (inv p) f) = f"
  apply (induction rule: expType_formula.induct)
  by (auto simp add: assms)

primrec applySym2Statement :: "nat2nat \<Rightarrow> statement \<Rightarrow> statement" where
  "applySym2Statement f skip = skip"
| "applySym2Statement f (assign as) = assign (applySym2Var f (fst as), applySym2Exp f (snd as))"
| "applySym2Statement f (parallel S1 S2) =
    parallel (applySym2Statement f S1) (applySym2Statement f S2)"
| "applySym2Statement f (iteStm b S1 S2) =
    iteStm (applySym2Form f b) (applySym2Statement f S1) (applySym2Statement f S2)"
| "applySym2Statement f (forallStm ps N) = forallStm (\<lambda>i. applySym2Statement f (ps i)) N"
| "applySym2Statement f (forallStmExcl ps i N) = forallStmExcl (\<lambda>j. applySym2Statement f (ps j)) i N"


primrec applyDSym2Statement :: "nat2nat \<Rightarrow> statement \<Rightarrow> statement" where
  "applyDSym2Statement f skip = skip"
| "applyDSym2Statement f (assign as) = assign ( (fst as), applyDSym2Exp f (snd as))"
| "applyDSym2Statement f (parallel S1 S2) =
    parallel (applyDSym2Statement f S1) (applyDSym2Statement f S2)"
| "applyDSym2Statement f (iteStm b S1 S2) =
    iteStm (applyDSym2Form f b) (applyDSym2Statement f S1) (applyDSym2Statement f S2)"
| "applyDSym2Statement f (forallStm ps N) = forallStm (\<lambda>i. applyDSym2Statement f (ps i)) N"
| "applyDSym2Statement f (forallStmExcl ps i N) = forallStmExcl (\<lambda>j. applyDSym2Statement f (ps j)) i N"

lemma applySym2statementInv [simp]:
  assumes "bij p"
  shows "applySym2Statement p (applySym2Statement (inv p) S) = S" (is "?P S")
  apply (induction S) by (auto simp add: assms)


lemma applyDSym2statementInv [simp]:
  assumes "bij p"
  shows "applyDSym2Statement p (applyDSym2Statement (inv p) S) = S" (is "?P S")
  apply (induction S) by (auto simp add: assms)

primrec applySym2Rule :: "nat2nat \<Rightarrow> rule \<Rightarrow> rule" where
  "applySym2Rule p (guard g a) = guard (applySym2Form p g) (applySym2Statement p a)"



primrec applyDSym2Rule :: "nat2nat \<Rightarrow> rule \<Rightarrow> rule" where
  "applyDSym2Rule p (guard g a) = guard (applyDSym2Form p g) (applyDSym2Statement p a)"


text \<open>Applying a permutation to a state\<close>
fun applySym2State :: "nat2nat \<Rightarrow> state \<Rightarrow> state" where
  "applySym2State p s (Ident sn) = applySym2Const p (s (Ident sn))" |
  "applySym2State p s (Para sn i) = applySym2Const p (s (Para sn ((inv p) i)))"|
  "applySym2State p s dontCareVar = applySym2Const p (s dontCareVar)"



text \<open>Applying a permutation to a state\<close>
fun applyDSym2State :: "nat2nat \<Rightarrow> state \<Rightarrow> state" where
  "applyDSym2State p s (Ident sn) = applyDSym2Const p (s (Ident sn))" |
  "applyDSym2State p s (Para sn i) = applyDSym2Const p (s (Para sn ( i)))"|
  "applyDSym2State p s dontCareVar = applyDSym2Const p (s dontCareVar)"


lemma applySym2StateInv [simp]:
  assumes "bij p"
  shows "applySym2State p (applySym2State (inv p) s) v = s v"
proof (induction v)
  case (Ident nm)
  then show ?case by (auto simp add: assms)
next
  case (Para nm i)
  then show ?case
    by (simp add: assms bij_is_surj surj_imp_inj_inv)
next
  case dontCareVar
  then show ?case by (auto simp add: assms)
qed


lemma applyDSym2StateInv [simp]:
  assumes "bij p"
  shows "applyDSym2State p (applyDSym2State (inv p) s) v = s v"
proof (induction v)
  case (Ident nm)
  then show ?case by (auto simp add: assms)
next
  case (Para nm i)
  then show ?case
    by (simp add: assms bij_is_surj surj_imp_inj_inv)
next
  case dontCareVar
  then show ?case by (auto simp add: assms)
qed


lemma stFormSymCorrespondence:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval (applySym2Exp p e) (applySym2State p s) = applySym2Const p (expEval e s) \<and>
         formEval (applySym2Form p f) (applySym2State p s) = formEval f s"
proof (induction rule: expType_formula.induct)
  case (IVar x)
  have "bij p"
    using assms by (simp add: permutes_bij)
  then show ?case
    apply (cases x)
    by (auto simp add: bijection.intro bijection.inv_left)
next
  case (eqn x1 x2)
  have "bij p"
    using assms by (simp add: permutes_bij)
  show ?case by (auto simp add: eqn \<open>bij p\<close>)
qed (auto)


lemma stFormDSymCorrespondence:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval (applyDSym2Exp p e) (applyDSym2State p s) = applyDSym2Const p (expEval e s) \<and>
         formEval (applyDSym2Form p f) (applyDSym2State p s) = formEval f s"
proof (induction rule: expType_formula.induct)
  case (IVar x)
  have "bij p"
    using assms by (simp add: permutes_bij)
  then show ?case
    apply (cases x)
    by (auto simp add: bijection.intro bijection.inv_left)
next
  case (eqn x1 x2)
  have "bij p"
    using assms by (simp add: permutes_bij)
  show ?case by (auto simp add: eqn \<open>bij p\<close>)
qed (auto)

lemma stFormSymCorrespondence1:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval (applySym2Exp p e) (applySym2State p s) = applySym2Const p (expEval e s)"
        "formEval (applySym2Form p f) (applySym2State p s) = formEval f s"
  using stFormSymCorrespondence assms by auto


lemma stFormDSymCorrespondence1:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval (applyDSym2Exp p e) (applyDSym2State p s) = applyDSym2Const p (expEval e s)"
        "formEval (applyDSym2Form p f) (applyDSym2State p s) = formEval f s"
  using stFormDSymCorrespondence assms by auto



lemma stFormSymCorrespondence2:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval e (applySym2State  p s) = applySym2Const  p (expEval (applySym2Exp  (inv p) e) s)"
        "formEval f (applySym2State  p s) = formEval (applySym2Form  (inv p) f) s"
proof -
  have "bij p"
    using assms permutes_bij by auto
  show "expEval  e (applySym2State  p s) = applySym2Const  p (expEval (applySym2Exp  (inv p) e) s)"
    unfolding stFormSymCorrespondence1(1)[OF assms,symmetric]
    using \<open>bij p\<close> by auto
  show "formEval f (applySym2State  p s) = formEval (applySym2Form  (inv p) f) s"
    by (metis \<open>bij p\<close> applySym2ExpFormInv assms stFormSymCorrespondence)
   (* unfolding stFormSymCorrespondence1(2)[OF assms, of "applySym2Form (inv p) f", symmetric]
    unfolding stFormSymCorrespondence1(2)[OF assms]
    using \<open>bij p\<close> by auto*)
qed

lemma stFormDSymCorrespondence2:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval e (applyDSym2State p s) = applyDSym2Const p (expEval (applyDSym2Exp (inv p) e) s)"
        "formEval f (applyDSym2State p s) = formEval (applyDSym2Form (inv p) f) s"
proof -
  have "bij p"
    using assms permutes_bij by auto
  show "expEval e (applyDSym2State p s) = applyDSym2Const p (expEval (applyDSym2Exp (inv p) e) s)"
    unfolding stFormDSymCorrespondence1(1)[OF assms,symmetric]
    using \<open>bij p\<close> by auto
  show "formEval f (applyDSym2State p s) = formEval (applyDSym2Form (inv p) f) s"
    unfolding stFormDSymCorrespondence1(2)[OF assms, of "applyDSym2Form (inv p) f", symmetric]
    using \<open>bij p\<close> by auto
qed

lemma stFormSymCorrespondence3:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval e (applySym2State (inv p) s) = applySym2Const (inv p) (expEval (applySym2Exp p e) s)"
        "formEval f (applySym2State (inv p) s) = formEval (applySym2Form p f) s"
proof -
  have a: "(inv p) permutes {x. x \<le> N}"
    by (simp add: assms permutes_inv)
  have b: "bij p"
    using assms permutes_bij by auto
  then have c: "inv (inv p) = p"
    using inv_inv_eq by auto
  show "expEval e (applySym2State (inv p) s) = applySym2Const (inv p) (expEval (applySym2Exp p e) s)"
    using stFormSymCorrespondence2(1)[OF a] c by auto
  show "formEval f (applySym2State (inv p) s) = formEval (applySym2Form p f) s"
    using stFormSymCorrespondence2(2)[OF a] c by auto
qed


lemma stFormDSymCorrespondence3:
  assumes "p permutes {x. x \<le> N}"
  shows "expEval e (applyDSym2State (inv p) s) = applyDSym2Const (inv p) (expEval (applyDSym2Exp p e) s)"
        "formEval f (applyDSym2State (inv p) s) = formEval (applyDSym2Form p f) s"
proof -
  have a: "(inv p) permutes {x. x \<le> N}"
    by (simp add: assms permutes_inv)
  have b: "bij p"
    using assms permutes_bij by auto
  then have c: "inv (inv p) = p"
    using inv_inv_eq by auto
  show "expEval e (applyDSym2State (inv p) s) = applyDSym2Const (inv p) (expEval (applyDSym2Exp p e) s)"
    using stFormDSymCorrespondence2(1)[OF a] c by auto
  show "formEval f (applyDSym2State (inv p) s) = formEval (applyDSym2Form p f) s"
    using stFormDSymCorrespondence2(2)[OF a] c by auto
qed

lemma varOfStmtApplySym2Statement [simp]:
  "varOfStmt (applySym2Statement p S) = (applySym2Var p) ` (varOfStmt S)"
  apply (induction S) by (auto simp add: varOfStmt.simps(5,6))


lemma varOfStmtApplyDSym2Statement [simp]:
  "varOfStmt (applyDSym2Statement p S) =  (varOfStmt S)"
  apply (induction S) by (auto simp add: varOfStmt.simps(5,6))

lemma applySym2VarEq:
  assumes "p permutes {x. x \<le> N}"
  shows
    "applySym2Var p v = Ident x \<Longrightarrow> v = Ident x"
    "applySym2Var p v = Para nm i \<Longrightarrow> v = Para nm (inv p i)"
    "applySym2Var p v = dontCareVar \<Longrightarrow> v = dontCareVar"
proof -
  have "bij p"
    using assms by (auto simp add: permutes_bij)
  show "applySym2Var p v = Para nm i \<Longrightarrow> v = Para nm (inv p i)"
    apply (cases v)
    by (auto simp add: \<open>bij p\<close> bij_inv_eq_iff)
qed (cases v, auto)+


lemma trans1Symmetric:
  assumes "p permutes {x. x \<le> N}"
  shows "applySym2State p (trans1 S s0) = trans1 (applySym2Statement p S) (applySym2State p s0)"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  have "applySym2State p (trans1 (assign x) s0) v =
        trans1 (applySym2Statement p (assign x)) (applySym2State p s0) v" for v
  proof (cases v)
    case (Ident x1)
    show ?thesis
      by (simp add: Ident applySym2VarEq(1)[OF assms] stFormSymCorrespondence[OF assms])
  next
    case (Para x21 x22)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "p (inv p x22) = x22"
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    show ?thesis
      by (auto simp add: Para * applySym2VarEq(2)[OF assms] stFormSymCorrespondence[OF assms])
  next
    case dontCareVar
    show ?thesis
      by (simp add: dontCareVar applySym2VarEq(3)[OF assms] stFormSymCorrespondence[OF assms])
  qed
  then show ?case
    by (rule ext)
next
  case (parallel S1 S2)
  have "applySym2State p (trans1 (parallel S1 S2) s0) v =
        trans1 (applySym2Statement p (parallel S1 S2)) (applySym2State p s0) v" for v
  proof (cases v)
    case dontCareVar
    have 1: "dontCareVar \<in> applySym2Var p ` varOfStmt S1 \<longleftrightarrow> dontCareVar \<in> varOfStmt S1"
      apply (auto simp add: applySym2VarEq(1)[OF assms])
       apply (metis (full_types) applySym2Var.simps(1,2) varType.distinct(5) varType.exhaust)
      by force
    show ?thesis
      by (auto simp add: dontCareVar 1 parallel[symmetric])
  next    
    case (Ident x)
    have 1: "Ident x \<in> applySym2Var p ` varOfStmt S1 \<longleftrightarrow> Ident x \<in> varOfStmt S1"
      apply (auto simp add: applySym2VarEq(3)[OF assms])
       apply (metis (full_types) applySym2Var.simps varType.distinct(1) varType.exhaust)
      by force
    show ?thesis
      by (auto simp add: Ident 1 parallel[symmetric])
  next
    case (Para nm i)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "inv p (p x) = x" for x
      by (simp add: \<open>bij p\<close> bij_is_inj)
    have **: "p (inv p x) = x" for x
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    have 1: "Para nm i \<in> applySym2Var p ` varOfStmt S1 \<longleftrightarrow> Para nm (inv p i) \<in> varOfStmt S1"
      apply (auto simp add: applySym2VarEq(2)[OF assms])
      subgoal for x apply (cases x) by (auto simp add: *)
      by (metis "**" applySym2Var.simps(2) image_iff)
    show ?thesis
      by (auto simp add: Para 1 parallel[symmetric])
  qed
  then show ?case
    by (rule ext)
next
  case (iteStm b S1 S2)
  show ?case
    apply (rule ext)
    by (auto simp add: stFormSymCorrespondence1[OF assms] iteStm)
next
  case (forallStm ps N)
  have "applySym2State p (trans1 (forallStm ps N) s0) v =
        trans1 (applySym2Statement p (forallStm ps N)) (applySym2State p s0) v" for v
  proof (cases v)
    case (Ident x)
    have 1: "Ident x \<in> applySym2Var p ` varOfStmt (ps i) \<longleftrightarrow> Ident x \<in> varOfStmt (ps i)" for i
      apply (auto simp add: applySym2VarEq(3)[OF assms])
       apply (metis (full_types) applySym2Var.simps varType.distinct(1) varType.exhaust)
      by force
    have 2: "largestInd (Ident x) N ps = None \<longleftrightarrow> largestInd (Ident x) N (\<lambda>i. applySym2Statement p (ps i)) = None"
      by (simp add: largestIndNone 1)
    have 3: "largestInd (Ident x) N ps = Some i \<longleftrightarrow> largestInd (Ident x) N (\<lambda>i. applySym2Statement p (ps i)) = Some i" for i
      by (simp add: largestIndSome 1)
    show ?thesis
      apply (auto simp add: Ident)
      apply (cases "largestInd (Ident x) N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStm[symmetric])
      done
  next
    case (Para nm i)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "inv p (p x) = x" for x
      by (simp add: \<open>bij p\<close> bij_is_inj)
    have **: "p (inv p x) = x" for x
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    have 1: "Para nm i \<in> applySym2Var p ` varOfStmt (ps i) \<longleftrightarrow> Para nm (inv p i) \<in> varOfStmt (ps i)"
      apply (auto simp add: applySym2VarEq(2)[OF assms])
      subgoal for x apply (cases x) by (auto simp add: *)
      by (metis "**" applySym2Var.simps(2) image_iff)
    have 2: "largestInd (Para nm (inv p i)) N ps = None \<longleftrightarrow> largestInd (Para nm i) N (\<lambda>i. applySym2Statement p (ps i)) = None"
      apply (auto simp add: largestIndNone)
       apply (metis \<open>bij p\<close> applySym2Var.simps(2) applySym2VarInv bij_betw_inv_into inv_inv_eq)
      by (metis "**" applySym2Var.simps(2) image_iff)
    have 3: "largestInd (Para nm (inv p i)) N ps = Some j \<longleftrightarrow> largestInd (Para nm i) N (\<lambda>i. applySym2Statement p (ps i)) = Some j" for j
      apply (auto simp add: largestIndSome)
         apply (metis "**" applySym2Var.simps(2) image_iff)
        apply (metis \<open>bij p\<close> applySym2Var.simps(2) applySym2VarInv bij_betw_inv_into inv_inv_eq)
       apply (metis \<open>bij p\<close> applySym2Var.simps(2) applySym2VarInv assms bij_betw_inv_into permutes_inv_inv)
      by (metis "**" applySym2Var.simps(2) image_iff)
    show ?thesis
    proof (cases "largestInd (Para nm (inv p i)) N ps")
      case None
      then show ?thesis
        using Para 2 by auto
    next
      case (Some j)
      then show ?thesis
        unfolding Para using 3[of j]
        by (auto simp add: forallStm[symmetric])
    qed
  next
    case dontCareVar
    have 1: "dontCareVar \<in> applySym2Var p ` varOfStmt (ps i) \<longleftrightarrow> dontCareVar \<in> varOfStmt (ps i)" for i
      apply (auto simp add: applySym2VarEq(1)[OF assms])
       apply (metis (full_types) applySym2Var.simps(1,2) varType.distinct(5) varType.exhaust)
      by force
    have 2: "largestInd dontCareVar N ps = None \<longleftrightarrow> largestInd dontCareVar N (\<lambda>i. applySym2Statement p (ps i)) = None"
      by (simp add: largestIndNone 1)
    have 3: "largestInd dontCareVar N ps = Some i \<longleftrightarrow> largestInd dontCareVar N (\<lambda>i. applySym2Statement p (ps i)) = Some i" for i
      by (simp add: largestIndSome 1)
    show ?thesis
      apply (auto simp add: dontCareVar)
      apply (cases "largestInd dontCareVar N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStm[symmetric])
      done
  qed
  then show ?case
    by (rule ext)
next
  case (forallStmExcl ps j N)
  have "applySym2State p (trans1 (forallStmExcl ps j N) s0) v =
        trans1 (applySym2Statement p (forallStmExcl ps j N)) (applySym2State p s0) v" for v
  proof (cases v)
    case (Ident x)
    have 1: "Ident x \<in> applySym2Var p ` varOfStmt (ps i) \<longleftrightarrow> Ident x \<in> varOfStmt (ps i)" for i
      apply (auto simp add: applySym2VarEq(3)[OF assms])
       apply (metis (full_types) applySym2Var.simps varType.distinct(1) varType.exhaust)
      by force
    have 2: "largestIndExcl (Ident x) j N ps = None \<longleftrightarrow>
             largestIndExcl (Ident x) j N (\<lambda>i. applySym2Statement p (ps i)) = None"
      by (simp add: largestIndExclNone 1)
    have 3: "largestIndExcl (Ident x) j N ps = Some i \<longleftrightarrow>
             largestIndExcl (Ident x) j N (\<lambda>i. applySym2Statement p (ps i)) = Some i" for i
      by (simp add: largestIndExclSome 1)
    show ?thesis
      apply (auto simp add: Ident)
      apply (cases "largestIndExcl (Ident x) j N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStmExcl[symmetric])
      done
  next
    case (Para nm i)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "inv p (p x) = x" for x
      by (simp add: \<open>bij p\<close> bij_is_inj)
    have **: "p (inv p x) = x" for x
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    have 1: "Para nm i \<in> applySym2Var p ` varOfStmt (ps i) \<longleftrightarrow> Para nm (inv p i) \<in> varOfStmt (ps i)"
      apply (auto simp add: applySym2VarEq(2)[OF assms])
      subgoal for x apply (cases x) by (auto simp add: *)
      by (metis "**" applySym2Var.simps(2) image_iff)
    have 2: "largestIndExcl (Para nm (inv p i)) j N ps = None \<longleftrightarrow>
             largestIndExcl (Para nm i) j N (\<lambda>i. applySym2Statement p (ps i)) = None"
      apply (auto simp add: largestIndExclNone)
       apply (metis \<open>bij p\<close> applySym2Var.simps(2) applySym2VarInv bij_betw_inv_into inv_inv_eq)
      by (metis "**" applySym2Var.simps(2) image_iff)
    have 3: "largestIndExcl (Para nm (inv p i)) j N ps = Some k \<longleftrightarrow>
             largestIndExcl (Para nm i) j N (\<lambda>i. applySym2Statement p (ps i)) = Some k" for k
      apply (auto simp add: largestIndExclSome)
         apply (metis "**" applySym2Var.simps(2) image_iff)
        apply (metis \<open>bij p\<close> applySym2Var.simps(2) applySym2VarInv bij_betw_inv_into inv_inv_eq)
       apply (metis \<open>bij p\<close> applySym2Var.simps(2) applySym2VarInv assms bij_betw_inv_into permutes_inv_inv)
      by (metis "**" applySym2Var.simps(2) image_iff)
    show ?thesis
    proof (cases "largestIndExcl (Para nm (inv p i)) j N ps")
      case None
      then show ?thesis
        using Para 2 by auto
    next
      case (Some j)
      then show ?thesis
        unfolding Para using 3[of j]
        by (auto simp add: forallStmExcl[symmetric])
    qed
  next
    case dontCareVar
    have 1: "dontCareVar \<in> applySym2Var p ` varOfStmt (ps i) \<longleftrightarrow> dontCareVar \<in> varOfStmt (ps i)" for i
      apply (auto simp add: applySym2VarEq(1)[OF assms])
       apply (metis (full_types) applySym2Var.simps(1,2) varType.distinct(5) varType.exhaust)
      by force
    have 2: "largestIndExcl dontCareVar j N ps = None \<longleftrightarrow>
             largestIndExcl dontCareVar j N (\<lambda>i. applySym2Statement p (ps i)) = None"
      by (simp add: largestIndExclNone 1)
    have 3: "largestIndExcl dontCareVar j N ps = Some i \<longleftrightarrow>
             largestIndExcl dontCareVar j N (\<lambda>i. applySym2Statement p (ps i)) = Some i" for i
      by (simp add: largestIndExclSome 1)
    show ?thesis
      apply (auto simp add: dontCareVar)
      apply (cases "largestIndExcl dontCareVar j N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStmExcl[symmetric])
      done
  qed
  then show ?case
    by (rule ext)
qed



lemma trans1DSymmetric:
  assumes "p permutes {x. x \<le> N}"
  shows "applyDSym2State p (trans1 S s0) = trans1 (applyDSym2Statement p S) (applyDSym2State p s0)"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  have "applyDSym2State p (trans1 (assign x) s0) v =
        trans1 (applyDSym2Statement p (assign x)) (applyDSym2State p s0) v" for v
  proof (cases v)
    case (Ident x1)
    show ?thesis
      by (simp add: Ident   stFormDSymCorrespondence[OF assms])
  next
    case (Para x21 x22)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "p (inv p x22) = x22"
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    show ?thesis
      by (auto simp add: Para *  stFormDSymCorrespondence[OF assms])
  next
    case dontCareVar
    show ?thesis
      by (simp add: dontCareVar  stFormDSymCorrespondence[OF assms])
  qed
  then show ?case
    by (rule ext)
next
  case (parallel S1 S2)
  have "applyDSym2State p (trans1 (parallel S1 S2) s0) v =
        trans1 (applyDSym2Statement p (parallel S1 S2)) (applyDSym2State p s0) v" for v
  proof (cases v)
    case dontCareVar
    have 1: "dontCareVar \<in> applySym2Var p ` varOfStmt S1 \<longleftrightarrow> dontCareVar \<in> varOfStmt S1"
      apply (auto simp add: applySym2VarEq(1)[OF assms])
       apply (metis (full_types) applySym2Var.simps(1,2) varType.distinct(5) varType.exhaust)
      by force
    show ?thesis
      by (auto simp add: dontCareVar 1 parallel[symmetric])
  next    
    case (Ident x)
    have 1: "Ident x \<in> applySym2Var p ` varOfStmt S1 \<longleftrightarrow> Ident x \<in> varOfStmt S1"
      apply (auto simp add: applySym2VarEq(3)[OF assms])
       apply (metis (full_types) applySym2Var.simps varType.distinct(1) varType.exhaust)
      by force
    show ?thesis
      by (auto simp add: Ident 1 parallel[symmetric])
  next
    case (Para nm i)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "inv p (p x) = x" for x
      by (simp add: \<open>bij p\<close> bij_is_inj)
    have **: "p (inv p x) = x" for x
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    have 1: "Para nm i \<in> applySym2Var p ` varOfStmt S1 \<longleftrightarrow> Para nm (inv p i) \<in> varOfStmt S1"
      apply (auto simp add: applySym2VarEq(2)[OF assms])
      subgoal for x apply (cases x) by (auto simp add: *)
      by (metis "**" applySym2Var.simps(2) image_iff)
    show ?thesis
      by (auto simp add: Para 1 parallel[symmetric])
  qed
  then show ?case
    by (rule ext)
next
  case (iteStm b S1 S2)
  show ?case
    apply (rule ext)
    by (auto simp add: stFormDSymCorrespondence1[OF assms] iteStm)
next
  case (forallStm ps N)
  have "applyDSym2State p (trans1 (forallStm ps N) s0) v =
        trans1 (applyDSym2Statement p (forallStm ps N)) (applyDSym2State p s0) v" for v
  proof (cases v)
    case (Ident x)
    (*have 1: "Ident x \<in> varOfStmt (ps i) \<longleftrightarrow> Ident x \<in> varOfStmt (ps i)" for i
      apply (auto )
       apply (metis (full_types) applySym2Var.simps varType.distinct(1) varType.exhaust)
      by force*)
    have 2: "largestInd (Ident x) N ps = None \<longleftrightarrow> largestInd (Ident x) N (\<lambda>i. applyDSym2Statement p (ps i)) = None"
      by (simp add: largestIndNone )
    have 3: "largestInd (Ident x) N ps = Some i \<longleftrightarrow> largestInd (Ident x) N (\<lambda>i. applyDSym2Statement p (ps i)) = Some i" for i
      by (simp add: largestIndSome )
    show ?thesis
      apply (auto simp add: Ident)
      apply (cases "largestInd (Ident x) N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStm[symmetric])
      done
  next
    case (Para nm i)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "inv p (p x) = x" for x
      by (simp add: \<open>bij p\<close> bij_is_inj)
    have **: "p (inv p x) = x" for x
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
    (*have 1: "Para nm i \<in> applySym2Var p ` varOfStmt (ps i) \<longleftrightarrow> Para nm (inv p i) \<in> varOfStmt (ps i)"
      apply (auto simp add: applySym2VarEq(2)[OF assms])
      subgoal for x apply (cases x) by (auto simp add: 
      by (metis "**" applySym2Var.simps(2) image_iff)*)
    have 2: "largestInd (Para nm ( i)) N ps = None \<longleftrightarrow> largestInd (Para nm i) N (\<lambda>i. applyDSym2Statement p (ps i)) = None"
      by (auto simp add: largestIndNone) 
    have 3: "largestInd (Para nm ( i)) N ps = Some j \<longleftrightarrow> largestInd (Para nm i) N (\<lambda>i. applyDSym2Statement p (ps i)) = Some j" for j
     by (auto simp add: largestIndSome)
         
    show ?thesis
    proof (cases "largestInd (Para nm ( i)) N ps")
      case None
      then show ?thesis
        using Para 2 by auto
    next
      case (Some j)
      then show ?thesis
        unfolding Para using 3[of j]
        by (auto simp add: forallStm[symmetric])
    qed
  next
    case dontCareVar
     
    have 2: "largestInd dontCareVar N ps = None \<longleftrightarrow> largestInd dontCareVar N (\<lambda>i. applyDSym2Statement p (ps i)) = None"
      by (simp add: largestIndNone )
    have 3: "largestInd dontCareVar N ps = Some i \<longleftrightarrow> largestInd dontCareVar N (\<lambda>i. applyDSym2Statement p (ps i)) = Some i" for i
      by (simp add: largestIndSome )
    show ?thesis
      apply (auto simp add: dontCareVar)
      apply (cases "largestInd dontCareVar N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStm[symmetric])
      done
  qed
  then show ?case
    by (rule ext)
next
  case (forallStmExcl ps j N)
  have "applyDSym2State p (trans1 (forallStmExcl ps j N) s0) v =
        trans1 (applyDSym2Statement p (forallStmExcl ps j N)) (applyDSym2State p s0) v" for v
  proof (cases v)
    case (Ident x)
     
    have 2: "largestIndExcl (Ident x) j N ps = None \<longleftrightarrow>
             largestIndExcl (Ident x) j N (\<lambda>i. applyDSym2Statement p (ps i)) = None"
      by (simp add: largestIndExclNone )
    have 3: "largestIndExcl (Ident x) j N ps = Some i \<longleftrightarrow>
             largestIndExcl (Ident x) j N (\<lambda>i. applyDSym2Statement p (ps i)) = Some i" for i
      by (simp add: largestIndExclSome )
    show ?thesis
      apply (auto simp add: Ident)
      apply (cases "largestIndExcl (Ident x) j N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStmExcl[symmetric])
      done
  next
    case (Para nm i)
    have "bij p"
      using assms by (auto simp add: permutes_bij)
    have *: "inv p (p x) = x" for x
      by (simp add: \<open>bij p\<close> bij_is_inj)
    have **: "p (inv p x) = x" for x
      by (meson \<open>bij p\<close> bij_inv_eq_iff)
     
    have 2: "largestIndExcl (Para nm (  i)) j N ps = None \<longleftrightarrow>
             largestIndExcl (Para nm i) j N (\<lambda>i. applyDSym2Statement p (ps i)) = None"
     by (auto simp add: largestIndExclNone)
        
    have 3: "largestIndExcl (Para nm (  i)) j N ps = Some k \<longleftrightarrow>
             largestIndExcl (Para nm i) j N (\<lambda>i. applyDSym2Statement p (ps i)) = Some k" for k
      by (auto simp add: largestIndExclSome)
         
    show ?thesis
    proof (cases "largestIndExcl (Para nm (  i)) j N ps")
      case None
      then show ?thesis
        using Para 2 by auto
    next
      case (Some j)
      then show ?thesis
        unfolding Para using 3[of j]
        by (auto simp add: forallStmExcl[symmetric])
    qed
  next
    case dontCareVar
    
    have 2: "largestIndExcl dontCareVar j N ps = None \<longleftrightarrow>
             largestIndExcl dontCareVar j N (\<lambda>i. applyDSym2Statement p (ps i)) = None"
      by (simp add: largestIndExclNone )
    have 3: "largestIndExcl dontCareVar j N ps = Some i \<longleftrightarrow>
             largestIndExcl dontCareVar j N (\<lambda>i. applyDSym2Statement p (ps i)) = Some i" for i
      by (simp add: largestIndExclSome )
    show ?thesis
      apply (auto simp add: dontCareVar)
      apply (cases "largestIndExcl dontCareVar j N ps")
      subgoal using 2 by auto
      subgoal for i using 3[of i]
        by (auto simp add: forallStmExcl[symmetric])
      done
  qed
  then show ?case
    by (rule ext)
qed


subsection \<open>Typing rules\<close>

primrec getValueType :: "scalrValueType \<Rightarrow> typeType" where
  "getValueType (enum t v) = enumType" |
  "getValueType (index n) = indexType" |
  "getValueType (boolV n) = boolType" |
  "getValueType (dontCare) = anyType" |
  "getValueType (data d) = dataType"

definition typeOf :: "state \<Rightarrow> varType \<Rightarrow> typeType" where [simp]:
  "typeOf s x = getValueType (s x)" 

definition isBoolVal :: "state \<Rightarrow> varType \<Rightarrow> bool" where [simp]:
  "isBoolVal s e \<equiv> typeOf s e = boolType"

definition isEnumVal :: "state \<Rightarrow> varType \<Rightarrow> bool" where [simp]:
  "isEnumVal s e \<equiv> typeOf s e =  enumType"


definition isDataVal :: "state \<Rightarrow> varType \<Rightarrow> bool" where [simp]:
  "isDataVal s e \<equiv> typeOf s e =  dataType"


definition sameType :: "state \<Rightarrow> varType \<Rightarrow> varType \<Rightarrow> bool" where [simp]:
  "sameType s e1 e2 \<equiv> typeOf s e1 = typeOf s e2"

text \<open>Type checking of expressions and formulas\<close>
primrec deriveExp :: "envType \<Rightarrow> expType \<Rightarrow> typeType option" and
        deriveForm :: "envType \<Rightarrow> formula \<Rightarrow> bool" where
  "deriveExp s (Const x) =
    (case x of enum nm i \<Rightarrow> Some enumType
             | boolV b \<Rightarrow> Some boolType
             | index n \<Rightarrow> Some indexType
             | data d \<Rightarrow> Some dataType 
             | _ \<Rightarrow> None)"
| "deriveExp s (IVar v) = (if s v \<noteq> anyType then Some (s v) else None)"
| "deriveExp s (iteForm b e1 e2) = 
    (if (deriveExp s e1 = deriveExp s e2) \<and> (deriveExp s e1 \<noteq> None) \<and> deriveForm s b = True
     then deriveExp s e1 else None)"
| "deriveExp s dontCareExp = None"

| "deriveForm s (eqn e1 e2) = (deriveExp s e1 = deriveExp s e2 \<and> deriveExp s e1 \<noteq> None)"
| "deriveForm s (neg f) = deriveForm s f"
| "deriveForm s (andForm f1 f2) = (deriveForm s f1 \<and> deriveForm s f2)"
| "deriveForm s (orForm f1 f2) = (deriveForm s f1 \<and> deriveForm s f2)"
| "deriveForm s (implyForm f1 f2) = (deriveForm s f1 \<and> deriveForm s f2)"
| "deriveForm s chaos = True"
| "deriveForm s dontCareForm = False"
| "deriveForm s (forallForm pf N) = (\<forall>i\<le>N. deriveForm s (pf i))"
| "deriveForm s (forallFormExcl pf j N) = (\<forall>i\<le>N. deriveForm s (pf i))"
| "deriveForm s (existForm pf N) = (\<forall>i\<le>N. deriveForm s (pf i))"

text \<open>A variable is safe with respect to M if it is not of the form
  a[i] with i > M.\<close>
primrec safeVar :: "varType \<Rightarrow> nat \<Rightarrow> bool" where
  "safeVar (Ident x) M = True" |
  "safeVar (Para n i) M = (i \<le> M)" |
  "safeVar (dontCareVar) M = False"

primrec safeExp :: "envType \<Rightarrow> nat \<Rightarrow> expType \<Rightarrow> bool" and
        safeForm :: "envType \<Rightarrow> nat \<Rightarrow> formula \<Rightarrow> bool" where
  "safeExp s M (Const x) =
    (case x of enum nm i \<Rightarrow> True
             | boolV b \<Rightarrow> True
             | index n \<Rightarrow> n \<le> M
             | data d \<Rightarrow> True
             | _ \<Rightarrow> False)"

| "safeExp s M (IVar v) = (safeVar v M \<and> (s v = enumType \<or> s v = boolType  \<or> s v = dataType))"
| "safeExp env M (iteForm b e1 e2) = (safeExp env  M e1 \<and> safeExp  env M e2 \<and> safeForm  env M b)"
 (* False" *)
| "safeExp env M dontCareExp = False"

(* There are three possibilities:
   1. e1 is of index type, either a safe variable or a constant, and e2 is
      a constant safe index i.
   2. e2 is of index type, either a safe variable or a constant, and e1 is
      a constant safe index i.
   3. both e1 and e2 are either enum or boolean values, and both are safe. *)
| "safeForm env M (eqn e1 e2) =
 ((deriveExp env e1 = Some indexType \<and> safeExp env M e2 \<and> (\<exists>i. e2 = Const (index i)) \<and>
   ((\<exists>v. e1 = IVar v \<and> safeVar v M) \<or> (\<exists>i. e1 = Const (index i)))) \<or>
  (deriveExp env e2 = Some indexType \<and> safeExp env M e1 \<and> (\<exists>i. e1 = Const (index i)) \<and>
   ((\<exists>v. e2 = IVar v \<and> safeVar v M) \<or> (\<exists>i. e2 = Const (index i)))) \<or>
  ((deriveExp env e1 = Some enumType \<or> deriveExp env e1 = Some boolType\<or> deriveExp env e1 = Some dataType) \<and>
   (safeExp env M e1 \<and> safeExp env M e2)))"

| "safeForm env M (neg f) = safeForm env M f"
| "safeForm env M (andForm f1 f2) = (safeForm env M f1 \<and> safeForm env M f2)"
| "safeForm env M (orForm f1 f2) = (safeForm env M f1 \<and> safeForm env M f2)"
| "safeForm env M (implyForm f1 f2) = (safeForm env M f1 \<and> safeForm env M f2)"
| "safeForm env M (forallForm pf N) = False"
| "safeForm env M (existForm pf N) = False"
| "safeForm env M (forallFormExcl pf j N) = False"
| "safeForm env M chaos = True"
| "safeForm env M dontCareForm = False"

text \<open>A state agrees with an environment.\<close>
definition fitEnv :: "state \<Rightarrow> envType \<Rightarrow> bool" where
  "fitEnv s env = (\<forall>v. env v \<noteq> anyType \<longrightarrow> typeOf s v = env v)"

subsection \<open>Reachability\<close>

inductive reachableUpTo :: "formula set \<Rightarrow> rule set \<Rightarrow> nat \<Rightarrow> state \<Rightarrow> bool" where
  reachableSet0: "\<forall>f\<in>fs. formEval f s \<Longrightarrow> reachableUpTo fs rs 0 s"
| reachableSetNext: "reachableUpTo fs rs n s \<Longrightarrow> guard g a \<in> rs \<Longrightarrow> formEval g s \<Longrightarrow>
                     reachableUpTo fs rs (Suc n) (trans1 a s)"

inductive_cases reachableUpTo0: "reachableUpTo  fs rs 0 s"
inductive_cases reachableUpToSuc: "reachableUpTo  fs rs (Suc n) s"

text \<open>A set of rules is symmetric\<close>
definition symProtRules :: "nat \<Rightarrow> rule set \<Rightarrow> bool" where [simp]:
  "symProtRules N rs = (\<forall>p r. p permutes {x. x \<le> N} \<and> r \<in> rs \<longrightarrow> applySym2Rule p r \<in> rs)"


definition DsymProtRules :: "nat \<Rightarrow> rule set \<Rightarrow> bool" where [simp]:
  "DsymProtRules N rs = (\<forall>p r. p permutes {x. x \<le> N} \<and> r \<in> rs \<longrightarrow> applyDSym2Rule p r \<in> rs)"


text \<open>A list of formulas is symmetric\<close>
definition symPredSet :: "nat \<Rightarrow> formula set \<Rightarrow> bool" where [simp]:
  "symPredSet  N fs = (\<forall>p f. p permutes {x. x \<le> N} \<and> f \<in> fs \<longrightarrow> applySym2Form  p f \<in> fs)"

text \<open>A list of formulas is symmetric\<close>
definition DsymPredSet :: "nat \<Rightarrow> formula set \<Rightarrow> bool" where [simp]:
  "DsymPredSet N fs = (\<forall>p f. p permutes {x. x \<le> N} \<and> f \<in> fs \<longrightarrow> applyDSym2Form p f \<in> fs)"

lemma reachSymLemma:
  assumes "symPredSet  N fs"
    and "symProtRules  N rs"
    and "p permutes {x. x \<le> N}"
  shows "\<forall>s. reachableUpTo  fs rs i s \<longrightarrow> reachableUpTo  fs rs i (applySym2State  p s)"
proof (induction i)
  case 0
  show ?case
    apply clarify subgoal for s
      apply (auto elim!: reachableUpTo0)
      apply (rule reachableUpTo.intros(1))
      apply (auto simp add: stFormSymCorrespondence2(2)[OF assms(3)])
      using assms(1,3) permutes_inv unfolding symPredSet_def
      by (metis applySym2ExpFormInv permutes_bij)  
    done
next
  case (Suc i)
  have 1: "guard g a \<in> rs \<Longrightarrow> guard (applySym2Form  p g) (applySym2Statement  p a) \<in> rs" for g a
    using assms(2,3) unfolding symProtRules_def by force
  show ?case
    apply clarify subgoal for s
      apply (auto elim!: reachableUpToSuc)
      subgoal for s0 g a
        unfolding trans1Symmetric[OF assms(3)]
        apply (rule reachableUpTo.intros(2))
        subgoal using Suc by auto
        using 1 apply auto
        using stFormSymCorrespondence1[OF assms(3)] by auto
      done
    done
qed


lemma reachDSymLemma:
  assumes "DsymPredSet N fs"
    and "DsymProtRules N rs"
    and "p permutes {x. x \<le> N}"
  shows "\<forall>s. reachableUpTo fs rs i s \<longrightarrow> reachableUpTo  fs rs i (applyDSym2State p s)"
proof (induction i)
  case 0
  show ?case
    apply clarify subgoal for s
      apply (auto elim!: reachableUpTo0)
      apply (rule reachableUpTo.intros(1))
      apply (auto simp add: stFormDSymCorrespondence2(2)[OF assms(3)])
      using assms(1,3) permutes_inv unfolding DsymPredSet_def
      by metis
    done
next
  case (Suc i)
  have 1: "guard g a \<in> rs \<Longrightarrow> guard (applyDSym2Form p g) (applyDSym2Statement p a) \<in> rs" for g a
    using assms(2,3) unfolding DsymProtRules_def by force
  show ?case
    apply clarify subgoal for s
      apply (auto elim!: reachableUpToSuc)
      subgoal for s0 g a
        unfolding trans1DSymmetric[OF assms(3)]
        apply (rule reachableUpTo.intros(2))
        subgoal using Suc by auto
        using 1 apply auto
        using stFormDSymCorrespondence1[OF assms(3)] by auto
      done
    done
qed

lemma SymLemma:
  assumes "symPredSet N fs"
    and "symProtRules N rs"
    and "\<forall>s i. reachableUpTo fs rs i s \<longrightarrow> formEval f s"
    and "p permutes {x. x \<le> N}"
    and "reachableUpTo fs rs i s"
  shows "formEval (applySym2Form p f) s"
proof -
  have "bij p"
    using assms(4) permutes_bij by blast
  have 0: "(inv p) permutes {x. x \<le> N}"
    using assms(4)
    by (simp add: permutes_inv)
  have 1: "reachableUpTo fs rs i (applySym2State (inv p) s)"
    using reachSymLemma[OF assms(1,2) 0] assms(5) by auto 
  have 2: "formEval (applySym2Form p f) (applySym2State p (applySym2State (inv p) s))"
    unfolding stFormSymCorrespondence1[OF assms(4)]
    using 1 assms(3) by auto
  then show ?thesis
    unfolding applySym2StateInv[OF \<open>bij p\<close>] by auto
qed


lemma DSymLemma:
  assumes "DsymPredSet N fs"
    and "DsymProtRules N rs"
    and "\<forall>s i. reachableUpTo fs rs i s \<longrightarrow> formEval f s"
    and "p permutes {x. x \<le> N}"
    and "reachableUpTo fs rs i s"
  shows "formEval (applyDSym2Form p f) s"
proof -
  have "bij p"
    using assms(4) permutes_bij by blast
  have 0: "(inv p) permutes {x. x \<le> N}"
    using assms(4)
    by (simp add: permutes_inv)
  have 1: "reachableUpTo fs rs i (applyDSym2State (inv p) s)"
    using reachDSymLemma[OF assms(1,2) 0] assms(5) by auto 
  have 2: "formEval (applyDSym2Form p f) (applyDSym2State p (applyDSym2State (inv p) s))"
    unfolding stFormDSymCorrespondence1[OF assms(4)]
    using 1 assms(3) by auto
  then show ?thesis
    unfolding applyDSym2StateInv[OF \<open>bij p\<close>] by auto
qed


subsection \<open>Rule set parameterized by processes\<close>

text \<open>We consider a special form of rule set, where there is a set associated
to each process i\<close>
definition setOverDownN :: "nat \<Rightarrow> (nat \<Rightarrow> 'a set) \<Rightarrow> 'a set" where
  "setOverDownN N f = {r. \<exists>n\<le>N. r \<in> f n}"

definition setOverDownN2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> 'a set) \<Rightarrow> 'a set"  where
  "setOverDownN2 N f = {r. \<exists>n1 n2. n1\<le>N \<and> n2\<le>N \<and> r \<in> f n1 n2}"

text \<open>There is a general theorem for showing symmetry\<close>
definition symParamRules :: "nat \<Rightarrow> (nat \<Rightarrow> rule set) \<Rightarrow> bool" where
  "symParamRules N f =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> applySym2Rule p ` f i = f (p i))"


text \<open>There is a general theorem for showing symmetry\<close>
definition DsymParamRules :: "nat \<Rightarrow> (nat \<Rightarrow> rule set) \<Rightarrow> bool" where
  "DsymParamRules N f =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> applyDSym2Rule p ` f i = f (p i))"


theorem symProtFromSymParam:
  assumes "symParamRules N f"
  shows "symProtRules N (setOverDownN N f)"
proof -
  have 1: "applySym2Rule p r \<in> f (p n)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "r \<in> f n" for p r n
  proof -
    have "applySym2Rule p ` f n = f (p n)"
      using assms unfolding symParamRules_def
      using that(1,2) by auto
    then show ?thesis
      using that(3) by auto
  qed
  show ?thesis
    unfolding symProtRules_def setOverDownN_def
    apply auto
    subgoal for p r n
      apply (rule exI[where x="p n"])
      apply auto
      using permutes_in_image apply fastforce
      using assms unfolding symParamRules_def
      using 1 by auto
    done
qed


theorem DsymProtFromSymParam:
  assumes "DsymParamRules N f"
  shows "DsymProtRules N (setOverDownN N f)"
proof -
  have 1: "applyDSym2Rule p r \<in> f (p n)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "r \<in> f n" for p r n
  proof -
    have "applyDSym2Rule p ` f n = f (p n)"
      using assms unfolding DsymParamRules_def
      using that(1,2) by auto
    then show ?thesis
      using that(3) by auto
  qed
  show ?thesis
    unfolding symProtRules_def setOverDownN_def
    apply auto
    subgoal for p r n
      apply (rule exI[where x="p n"])
      apply auto
      using permutes_in_image apply fastforce
      using assms unfolding symParamRules_def
      using 1 by auto
    done
qed

definition symParamRule2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> rule) \<Rightarrow> bool" where
  "symParamRule2 N r =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> applySym2Rule p (r i j) = r (p i) (p j))"
definition DsymParamRule2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> rule) \<Rightarrow> bool" where
  "DsymParamRule2 N r =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> applyDSym2Rule p (r i j) = r (p i) (p j))"


definition symParamRules2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> rule set) \<Rightarrow> bool" where
  "symParamRules2 N rs =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> applySym2Rule p ` (rs i j) = rs (p i) (p j))"



definition DsymParamRules2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> rule set) \<Rightarrow> bool" where
  "DsymParamRules2 N rs =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> applyDSym2Rule p ` (rs i j) = rs (p i) (p j))"

lemma symParamRules2Empty:
  "symParamRules2 N (\<lambda>i j. {})"
  unfolding symParamRules2_def by auto


lemma DsymParamRules2Empty:
  "DsymParamRules2 N (\<lambda>i j. {})"
  unfolding DsymParamRules2_def by auto

lemma symParamRules2Insert:
  assumes "symParamRule2 N r"
    and "symParamRules2 N rs"
  shows "symParamRules2 N (\<lambda>i j. insert (r i j) (rs i j))"
  using assms unfolding symParamRule2_def symParamRules2_def by auto


lemma DsymParamRules2Insert:
  assumes "DsymParamRule2 N r"
    and "DsymParamRules2 N rs"
  shows "DsymParamRules2 N (\<lambda>i j. insert (r i j) (rs i j))"
  using assms unfolding DsymParamRule2_def DsymParamRules2_def by auto


theorem symProtFromSymParam2:
  assumes "symParamRules2 N f"
  shows "symProtRules N (setOverDownN2 N f)"
proof -
  have 1: "applySym2Rule p r \<in> f (p n) (p m)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "m \<le> N"  "r \<in> f n m" for p r n m
  proof -
    have "applySym2Rule p ` (f n m)= f (p n) (p m)"
      using assms symParamRules2_def that(1) that(2) that(3) by blast
    then show ?thesis
      using that(4) by blast 
  qed
  show ?thesis
    unfolding symProtRules_def setOverDownN2_def
    apply auto
    subgoal for p r n m
      apply (rule exI[where x="p n"])
      apply (rule conjI)
      apply (metis mem_Collect_eq permutes_def)
      apply (rule exI[where x="p m"])
      apply auto
      using permutes_in_image apply fastforce
      using 1 by blast
    done
qed



theorem DsymProtFromDSymParam2:
  assumes "DsymParamRules2 N f"
  shows "DsymProtRules N (setOverDownN2 N f)"
proof -
  have 1: "applyDSym2Rule p r \<in> f (p n) (p m)"
    if "p permutes {x. x \<le> N}" "n \<le> N" "m \<le> N"  "r \<in> f n m" for p r n m
  proof -
    have "applyDSym2Rule p ` (f n m)= f (p n) (p m)"
      using assms DsymParamRules2_def that(1) that(2) that(3) by blast
    then show ?thesis
      using that(4) by blast 
  qed
  show ?thesis
    unfolding DsymProtRules_def setOverDownN2_def
    apply auto
    subgoal for p r n m
      apply (rule exI[where x="p n"])
      apply (rule conjI)
      apply (metis mem_Collect_eq permutes_def)
      apply (rule exI[where x="p m"])
      apply auto
      using permutes_in_image apply fastforce
      using 1 by blast
    done
qed


subsection \<open>Formula set parameterized by two processes\<close>

text \<open>Likewise, we consider special cases of parameterized formulas.\<close>

definition equivForm :: "formula \<Rightarrow> formula \<Rightarrow> bool" where 
  "equivForm f1 f2 = (\<forall>s. formEval f1 s = formEval f2 s)"

lemma equivFormRefl [simp]:
  "equivForm f f"
  unfolding equivForm_def by auto

lemma equivFormSym:
  "equivForm f1 f2 \<longleftrightarrow> equivForm f2 f1"
  unfolding equivForm_def by auto

lemma equivFormTrans:
  "equivForm f1 f2 \<Longrightarrow> equivForm f2 f3 \<Longrightarrow> equivForm f1 f3"
  unfolding equivForm_def by auto

lemma equivFormAnd:
  "equivForm f1 f2 \<Longrightarrow> equivForm g1 g2 \<Longrightarrow> equivForm (andForm f1 g1) (andForm f2 g2)"
  by (simp add: equivForm_def)

primrec isImplyForm :: "formula \<Rightarrow> bool" where
  "isImplyForm (implyForm A B) = True" |
  "isImplyForm (eqn e1 e2) = False" |
  "isImplyForm (andForm f1 f2) = False" |
  "isImplyForm (neg f1) = False" |
  "isImplyForm (orForm f1 f2) = False" | 
  "isImplyForm (chaos) = False"|
  "isImplyForm (forallForm pf N) = False" |
  "isImplyForm (existForm pf N ) = False" |
  "isImplyForm (dontCareForm) = False" |
  "isImplyForm (forallFormExcl pf N i) = False"

text \<open>Antecedent of an imply form\<close>
primrec ant :: "formula \<Rightarrow> formula" where
  "ant (implyForm A B) = A"

text \<open>Consequent of an imply form\<close>
primrec cons :: "formula \<Rightarrow> formula" where
  "cons (implyForm A B) = B"

definition symParamForm :: "nat \<Rightarrow> (nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "symParamForm N f =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivForm (applySym2Form p (f i)) (f (p i)))"

definition symParamForm2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "symParamForm2 N f =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow>
             equivForm (applySym2Form p (f i j)) (f (p i) (p j)))"


definition DsymParamForm :: "nat \<Rightarrow> (nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "DsymParamForm N f =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivForm (applyDSym2Form p (f i)) (f (p i)))"

definition DsymParamForm2 :: "   nat\<Rightarrow>(nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "DsymParamForm2    N f =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow>
             equivForm (applyDSym2Form p (f i j)) (f (p i) (p j)))"

text \<open>Each pf_i is of the form A_i --> C_i, where A_i and C_i are symmetric in i.\<close>
definition symParamImplyForm :: "nat \<Rightarrow> (nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "symParamImplyForm N pf \<equiv>
    (\<exists>ant cons. pf = (\<lambda>i. ant i \<longrightarrow>\<^sub>f cons i) \<and> symParamForm N ant \<and> symParamForm N cons)"

primrec symParamFormList :: "nat \<Rightarrow> ((nat \<Rightarrow> formula) list) \<Rightarrow> bool" where
  "symParamFormList N [] = True" |
  "symParamFormList N (f#fl) = (symParamForm N f \<and> symParamFormList N fl)" 

primrec symParamImplyFormList :: "nat \<Rightarrow> ((nat \<Rightarrow> formula) list) \<Rightarrow> bool" where
  "symParamImplyFormList N [] = True" |
  "symParamImplyFormList N (f#fl) = (symParamImplyForm N f \<and> symParamImplyFormList N fl)" 

definition symParam2Form2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "symParam2Form2 N f =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> 
             equivForm (applySym2Form p (f i j)) (f (p i) (p j)))"

definition symParam2ImplyForm::"nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "symParam2ImplyForm N pf \<equiv>
    (\<exists>ant cons. pf = (\<lambda>i j. (ant i j \<longrightarrow>\<^sub>f cons i j)) \<and> symParamForm2 N ant \<and> symParamForm2 N cons)"

primrec symParam2Form2List :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list \<Rightarrow> bool" where
  "symParam2Form2List N [] = True" |
  "symParam2Form2List N (f#fs) = (symParam2Form2 N f \<and> symParam2Form2List N fs)"

primrec symParam2ImplyForm2List :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list\<Rightarrow> bool" where
  "symParam2ImplyForm2List N [] = True" |
  "symParam2ImplyForm2List N (f#fs) = (symParam2ImplyForm N f \<and> symParam2ImplyForm2List N fs)"




text \<open>Each pf_i is of the form A_i --> C_i, where A_i and C_i are Dsymmetric in i.\<close>
definition DsymParamImplyForm :: "nat \<Rightarrow> (nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "DsymParamImplyForm N pf \<equiv>
    (\<exists>ant cons. pf = (\<lambda>i. ant i \<longrightarrow>\<^sub>f cons i) \<and> DsymParamForm N ant \<and> DsymParamForm N cons)"

primrec DsymParamFormList :: "nat \<Rightarrow> ((nat \<Rightarrow> formula) list) \<Rightarrow> bool" where
  "DsymParamFormList N [] = True" |
  "DsymParamFormList N (f#fl) = (DsymParamForm N f \<and> DsymParamFormList N fl)" 

primrec DsymParamImplyFormList :: "nat \<Rightarrow> ((nat \<Rightarrow> formula) list) \<Rightarrow> bool" where
  "DsymParamImplyFormList N [] = True" |
  "DsymParamImplyFormList N (f#fl) = (DsymParamImplyForm N f \<and> DsymParamImplyFormList N fl)" 

definition DsymParam2Form2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "DsymParam2Form2 N f =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> 
             equivForm (applySym2Form p (f i j)) (f (p i) (p j)))"

definition DsymParam2ImplyForm::"nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> bool" where
  "DsymParam2ImplyForm N pf \<equiv>
    (\<exists>ant cons. pf = (\<lambda>i j. (ant i j \<longrightarrow>\<^sub>f cons i j)) \<and> DsymParamForm2 N ant \<and> DsymParamForm2 N cons)"

primrec DsymParam2Form2List :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list \<Rightarrow> bool" where
  "DsymParam2Form2List N [] = True" |
  "DsymParam2Form2List N (f#fs) = (DsymParam2Form2 N f \<and> DsymParam2Form2List N fs)"

primrec DsymParam2ImplyForm2List :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list\<Rightarrow> bool" where
  "DsymParam2ImplyForm2List N [] = True" |
  "DsymParam2ImplyForm2List N (f#fs) = (DsymParam2ImplyForm N f \<and> DsymParam2ImplyForm2List N fs)"


lemma symParamFormImply:
  assumes "symParamForm N f1"
    and "symParamForm N f2"
  shows "symParamForm N (\<lambda>i. implyForm (f1 i) (f2 i))"
  using assms equivForm_def unfolding symParamForm_def by auto

lemma symParamFormOr:
  assumes "symParamForm N f1"
    and "symParamForm N f2"
  shows "symParamForm N (\<lambda>i. orForm (f1 i) (f2 i))"
  using assms equivForm_def unfolding symParamForm_def by auto

lemma symParamFormAnd:
  assumes "symParamForm N f1"
    and "symParamForm N f2"
  shows "symParamForm N (\<lambda>i. andForm (f1 i) (f2 i))"
  using assms equivForm_def unfolding symParamForm_def by auto

lemma symParamFormForall:
  assumes "symParamForm2 N f"
  shows "symParamForm N (\<lambda>i. forallForm (\<lambda>j. f i j) N)"
proof -
  have a: "formEval (f (p i) j) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>k\<le>N. formEval (applySym2Form p (f i k)) s" "j \<le> N" for p i j s
  proof -
    have 1: "inv p j \<le> N"
      using that(1,4)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "formEval (applySym2Form p (f i (inv p j))) s"
      using that(3) 1 by auto
    have 3: "equivForm (applySym2Form p (f i (inv p j))) (f (p i) j)"
      using assms that unfolding symParamForm2_def
      using 1 permutes_inverses(1) by fastforce
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  have b: "formEval (applySym2Form p (f i j)) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>k\<le>N. formEval (f (p i) k) s" "j \<le> N" for p i j s
  proof -
    have 1: "p j \<le> N"
      using bij_betwE permutes_imp_bij that(1) that(4) by fastforce
    have 2: "formEval (f (p i) (p j)) s"
      using that(3) 1 by auto
    have 3: "equivForm (applySym2Form p (f i j)) (f (p i) (p j))"
      using assms that unfolding symParamForm2_def by auto
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  show ?thesis
    unfolding symParamForm_def applySym2Form.simps equivForm_def
    using a b by auto
qed

lemma symParamFormForallExcl:
  assumes "symParamForm2 N f"
  shows "symParamForm N (\<lambda>i. forallFormExcl (\<lambda>j. f i j) i N)"
proof -
  have a: "formEval (f (p i) j) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>j\<le>N. j \<noteq> i \<longrightarrow> formEval (applySym2Form p (f i j)) s"
       "j \<le> N" "j \<noteq> p i" for p i s j
  proof -
    have 1: "inv p j \<le> N"
      using that(1,4)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "inv p j \<noteq> i"
    proof (rule ccontr)
      assume b: "\<not>inv p j \<noteq> i"
      have "inv p j = i" using b by auto
      then have "p (inv p j) = p i" by auto
      moreover have "p (inv p j) = j"
        apply (rule bijection.inv_right)
        using bijection.intro permutes_bij that(1) by auto
      ultimately show False
        using that(5) by auto
    qed
    have 3: "formEval (applySym2Form p (f i (inv p j))) s"
      using that(3) 1 2 by auto
    have 4: "equivForm (applySym2Form p (f i (inv p j))) (f (p i) (p (inv p j)))"
      using assms(1) unfolding symParamForm2_def using 1 that by auto
    have 5: "p (inv p j) = j"
      apply (rule bijection.inv_right)
      using bijection.intro permutes_bij that(1) by auto
    show ?thesis
      using 3 4 5 unfolding equivForm_def by auto
  qed
  have b: "formEval (applySym2Form p (f i j)) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>j\<le>N. j \<noteq> p i \<longrightarrow> formEval (f (p i) j) s"
       "j \<le> N" "j \<noteq> i" for p i s j
  proof -
    have 1: "p j \<le> N"
      using that(1,4)
      by (metis (full_types) mem_Collect_eq permutes_def)
    have 2: "p j \<noteq> p i"
    proof (rule ccontr)
      assume b: "\<not>p j \<noteq> p i"
      have "p j = p i" using b by auto
      then have "inv p (p j) = inv p (p i)" by auto
      moreover have "inv p (p j) = j"
        apply (rule bijection.inv_left)
        using bijection.intro permutes_bij that(1) by auto
      moreover have "inv p (p i) = i"
        apply (rule bijection.inv_left)
        using bijection.intro permutes_bij that(1) by auto
      ultimately show False
        using that(5) by auto
    qed
    have 3: "formEval (f (p i) (p j)) s"
      using that(3) 1 2 by auto
    have 4: "equivForm (f (p i) (p j)) (applySym2Form p (f i j))"
      apply (subst equivFormSym)
      using assms(1) unfolding symParamForm2_def by (simp add: that)
    show ?thesis
      using 3 4 unfolding equivForm_def by auto
  qed
  show ?thesis
    unfolding symParamForm_def applySym2Form.simps equivForm_def
    using a b by auto
qed

lemma symParamForm2Imply:
  assumes "symParamForm2 N f1"
    and "symParamForm2 N f2"
  shows "symParamForm2 N (\<lambda>i j. implyForm (f1 i j) (f2 i j))"
  using assms equivForm_def unfolding symParamForm2_def by auto

lemma symParamForm2Or:
  assumes "symParamForm2 N f1"
    and "symParamForm2 N f2"
  shows "symParamForm2 N (\<lambda>i j. orForm (f1 i j) (f2 i j))"
  using assms equivForm_def unfolding symParamForm2_def by auto

lemma symParamForm2And:
  assumes "symParamForm2 N f1"
    and "symParamForm2 N f2"
  shows "symParamForm2 N (\<lambda>i j. andForm (f1 i j) (f2 i j))"
  using assms equivForm_def unfolding symParamForm2_def by auto

lemma symParamFormForallExcl2:
  assumes "symParamForm2 N f"
  shows "symParamForm2 N (\<lambda> j i. forallFormExcl (\<lambda>k. f i k) i N)"
  using assms symParamForm2_def symParamFormForallExcl symParamForm_def by auto


lemma symParamFormForallExcl1:
  assumes "symParamForm2 N f"
  shows "symParamForm2 N (\<lambda>  i j. forallFormExcl (\<lambda>k. f i k) i N)"
  using assms symParamForm2_def symParamFormForallExcl symParamForm_def by auto

lemma symParamForm2Forall1:
  assumes "symParamForm2 N f"
  shows "symParamForm2 N (\<lambda> j i. forallForm (\<lambda>k. f i k ) N)"
  using assms symParamForm2_def symParamFormForall symParamForm_def by auto


lemma symParamForm2Forall2:
  assumes "symParamForm2 N f"
  shows "symParamForm2 N (\<lambda> j i. forallForm (\<lambda>k. f j k ) N)"
  using assms symParamForm2_def symParamFormForall symParamForm_def by auto


  
lemma DsymParamFormImply:
  assumes "DsymParamForm N f1"
    and "DsymParamForm N f2"
  shows "DsymParamForm N (\<lambda>i. implyForm (f1 i) (f2 i))"
  using assms equivForm_def unfolding DsymParamForm_def by auto

lemma DsymParamFormOr:
  assumes "DsymParamForm N f1"
    and "DsymParamForm N f2"
  shows "DsymParamForm N (\<lambda>i. orForm (f1 i) (f2 i))"
  using assms equivForm_def unfolding DsymParamForm_def by auto

lemma DsymParamFormAnd:
  assumes "DsymParamForm N f1"
    and "DsymParamForm N f2"
  shows "DsymParamForm N (\<lambda>i. andForm (f1 i) (f2 i))"
  using assms equivForm_def unfolding DsymParamForm_def by auto

lemma DsymParamFormForall:
  assumes "DsymParamForm2 N f"
  shows "DsymParamForm N (\<lambda>i. forallForm (\<lambda>j. f i j) N)"
proof -
  have a: "formEval (f (p i) j) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>k\<le>N. formEval (applyDSym2Form p (f i k)) s" "j \<le> N" for p i j s
  proof -
    have 1: "inv p j \<le> N"
      using that(1,4)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "formEval (applyDSym2Form p (f i (inv p j))) s"
      using that(3) 1 by auto
    have 3: "equivForm (applyDSym2Form p (f i (inv p j))) (f (p i) j)"
      using assms that unfolding DsymParamForm2_def
      using 1 permutes_inverses(1) by fastforce
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  have b: "formEval (applyDSym2Form p (f i j)) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>k\<le>N. formEval (f (p i) k) s" "j \<le> N" for p i j s
  proof -
    have 1: "p j \<le> N"
      using bij_betwE permutes_imp_bij that(1) that(4) by fastforce
    have 2: "formEval (f (p i) (p j)) s"
      using that(3) 1 by auto
    have 3: "equivForm (applyDSym2Form p (f i j)) (f (p i) (p j))"
      using assms that unfolding DsymParamForm2_def by auto
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  show ?thesis
    unfolding DsymParamForm_def applySym2Form.simps equivForm_def
    using a b by auto
qed



lemma DsymParamFormForallExcl:
  assumes "DsymParamForm2 N f"
  shows "DsymParamForm N (\<lambda>i. forallFormExcl (\<lambda>j. f i j) i N)"
proof -
  have a: "formEval (f (p i) j) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>j\<le>N. j \<noteq> i \<longrightarrow> formEval (applyDSym2Form p (f i j)) s"
       "j \<le> N" "j \<noteq> p i" for p i s j
  proof -
    have 1: "inv p j \<le> N"
      using that(1,4)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "inv p j \<noteq> i"
    proof (rule ccontr)
      assume b: "\<not>inv p j \<noteq> i"
      have "inv p j = i" using b by auto
      then have "p (inv p j) = p i" by auto
      moreover have "p (inv p j) = j"
        apply (rule bijection.inv_right)
        using bijection.intro permutes_bij that(1) by auto
      ultimately show False
        using that(5) by auto
    qed
    have 3: "formEval (applyDSym2Form p (f i (inv p j))) s"
      using that(3) 1 2 by auto
    have 4: "equivForm (applyDSym2Form p (f i (inv p j))) (f (p i) (p (inv p j)))"
      using assms(1) unfolding DsymParamForm2_def using 1 that by auto
    have 5: "p (inv p j) = j"
      apply (rule bijection.inv_right)
      using bijection.intro permutes_bij that(1) by auto
    show ?thesis
      using 3 4 5 unfolding equivForm_def by auto
  qed
  have b: "formEval (applyDSym2Form p (f i j)) s"
    if "p permutes {x. x \<le> N}" "i \<le> N" "\<forall>j\<le>N. j \<noteq> p i \<longrightarrow> formEval (f (p i) j) s"
       "j \<le> N" "j \<noteq> i" for p i s j
  proof -
    have 1: "p j \<le> N"
      using that(1,4)
      by (metis (full_types) mem_Collect_eq permutes_def)
    have 2: "p j \<noteq> p i"
    proof (rule ccontr)
      assume b: "\<not>p j \<noteq> p i"
      have "p j = p i" using b by auto
      then have "inv p (p j) = inv p (p i)" by auto
      moreover have "inv p (p j) = j"
        apply (rule bijection.inv_left)
        using bijection.intro permutes_bij that(1) by auto
      moreover have "inv p (p i) = i"
        apply (rule bijection.inv_left)
        using bijection.intro permutes_bij that(1) by auto
      ultimately show False
        using that(5) by auto
    qed
    have 3: "formEval (f (p i) (p j)) s"
      using that(3) 1 2 by auto
    have 4: "equivForm (f (p i) (p j)) (applyDSym2Form p (f i j))"
      apply (subst equivFormSym)
      using assms(1) unfolding DsymParamForm2_def by (simp add: that)
    show ?thesis
      using 3 4 unfolding equivForm_def by auto
  qed
  show ?thesis
    unfolding DsymParamForm_def applyDSym2Form.simps equivForm_def
    using a b by auto
qed

lemma DsymParamForm2Imply:
  assumes "DsymParamForm2 N f1"
    and "DsymParamForm2 N f2"
  shows "DsymParamForm2 N (\<lambda>i j. implyForm (f1 i j) (f2 i j))"
  using assms equivForm_def unfolding DsymParamForm2_def by auto

lemma DsymParamForm2Or:
  assumes "DsymParamForm2 N f1"
    and "DsymParamForm2 N f2"
  shows "DsymParamForm2 N (\<lambda>i j. orForm (f1 i j) (f2 i j))"
  using assms equivForm_def unfolding DsymParamForm2_def by auto

lemma DsymParamForm2And:
  assumes "DsymParamForm2 N f1"
    and "DsymParamForm2 N f2"
  shows "DsymParamForm2 N (\<lambda>i j. andForm (f1 i j) (f2 i j))"
  using assms equivForm_def unfolding DsymParamForm2_def by auto

lemma DsymParamFormForallExcl2:
  assumes "DsymParamForm2 N f"
  shows "DsymParamForm2 N (\<lambda> j i. forallFormExcl (\<lambda>k. f i k) i N)"
  using assms DsymParamForm2_def DsymParamFormForallExcl DsymParamForm_def by auto


lemma DsymParamFormForallExcl1:
  assumes "DsymParamForm2 N f"
  shows "DsymParamForm2 N (\<lambda>  i j. forallFormExcl (\<lambda>k. f i k) i N)"
  using assms DsymParamForm2_def DsymParamFormForallExcl DsymParamForm_def by auto

lemma DsymParamForm2Forall1:
  assumes "DsymParamForm2 N f"
  shows "DsymParamForm2 N (\<lambda> j i. forallForm (\<lambda>k. f i k ) N)"
  using assms DsymParamForm2_def DsymParamFormForall DsymParamForm_def by auto


lemma DsymParamForm2Forall2:
  assumes "DsymParamForm2 N f"
  shows "DsymParamForm2 N (\<lambda> j i. forallForm (\<lambda>k. f j k ) N)"
  using assms DsymParamForm2_def DsymParamFormForall DsymParamForm_def by auto



subsection \<open>Equivalence of statements and rules\<close>

definition equivStatement :: "statement \<Rightarrow> statement \<Rightarrow> bool" where
  "equivStatement S1 S2 = (varOfStmt S1 = varOfStmt S2 \<and> (\<forall>s. trans1 S1 s = trans1 S2 s))"

lemma equivStatementRefl [intro]:
  "equivStatement S S"
  unfolding equivStatement_def by auto

lemma equivStatementSym:
  "equivStatement S1 S2 \<Longrightarrow> equivStatement S2 S1"
  unfolding equivStatement_def by auto

lemma equivStatementTrans:
  "equivStatement S1 S2 \<Longrightarrow> equivStatement S2 S3 \<Longrightarrow> equivStatement S1 S3"
  unfolding equivStatement_def by auto

lemma equivStatementSkipLeft:
  "equivStatement (skip || S) S"
  unfolding equivStatement_def by auto

lemma unaffectedVars:
  "x \<notin> varOfStmt S \<Longrightarrow> s x = trans1 S s x"
  apply (induction S) apply (auto simp add: varOfStmtEq)
  subgoal for ps N
    apply (cases "largestInd x N ps")
    by (auto simp add: largestIndSome)
  subgoal for ps j N
    apply (cases "largestIndExcl x j N ps")
     apply simp
    using largestIndExclSome varOfStmtEq2 by auto
  done

lemma equivStatementSkipRight:
  "equivStatement (S || skip) S"
  unfolding equivStatement_def
  apply auto subgoal for s
    apply (rule ext) using unaffectedVars by auto
  done

lemma equivStatementParallel:
  "equivStatement S1 S1' \<Longrightarrow> equivStatement S2 S2' \<Longrightarrow> equivStatement (S1 || S2) (S1' || S2')"
  by (auto simp add: equivStatement_def)

lemma equivStatementIteStm:
  "equivForm b b' \<Longrightarrow>
   equivStatement S1 S1' \<Longrightarrow> equivStatement S2 S2' \<Longrightarrow> equivStatement (iteStm b S1 S2) (iteStm b' S1' S2')"
  by (auto simp add: equivForm_def equivStatement_def)

lemma equivStatementForall:
  assumes "\<forall>i. i \<le> N \<longrightarrow> equivStatement (f i) (g i)"
  shows "equivStatement (forallStm f N) (forallStm g N)"
proof -
  have a: "largestInd v N f = None \<longleftrightarrow> largestInd v N g = None" for v
    unfolding largestIndNone
    using assms unfolding equivStatement_def by auto
  have b: "largestInd v N f = Some i \<longleftrightarrow> largestInd v N g = Some i" for v i
    unfolding largestIndSome
    using assms unfolding equivStatement_def by auto
  have c: "(case largestInd v N f of None \<Rightarrow> s v | Some i \<Rightarrow> trans1 (f i) s v) =
           (case largestInd v N g of None \<Rightarrow> s v | Some i \<Rightarrow> trans1 (g i) s v)" for s v
  proof (cases "largestInd v N f")
    case None
    have "largestInd v N g = None"
      using None a by auto
    then show ?thesis
      using assms unfolding equivStatement_def None by auto
  next
    case (Some i)
    have "largestInd v N g = Some i"
      using Some b by auto
    then show ?thesis
      using assms unfolding equivStatement_def Some apply auto
      by (simp add: largestIndSome)
  qed
  have "trans1 (forallStm f N) s v = trans1 (forallStm g N) s v" for v s
    using a c by auto
  then show ?thesis
    apply (auto simp add: equivStatement_def varOfStmtEq)
    using assms equivStatement_def by auto
qed

lemma equivStatementForallExcl:
  assumes "\<forall>i. i \<le> N \<longrightarrow> equivStatement (f i) (g i)"
  shows "equivStatement (forallStmExcl f j N) (forallStmExcl g j N)"
proof -
  have a: "largestIndExcl v j N f = None \<longleftrightarrow> largestIndExcl v j N g = None" for v
    unfolding largestIndExclNone
    using assms unfolding equivStatement_def by auto
  have b: "largestIndExcl v j N f = Some i \<longleftrightarrow> largestIndExcl v j N g = Some i" for v i
    unfolding largestIndExclSome
    using assms unfolding equivStatement_def by auto
  have c: "(case largestIndExcl v j N f of None \<Rightarrow> s v | Some i \<Rightarrow> trans1 (f i) s v) =
           (case largestIndExcl v j N g of None \<Rightarrow> s v | Some i \<Rightarrow> trans1 (g i) s v)" for s v
  proof (cases "largestIndExcl v j N f")
    case None
    have "largestIndExcl v j N g = None"
      using None a by auto
    then show ?thesis
      using assms unfolding equivStatement_def None by auto
  next
    case (Some i)
    have "largestIndExcl v j N g = Some i"
      using Some b by auto
    then show ?thesis
      using assms unfolding equivStatement_def Some apply auto
      by (simp add: largestIndExclSome)
  qed
  have "trans1 (forallStmExcl f j N) s v = trans1 (forallStmExcl g j N) s v" for v s
    using a c by auto
  then show ?thesis
    apply (auto simp add: equivStatement_def varOfStmtEq2)
    using assms equivStatement_def by auto
qed

lemma equivStatementPermute:
  assumes "p permutes {x. x \<le> N}"
    and "mutualDiffVars ps"
  shows "equivStatement (forallStm ps N) (forallStm (\<lambda>i. ps (p i)) N)"
proof -
  have a: "bij p"
    using assms(1) permutes_bij by auto
  have b: "inv p i \<le> N" "x \<in> varOfStmt (ps (p (inv p i)))" if "i \<le> N" "x \<in> varOfStmt (ps i)" for x i
  proof -
    show 1: "inv p i \<le> N"
      using that(1) assms(1)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "p (inv p i) = i"
      by (rule permutes_inverses[OF assms(1)])
    show "x \<in> varOfStmt (ps (p (inv p i)))"
      using 1 2 that(2) by auto
  qed
  have c: "p i \<le> N" "x \<in> varOfStmt (ps (p i))" if "i \<le> N" "x \<in> varOfStmt (ps (p i))" for x i
  proof -
    show 1: "p i \<le> N"
      by (metis (full_types) assms(1) mem_Collect_eq permutes_def that(1))
    show "x \<in> varOfStmt (ps (p i))"
      using 1 that(2) by auto
  qed
  have bc: "varOfStmt (forallStm (\<lambda>i. ps (p i)) N) = varOfStmt (forallStm ps N)"
    apply (rule set_eqI)
    unfolding varOfStmtEq using b c by blast
  have d: "trans1 (forallStm ps N) s v = trans1 (forallStm (\<lambda>i. ps (p i)) N) s v" for s v
  proof -
    have d1: "mutualDiffVars (\<lambda>i. ps (p i))"
      using assms(2) unfolding mutualDiffVars_def
      using assms(1) by (metis permutes_def)
    have d2: "trans1 (ps (THE i. v \<in> varOfStmt (ps i))) s v = trans1 (ps (p (THE i. v \<in> varOfStmt (ps (p i))))) s v"
      if assmd2: "v \<in> varOfStmt (forallStm ps N)"
    proof -
      obtain i where d21: "i \<le> N" "v \<in> varOfStmt (ps i)"
        using assmd2 varOfStmtEq by blast
      have d22: "(THE i. v \<in> varOfStmt (ps i)) = i"
        apply (rule the_equality) apply (rule d21(2))
        using assms(2) unfolding mutualDiffVars_def using d21(2) by blast
      have d23: "p (inv p i) = i"
        apply (rule permutes_inverses(1))
        using assms(1) by auto
      have d24: "v \<in> varOfStmt (ps (p (inv p i)))"
        using d23 d21(2) by auto
      have d25: "(THE i. v \<in> varOfStmt (ps (p i))) = inv p i"
        apply (rule the_equality)
         apply (auto simp add: d23 d21(2))
        using d1[unfolded mutualDiffVars_def] d24 by auto
      show ?thesis
        unfolding d22 d25 d23 by auto
    qed
    show ?thesis
      unfolding trans1ForallAlt[OF assms(2)] trans1ForallAlt[OF d1] bc
      using d2 by auto
  qed
  show ?thesis
    unfolding equivStatement_def using bc d by auto
qed

lemma equivStatementPermuteExcl:
  assumes "p permutes {x. x \<le> N}"
    and "mutualDiffVars ps"
  shows "equivStatement (forallStmExcl ps (p j) N) (forallStmExcl (\<lambda>i. ps (p i)) j N)"
proof -
  have a: "bij p"
    using assms(1) permutes_bij by auto
  have b: "inv p i \<le> N" "inv p i \<noteq> j" "x \<in> varOfStmt (ps (p (inv p i)))"
    if "i \<le> N" "i \<noteq> p j" "x \<in> varOfStmt (ps i)" for x i
  proof -
    show 1: "inv p i \<le> N"
      using that(1) assms(1)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "p (inv p i) = i"
      by (rule permutes_inverses[OF assms(1)])
    show "inv p i \<noteq> j"
      using "2" that(2) by auto
    show "x \<in> varOfStmt (ps (p (inv p i)))"
      using 1 2 that(3) by auto
  qed
  have c: "p i \<le> N" "p i \<noteq> p j" "x \<in> varOfStmt (ps (p i))" if "i \<le> N" "i \<noteq> j" "x \<in> varOfStmt (ps (p i))" for x i
  proof -
    show 1: "p i \<le> N"
      by (metis (full_types) assms(1) mem_Collect_eq permutes_def that(1))
    show "p i \<noteq> p j"
      by (metis a bij_pointE that(2))
    show "x \<in> varOfStmt (ps (p i))"
      using 1 that(3) by auto
  qed
  have bc: "varOfStmt (forallStmExcl (\<lambda>i. ps (p i)) j N) = varOfStmt (forallStmExcl ps (p j) N)"
    apply (rule set_eqI)
    unfolding varOfStmtEq2 using b c by meson
  have d: "trans1 (forallStmExcl ps (p j) N) s v = trans1 (forallStmExcl (\<lambda>i. ps (p i)) j N) s v" for s v
  proof -
    have d1: "mutualDiffVars (\<lambda>i. ps (p i))"
      using assms(2) unfolding mutualDiffVars_def
      using assms(1) by (metis permutes_def)
    have d2: "trans1 (ps (THE i. i \<noteq> p j \<and> v \<in> varOfStmt (ps i))) s v = trans1 (ps (p (THE i. i \<noteq> j \<and> v \<in> varOfStmt (ps (p i))))) s v"
      if assmd2: "v \<in> varOfStmt (forallStmExcl ps (p j) N)"
    proof -
      obtain i where d21: "i \<le> N" "i \<noteq> p j" "v \<in> varOfStmt (ps i)"
        using assmd2 varOfStmtEq2 by blast
      have d22: "(THE i. i \<noteq> p j \<and> v \<in> varOfStmt (ps i)) = i"
        apply (rule the_equality) apply (simp add: d21(2,3))
        using assms(2) unfolding mutualDiffVars_def using d21(3) by blast
      have d23: "p (inv p i) = i"
        apply (rule permutes_inverses(1))
        using assms(1) by auto
      have d24: "v \<in> varOfStmt (ps (p (inv p i)))"
        using d23 d21(3) by auto
      have d24': "p (inv p i) = i"
        by (simp add: d23)
      have d25: "(THE i. i \<noteq> j \<and> v \<in> varOfStmt (ps (p i))) = inv p i"
        apply (rule the_equality)
         apply (auto simp add: d23 d21(3))
        using d1[unfolded mutualDiffVars_def] d24 d24'
        using d21(2) apply auto[1]
        by (metis \<open>\<forall>i j. i \<noteq> j \<longrightarrow> varOfStmt (ps (p i)) \<inter> varOfStmt (ps (p j)) = {}\<close> d21(3) d24' disjoint_iff)
      show ?thesis
        unfolding d22 d25 d23 by auto
    qed
    show ?thesis
      unfolding trans1ForallExclAlt[OF assms(2)] trans1ForallExclAlt[OF d1] bc
      using d2 by auto
  qed
  show ?thesis
    unfolding equivStatement_def using bc d by auto
qed

definition symParamStatement :: "nat \<Rightarrow> (nat \<Rightarrow> statement) \<Rightarrow> bool" where
  "symParamStatement N ps =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivStatement (applySym2Statement p (ps i)) (ps (p i)))"

lemma symParamStatementParallel:
  assumes "symParamStatement N a1"
    and "symParamStatement N a2"
  shows "symParamStatement N (\<lambda>i. parallel (a1 i) (a2 i))"
  using assms unfolding symParamStatement_def equivStatement_def by auto

lemma symParamStatementIte:
  assumes "symParamForm N b"
    and "symParamStatement N a1"
    and "symParamStatement N a2"
  shows "symParamStatement N (\<lambda>i. iteStm (b i) (a1 i) (a2 i))"
  using assms unfolding symParamStatement_def symParamForm_def
  by (auto intro: equivStatementIteStm)

definition symParamStatement2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> statement) \<Rightarrow> bool" where
  "symParamStatement2 N ps =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow>
             equivStatement (applySym2Statement p (ps i j)) (ps (p i) (p j)))"

lemma symParamStatementForall:
  assumes "symParamStatement2 N ps"
    and "\<And>i. mutualDiffVars (ps i)"
  shows "symParamStatement N (\<lambda>i. forallStm (\<lambda>j. ps i j) N)"
proof -
  have a: "equivStatement (forallStm (\<lambda>j. applySym2Statement p (ps i j)) N)
                          (forallStm (\<lambda>j. ps (p i) (p j)) N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementForall)
    using assms unfolding symParamStatement2_def by (simp add: that)
  have b: "equivStatement (forallStm (\<lambda>j. ps (p i) (p j)) N)
                          (forallStm (\<lambda>j. ps (p i) j) N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementSym)
    apply (rule equivStatementPermute)
    using that assms(2) by auto
  show ?thesis
    unfolding symParamStatement_def applySym2Statement.simps
    using a b equivStatementTrans by blast
qed

lemma symParamStatementForallExcl:
  assumes "symParamStatement2 N ps"
    and "\<And>i. mutualDiffVars (ps i)"
  shows "symParamStatement N (\<lambda>i. forallStmExcl (\<lambda>j. ps i j) i N)"
proof -
  have a: "equivStatement (forallStmExcl (\<lambda>j. applySym2Statement p (ps i j)) i N)
                          (forallStmExcl (\<lambda>j. ps (p i) (p j)) i N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementForallExcl)
    using assms unfolding symParamStatement2_def by (simp add: that)
  have b: "equivStatement (forallStmExcl (\<lambda>j. ps (p i) (p j)) i N)
                          (forallStmExcl (\<lambda>j. ps (p i) j) (p i) N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementSym)
    apply (rule equivStatementPermuteExcl)
    using that assms(2) by auto
  show ?thesis
    unfolding symParamStatement_def applySym2Statement.simps
    using a b equivStatementTrans by blast
qed


definition DsymParamStatement :: "nat \<Rightarrow> (nat \<Rightarrow> statement) \<Rightarrow> bool" where
  "DsymParamStatement N ps =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivStatement (applyDSym2Statement p (ps i)) (ps (p i)))"

lemma DsymParamStatementParallel:
  assumes "DsymParamStatement N a1"
    and "DsymParamStatement N a2"
  shows "DsymParamStatement N (\<lambda>i. parallel (a1 i) (a2 i))"
  using assms unfolding DsymParamStatement_def equivStatement_def by auto

lemma DsymParamStatementIte:
  assumes "DsymParamForm N b"
    and "DsymParamStatement N a1"
    and "DsymParamStatement N a2"
  shows "DsymParamStatement N (\<lambda>i. iteStm (b i) (a1 i) (a2 i))"
  using assms unfolding DsymParamStatement_def DsymParamForm_def
  by (auto intro: equivStatementIteStm)

definition DsymParamStatement2 :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> statement) \<Rightarrow> bool" where
  "DsymParamStatement2 N ps =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow>
             equivStatement (applyDSym2Statement p (ps i j)) (ps (p i) (p j)))"

lemma DsymParamStatementForall:
  assumes "DsymParamStatement2 N ps"
    and "\<And>i. mutualDiffVars (ps i)"
  shows "DsymParamStatement N (\<lambda>i. forallStm (\<lambda>j. ps i j) N)"
proof -
  have a: "equivStatement (forallStm (\<lambda>j. applyDSym2Statement p (ps i j)) N)
                          (forallStm (\<lambda>j. ps (p i) (p j)) N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementForall)
    using assms unfolding DsymParamStatement2_def by (simp add: that)
  have b: "equivStatement (forallStm (\<lambda>j. ps (p i) (p j)) N)
                          (forallStm (\<lambda>j. ps (p i) j) N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementSym)
    apply (rule equivStatementPermute)
    using that assms(2) by auto
  show ?thesis
    unfolding DsymParamStatement_def applyDSym2Statement.simps
    using a b equivStatementTrans by blast
qed

lemma DsymParamStatementForallExcl:
  assumes "DsymParamStatement2 N ps"
    and "\<And>i. mutualDiffVars (ps i)"
  shows "DsymParamStatement N (\<lambda>i. forallStmExcl (\<lambda>j. ps i j) i N)"
proof -
  have a: "equivStatement (forallStmExcl (\<lambda>j. applyDSym2Statement p (ps i j)) i N)
                          (forallStmExcl (\<lambda>j. ps (p i) (p j)) i N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementForallExcl)
    using assms unfolding DsymParamStatement2_def by (simp add: that)
  have b: "equivStatement (forallStmExcl (\<lambda>j. ps (p i) (p j)) i N)
                          (forallStmExcl (\<lambda>j. ps (p i) j) (p i) N)"
    if "p permutes {x. x \<le> N}" "i \<le> N" for p i
    apply (rule equivStatementSym)
    apply (rule equivStatementPermuteExcl)
    using that assms(2) by auto
  show ?thesis
    unfolding DsymParamStatement_def applyDSym2Statement.simps
    using a b equivStatementTrans by blast
qed

fun equivRule :: "rule \<Rightarrow> rule \<Rightarrow> bool" (infix "=\<^sub>r" 30) where 
  "equivRule (guard g1 a1) (guard g2 a2) \<longleftrightarrow> equivForm g1 g2 \<and> equivStatement a1 a2"

lemma equivRuleRefl:
  "equivRule r r"
  apply (cases r) by auto

lemma equivRuleSym:
  "equivRule r1 r2 \<longleftrightarrow> equivRule r2 r1"
  apply (cases r1, cases r2) using equivFormSym equivStatementSym by auto

lemma equivRuleTrans:
  "equivRule r1 r2 \<Longrightarrow> equivRule r2 r3 \<Longrightarrow> equivRule r1 r3"
  apply (cases r1, cases r2, cases r3)
  using equivFormTrans equivStatementTrans by auto


lemma equivRuleImplySamePostTrans:
  assumes a:"equivRule r1 r2"
  shows "trans1 (act r1) s =trans1 (act r2) s"
  using assms equivRule.elims(2) equivStatement_def by fastforce

lemma equivRuleImplySameTrig:
  assumes a:"equivRule r1 r2"
  shows " formEval (pre r1) s =formEval (pre r2) s"
  by (metis assms equivForm_def equivRule.elims(2) pre.simps) 

lemma ruleSetMonoImplyreachStateMono:
  assumes   b:"reachableUpTo fs rs1 i s"
shows "(\<forall>r1. r1 \<in> rs1 \<longrightarrow> (\<exists>r2. r2 \<in>rs2 \<and>equivRule r1 r2)) \<longrightarrow>
   reachableUpTo fs rs2 i s"       
using b proof (induct)
  case (reachableSet0 fs s rs)
  then show ?case
    by (simp add: reachableUpTo.reachableSet0)  
next
  case (reachableSetNext fs rs n s g a) 
  then show ?case
    by (smt (verit, del_insts) act.simps equivRule.elims(2) equivRuleImplySamePostTrans equivRuleImplySameTrig pre.simps reachableUpTo.reachableSetNext)  
qed 
  
      
definition symParamRule :: "nat \<Rightarrow> (nat \<Rightarrow> rule) \<Rightarrow> bool" where
  "symParamRule N r =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivRule (applySym2Rule p (r i)) (r (p i)))"

definition symParamRule2':: "nat\<Rightarrow>(nat \<Rightarrow>nat\<Rightarrow>rule) \<Rightarrow> bool" where
  "symParamRule2' N r =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N\<longrightarrow>
             equivRule (applySym2Rule p (r i j)) (r (p i) (p j)))"


definition DsymParamRule :: "nat \<Rightarrow> (nat \<Rightarrow> rule) \<Rightarrow> bool" where
  "DsymParamRule N r =
    (\<forall>p i. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> equivRule (applyDSym2Rule p (r i)) (r (p i)))"
 
definition DsymParamRule2':: "nat\<Rightarrow>(nat \<Rightarrow>nat\<Rightarrow>rule) \<Rightarrow> bool" where
  "DsymParamRule2' N r =
    (\<forall>p i j. p permutes {x. x \<le> N} \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N\<longrightarrow>
             equivRule (applyDSym2Rule p (r i j)) (r (p i) (p j)))"


lemma symParamRuleI:
  "symParamForm N f \<Longrightarrow> symParamStatement N ps \<Longrightarrow> symParamRule N (\<lambda>i. guard (f i) (ps i))"
  unfolding symParamRule_def symParamForm_def symParamStatement_def by auto

lemma symParamRuleI2:
  "symParamForm2 N f \<Longrightarrow> symParamStatement2 N ps \<Longrightarrow> symParamRule2' N (\<lambda>i j. guard (f i j) (ps i j))"
  unfolding symParamRule2'_def symParamForm2_def symParamStatement2_def by auto

     
lemma DsymParamRuleI:
  "DsymParamForm N f \<Longrightarrow> DsymParamStatement N ps \<Longrightarrow> DsymParamRule N (\<lambda>i. guard (f i) (ps i))"
  unfolding DsymParamRule_def DsymParamForm_def DsymParamStatement_def by auto

lemma DsymParamRuleI2:
  "DsymParamForm2 N f \<Longrightarrow> DsymParamStatement2 N ps \<Longrightarrow> DsymParamRule2' N (\<lambda>i j. guard (f i j) (ps i j))"
  unfolding DsymParamRule2'_def DsymParamForm2_def DsymParamStatement2_def by auto


text \<open>A set of rules is symmetric with respect to semantic equivalence\<close>
definition symProtRules' :: "nat \<Rightarrow> rule set \<Rightarrow> bool" where [simp]:
  "symProtRules' N rs = (\<forall>p r. p permutes {x. x \<le> N} \<and> r \<in> rs \<longrightarrow>
     (\<exists>r'. r' \<in> rs \<and> equivRule (applySym2Rule p r) r'))"

text \<open>A set of formulas is symmetric with respect to semantic equivalence\<close>
definition symPredSet' :: "nat \<Rightarrow> formula set \<Rightarrow> bool" where [simp]:
  "symPredSet' N fs = (\<forall>p f. p permutes {x. x \<le> N} \<and> f \<in> fs \<longrightarrow>
     (\<exists>f'. f' \<in> fs \<and> equivForm (applySym2Form p f) f'))"


text \<open>A set of rules is Dsymmetric with respect to semantic equivalence\<close>
definition DsymProtRules' :: "nat \<Rightarrow> rule set \<Rightarrow> bool" where [simp]:
  "DsymProtRules' N rs = (\<forall>p r. p permutes {x. x \<le> N} \<and> r \<in> rs \<longrightarrow>
     (\<exists>r'. r' \<in> rs \<and> equivRule (applyDSym2Rule p r) r'))"

text \<open>A set of formulas is Dsymmetric with respect to semantic equivalence\<close>
definition DsymPredSet' :: "nat \<Rightarrow> formula set \<Rightarrow> bool" where [simp]:
  "DsymPredSet' N fs = (\<forall>p f. p permutes {x. x \<le> N} \<and> f \<in> fs \<longrightarrow>
     (\<exists>f'. f' \<in> fs \<and> equivForm (applyDSym2Form p f) f'))"


lemma symPredSetForall:
  assumes "symParamForm N f"
  shows "symPredSet' N {(\<forall>\<^sub>fi. f i) N}"
proof -
  have a: "formEval (f i) s"
    if "p permutes {x. x \<le> N}" "\<forall>i\<le>N. formEval (applySym2Form p (f i)) s" "i \<le> N" for p i s
  proof -
    have 1: "inv p i \<le> N"
      using that(1,3)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "formEval (applySym2Form p (f (inv p i))) s"
      using that(2) 1 by auto
    have 3: "equivForm (applySym2Form p (f (inv p i))) (f i)"
      using that assms unfolding symParamForm_def
      using 1 permutes_inverses(1) by fastforce
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  have b: "formEval (applySym2Form p (f i)) s"
    if "p permutes {x. x \<le> N}" "\<forall>i\<le>N. formEval (f i) s" "i \<le> N" for p i s
  proof -
    have 1: "p i \<le> N"
      using bij_betwE permutes_imp_bij that(1,3) by fastforce
    have 2: "formEval (f (p i)) s"
      using that(2) 1 by auto
    have 3: "equivForm (applySym2Form p (f i)) (f (p i))"
      using assms that unfolding symParamForm_def by auto
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  show ?thesis
    unfolding symPredSet'_def equivForm_def
    using a b by auto
qed

lemma trans1Symmetric':
  assumes "p permutes {x. x \<le> N}"
    and "equivStatement S' (applySym2Statement p S)"
  shows "applySym2State p (trans1 S s0) = trans1 S' (applySym2State p s0)"
  using assms equivStatement_def trans1Symmetric by auto

lemma stFormSymCorrespondence1':
  assumes "p permutes {x. x \<le> N}"
    and "equivForm (applySym2Form p f) f'"
  shows "formEval f' (applySym2State p s) = formEval f s"
  using assms equivForm_def stFormSymCorrespondence by blast
   
lemma reachSymLemma':
  assumes "symPredSet' N fs"
    and "symProtRules' N rs"
    and "p permutes {x. x \<le> N}"
  shows "\<forall>s. reachableUpTo fs rs i s \<longrightarrow> reachableUpTo fs rs i (applySym2State p s)"
proof (induction i)
  case 0
  show ?case
    apply clarify subgoal for s
      apply (auto elim!: reachableUpTo0)
      apply (rule reachableUpTo.intros(1))
      apply (auto simp add: stFormSymCorrespondence2(2)[OF assms(3)])
       using assms(1,3) permutes_inv unfolding symPredSet'_def equivForm_def  by blast
    done
next
  case (Suc i)
  fix i
  assume a0: "\<forall>s. reachableUpTo fs rs i s \<longrightarrow> reachableUpTo fs rs i (applySym2State p s) "
  show "\<forall>s. reachableUpTo fs rs (Suc i) s \<longrightarrow> reachableUpTo fs rs (Suc i) (applySym2State p s)"
  proof (rule allI, rule)
    fix s
    assume a1: "reachableUpTo fs rs (Suc i) s"
    have "\<exists>s0 g a. reachableUpTo fs rs i s0 \<and> formEval g s0 \<and>s=trans1 a s0 \<and> guard g a \<in> rs"
      by (meson a1 reachableUpToSuc)
    then obtain s0 g a where a2: "reachableUpTo fs rs i s0 \<and> formEval g s0 \<and>s=trans1 a s0 \<and> guard g a \<in> rs"
      by blast
    have "\<exists>r'. equivRule (guard (applySym2Form p g) (applySym2Statement p a)) r'\<and> r' \<in> rs"
      using a2 assms(2) assms(3) by fastforce 
    then obtain g' a' where a3:
      "equivRule (guard (applySym2Form p g) (applySym2Statement p a)) (guard g' a') \<and>
       guard g' a' \<in> rs"
      by (metis equivRule.elims(2))
    then have a31: "equivForm  (applySym2Form p g) g' \<and> equivStatement (applySym2Statement p a) a'"
      by auto
    have a4: "reachableUpTo fs rs i (applySym2State p s0)"
      using a0 a2 by blast  
    have "formEval g' (applySym2State p s0)"
      using a2 a3 assms(3) stFormSymCorrespondence1' by auto
    then have a5: "reachableUpTo fs rs (Suc i) (trans1 a' (applySym2State p s0))"
      using a3 a4 reachableSetNext by blast
    show "reachableUpTo fs rs (Suc i) (applySym2State p s)"
      using a2 a31 a5 assms(3) equivStatement_def trans1Symmetric by auto  
  qed
qed

lemma SymLemma':
  assumes "symPredSet' N fs"
    and "symProtRules' N rs"
    and "\<forall>s i. reachableUpTo fs rs i s \<longrightarrow> formEval f s"
    and "p permutes {x. x \<le> N}"
    and "reachableUpTo fs rs i s"
  shows "formEval (applySym2Form p f) s"
proof -
  have "bij p"
    using assms(4) permutes_bij by blast
  have 0: "(inv p) permutes {x. x \<le> N}"
    using assms(4)
    by (simp add: permutes_inv)
  have 1: "reachableUpTo fs rs i (applySym2State (inv p) s)"
    using reachSymLemma'[OF assms(1,2) 0] assms(5) by auto 
  have 2: "formEval (applySym2Form p f) (applySym2State p (applySym2State (inv p) s))"
    unfolding stFormSymCorrespondence1[OF assms(4)]
    using 1 assms(3) by auto
  then show ?thesis
    unfolding applySym2StateInv[OF \<open>bij p\<close>] by auto
qed


lemma DsymPredSetForall:
  assumes "DsymParamForm N f"
  shows "DsymPredSet' N {(\<forall>\<^sub>fi. f i) N}"
proof -
  have a: "formEval (f i) s"
    if "p permutes {x. x \<le> N}" "\<forall>i\<le>N. formEval (applyDSym2Form p (f i)) s" "i \<le> N" for p i s
  proof -
    have 1: "inv p i \<le> N"
      using that(1,3)
      by (metis (full_types) mem_Collect_eq permutes_def permutes_inverses(1))
    have 2: "formEval (applyDSym2Form p (f (inv p i))) s"
      using that(2) 1 by auto
    have 3: "equivForm (applyDSym2Form p (f (inv p i))) (f i)"
      using that assms unfolding DsymParamForm_def
      using 1 permutes_inverses(1) by fastforce
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  have b: "formEval (applyDSym2Form p (f i)) s"
    if "p permutes {x. x \<le> N}" "\<forall>i\<le>N. formEval (f i) s" "i \<le> N" for p i s
  proof -
    have 1: "p i \<le> N"
      using bij_betwE permutes_imp_bij that(1,3) by fastforce
    have 2: "formEval (f (p i)) s"
      using that(2) 1 by auto
    have 3: "equivForm (applyDSym2Form p (f i)) (f (p i))"
      using assms that unfolding DsymParamForm_def by auto
    show ?thesis
      using 2 3 unfolding equivForm_def by auto
  qed
  show ?thesis
    unfolding DsymPredSet'_def equivForm_def
    using a b by auto
qed

lemma trans1DSymmetric':
  assumes "p permutes {x. x \<le> N}"
    and "equivStatement S' (applyDSym2Statement p S)"
  shows "applyDSym2State p (trans1 S s0) = trans1 S' (applyDSym2State p s0)"
  using assms equivStatement_def trans1DSymmetric by auto

lemma stFormDSymCorrespondence1':
  assumes "p permutes {x. x \<le> N}"
    and "equivForm (applyDSym2Form p f) f'"
  shows "formEval f' (applyDSym2State p s) = formEval f s"
  using assms equivForm_def stFormDSymCorrespondence by blast
   
lemma reachDSymLemma':
  assumes "DsymPredSet' N fs"
    and "DsymProtRules' N rs"
    and "p permutes {x. x \<le> N}"
  shows "\<forall>s. reachableUpTo fs rs i s \<longrightarrow> reachableUpTo fs rs i (applyDSym2State p s)"
proof (induction i)
  case 0
  show ?case
    apply clarify subgoal for s
      apply (auto elim!: reachableUpTo0)
      apply (rule reachableUpTo.intros(1))
      apply (auto simp add: stFormDSymCorrespondence2(2)[OF assms(3)])
       using assms(1,3) permutes_inv unfolding DsymPredSet'_def equivForm_def  by blast
    done
next
  case (Suc i)
  fix i
  assume a0: "\<forall>s. reachableUpTo fs rs i s \<longrightarrow> reachableUpTo fs rs i (applyDSym2State p s) "
  show "\<forall>s. reachableUpTo fs rs (Suc i) s \<longrightarrow> reachableUpTo fs rs (Suc i) (applyDSym2State p s)"
  proof (rule allI, rule)
    fix s
    assume a1: "reachableUpTo fs rs (Suc i) s"
    have "\<exists>s0 g a. reachableUpTo fs rs i s0 \<and> formEval g s0 \<and>s=trans1 a s0 \<and> guard g a \<in> rs"
      by (meson a1 reachableUpToSuc)
    then obtain s0 g a where a2: "reachableUpTo fs rs i s0 \<and> formEval g s0 \<and>s=trans1 a s0 \<and> guard g a \<in> rs"
      by blast
    have "\<exists>r'. equivRule (guard (applyDSym2Form p g) (applyDSym2Statement p a)) r'\<and> r' \<in> rs"
      using a2 assms(2) assms(3) by fastforce 
    then obtain g' a' where a3:
      "equivRule (guard (applyDSym2Form p g) (applyDSym2Statement p a)) (guard g' a') \<and>
       guard g' a' \<in> rs"
      by (metis equivRule.elims(2))
    then have a31: "equivForm  (applyDSym2Form p g) g' \<and> equivStatement (applyDSym2Statement p a) a'"
      by auto
    have a4: "reachableUpTo fs rs i (applyDSym2State p s0)"
      using a0 a2 by blast  
    have "formEval g' (applyDSym2State p s0)"
      using a2 a3 assms(3) stFormDSymCorrespondence1' by auto
    then have a5: "reachableUpTo fs rs (Suc i) (trans1 a' (applyDSym2State p s0))"
      using a3 a4 reachableSetNext by blast
    show "reachableUpTo fs rs (Suc i) (applyDSym2State p s)"
      using a2 a31 a5 assms(3) equivStatement_def trans1DSymmetric by auto  
  qed
qed

lemma DSymLemma':
  assumes "DsymPredSet' N fs"
    and "DsymProtRules' N rs"
    and "\<forall>s i. reachableUpTo fs rs i s \<longrightarrow> formEval f s"
    and "p permutes {x. x \<le> N}"
    and "reachableUpTo fs rs i s"
  shows "formEval (applyDSym2Form p f) s"
proof -
  have "bij p"
    using assms(4) permutes_bij by blast
  have 0: "(inv p) permutes {x. x \<le> N}"
    using assms(4)
    by (simp add: permutes_inv)
  have 1: "reachableUpTo fs rs i (applyDSym2State (inv p) s)"
    using reachDSymLemma'[OF assms(1,2) 0] assms(5) by auto 
  have 2: "formEval (applyDSym2Form p f) (applyDSym2State p (applyDSym2State (inv p) s))"
    unfolding stFormDSymCorrespondence1[OF assms(4)]
    using 1 assms(3) by auto
  then show ?thesis
    unfolding applyDSym2StateInv[OF \<open>bij p\<close>] by auto
qed 

(*lemma DsymParamRuleI2:
  "DsymParamForm2 N f \<Longrightarrow> DsymParamStatement2 N ps \<Longrightarrow> DsymParamRule2' N (\<lambda>i j. guard (f i j) (ps i j))"
  unfolding DsymParamRule2'_def DsymParamForm2_def DsymParamStatement2_def apply auto done*)


subsection \<open>Strengthening\<close>

text \<open>Strengthen a guard g by auxiliary invariant\<close>

fun strengthenForm :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "strengthenForm invf g = andForm g invf"

fun strengthenRule :: "formula \<Rightarrow> rule \<Rightarrow> rule" where
  "strengthenRule invf (guard g a) = guard (strengthenForm invf g) a"

lemma symParamStrengthenRule:
  assumes "symParamRule N r"
    and "symParamForm N f"
  shows "symParamRule N (\<lambda>i. strengthenRule (f i) (r i))"
proof -
  have a: "equivForm (applySym2Form p (strengthenForm (f i) a1)) (strengthenForm (f (p i)) a2) \<and>
           equivStatement (applySym2Statement p g1) g2"
    if "p permutes {x. x \<le> N}" "i \<le> N" "r i = guard a1 g1" "r (p i) = guard a2 g2" for p i a1 a2 g1 g2
  proof -
    have 1: "equivRule (applySym2Rule p (r i)) (r (p i))"
      using assms(1) unfolding symParamRule_def
      using that(1,2) by auto
    have 2: "equivForm (applySym2Form p a1) a2"
      using 1 unfolding that(3,4) by auto
    have 3: "equivForm (applySym2Form p (f i)) (f (p i))"
      using assms(2) unfolding symParamForm_def using that(1,2) by auto
    have 4: "equivForm (applySym2Form p (strengthenForm (f i) a1)) (strengthenForm (f (p i)) a2)"
      using 2 3 unfolding equivForm_def by auto
    have 5: "equivStatement (applySym2Statement p g1) g2"
      using 1 unfolding that(3,4) by auto
    show ?thesis
      unfolding that(3,4) using 4 5 by auto
  qed
  show ?thesis
    unfolding symParamRule_def
    apply auto subgoal for p i
      apply (cases "r i") subgoal for a1 g1
        apply (cases "r (p i)") subgoal for a2 g2
          using a by auto
        done
      done
    done
qed

primrec strengtheAddnForms :: "formula \<Rightarrow> formula list\<Rightarrow> formula" where
  "strengtheAddnForms g [] = chaos" |
  "strengtheAddnForms g (f#fs) = andForm f (strengtheAddnForms g fs)"

definition strengthenFormList :: "formula list \<Rightarrow> formula  \<Rightarrow> formula" where [simp]:
  "strengthenFormList invfs g \<equiv> andForm g (strengtheAddnForms g invfs)"

fun strengthenRuleByFrmL :: "formula list \<Rightarrow> rule \<Rightarrow> rule" where
  "strengthenRuleByFrmL invf (guard g a) = 
  guard (andForm g (strengtheAddnForms g invf)) a"

lemma strengthenRuleByFrmL_Cons:
  "strengthenRuleByFrmL (inv1 # rest) (guard g a) =\<^sub>r
    strengthenRule inv1 (strengthenRuleByFrmL rest (guard g a))"
  apply (induction rest)
  by (auto simp add: equivForm_def)

subsection \<open>More refined strengthening\<close>

fun has_conj :: "formula \<Rightarrow> formula \<Rightarrow> bool" where
  "has_conj (f1 \<and>\<^sub>f f2) f = (if f1 = f then True else has_conj f2 f)"
| "has_conj g f = (g = f)"

fun has_all_conj :: "formula \<Rightarrow> formula \<Rightarrow> bool" where
  "has_all_conj g (f1 \<and>\<^sub>f f2) = (has_conj g f1 \<and> has_all_conj g f2)"
| "has_all_conj g f = has_conj g f"

fun removeImplies2 :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "removeImplies2 (f1 \<longrightarrow>\<^sub>f f2) g = (if has_all_conj g f1 then f2 else f1 \<longrightarrow>\<^sub>f f2)"
| "removeImplies2 f g = f"

fun rec_andForm :: "formula \<Rightarrow> formula \<Rightarrow> formula" where
  "rec_andForm (f1 \<and>\<^sub>f f2) g = (f1 \<and>\<^sub>f rec_andForm f2 g)"
| "rec_andForm f g = andForm f g"

definition strengthenForm2 :: "formula \<Rightarrow> formula \<Rightarrow> formula" where [simp]:
  "strengthenForm2 invf g = rec_andForm g (removeImplies2 invf g)"

fun strengthenRule2 :: "formula \<Rightarrow> rule \<Rightarrow> rule" where
  "strengthenRule2 invf (guard g a) = guard (strengthenForm2 invf g) a"

lemma has_conj_correct:
  "has_conj f1 f2 \<Longrightarrow> formEval f1 s \<Longrightarrow> formEval f2 s"
  apply (induction f1, auto) by metis

lemma has_conj_all_correct':
  "True \<and> (has_all_conj f1 f2 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 s)"
proof (induction rule: expType_formula.induct[of "\<lambda>_. True" "\<lambda>f. has_all_conj f1 f \<longrightarrow> formEval f1 s \<longrightarrow> formEval f s" _ f2])
  case (eqn x1 x2)
  then show ?case
    apply auto
    using evalEqn has_conj_correct by blast
next
  case (andForm x1 x2)
  then show ?case
    using has_conj_correct by auto
next
  case (neg x)
  then show ?case
    by (meson has_all_conj.simps has_conj_correct)
next
  case (orForm x1 x2)
  then show ?case
    by (meson has_all_conj.simps has_conj_correct)
next
  case (implyForm x1 x2)
  then show ?case
    by (meson has_all_conj.simps has_conj_correct)
next
  case (forallForm x1 x2)
  then show ?case
    by (meson has_all_conj.simps has_conj_correct)
next
  case (existForm x1 x2)
  then show ?case
    by (meson has_all_conj.simps has_conj_correct)
next
  case (forallFormExcl x1 x2 x3)
  then show ?case
    by (meson has_all_conj.simps has_conj_correct)
qed (auto)

lemma has_conj_all_correct:
  "has_all_conj f1 f2 \<Longrightarrow> formEval f1 s \<Longrightarrow> formEval f2 s"
  using has_conj_all_correct' by auto

lemma rec_andForm_correct:
  "formEval (rec_andForm f g) s \<longleftrightarrow> formEval (andForm f g) s"
  apply (induction f) by auto

lemma removeImplies2Equiv [simp]:
  "formEval g s \<Longrightarrow> formEval (removeImplies2 invf g) s \<longleftrightarrow> formEval invf s"
  apply (cases invf) apply auto
  using has_conj_all_correct by auto

lemma strengthenFormCorrect:
  "formEval (strengthenForm2 invf g) s \<longleftrightarrow> formEval (strengthenForm invf g) s"
  by (metis evalAnd rec_andForm_correct removeImplies2Equiv strengthenForm.elims strengthenForm2_def)

theorem strengthenRuleCorrect:
  "equivRule (strengthenRule2 invf r) (strengthenRule invf r)"
  apply (cases r) apply auto
  using equivForm_def rec_andForm_correct by auto

theorem strengthenRuleCong:
  "r =\<^sub>r r' \<Longrightarrow> strengthenRule invf r =\<^sub>r strengthenRule invf r'"
  apply (cases r, cases r') by (auto simp add: equivForm_def)

theorem strengthenRuleCorrect2:
  "r =\<^sub>r r' \<Longrightarrow> equivRule (strengthenRule2 invf r) (strengthenRule invf r')"
  by (meson equivRuleTrans strengthenRuleCong strengthenRuleCorrect)


text \<open>Equivalence between strengthenRule and strengthenRule2\<close>

fun strengthenRuleByFrmL2 :: "formula list \<Rightarrow> rule \<Rightarrow> rule" where
  "strengthenRuleByFrmL2 [] r = r"
| "strengthenRuleByFrmL2 (f # rest) r = strengthenRule2 f (strengthenRuleByFrmL2 rest r)"

lemma strengthenRuleByFrmL2Act:
  "act (strengthenRuleByFrmL2 invLs r) = act r"
proof (induction invLs arbitrary: r)
  case Nil
  then show ?case by auto
next
  case (Cons f invLs)
  show ?case
    apply auto
    by (metis Cons.IH act.simps pre.cases strengthenRule2.simps)
qed


lemma strengthenRuleByFrml2Equiv:
  "equivRule (strengthenRuleByFrmL2 invfs r) (strengthenRuleByFrmL invfs r)" (is "?P invf")  
proof (induction invfs arbitrary: r)
  case Nil
  then show ?case
    apply (cases r) by (auto simp add: equivForm_def)
next
  case (Cons a invfs)
  have a1: "strengthenRuleByFrmL (a # invfs) r =\<^sub>r
            strengthenRule a (strengthenRuleByFrmL invfs r)"
    apply (cases r)
    using strengthenRuleByFrmL_Cons by auto
  show ?case    
    apply auto
    using Cons.IH a1 equivRuleSym equivRuleTrans strengthenRuleCorrect2 by blast
qed


subsection \<open>Assume-guarantee property of strengthening\<close>

text \<open>This corresponds to Lemma 1 in the Handbook of Model Checking
  Inv - the set of possible strengthening
  rs  - set of rules before strengthening
  rs' - set of rules after strengthening
  f   - invariant to be checked
\<close>

lemma strengthenFormListSat:
  assumes  b:"formEval g s"
  shows "(\<forall>inv.   inv \<in>set invL \<longrightarrow>  formEval inv s) \<longrightarrow>
  formEval (strengthenFormList invL g) s" (is "?P invL")
proof(induct_tac invL)
  show "?P []"
    using b   by  simp
next
  fix a LS
  assume b1:"?P LS"
  show "?P (a#LS)"
  proof 
    assume c:"\<forall>inv. inv \<in> set (a # LS) \<longrightarrow> formEval inv s"
    have c0:"(\<forall>inv. inv \<in> set ( LS) \<longrightarrow> formEval inv s) \<and>formEval a s "
      by (simp add: c)
    have c1:"formEval (strengthenFormList LS g) s"
      using b1 c0 by fastforce  
    show "formEval (strengthenFormList (a # LS) g) s"
      using c0 c1 by auto 
  qed
qed

lemma strengthenFrmListProt1SimProt:
  assumes a1: "\<forall>r. r \<in> rs \<longrightarrow> ((\<exists>invL . invL \<in> S  \<and> strengthenRuleByFrmL invL r   \<in> rs') \<or> r \<in> rs')"
    and a2: "\<forall>i s invL f. reachableUpTo I rs' i s \<longrightarrow>invL \<in> S\<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s" 
  shows "\<forall>s. reachableUpTo I rs i s \<longrightarrow>
             (reachableUpTo I rs' i s \<and> (\<forall>invL f. invL \<in> S\<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s))" (is "?P i")
proof (induct_tac i)
  show "?P 0"
    by (meson a2 reachableSet0 reachableUpTo0)
next
  fix n
  assume b0: "?P n"
  show "?P (Suc n)"
  proof ((rule allI)+,(rule impI)+)
    fix s f
    assume b1: "reachableUpTo I rs (Suc n) s"
    have "\<exists>s0 g a. reachableUpTo I rs n s0 \<and> formEval g s0 \<and> trans1 a s0 = s \<and> guard g a \<in> rs"
      by (metis b1 reachableUpToSuc)
    then obtain s0 g a where c1:
      "reachableUpTo I rs n s0 \<and> formEval g s0 \<and> trans1 a s0 = s \<and> guard g a \<in> rs"
      by blast
    let ?r="guard g a"
    have c2:" ((\<exists>invL . invL \<in> S \<and> strengthenRuleByFrmL invL  ?r \<in> rs') | ?r \<in> rs')" 
      using a1 c1 by blast
    from b0 c1 c2 have c3:"\<forall>invL f. invL \<in> S\<longrightarrow> f \<in> set invL -->  formEval f s0"
      by auto                                  
    from c2 obtain invL   where c2:"invL \<in> S \<and>    strengthenRuleByFrmL invL ?r \<in> rs' | ?r\<in> rs'"
      by blast
    moreover
    {
      assume c2: "invL \<in> S \<and>    strengthenRuleByFrmL invL ?r \<in> rs'"
      have c4: "formEval (pre ( strengthenRuleByFrmL invL ?r)) s0"
        using c1 c2 c3 strengthenFormListSat by auto 
      have c5: "trans1 (act (strengthenRule f ?r)) s0 = trans1 (act ?r) s0"
        by simp
      have c7: "reachableUpTo I rs' n s0"
        using b0 c1 by blast
      have "reachableUpTo I rs' (Suc n) s \<and> (\<forall>invL f. invL \<in> S\<longrightarrow> f \<in> set invL\<longrightarrow> formEval f s)"
        by (metis a2 c1 c2 c4 c7 pre.simps reachableUpTo.simps strengthenRuleByFrmL.simps) 
    }
    moreover
    {
      assume c2:"?r \<in> rs'"
      have "reachableUpTo I rs' (Suc n) s \<and>  (\<forall>invL f. invL \<in> S\<longrightarrow> f \<in> set invL\<longrightarrow> formEval f s)"
      using a2 b0 c1 c2 reachableSetNext by blast
    }
    ultimately show "reachableUpTo I rs' (Suc n) s \<and>  (\<forall>invL f. invL \<in> S\<longrightarrow> f \<in> set invL\<longrightarrow> formEval f s)"
      by blast
  qed
qed 

lemma strengthenFrmLstProt2SimProt1:
  assumes a1: "\<forall>r1. r1 \<in> rs1 \<longrightarrow>
    ((\<exists>r invL. r\<in>rs\<and> invL \<in> S  \<and> r1=strengthenRuleByFrmL invL r \<and> strengthenRuleByFrmL2 invL r \<in> rs2)
     \<or> r1 \<in> rs2)"
    and a2: "\<forall>i s invL f. reachableUpTo I rs2 i s \<longrightarrow> invL \<in> S\<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s" 
  shows "\<forall>s. reachableUpTo I rs1 i s \<longrightarrow>
          (reachableUpTo I rs2 i s \<and> (\<forall>invL f. invL \<in> S\<longrightarrow> f \<in> set invL  \<longrightarrow> formEval f s))" (is "?P i")
proof (induct_tac i)  
  show "?P 0"
    by (meson a2 reachableSet0 reachableUpTo0) 
next
  fix n
  assume b0:"?P n"
  show "?P (Suc n)"
  proof((rule allI)+,(rule impI)+)
    fix s
    assume b1: "reachableUpTo I rs1 (Suc n) s"  
    have c1:"\<exists>s0 g a. guard g a \<in> rs1 \<and> reachableUpTo I rs1 n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by (metis b1 reachableUpToSuc) 
    from c1 obtain s0 g a where c1:
      "guard g a \<in> rs1 \<and> reachableUpTo I rs1 n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by blast
    have c2: "(\<exists>r invL.  r \<in> rs \<and> invL\<in>S \<and>guard g a = strengthenRuleByFrmL invL r 
     \<and> strengthenRuleByFrmL2 invL  r \<in> rs2) \<or>
              (guard g a \<in> rs2)"
      using a1 c1 by blast
    moreover
    {
      assume c2:"\<exists>r invL. r \<in> rs \<and> invL \<in> S \<and> guard g a = strengthenRuleByFrmL invL r \<and>
                          strengthenRuleByFrmL2 invL r \<in> rs2"
      from c2 obtain r invL where c2:
        "invL \<in> S \<and> r \<in> rs \<and> guard g a = strengthenRuleByFrmL invL r \<and> strengthenRuleByFrmL2 invL r \<in> rs2"
        by blast
      from b0 c1 c2 have c3: "\<forall>invL f. invL \<in> S\<longrightarrow> f \<in> set invL  \<longrightarrow> formEval f s0"
        by auto
      have c4: "formEval (pre (strengthenRuleByFrmL2 invL r)) s0"
        by (metis c1 c2 equivForm_def equivRule.elims(2) pre.simps strengthenRuleByFrml2Equiv)
      have c5: "trans1 (act (strengthenRuleByFrmL2 invL r)) s0 = trans1 (act r) s0"
        by (simp add: strengthenRuleByFrmL2Act)
      have c6: "trans1 (act (strengthenRuleByFrmL2 invL r)) s0 = trans1 (act r) s0"
        using c5 by auto
      have c7: "reachableUpTo I rs2 n s0"
        using b0 c1 by blast
      have c8: "formEval (pre (strengthenRuleByFrmL2 invL r)) s0"
        by (simp add: c4)
      have c8:"reachableUpTo I rs2 (Suc n) (trans1 (act (strengthenRuleByFrmL2 invL r)) s0)"
        by (metis act.simps c2 c7 c8 equivRule.elims(2) pre.simps reachableSetNext strengthenRuleByFrml2Equiv)
      have "reachableUpTo I rs2 (Suc n) s \<and> (\<forall>invL f. invL \<in> S \<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s)"
        by (metis a2 act.simps c1 c2 c8 equivRule.elims(2) equivStatement_def strengthenRuleByFrml2Equiv)
    }
    moreover
    {
      assume c2: "guard g a \<in> rs2"
      have "reachableUpTo I rs2 (Suc n) s \<and> (\<forall>invL f. invL \<in> S \<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s)"
        using a2 b0 c1 c2 reachableSetNext by blast 
    }
    ultimately show "reachableUpTo I rs2 (Suc n) s \<and> (\<forall>invL f. invL \<in> S \<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s)"
      by blast
  qed
qed 

lemma strengthenFrmList2Prot2SimProt:
  assumes a1: "\<forall>r. r \<in> rs \<longrightarrow> ((\<exists>invL. invL \<in> S  \<and>  strengthenRuleByFrmL2 invL r \<in> rs2) \<or> (r \<in> rs2))"
    and a2: "\<forall>i s invL f. reachableUpTo I rs2 i s \<longrightarrow> invL \<in> S\<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s" 
  shows "\<forall>s. reachableUpTo I rs i s \<longrightarrow>
    (reachableUpTo I rs2 i s \<and> (\<forall>invL f.   invL \<in> S\<longrightarrow> f \<in> set invL\<longrightarrow> formEval f s))" (is "?P i")
proof (rule allI, rule impI)
  fix s
  assume b1: "reachableUpTo I rs i s"
  let ?rs1="{r'. (\<exists>invL r.  r \<in> rs \<and>invL \<in> S \<and> r' = strengthenRuleByFrmL invL r \<and> 
    strengthenRuleByFrmL2 invL r \<in> rs2) \<or>
                 (r' \<in> rs \<and> r' \<in> rs2)}"
  have b2:"\<forall>i s. reachableUpTo I ?rs1 i s \<longrightarrow>
    reachableUpTo I rs2 i s \<and> (\<forall>invL f.   invL \<in> S\<longrightarrow> f \<in> set invL\<longrightarrow> formEval f s)"
    apply (rule allI)
    apply (rule_tac ?rs1.0="?rs1" and ?rs="rs" and ?rs2.0="rs2" in strengthenFrmLstProt2SimProt1)
    apply auto apply (cut_tac a2) by blast
  have b3: "\<forall>s. reachableUpTo I rs i s\<longrightarrow>
    reachableUpTo I ?rs1 i s \<and> (\<forall>invL f.   invL \<in> S\<longrightarrow> f \<in> set invL\<longrightarrow> formEval f s)"
    apply (rule strengthenFrmListProt1SimProt )
    using a1 apply auto[1]
    using b2 by blast
  show "reachableUpTo I rs2 i s \<and> (\<forall>invL f.   invL \<in> S\<longrightarrow> f \<in> set invL\<longrightarrow> formEval f s)"
    using b1 b2 b3 by blast
qed


primrec map2'::"(nat \<Rightarrow> nat \<Rightarrow> formula) list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula list" where
  "map2' [] i j = []" |
  "map2' (pf # pfl) i j = (pf i j) # (map2' pfl i j)"

lemma map2'Corres: 
  "(i \<le> N \<and> j \<le> N) \<longrightarrow> f \<in> set (map2' invL0 i j) \<longrightarrow> (\<exists>pf. pf \<in> set invL0 \<and> f = pf i j)"
  by (induct_tac invL0, auto)

definition strengthenFwRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>bool" where
"strengthenFwRel rs S rs2 N\<equiv>
\<forall>r'. r' \<in> rs2 \<longrightarrow> ((\<exists>r invL i j. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> r \<in> rs \<and>
                r' = strengthenRuleByFrmL2 (map2' invL i j) r) \<or> r' \<in> rs)"


lemma strenRelFwRefl: 
  shows "strengthenFwRel rs S rs N"
  apply( unfold strengthenFwRel_def)
  by (metis) 


definition strengthenBwRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>bool" where
"strengthenBwRel rs S rs2 N\<equiv>
\<forall>r. r \<in> rs \<longrightarrow> ((\<exists>invL i j. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and>
                strengthenRuleByFrmL2 (map2' invL i j) r \<in> rs2) \<or> r \<in> rs2)"


lemma strenRelBwUnion:
  assumes a1:"strengthenBwRel rs1 S rs1' N " and
  a2:"strengthenBwRel rs2 S rs2' N"
  shows "strengthenBwRel (rs1 \<union> rs2) S (rs1' \<union> rs2') N"
  apply(cut_tac a1 a2, unfold strengthenBwRel_def)
  by (metis Un_iff) 
  

lemma strenRelBwRefl': 
  shows "strengthenBwRel rs S rs N"
  apply( unfold strengthenBwRel_def)
  by (metis)  

definition strengthenRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>bool" where
"strengthenRel rs S rs2 N\<equiv>
  strengthenFwRel rs S rs2 N \<and> strengthenBwRel rs S rs2 N"


subsection \<open>Node Abstraction and Data Abstraction\<close>

text \<open>Abstraction of constant:
  Index greater than M is abstracted to M + 1, others are unchanged.
\<close>
primrec DabsTransfConst :: " scalrValueType \<Rightarrow> scalrValueType" where
  "DabsTransfConst  (enum t n) = enum t n"
| "DabsTransfConst  (index n) = (  index n)"
| "DabsTransfConst  (boolV b) = boolV b"
| "DabsTransfConst  dontCare = dontCare"
| "DabsTransfConst  (data b) =(if (b=0) then ( data b) else ( data 1))"

primrec absTransfConst :: "nat \<Rightarrow> scalrValueType \<Rightarrow> scalrValueType" where
  "absTransfConst M (enum t n) = enum t n"
| "absTransfConst M (index n) = (if n > M then index (M+1) else index n)"
| "absTransfConst M (boolV b) = boolV b"
| "absTransfConst M dontCare = dontCare"
| "absTransfConst M (data b) = data b"


text \<open>Abstraction of state\<close>
fun abs1 :: "nat \<Rightarrow> state \<Rightarrow> state" where
  "abs1 M s (Para nm i) = (if i > M then dontCare else absTransfConst M (s (Para nm i)))"
| "abs1 M s (Ident v) = absTransfConst M (s (Ident v))"
| "abs1 M s dontCareVar = dontCare"


text \<open>Abstraction of state\<close>
fun Dabs1 :: "  state \<Rightarrow> state" where
  "Dabs1   s (Para nm i) = (  DabsTransfConst  (s (Para nm i)))"
| "Dabs1  s (Ident v) = DabsTransfConst  (s (Ident v))"
| "Dabs1   s dontCareVar = dontCare"

text \<open>Abstraction of variables\<close>
primrec absTransfVar :: "nat \<Rightarrow> varType \<Rightarrow> varType" where 
  "absTransfVar M (Ident n) = Ident n" |
  "absTransfVar M (Para n i) =
    (if i > M then dontCareVar else Para n i)" |
  "absTransfVar M dontCareVar = dontCareVar"

lemma abs1Eq:
  "abs1 M s v = (if absTransfVar M v = dontCareVar then dontCare else absTransfConst M (s v))"
  apply (cases v) by auto

primrec boundVar :: "nat \<Rightarrow> expType \<Rightarrow> bool" where
  "boundVar i (Const n) = 
  (case n of 
    index j \<Rightarrow> i = j | boolV b \<Rightarrow> True | enum t v \<Rightarrow> False | _ \<Rightarrow>False)"
| "boundVar i (IVar v) =
    (case v of Ident n \<Rightarrow> True | Para n j \<Rightarrow> i = j | dontCareVar \<Rightarrow> False)"
| "boundVar i (iteForm b e1 e2) = False"
| "boundVar i (dontCareExp) = False"

primrec boundExp :: "nat \<Rightarrow> expType \<Rightarrow> bool" and
        boundForm :: "nat \<Rightarrow> formula \<Rightarrow> bool" where
  "boundExp i (Const x) =
    (case x of enum nm k \<Rightarrow> True | boolV b \<Rightarrow> True |data d\<Rightarrow>True | index j \<Rightarrow> i = j | _ \<Rightarrow> False)"
| "boundExp i (IVar v) = False"
| "boundExp i (iteForm b e1 e2) = False"
| "boundExp i (dontCareExp) = False"

| "boundForm i (eqn e1 e2) = (boundVar i e1 \<and> boundExp i e2)"
| "boundForm i (neg f) = boundForm i f"
| "boundForm i (andForm f1 f2) = (boundForm i f1 \<and> boundForm i f2)"
| "boundForm i (orForm f1 f2) = (boundForm i f1 \<and> boundForm i f2)"
| "boundForm i (implyForm f1 f2) = (boundForm i f1 \<and> boundForm i f2)"
| "boundForm i chaos = True"
| "boundForm i dontCareForm = False"
| "boundForm i (forallForm pf N) = False"
| "boundForm i (existForm pf N) = False"
| "boundForm i (forallFormExcl pf j N) = False"


primrec dboundExp :: "nat \<Rightarrow> expType \<Rightarrow> bool" and
        dboundForm :: "nat \<Rightarrow> formula \<Rightarrow> bool" where
  "dboundExp i (Const x) =
    (case x of enum nm k \<Rightarrow> True | boolV b \<Rightarrow> True |data d\<Rightarrow>d=i | index j \<Rightarrow> True | _ \<Rightarrow> False)"
| "dboundExp i (IVar v) = True"
| "dboundExp i (iteForm b e1 e2) = (dboundForm i b \<and>  dboundExp i e1 \<and> dboundExp i e2)"
| "dboundExp i (dontCareExp) = False"

| "dboundForm i (eqn e1 e2) = ( dboundExp i e1 \<and> dboundExp i e2)"
| "dboundForm i (neg f) = dboundForm i f"
| "dboundForm i (andForm f1 f2) = (dboundForm i f1 \<and> dboundForm i f2)"
| "dboundForm i (orForm f1 f2) = (dboundForm i f1 \<and> dboundForm i f2)"
| "dboundForm i (implyForm f1 f2) = (dboundForm i f1 \<and> dboundForm i f2)"
| "dboundForm i chaos = True"
| "dboundForm i dontCareForm = False"
| "dboundForm i (forallForm pf N) = (\<forall>k. dboundForm i (pf k)) "
| "dboundForm i (existForm pf N) = (\<forall>k. dboundForm i (pf k))"
| "dboundForm i (forallFormExcl pf j N) = (\<forall>k. dboundForm i (pf k))"

primrec boundValue::"nat \<Rightarrow>scalrValueType \<Rightarrow> bool" where
  "boundValue M (enum nm k) = True" | 
  "boundValue M (boolV b) = True" |
  "boundValue M (index i) =  (i \<le> M) " |"boundValue M (data b) = True" |
  "boundValue M (dontCare) =False"

lemma absUnchanged:
  assumes "case v of Ident n \<Rightarrow> True | Para n i \<Rightarrow> i \<le> M | dontCareVar \<Rightarrow> False"
    and "case s v of index i \<Rightarrow> i \<le>M | dontCare \<Rightarrow> False | _ \<Rightarrow> True"
  shows "abs1 M s v = s v"
  apply (cases v) using assms by (cases "s v", auto)+

lemma absUnchanged2:
  assumes "case v of Ident n \<Rightarrow> True | Para n i \<Rightarrow> i \<le> M | dontCareVar \<Rightarrow> False"
    and "case abs1 M s v of index i \<Rightarrow> i\<le>M | dontCare \<Rightarrow> False | _ \<Rightarrow> True"
  shows "abs1 M s v = s v"
  apply (cases v) using assms by (cases "s v", auto)+


lemma boundEval:
  assumes "i \<le> M"
  shows "(boundExp  i e \<longrightarrow> ( expEval e s) = expEval e (abs1 M s)  ) \<and>
         (boundForm  i f \<longrightarrow> (formEval f s \<longleftrightarrow> formEval f (abs1 M s)))"
    (is "?Pe e \<and> ?Pf f")
proof (induction rule: expType_formula.induct)
  case (eqn e1 e2)
  show ?case 
  proof 
    assume a1:"boundForm i (e1 =\<^sub>f e2)"
    have a3:"( expEval e2 s) = expEval e2 (abs1 M s)"
      using a1 eqn.IH(2) by force
    have a2:"(boundVar i e1 \<and> boundExp i e2) "
      by (cut_tac a1,auto)
    have b1:"( expEval e2 s) = expEval e2 (abs1 M s)  "
      using a2 eqn.IH(2) by blast
    show "formEval (e1 =\<^sub>f e2) s = formEval (e1 =\<^sub>f e2) (abs1 M s) "
    proof(cases e1)
      case (IVar x1)
      note IVar1 = IVar
      then show ?thesis
      proof(cases e2)
        case (IVar x2)
        thm IVar1
        then show ?thesis
          using a2 boundExp.simps(2) by blast  
      next
        case (Const x2)
        then show ?thesis 
        proof(case_tac x2)
          fix x11 x12
          assume c1:"x2 = enum x11 x12 "
          show ?thesis 
            apply(case_tac "s x1")
               apply (smt (z3) IVar1 a2 a3 abs1Eq absTransfConst.simps(1) absTransfVar.simps(1) absTransfVar.simps(2) assms boundVar.simps(2) evalEqn evalVar not_le varType.exhaust varType.simps(10) varType.simps(11))
              apply (simp add: Const IVar1 abs1Eq c1)
             apply (simp add: Const IVar1 abs1Eq c1)
            using IVar1 abs1Eq absTransfConst.simps(4) b1 evalEqn evalVar apply presburger
            by (simp add: Const IVar1 abs1Eq c1)
        next
          fix x2a
          assume c1:"x2 = index x2a"
          have c2:"x2a =i "
            using Const a2 c1 by auto 
          show ?thesis 
          proof(cases "s x1")
            case (enum x11 x12)
            then show ?thesis
              by (simp add: Const IVar1 abs1Eq c1) 
          next
            case (index i1)
            show ?thesis
            proof
              assume d1:"formEval (e1 =\<^sub>f e2) s "
              have d3:"expEval e2  (abs1 M s) = index i1"
                using IVar1 a3 d1 index by force
              have d4:"expEval e1  (abs1 M s) = index i1"
                by (smt (verit, ccfv_SIG) Const IVar1 a2 abs1.elims absTransfConst.simps(2) assms boundVar.simps(2) c1 c2 d3 evalConst evalVar index leD varType.simps(10) varType.simps(11))
              show "formEval (e1 =\<^sub>f e2) (abs1 M s)"
                using d3 d4 evalEqn by presburger 
            next
              assume d1:"formEval (e1 =\<^sub>f e2) (abs1 M s)"
               have d4:"expEval e2  (abs1 M s) = index x2a"
                 by (simp add: Const c1) 
               have d5:"expEval e2 s = index x2a"
                 by (simp add: b1 d4)
              
                 
              have d6:"expEval e1  (abs1 M s) = index x2a"
                apply(simp add:Const IVar1 index)
                using IVar1 d1 d4 by force
                
              have d7:"expEval e1  s = index i1"
                by (simp add: IVar1 index)

              have d8:"s x1=index i1"
                using index by blast

              have d9:" (abs1 M s) x1=index i1"
                by (smt (verit, best) IVar1 abs1.elims absUnchanged2 assms c2 d6 evalVar index not_le_imp_less scalrValueType.distinct(11) scalrValueType.simps(26) varType.simps(10) varType.simps(9))   
                 
              have d10:"i1=x2a"
                using  d6 d7 d8 d9 by(auto simp add:IVar1 index)
                
              show "formEval (e1 =\<^sub>f e2) s"
                by (simp add: Const IVar1 c1 d10 index) 
            qed
           
          next
            case (boolV x3)
            then show ?thesis
              by (simp add: Const IVar1 abs1Eq c1) 
          next
            case dontCare
            then show ?thesis
              using IVar1 a3 abs1Eq absTransfConst.simps(4) evalEqn evalVar by presburger  
          next
            case (data d)
            then show ?thesis
              by (simp add: Const IVar1 abs1Eq c1)
              
          qed
        next
          fix x3
          assume c1:"x2=(boolV x3)"
          show ?thesis
          proof(cases "s x1")
            case (enum x11 x12)
            then show ?thesis
              by (simp add: Const IVar1 abs1Eq c1)  
          next
            case (index x2)
            then show ?thesis
              by (simp add: Const IVar1 abs1Eq c1) 
          next
            case (boolV x4)
            show ?thesis
            proof
              assume d1:"formEval (e1 =\<^sub>f e2) s "
              have d2:"x3=x4"
                using Const IVar1 boolV c1 d1 by force 
              have d3:"expEval e2  (abs1 M s) = boolV x3"
                using Const c1 evalConst by presburger 
              have d4:"expEval e1  (abs1 M s) = boolV x4"
                apply(cut_tac IVar1, auto)
                by (smt (verit, del_insts) a2 abs1.elims absTransfConst.simps(3) assms boolV boundVar.simps(2) leD varType.simps(10) varType.simps(11)) 
              show "formEval (e1 =\<^sub>f e2) (abs1 M s)"
                by (simp add: d2 d3 d4) 
            next
              assume d1:"formEval (e1 =\<^sub>f e2) (abs1 M s)"
              show "formEval (e1 =\<^sub>f e2) s"
                by (metis Const IVar1 abs1Eq absTransfConst.simps(3) boolV c1 d1 evalConst evalEqn evalVar scalrValueType.distinct(15))
                (*by (metis Const IVar1 abs1Eq absTransfConst.simps(3) boolV c1 d1 evalConst evalEqn evalVar scalrValueType.distinct(11)) *)  
            qed
          next
            case dontCare
            then show ?thesis
              by (simp add: IVar1 a3 abs1Eq)   
          next
            case (data d)
            then show ?thesis
              by (simp add: Const IVar1 abs1Eq c1)
              
          qed
        next
          assume c1:"x2=dontCare"
          show ?thesis
            using Const a2 c1 by auto
        next
          fix d
          assume c1:" x2=(data d)"
            then show ?thesis
              by (smt (verit, ccfv_SIG) Const IVar1 a2 abs1.elims absUnchanged absUnchanged2 assms boundVar.simps(2) evalConst evalEqn evalVar scalrValueType.simps(29) varType.simps(10) varType.simps(11) varType.simps(9))
              
        qed 
      next
        case (iteForm x31 x32 x33)
        show ?thesis
          using a2 boundExp.simps(3) iteForm by blast 
      next
        case dontCareExp
        then show ?thesis
          using a2 boundExp.simps(4) by blast  
      qed
    next
      case (Const x2)
      then show ?thesis
        by (simp add: b1)
    next 
      case (iteForm x31 x32 x33)
      then show ?thesis
        using a2 boundVar.simps(3) by blast 
    next
      case dontCareExp
      then show ?thesis
        using a2 boundVar.simps(4) by blast   
    qed
  qed
qed (auto) 
 
lemma boolTypeSafe:
  "deriveExp env e = Some boolType \<longrightarrow>
   fitEnv s env \<longrightarrow> getValueType (expEval e s) = boolType" (is "?P e")
proof (induct_tac e)
  fix x1
  let ?e="IVar x1" 
  show "?P ?e"
    by (simp add: fitEnv_def)
next
  fix x2
  let ?e="Const x2"
  show "?P ?e"
    by (case_tac x2, auto)
qed (auto)

lemma enumTypeSafe:
  "deriveExp env e = Some enumType\<longrightarrow>
   fitEnv s env \<longrightarrow> getValueType (expEval e s) = enumType" (is "?P e")
proof(induct_tac e)
  fix x1
  let ?e="IVar x1" 
  show "?P ?e"
    by (simp add: fitEnv_def)
next
  fix x2
  let ?e="Const x2"
  show "?P ?e"
    by (case_tac x2, auto)
qed (auto)

lemma indexTypeSafe:
  "deriveExp env e = Some indexType \<longrightarrow>
   fitEnv s env \<longrightarrow> getValueType (expEval e s) = indexType" (is "?P e")
proof (induct_tac e)
  fix x1
  let ?e="IVar x1" 
  show "?P ?e"
    by (simp add: fitEnv_def)
next
  fix x2
  let ?e="Const x2"
  show "?P ?e"
    by (case_tac x2, auto)
qed (auto)


lemma dataTypeSafe:
  "deriveExp env e = Some dataType \<longrightarrow>
   fitEnv s env \<longrightarrow> getValueType (expEval e s) = dataType" (is "?P e")
proof (induct_tac e)
  fix x1
  let ?e="IVar x1" 
  show "?P ?e"
    by (simp add: fitEnv_def)
next
  fix x2
  let ?e="Const x2"
  show "?P ?e"
    by (case_tac x2, auto)
qed (auto)


text \<open>Abstraction of expressions and formulas\<close>
primrec absTransfExp :: "envType\<Rightarrow>nat \<Rightarrow> expType \<Rightarrow> expType" and
  absTransfForm :: "envType\<Rightarrow>nat \<Rightarrow> formula \<Rightarrow> formula" where
  "absTransfExp env M  (Const i) = Const (absTransfConst M i)" |

  "absTransfExp env M  (IVar v) =
    (if absTransfVar  M  v = dontCareVar then dontCareExp
     else IVar (absTransfVar M v))" |

  "absTransfExp env M  (iteForm b e1 e2) = 
    (if (absTransfForm env M b) = dontCareForm \<or> 
    (absTransfExp env M e1) =dontCareExp \<or>
       (absTransfExp env M e2) =dontCareExp\<or>
      (~safeForm env M b) then dontCareExp
    else (iteForm  (absTransfForm env M b) (absTransfExp env M e1) 
     (absTransfExp env M e2)))" |

  "absTransfExp env M  dontCareExp = dontCareExp" |

  "absTransfForm env M  (eqn e1 e2) =
    (let e1'=absTransfExp env M  e1 in
     let e2'=absTransfExp env M  e2 in
    (if  e1'= dontCareExp \<or>  e2' = dontCareExp
     then dontCareForm 
    
     else eqn e1' e2'))" |

  "absTransfForm env M  (neg f) =
    (if safeForm env M  f then neg (absTransfForm env M f) else dontCareForm)" |

  "absTransfForm env M  (andForm f1 f2) =
    (let f1'=absTransfForm env M f1 in
     let f2'=absTransfForm env M f2 in
     if f1' = dontCareForm    then f2'
     else if f2' = dontCareForm    then f1'
     else andForm f1' f2')" |

  "absTransfForm env0 M (orForm a b) =
    (let f1= absTransfForm env0 M a in
     let f2= absTransfForm env0 M b in
     if f1 = dontCareForm then dontCareForm
     else if f2 = dontCareForm then dontCareForm
     else orForm f1 f2)" |

  "absTransfForm env M (implyForm a b) =  
    (let f1 = absTransfForm env M a in
     let f2 = absTransfForm env M b in
     if f1 = dontCareForm then dontCareForm
     else if f2 = dontCareForm then dontCareForm
     else if safeForm env M a then implyForm f1 f2 else dontCareForm)" |

  "absTransfForm env M chaos = chaos" |

  "absTransfForm env M dontCareForm = dontCareForm" |

  "absTransfForm env M (forallForm (pf) N) =
    (if M \<le> N \<and> (\<forall>j. boundForm j (pf j))
     then forallForm pf M
     else dontCareForm)" |

  "absTransfForm env M (existForm (pf) N) =
    (if M \<le>N \<and> (\<forall>j. boundForm j (pf j)) \<and>
    (\<forall>j. j>M \<longrightarrow> absTransfForm env M (pf j) \<noteq>dontCareForm \<and>
        absTransfForm env M (pf j) = absTransfForm env M (pf (M +1)) ) 
    
    then (orForm (existForm (pf) (M ) ) (absTransfForm env M (pf (M +1))))
     else 
        (if ( (\<forall>j. dboundForm j (pf j) \<and> absTransfForm env M (pf j) ~= dontCareForm )) 
         then existForm (\<lambda>j.  absTransfForm env M (pf j)) N 
         else dontCareForm))" |
(* (\<exists> apf. (\<forall>j. absTransfForm env M (pf j) =apf j \<and> absTransfForm env M (pf j) ~= dontCareForm )) *)
  "absTransfForm env M (forallFormExcl pf i N) =
    (if i > M \<and> M \<le> N \<and> (\<forall>j. boundForm j (pf j)) then forallForm pf M
     else if i \<le> M \<and> M \<le> N \<and> (\<forall>j. boundForm j (pf j)) then forallFormExcl pf i M
     else dontCareForm)"


primrec DsafeExp :: "envType   \<Rightarrow> expType \<Rightarrow> bool" and
        DsafeForm :: "envType  \<Rightarrow> formula \<Rightarrow> bool" where
  "DsafeExp s  (Const x) =
    (case x of enum nm i \<Rightarrow> True
             | boolV b \<Rightarrow> True
             | index n \<Rightarrow> True
             | data d \<Rightarrow> d=0
             | _ \<Rightarrow> False)"

| "DsafeExp s  (IVar v) =
   ( (s v = enumType \<or> s v = boolType  \<or> s v = indexType ))"
| "DsafeExp env  (iteForm b e1 e2) = (deriveExp env e1=deriveExp env e2 \<and>DsafeExp env    e1 \<and> DsafeExp  env   e2 \<and> DsafeForm  env   b)"
 (* False" *)
| "DsafeExp env   dontCareExp = False"

(* There are three possibilities:
   1. e1 is of index type, either a Dsafe variable or a constant, and e2 is
      a constant Dsafe index i.
   2. e2 is of index type, either a Dsafe variable or a constant, and e1 is
      a constant Dsafe index i.
   3. both e1 and e2 are either enum or boolean values, and both are Dsafe. *)
| "DsafeForm env   (eqn e1 e2) = ((deriveExp env e1=deriveExp env e2 \<and> 
  (deriveExp env e1\<noteq>Some(dataType)\<longrightarrow> DsafeExp env   e1 \<and> DsafeExp env   e2) \<and>
  (deriveExp env e1=Some(dataType)\<longrightarrow>((e1=Const (data 0)&(\<exists>v. e2=IVar v)) \<or>((\<exists>v. e1=IVar v) \<and>e2=Const (data 0)))))) "

| "DsafeForm env   (neg f) = DsafeForm env   f"
| "DsafeForm env   (andForm f1 f2) = (DsafeForm env   f1 \<and> DsafeForm env   f2)"
| "DsafeForm env   (orForm f1 f2) = (DsafeForm env   f1 \<and> DsafeForm env   f2)"
| "DsafeForm env   (implyForm f1 f2) = (DsafeForm env  f1 \<and> DsafeForm env  f2)"
| "DsafeForm env  (forallForm pf N) =  (\<forall>i. i\<le>N \<longrightarrow>DsafeForm env (pf i))"
| "DsafeForm env  (existForm pf N) =  (\<forall>i. i\<le>N \<longrightarrow>DsafeForm env (pf i))"
| "DsafeForm env  (forallFormExcl pf j N) =  (\<forall>i. i\<le>N \<longrightarrow>DsafeForm env (pf i))"
| "DsafeForm env  chaos = True"
| "DsafeForm env  dontCareForm = False"


primrec DabsTransfExp :: "envType  \<Rightarrow> expType \<Rightarrow> expType" and
  DabsTransfForm :: "envType  \<Rightarrow> formula \<Rightarrow> formula" where
  "DabsTransfExp env   (Const i) = Const (DabsTransfConst  i)" |

  "DabsTransfExp env   (IVar v) =
   (if     v = dontCareVar then dontCareExp
   else
    (IVar v))" |

  "DabsTransfExp env   (iteForm b e1 e2) = 
    ( if (DsafeForm env b \<and> (DabsTransfExp env  e1)\<noteq> dontCareExp \<and> 
      (DabsTransfExp env  e2) \<noteq>dontCareExp) then
      (iteForm  (DabsTransfForm env  b) (DabsTransfExp env   e1) 
     (DabsTransfExp env  e2))
      else dontCareExp)" |

  "DabsTransfExp env   dontCareExp = dontCareExp" |

  "DabsTransfForm env   (eqn e1 e2) =
    (let e1'=DabsTransfExp env   e1 in
     let e2'=DabsTransfExp env   e2 in
    (if ((  (DabsTransfExp env  e1)\<noteq> dontCareExp \<and> 
      (DabsTransfExp env  e2) \<noteq>dontCareExp)) then  eqn e1' e2' else dontCareForm))" |

  "DabsTransfForm env   (neg f) =
    ( if (DsafeForm env f) then  neg (DabsTransfForm env  f) 
      else dontCareForm )" |


  "DabsTransfForm env   (andForm f1 f2) =
    (let f1'=DabsTransfForm env  f1 in
     let f2'=DabsTransfForm env  f2 in 
     if f1 = dontCareForm then dontCareForm
     else if f2 = dontCareForm then dontCareForm
     else andForm f1' f2')" |

  "DabsTransfForm env0  (orForm a b) =
    (let f1= DabsTransfForm env0  a in
     let f2= DabsTransfForm env0  b in  
     if f1 = dontCareForm then dontCareForm
     else if f2 = dontCareForm then dontCareForm
     else orForm f1 f2)" |

  "DabsTransfForm env  (implyForm a b) =  
    (let f1 = DabsTransfForm env  a in
     let f2 = DabsTransfForm env  b in  
     if f1 = dontCareForm then dontCareForm
     else if f2 = dontCareForm then dontCareForm
     else   if DsafeForm env a  then implyForm f1 f2 else dontCareForm  )" |

  "DabsTransfForm env  chaos = chaos" |

  "DabsTransfForm env  dontCareForm = dontCareForm" |

  "DabsTransfForm env  (forallForm (pf) N) =     
    ( if (DsafeForm env (forallForm (pf) N))
      then  forallForm   (pf ) N
      else  (if  (\<forall>j. boundForm j (pf j)) 
              then forallForm (\<lambda> j.  DabsTransfForm env (pf j )) N 
             else dontCareForm))"  |
(*\<and> (\<exists>pf'. \<forall>j.  DabsTransfForm env (pf j ) = pf' j*)
  "DabsTransfForm env  (existForm (pf) N) =
     (if (DsafeForm env (existForm (pf) N))
      then  
      existForm pf  N
      else (if ( (\<forall>j. j>0 \<longrightarrow>(DabsTransfForm env  (pf j) \<noteq>dontCareForm \<and>
        DabsTransfForm env  (pf j) = DabsTransfForm env (pf 1)) ))
         then orForm (DabsTransfForm env ( pf 0)) (DabsTransfForm env ( pf 1))
         else dontCareForm ))
      " |

  "DabsTransfForm env   (forallFormExcl pf i N) =
    (if (DsafeForm env (forallForm (pf) N)) then  forallFormExcl pf i N
     else dontCareForm )"


definition wellDerivedExp::"expType \<Rightarrow> envType \<Rightarrow> bool" where
"wellDerivedExp e env \<equiv> deriveExp env e =Some dataType \<or>
  deriveExp env e =Some boolType \<or>  deriveExp env e =Some indexType \<or>
  deriveExp env e =Some enumType"

lemma absTransfConstEnum [simp]:
  "absTransfConst M v = enum nm i \<longleftrightarrow> v = enum nm i"
  apply (cases v) by auto


lemma DabsTransfConstEnum [simp]:
  "DabsTransfConst  v = enum nm i \<longleftrightarrow> v = enum nm i"
  apply (cases v) by auto

lemma absTransfConstBoolV [simp]:
  "absTransfConst M v = boolV b \<longleftrightarrow> v = boolV b"
  apply (cases v) by auto


lemma DabsTransfConstBoolV [simp]:
  "DabsTransfConst  v = boolV b \<longleftrightarrow> v = boolV b"
  apply (cases v) by auto

lemma absTransfConstEnum1 [simp]:
  "fitEnv s env \<Longrightarrow> env v = enumType \<Longrightarrow> absTransfConst M (s v) = s v"
  apply(unfold fitEnv_def getValueType_def, auto)
  by (smt (verit, best) absTransfConst.simps(4) absTransfConst.simps(5) absTransfConstBoolV absTransfConstEnum getValueType.simps(2) scalrValueType.exhaust typeType.simps(2) typeType.simps(6)) 


lemma DabsTransfConstEnum1 [simp]:
  "fitEnv s env \<Longrightarrow> env v = enumType \<Longrightarrow> DabsTransfConst  (s v) = s v"
  apply(unfold fitEnv_def getValueType_def, auto)
  by (metis DabsTransfConst.simps(1) DabsTransfConst.simps(2) DabsTransfConst.simps(3) DabsTransfConst.simps(4) getValueType.simps(5) scalrValueType.exhaust typeType.distinct(5) typeType.distinct(7))
   
lemma absTransfConstBoolV1 [simp]:
  "fitEnv s env \<Longrightarrow> env v = boolType \<Longrightarrow> absTransfConst M (s v) = s v"
  apply(unfold fitEnv_def getValueType_def, auto)
  by (metis absTransfConst.simps(1) absTransfConst.simps(3) absTransfConst.simps(4) getValueType.simps(2) getValueType.simps(5) scalrValueType.exhaust typeType.distinct(15) typeType.distinct(17) typeType.distinct(9)) 

lemma DabsTransfConstBoolV1 [simp]:
  "fitEnv s env \<Longrightarrow> env v = boolType \<Longrightarrow> DabsTransfConst  (s v) = s v"
  apply(unfold fitEnv_def getValueType_def, auto)
  by (metis DabsTransfConst.simps(1) DabsTransfConst.simps(2) DabsTransfConst.simps(3) DabsTransfConst.simps(4) getValueType.simps(5) scalrValueType.exhaust typeType.distinct(15) typeType.distinct(17))
  
lemma absTransfConstData1 [simp]:
  "fitEnv s env \<Longrightarrow> env v = dataType \<Longrightarrow> absTransfConst M (s v) = s v"
  apply(unfold fitEnv_def getValueType_def, auto)
  by (metis absTransfConst.simps(3) absTransfConst.simps(4) absTransfConst.simps(5) getValueType.simps(1) getValueType.simps(2) scalrValueType.exhaust typeType.distinct(14) typeType.distinct(20) typeType.distinct(7))  

(*lemma DabsTransfConstData1 [simp]:
  "fitEnv s env \<Longrightarrow> env v = dataType \<Longrightarrow> DsafeExp env (IVar v) \<Longrightarrow>absTransfConst M (s v) = s v"
  by(unfold fitEnv_def getValueType_def, auto) 
*)
lemma absBoundVar:
  assumes "i \<le> M"
    and "boundVar i e"
  shows "absTransfExp env M e = e"
proof (cases e)
  case (IVar v)
  have "absTransfVar M v = v"
    apply (cases v)
      apply auto using assms(2) unfolding IVar
    using assms by auto
  then show ?thesis
    using IVar apply auto
    using assms unfolding IVar by auto
next
  case (Const x2)
  then show ?thesis
    using assms Const
    apply(case_tac x2)
    by auto
next
  case (iteForm x31 x32 x33)
  then show ?thesis
    using assms by auto
next
  case dontCareExp
  then show ?thesis by auto
qed

lemma DabsBoundVar:
  assumes   "boundVar i e"
  shows "DabsTransfExp env  e = e"
proof (cases e)
  case (IVar v)
  show ?thesis
    using IVar apply auto
    using assms unfolding IVar by auto
next
  case (Const x2)
  then show ?thesis
    using assms Const
    apply(case_tac x2)
    by auto
next
  case (iteForm x31 x32 x33)
  then show ?thesis
    using assms by auto
next
  case dontCareExp
  then show ?thesis by auto
qed

lemma safeVarLemma:
  "safeVar v M \<Longrightarrow> absTransfVar M v = v" 
  by (case_tac "v", auto)

lemma safeEval1:
  "(fitEnv s env \<longrightarrow>
     deriveExp env e \<noteq> None \<longrightarrow>
     safeExp env M e \<longrightarrow>
     absTransfExp env M e \<noteq> dontCareExp \<and>
     absTransfConst M (expEval e s) = expEval (absTransfExp env M e) (abs1 M s)) \<and>
    (fitEnv s env \<longrightarrow>
     deriveForm env f \<longrightarrow>
     safeForm env M f \<longrightarrow>
     absTransfForm env M f \<noteq> dontCareForm \<and>
     formEval f s = formEval (absTransfForm env M f) (abs1 M s))"
  (is "(?antE1 e \<longrightarrow>?antE2 e\<longrightarrow> ?consE e s) \<and> (?antF1 f \<longrightarrow>?antF2 f \<longrightarrow> ?consF f s)")
proof (induction rule: expType_formula.induct[where expType=e and formula=f])
  case (IVar x)
  then show ?case
    apply (cases x) by auto
next
  case (eqn e1 e2)
  show ?case
  proof (rule impI)+
    assume b1:"fitEnv s env" and 
      b2:"deriveForm env (e1 =\<^sub>f e2) " and
      b3:"safeForm env M (e1 =\<^sub>f e2) " 
    show "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
    formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
    proof -
      have c1:"(deriveExp  env e1 =deriveExp  env e2)& (deriveExp  env e1\<noteq>None) "
        using b2 deriveForm.simps(1) by blast
      have "deriveExp env e1 = Some indexType \<and>
            safeExp env M e2 \<and>
            (\<exists>i. e2 = Const (index i)) \<and>
            ((\<exists>v. e1 = IVar v \<and> safeVar v M) \<or> (\<exists>i. e1 = Const (index i))) \<or>
            deriveExp env e2 = Some indexType \<and>
            safeExp env M e1 \<and>
            (\<exists>i. e1 = Const (index i)) \<and>
            ((\<exists>v. e2 = IVar v \<and> safeVar v M) \<or> (\<exists>i. e2 = Const (index i))) \<or>
            deriveExp env e1 = Some enumType \<or>
            deriveExp env e1 = Some boolType  \<or>
            deriveExp env e1 = Some dataType\<and> safeExp env M e1 \<and> safeExp env M e2"
        using b3 by auto 
      moreover
      {assume b4:"(deriveExp env  e1=Some(indexType) \<and> 
                  safeExp env M  e2\<and>(\<exists>i. e2=Const ( index i) ) \<and>
                  (( \<exists> v. e1=IVar v \<and> safeVar v M) | (\<exists>i. e1=Const ( index i))))"
        have b5: "deriveExp env  e2=Some(indexType)"
          by(cut_tac b2 b4,auto)
        have b6: "getValueType (expEval e1 s) = indexType"
          using b4 b1 indexTypeSafe by blast
        have b7: "getValueType (expEval e2 s) = indexType"
          using b5 b1 indexTypeSafe by blast
        obtain n1 where b8: "expEval e1 s = index n1"
          using b6 b4 by (cases "expEval e1 s", auto)
        obtain n2 where b9: "expEval e2 s = index n2"
          using b7 by (cases "expEval e2 s", auto)
        have b10: "n2 \<le> M"
          by (cut_tac b4 b9, auto)
        have b11: "(\<exists>v. e1 = IVar v \<and> safeVar v M) \<or> (\<exists>i. e1 = Const (index i))"
          using b4 by force
        moreover
        {assume b11:"\<exists> v. e1=IVar v \<and> safeVar v M"
          from b11 obtain v where b11:"e1=IVar v \<and> safeVar v M"
            by blast
          have b12:"expEval (absTransfExp env M e1) (abs1 M s) = 
          (if (n1 \<le>M) then (index n1) else (index (M+1)))"
            apply(cut_tac b11 b8,auto)
              apply (metis safeVar.simps(3) safeVarLemma) 
             apply (metis abs1Eq absTransfConst.simps(2) absTransfVar.simps(1) absTransfVar.simps(2) leD safeVar.simps(3) varType.exhaust)
            by (simp add: abs1Eq safeVarLemma) 
          have b13:"expEval (absTransfExp env M e2) (abs1 M s) = 
          (if (n2 \<le>M) then (index n2) else (index (M+1)))"
            by (metis eqn(2) absTransfConst.simps(2) b1 b10 b4 b9 c1 leD)
          have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
                formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
            apply(cut_tac b8 b9 b10 b11 b12 b13,auto)
               apply (metis safeVar.simps(3) safeVarLemma)
            using b4 apply force
            using b4 apply force
            by (smt (z3) One_nat_def eqn(2) absTransfExp.simps(2) add_diff_cancel_left' b1 b12 b4 c1 diff_is_0_eq' evalEqn nat.simps(3) scalrValueType.inject(2))
        }
        moreover
        {assume b11:"(\<exists>i. e1=Const ( index i))"
          from b11 obtain j where b11:"e1=Const ( index j)"
            by blast
          have b12:"expEval (absTransfExp env M e1) (abs1 M s) = 
                    (if (n1 \<le>M) then (index n1) else (index (M+1)))"
            by(cut_tac b11 b8,auto) 
          have b13:"expEval (absTransfExp env M e2) (abs1 M s) = 
                    (if (n2 \<le>M) then (index n2) else (index (M+1)))"
            by (metis eqn(2) absTransfConst.simps(2) b1 b10 b4 b9 c1 leD)
          have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
                formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
            apply(cut_tac b8 b9 b10,auto)
            using b11 b4 apply fastforce
             apply (smt (z3) b12 b13 evalDontCareForm evalEqn)
            by (smt (z3) add_le_same_cancel1 b12 b13 evalDontCareExp evalEqn getValueType.simps(2) getValueType.simps(4) not_one_le_zero scalrValueType.inject(2) typeType.distinct(11)) 
        }
        ultimately have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
          formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
          by blast
      }
      moreover
      {assume b4:"(deriveExp env  e2=Some(indexType) \<and> 
                  safeExp env M  e1\<and>(\<exists>i. e1=Const ( index i) ) \<and>
                  (( \<exists> v. e2=IVar v \<and> safeVar v  M  ) | (\<exists>i. e2=Const ( index i))))"
        have b5:"deriveExp env e1 = Some indexType"
          by(cut_tac b2 b4,auto)
        have b6:"getValueType (expEval e2 s) = indexType"
          using b4 b1 indexTypeSafe by blast
        have b7:"getValueType (expEval e1 s) = indexType"
          using b5 b1 indexTypeSafe by blast
        obtain n1 where b8:"(expEval e2 s) = index n1"
          using b6 by (cases "expEval e2 s", auto)
        obtain n2 where b9:"(expEval e1 s) = index n2"
          using b7 by (cases "expEval e1 s", auto)
        have b10: "n2 \<le> M"
          by (cut_tac b4 b9, auto)
        have b11: "(\<exists>v. e2 = IVar v \<and> safeVar v M) \<or> (\<exists>i. e2 = Const (index i))"
          using b4 by force
        moreover
        {assume b11:"\<exists> v. e2=IVar v \<and> safeVar v  M"
          from b11 obtain v where b11:"e2=IVar v \<and> safeVar v  M"
            by blast
          have b12:"expEval (absTransfExp env M e1) (abs1 M s) = 
                    (if (n2 \<le>M) then (index n2) else (index (M+1)))"
            by (metis eqn(1) absTransfConst.simps(2) b1 b10 b4 b9 c1 leD)
          have b13:"expEval (absTransfExp env M e2) (abs1 M s) = 
                    (if (n1 \<le>M) then (index n1) else (index (M+1)))"
            apply(cut_tac b11 b8,auto)
              apply (metis safeVar.simps(3) safeVarLemma) 
             apply (metis abs1Eq absTransfConst.simps(2) absTransfVar.simps(1) absTransfVar.simps(2) leD safeVar.simps(3) varType.exhaust)
            by (simp add: abs1Eq safeVarLemma) 
          have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
                formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
            apply(cut_tac b8 b9 b10 b12 b13,auto)
            apply (smt (z3) evalDontCareExp formula.simps(25) scalrValueType.simps(16)) 
             apply (smt (z3) evalDontCareForm evalEqn)
            by (smt (z3) add_le_same_cancel1 evalDontCareExp evalEqn not_one_le_zero scalrValueType.distinct(11) scalrValueType.inject(2)) 
        }
        moreover
        {assume b11:"(\<exists>i. e2=Const ( index i))"
          from b11 b8 have b11:"e2=Const ( index n1)"
            by force 
          have b12:"expEval (absTransfExp env M e1) (abs1 M s) = 
                    (if (n2 \<le>M) then (index n2) else (index (M+1)))"
            by (metis eqn(1) absTransfConst.simps(2) b1 b10 b4 b9 c1 leD)
          have b13:"expEval (absTransfExp env M e2) (abs1 M s) = 
                    (if (n1 \<le>M) then (index n1) else (index (M+1)))"
            by (simp add: b11) 
          have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
                formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
            using b11 b4 by force 
        }
        ultimately have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
          formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
          by blast
      }
      moreover
      {assume b4:"(deriveExp env  e1=Some(enumType)\<or>deriveExp env  e1=Some(boolType)\<or>deriveExp env  e1=Some(dataType))
                   \<and>(safeExp env  M e1 \<and> safeExp  env M e2)"
        moreover
        {assume b5:"deriveExp env  e1=Some( enumType) \<and>(safeExp env  M e1 \<and> safeExp  env M e2)"
          have b6:"deriveExp env  e2=Some( enumType)"
            using b2 b5 by auto
          have b7:"getValueType (expEval e1 s)= enumType"
            using   b1 b5 enumTypeSafe by blast 
          have b8:"\<exists>nt nv. (expEval e1 s)= enum nt nv" 
            apply(cut_tac b7,case_tac "(expEval e1 s)", auto)done
          have b9:"getValueType (expEval e2 s)= enumType"
            using   b1 b6 enumTypeSafe by blast 
          have b10:"\<exists>nt nv. (expEval e2 s)= enum nt nv" 
            apply(cut_tac b9,case_tac "(expEval e2 s)", auto)done
          have b11:"absTransfConst M (expEval e1 s) =  expEval (absTransfExp env M e1) (abs1 M s) "
            using eqn(1) b1 b5 by fastforce 
          have b12:"absTransfConst M (expEval e2 s) =  expEval (absTransfExp env M e2) (abs1 M s) "
            using eqn(2) b1 b5 c1 by fastforce 
          have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
                formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
            using eqn b1 b10 b5 b8 c1 by force
        }
        moreover
        {assume b5:"deriveExp env  e1=Some( boolType) \<and>(safeExp env  M e1 \<and> safeExp  env M e2)"
          have b6:"deriveExp env  e2=Some( boolType)"
            using b2 b5 by auto
          have b7:"getValueType (expEval e1 s)= boolType"
            using   b1 b5 boolTypeSafe by blast 
          have b8:"\<exists>b. (expEval e1 s)= boolV b" 
            apply(cut_tac b7,case_tac "(expEval e1 s)", auto)done
          have b9:"getValueType (expEval e2 s)= boolType"
            using   b1 b6 boolTypeSafe by blast 
          have b10:"\<exists>b. (expEval e2 s)= boolV b" 
            apply(cut_tac b9,case_tac "(expEval e2 s)", auto)done
          have b11:"absTransfConst M (expEval e1 s) =  expEval (absTransfExp env M e1) (abs1 M s) "
            using eqn(1) b1 b5 by fastforce 
          have b12:"absTransfConst M (expEval e2 s) =  expEval (absTransfExp env M e2) (abs1 M s) "
            using eqn(2) b1 b5 c1 by fastforce 
          have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
                formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
            using eqn b1 b10 b5 b8 c1 by force    
        }
          moreover
        {assume b5:"deriveExp env  e1=Some( dataType) \<and>(safeExp env  M e1 \<and> safeExp  env M e2)"
          have b6:"deriveExp env  e2=Some( dataType)"
            using b2 b5 by auto
          have b7:"getValueType (expEval e1 s)= dataType"
            using   b1 b5 dataTypeSafe by blast 
          have b8:"\<exists>b. (expEval e1 s)= data b" 
            apply(cut_tac b7,case_tac "(expEval e1 s)", auto)done
          have b9:"getValueType (expEval e2 s)= dataType"
            using   b1 b6 dataTypeSafe by blast 
          have b10:"\<exists>b. (expEval e2 s)= data b" 
            apply(cut_tac b9,case_tac "(expEval e2 s)", auto)done
          have b11:"absTransfConst M (expEval e1 s) =  expEval (absTransfExp env M e1) (abs1 M s) "
            using eqn(1) b1 b5 by fastforce 
          have b12:"absTransfConst M (expEval e2 s) =  expEval (absTransfExp env M e2) (abs1 M s) "
            using eqn(2) b1 b5 c1 by fastforce 
          have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
                formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
            using eqn b1 b10 b5 b8 c1 by force    
        }
        ultimately  have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
          formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
          by blast
      }
      ultimately  show "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm \<and>
        formEval (e1 =\<^sub>f e2) s = formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
        by (metis b3 safeForm.simps(1)) 
    qed
  qed
qed (auto)


lemma DsafeTransf: assumes "env dontCareVar =anyType"
  shows "( 
     DsafeExp env  e \<longrightarrow> 
     wellDerivedExp e env \<and>
      deriveExp env e \<noteq> None\<and>
     DabsTransfExp env   e=e) \<and>
    ( 
     DsafeForm env   f \<longrightarrow>
        deriveForm env f \<and> DabsTransfForm env   f =f )"
  (is "(?antE1 e \<longrightarrow>?consE e ) \<and> (?antF1 f \<longrightarrow>?consF f )")
proof (induction rule: expType_formula.induct[where expType=e and formula=f])
  case (IVar x)
  then show ?case 
   apply (cases x) using assms apply auto
    using deriveExp.simps(2) typeType.distinct(5) wellDerivedExp_def apply presburger
    using deriveExp.simps(2) typeType.distinct(15) wellDerivedExp_def apply presburger
    using deriveExp.simps(2) typeType.distinct(11) wellDerivedExp_def apply presburger
    using deriveExp.simps(2) typeType.distinct(5) wellDerivedExp_def apply presburger 
    using deriveExp.simps(2) typeType.distinct(15) wellDerivedExp_def apply presburger
    using deriveExp.simps(2) typeType.distinct(11) wellDerivedExp_def by presburger  
next
  case (Const x)
  then show ?case 
    apply(case_tac x)   apply auto 
    apply (simp add: wellDerivedExp_def)   
    apply (simp add: wellDerivedExp_def)  
    apply (simp add: wellDerivedExp_def)   apply (simp add: wellDerivedExp_def) done
next
  case (iteForm x1 x2 x3)
  show ?case  
  proof(rule impI)+
    assume  
    a2:"DsafeExp env (iteForm x1 x2 x3)"
    have a3:"DsafeExp env x2 & DsafeExp env x3 & DsafeForm env x1 \<and>
    deriveExp env x2=deriveExp env x3 "
      using a2 by auto
    have a4:"?consE x2"
      using  a3 iteForm.IH(2) by fastforce
    have a6:"?consE x3"
      using a3 iteForm.IH(3) by fastforce 
    have a5:"?consF x1"
      using a3 iteForm.IH(1) by fastforce

    have "deriveExp env x2= Some boolType \<or> deriveExp env x2= Some enumType \<or> 
      deriveExp env x2= Some indexType \<or> deriveExp env x2= Some dataType"
      using a4 wellDerivedExp_def by blast

    moreover
    {assume b1:"deriveExp env x2= Some indexType"
      have b2:"deriveExp env x3= Some indexType"
        using a3 b1 by presburger
      have b3:"deriveExp env (iteForm x1 x2 x3) =Some indexType"
        by (simp add: a5 b1 b2)
        
      have " ?consE (iteForm x1 x2 x3)"
        using a2 a3 a4 a5 a6 b1 b2 b3 apply auto
       using deriveExp.simps(3) wellDerivedExp_def by presburger 
   }

    {assume b1:"deriveExp env x2= Some enumType"
      have b2:"deriveExp env x3= Some enumType"
        using a3 b1 by presburger
      have b3:"deriveExp env (iteForm x1 x2 x3) =Some enumType"
        by (simp add: a5 b1 b2)
        
      have " ?consE (iteForm x1 x2 x3)"
        using  a2 a3 a4 a5 a6 b1 b2 b3 apply auto
       using deriveExp.simps(3) wellDerivedExp_def by presburger 
   }

  {assume b1:"deriveExp env x2= Some dataType"
      have b2:"deriveExp env x3= Some dataType"
        using a3 b1 by presburger
      have b3:"deriveExp env (iteForm x1 x2 x3) =Some dataType"
        by (simp add: a5 b1 b2)
        
      have "?consE (iteForm x1 x2 x3)"
        using  a2 a3 a4 a5 a6 b1 b2 b3 apply auto
       using deriveExp.simps(3) wellDerivedExp_def by presburger 
   }
   ultimately show "?consE (iteForm x1 x2 x3)"
     using a3 a4 a5 a6 wellDerivedExp_def by auto
 qed
next
  case dontCareExp
  then show ?case by auto
next
  case (eqn e1 e2)
  show ?case  
  proof (rule impI)+
    assume  
      b3:"DsafeForm env  (e1 =\<^sub>f e2) "  
    show " ?consF (e1 =\<^sub>f e2)"
    proof -
      
      (*have c10:" DsafeExp env  e1 \<and> DsafeExp env  e2"
        using DsafeForm.simps(1) b3 by blast*)

      have c1:"(deriveExp  env e1 =deriveExp  env e2)"
        using DsafeForm.simps(1) b3 by presburger 

      have c2:" 
    wellDerivedExp e1 env \<and> 
    deriveExp env e1 \<noteq> None  "
        by (metis DsafeForm.simps(1) b3 eqn.IH(1) option.discI wellDerivedExp_def)
       
      
      have "(deriveExp env e1 = Some indexType \<or> 
            deriveExp env e1 = Some enumType \<or>
            deriveExp env e1 = Some boolType  \<or>deriveExp env e1 = Some dataType )"
        using  b3 c1  c2 assms by(unfold wellDerivedExp_def, auto ) 
      moreover
      {assume b4:"deriveExp env  e1=Some(indexType) "
        have b5: "deriveExp env  e2=Some(indexType)"
          by(cut_tac c1 b4,auto) 
        
        have "?consF (e1 =\<^sub>f e2)"
          using b3 b4 eqn.IH(1) eqn.IH(2) by force 
      } 
      
      moreover
      {assume b4:"deriveExp env  e1=Some(boolType) "
        have b5: "deriveExp env  e2=Some(boolType)"
          by(cut_tac c1 b4,auto)
         
        
        have "?consF (e1 =\<^sub>f e2)"
          using b3 b4 eqn.IH(1) eqn.IH(2) by auto 
      } 
      moreover 
        {assume b5:"deriveExp env  e1=Some( enumType)"
          have b6:"deriveExp env  e2=Some( enumType)"
            using c1 b5 by auto
           
          have "?consF (e1 =\<^sub>f e2)"
            using b3 b5 eqn.IH(1) eqn.IH(2) by force  
        }  
       moreover 
        {assume b5:"deriveExp env  e1=Some( dataType)"
          have b6:"deriveExp env  e2=Some( dataType)"
            using c1 b5 by auto
          have b7:"e1=Const (data 0) \<and> (\<exists>v. e2=IVar v) |(\<exists>v. e1=IVar v) \<and> e2=Const (data 0) "
            using b3 b5 by auto
         have "?consF (e1 =\<^sub>f e2)" thm disjE
            apply(cut_tac b7,erule disjE)
           using assms c1 apply force
           using assms c1 by force  
           }  
        ultimately  show "?consF  (e1 =\<^sub>f e2)"
          by blast 
        qed       
      qed

next
  case (andForm x1 x2)
  then show ?case  by auto
next
  case (neg x)
  then show ?case  by auto
next
  case (orForm x1 x2)
  then show ?case  by auto
next
  case (implyForm x1 x2)
  then show ?case  by auto
next
  case (forallForm pf N)     
  show ?case      
  proof(rule impI)+
    let ?f="forallForm pf N"
    assume   b2:"?antF1 ?f"
    
    show "?consF ?f "
    proof -
      have c0:"(\<forall>i\<le>N. DsafeForm env (pf i))"
        using DsafeForm.simps(6) b2 by blast
      have c0a:"\<forall>i\<le>N. ?consF (pf i) "
        using  c0 forallForm.IH by blast 
      have c0b:" deriveForm env (?f)"
        by (simp add: c0a)  

      have c2:"(DabsTransfForm env  (forallForm pf N)) = forallForm pf  N"
        by (meson DabsTransfForm.simps(8) b2) 

      have c2a:"\<forall>i\<le>N. DabsTransfForm env (pf i) = (pf i)"
        using c0a by blast
        
       
    show "?consF ?f "
      using c0b c2 by blast  
  qed   
  qed 
next
case (existForm x1 x2)
  then show ?case by auto
next
  case (forallFormExcl x1 x2 x3)
  then show ?case  by auto
next
  case chaos
  then show ?case  by auto
next
  case dontCareForm
  then show ?case  by auto
qed



lemma DsafeEval1: assumes "env dontCareVar =anyType"
  shows "(fitEnv s env \<longrightarrow>
     DsafeExp env  e \<longrightarrow> 
     wellDerivedExp e env \<and>
      deriveExp env e \<noteq> None\<and>
     DabsTransfExp env   e=e \<and>
     DabsTransfConst  (expEval e s) = expEval (DabsTransfExp env   e) (Dabs1   s)) \<and>
    (fitEnv s env \<longrightarrow> 
     DsafeForm env   f \<longrightarrow>
        deriveForm env f \<and> DabsTransfForm env   f =f \<and>
     formEval f s = formEval (DabsTransfForm env   f) (Dabs1  s))"
  (is "(?antE1 e \<longrightarrow>?antE2 e\<longrightarrow> ?consE e ) \<and> (?antF1 f \<longrightarrow>?antF2 f  \<longrightarrow>?consF f )")
proof (induction rule: expType_formula.induct[where expType=e and formula=f])
  case (IVar x)
  then show ?case 
   apply (cases x) using assms apply auto
    using deriveExp.simps(2) typeType.distinct(5) wellDerivedExp_def apply presburger
    using deriveExp.simps(2) typeType.distinct(15) wellDerivedExp_def apply presburger
    using deriveExp.simps(2) typeType.distinct(11) wellDerivedExp_def apply presburger
    using deriveExp.simps(2) typeType.distinct(5) wellDerivedExp_def apply presburger 
    using deriveExp.simps(2) typeType.distinct(15) wellDerivedExp_def apply presburger
    using deriveExp.simps(2) typeType.distinct(11) wellDerivedExp_def by presburger  
next
  case (Const x)
  then show ?case 
    apply(case_tac x)   apply auto 
    apply (simp add: wellDerivedExp_def)   
    apply (simp add: wellDerivedExp_def)  
    apply (simp add: wellDerivedExp_def)   apply (simp add: wellDerivedExp_def) done
next
  case (iteForm x1 x2 x3)
  show ?case  
  proof(rule impI)+
    assume a1:"fitEnv s env " and
    a2:"DsafeExp env (iteForm x1 x2 x3)"
    have a3:"DsafeExp env x2 & DsafeExp env x3 & DsafeForm env x1 \<and>
    deriveExp env x2=deriveExp env x3 "
      using a2 by auto
    have a4:"?consE x2"
      using a1 a3 iteForm.IH(2) by fastforce
    have a6:"?consE x3"
      using a1 a3 iteForm.IH(3) by fastforce 
    have a5:"?consF x1"
      using a1 a3 iteForm.IH(1) by fastforce

    have "deriveExp env x2= Some boolType \<or> deriveExp env x2= Some enumType \<or> 
      deriveExp env x2= Some indexType \<or> deriveExp env x2= Some dataType"
      using a4 wellDerivedExp_def by blast

    moreover
    {assume b1:"deriveExp env x2= Some indexType"
      have b2:"deriveExp env x3= Some indexType"
        using a3 b1 by presburger
      have b3:"deriveExp env (iteForm x1 x2 x3) =Some indexType"
        by (simp add: a5 b1 b2)
        
      have " ?consE (iteForm x1 x2 x3)"
        using a1 a2 a3 a4 a5 a6 b1 b2 b3 apply auto
       using deriveExp.simps(3) wellDerivedExp_def apply presburger
       using b3 wellDerivedExp_def by blast
   }

    {assume b1:"deriveExp env x2= Some enumType"
      have b2:"deriveExp env x3= Some enumType"
        using a3 b1 by presburger
      have b3:"deriveExp env (iteForm x1 x2 x3) =Some enumType"
        by (simp add: a5 b1 b2)
        
      have " ?consE (iteForm x1 x2 x3)"
        using a1 a2 a3 a4 a5 a6 b1 b2 b3 apply auto
       using deriveExp.simps(3) wellDerivedExp_def apply presburger
       using b3 wellDerivedExp_def by blast
   }

  {assume b1:"deriveExp env x2= Some dataType"
      have b2:"deriveExp env x3= Some dataType"
        using a3 b1 by presburger
      have b3:"deriveExp env (iteForm x1 x2 x3) =Some dataType"
        by (simp add: a5 b1 b2)
        
      have "?consE (iteForm x1 x2 x3)"
        using a1 a2 a3 a4 a5 a6 b1 b2 b3 apply auto
       using deriveExp.simps(3) wellDerivedExp_def apply presburger
       using b3 wellDerivedExp_def by blast
   }
   ultimately show "?consE (iteForm x1 x2 x3)"
     using a3 a4 a5 a6 wellDerivedExp_def by auto
 qed
next
  case dontCareExp
  then show ?case by auto
next
  case (eqn e1 e2)
  show ?case  
  proof (rule impI)+
    assume b1:"fitEnv s env"   and
      b3:"DsafeForm env  (e1 =\<^sub>f e2) "  
    show " ?consF (e1 =\<^sub>f e2)"
    proof -
      
      (*have c10:" DsafeExp env  e1 \<and> DsafeExp env  e2"
        using DsafeForm.simps(1) b3 by blast*)

      have c1:"(deriveExp  env e1 =deriveExp  env e2)"
        using DsafeForm.simps(1) b3 by presburger 

     (* have c2:" 
    wellDerivedExp e1 env \<and> 
    deriveExp env e1 \<noteq> None \<and>
    DabsTransfConst (expEval e1 s) = expEval (DabsTransfExp env e1) (Dabs1 s)"
        using b1 c10 eqn.IH(1) by fastforce*)
      
      have "(deriveExp env e1 = Some indexType \<or> 
            deriveExp env e1 = Some enumType \<or>
            deriveExp env e1 = Some boolType  \<or>deriveExp env e1 = Some dataType  )"
        using DsafeForm.simps(1) b1 b3 eqn.IH(1) wellDerivedExp_def by blast 
      moreover
      {assume b4:"deriveExp env  e1=Some(indexType) "
        have b5: "deriveExp env  e2=Some(indexType)"
          by(cut_tac c1 b4,auto)
        have b6: "getValueType (expEval e1 s) = indexType"
          using b4 b1 indexTypeSafe by blast
        have b7: "getValueType (expEval e2 s) = indexType"
          using b5 b1 indexTypeSafe by blast
        obtain n1 where b8: "expEval e1 s = index n1"
          using b6 by (cases "expEval e1 s", auto)
        obtain n2 where b9: "expEval e2 s = index n2"
          using b7 by (cases "expEval e2 s", auto)
        
        have "?consF (e1 =\<^sub>f e2)"
          using b1 b3 b4 b8 b9 eqn.IH(1) eqn.IH(2) by force 
          
      } 
      
      moreover
      {assume b4:"deriveExp env  e1=Some(boolType) "
        have b5: "deriveExp env  e2=Some(boolType)"
          by(cut_tac c1 b4,auto)
        have b6: "getValueType (expEval e1 s) = boolType"
          using b4 b1 boolTypeSafe by blast
        have b7: "getValueType (expEval e2 s) = boolType"
          using b5 b1 boolTypeSafe by blast
        obtain n1 where b8: "expEval e1 s = boolV n1"
          using b6 by (cases "expEval e1 s", auto)
        obtain n2 where b9: "expEval e2 s = boolV  n2"
          using b7 by (cases "expEval e2 s", auto)
        
        have "?consF (e1 =\<^sub>f e2)"
          by (metis DabsTransfConst.simps(3) DsafeForm.simps(1) DsafeTransf assms b1 b3 b4 b8 b9 eqn.IH(1) eqn.IH(2) evalEqn option.inject typeType.distinct(17))
          
          
      } 
      moreover 
        {assume b5:"deriveExp env  e1=Some( enumType)"
          have b6:"deriveExp env  e2=Some( enumType)"
            using c1 b5 by auto
          have b7:"getValueType (expEval e1 s)= enumType"
            using   b1 b5 enumTypeSafe by blast 
          have b8:"\<exists>nt nv. (expEval e1 s)= enum nt nv" 
            apply(cut_tac b7,case_tac "(expEval e1 s)", auto)done
          have b9:"getValueType (expEval e2 s)= enumType"
            using   b1 b6 enumTypeSafe by blast 
          have b10:"\<exists>nt nv. (expEval e2 s)= enum nt nv" 
            apply(cut_tac b9,case_tac "(expEval e2 s)", auto)done
          have b11:"DabsTransfConst  (expEval e1 s) =  expEval (DabsTransfExp env  e1) (Dabs1  s) "
            using b1 b3 b5 eqn.IH(1) by fastforce
            
          have b12:"DabsTransfConst  (expEval e2 s) =  expEval (DabsTransfExp env  e2) (Dabs1  s) "
            using b1 b3 b5 eqn.IH(2) by force
            
          have "?consF (e1 =\<^sub>f e2)"
            using DsafeTransf assms b10 b11 b12 b3 b5 b8 by force
             
        }  

       moreover 
        {assume b5:"deriveExp env  e1=Some( dataType)"
          have b6:"deriveExp env  e2=Some( dataType)"
            using c1 b5 by auto
          have b7:"getValueType (expEval e1 s)= dataType"
            using   b1 b5 dataTypeSafe by blast 
          have b8:"\<exists>d. (expEval e1 s)=data d " 
            apply(cut_tac b7,case_tac "(expEval e1 s)", auto)done
          have b9:"getValueType (expEval e2 s)= dataType"
            using   b1 b6 dataTypeSafe by blast 
          have b10:"\<exists>d'. (expEval e2 s)= data d'" 
            apply(cut_tac b9,case_tac "(expEval e2 s)", auto)done
          have b11:"DabsTransfConst  (expEval e1 s) =  expEval (DabsTransfExp env  e1) (Dabs1  s) "
            by (metis Dabs1.elims DabsTransfExp.simps(1) DabsTransfExp.simps(2) DabsTransfForm.simps(1) DsafeForm.simps(1) DsafeTransf assms b3 b5 evalConst evalVar formula.distinct(17))
             
          have b12:"DabsTransfConst  (expEval e2 s) =  expEval (DabsTransfExp env  e2) (Dabs1  s) "
            by (metis Dabs1.elims DabsTransfExp.simps(1) DabsTransfExp.simps(2) DabsTransfForm.simps(1) DsafeForm.simps(1) DsafeTransf assms b3 b5 evalConst evalVar formula.distinct(17))
            
          have "e1=Const (data 0) \<or> e2 =Const (data 0)"
            using b3 b5 by auto
          moreover
          {assume "e1 =Const (data 0)"
           
          have "?consF (e1 =\<^sub>f e2)"
            by (metis DabsTransfConst.simps(5) DabsTransfForm.simps(1) DsafeTransf \<open>e1 = Const (data 0)\<close> assms b10 b11 b12 b3 evalConst evalEqn formula.distinct(17) scalrValueType.inject(4) zero_neq_one)
          }  
         moreover
          {assume "e2 =Const (data 0)"
           
          have "?consF (e1 =\<^sub>f e2)"
            by (metis DabsTransfConst.simps(5) DabsTransfForm.simps(1) DsafeTransf \<open>e2 = Const (data 0)\<close> assms b11 b12 b3 b8 evalConst evalEqn formula.distinct(17) scalrValueType.inject(4) zero_neq_one)
             
        }  
         ultimately  have "?consF  (e1 =\<^sub>f e2)" by blast
        }  
        ultimately  show "?consF  (e1 =\<^sub>f e2)"
          by blast 
        qed       
      qed

next
  case (andForm x1 x2)
  then show ?case  by auto
next
  case (neg x)
  then show ?case  by auto
next
  case (orForm x1 x2)
  then show ?case  by auto
next
  case (implyForm x1 x2)
  then show ?case  by auto
next
  case (forallForm pf N)     
  show ?case      
  proof(rule impI)+
    let ?f="forallForm pf N"
    assume b1:"(?antF1 ?f)" and b2:"?antF2 ?f"
    
    show "?consF ?f "
    proof -
      have c0:"(\<forall>i\<le>N. DsafeForm env (pf i))"
        using DsafeForm.simps(6) b2 by blast
      have c0a:"\<forall>i\<le>N. ?consF (pf i) "
        using b1 c0 forallForm.IH by blast 
      have c0b:" deriveForm env (?f)"
        by (simp add: c0a)  

      have c2:"(DabsTransfForm env  (forallForm pf N)) = forallForm pf  N"
        by (meson DabsTransfForm.simps(8) b2) 

      have c2a:"\<forall>i\<le>N. DabsTransfForm env (pf i) = (pf i)"
        using c0a by blast
        
      have "formEval (forallForm pf N) s = formEval (   (forallForm pf N)) (Dabs1 s)"
      proof     
        assume d1:"formEval (forallForm pf N) s"
        have c3:"\<forall>i. i\<le>N \<longrightarrow> formEval (pf i) s "
          by(cut_tac d1,auto)
        
        have c5:"\<forall>i. i\<le>N \<longrightarrow> formEval (DabsTransfForm env (pf i)) (Dabs1    s) "
          using c0a c3 by blast

       
          
        show "formEval (  (forallForm pf N)) (Dabs1 s)"
          using c5 c0a  by auto 
      next
        assume d1:"formEval  (forallForm pf N)  (Dabs1 s)"
        have c5:"\<forall>i. i\<le>N \<longrightarrow> formEval (  (pf i)) (Dabs1    s) "
          using d1 by auto

        have c51:"\<forall>i. i\<le>N \<longrightarrow>(DabsTransfForm env (pf i)) =pf i" 
          using c0a by blast
           
 
        have c3:"\<forall>i. i\<le>N \<longrightarrow> formEval (pf i) s "
          using c0a c5 by presburger
           
        have c6:"formEval (forallForm pf N) ( s)"
          using c3 evalForall by blast
      show " formEval (forallForm pf N) s"
        using c2 c6 by presburger 
    qed
    show "?consF ?f "
      using \<open>formEval (forallForm pf N) s = formEval (forallForm pf N) (Dabs1 s)\<close> c0b c2 by presburger 
  qed   
  qed 
next
case (existForm x1 x2)
  then show ?case by auto
next
  case (forallFormExcl x1 x2 x3)
  then show ?case  by auto
next
  case chaos
  then show ?case  by auto
next
  case dontCareForm
  then show ?case  by auto
qed

(*lemma  DabsBoundExpForm:
  assumes "\<forall>i. dboundExp i (pe i) \<and>  absTransfExp env M (pe i)\<noteq>dontCareExp"  
  shows "(dboundExp i e \<longrightarrow> deriveExp env  e\<noteq>None  \<longrightarrow> absTransfExp env M e\<noteq>dontCareExp\<longrightarrow> (pe. pe i=  absTransfExp env M  e))   &
 ( dboundForm i f \<longrightarrow> deriveForm env f \<longrightarrow>  
           absTransfForm env M f \<noteq> dontCareForm \<longrightarrow> absTransfForm env M f = absTransfForm env M f )" 
    (is "(?ante1 e \<longrightarrow> ?ante2 e \<longrightarrow>?ante3 e \<longrightarrow>?Pe e) &( ?antf1 f \<longrightarrow> ?antf2 f \<longrightarrow>?antf3 f \<longrightarrow>?Pf f)")*)

lemma  absBoundExpForm:
  assumes "i \<le> M"
  shows "(boundExp i e \<longrightarrow> deriveExp env e\<noteq>None  \<longrightarrow>safeExp env M e \<and> absTransfExp env M e\<noteq>dontCareExp)   &
 ( boundForm i f \<longrightarrow> deriveForm env f \<longrightarrow>  safeForm env M f \<and>
           absTransfForm env M f \<noteq> dontCareForm)" 
    (is "(?ante1 e \<longrightarrow> ?ante2 e \<longrightarrow>?Pe e) &( ?antf1 f \<longrightarrow> ?antf2 f \<longrightarrow>?Pf f)")

proof (induction rule: expType_formula.induct[where expType=e and formula=f])   
  fix x
  let ?e="(IVar x)"
  show "?ante1 ?e \<longrightarrow> ?ante2 ?e \<longrightarrow>?Pe ?e"
    using boundExp.simps(2) by blast
next
  fix c
  let ?e="(Const c)"
  show "?ante1 ?e \<longrightarrow> ?ante2 ?e \<longrightarrow>?Pe ?e"
    using assms apply(cases c) by auto 

next 
  fix b e1 e2
  let ?e="iteForm b e1 e2"
  show "?ante1 ?e \<longrightarrow> ?ante2 ?e \<longrightarrow>?Pe ?e"
    by simp

next
  let ?e=dontCareExp
  show "?ante1 ?e \<longrightarrow> ?ante2 ?e \<longrightarrow>?Pe ?e"
    by simp
next
  fix e1 e2
  let ?f="eqn e1 e2"
  assume "?ante1 e1 \<longrightarrow> ?ante2 e1 \<longrightarrow>?Pe e1"  "?ante1 e2 \<longrightarrow> ?ante2 e2 \<longrightarrow>?Pe e2" 
  show "?antf1 ?f \<longrightarrow> ?antf2 ?f \<longrightarrow>?Pf ?f"
  proof(rule impI)+
    assume a1:"boundForm i (e1 =\<^sub>f e2) " and a2:" deriveForm env (e1 =\<^sub>f e2) " 
    have a3:"(boundVar i e1 \<and> boundExp i e2)"
      using \<open>boundForm i (e1 =\<^sub>f e2)\<close> by auto
    have "\<exists>t. deriveExp env e1= Some(t)"
      using \<open>deriveForm env (e1 =\<^sub>f e2)\<close> deriveForm.simps(1) by blast
    then obtain t where "  deriveExp env e1= Some(t)" 
      by blast

    have " deriveExp env e2= Some(t)"
      using \<open>deriveExp env e1 = Some t\<close> \<open>deriveForm env (e1 =\<^sub>f e2)\<close> by force 

    have "safeExp env M e2"
      by (simp add: \<open>boundExp i e2 \<longrightarrow> deriveExp env e2 \<noteq> None \<longrightarrow> safeExp env M e2 \<and> absTransfExp env M e2 \<noteq> dontCareExp\<close> \<open>deriveExp env e2 = Some t\<close> a3)
    have "\<exists>c d en ev b. e2=Const c \<and> (c= data d \<or> c= boolV b \<or> c=index i \<or> c=enum en ev)"
      using a3
      apply(cases e2)
         apply auto
      apply(case_tac x2)
      by auto
    have "(\<exists>v iv pv. (v=Ident iv | v =Para pv i) & e1= IVar v) |
          (EX c b . (c=index i | c =boolV b) & e1 =Const c)"
      using a3 apply(cases e1) apply  simp
      apply (smt (z3) varType.exhaust varType.simps(10) varType.simps(11))
      apply(case_tac x2)
      apply auto[1]
      apply force
      apply force
      apply simp
        apply simp
      by auto
    moreover 
    {assume b0:"(\<exists>v iv pv. (v=Ident iv | v =Para pv i) & e1= IVar v) "
       obtain v and iv and pv where b1: "(v=Ident iv | v =Para pv i) & e1= IVar v "
         using b0 by blast 
       have "safeVar   v i"
         using b1 by fastforce
        
      have "safeForm env M (e1 =\<^sub>f e2)"   
      proof(case_tac t)
        assume "t = enumType"
         show ?thesis
           using b1
           by (metis \<open>deriveExp env e1 = Some t\<close> \<open>safeExp env M e2\<close> \<open>t = enumType\<close> a2 assms deriveExp.simps(2) deriveForm.simps(1) option.inject safeExp.simps(2) safeForm.simps(1) safeVar.simps(1) safeVar.simps(2)) 
        next
          assume "t = indexType" 
         show ?thesis
           using b1
           using \<open>\<exists>c d en ev b. e2 = Const c \<and> (c = data d \<or> c = boolV b \<or> c = index i \<or> c = enum en ev)\<close> \<open>deriveExp env e1 = Some t\<close> \<open>deriveExp env e2 = Some t\<close> \<open>safeExp env M e2\<close> \<open>t = indexType\<close> typeType.distinct(9) by force 
       next
           assume "t = boolType" 
         show ?thesis
           using b1
           by (metis \<open>deriveExp env e1 = Some t\<close> \<open>safeExp env M e2\<close> \<open>t = boolType\<close> assms deriveExp.simps(2) option.inject option.simps(3) safeExp.simps(2) safeForm.simps(1) safeVar.simps(1) safeVar.simps(2)) 
       next
         assume  "t = anyType" 
         show ?thesis
           by (metis \<open>deriveExp env e1 = Some t\<close> \<open>t = anyType\<close> b1 deriveExp.simps(2) option.distinct(1) option.inject)
       next
         assume "t = dataType" 
         show ?thesis
           by (metis \<open>deriveExp env e1 = Some t\<close> \<open>safeExp env M e2\<close> \<open>t = dataType\<close> a2 assms b1 deriveExp.simps(2) deriveForm.simps(1) option.sel safeExp.simps(2) safeForm.simps(1) safeVar.simps(1) safeVar.simps(2))
            
       qed
     }
     moreover
     {assume b0:"(EX c b . (c=index i | c =boolV b) & e1 =Const c)"
       obtain c and b where b1:"(c=index i | c =boolV b) & e1 =Const c"
         using b0 by blast
       have "safeForm env M (e1 =\<^sub>f e2)"
       proof(case_tac t)
        assume "t = enumType"
         show ?thesis
           using b1
           using \<open>deriveExp env e1 = Some t\<close> \<open>t = enumType\<close> by fastforce
         next
          assume "t = indexType" 
         show ?thesis
           using b1
           using \<open>\<exists>c d en ev b. e2 = Const c \<and> (c = data d \<or> c = boolV b \<or> c = index i \<or> c = enum en ev)\<close> \<open>deriveExp env e1 = Some t\<close> \<open>deriveExp env e2 = Some t\<close> \<open>safeExp env M e2\<close> \<open>t = indexType\<close> typeType.distinct(9) by force 
       next
           assume "t = boolType" 
         show ?thesis
           using b1
           using \<open>deriveExp env e1 = Some t\<close> \<open>safeExp env M e2\<close> \<open>t = boolType\<close> by auto 
         
       next
         assume  "t = anyType" 
         show ?thesis
           using \<open>deriveExp env e1 = Some t\<close> \<open>t = anyType\<close> calculation(1) calculation(2) by fastforce
            
         next
         assume "t = dataType" 
         show ?thesis
           using \<open>deriveExp env e1 = Some t\<close> \<open>t = dataType\<close> b1 by fastforce
               
       qed
     }
     ultimately 
     have "safeForm env M (e1 =\<^sub>f e2)"
       by blast

     have "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm"
       using \<open>boundExp i e2 \<longrightarrow> deriveExp env e2 \<noteq> None \<longrightarrow> safeExp env M e2 \<and> absTransfExp env M e2 \<noteq> dontCareExp\<close> \<open>deriveExp env e2 = Some t\<close> a3 absBoundVar assms by auto
     show "?Pf ?f"
       using \<open>absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm\<close> \<open>safeForm env M (e1 =\<^sub>f e2)\<close> by blast
   qed
 qed(auto)
      
lemma absTransfFormSim:
  "(fitEnv s env \<longrightarrow>
     deriveExp env e \<noteq> None \<longrightarrow>
     absTransfExp env M e \<noteq> dontCareExp \<longrightarrow>
     expEval (absTransfExp env M e) (abs1 M s) = absTransfConst M (expEval e s)) \<and>
    (fitEnv s env \<longrightarrow>
     deriveForm env f \<longrightarrow>
     absTransfForm env M f \<noteq> dontCareForm \<longrightarrow>
     formEval f s \<longrightarrow> formEval (absTransfForm env M f) (abs1 M s))"
 (is "(?antE1 e \<longrightarrow> ?consE e ) \<and> (?antF1 f   \<longrightarrow>?consF f )")
proof (induction rule: expType_formula.induct[where expType=e and formula=f])
  case (IVar v)
  show ?case
    apply (cases v) by auto
next
  case (iteForm b e1 e2)
  show ?case
  proof(rule impI)+
    assume b1:"fitEnv s env" and
      b2:"deriveExp env (iteForm b e1 e2) \<noteq> None " and
      b3:"absTransfExp env M (iteForm b e1 e2) \<noteq> dontCareExp "
    show "expEval (absTransfExp env M (iteForm b e1 e2)) (abs1 M s) = 
    absTransfConst M (expEval (iteForm b e1 e2) s)"
    proof -
      from b2 have b4:" (deriveExp  env e1 =deriveExp  env e2)& (deriveExp  env e1\<noteq>None)\<and>
      deriveForm  env b=True "
        by (meson deriveExp.simps(3))
      from b3 have b5:"(absTransfForm env M b) \<noteq> dontCareForm  \<and>
      (absTransfExp env M e1)\<noteq> dontCareExp \<and> 
      (absTransfExp env M e2) \<noteq>dontCareExp\<and>
        safeForm env M b"
        by (meson absTransfExp.simps(3)) 
      have b50:"(absTransfForm env M b)\<noteq>dontCareForm\<and>
      (formEval b s \<longleftrightarrow> formEval (absTransfForm env M b)  (abs1 M s))"
        by (simp add: b1 b4 b5 safeEval1) 
      have "formEval b s \<or> \<not>formEval b s"  by blast
      moreover
      {assume b6:"formEval b s"
        have "expEval (absTransfExp env M (iteForm b e1 e2)) (abs1 M s) = 
        absTransfConst M (expEval (iteForm b e1 e2) s)"
          apply(cut_tac b4 b5 b6, auto)
          using b1 b4 iteForm.IH(2) apply blast
          using b1 iteForm.IH(1) by blast
      }
      {assume b6:"\<not>formEval b s"
        have b7:"(deriveExp  env e2\<noteq>None)"
          by (metis b4)
        have b8:"\<not>formEval (absTransfForm env M b) (abs1 M s)"
          using b50 b6 by force 
        have "expEval (absTransfExp env M (iteForm b e1 e2)) (abs1 M s) = 
          absTransfConst M (expEval (iteForm b e1 e2) s)"
          apply(cut_tac b4 b5 b6 b7 b8, auto)
          using b1 iteForm.IH(3) by blast
      }
      ultimately show "expEval (absTransfExp env M (iteForm b e1 e2)) (abs1 M s) = 
        absTransfConst M (expEval (iteForm b e1 e2) s)"
        using \<open>formEval b s \<Longrightarrow> expEval (absTransfExp env M (iteForm b e1 e2)) (abs1 M s) = absTransfConst M (expEval (iteForm b e1 e2) s)\<close> by linarith
    qed 
  qed
next
  case (eqn e1 e2)
  have "formEval (e1 =\<^sub>f e2) s \<longrightarrow> formEval (absTransfForm env M (e1 =\<^sub>f e2)) (abs1 M s)"
    if "absTransfForm env M (e1 =\<^sub>f e2) \<noteq> dontCareForm" and
      "fitEnv s env" and "deriveForm env (e1 =\<^sub>f e2)"
  proof -
    have 1: "absTransfExp env M e1 \<noteq> dontCareExp" "absTransfExp env M e2 \<noteq> dontCareExp"
      using that by auto
    have 2: "absTransfForm env M (e1 =\<^sub>f e2) = eqn (absTransfExp env M e1) (absTransfExp env M e2)"
      using 1 by auto
    have 3: "expEval (absTransfExp env M e1) (abs1 M s) = absTransfConst M (expEval e1 s)"
      "expEval (absTransfExp env M e2) (abs1 M s) = absTransfConst M (expEval e2 s)"
      using eqn 2
      using "1"(1) deriveForm.simps(1) that(2) that(3) apply blast
      using "1"(2) eqn.IH(2) that(2) that(3) by auto   
    show ?thesis
      unfolding 2 3 formEval.simps by auto
  qed
  then show ?case 
    apply(case_tac "safeForm env M (e1 =\<^sub>f e2)")
     apply blast
    using eqn.IH(1) eqn.IH(2) by auto 
next
  case (neg f)
  show ?case
    by (auto simp add: safeEval1) 
next
  case (implyForm x1 x2)
  show ?case 
  proof(rule impI)+ 
    assume b1:"fitEnv s env"
      and b2:"deriveForm env (x1 \<longrightarrow>\<^sub>f x2)"
      and b3:"absTransfForm env M (x1 \<longrightarrow>\<^sub>f x2) \<noteq> dontCareForm"
      and b4: "formEval (x1 \<longrightarrow>\<^sub>f x2) s"
    have b5:"safeForm env M x1"
      using absTransfForm.simps(5) b3 unfolding Let_def by presburger
    have b6:"deriveForm env x1 \<and> deriveForm env x2 "
      by (meson b2 deriveForm.simps(5))
    have b7:"absTransfForm env M x1 \<noteq> dontCareForm \<and> absTransfForm env M x2 \<noteq> dontCareForm "
      using absTransfForm.simps(5) b3 by (smt (verit))
    have b8:"absTransfForm env M x1 \<noteq> dontCareForm \<and>
      formEval x1 s = formEval (absTransfForm env M x1) (abs1 M s)"
      using b1 b5 b6 safeEval1 by presburger
    show "formEval (absTransfForm env M (x1 \<longrightarrow>\<^sub>f x2)) (abs1 M s) "
      using b1 b4 b6 b8 implyForm.IH(2) by (auto simp add: Let_def)
  qed  
next
  case (forallForm pf N)
  show ?case  
  proof(rule impI)+
    assume b1:"fitEnv s env" and
      b2:"deriveForm env (forallForm pf N) " and 
      b4:"absTransfForm env M (forallForm pf N) \<noteq> dontCareForm " and
      b5:"formEval (forallForm pf N) s" 
    show "formEval (absTransfForm env M (forallForm pf N)) (abs1 M s) "
    proof -
      have c1:"M\<le>N & (\<forall>j. boundForm j (pf j))"
        using absTransfForm.simps(8) b4 by presburger
      have c2:"(absTransfForm env M (forallForm pf N)) = forallForm pf  M"
        by (simp add: c1)
      have c3:"\<forall>i. i\<le>N \<longrightarrow> formEval (pf i) s "
        by(cut_tac b5,auto)
      have c4:"\<forall>i. i\<le>M \<longrightarrow> formEval (pf i) s "
        apply(cut_tac c1 c3,auto) done
      have c5:"\<forall>i. i\<le>M \<longrightarrow> formEval (pf i) (abs1 M s) "
        using boundEval c1 c4 by blast 
      have c6:"formEval (forallForm pf M) (abs1 M s)"
        using c5 evalForall by blast
      show "formEval (absTransfForm env M (forallForm pf N)) (abs1 M s)"
        using c2 c6 by presburger 
    qed
  qed
next
  case (existForm pf N)
  show ?case
  proof(rule impI)+
    assume b1: "fitEnv s env"
      and b2: "deriveForm env (existForm pf N)" 
      and b4: "absTransfForm env M (existForm pf N) \<noteq> dontCareForm"
      and b5: "formEval (existForm pf N) s" 
    show "formEval (absTransfForm env M (existForm pf N)) (abs1 M s)"
    proof -
       (*if M \<le>N \<and> (\<forall>j. boundForm j (pf j)) \<and>
    (\<forall>j. j>M \<longrightarrow> absTransfForm env M (pf j) \<noteq>dontCareForm \<and>
        absTransfForm env M (pf j) = absTransfForm env M (pf (M +1)) ) 
    
    then (orForm (existForm (pf) (M ) ) (absTransfForm env M (pf (M +1))))
     else 
        (if (\<exists> apf. (\<forall>j. absTransfForm env M (pf j) =apf j)*) 
      let ?P="M \<le>N \<and> (\<forall>j. boundForm j (pf j)) \<and>
      (\<forall>j. j>M \<longrightarrow> absTransfForm env M (pf j) \<noteq>dontCareForm \<and>
        absTransfForm env M (pf j) = absTransfForm env M (pf (M +1)) )" 
      have "?P | \<not>?P" by blast 
      moreover
      {assume c00: "?P"
      have c0:" M \<le>N \<and> (\<forall>j. boundForm j (pf j))"
        by (meson absTransfForm.simps(9) b4 c00)
        

      
      have c2:"(absTransfForm env M (existForm pf N)) =
         orForm (existForm pf  M ) (absTransfForm env M (pf (M+1)))
     "
        by (smt (verit, del_insts) absTransfForm.simps(9) c00)
       (* by (meson absTransfForm.simps(9) c00) *)
        
      have "\<exists>i. i\<le>N \<and> formEval (pf i) s"
        using b5 evalExist by blast 

      then obtain i where c1:"i\<le>N \<and> formEval (pf i) s"
        by blast
        
      have c2a:"deriveForm env (pf i)"
        using b2 c1 deriveForm.simps(10) by blast 

      have c4:"pf i : range pf"
        by blast

     
      have c5:"\<forall>i. i > M \<longrightarrow> (absTransfForm env M (pf i)) = (absTransfForm env M (pf (M +1)))"
        by (meson absTransfForm.simps(9) c00)

      have "i \<le> M \<or> i>M"
        by arith
      moreover
      {assume d1:"i\<le>M"

        have c3:"(absTransfForm env M (pf i)\<noteq> dontCareForm)"
          using absBoundExpForm c0 c2a d1 by blast 
          
         
        
        have d2:"formEval (absTransfForm env M (pf i)) (abs1 M s)"
          using b1 c1 c2a c3 existForm.IH by blast 

        have "formEval (absTransfForm env M (existForm pf N)) (abs1 M s) "
          using c2 apply simp apply(rule disjI1) 
          apply(rule_tac x="i" in exI)
          using boundEval c0 c1 d1 by blast 
      }
      moreover
      {assume d1:"i>M" 
        have c3:"(absTransfForm env M (pf i)\<noteq> dontCareForm)"
          by (metis absTransfForm.simps(9) c00 d1) 
        have "formEval (absTransfForm env M (pf i)) (abs1 M s)"
          using b1 c1 c2a c3 existForm.IH by blast 

        have "formEval (absTransfForm env M (pf (M+1))) (abs1 M s)"
          by (metis \<open>formEval (absTransfForm env M (pf i)) (abs1 M s)\<close> c5 d1) 
        have "formEval (absTransfForm env M (existForm pf N)) (abs1 M s) "
           using c2 apply simp apply(rule disjI2)
           using \<open>formEval (absTransfForm env M (pf (M + 1))) (abs1 M s)\<close> c5 lessI by presburger
          
      }
      ultimately have "formEval (absTransfForm env M (existForm pf N)) (abs1 M s) "
        by fastforce  
    }
    moreover
    {assume c00: "~?P"
      let ?Q=" (\<forall>j. dboundForm j (pf j)  \<and> absTransfForm env M (pf j) ~= dontCareForm )"
      have "?Q |  \<not>?Q" by blast
      moreover
      {assume c01:"?Q"
       (* obtain apf where c02:" (\<forall>j. absTransfForm env M (pf j) =apf j \<and> absTransfForm env M (pf j) ~= dontCareForm)"
          using c01  by blast *)
        have "\<exists>i. i\<le>N \<and> formEval (pf i) s"
        using b5 evalExist by blast

      then obtain i where c1:"i\<le>N \<and> formEval (pf i) s"
        by blast
        
      have c2a:"deriveForm env (pf i)"
        using b2 c1 deriveForm.simps(10) by blast
         

      
        

      have c4:"pf i : range pf"
        by blast

     
     (* have c5:" (absTransfForm env M (pf i)) = apf i \<and> absTransfForm env M (pf i) ~= dontCareForm"
        by (meson absTransfForm.simps(9) c02)*)

     
     have d2:"formEval (absTransfForm env M (pf i)) (abs1 M s)"
       using b1 c01 c1 c2a existForm.IH by blast 

     have d3:"(absTransfForm env M (existForm pf N)) =
          (existForm (\<lambda>j. absTransfForm env M (pf j)) N) 
     "
       using c00 c01  absTransfForm.simps(9)  apply meson done
     have d4:"formEval ( (\<lambda>j. absTransfForm env M (pf j)) i) (abs1 M s)"
       using d2 by fastforce 
     have d5:"formEval  (existForm (\<lambda>j. absTransfForm env M (pf j)) N)  (abs1 M s)"
       using c1 d4 evalExist by blast
     have "formEval  (absTransfForm env M (existForm pf N))  (abs1 M s)"
       using d3 d5 by presburger 
   }
   moreover
    {assume c01:"~?Q"
     have d3:"(absTransfForm env M (existForm pf N)) =
         dontCareForm
     "
       using c00 c01  absTransfForm.simps(9)  by metis 
     have "formEval  (absTransfForm env M (existForm pf N))  (abs1 M s)"
       using b4 d3 by blast   
   }
   ultimately have "formEval (absTransfForm env M (existForm pf N)) (abs1 M s) "
     by fastforce
 }
  ultimately show "formEval (absTransfForm env M (existForm pf N)) (abs1 M s) "
     by fastforce
    qed
  qed
next
  case (forallFormExcl pf i N)
  show ?case
  proof (rule impI)+
    assume b1: "fitEnv s env"
      and b2: "deriveForm env (forallFormExcl pf i N)"
      and b4: "absTransfForm env M (forallFormExcl pf i N) \<noteq> dontCareForm"
      and b5: "formEval (forallFormExcl pf i N) s" 
    show "formEval (absTransfForm env M (forallFormExcl pf i N)) (abs1 M s)"
    proof -
      have c1: "M \<le> N \<and> (\<forall>j. boundForm j (pf j))"
        using absTransfForm.simps(10) b4 by presburger
      have c2: "absTransfForm env M (forallFormExcl pf i N) =
        (if i > M then forallForm pf M else forallFormExcl pf i M)"
        by (simp add: c1)
      have c3: "\<forall>j. j \<le> N \<longrightarrow> j \<noteq> i \<longrightarrow> formEval (pf j) s"
        by (cut_tac b5,auto)
      have c5: "\<forall>j. j \<le> M \<longrightarrow> j \<noteq> i \<longrightarrow> formEval (pf j) (abs1 M s)"
        by (metis boundEval c1 c3 le_trans) 
      have c6: "i > M \<Longrightarrow> formEval (forallForm pf M) (abs1 M s)"
        using c1 c5 by fastforce
      have c7: "i > M \<Longrightarrow> formEval (forallFormExcl pf i M) (abs1 M s) =
                formEval (forallForm pf M) (abs1 M s)"
        using c6 by force
      have c8: "i \<le> M \<Longrightarrow> formEval (forallFormExcl pf i M) (abs1 M s)"
        using c1 c5 by fastforce
      with c2 show "formEval (absTransfForm env M (forallFormExcl pf i N)) (abs1 M s)"
        using c6 c8 by (metis not_le_imp_less) 
    qed
  qed
qed (auto simp add: Let_def)




lemma DabsTransfFormSim:
  assumes "env dontCareVar =anyType"

shows  "(fitEnv s env \<longrightarrow>
     deriveExp env e \<noteq> None \<longrightarrow>
     DabsTransfExp env  e \<noteq> dontCareExp \<longrightarrow>
     expEval (DabsTransfExp env  e) (Dabs1  s) = DabsTransfConst  (expEval e s)) \<and>
    (fitEnv s env \<longrightarrow>
     deriveForm env f \<longrightarrow>
     DabsTransfForm env  f \<noteq> dontCareForm \<longrightarrow>
     formEval f s \<longrightarrow> formEval (DabsTransfForm env  f) (Dabs1  s))"
 (is "(?antE1 e \<longrightarrow> ?consE e ) \<and> (?antF1 f   \<longrightarrow>?consF f )")
proof (induction rule: expType_formula.induct[where expType=e and formula=f])
  case (IVar v)
  show ?case
    apply (cases v) by auto
next
  case (iteForm b e1 e2)
  show ?case
  proof(rule impI)+
    assume b1:"fitEnv s env" and
      b2:"deriveExp env (iteForm b e1 e2) \<noteq> None " and
      b3:"DabsTransfExp env  (iteForm b e1 e2) \<noteq> dontCareExp "
    show "expEval (DabsTransfExp env  (iteForm b e1 e2)) (Dabs1  s) = 
    DabsTransfConst  (expEval (iteForm b e1 e2) s)"
    proof -
      from b2 have b4:" (deriveExp  env e1 =deriveExp  env e2)& (deriveExp  env e1\<noteq>None)\<and>
      deriveForm  env b=True "
        by (meson deriveExp.simps(3))
      have b5:"
      (DabsTransfExp env  e1)\<noteq> dontCareExp \<and> 
      (DabsTransfExp env  e2) \<noteq>dontCareExp\<and>
        DsafeForm env  b"
        by (meson DabsTransfExp.simps(3) b3) 
      have b50:" 
      (formEval b s = formEval (DabsTransfForm env  b)  (Dabs1  s))"
        using DsafeEval1 assms b1 b5 by blast 
        
      have "formEval b s \<or> \<not>formEval b s"  by blast
      moreover
      {assume b6:"formEval b s"
        have "expEval (DabsTransfExp env  (iteForm b e1 e2)) (Dabs1  s) = 
        DabsTransfConst  (expEval (iteForm b e1 e2) s)"
          apply(cut_tac b4 b5 b6, auto)
          using b1 b4 iteForm.IH(2) apply blast
          using b50 by blast 
      }
      {assume b6:"\<not>formEval b s"
        have b7:"(deriveExp  env e2\<noteq>None)"
          by (metis b4)
        have b8:"\<not>formEval (DabsTransfForm env  b) (Dabs1  s)"
          using b50 b6 by force 
        have "expEval (DabsTransfExp env  (iteForm b e1 e2)) (Dabs1  s) = 
          DabsTransfConst  (expEval (iteForm b e1 e2) s)"
          apply(cut_tac b4 b5 b6 b7 b8, auto)
          using b1 iteForm.IH(3) by blast
      }
      ultimately show "expEval (DabsTransfExp env  (iteForm b e1 e2)) (Dabs1  s) = 
        DabsTransfConst  (expEval (iteForm b e1 e2) s)"
        using \<open>formEval b s \<Longrightarrow> expEval (DabsTransfExp env (iteForm b e1 e2)) (Dabs1 s) = DabsTransfConst (expEval (iteForm b e1 e2) s)\<close> by blast
           
      qed 
  qed
next
  case (eqn e1 e2)
  have "formEval (e1 =\<^sub>f e2) s \<longrightarrow> formEval (DabsTransfForm env  (e1 =\<^sub>f e2)) (Dabs1  s)"
    if "DabsTransfForm env  (e1 =\<^sub>f e2) \<noteq> dontCareForm" and
      "fitEnv s env" and "deriveForm env (e1 =\<^sub>f e2)"
  proof -
    have 1: "DabsTransfExp env  e1 \<noteq> dontCareExp" "DabsTransfExp env  e2 \<noteq> dontCareExp"
      using that by auto
    have 2: "DabsTransfForm env  (e1 =\<^sub>f e2) = eqn (DabsTransfExp env  e1) (DabsTransfExp env  e2)"
      by (meson DabsTransfForm.simps(1) that(1))
       
    have 3: "expEval (DabsTransfExp env  e1) (Dabs1  s) = DabsTransfConst  (expEval e1 s)"
      "expEval (DabsTransfExp env  e2) (Dabs1  s) = DabsTransfConst  (expEval e2 s)"
      using eqn 2
      using "1"(1) deriveForm.simps(1) that(2) that(3) apply blast
      using "1"(2) eqn.IH(2) that(2) that(3) by auto   
    show ?thesis
      unfolding 2 3 formEval.simps by auto
  qed
  then show ?case 
    apply(case_tac "DsafeForm env  (e1 =\<^sub>f e2)")
     apply blast
    using eqn.IH(1) eqn.IH(2) by auto 
next
  case (neg f)
  show ?case
    using DabsTransfForm.simps(2) DsafeEval1 assms evalNeg by presburger 
next
  case (implyForm x1 x2)
  show ?case   
  proof(rule impI)+ 
    assume b1:"fitEnv s env"
      and b2:"deriveForm env (x1 \<longrightarrow>\<^sub>f x2)"
      and b3:"DabsTransfForm env  (x1 \<longrightarrow>\<^sub>f x2) \<noteq> dontCareForm"
      and b4: "formEval (x1 \<longrightarrow>\<^sub>f x2) s"
    have b5:"DsafeForm env  x1"
      by (smt (z3) DabsTransfForm.simps(5) b3) 
    have b6:"deriveForm env x1 \<and> deriveForm env x2 "
      by (meson b2 deriveForm.simps(5))
    have b7:"DabsTransfForm env  x1 \<noteq> dontCareForm \<and> DabsTransfForm env  x2 \<noteq> dontCareForm "
      by (smt (z3) DabsTransfForm.simps(5) b3) 
    (*have b8:"DabsTransfForm env  M x1 \<noteq> dontCareForm \<and>
      formEval x1 s = formEval (absTransfForm env M x1) (abs1 M s)"
      using b1 b5 b6 safeEval1 by presburger*)
    show "formEval (DabsTransfForm env  (x1 \<longrightarrow>\<^sub>f x2)) (Dabs1  s) "
      using DsafeEval1 assms b1 b4 b5 b6 b7 implyForm.IH(2) by auto 
  qed  
next
  case (forallForm pf N)
  show ?case  
  proof(rule impI)+
    assume b1:"fitEnv s env" and
      b2:"deriveForm env (forallForm pf N) " and 
      b4:"DabsTransfForm env  (forallForm pf N) \<noteq> dontCareForm " and
      b5:"formEval (forallForm pf N) s" 
    show "formEval (DabsTransfForm env  (forallForm pf N)) (Dabs1  s) "
    proof -
      (*have c1:"M\<le>N & (\<forall>j. boundForm j (pf j))"
        using absTransfForm.simps(8) b4 by presburger
      have c2:"(absTransfForm env M (forallForm pf N)) = forallForm pf  M"
        by (simp add: c1)
      have c3:"\<forall>i. i\<le>N \<longrightarrow> formEval (pf i) s "
        by(cut_tac b5,auto)
      have c4:"\<forall>i. i\<le>M \<longrightarrow> formEval (pf i) s "
        apply(cut_tac c1 c3,auto) done
      have c5:"\<forall>i. i\<le>M \<longrightarrow> formEval (pf i) (abs1 M s) "
        using boundEval c1 c4 by blast 
      have c6:"formEval (forallForm pf M) (abs1 M s)"
        using c5 evalForall by blast*)
      have "DsafeForm env (forallForm pf N) \<or> ~DsafeForm env (forallForm pf N)"
        by (meson DabsTransfForm.simps(8) b4)
      moreover
      {assume "DsafeForm env (forallForm pf N)"
        have  "formEval (DabsTransfForm env  (forallForm pf N)) (Dabs1  s)"
        
          using DsafeEval1 \<open>DsafeForm env (forallForm pf N)\<close> assms b1 b5 by blast 
      }
      moreover
      {assume "\<not>DsafeForm env (forallForm pf N)"
        have "((\<forall>j. boundForm j (pf j)) \<and> (\<exists>pf'. \<forall>j.  DabsTransfForm env (pf j ) = pf' j)) |
              \<not>((\<forall>j. boundForm j (pf j)) \<and> (\<exists>pf'. \<forall>j.  DabsTransfForm env (pf j ) = pf' j))"
          by blast
        moreover
        {assume c1:"((\<forall>j. boundForm j (pf j)) )"
          (*from c1 obtain pf'  where c2:"\<forall>j.  DabsTransfForm env (pf j ) = pf' j"
            by blast*)
          have "(DabsTransfForm env  (forallForm pf N)) =
             forallForm (\<lambda> j.  DabsTransfForm env (pf j )) N"
            using DabsTransfForm.simps(8) \<open>\<not> DsafeForm env (forallForm pf N)\<close> c1 by presburger
             
        have  "formEval (DabsTransfForm env  (forallForm pf N)) (Dabs1  s)"
          using \<open>DabsTransfForm env (forallForm pf N) = (\<forall>\<^sub>fj. DabsTransfForm env (pf j)) N\<close> b1 b2 b5 forallForm by fastforce
          
        }
       moreover
       {assume c1:"\<not>((\<forall>j. boundForm j (pf j)))"
         have "(DabsTransfForm env  (forallForm pf N)) =dontCareForm"
           by (meson DabsTransfForm.simps(8) \<open>\<not> DsafeForm env (forallForm pf N)\<close> c1)
          have  "formEval (DabsTransfForm env  (forallForm pf N)) (Dabs1  s)"
            using \<open>DabsTransfForm env (forallForm pf N) = dontCareForm\<close> by auto
        }
        ultimately have "formEval (DabsTransfForm env  (forallForm pf N)) (Dabs1  s)" by blast
      }  
      ultimately show "formEval (DabsTransfForm env  (forallForm pf N)) (Dabs1  s)" by blast
    

    qed
  qed
next
  case (existForm pf N)
  show ?case  
  proof(rule impI)+
    assume b1: "fitEnv s env"
      and b2: "deriveForm env (existForm pf N)" 
      and b4: "DabsTransfForm env  (existForm pf N) \<noteq> dontCareForm"
      and b5: "formEval (existForm pf N) s" 
    
    have "DsafeForm env (existForm pf N) | \<not> DsafeForm env (existForm pf N)"
      by blast
    moreover
    {assume c1:"DsafeForm env (existForm pf N)"
      
    have c2:"DabsTransfForm env  (existForm pf N) = (existForm pf N)"
      by (meson DabsTransfForm.simps(9) c1 \<open>DsafeForm env (existForm pf N)\<close>) 
    have c3:"\<exists>i. i\<le>N \<and>  formEval (pf i) s"
      using b5 by auto
    then obtain i where  c4:"i\<le>N \<and>  formEval (pf i) s"
      by blast
    have c5:"DsafeForm env (pf i)"
      using DsafeForm.simps(7) c1 c4 by blast
    have "formEval (pf i) (Dabs1  s)"
      by (metis DsafeEval1 assms b1 c4 c5)
      
    have "formEval (DabsTransfForm env  (existForm pf N)) (Dabs1  s)"
      using \<open>formEval (pf i) (Dabs1 s)\<close> c2 c4 by auto 
    }
  moreover
  {assume c1:"\<not>DsafeForm env (existForm pf N)"
    let ?P="  (\<forall>j. j>0 \<longrightarrow>DabsTransfForm env  (pf j) \<noteq>dontCareForm \<and>
        DabsTransfForm env  (pf j) = DabsTransfForm env (pf 1) )"
    have "?P  \<or>\<not>?P" by blast 
      moreover
      {assume c2:"?P"
        have "DabsTransfForm env  (existForm pf N) =
          (if ( (\<forall>j. j>0 \<longrightarrow>(DabsTransfForm env  (pf j) \<noteq>dontCareForm \<and>
        DabsTransfForm env  (pf j) = DabsTransfForm env (pf 1)) ))
         then orForm (DabsTransfForm env ( pf 0)) (DabsTransfForm env ( pf 1))
         else dontCareForm )"
          using DabsTransfForm.simps(9) c1 by presburger
        have "(if ( (\<forall>j. j>0 \<longrightarrow>(DabsTransfForm env  (pf j) \<noteq>dontCareForm \<and>
        DabsTransfForm env  (pf j) = DabsTransfForm env (pf 1)) ))
         then orForm (DabsTransfForm env ( pf 0)) (DabsTransfForm env ( pf 1))
         else dontCareForm ) = orForm (DabsTransfForm env ( pf 0)) (DabsTransfForm env ( pf 1))"
          by (meson \<open>DabsTransfForm env (existForm pf N) = (if  (\<forall>j>0. DabsTransfForm env (pf j) \<noteq> dontCareForm \<and> DabsTransfForm env (pf j) = DabsTransfForm env (pf 1)) then DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1) else dontCareForm)\<close> b4) 
        have  "DabsTransfForm env  (existForm pf N) =  orForm (DabsTransfForm env ( pf 0)) (DabsTransfForm env ( pf 1))"
          using \<open>(if (\<forall>j>0. DabsTransfForm env (pf j) \<noteq> dontCareForm \<and> DabsTransfForm env (pf j) = DabsTransfForm env (pf 1)) then DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1) else dontCareForm) = (DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1))\<close> \<open>DabsTransfForm env (existForm pf N) = (if  (\<forall>j>0. DabsTransfForm env (pf j) \<noteq> dontCareForm \<and> DabsTransfForm env (pf j) = DabsTransfForm env (pf 1)) then DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1) else dontCareForm)\<close> by auto
       
        have "\<exists>i. i\<le>N \<and> formEval (pf i) s"
        using b5 evalExist by blast 

        then obtain i where c1:"i\<le>N \<and> formEval (pf i) s"
           by blast
        
         have c2a:"deriveForm env (pf i)"
           using b2 c1 deriveForm.simps(10) by blast 

         have c4:"pf i : range pf"
           by blast

     
         have c5:"\<forall>i. i > 0 \<longrightarrow> (DabsTransfForm env  (pf i)) = (DabsTransfForm env  (pf (1)))"
           by (metis \<open>(if   (\<forall>j>0. DabsTransfForm env (pf j) \<noteq> dontCareForm \<and> DabsTransfForm env (pf j) = DabsTransfForm env (pf 1)) then DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1) else dontCareForm) = (DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1))\<close> formula.distinct(59))
            
          
         have "i = 0 \<or> i>0" by arith

         moreover
         {assume "i=0"
           have "formEval (DabsTransfForm env (pf i) ) (Dabs1  s)  "
             by (metis b1 c1 c2a c4 evalDontCareForm existForm)
           have "formEval (DabsTransfForm env  (existForm pf N)) (Dabs1  s)"
             using \<open>DabsTransfForm env (existForm pf N) = (DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1))\<close> \<open>formEval (DabsTransfForm env (pf i)) (Dabs1 s)\<close> \<open>i = 0\<close> by fastforce
         }
         moreover
         {assume "i>0"
           have "formEval (DabsTransfForm env (pf i) ) (Dabs1  s)  "
             by (metis b1 c1 c2a evalDontCareForm existForm range_eqI)
           have "formEval (DabsTransfForm env (pf 1) ) (Dabs1  s)  "
             by (metis \<open>0 < i\<close> \<open>formEval (DabsTransfForm env (pf i)) (Dabs1 s)\<close> c5)  
           have "formEval (DabsTransfForm env  (existForm pf N)) (Dabs1  s)"
             using \<open>DabsTransfForm env (existForm pf N) = (DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1))\<close> \<open>formEval (DabsTransfForm env (pf 1)) (Dabs1 s)\<close> by auto  
         }
         ultimately  have "formEval (DabsTransfForm env  (existForm pf N)) (Dabs1  s)"
           by blast
       }
       moreover
       {assume "\<not>?P"
          have "DabsTransfForm env  (existForm pf N) =
          (if ( (\<forall>j. j>0 \<longrightarrow>(DabsTransfForm env  (pf j) \<noteq>dontCareForm \<and>
        DabsTransfForm env  (pf j) = DabsTransfForm env (pf 1)) ))
         then orForm (DabsTransfForm env ( pf 0)) (DabsTransfForm env ( pf 1))
         else dontCareForm )"
          using DabsTransfForm.simps(9) c1 by presburger
        have "(if ((\<forall>j. j>0 \<longrightarrow>(DabsTransfForm env  (pf j) \<noteq>dontCareForm \<and>
        DabsTransfForm env  (pf j) = DabsTransfForm env (pf 1)) ))
         then orForm (DabsTransfForm env ( pf 0)) (DabsTransfForm env ( pf 1))
         else dontCareForm ) =dontCareForm"
          by (metis \<open>\<not> ( (\<forall>j>0. DabsTransfForm env (pf j) \<noteq> dontCareForm \<and> DabsTransfForm env (pf j) = DabsTransfForm env (pf 1)))\<close>)
        have "DabsTransfForm env  (existForm pf N) = dontCareForm"
          using \<open>(if   (\<forall>j>0. DabsTransfForm env (pf j) \<noteq> dontCareForm \<and> DabsTransfForm env (pf j) = DabsTransfForm env (pf 1))
         then DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1) else dontCareForm) = dontCareForm\<close>
            \<open>DabsTransfForm env (existForm pf N) = (if  (\<forall>j>0. DabsTransfForm env (pf j) \<noteq> dontCareForm \<and> DabsTransfForm env (pf j) = DabsTransfForm env (pf 1)) then DabsTransfForm env (pf 0) \<or>\<^sub>f DabsTransfForm env (pf 1) else dontCareForm)\<close> by auto
        have "formEval (DabsTransfForm env  (existForm pf N)) (Dabs1  s)"
          using \<open>DabsTransfForm env (existForm pf N) = dontCareForm\<close> b4 by blast
      }
      ultimately  have "formEval (DabsTransfForm env  (existForm pf N)) (Dabs1  s)"
        by blast
    }
     ultimately  show "formEval (DabsTransfForm env  (existForm pf N)) (Dabs1  s)"
        by blast
    qed
 
next
  case (forallFormExcl pf i N)
  show ?case 
  proof (rule impI)+
    assume b1: "fitEnv s env"
      and b2: "deriveForm env (forallFormExcl pf i N)"
      and b4: "DabsTransfForm env  (forallFormExcl pf i N) \<noteq> dontCareForm"
      and b5: "formEval (forallFormExcl pf i N) s" 
    have "DsafeForm env (forallFormExcl pf i N)"
      by (meson DabsTransfForm.simps(10) DsafeForm.simps(6) DsafeForm.simps(8) b4) 
        
    show "formEval (DabsTransfForm env  (forallFormExcl pf i N)) (Dabs1  s)"
      using DsafeEval1 \<open>DsafeForm env (forallFormExcl pf i N)\<close> assms b1 b5 by blast
     
  qed
qed (auto simp add: Let_def)



lemma absTransfFormSim1:
  "absTransfExp env M e \<noteq> dontCareExp \<Longrightarrow>
   fitEnv s env \<Longrightarrow>
   deriveExp env e \<noteq> None \<Longrightarrow>
   expEval (absTransfExp env M e) (abs1 M s) = absTransfConst M (expEval e s)"
  using absTransfFormSim by blast 
  
lemma absTransfFormSim2:
  "fitEnv s env \<Longrightarrow>
   deriveForm env f \<Longrightarrow>
   absTransfForm env M f \<noteq> dontCareForm \<Longrightarrow>
   formEval f s \<Longrightarrow> formEval (absTransfForm env M f) (abs1 M s)"
  using absTransfFormSim by auto

subsection \<open>Wellformedness\<close>
 
text \<open>The condition only used in ite exp in for statement\<close>

definition wellCmpExp::"expType \<Rightarrow>bool" where
"wellCmpExp e\<equiv>(\<exists>rv. e= (Const (index rv))) \<or> (\<exists>rv. e= (IVar (Ident rv)))"

fun  boundAssignCond:: "nat \<Rightarrow> formula \<Rightarrow> bool" where
"boundAssignCond i (eqn l r) =
    (boundForm i (eqn l r)
   \<or> l = Const (index i) \<and> wellCmpExp r
   \<or> r = Const (index i) \<and> wellCmpExp l) " 
| "boundAssignCond i (neg f) = boundAssignCond i f"
| "boundAssignCond i (andForm f1 f2) = (boundAssignCond i f1 \<and> boundAssignCond i f2)"
| "boundAssignCond i (orForm f1 f2) = (boundAssignCond i f1 \<and> boundAssignCond i f2)"
| "boundAssignCond i (implyForm f1 f2) = (boundAssignCond i f1 \<and> boundAssignCond i f2)"
| "boundAssignCond i chaos = True"
| "boundAssignCond i dontCareForm = False"
| "boundAssignCond i (forallForm pf N) = False"
| "boundAssignCond i (existForm pf N) = False"
| "boundAssignCond i (forallFormExcl pf j N) = False"

fun boundAssignExp::" nat \<Rightarrow>expType \<Rightarrow>bool" where
  "boundAssignExp i dontCareExp =False" |

  "boundAssignExp i (Const n) =
    (case n of 
       index j \<Rightarrow> i = j | boolV b \<Rightarrow> True | enum t v \<Rightarrow> True | data d\<Rightarrow>True|_ \<Rightarrow> False)" |

  "boundAssignExp i (iteForm b e1 e2) =
    (boundAssignCond i b \<and> boundAssignExp i e1 \<and> boundAssignExp i e2)" |

  "boundAssignExp i (IVar v) = 
    (case v of Para n j \<Rightarrow> j = i | _ \<Rightarrow> False)"

text \<open>The statement only assigns to index i\<close>
fun boundAssign :: " nat \<Rightarrow> statement \<Rightarrow> bool" where
  "boundAssign i skip = True"
| "boundAssign i (assign (v, e)) = (\<exists>nm. v = Para nm i \<and> boundAssignExp i e)"  (*\<and> (boundVar  i e )*)
| "boundAssign i (S1 || S2) = (boundAssign i S1 \<and> boundAssign i S2)"
| "boundAssign i (iteStm b S1 S2) = (boundAssignCond i b \<and> boundAssign i S1 \<and> boundAssign i S2)"
| "boundAssign i (forallStm ps N) = False"
| "boundAssign i (forallStmExcl ps j N) = False"


fun nonDataAssign :: " envType \<Rightarrow> statement \<Rightarrow> bool" where
  "nonDataAssign env skip = True"
| "nonDataAssign env (assign (v, e)) =(v\<noteq>dontCareVar \<and> DsafeExp env e)"
| "nonDataAssign env (S1 || S2) = False"
| "nonDataAssign env (iteStm b S1 S2) = False"
| "nonDataAssign env (forallStm ps N) = False"
| "nonDataAssign env (forallStmExcl ps j N) = False"


text \<open>The statement is well-formed, with all forallStm over n.\<close>
primrec wellFormedStatement :: " envType\<Rightarrow>   nat\<Rightarrow>statement \<Rightarrow> bool" where
  "wellFormedStatement env  n skip = True"

| wellAssign:"wellFormedStatement env   n (assign x) =
  (\<forall>M. absTransfVar M (fst x) \<noteq> dontCareVar \<longrightarrow> absTransfExp env M (snd x) \<noteq> dontCareExp)" 

| wellPar: "wellFormedStatement env n (parallel S1 S2) = 
  (wellFormedStatement env n S1 \<and> wellFormedStatement env n S2)"

| wellIte: "wellFormedStatement env n (iteStm b S1 S2) =
  ((\<forall>M. safeForm env M b) \<and> wellFormedStatement env n S1 \<and> wellFormedStatement env n S2)"

| wellForall:"wellFormedStatement env n (forallStm ps N) = 
  (n = N \<and> (\<forall>i. boundAssign i (ps i))
   \<and> (\<forall>i. i \<le> N \<longrightarrow> wellFormedStatement env n (ps i)))"

| wellForallExcl:"wellFormedStatement env n (forallStmExcl ps j N) =
  (n = N \<and> (\<forall>i. boundAssign i (ps i))
   \<and> (\<forall>i. i \<le> N \<longrightarrow> wellFormedStatement env n (ps i)))"


primrec DwellFormedStatement :: " envType \<Rightarrow>statement \<Rightarrow> bool" where
  "DwellFormedStatement env   skip = True"

| DwellAssign:"DwellFormedStatement env    (assign x) =
  (fst x \<noteq>dontCareVar \<and>  DabsTransfExp env  (snd x) \<noteq> dontCareExp)" 

| DwellPar: "DwellFormedStatement env  (parallel S1 S2) = 
  (DwellFormedStatement env  S1 \<and> DwellFormedStatement env S2)"

| DwellIte: "DwellFormedStatement env  (iteStm b S1 S2) =
  (( DsafeForm env  b) \<and> DwellFormedStatement env S1 \<and> DwellFormedStatement env S2)"

| DwellForall:"DwellFormedStatement env  (forallStm ps N) = 
  (  (\<forall>i. boundAssign i (ps i)  \<and> nonDataAssign env (ps i) )
   \<and> (\<forall>i.   DwellFormedStatement env (ps i)) )"

| DwellForallExcl:"DwellFormedStatement env  (forallStmExcl ps j N) =
  (  (\<forall>i. boundAssign i (ps i) \<and> nonDataAssign env (ps i))
   \<and> (\<forall>i.   DwellFormedStatement env (ps i)))"


lemma varOfStmtBoundAssign:
  "boundAssign i S \<Longrightarrow> v \<in> varOfStmt S \<Longrightarrow> (\<exists>nm. v = Para nm i)"
proof (induction S)
  case (assign x)
  then show ?case apply (cases x) by auto
qed (auto)

lemma varOfStmtBoundAssignValid:
  "boundAssign i S \<Longrightarrow> v \<in> varOfStmt S \<Longrightarrow> i \<le> M \<Longrightarrow> absTransfVar M v \<noteq> dontCareVar"
  using varOfStmtBoundAssign by fastforce

subsection \<open>Abstraction of statement\<close>

primrec deriveStmt :: "envType \<Rightarrow> statement \<Rightarrow> bool" where 
  "deriveStmt env skip = True"
| "deriveStmt env (assign as) =
    (deriveExp env (IVar (fst as)) = deriveExp env (snd as) \<and>
     deriveExp env (IVar (fst as)) \<noteq> None)"
| "deriveStmt env (parallel S1 S2) = (deriveStmt env S1 \<and> deriveStmt env S2)"
| "deriveStmt env (iteStm b S1 S2) = (deriveForm env b \<and> deriveStmt env S1 \<and> deriveStmt env S2)"
| "deriveStmt env (forallStm PS N) = (\<forall>i. i \<le> N \<longrightarrow> deriveStmt env (PS i))"
| "deriveStmt env (forallStmExcl PS j N) = (\<forall>i. i \<le> N \<longrightarrow> deriveStmt env (PS i))"

primrec absTransfStatement :: "envType \<Rightarrow> nat \<Rightarrow> statement \<Rightarrow> statement" where
  "absTransfStatement env M skip = skip" |
  "absTransfStatement env M (assign as) = 
    (if absTransfVar M (fst as) = dontCareVar 
     then skip
     else assign (fst as, absTransfExp env M (snd as)))" |
  "absTransfStatement env M (parallel S1 S2) =
    parallel (absTransfStatement env M S1) (absTransfStatement env M S2)" |
  "absTransfStatement env M (iteStm b S1 S2) =
    iteStm (absTransfForm env M b) (absTransfStatement env M S1) (absTransfStatement env M S2)" |
  "absTransfStatement env M (forallStm PS N) =
    forallStm (\<lambda>i. absTransfStatement env M (PS i)) M" |
  "absTransfStatement env M (forallStmExcl PS j N) =
    (if j \<le> M then forallStmExcl (\<lambda>i. absTransfStatement env M (PS i)) j M else
     if j > M then forallStm (\<lambda>i. absTransfStatement env M (PS i)) M else skip)"


primrec DabsTransfStatement :: "envType   \<Rightarrow> statement \<Rightarrow> statement" where
  "DabsTransfStatement env    skip = skip" |
  "DabsTransfStatement env   (assign as) =  
     assign (fst as, DabsTransfExp env   (snd as))" |
  "DabsTransfStatement env   (parallel S1 S2) =
    parallel (DabsTransfStatement env   S1) (DabsTransfStatement env   S2)" |
  "DabsTransfStatement env   (iteStm b S1 S2) =
    iteStm (DabsTransfForm env   b) (DabsTransfStatement env   S1) (DabsTransfStatement env   S2)" |
 DabsForall: "DabsTransfStatement env   (forallStm PS N) =
    forallStm PS N" |
 DabsForallExcl:  "DabsTransfStatement env  (forallStmExcl PS j N) =
    ( forallStmExcl  (PS ) j N)"

definition equivExp :: "envType \<Rightarrow> expType \<Rightarrow> expType \<Rightarrow> bool" where
  "equivExp env e1 e2 \<equiv> \<forall>s. expEval e1 s = expEval e2 s"

lemma boundSafe:
  assumes "i \<le> M"
  shows "(boundExp  i e \<longrightarrow>(\<exists>et. deriveExp env e =Some(et)) \<longrightarrow>safeExp env M e  ) \<and>
         (boundForm  i f \<longrightarrow> deriveForm env f \<longrightarrow>safeForm env M f)"
    (is "?Pe e \<and> ?Pf f")
proof (induction rule: expType_formula.induct)
  fix x
  let ?e="IVar x"
  show "?Pe ?e"
    using boundExp.simps(2) by blast
next
  fix c
  let ?e="Const c"
  show "?Pe ?e"
    apply(case_tac "c")
       apply simp
    using assms apply force
     apply simp
     apply simp
    by simp
next
  fix b e1 e2
  let ?e="iteForm b e1 e2"
  show "?Pe ?e"
    by auto 
next
  let ?e="dontCareExp"
  show "?Pe ?e"
    by auto 
next
  fix e1 e2
  let ?f="eqn e1 e2"
  assume a:"?Pe e2"
  show "?Pf ?f"
  proof(rule impI)+
    assume b1: "boundForm i ?f" and
      b2: "deriveForm env ?f"
    have b3:"boundVar i e1 & boundExp i e2"
      by(cut_tac b1,auto)
    show "safeForm env M ?f"
    proof(cases e1)
      case (IVar x1)
      then show ?thesis
      proof(cases "env x1")
        case enumType
        then show ?thesis 
        proof -
          have "safeExp env M e1"
            by(cut_tac b2 b3 IVar enumType assms, case_tac x1, auto)
          have "deriveExp env e1=Some(enumType)"
            by (simp add: IVar enumType)
          have "deriveExp env e2=Some(enumType)"
            using \<open>deriveExp env e1 = Some enumType\<close> b2 by fastforce
          then have "\<exists>et. deriveExp env e2=Some(et)"
            by blast
          then have "safeExp env M e2" 
            by(cut_tac b3 assms a,auto  )  
          show ?thesis
            by (simp add: \<open>deriveExp env e1 = Some enumType\<close> \<open>safeExp env M e1\<close> \<open>safeExp env M e2\<close>) 
        qed    
      next
        case indexType
        then show ?thesis 
        proof -
          have c1:"deriveExp env e1=Some(indexType)"
            by (simp add: IVar indexType)
          have c2:"deriveExp env e2=Some(indexType)"
            using \<open>deriveExp env e1 = Some indexType\<close> b2 by fastforce
          then have c3:"\<exists>et. deriveExp env e2=Some(et)"
            by blast
          then have c4:"safeExp env M e2" 
            by(cut_tac b3 assms a, auto)
          have c5:"\<exists> i2. e2=Const (index i2)"
            apply(cases e2)
            using b3 boundExp.simps(2) apply blast
            apply (metis (no_types, lifting) c2 deriveExp.simps(1) enumTypeSafe evalConst fitEnv_def getValueType.simps(3) getValueType.simps(5) indexTypeSafe option.distinct(1) scalrValueType.exhaust scalrValueType.simps(25) scalrValueType.simps(28) typeType.distinct(1) typeType.distinct(13) typeType.distinct(9))
               using b3 boundExp.simps(3) apply blast
            using b3 boundExp.simps(4) by blast
          have "safeVar x1  M"
            by (smt (verit, ccfv_threshold) IVar assms b3 boundVar.simps(2) safeVar.simps(1) safeVar.simps(2) varType.exhaust varType.simps(10) varType.simps(11))
          show ?thesis
            using IVar \<open>safeVar x1 M\<close> c1 c4 c5 safeForm.simps(1) by blast
        qed
      next
        case boolType
        then show ?thesis 
        proof -
          have "safeExp env M e1"
            by(cut_tac b2 b3 IVar boolType assms, case_tac x1,auto )
          have "deriveExp env e1=Some(boolType)"
            by (simp add: IVar boolType)
          have "deriveExp env e2=Some(boolType)"
            using \<open>deriveExp env e1 = Some boolType\<close> b2 by fastforce
          then have "\<exists>et. deriveExp env e2=Some(et)"
            by blast
          then have "safeExp env M e2" 
            by(cut_tac b3 assms a,auto  )  
          show ?thesis
            by (simp add: \<open>deriveExp env e1 = Some boolType\<close> \<open>safeExp env M e1\<close> \<open>safeExp env M e2\<close>) 
        qed
      next
        case dataType
        then show ?thesis 
        proof -
          have "safeExp env M e1"
            by(cut_tac b2 b3 IVar dataType assms, case_tac x1,auto )
          have "deriveExp env e1=Some(dataType)"
            by (simp add: IVar dataType)
          have "deriveExp env e2=Some(dataType)"
            using \<open>deriveExp env e1 = Some dataType\<close> b2 by fastforce
          then have "\<exists>et. deriveExp env e2=Some(et)"
            by blast
          then have "safeExp env M e2" 
            by(cut_tac b3 assms a,auto  )  
          show ?thesis
            by (simp add: \<open>deriveExp env e1 = Some dataType\<close> \<open>safeExp env M e1\<close> \<open>safeExp env M e2\<close>) 
        qed
      next
        case anyType
        then show ?thesis
          by (metis IVar b2 deriveExp.simps(2) deriveForm.simps(1))  
      qed
    next
      case (Const x2)
      show ?thesis
      proof(cases x2)
        case (enum x11 x12)
        then show ?thesis
          using Const b3 by fastforce  
      next
        case (index i1)
        then show ?thesis  
        proof -
          have d1:"i1=i"
            using Const b3 index by auto
          have d2:"deriveExp env e1= Some(indexType)"
            by (simp add: Const index)
          have d3:"deriveExp env e2= Some(indexType)"
            using \<open>deriveExp env e1 = Some indexType\<close> b2 by force  
          then have d4:"\<exists>et. deriveExp env e2=Some(et)"
            by blast
          then have d5:"safeExp env M e2" 
            by(cut_tac b3 assms a,auto)
          have d6:"\<exists> i2. e2=Const (index i2)"
            apply(cases e2)
            using b3 boundExp.simps(2) apply blast
            apply(cases x2)
            using index apply force
            apply (metis (no_types, lifting) d3 deriveExp.simps(1) evalConst fitEnv_def getValueType.simps(1) getValueType.simps(3) getValueType.simps(5) indexTypeSafe option.distinct(1) scalrValueType.exhaust scalrValueType.simps(28) typeType.distinct(1) typeType.distinct(13) typeType.distinct(9))
            using index apply force
            using index apply force
            using index apply force
              using b3 boundExp.simps(3) apply blast
            using b3 boundExp.simps(4) by blast         
          show ?thesis
            apply simp
            using Const d2 d5 d6 index by blast   
        qed
      next
        case (boolV x3)
        then show ?thesis
          using Const a b2 b3 by auto 
      next
        case dontCare
        then show ?thesis
          using Const b3 by force 
      next
        case (data d)
        then show ?thesis
          using Const b3 by force 
      qed
    next
      case (iteForm x11 e11 e21)
      then show ?thesis
        using b3 boundVar.simps(3) by blast
    next
      case dontCareExp
      then show ?thesis
        using b3 boundVar.simps(4) by blast
    qed
  qed
next
  fix f1 f2
  assume "?Pf f1" and "?Pf f2"
  let ?f="(f1 \<and>\<^sub>f f2)"
  show "?Pf ?f"
  proof(rule impI)+
    assume "boundForm i (f1 \<and>\<^sub>f f2)" and " deriveForm env (f1 \<and>\<^sub>f f2)"
    show "safeForm env M ?f"
      using \<open>boundForm i (f1 \<and>\<^sub>f f2)\<close> \<open>boundForm i f1 \<longrightarrow> deriveForm env f1 \<longrightarrow> safeForm env M f1\<close> \<open>boundForm i f2 \<longrightarrow> deriveForm env f2 \<longrightarrow> safeForm env M f2\<close> \<open>deriveForm env (f1 \<and>\<^sub>f f2)\<close> by force
  qed
next
  fix f1
  assume "?Pf f1"  
  let ?f="neg f1"
  show "?Pf ?f"
  proof(rule impI)+  
    assume "boundForm i ?f" and "deriveForm env ?f"
    have "boundForm i f1"
      using \<open>boundForm i (\<not>\<^sub>f f1)\<close> by auto
    have "deriveForm env f1"
      using \<open>deriveForm env (\<not>\<^sub>f f1)\<close> deriveForm.simps(2) by blast
    have "safeForm env M f1"
      by (simp add: \<open>boundForm i f1 \<longrightarrow> deriveForm env f1 \<longrightarrow> safeForm env M f1\<close> \<open>boundForm i f1\<close> \<open>deriveForm env f1\<close>)
    show "safeForm env M ?f"
      by (simp add: \<open>safeForm env M f1\<close>)
  qed 
next
  fix f1 f2
  assume "?Pf f1" and "?Pf f2"
  let ?f="(orForm f1  f2)"
  show "?Pf ?f"
  proof(rule impI)+
    assume "boundForm i (?f)" and " deriveForm env (orForm f1  f2)"
    show "safeForm env M ?f"
      using \<open>boundForm i (f1 \<or>\<^sub>f f2)\<close> \<open>boundForm i f1 \<longrightarrow> deriveForm env f1 \<longrightarrow> safeForm env M f1\<close> \<open>boundForm i f2 \<longrightarrow> deriveForm env f2 \<longrightarrow> safeForm env M f2\<close> \<open>deriveForm env (f1 \<or>\<^sub>f f2)\<close> by auto 
  qed    
next 
  fix f1 f2
  assume "?Pf f1" and "?Pf f2"
  let ?f="(implyForm f1  f2)"
  show "?Pf ?f"
  proof(rule impI)+
    assume "boundForm i (?f)" and " deriveForm env ?f"
    show "safeForm env M ?f"
      using \<open>boundForm i (f1 \<longrightarrow>\<^sub>f f2)\<close> \<open>boundForm i f1 \<longrightarrow> deriveForm env f1 \<longrightarrow> safeForm env M f1\<close> \<open>boundForm i f2 \<longrightarrow> deriveForm env f2 \<longrightarrow> safeForm env M f2\<close> \<open>deriveForm env (f1 \<longrightarrow>\<^sub>f f2)\<close> by auto
  qed 
next
  fix pf N
  let ?f="(forallForm pf N)"
  show "?Pf ?f"
    using boundForm.simps(8) by blast
next
  fix pf N
  let ?f="(existForm pf N)"
  show "?Pf ?f"
    using boundForm.simps(9) by blast
next
  fix pf i N
  let ?f="(forallFormExcl pf i N)"
  show "?Pf ?f"
    using boundForm.simps(10) by blast
next
  show "?Pf chaos"
    by force
next
  show "?Pf dontCareForm"
    by auto 
qed

lemma absBoundAssignCond:
  assumes "i \<le> M"
  shows "boundAssignCond i f \<longrightarrow> deriveForm env f \<longrightarrow>
          (equivForm (absTransfForm env M f) f \<and>
           safeForm env M f \<and>
           absTransfForm env M f \<noteq> dontCareForm)" (is "?ant1 f \<longrightarrow> ?ant2 f \<longrightarrow>?P f")
proof (induct_tac f)
  fix x
  show "True"
    by simp
next    
  fix l r
  let ?f="(eqn l r)"
  show "?ant1 ?f \<longrightarrow> ?ant2 ?f \<longrightarrow>?P ?f"
  proof(rule impI)+
    assume a1:"?ant1 ?f" and a2:"?ant2 ?f "
    have IH1: "(boundForm i (eqn l r)
              \<or> l = Const (index i) \<and> wellCmpExp r
              \<or> r = Const (index i) \<and> wellCmpExp l)"
      using a1 boundAssignCond.simps(1) by blast
    moreover
    {assume a1:"boundForm i (eqn l r)"
      have a1:"((boundVar i l \<and> boundExp i r) ) "
        using a1 by auto
      have "absTransfExp env M l=l"
        using a1 absBoundVar assms by blast
      have "absTransfExp env M r=r"  
        apply(cut_tac a1 assms,case_tac "r", auto,case_tac "x2",auto) done
      have "safeForm env M ?f"
        using a1 a2 assms boundForm.simps(1) boundSafe by blast
      have b1:"?P ?f"
        using \<open>absTransfExp env M l = l\<close> \<open>absTransfExp env M r = r\<close> \<open>safeForm env M (l =\<^sub>f r)\<close> by auto 
    }
    moreover
    {assume a1:"l=Const (index i) \<and>(wellCmpExp r)"
      have b1:"equivForm  (absTransfForm env M ?f)  ?f" 
        by(cut_tac a1 assms,unfold wellCmpExp_def equivForm_def, auto simp add:Let_def)    
      have "safeForm env M ?f"
        apply(cut_tac a1 assms,auto)
        using a2 apply auto[1]
        using a2 apply force
         apply (meson safeVar.simps(1) wellCmpExp_def)
        by (meson safeVar.simps(1) wellCmpExp_def)
      have b1:"?P ?f"
        apply(rule conjI)
        using b1 apply blast
        apply(rule conjI)
        using \<open>safeForm env M (l =\<^sub>f r)\<close> a1 b1 expType.distinct(9) apply blast
        by(cut_tac a1 assms, unfold wellCmpExp_def,auto)
    }
    moreover
    {assume a1:"(r=(Const (index i)) \<and>(wellCmpExp l ))"
      have b1:"equivForm  (absTransfForm env M ?f)  ?f" 
        apply(cut_tac a1 assms,unfold wellCmpExp_def equivForm_def, auto simp add:Let_def)
        by (metis discrete not_less order_refl scalrValueType.inject(2))
      have "safeForm env M ?f"
        using a1 a2 assms wellCmpExp_def by force 
      have b1:"?P ?f"
        apply(rule conjI)
        using b1 apply blast
        apply(rule conjI)
        using \<open>safeForm env M (l =\<^sub>f r)\<close> a1 b1 expType.distinct(9) apply blast
        by(cut_tac a1 assms, unfold wellCmpExp_def,auto) 
    }
    ultimately show "?P ?f "
      by blast
  qed
next
  fix f
  let ?f="neg f" 
  assume a1:"?ant1 f \<longrightarrow> ?ant2 f \<longrightarrow>?P f"
  show "?ant1 ?f \<longrightarrow> ?ant2 ?f \<longrightarrow>?P ?f"
  proof(rule impI)+
    assume "?ant1 ?f"  and "?ant2 ?f "  
    have "boundAssignCond i ( f)"
      using \<open>boundAssignCond i (\<not>\<^sub>f f)\<close> boundAssignCond.simps(2) by blast
    have "deriveForm env f "
      using \<open>deriveForm env (\<not>\<^sub>f f)\<close> by auto
    have "equivForm  (absTransfForm env M f)  f \<and>safeForm env M f"
      by (simp add: \<open>boundAssignCond i f\<close> \<open>deriveForm env f\<close> a1) 
    then show "?P ?f"
      by(unfold equivForm_def,auto)
  qed
next
  fix f1 f2
  assume a1:"?ant1 f1 \<longrightarrow> ?ant2 f1 \<longrightarrow>?P f1"  and a2:"?ant1 f2 \<longrightarrow> ?ant2 f2 \<longrightarrow>?P f2"
  let ?f="(orForm f1  f2)"
  show "?ant1 ?f \<longrightarrow> ?ant2 ?f \<longrightarrow>?P ?f"
  proof(rule impI)+
    assume b1:"?ant1 ?f"  and b2:"?ant2 ?f "
    have b3:"boundAssignCond  i f1 \<and> boundAssignCond  i f2"
      using b1 boundAssignCond.simps(4) by blast
    have b4:"deriveForm env f1 \<and> deriveForm env f2"
      using b2 by auto 
    have b5:"?P f1"
      using a1 b3 b4 by blast 
    have b6:"?P f2"
      using a2 b3 b4 by blast 
    show "?P ?f"
      by(cut_tac b5 b6, unfold equivForm_def, auto)
  qed  
next
  fix f1 f2
  assume a1:"?ant1 f1 \<longrightarrow> ?ant2 f1 \<longrightarrow>?P f1"  and a2:"?ant1 f2 \<longrightarrow> ?ant2 f2 \<longrightarrow>?P f2"
  let ?f="(andForm f1  f2)"
  show "?ant1 ?f \<longrightarrow> ?ant2 ?f \<longrightarrow>?P ?f"
  proof(rule impI)+
    assume b1:"?ant1 ?f"  and b2:"?ant2 ?f "
    have b3:"boundAssignCond  i f1 \<and> boundAssignCond  i f2"
      using b1 boundAssignCond.simps(3) by blast
    have b4:"deriveForm env f1 \<and> deriveForm env f2"
      using b2 by auto 
    have b5:"?P f1"
      using a1 b3 b4 by blast 
    have b6:"?P f2"
      using a2 b3 b4 by blast 
    show "?P ?f"
      by(cut_tac b5 b6, unfold equivForm_def, auto)
  qed 
next
  fix f1 f2
  assume a1:"?ant1 f1 \<longrightarrow> ?ant2 f1 \<longrightarrow>?P f1"  and a2:"?ant1 f2 \<longrightarrow> ?ant2 f2 \<longrightarrow>?P f2"
  let ?f="(implyForm f1  f2)"
  show "?ant1 ?f \<longrightarrow> ?ant2 ?f \<longrightarrow>?P ?f"
  proof(rule impI)+
    assume b1:"?ant1 ?f"  and b2:"?ant2 ?f "
    have b3:"boundAssignCond  i f1 \<and> boundAssignCond  i f2"
      using b1 boundAssignCond.simps(5) by blast
    have b4:"deriveForm env f1 \<and> deriveForm env f2"
      using b2 by auto 
    have b5:"?P f1"
      using a1 b3 b4 by blast 
    have b6:"?P f2"
      using a2 b3 b4 by blast 
    show "?P ?f"
      by(cut_tac b5 b6, unfold equivForm_def, auto)
  qed 
next
  fix ps N
  let ?f="forallForm ps N"
  show "?ant1 ?f \<longrightarrow> ?ant2 ?f \<longrightarrow>?P ?f"
    using boundAssignCond.simps(8) by blast
next
  fix ps N
  let ?f="existForm ps N"
  show "?ant1 ?f \<longrightarrow> ?ant2 ?f \<longrightarrow>?P ?f"
    using boundAssignCond.simps(9) by blast
next
  fix ps i N
  let ?f="forallFormExcl ps i N"
  show "?ant1 ?f \<longrightarrow> ?ant2 ?f \<longrightarrow>?P ?f"
    using boundAssignCond.simps(10) by blast
next
  let ?f="chaos"
  show "?ant1 ?f \<longrightarrow> ?ant2 ?f \<longrightarrow>?P ?f"
    by auto 
qed (auto)

lemma absBoundAssignExp:
  assumes "i \<le> M"
  shows "boundAssignExp i e \<longrightarrow>
         (\<exists>et. deriveExp env e = Some et) \<longrightarrow>
         (absTransfExp env M e \<noteq> dontCareExp \<and>
          equivExp env (absTransfExp env M e) e)" (is "?ant1 e\<longrightarrow>?ant2 e\<longrightarrow>?P e")
proof (induct_tac e)
  fix v
  let ?e="IVar v"
  show "?ant1 ?e\<longrightarrow>?ant2 ?e\<longrightarrow>?P ?e"
  proof(rule impI)+
    assume a:"?ant1 ?e" and b:"?ant2 ?e"
    have "absTransfVar M v = v"
      by (smt (verit, del_insts) a absTransfVar.simps(1) absTransfVar.simps(2) absTransfVar.simps(3) assms boundAssignExp.simps(4) leD varType.exhaust varType.simps(10))
    then show "?P ?e"
      apply auto
      using a apply force
      using equivExp_def by blast
  qed
next
  fix c2
  let ?e="Const c2"                                                              
  show "?ant1 ?e\<longrightarrow>?ant2 ?e\<longrightarrow>?P ?e"
  proof(rule impI)+
    assume a:"?ant1 ?e" and b:"?ant2 ?e"
    show "?P ?e"
    proof(cases c2)
      case (enum x11 x12)
      then show ?thesis
        by (simp add: equivExp_def) 
    next
      case (index x2)
      have "x2=i" 
        apply(cut_tac a index)
        by simp
      then show ?thesis
        by (simp add: assms equivExp_def index leD) 
    next
      case (boolV x3)
      then show ?thesis
        by (simp add: equivExp_def)  
        
    next
      case dontCare
      then show ?thesis
        using a by auto  
        
    next
      case (data x5)
      then show ?thesis
        by (simp add: equivExp_def)  
        
    qed
  qed       
next
  fix b e1 e2
  let ?e="iteForm b e1 e2"
  assume IH1:"?ant1 e1\<longrightarrow>?ant2 e1\<longrightarrow>?P e1" and IH2:"?ant1 e2\<longrightarrow>?ant2 e2\<longrightarrow>?P e2"
  show "?ant1 ?e\<longrightarrow>?ant2 ?e\<longrightarrow>?P ?e"
  proof(rule impI)+
    assume a:"?ant1 ?e" and b:"?ant2 ?e"
    have c1:"boundAssignCond i b \<and> boundAssignExp  i e1 & boundAssignExp  i e2"
      using a boundAssignExp.simps(3) by blast
    have c2:"deriveForm env b \<and> deriveExp env e1=deriveExp env e2 & deriveExp env e1\<noteq>None  "
      by (metis b deriveExp.simps(3) option.distinct(1))
    have c3:"\<exists>et. deriveExp env e1=Some(et)"
      using c2 by blast  
    have c4:"\<exists>et. deriveExp env e2=Some(et)"
      using c2 c3 by auto 
    have c5:"equivForm  (absTransfForm env M b)  b \<and>safeForm env M b \<and> (absTransfForm env M b)\<noteq>dontCareForm"
      using absBoundAssignCond assms c1 c2 by presburger
    have c6:"?P e1"
      using IH1 c1 c3 by blast  
    have c7:"?P e2"
      using IH2 c1 c4 by blast 
    show "?P ?e"
      using c5 c6 c7 equivExp_def equivForm_def by auto
  qed 
next
  let ?e="dontCareExp"
  show "?ant1 ?e\<longrightarrow>?ant2 ?e\<longrightarrow>?P ?e"
    by force
qed(auto)


lemma nonDataAssignDabs: assumes "env dontCareVar=anyType"
  shows "nonDataAssign env S \<longrightarrow>deriveStmt env S\<longrightarrow>DabsTransfStatement env S =S" (is "?P S")
proof(induct_tac S)
  show "?P skip" 
    by auto
next
  fix x
  let ?S="assign x"
  show "?P ?S"
  proof(rule impI)+
    assume " nonDataAssign env (assign x)" "deriveStmt env (assign x)"
    have " (fst x) \<noteq> dontCareVar"
      by (metis \<open>nonDataAssign env (assign x)\<close> nonDataAssign.simps(2) prod.exhaust_sel)
    have "DsafeExp env (snd x)"
      by (metis \<open>nonDataAssign env (assign x)\<close> nonDataAssign.simps(2) prod.collapse)
    have "deriveExp env (snd x)\<noteq>None"
      by (metis \<open>deriveStmt env (assign x)\<close> deriveStmt.simps(2))
      
    have "DabsTransfExp env (snd x) = snd x"
      by (simp add: DsafeTransf \<open>DsafeExp env (snd x)\<close> assms)
    show "DabsTransfStatement env (assign x) = assign x"
      by (simp add: \<open>DabsTransfExp env (snd x) = snd x\<close>)
  qed
qed(auto)
      
lemma equivStatementBoundAssign:
  assumes "i \<le> M"
  shows "boundAssign i S \<Longrightarrow> deriveStmt env S \<Longrightarrow> equivStatement (absTransfStatement env M S) S"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  show ?case
  proof (cases x)
    case (Pair v e)
    obtain nm where v: "v = Para nm i" "boundAssignExp  i e" (*"boundVar i e"*)
      using assign unfolding Pair by auto
    have deriveE:"
    (deriveExp env (IVar (fst x)) = deriveExp env (snd x)  \<and>
     deriveExp env (IVar (fst x)) \<noteq> None)"
      using assign.prems(2) deriveStmt.simps(2) by blast
    have valid_e: "equivExp env (absTransfExp env M e)  e"
      by (metis Pair \<open>\<And>thesis. (\<And>nm. \<lbrakk>v = Para nm i; boundAssignExp i e\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> absBoundAssignExp assms deriveE deriveExp.simps(2) prod.sel(2))
    have "absTransfStatement env M (assign (Para nm i, e)) = assign (Para nm i,(absTransfExp env M e))"
      using valid_e assms by auto
    show ?thesis
    proof(unfold Pair v  equivStatement_def,rule conjI)
      show "varOfStmt (absTransfStatement env M (assign (Para nm i, e))) = varOfStmt (assign (Para nm i, e))"
        using \<open>absTransfStatement env M (assign (Para nm i, e)) = assign (Para nm i, absTransfExp env M e)\<close> by force
    next
      show "\<forall>s. trans1 (absTransfStatement env M (assign (Para nm i, e))) s = trans1 (assign (Para nm i, e)) s"
      proof(rule allI,rule ext)
        fix s x
        show "trans1 (absTransfStatement env M (assign (Para nm i, e))) s x = trans1 (assign (Para nm i, e)) s x"
        proof(case_tac "x= (Para nm i)")
          assume "x= (Para nm i)"
          show "trans1 (absTransfStatement env M (assign (Para nm i, e))) s x = trans1 (assign (Para nm i, e)) s x"
            using \<open>absTransfStatement env M (assign (Para nm i, e)) = assign (Para nm i, absTransfExp env M e)\<close> equivExp_def valid_e by auto
        next
          assume "x\<noteq> (Para nm i)"
          show "trans1 (absTransfStatement env M (assign (Para nm i, e))) s x = trans1 (assign (Para nm i, e)) s x"
            using \<open>absTransfStatement env M (assign (Para nm i, e)) = assign (Para nm i, absTransfExp env M e)\<close> equivExp_def valid_e by auto
        qed
      qed
    qed
  qed
next
  case (parallel S1 S2)
  then show ?case
    by (auto simp add: equivStatement_def)
next
  case (iteStm b S1 S2)
  show ?case
    apply auto
    apply (rule equivStatementIteStm)
      apply (meson absBoundAssignCond assms boundAssign.simps(4) deriveStmt.simps(4) iteStm.prems(1,2))
    using boundAssign.simps(4) deriveStmt.simps(4) iteStm by blast+
next
  case (forallStm ps N)
  then show ?case by auto
next
  case (forallStmExcl ps j N)
  then show ?case by auto
qed

lemma equivStatementForallAbs:
  assumes "\<And>i. boundAssign i (ps i)"
    and "\<And>i. i \<le> N \<longrightarrow> deriveStmt env (ps i)" and "M \<le> N"
  shows "equivStatement
    (forallStm (\<lambda>i. absTransfStatement env M (ps i)) M)
    (forallStm ps M)"
proof -
  have a: "equivStatement (absTransfStatement env M (ps i)) (ps i)" if "i \<le> M" for i
    using equivStatementBoundAssign that assms by auto
  have b: "varOfStmt (forallStm (\<lambda>i. absTransfStatement env M (ps i)) M) = varOfStmt (forallStm ps M)"
    apply (auto simp add: varOfStmtEq)
    using a unfolding equivStatement_def by auto
  have c: "largestInd v M (\<lambda>i. absTransfStatement env  M (ps i)) = None \<longleftrightarrow> largestInd v M ps = None" for v
    unfolding largestIndNone using a equivStatement_def by auto
  have d: "largestInd v M (\<lambda>j. absTransfStatement env M (ps j)) = Some i \<longleftrightarrow> largestInd v M ps = Some i" for v i
    unfolding largestIndSome using a equivStatement_def by auto
  have e: "trans1 (forallStm (\<lambda>i. absTransfStatement env M (ps i)) M) s v = trans1 (forallStm ps M) s v" for s v
    using c[of v] d[of v] apply auto
    by (metis a equivStatement_def largestIndSome)
  show ?thesis
    unfolding equivStatement_def using b e by auto
qed

lemma equivStatementForallExclAbs:
  assumes "\<And>i. boundAssign i (ps i)"
    and "\<And>i. i \<le> N \<longrightarrow> deriveStmt env (ps i)" and "M \<le> N"
  shows "equivStatement
    (forallStmExcl (\<lambda>i. absTransfStatement env M (ps i)) j M)
    (forallStmExcl ps j M)"
proof -
  have a: "equivStatement (absTransfStatement env M (ps i)) (ps i)" if "i \<le> M" for i
    using equivStatementBoundAssign that assms by auto
  have b: "varOfStmt (forallStm (\<lambda>i. absTransfStatement env M (ps i)) M) = varOfStmt (forallStm ps M)"
    apply (auto simp add: varOfStmtEq)
    using a unfolding equivStatement_def by auto
  have c: "largestIndExcl v j M (\<lambda>i. absTransfStatement env M (ps i)) = None \<longleftrightarrow> largestIndExcl v j M ps = None" for v
    unfolding largestIndExclNone using a equivStatement_def by auto
  have d: "largestIndExcl v j M (\<lambda>j. absTransfStatement env M (ps j)) = Some i \<longleftrightarrow> largestIndExcl v j M ps = Some i" for v i
    unfolding largestIndExclSome using a equivStatement_def by auto
  have e: "trans1 (forallStmExcl (\<lambda>i. absTransfStatement env M (ps i)) j M) s v = trans1 (forallStmExcl ps j M) s v" for s v
    using c[of v] d[of v] apply auto
    by (metis a equivStatement_def largestIndExclSome)
  show ?thesis
    unfolding equivStatement_def using b e
    by (meson a equivStatementForallExcl equivStatement_def)
qed

lemma equivStatementForallExclAbs2:
  assumes "j > M"
  shows "equivStatement (forallStmExcl ps j M) (forallStm ps M)"
proof -
  have "largestIndExcl v j M ps = largestInd v M ps" for v
    apply (cases "largestInd v M ps")
     apply (metis largestIndExclNone largestIndNone)
    by (smt (verit) assms largestIndExclSome largestIndSome leD)
  then show ?thesis
    unfolding equivStatement_def apply (auto simp add: varOfStmtEq varOfStmtEq2)
    using assms by auto 
qed

lemma varOfStmtAbs:
  assumes "M \<le> n"
  shows "wellFormedStatement env n S \<Longrightarrow> deriveStmt env S \<Longrightarrow> fitEnv s env \<Longrightarrow>
         v \<in> varOfStmt (absTransfStatement env M S) \<longleftrightarrow>
         v \<in> varOfStmt S \<and> absTransfVar M v \<noteq> dontCareVar"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  then show ?case by auto
next
  case (parallel S1 S2)
  then show ?case by auto
next
  case (iteStm b S1 S2)
  then show ?case by auto
next
  case (forallStm ps N)
  have a: "boundAssign i (ps i)"  for i
    using forallStm.prems(1) by force 
  have b: "Para nm j \<in> varOfStmt (ps i) \<longrightarrow> j = i" for nm i j
    using varOfStmtBoundAssign[OF a] by auto
  have c: "\<exists>j\<le>n. v \<in> varOfStmt (ps j)" "absTransfVar M v \<noteq> dontCareVar"
    if "i \<le> M" "v \<in> varOfStmt (absTransfStatement env M (ps i))" for i
  proof -
    have c1: "wellFormedStatement env n (ps i)" "n = N"
      apply (metis assms dual_order.trans forallStm.prems(1) that(1) wellForall)
      using forallStm(2) by auto
    have c2: "v \<in> varOfStmt (absTransfStatement env M (ps i)) = 
              (v \<in> varOfStmt (ps i) \<and> absTransfVar M v \<noteq> dontCareVar)"
      apply (rule forallStm(1))
      apply blast
      apply (simp add: c1(1))
      using forallStm.prems(2) apply auto[1]
      using assms c1(2) that(1) apply auto[1]
      by (simp add: forallStm.prems(3)) 
    have c3: "v \<in> varOfStmt (ps i)" "absTransfVar M v \<noteq> dontCareVar"
      using c2 that(2) by auto
    show "\<exists>j\<le>n. v \<in> varOfStmt (ps j)"
      apply (rule exI[where x=i])
      using assms c1(2) c3(1) le_trans that(1) by blast
    show "absTransfVar M v \<noteq> dontCareVar"
      using c3 by auto
  qed
  have d: "\<exists>j\<le>M. v \<in> varOfStmt (absTransfStatement env M (ps j))"
    if assmd: "absTransfVar M v \<noteq> dontCareVar" "i \<le> N" "v \<in> varOfStmt (ps i)" for i
  proof -
    obtain nm where d1: "v = Para nm i"
      using assmd(3) a[of i] varOfStmtBoundAssign by blast
    have d2: "i \<le> M"
      using d1 assmd(1) nat_neq_iff by fastforce
    have d3: "wellFormedStatement env n (ps i)" "n = N"
      using forallStm.prems(1) that(2) apply force
      using forallStm(2) by auto
    have d4: "absTransfVar M v \<noteq> dontCareVar"
      using d1 d2 by auto
    have d5: "v \<in> varOfStmt (absTransfStatement env M (ps i)) =
              (v \<in> varOfStmt (ps i) \<and> absTransfVar M v \<noteq> dontCareVar)"
      apply (rule forallStm(1))
      apply blast
      apply (simp add: d3(1))
      using forallStm.prems(2) apply auto[1]
      using that(2) apply auto[1] 
      by (simp add: forallStm.prems(3)) 
    show ?thesis
      apply (rule exI[where x=i])
      unfolding d5 by (auto simp add: d2 d4 assmd(3))
  qed
  show ?case
    using c(1) c(2) d forallStm.prems(1) varOfStmtEq by auto 
next
  case (forallStmExcl ps j N)
  have a: "boundAssign i (ps i)"  for i
    using forallStmExcl.prems(1) by force 
  have b: "Para nm j \<in> varOfStmt (ps i) \<longrightarrow> j = i" for nm i j
    using varOfStmtBoundAssign[OF a] by auto
  have c: "\<exists>j\<le>n. v \<in> varOfStmt (ps j)" "absTransfVar M v \<noteq> dontCareVar"
    if "i \<le> M" "v \<in> varOfStmt (absTransfStatement env M (ps i))" for i
  proof -
    have c1: "wellFormedStatement env n (ps i)" "n = N"
      apply (metis assms forallStmExcl.prems(1) order_trans that(1) wellForallExcl)
      using forallStmExcl(2) by auto
    have c2: "v \<in> varOfStmt (absTransfStatement env M (ps i)) = 
              (v \<in> varOfStmt (ps i) \<and> absTransfVar M v \<noteq> dontCareVar)"
      apply (rule forallStmExcl(1))
      apply blast
      apply (simp add: c1(1))
      using forallStmExcl.prems(2) apply auto[1]
      using assms c1(2) that(1) apply auto[1]
      by (simp add: forallStmExcl.prems(3)) 
    have c3: "v \<in> varOfStmt (ps i)" "absTransfVar M v \<noteq> dontCareVar"
      using c2 that(2) by auto
    show "\<exists>j\<le>n. v \<in> varOfStmt (ps j)"
      apply (rule exI[where x=i])
      using assms c1(2) c3(1) le_trans that(1) by blast
    show "absTransfVar M v \<noteq> dontCareVar"
      using c3 by auto
  qed
  have d: "\<exists>j\<le>M. v \<in> varOfStmt (absTransfStatement env M (ps j))"
    if assmd: "absTransfVar M v \<noteq> dontCareVar" "i \<le> N" "v \<in> varOfStmt (ps i)" for i
  proof -
    obtain nm where d1: "v = Para nm i"
      using assmd(3) a[of i] varOfStmtBoundAssign by blast
    have d2: "i \<le> M"
      using d1 assmd(1) nat_neq_iff by fastforce
    have d3: "wellFormedStatement env n (ps i)" "n = N"
      using forallStmExcl.prems(1) that(2) apply force
      using forallStmExcl(2) by auto
    have d4: "absTransfVar M v \<noteq> dontCareVar"
      using d1 d2 by auto
    have d5: "v \<in> varOfStmt (absTransfStatement env M (ps i)) =
              (v \<in> varOfStmt (ps i) \<and> absTransfVar M v \<noteq> dontCareVar)"
      apply (rule forallStmExcl(1))
      apply blast
      apply (simp add: d3(1))
      using forallStmExcl.prems(2) apply auto[1]
      using that(2) apply auto[1] 
      by (simp add: forallStmExcl.prems(3)) 
    show ?thesis
      apply (rule exI[where x=i])
      unfolding d5 by (auto simp add: d2 d4 assmd(3))
  qed
  show ?case
    apply (cases "j \<le> M")
    subgoal
      apply (auto simp add: varOfStmtEq2 c d)
       apply (metis assms deriveStmt.simps(6) forallStmExcl le_trans range_eqI wellForallExcl)
      by (metis absTransfVar.simps(2) deriveStmt.simps(6) forallStmExcl leI rangeI varOfStmtBoundAssign wellForallExcl)
    subgoal
      apply (auto simp add: varOfStmtEq2 varOfStmtEq)
      apply (metis assms deriveStmt.simps(6) forallStmExcl le_trans range_eqI wellForallExcl)
      using c(2) apply blast
      by (simp add: d)
    done
qed

(*lemma DabsForallStmSame:
  assumes a1:"DwellFormedStatement env  (forallStm ps N)   " and  a2:"deriveStmt env S " 
  shows "DabsTransfStatement env (forallStm ps N) = (forallStm ps N)"*)
  

lemma varOfStmtDAbs: 
  shows "DwellFormedStatement env  S \<Longrightarrow> deriveStmt env S \<Longrightarrow> fitEnv s env \<Longrightarrow>
         v \<in> varOfStmt (DabsTransfStatement env  S) \<longleftrightarrow>
         v \<in> varOfStmt S  "
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  then show ?case by auto
next
  case (parallel S1 S2)
  then show ?case by auto
next
  case (iteStm b S1 S2)
  then show ?case by auto
next
  case (forallStm ps N) 
  then show ?case
    using DabsTransfStatement.simps(5) by presburger  
next
  case (forallStmExcl ps j N)
  then show ?case
    by simp
    
qed

lemma absStatement:
  assumes "M \<le> n"
  shows "wellFormedStatement env n S \<Longrightarrow>
         fitEnv s env \<Longrightarrow> deriveStmt env S \<Longrightarrow>
         abs1 M (trans1 S s) = trans1 (absTransfStatement env M S) (abs1 M s)"
proof (induction S)
  case skip
  then show ?case by auto
next
  case (assign x)
  have a0:"wellFormedStatement env n (assign x)"
    using assign.prems(1) by blast 
  (*have a1:"EX i. i \<le>n \<and>boundVar i (IVar (fst x)) \<and> boundAssignExp i (snd x)"
    using a0 wellAssign by blast*)

 (* have a2:"absTransfVar M (fst x) \<noteq> dontCareVar \<longrightarrow> absTransfExp env M (snd x) \<noteq> dontCareExp "
    using a1 assms by blast*)
    
  have a: "abs1 M (\<lambda>a. if v = a then expEval e s else s a) w = abs1 M s w"
    if "absTransfVar M v = dontCareVar" "x = (v, e)" for v e w
  proof -
    have "v = dontCareVar \<or> (\<exists>n i. i > M \<and> v = Para n i)"
      using that apply (cases v) apply auto
      by (meson varType.distinct(5))
    then show ?thesis
      apply (cases w) by auto
  qed
  have b: "abs1 M (\<lambda>a. if v = a then expEval e s else s a) w =
           (if v = w then expEval (absTransfExp env M e) (abs1 M s) else abs1 M s w)"
    if "absTransfVar M v \<noteq> dontCareVar" "x = (v, e)" for v e w
  proof -
    have 1:"v=fst x"
      by (simp add: that(2)) 
    have valid_e: "absTransfExp env M e \<noteq> dontCareExp"
      using assign that a0 assms by auto
      
    have "(\<exists>n. v = Ident n) \<or> (\<exists>n i. i \<le> M \<and> v = Para n i)"
      using that apply (cases v) apply auto
      by (meson leI)
    have "deriveExp env (IVar v) = deriveExp env e \<and> 
      deriveExp env e\<noteq>None"
      by (metis assign.prems(3) deriveStmt.simps(2) prod.sel(1) prod.sel(2) that(2)) 
    then show ?thesis
     (* using abs1Eq assign.prems(2) safeEval1 that(1) valid_e by presburger*)
      apply (cases w) apply auto
      using absTransfFormSim1 assign.prems(2) valid_e apply auto[1]
      using that(1) apply auto[1]
      using absTransfFormSim1 assign.prems(2) valid_e apply auto[1]
      using absTransfVar.simps(3) that(1) by blast 
  qed
  show ?case
    apply (cases x)
    subgoal for v e apply auto
      unfolding snd_def
      using a apply auto[1]
      using b apply auto[1]
      done
    done
next
  case (parallel S1 S2)
  have a: "wellFormedStatement env n S1" "wellFormedStatement env n S2"
    using parallel(3) by auto
  have a2:"deriveStmt env S1" "deriveStmt env S2"
    using deriveStmt.simps(3) parallel.prems(3) by blast+
  have b: "v \<in> varOfStmt (absTransfStatement env M S1) \<longleftrightarrow> 
           v \<in> varOfStmt S1 \<and> absTransfVar M v \<noteq> dontCareVar" for v
    using varOfStmtAbs[OF assms a(1)] a2(1) parallel.prems(2) by auto
  have c: "abs1 M (\<lambda>a. if a \<in> varOfStmt S1 then trans1 S1 s a else trans1 S2 s a) w =
           (if w \<in> varOfStmt (absTransfStatement env M S1) then
              abs1 M (trans1 S1 s) w
            else
              abs1 M (trans1 S2 s) w)" for w
    unfolding abs1Eq b by auto
  show ?case
    using parallel c by auto
next
  case (iteStm b S1 S2)
  have "safeForm env M b"
    using iteStm(3) by auto
  then have a1: "formEval (absTransfForm env M b) (abs1 M s) = formEval b s"
    by (metis absTransfForm.simps(2) absTransfFormSim2 deriveForm.simps(2) deriveStmt.simps(4)
              evalDontCareForm evalNeg iteStm.prems(2) iteStm.prems(3))
  show ?case
    apply (auto simp add: a1)
    apply (rule ext)
    using iteStm by auto
next
  case (forallStm ps N)
  have a: "n = N"
    using forallStm(2) by auto
  have b: "boundAssign i (ps i)" "wellFormedStatement env n (ps i)" if "i\<le>N" for i
    using forallStm.prems(1) that apply fastforce
    using forallStm.prems(1) that by auto
  have b1:"fitEnv s env" 
    by (simp add: forallStm.prems(2))
  have c: "i \<le> N \<longrightarrow>
           (v \<in> varOfStmt (absTransfStatement env M (ps i)) \<longleftrightarrow>
            v \<in> varOfStmt (ps i) \<and> absTransfVar M v \<noteq> dontCareVar)" for v i
    apply (rule impI)
    apply (rule varOfStmtAbs[OF assms b(2)])
    apply simp
    using forallStm.prems(3) apply auto[1] 
    by (cut_tac b1,simp)
  have d: "i \<le> N \<longrightarrow>
           abs1 M (trans1 (ps i) s) = trans1 (absTransfStatement env M (ps i)) (abs1 M s)" for i
    using forallStm(1)[OF _ b(2)] apply auto
    using deriveStmt.simps(5) forallStm.prems(2) forallStm.prems(3)
    by blast
  have e: "largestInd v M (\<lambda>i. absTransfStatement env M (ps i)) = None \<longleftrightarrow>
           largestInd v N ps = None \<or> absTransfVar M v = dontCareVar" for v
    unfolding largestIndNone c apply auto
      apply (metis absTransfVar.simps(2) b(1) c leI varOfStmtBoundAssign) 
    using a assms c by auto
  have f: "largestInd v M (\<lambda>j. absTransfStatement env M (ps j)) = Some i \<longleftrightarrow>
           largestInd v N ps = Some i \<and> absTransfVar M v \<noteq> dontCareVar" for v i
    unfolding largestIndSome c apply auto
    using a assms dual_order.trans apply blast
    using a assms c le_trans apply blast
        apply (metis b(1) c dual_order.trans less_imp_le_nat varOfStmtBoundAssign varType.inject(2))
       apply (metis a assms c dual_order.trans)
      apply (metis absTransfVar.simps(2) b(1) not_le_imp_less varOfStmtBoundAssign)
    using c apply presburger
    by (metis a assms c order.trans)
  have g: "abs1 M (\<lambda>a. case largestInd a N ps of None \<Rightarrow> s a | Some i \<Rightarrow> trans1 (ps i) s a) w =
            (case largestInd w M (\<lambda>i. absTransfStatement env M (ps i)) of
               None \<Rightarrow> abs1 M s w
             | Some i \<Rightarrow> abs1 M (trans1 (ps i) s) w)" for w
    unfolding abs1Eq using e f
    by (smt option.case_eq_if option.collapse)
  show ?case
    apply auto apply (rule ext)
    subgoal for w
      unfolding g
      apply (cases "largestInd w M (\<lambda>i. absTransfStatement env M (ps i))")
       apply auto
      subgoal premises pre for i
      proof -
        have "i \<le> N"
          using pre largestIndSome a assms by auto
        then show ?thesis
          using d by simp
      qed
      done
    done
next
  case (forallStmExcl ps j N)
  have a: "n = N"
    using forallStmExcl(2) by auto
  have b: "boundAssign i (ps i)" "wellFormedStatement env n (ps i)" if "i\<le>N" for i
    using forallStmExcl.prems(1) that apply fastforce
    using forallStmExcl.prems(1) that by auto
  have b1:"fitEnv s env" 
    by (simp add: forallStmExcl.prems(2))
  have c: "i \<le> N \<longrightarrow>
           (v \<in> varOfStmt (absTransfStatement env M (ps i)) \<longleftrightarrow>
            v \<in> varOfStmt (ps i) \<and> absTransfVar M v \<noteq> dontCareVar)" for v i
    apply (rule impI)
    apply (rule varOfStmtAbs[OF assms b(2)])
    apply simp
    using forallStmExcl.prems(3) apply auto[1] 
    by (cut_tac b1, simp)
  have d: "i \<le> N \<Longrightarrow>
           abs1 M (trans1 (ps i) s) = trans1 (absTransfStatement env M (ps i)) (abs1 M s)" for i
    using forallStmExcl(1)[OF _ b(2)] apply auto
    using deriveStmt.simps(5) forallStmExcl
    by (meson deriveStmt.simps(6))
  have e: "largestIndExcl v j M (\<lambda>i. absTransfStatement env M (ps i)) = None \<longleftrightarrow>
           largestIndExcl v j N ps = None \<or> absTransfVar M v = dontCareVar" for v
    unfolding largestIndExclNone c apply auto
      apply (metis absTransfVar.simps(2) b(1) c leI varOfStmtBoundAssign) 
    using a assms c by auto
  have f: "largestIndExcl v j M (\<lambda>j. absTransfStatement env M (ps j)) = Some i \<longleftrightarrow>
           largestIndExcl v j N ps = Some i \<and> absTransfVar M v \<noteq> dontCareVar" for v i
    unfolding largestIndExclSome c apply auto
    using a assms dual_order.trans apply blast
    using a assms c le_trans apply blast
        apply (metis b(1) c dual_order.trans less_imp_le_nat varOfStmtBoundAssign varType.inject(2))
       apply (metis a assms c dual_order.trans)
      apply (metis absTransfVar.simps(2) b(1) not_le_imp_less varOfStmtBoundAssign)
    using c apply presburger
    by (metis a assms c order.trans)
  have g: "abs1 M (\<lambda>a. case largestIndExcl a j N ps of None \<Rightarrow> s a | Some i \<Rightarrow> trans1 (ps i) s a) w =
            (case largestIndExcl w j M (\<lambda>i. absTransfStatement env M (ps i)) of
               None \<Rightarrow> abs1 M s w
             | Some i \<Rightarrow> abs1 M (trans1 (ps i) s) w)" for w
    unfolding abs1Eq using e f
    by (smt option.case_eq_if option.collapse)
  show ?case
    apply auto apply (rule ext)
    subgoal for w
      unfolding g
      apply (cases "largestIndExcl w j M (\<lambda>i. absTransfStatement env M (ps i))")
       apply auto
      subgoal premises pre for i
      proof -
        have "i \<le> N"
          using pre largestIndExclSome a assms by auto
        then show ?thesis
          using d by simp
      qed
      done
    apply (rule ext)
    subgoal for w
      unfolding g apply (cases "largestIndExcl w j M (\<lambda>i. absTransfStatement env M (ps i))")
       apply auto
       apply (smt (verit, best) a assms b(1) c largestIndExclNone largestIndNone le_trans
                  option.simps(4) varOfStmtBoundAssignValid)
      subgoal premises pre for i
      proof -
        have b1: "i \<le> N"
          using pre largestIndExclSome a assms by auto
        have b2: "largestIndExcl w j M (\<lambda>i. absTransfStatement env M (ps i)) = Some i"
          using pre by auto
        have b3: "i \<le> M" "i \<noteq> j" "w \<in> varOfStmt (absTransfStatement env M (ps i))"
          "(\<forall>k\<le>M. k > i \<and> k \<noteq> j \<longrightarrow> w \<notin> varOfStmt (absTransfStatement env M (ps k)))"
          using b2 largestIndExclSome by auto
        have b4: "largestInd w M (\<lambda>i. absTransfStatement env M (ps i)) = Some i"
          unfolding largestIndSome using b3 a assms c pre(1) by auto
        show ?thesis
          by (simp add: b1 b4 d)
      qed
      done
    done
qed

lemma Dabs1Eq:
  "Dabs1 s  v = (if   v = dontCareVar then dontCare else DabsTransfConst  (s v))"
  apply (cases v) apply auto done

lemma DabsStatement:  
  assumes "env dontCareVar =anyType"
  shows "DwellFormedStatement env  S \<Longrightarrow>
         fitEnv s env \<Longrightarrow> deriveStmt env S \<Longrightarrow>
         Dabs1  (trans1 S s) = trans1 (DabsTransfStatement env  S) (Dabs1  s)"

proof (induction S)
case skip
  then show ?case  by auto
next
  case (assign x)
  have "fst x\<noteq>dontCareVar"
    using assign.prems(1) by auto

  have "DabsTransfExp env  (snd x) \<noteq> dontCareExp "
    using DwellAssign assign.prems(1) by blast
    
   
  show ?case
  proof(cases x,auto,unfold snd_def,auto,rule)
    fix v e w
    assume "x=(v,e)"
    have d1:"deriveExp env e\<noteq>None"
      by (metis \<open>x = (v, e)\<close> assign.prems(3) deriveStmt.simps(2) sndI)
    have d2:"DabsTransfExp env  e \<noteq> dontCareExp "
      using \<open>DabsTransfExp env (snd x) \<noteq> dontCareExp\<close> \<open>x = (v, e)\<close> by auto
    show "Dabs1 (\<lambda>c. if v = c then expEval e s else s c) w =
       (if v = w then expEval (DabsTransfExp env e) (Dabs1 s) else Dabs1 s w)"
    proof(cases "w=v")
      case True
      then show ?thesis 
        apply auto
        apply(cases v)
        apply auto
        apply (simp add: DabsTransfFormSim assign.prems(2) assms d1 d2)
        apply (simp add: DabsTransfFormSim assign.prems(2) assms d1 d2)
        using \<open>fst x \<noteq> dontCareVar\<close> \<open>x = (v, e)\<close> by force 
         
    next
      case False
      then show ?thesis
        by (smt (verit, ccfv_SIG) Dabs1.elims Dabs1.simps(1) Dabs1.simps(2))  
        
    qed 
  qed
next
  case (parallel S1 S2)
   
  have a: "DwellFormedStatement env  S1" "DwellFormedStatement env  S2"
    using parallel(3) by auto
  have a2:"deriveStmt env S1" "deriveStmt env S2"
    using deriveStmt.simps(3) parallel.prems(3) by blast+
  have b: "v \<in> varOfStmt (DabsTransfStatement env  S1) \<longleftrightarrow> 
           v \<in> varOfStmt S1  " for v
    using a(1) a2(1) parallel.prems(2) varOfStmtDAbs by blast 
  have c: "Dabs1  (\<lambda>a. if a \<in> varOfStmt S1 then trans1 S1 s a else trans1 S2 s a) w =
           (if w \<in> varOfStmt (DabsTransfStatement env  S1) then
              Dabs1  (trans1 S1 s) w
            else
              Dabs1  (trans1 S2 s) w)" for w
    apply(case_tac " w \<in> varOfStmt (DabsTransfStatement env  S1)")
     apply auto
    apply(cases w)
    using a(1) a2(1) parallel.prems(2) varOfStmtDAbs apply auto[1]
    using a(1) a2(1) parallel.prems(2) varOfStmtDAbs apply force
     apply force
    apply(cases w)
    apply (simp add: b)
    apply (simp add: b)
    using Dabs1.simps(3) by presburger 
  show ?case
    using parallel c by auto
next
  case (iteStm b S1 S2)
  
  have "DsafeForm env  b"
    using iteStm(3) by auto
  then have a1: "formEval (DabsTransfForm env  b) (Dabs1  s) = formEval b s"
    using DsafeEval1 assms iteStm.prems(2) by blast 
  show ?case
    apply (auto simp add: a1)
    apply (rule ext)
    using iteStm by auto

next
  case (forallStm ps N) 
  
  (*have a: "n = N"
    using forallStm(2) by auto*)
  have b: "boundAssign i (ps i)" "DwellFormedStatement env  (ps i)" if "i\<le>N" for i
    using forallStm.prems(1) that apply fastforce
    using forallStm.prems(1) that by auto
  have b1:"fitEnv s env" 
    by (simp add: forallStm.prems(2))
  have c: "i \<le> N \<longrightarrow>
           (v \<in> varOfStmt (DabsTransfStatement env  (ps i)) \<longleftrightarrow>
            v \<in> varOfStmt (ps i) )" for v i
    apply (rule impI)
    using b(2) forallStm.prems(2) forallStm.prems(3) varOfStmtDAbs by force 
  have d: "i \<le> N \<longrightarrow>
           Dabs1  (trans1 (ps i) s) = trans1 (DabsTransfStatement env  (ps i)) (Dabs1  s)" for i
    using forallStm(1)[OF _ b(2)] apply auto
    using deriveStmt.simps(5) forallStm.prems(2) forallStm.prems(3)
    by blast

  have d1: "i \<le> N \<longrightarrow>
           Dabs1  (trans1 (ps i) s) = trans1 (DabsTransfStatement env  (ps i)) (Dabs1  s)" for i
    using forallStm(1)[OF _ b(2)] apply auto
    using deriveStmt.simps(5) forallStm.prems(2) forallStm.prems(3)
    by blast
  have e: "largestInd v N (\<lambda>i. DabsTransfStatement env  (ps i)) = None \<longleftrightarrow>
           largestInd v N ps = None \<or>   v = dontCareVar" for v
    unfolding largestIndNone c apply auto
    using c apply blast
    using c apply blast
    using b(1) c varOfStmtBoundAssign by blast 
  have f: "largestInd v N (\<lambda>j. DabsTransfStatement env  (ps j)) = Some i \<longleftrightarrow>
           largestInd v N ps = Some i  \<and> v ~= dontCareVar" for v i
    unfolding largestIndSome c apply auto
    using c apply blast
    using c apply blast
    apply (meson absTransfVar.simps(3) b(1) c varOfStmtBoundAssignValid)
    using c apply blast
    using c by blast 
  have g: "Dabs1  (\<lambda>a. case largestInd a N ps of None \<Rightarrow> s a | Some i \<Rightarrow> trans1 (ps i) s a) w =
            (case largestInd w N (\<lambda>i. DabsTransfStatement env  (ps i)) of
               None \<Rightarrow> Dabs1  s w
             | Some i \<Rightarrow> Dabs1  (trans1 (ps i) s) w)" for w
    unfolding Dabs1Eq using e f
    by (smt option.case_eq_if option.collapse)
  have h:"i \<le> N \<longrightarrow>(ps i) = DabsTransfStatement env  (ps i)"  for i
    using b
    using DwellForall assms deriveStmt.simps(5) forallStm.prems(1) forallStm.prems(3) nonDataAssignDabs by presburger 
  show ?case
    apply auto apply (rule ext)
    subgoal for w
      unfolding g
      apply (cases "largestInd w N (\<lambda>i. DabsTransfStatement env  (ps i))")
       apply auto
       apply (metis c largestIndNone option.simps(4))
      using f apply simp
      subgoal premises pre for i
      proof -
        have "i \<le> N"
          using largestIndSome pre by blast 
        then show ?thesis
          using d1 h by presburger 
      qed
      done
    done 
next
  case (forallStmExcl ps j N) 
  have b: "boundAssign i (ps i)" "DwellFormedStatement env  (ps i)" if "i\<le>N" for i
    using forallStmExcl.prems(1) that apply fastforce
    using forallStmExcl.prems(1) that by auto
  have b1:"fitEnv s env" 
    by (simp add: forallStmExcl.prems(2))
  have c: "i \<le> N \<longrightarrow>
           (v \<in> varOfStmt (DabsTransfStatement env  (ps i)) \<longleftrightarrow>
            v \<in> varOfStmt (ps i))" for v i
    apply (rule impI)
    using b(2) forallStmExcl.prems(2) forallStmExcl.prems(3) varOfStmtDAbs by auto 
  have d: "i \<le> N \<Longrightarrow>
           Dabs1  (trans1 (ps i) s) = trans1 (DabsTransfStatement env  (ps i)) (Dabs1  s)" for i
    using forallStmExcl(1)[OF _ b(2)] apply auto
    using deriveStmt.simps(5) forallStmExcl
    by (meson deriveStmt.simps(6))
  have e: "largestIndExcl v j N (\<lambda>i. DabsTransfStatement env  (ps i)) = None \<longleftrightarrow>
           largestIndExcl v j N ps = None \<or>   v = dontCareVar" for v
    unfolding largestIndExclNone c apply auto
      apply (metis absTransfVar.simps(2) b(1) c leI varOfStmtBoundAssign)
    apply (meson c)
    using b(1) c varOfStmtBoundAssign by blast  
  have f: "largestIndExcl v j N (\<lambda>j. DabsTransfStatement env  (ps j)) = Some i \<longleftrightarrow>
           largestIndExcl v j N ps = Some i \<and>   v \<noteq> dontCareVar" for v i
    unfolding largestIndExclSome c apply auto
    using c apply blast
    using c apply blast
    apply (meson absTransfVar.simps(3) b(1) c varOfStmtBoundAssignValid)
    using c apply presburger
    using c by blast 
  have g: "Dabs1  (\<lambda>a. case largestIndExcl a j N ps of None \<Rightarrow> s a | Some i \<Rightarrow> trans1 (ps i) s a) w =
            (case largestIndExcl w j N  (\<lambda>i. DabsTransfStatement env  (ps i)) of
               None \<Rightarrow> Dabs1  s w
             | Some i \<Rightarrow> Dabs1  (trans1 (ps i) s) w)" for w
    unfolding Dabs1Eq using e f
    by (smt option.case_eq_if option.collapse)
  have h:"i \<le> N \<longrightarrow>(ps i) = DabsTransfStatement env  (ps i)"  for i
    using b
    using DwellForallExcl assms deriveStmt.simps(6) forallStmExcl.prems(1) forallStmExcl.prems(3) nonDataAssignDabs by presburger
  show ?case
    apply auto apply (rule ext)
    subgoal for w
      unfolding g
      apply (cases "largestIndExcl w j N (\<lambda>i. DabsTransfStatement env  (ps i))")
       apply auto
      apply (simp add: c largestIndExclNone option.case_eq_if)
      subgoal premises pre for i
      proof -
        have "i \<le> N"
          using largestIndExclSome pre by blast 
        then show ?thesis
          using d f h pre by auto 
      qed
      done
    done
qed
     

subsection \<open>Simplified abstraction for statement\<close>

primrec absTransfStatement2 :: "envType\<Rightarrow>nat \<Rightarrow> statement \<Rightarrow> statement" where
  "absTransfStatement2 env M skip = skip" |
  "absTransfStatement2 env M (assign as) = 
    (if absTransfVar M (fst as) = dontCareVar 
     then skip
     else assign (fst as, absTransfExp env M (snd as)))" |
  "absTransfStatement2 env M (S1 || S2) =
  (let s1=absTransfStatement2 env M S1 in
   let s2=absTransfStatement2 env M S2 in
    if s1 = skip then s2 else if s2 = skip then s1 else s1 || s2)" |
  "absTransfStatement2 env M (iteStm b S1 S2) =
  (let s1=absTransfStatement2 env M S1 in
   let s2=absTransfStatement2 env M S2 in
    if s1 = skip \<and> s2 = skip then skip else
    iteStm (absTransfForm env M b) s1 s2)" |
  "absTransfStatement2 env M (forallStm PS N) =
    forallStm PS M" |
  "absTransfStatement2 env M (forallStmExcl PS j N) =
    (if j \<le> M then forallStmExcl PS j M
     else forallStm PS M)"
 
lemma absStatementEq:
  assumes "M \<le> N"
  shows "wellFormedStatement env N S \<Longrightarrow>
         fitEnv s env \<Longrightarrow>
         deriveStmt env S \<Longrightarrow>
         equivStatement (absTransfStatement env M S) (absTransfStatement2 env M S)"
proof (induction S)
  case (parallel S1 S2)   
  have a1:"deriveStmt env S1 \<and> deriveStmt env S2"
    using deriveStmt.simps(3) parallel.prems(3) by blast  
  have a: "equivStatement (absTransfStatement env M S1) (absTransfStatement2 env M S1)"
    using a1 parallel.IH(1) parallel.prems(1) parallel.prems(2) wellFormedStatement.simps(3) by blast 
  have b: "equivStatement (absTransfStatement env M S2) (absTransfStatement2 env M S2)"
    using a1 parallel.IH(2) parallel.prems(1) parallel.prems(2) wellFormedStatement.simps(3) by blast
  have c: "equivStatement
            (absTransfStatement env M S1 || absTransfStatement env M S2)
            (absTransfStatement2 env M S1 || absTransfStatement2 env M S2)"
    using a b by (auto intro: equivStatementParallel)
  show ?case
    apply (cases "absTransfStatement2 env M S1 = skip")
    subgoal
      apply auto apply (rule equivStatementTrans[OF c])
      using b equivStatementSkipLeft equivStatementTrans by auto
    apply (cases "absTransfStatement2 env M S2 = skip")
    subgoal
      apply auto apply (rule equivStatementTrans[OF c])
      by (metis equivStatementSkipRight)
    using c by auto
next
  case (iteStm b S1 S2)
  show ?case
    using iteStm by (auto simp add: Let_def equivStatement_def)
next
  case (forallStm ps N')
  have a1: "N' = N"
    using forallStm.prems(1) by force
  have a2: "\<And>i. i \<le> N \<longrightarrow> deriveStmt env (ps i)"
    using \<open>N' = N\<close> deriveStmt.simps(5) forallStm.prems(3) by blast
  show ?case
    apply auto
    apply (rule equivStatementForallAbs)
    using forallStm.prems(1) apply auto[1]
    apply(cut_tac a2,simp)
    by (simp add: assms) 
next
  case (forallStmExcl ps j N')
  have a1: "N' = N"
    using forallStmExcl.prems(1) by force
  have a2: "\<And>i. i \<le> N \<longrightarrow> deriveStmt env (ps i)"
    using a1 deriveStmt.simps(6) forallStmExcl.prems(3) by blast
  show ?case
    apply auto
     apply (rule equivStatementForallExclAbs)
    using forallStmExcl.prems(1) apply auto[1]
    apply(cut_tac a2,simp)
    apply (simp add: assms) 
    by (meson a2 assms equivStatementBoundAssign equivStatementForall forallStmExcl.prems(1)
              le_trans wellForallExcl)
qed (auto)

lemma absStatement2:
  assumes "M \<le> N"
  shows "wellFormedStatement env N S \<Longrightarrow> 
        fitEnv s env \<Longrightarrow>
        deriveStmt env S \<Longrightarrow>
         abs1 M (trans1 S s) = trans1 (absTransfStatement2 env M S) (abs1 M s)"
  using absStatement absStatementEq assms equivStatement_def by auto


subsection \<open>Abstraction of rules, simulation relation\<close>

fun topTransfForm :: "formula \<Rightarrow> formula" where
  "topTransfForm f = (if f = dontCareForm then chaos else f)"

fun wellFormedRule :: "envType \<Rightarrow>nat \<Rightarrow> rule \<Rightarrow> bool" where
  "wellFormedRule env M (guard g a) = wellFormedStatement env M a"

fun DwellFormedRule :: "envType   \<Rightarrow> rule \<Rightarrow> bool" where
  "DwellFormedRule env  (guard g a) = DwellFormedStatement env  a"

lemma strengthenRule2Keep:
  "wellFormedRule env N r \<Longrightarrow> wellFormedRule env N (strengthenRuleByFrmL2 f r)"
proof (induction f arbitrary: r)
  case Nil
  then show ?case by auto
next
  case (Cons a f)
  show ?case
    apply auto apply (cases r)
    by (metis Cons.IH Cons.prems strengthenRule2.simps wellFormedRule.elims(2) wellFormedRule.simps)
qed


lemma strengthenRule2KeepD:
  "DwellFormedRule env  r \<Longrightarrow> DwellFormedRule env  (strengthenRuleByFrmL2 f r)"
proof (induction f arbitrary: r)
  case Nil
  then show ?case by auto
next
  case (Cons a f)
  show ?case
    apply auto apply (cases r)
    by (metis Cons.prems DwellFormedRule.simps act.simps equivRule.elims(2) strengthenRule2.simps strengthenRuleByFrmL2Act strengthenRuleByFrml2Equiv)
 qed

primrec deriveRule :: "envType \<Rightarrow> rule \<Rightarrow> bool" where
  "deriveRule env (guard g S) = (deriveForm env g \<and> deriveStmt env S)"

fun absTransfRule :: "envType \<Rightarrow> nat \<Rightarrow> rule \<Rightarrow> rule" where
  "absTransfRule env M (guard g a) =
    (let b = absTransfStatement2 env M a in
     (if b = skip then (guard chaos skip)
      else guard (topTransfForm (absTransfForm env M g)) b))"

fun DabsTransfRule :: "envType   \<Rightarrow> rule \<Rightarrow> rule" where
  "DabsTransfRule env  (guard g a) =
    (let b = DabsTransfStatement env  a  in
     guard (  (DabsTransfForm env  g)) b)"

definition transSimRule :: "envType \<Rightarrow> rule \<Rightarrow> rule \<Rightarrow> nat \<Rightarrow> bool" where
  "transSimRule env r1 r2 M =
    (\<forall>s. fitEnv s env \<longrightarrow> deriveRule env r1\<longrightarrow>
      formEval (pre r1) s \<longrightarrow> formEval (pre r2) (abs1 M s) \<and>
         abs1 M (trans1 (act r1) s) = trans1 (act r2) (abs1 M s))"

definition DtransSimRule :: "envType \<Rightarrow> rule \<Rightarrow> rule  \<Rightarrow> bool" where
  "DtransSimRule env r1 r2  =
    (\<forall>s. fitEnv s env \<longrightarrow> deriveRule env r1\<longrightarrow>
      formEval (pre r1) s \<longrightarrow> formEval (pre r2) (Dabs1  s) \<and>
         Dabs1  (trans1 (act r1) s) = trans1 (act r2) (Dabs1  s))"

lemma absRuleSim:
  assumes "M \<le> N"
  shows "wellFormedRule env N r \<Longrightarrow> transSimRule env r (absTransfRule env M r) M"
proof(unfold transSimRule_def, auto)
  fix sa
  assume a1:"wellFormedRule env N r " and  
         a3:" fitEnv sa env" and
         a4:" deriveRule env r " and a5:" formEval (pre r) sa"
  show "formEval (pre (absTransfRule env M r)) (abs1 M sa)"
  proof (cases r)
    fix g a
    assume b0:"r=guard g a" 
    have b2:"deriveForm env g"
      using \<open>r = (g \<triangleright> a)\<close> a4 deriveRule.simps by blast
    show "formEval (pre (absTransfRule env M r)) (abs1 M sa)"
      using a3 a5 absTransfFormSim b0 b2 by (auto simp add: Let_def)
  qed
next
  fix s
  assume a1:"wellFormedRule env N r " and 
         a3:" fitEnv s env" and
         a4:" deriveRule env r " and a5:" formEval (pre r) s"
  show "abs1 M (trans1 (act r) s) = trans1 (act (absTransfRule env M r)) (abs1 M s)"
   proof (cases r)
    fix g a
    assume b0:"r=guard g a" 
    have b2:"deriveForm env g"
      using \<open>r = (g \<triangleright> a)\<close> a4 deriveRule.simps by blast
    show "abs1 M (trans1 (act r) s) = trans1 (act (absTransfRule env M r)) (abs1 M s)"
      using a1 a3 a4 absStatement2 assms b0 by (auto simp add: Let_def)
  qed
qed


lemma DabsRuleSim: assumes "env dontCareVar =anyType"
  shows "DwellFormedRule env  r \<Longrightarrow> DtransSimRule env r (DabsTransfRule env  r) "
proof(unfold DtransSimRule_def, auto)
  fix sa
  assume a1:"DwellFormedRule env  r " and  
         a3:" fitEnv sa env" and
         a4:" deriveRule env r " and a5:" formEval (pre r) sa"
  show "formEval (pre (DabsTransfRule env  r)) (Dabs1  sa)"
  proof (cases r)
    fix g a
    assume b0:"r=guard g a" 
    have b2:"deriveForm env g"
      using \<open>r = (g \<triangleright> a)\<close> a4 deriveRule.simps by blast
    show "formEval (pre (DabsTransfRule env   r)) (Dabs1   sa)"
      by (metis DabsTransfFormSim DabsTransfRule.simps a3 a5 assms b0 b2 evalDontCareForm pre.simps)
    
  qed
next
  fix s
  assume a1:"DwellFormedRule env  r " and 
         a3:" fitEnv s env" and
         a4:" deriveRule env r " and a5:" formEval (pre r) s"
  show "Dabs1  (trans1 (act r) s) = trans1 (act (DabsTransfRule env  r)) (Dabs1  s)"
   proof (cases r)
    fix g a
    assume b0:"r=guard g a" 
    have b2:"deriveForm env g"
      using \<open>r = (g \<triangleright> a)\<close> a4 deriveRule.simps by blast
    show "Dabs1  (trans1 (act r) s) = trans1 (act (DabsTransfRule env  r)) (Dabs1  s)"
      using DabsStatement a1 a3 a4 assms b0 by auto 
  qed
qed


definition transSimRules :: "envType\<Rightarrow>rule set \<Rightarrow> rule set \<Rightarrow> nat \<Rightarrow> bool" where
  "transSimRules env rs1 rs2 M = (\<forall>r\<in>rs1. \<exists>r'\<in>rs2. transSimRule env r r' M)"


definition DtransSimRules :: "envType\<Rightarrow>rule set \<Rightarrow> rule set   \<Rightarrow> bool" where
  "DtransSimRules env rs1 rs2  = (\<forall>r\<in>rs1. \<exists>r'\<in>rs2. DtransSimRule env r r' )"

text \<open>f2 simulates f1 on the abstract state\<close>
definition predSim :: "envType\<Rightarrow>formula \<Rightarrow> formula \<Rightarrow> nat \<Rightarrow> bool" where
  "predSim env f1 f2 M = 
  (\<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow>formEval f1 s \<longrightarrow> formEval f2 (abs1 M s))"

definition predSimSet :: "envType\<Rightarrow> formula set \<Rightarrow> formula set \<Rightarrow> nat \<Rightarrow> bool" where
  "predSimSet env fs1 fs2 M = (\<forall>f2\<in>fs2. \<exists>f1\<in>fs1. predSim env f1 f2 M)"


definition DpredSim :: "envType\<Rightarrow>formula \<Rightarrow> formula   \<Rightarrow> bool" where
  "DpredSim env f1 f2  = 
  (\<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow>formEval f1 s \<longrightarrow> formEval f2 (Dabs1  s))"

definition DpredSimSet :: "envType\<Rightarrow> formula set \<Rightarrow> formula set   \<Rightarrow> bool" where
  "DpredSimSet env fs1 fs2   = (\<forall>f2\<in>fs2. \<exists>f1\<in>fs1. DpredSim env f1 f2  )"

lemma transSimRulesReachable:
  assumes "predSimSet env fs1 fs2 M"
    and "transSimRules env rs1 rs2 M" 
    and "\<And>r. r \<in> rs1 \<longrightarrow> deriveRule env r"
    and "\<And>f. f \<in> fs1 \<longrightarrow> deriveForm env f"
    and "\<forall>s i. reachableUpTo fs1 rs1 i s \<longrightarrow> fitEnv s env"
  shows "reachableUpTo fs1 rs1 i s \<Longrightarrow> reachableUpTo fs2 rs2 i (abs1 M s)"
proof (induction i arbitrary: s)
  case 0
  have a: "formEval f1 s" if "f1 \<in> fs1" for f1
    using reachableUpTo0[OF 0] that by auto
  have b: "formEval f2 (abs1 M s)" if assmb: "f2 \<in> fs2" for f2
  proof -
    obtain f1 where b1: "f1 \<in> fs1" "predSim env f1 f2 M"
      using assms(1) unfolding predSimSet_def using assmb by auto
    have b2:"deriveForm env f1"
      using assms(4) b1(1) by blast
    have b3:"fitEnv s env"
      using "0.prems" assms(5) by blast
    with b1 b2 show ?thesis
      unfolding predSim_def using a(1) by auto
  qed
  show ?case
    apply (rule reachableSet0)
    using b by auto
next
  case (Suc i)
  obtain s' g a where a: "s = trans1 a s'" "reachableUpTo fs1 rs1 i s'" "(g \<triangleright> a) \<in> rs1" "formEval g s'"
    using reachableUpToSuc[OF Suc(2)] by metis
  obtain r2 where b: "r2 \<in> rs2" "transSimRule env (g \<triangleright> a) r2 M"
    using assms(2) a(3) unfolding transSimRules_def by auto
  have c0:"fitEnv s' env"
    using a(2) assms(5) by blast 
  have c: "formEval (pre r2) (abs1 M s')"
    using a(3) a(4) assms(3) b(2) c0 transSimRule_def by fastforce
  have d: "abs1 M (trans1 a s') = trans1 (act r2) (abs1 M s')"
    using a(3) a(4) assms(3) b(2) c0 transSimRule_def by fastforce
  have e: "reachableUpTo fs2 rs2 i (abs1 M s')"
    by (rule Suc(1)[OF a(2)])
  show ?case
    unfolding a(1) d
    apply (rule reachableSetNext[OF e _ c])
    using b(1) apply (cases r2) by auto
qed



lemma DtransSimRulesReachable:
  assumes "DpredSimSet env fs1 fs2 "
    and "DtransSimRules env rs1 rs2 " 
    and "\<And>r. r \<in> rs1 \<longrightarrow> deriveRule env r"
    and "\<And>f. f \<in> fs1 \<longrightarrow> deriveForm env f"
    and "\<forall>s i. reachableUpTo fs1 rs1 i s \<longrightarrow> fitEnv s env"
  shows "reachableUpTo fs1 rs1 i s \<Longrightarrow> reachableUpTo fs2 rs2 i (Dabs1  s)"
proof (induction i arbitrary: s)
  case 0
  have a: "formEval f1 s" if "f1 \<in> fs1" for f1
    using reachableUpTo0[OF 0] that by auto
  have b: "formEval f2 (Dabs1  s)" if assmb: "f2 \<in> fs2" for f2
  proof -
    obtain f1 where b1: "f1 \<in> fs1" "DpredSim env f1 f2 "
      using assms(1) unfolding DpredSimSet_def using assmb by auto
    have b2:"deriveForm env f1"
      using assms(4) b1(1) by blast
    have b3:"fitEnv s env"
      using "0.prems" assms(5) by blast
    with b1 b2 show ?thesis
      unfolding DpredSim_def using a(1) by auto
  qed
  show ?case
    apply (rule reachableSet0)
    using b by auto
next
  case (Suc i)
  obtain s' g a where a: "s = trans1 a s'" "reachableUpTo fs1 rs1 i s'" "(g \<triangleright> a) \<in> rs1" "formEval g s'"
    using reachableUpToSuc[OF Suc(2)] by metis
  obtain r2 where b: "r2 \<in> rs2" "DtransSimRule env (g \<triangleright> a) r2"
    using assms(2) a(3) unfolding DtransSimRules_def by auto
  have c0:"fitEnv s' env"
    using a(2) assms(5) by blast 
  have c: "formEval (pre r2) (Dabs1  s')"
    using a(3) a(4) assms(3) b(2) c0 DtransSimRule_def by fastforce
  have d: "Dabs1  (trans1 a s') = trans1 (act r2) (Dabs1  s')"
    using a(3) a(4) assms(3) b(2) c0 DtransSimRule_def by fastforce
  have e: "reachableUpTo fs2 rs2 i (Dabs1  s')"
    by (rule Suc(1)[OF a(2)])
  show ?case
    unfolding a(1) d
    apply (rule reachableSetNext[OF e _ c])
    using b(1) apply (cases r2) by auto
qed

definition oneParamCons :: "nat \<Rightarrow> (nat \<Rightarrow> rule) \<Rightarrow> rule set" where [simp]:
  "oneParamCons N pr \<equiv> {r. \<exists>i. i \<le> N \<and> r = pr i}"

definition twoParamsCons :: "nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> rule) \<Rightarrow> rule set" where [simp]:
  "twoParamsCons N pr \<equiv>  {r. \<exists>i j. i \<le> N \<and> j \<le> N \<and> r = pr i j}"

lemma symParaRuleInfSymRuleSet: 
  assumes a: "symParamRule N pr"
  shows "symProtRules' N (oneParamCons N pr)"
proof (unfold symProtRules'_def,(rule allI)+,rule)
  fix p r
  assume a1: "p permutes {x. x \<le> N} \<and> r \<in> oneParamCons N pr"
  from a1 have a2: "\<exists>i. i \<le> N \<and> r = pr i"
    by (unfold oneParamCons_def, auto)
  then obtain i where a3: "i \<le> N \<and> r = pr i"
    by blast
  have a4: "p i \<le> N"
    using a3 local.a1 permutes_in_image by fastforce 
  show "\<exists>r'. r' \<in> oneParamCons N pr \<and> equivRule (applySym2Rule p r) r'"
    apply (cut_tac a a1 a3, unfold symParamRule_def)
    apply (rule_tac x="pr (p i)" in exI)
    apply auto
    using a4 oneParamCons_def by auto
qed

lemma DsymParaRuleInfSymRuleSet: 
  assumes a: "DsymParamRule N pr"
  shows "DsymProtRules' N (oneParamCons N pr)"
proof (unfold DsymProtRules'_def,(rule allI)+,rule)
  fix p r
  assume a1: "p permutes {x. x \<le> N} \<and> r \<in> oneParamCons N pr"
  from a1 have a2: "\<exists>i. i \<le> N \<and> r = pr i"
    by (unfold oneParamCons_def, auto)
  then obtain i where a3: "i \<le> N \<and> r = pr i"
    by blast
  have a4: "p i \<le> N"
    using a3 local.a1 permutes_in_image by fastforce 
  show "\<exists>r'. r' \<in> oneParamCons N pr \<and> equivRule (applyDSym2Rule p r) r'"
    apply (cut_tac a a1 a3, unfold DsymParamRule_def)
    apply (rule_tac x="pr (p i)" in exI)
    apply auto
    using a4 oneParamCons_def by auto
qed

lemma symParaRuleInfSymRuleSet2:
  assumes a: "symParamRule2' N pr" 
  shows "symProtRules' N (twoParamsCons N pr)"
proof (unfold symProtRules'_def,(rule allI)+,rule)
  fix p r
  assume a1: "p permutes {x. x \<le> N} \<and> r \<in> twoParamsCons N pr"
  from a1 have a2: "\<exists>i j. i \<le> N \<and>j \<le>N  \<and>r = pr i j" (*\<and> i\<noteq>j*)
    by (unfold twoParamsCons_def, auto)
  then obtain i j where a3: "i \<le> N \<and>j \<le>N  \<and>r = pr i j" (*\<and>  i\<noteq>j*)
    by blast
  have a4: "p i  \<le> N \<and> p j \<le>N " 
    using a3 local.a1 permutes_in_image by fastforce 
  show "\<exists>r'. r' \<in> twoParamsCons N pr \<and> equivRule (applySym2Rule p r) r'"
    apply (cut_tac a a1 a3, unfold symParamRule2'_def)
    apply (rule_tac x="pr (p i) (p j)" in exI)
    apply auto
    using a4 apply blast
    done
  qed 

theorem symProtRulesUnion:
  assumes a1:"symProtRules' N A" and a2:"symProtRules' N B"
  shows "symProtRules' N (A \<union> B)"
  by (metis UnCI UnE a2 local.a1 symProtRules'_def)

theorem symPredsUnion:
  assumes a1:"symPredSet' N A" and a2:"symPredSet' N B"
  shows "symPredSet' N (A \<union> B)"
  using a2 local.a1 by fastforce 


theorem DsymProtRulesUnion:
  assumes a1:"DsymProtRules' N A" and a2:"DsymProtRules' N B"
  shows "DsymProtRules' N (A \<union> B)"
  by (metis UnCI UnE a2 local.a1 DsymProtRules'_def)

theorem DsymPredsUnion:
  assumes a1:"DsymPredSet' N A" and a2:"DsymPredSet' N B"
  shows "DsymPredSet' N (A \<union> B)"
  using a2 local.a1 by fastforce 

definition constrInv :: "((nat \<Rightarrow> formula) \<times> (nat \<Rightarrow> formula)) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where [simp]:
  "constrInv pair i j \<equiv> fst pair i \<longrightarrow>\<^sub>f \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<longrightarrow>\<^sub>f snd pair j"

definition constrInvByExcl :: "((nat \<Rightarrow> formula) \<times> (nat \<Rightarrow> formula)) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> formula" where
  "constrInvByExcl pair i N \<equiv> fst pair i \<longrightarrow>\<^sub>f forallFormExcl (snd pair) i N"

definition constrInvByExcls :: "((nat \<Rightarrow> formula) \<times> (nat \<Rightarrow> formula)) set \<Rightarrow> nat \<Rightarrow> formula set" where [simp]:
  "constrInvByExcls pairs N \<equiv>
    {f. \<exists>i pair. pair \<in> pairs \<and> i \<le> N \<and> f = (fst pair i \<longrightarrow>\<^sub>f forallFormExcl (snd pair) i N)}"

definition symPair :: "((nat \<Rightarrow> formula) \<times> (nat \<Rightarrow> formula)) \<Rightarrow> nat \<Rightarrow> bool" where [simp]:
  "symPair x N \<equiv> symParamForm N (fst x) \<and> symParamForm N (snd x)"

lemma permute_i:
  fixes N i  :: nat
  assumes   "i \<le> N"  
  shows "\<exists>p. p permutes {i. i \<le> N} \<and> p i = 0 "
proof -
  have a: ?thesis if assm_a: "i \<noteq> 1"
  proof -
    let ?p="Fun.swap i 0 id "
    have a1: "?p i = 0"
      using assms assm_a by (auto simp add: Fun.swap_def)
         show ?thesis
      apply (rule exI[where x="?p"])
      using a1 apply auto 
      apply (rule permutes_swap_id) using assms apply auto
      done
  qed
  have b: ?thesis if assm_b: "i = 1"
  proof -
    let ?p="Fun.swap i 0 id "
    have b1: "?p i = 0"
      using assms assm_b by (auto simp add: Fun.swap_def)  
    show ?thesis
      apply (rule exI[where x="?p"])
      using b1  apply auto 
      apply (rule permutes_swap_id) using assms apply auto 
      done
  qed
  show ?thesis
    using a b by auto
qed


lemma permute_inv_i:
  fixes N i  :: nat
  assumes   "i \<le> N"  
  shows "\<exists>p. p permutes {i. i \<le> N} \<and> p 0 = i "
proof -
  have a1: "\<exists>p. p permutes {i. i \<le> N} \<and> p i = 0  "
    using assms permute_i by presburger 

  then obtain p where a1:"p permutes {i. i \<le> N} \<and> p i = 0 "
    by blast
  let ?p="inv p"
  have "?p permutes {i. i \<le> N}"
    using local.a1 permutes_inv by blast
  show "\<exists>p. p permutes {i. i \<le> N} \<and> p 0 = i  "
    by (metis \<open>inv p permutes {i. i \<le> N}\<close> local.a1 permutes_inverses(2))
qed

lemma permute_ij:
  fixes N i j :: nat
  assumes "1 \<le> N" "i \<le> N" "j \<le> N" "i \<noteq> j"
  shows "\<exists>p. p permutes {i. i \<le> N} \<and> p i = 0 \<and> p j = 1"
proof -
  have a: ?thesis if assm_a: "i \<noteq> 1"
  proof -
    let ?p="Fun.swap i 0 id \<circ> Fun.swap j 1 id"
    have a1: "?p i = 0"
      using assms assm_a by (auto simp add: Fun.swap_def)
    have a2: "?p j = 1"
      using assm_a by (auto simp add: Fun.swap_def)
    show ?thesis
      apply (rule exI[where x="?p"])
      using a1 a2 apply auto
      apply (rule permutes_compose)
       apply (rule permutes_swap_id) using assms apply auto
      apply (rule permutes_swap_id) using assms by auto
  qed
  have b: ?thesis if assm_b: "i = 1"
  proof -
    let ?p="Fun.swap i 0 id \<circ> Fun.swap j 0 id"
    have b1: "?p i = 0"
      using assms assm_b by (auto simp add: Fun.swap_def)
    have b2: "?p j = 1"
      using assm_b by (auto simp add: Fun.swap_def)
    show ?thesis
      apply (rule exI[where x="?p"])
      using b1 b2 apply auto
      apply (rule permutes_compose)
       apply (rule permutes_swap_id) using assms apply auto
      apply (rule permutes_swap_id) using assms by auto
  qed
  show ?thesis
    using a b by auto
qed

lemma permute_inv_ij:
  fixes N i j :: nat
  assumes "1 \<le> N" "i \<le> N" "j \<le> N" "i \<noteq> j"
  shows "\<exists>p. p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 1 = j"
proof -
  have a1: "\<exists>p. p permutes {i. i \<le> N} \<and> p i = 0 \<and> p j = 1"
    using assms(2) assms(3) assms(4) permute_ij by auto
  then obtain p where a1:"p permutes {i. i \<le> N} \<and> p i = 0 \<and> p j = 1"
    by blast
  let ?p="inv p"
  have "?p permutes {i. i \<le> N}"
    using local.a1 permutes_inv by blast
  show "\<exists>p. p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 1 = j"
    by (metis \<open>inv p permutes {i. i \<le> N}\<close> local.a1 permutes_inverses(2))
qed

lemma symOnFuncInv:
  assumes a1: "symPair pair N"
    and a2: "1 \<le> N"
  shows "\<forall>i j. i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> i \<noteq> j \<longrightarrow>
    (\<exists>p. p permutes {i. i \<le> N} \<and> equivForm (applySym2Form p (constrInv pair 0 1)) (constrInv pair i j))"
proof ((rule allI)+,(rule impI)+)
  fix i j
  assume "i \<le> N" and "j \<le> N" and "i \<noteq> j"
  have "\<exists>p. p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 1 = j"
    using \<open>i \<le> N\<close> \<open>i \<noteq> j\<close> \<open>j \<le> N\<close> a2 permute_inv_ij by blast
  then obtain p where b1: "p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 1 = j"
    by blast
  show "\<exists>p. p permutes {i. i \<le> N} \<and> equivForm (applySym2Form p (constrInv pair 0 1)) (constrInv pair i j)"
  proof (rule_tac x=p in exI)
    show "p permutes {i. i \<le> N} \<and> equivForm (applySym2Form p (constrInv pair 0 1)) (constrInv pair i j)"
    proof(cut_tac a1, rule conjI)
      show "p permutes {i. i \<le> N}"
        using \<open>p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 1 = j\<close> by blast
    next
      have c1: "equivForm (applySym2Form p (fst pair 0)) (fst pair i)"
        using \<open>i \<le> N\<close> b1 local.a1 mem_Collect_eq symParamForm_def by fastforce
      have c2: "equivForm (applySym2Form p (snd pair 1)) (snd pair j)"
         using \<open>j \<le> N\<close> a2 b1 local.a1 symParamForm_def by fastforce
      show "equivForm (applySym2Form p (constrInv pair 0 1)) (constrInv pair i j)"
        apply (unfold constrInv_def,simp)
         apply (cut_tac c1 c2, unfold equivForm_def,auto)
         using One_nat_def b1 apply presburger
         using \<open>i \<noteq> j\<close> by blast
    qed
  qed
qed


lemma symOnFunc2:
  assumes a1: "symParamForm2 N f"
    and a2: "1 \<le> N"
  shows "\<forall>i j. i \<le> N \<longrightarrow> j \<le> N \<longrightarrow>
    (\<exists>p k. p permutes {i. i \<le> N} \<and> k \<le> 1 \<and> equivForm (applySym2Form p (f 0 k)) (f i j))"
proof ((rule allI)+,(rule impI)+)
  fix i j
  assume "i \<le> N" and "j \<le> N" 
  have "i \<noteq> j \<or> i = j" by blast
  moreover
  {assume b0: "i \<noteq> j" 
    have "\<exists>p. p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 1 = j"
      using \<open>i \<le> N\<close> \<open>i \<noteq> j\<close> \<open>j \<le> N\<close> a2 permute_inv_ij by blast
    then obtain p where b1: "p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 1 = j"
      by blast
    have "\<exists>p k. p permutes {i. i \<le> N} \<and> k\<le>1 \<and> equivForm (applySym2Form p (f 0 k)) (f i j)"
    proof (rule_tac x="p" in exI)
      show "\<exists>k. p permutes {i. i \<le> N}\<and> k\<le>1 \<and> equivForm (applySym2Form p (f 0 k)) (f i j)"
      proof (rule_tac x="1" in exI)
        show "p permutes {i. i \<le> N}\<and> 1\<le>(1::nat) \<and> equivForm (applySym2Form p (f 0 1)) (f i j)"
        proof (cut_tac a1, rule conjI)
          show "p permutes {i. i \<le> N}"
            using \<open>p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 1 = j\<close> by blast
        next
          show "1 \<le> (1::nat) \<and> equivForm (applySym2Form p (f 0 1)) (f i j)"
            using a1 a2 b1 b0 symParamForm2_def by auto        
        qed
      qed
    qed
  }
  moreover
  {assume b0: "i = j" 
    have "\<exists>p. p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 0 = j"
      by (metis \<open>i \<le> N\<close> a2 b0 le0 permute_inv_ij zero_neq_one) 
    then obtain p where b1: "p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 0 = j"
      by blast
    have "\<exists>p k. p permutes {i. i \<le> N} \<and> k\<le>1 \<and> equivForm (applySym2Form p (f 0 k)) (f i j)"
    proof (rule_tac x="p" in exI)
      show "\<exists>k. p permutes {i. i \<le> N}\<and> k\<le>1 \<and> equivForm (applySym2Form p (f 0 k)) (f i j)"
      proof (rule_tac x="0" in exI)
        show "p permutes {i. i \<le> N}\<and> 0\<le>(1::nat) \<and> equivForm (applySym2Form p (f 0 0)) (f i j)"
        proof (cut_tac a1, rule conjI)
          show "p permutes {i. i \<le> N}"
            using \<open>p permutes {i. i \<le> N} \<and> p 0 = i \<and> p 0 = j\<close> by blast
        next
          show "0 \<le> (1::nat) \<and> equivForm (applySym2Form p (f 0 0)) (f i j)"
            using a1 a2 b1 b0 symParamForm2_def by auto        
        qed
      qed
    qed
  }
  ultimately show "\<exists>p k. p permutes {i. i \<le> N} \<and> k \<le> 1 \<and> equivForm (applySym2Form p (f 0 k)) (f i j)"
    by blast
qed

lemma SymLemmaOnExcl:
  assumes "symPredSet' N Is"
    and "symProtRules' N rs"
    and "1 \<le> N"
    and "symPair pair N"
    and "reachableUpTo Is rs k s"
    and "\<forall>s i l. l \<le> 1 \<longrightarrow> reachableUpTo Is rs i s \<longrightarrow> formEval (constrInv pair 0 l) s"
    and "i \<le> N"
  shows "formEval (constrInvByExcl pair i N) s"
proof (simp add: constrInvByExcl_def, rule+)
  fix j
  assume b1: "formEval (fst pair i) s" and b2: "j \<noteq> i" and b3: "j \<le> N"
  have c1: "\<exists>p. p permutes {i. i \<le> N} \<and>
    equivForm (applySym2Form p (constrInv pair 0 1)) (constrInv pair i j)"
    using assms(3,4,7) b2 b3 symOnFuncInv by blast
  then obtain p where c1: "p permutes {i. i \<le> N} \<and>
    equivForm (applySym2Form p (constrInv pair 0 1)) (constrInv pair i j)" 
    by blast
  have c2: "formEval (applySym2Form p (constrInv pair 0 1)) s"
    using SymLemma' assms(1,2,5,6) c1 by blast
  have c3: "formEval (constrInv pair i j) s"
    using c1 c2 equivForm_def by blast
  show "formEval (snd pair j) s"
    by (cut_tac b1 b2 c3, unfold constrInv_def,auto)
qed


lemma SymLemmaOnExcl':
  assumes "symPredSet' N Is"
    and "symProtRules' N rs"
    and "1 \<le> N"
    and "symPair pair N"
    and "reachableUpTo Is rs k s"
    and "\<forall>s i l k. l \<le> M \<longrightarrow> k\<le>M \<longrightarrow>reachableUpTo Is rs i s \<longrightarrow> formEval (constrInv pair k l) s"
    and "i \<le> N"
    and "M\<le>N \<and> 1\<le>M"
    
    
  shows "formEval (constrInvByExcl pair i N) s"
proof (simp add: constrInvByExcl_def, rule+)
  fix j
  assume b1: "formEval (fst pair i) s" and b2: "j \<noteq> i" and b3: "j \<le> N"
  have c0: "1\<le>N"
    using assms(3) assms(8) le_trans by blast
     
  have c1: "\<exists>p. p permutes {i. i \<le> N} \<and>
    equivForm (applySym2Form p (constrInv pair 0 1)) (constrInv pair i j)"
    using assms(4) assms(7) b2 b3 c0 symOnFuncInv by presburger
     
  then obtain p where c1: "p permutes {i. i \<le> N} \<and>
    equivForm (applySym2Form p (constrInv pair 0 1)) (constrInv pair i j)" 
    by blast
  
  have c2: "formEval (applySym2Form p (constrInv pair 0 1)) s"
    using SymLemma' assms(1) assms(2) assms(5) assms(6) assms(8) c1 by blast
     
  have c3: "formEval (constrInv pair i j) s"
    using c1 c2 equivForm_def by blast
  show "formEval (snd pair j) s"
    by (cut_tac b1 b2 c3, unfold constrInv_def,auto)
qed



lemma absGen0:
  assumes "\<And>i. f i = g"
    and "absTransfRule env M g = g"
    and "M < N"
  shows "absTransfRule env M ` (oneParamCons N f) = oneParamCons M f"
  by (auto simp add: assms image_def)

lemma absGen:
  assumes "\<And>i. absTransfRule env M (f i) = (if i \<le> M then g i else h)"
    and "M < N"
  shows "absTransfRule env M ` (oneParamCons N f) = (oneParamCons M g) \<union> {h}"
  apply (auto simp add: assms image_def)
   apply (rule exI[where x="f (M + 1)"])
  apply (metis add_le_same_cancel1 assms(1) assms(2) discrete not_one_le_zero)
  subgoal for i apply (rule exI[where x="f i"])
    by (metis assms(1) assms(2) le_trans nat_le_linear not_le)
  done


lemma DabsGenInv:
  assumes "\<And>i. i\<le>N \<Longrightarrow> DabsTransfRule env  (f i) =  f i"
     
  shows "DabsTransfRule env  ` (oneParamCons N f) = (oneParamCons N f) "
  by (auto simp add: assms image_def)

lemma DabsGen:
  assumes "\<And>i.   DabsTransfRule env  (f i) = (if i =0 then f i else f 1)" and "0< N"
     
  shows "DabsTransfRule env  ` (oneParamCons N f) = (oneParamCons 1 f) "
  apply (auto simp add: assms image_def)
  by (metis One_nat_def assms(1) assms(2) dual_order.refl less_one order_less_le)
   

definition equivRuleSubsetEq::"rule set \<Rightarrow> rule set\<Rightarrow>bool" (infix "\<subseteq>\<^sub>r" 30) where 
" equivRuleSubsetEq rs1 rs2 \<equiv>
  ( \<forall>r1. r1\<in> rs1 \<longrightarrow>( \<exists>r2. r2 \<in> rs2 \<and>  equivRule r2  r1 ))" 
 
definition equivRuleSetEq::"rule set \<Rightarrow> rule set\<Rightarrow>bool" (infix "=\<^sub>R" 30) where 
" equivRuleSetEq rs1 rs2 \<equiv>
  (equivRuleSubsetEq rs1 rs2) & (equivRuleSubsetEq rs2 rs1)"

lemma equivRuleSetReflex:
  "\<lbrakk>rs1 \<subseteq> rs2\<rbrakk> \<Longrightarrow>  equivRuleSubsetEq rs1 rs2"
  using equivRuleRefl equivRuleSubsetEq_def by auto

lemma absGen':
  assumes "\<And>i. equivRule (absTransfRule env M (f i))  (if i \<le> M then g i else h)"
    and "M < N"
  shows "equivRuleSubsetEq ((absTransfRule env M)`(oneParamCons N f)) ((oneParamCons M g) \<union> {h} )"
proof(unfold equivRuleSubsetEq_def,rule allI, rule impI)
  fix r2
  assume a1:"r2 \<in>absTransfRule env M` oneParamCons N f "
  have "\<exists>i. i\<le>N \<and> r2=absTransfRule env M ( f i)" 
    apply(cut_tac a1, unfold  oneParamCons_def,auto) 
    done
  then obtain i where a2:"i\<le>N \<and> r2= absTransfRule env M ( f i)" by blast
  have "i\<le>M \<or>~i\<le>M" 
    by arith
  moreover
  {assume "i\<le>M"
    have "equivRule r2 (g i)"
      using \<open>i \<le> M\<close> a2 assms(1) by presburger 

    have "\<exists>abr. abr \<in> oneParamCons M g \<union> {h} \<and> equivRule abr r2" 
    proof(rule_tac x="g i" in exI)  
      show "g i \<in> oneParamCons M g \<union> {h} \<and> equivRule (g i) r2"
        using \<open>equivRule r2 (g i)\<close> \<open>i \<le> M\<close> equivRuleSym by fastforce 
    qed
  }
  moreover
  {assume "~i\<le>M"
    have "equivRule  r2  h"
      using \<open>~i \<le> M\<close> a2 assms(1) by presburger 
    have "\<exists>abr. abr \<in> oneParamCons M g \<union> {h} \<and> equivRule abr r2" 
    proof(rule_tac x="h" in exI)  
      show "h \<in> oneParamCons M g \<union> {h} \<and> equivRule (h) r2"
        using \<open>equivRule  r2 (h)\<close> \<open>~i \<le> M\<close> equivRuleSym by auto
    qed
  }
  ultimately  show "\<exists>abr. abr \<in> oneParamCons M g \<union> {h} \<and> equivRule abr r2" 
    by blast
qed 

lemma image_Un_subset:
"\<lbrakk>equivRuleSubsetEq (f`rs1) rs1'; equivRuleSubsetEq (f`rs2) rs2'\<rbrakk>\<Longrightarrow>
  equivRuleSubsetEq (f`(rs1 \<union> rs2)) (rs1' \<union> rs2')"
  using UnI2 Un_commute Un_iff equivRuleSubsetEq_def by auto

lemma absGen2:
  assumes "\<And>i j. absTransfRule env M (f i j) = 
    (if i \<le> M \<and>j \<le> M then g0 i j else 
     if i \<le> M \<and> j > M then g1 i else
     if i > M \<and> j \<le> M then g2 j
     else g3)" 
    and "M + 1 \<le> N"
  shows "absTransfRule env M ` (twoParamsCons N f) = 
    twoParamsCons M g0 \<union> oneParamCons M g1 \<union> oneParamCons M g2 \<union> {g3}"
proof
  show "absTransfRule env M ` twoParamsCons N f \<subseteq> twoParamsCons M g0 \<union> oneParamCons M g1 \<union> oneParamCons M g2 \<union> {g3}"
  proof 
    fix x
    assume b1:"x \<in> absTransfRule env M ` twoParamsCons N f "
    have b2:"\<exists>i j. i \<le> N \<and> j \<le> N \<and> x = absTransfRule env M (f i j)"
      using b1 by auto 
    then obtain i and j where b2:"i\<le>N \<and> j \<le> N \<and> x = absTransfRule env M (f i j)"
      by blast
    have "(i \<le> M \<and> j \<le> M) \<or> (i \<le> M \<and> j > M) \<or>
          (i > M \<and> j \<le> M) \<or> (i > M \<and> j > M)" by auto
    moreover
    {assume b3:"i \<le> M \<and> j \<le> M"
      have b4:"x = g0 i j"
        by (simp add: assms(1) b2 b3) 
      have "x \<in> twoParamsCons M g0"
        apply (cut_tac b2, simp)
        using b3 b4 by blast
      then have "x \<in> twoParamsCons M g0 \<union> oneParamCons M g1 \<union> oneParamCons M g2 \<union> {g3}" 
        by blast
    }
    moreover
    {assume b3:"(i \<le> M \<and>j >M )"
      have b4:"x=g1 i "
        using assms(1) b2 b3 by auto 
      have "x \<in>  (oneParamCons M g1) "
        apply simp
        using b3 b4 by blast
      then have "x \<in>twoParamsCons M g0 \<union> oneParamCons M g1 \<union> oneParamCons M g2 \<union> {g3}" 
        by blast
    }
    moreover
    {assume b3:"(i > M \<and>j \<le>M )"
      have b4:"x=g2 j "
        using assms(1) b2 b3 by auto 
      have "x \<in>  (oneParamCons M g2) "
        apply simp
        using b3 b4 by blast
      then have "x \<in>twoParamsCons M g0 \<union> oneParamCons M g1 \<union> oneParamCons M g2 \<union> {g3}" 
        by blast
    }
    moreover
    {assume b3:"i > M \<and> j > M"
      have b4:"x = g3"
        using assms(1) b2 b3 by auto 
      then have "x \<in> twoParamsCons M g0 \<union> oneParamCons M g1 \<union> oneParamCons M g2 \<union> {g3}" 
        by blast
    }
    ultimately show "x \<in> twoParamsCons M g0 \<union> oneParamCons M g1 \<union> oneParamCons M g2 \<union> {g3}"
      by blast
  qed
next
  show "twoParamsCons M g0 \<union> oneParamCons M g1 \<union> oneParamCons M g2 \<union> {g3} \<subseteq> absTransfRule env M ` twoParamsCons N f"
  proof
    fix x
    assume b1:"x \<in> twoParamsCons M g0 \<union> oneParamCons M g1 \<union> oneParamCons M g2 \<union> {g3}"
    show "x \<in> absTransfRule env M ` twoParamsCons N f "
    proof -
      have "x \<in> twoParamsCons M g0 |
       x\<in> oneParamCons M g1 |
       x \<in> oneParamCons M g2 |
        x=g3"
        using b1 by fastforce
      moreover
      {assume b1:"x \<in> twoParamsCons M g0 "
        have "EX i1 i2. i1\<le>M \<and> i2 \<le>M \<and> x=g0 i1 i2"
          by(cut_tac b1,auto)
        then obtain i1 and  i2 where b2:"i1\<le>M \<and> i2 \<le>M & x=g0 i1 i2"
          by auto
        then have b3:"i1\<le>N \<and> i2 \<le>N & x=absTransfRule env M (f i1 i2)"
          using assms by auto
        have "x \<in> absTransfRule env M ` twoParamsCons N f "
          using   b3 by auto
      }
      moreover
      {assume b1:"x\<in> oneParamCons M g1  "
        have "EX i1  . i1\<le>M   & x=g1 i1  "
          by(cut_tac b1,auto)
        then obtain i1   where b2:"i1\<le>M   & x=g1 i1  "
          by auto
        have "EX i2.   i2> M & i2\<le>N "
          using assms by auto
        then obtain i2 where b3:" i2> M & i2\<le>N "
          by presburger
        then have b4:" i1\<le>N   & i2\<le>N &i1\<noteq>i2 \<and> x=absTransfRule env M (f i1 i2)"
          using assms b2 by auto
        have "x \<in> absTransfRule env M ` twoParamsCons N f "
          using b4 by auto
      }
      moreover
      {assume b1:"x\<in> oneParamCons M g2  "
        have "EX i1  . i1\<le>M   & x=g2 i1  "
          by(cut_tac b1,auto)
        then obtain i1   where b2:"i1\<le>M   & x=g2 i1  "
          by auto
        have "EX i2.   i2> M & i2\<le>N "
          using assms by auto
        then obtain i2 where b3:" i2> M & i2\<le>N "
          by presburger
        then have b4:" i1\<le>N   & i2\<le>N \<and>i1\<noteq>i2\<and> x=absTransfRule env M (f  i2 i1)"
          using assms b2 by auto
        have "x \<in> absTransfRule env M ` twoParamsCons N f "
          using b4 by auto
      }
      moreover
      {assume b1:"x= g3  "
        have "EX i1. i1>M   &   i1\<le>N   "
          using assms by auto
        then obtain i1   where b2:"i1>M   &   i1\<le>N "
          by auto
        have "EX i2.   i2> M & i2\<le>N "
          by (simp add: \<open>\<exists>i1>M. i1 \<le> N\<close>)
        then obtain i2 where b3:" i2> M & i2\<le>N  "
          by presburger
        then have b4:" i1\<le>N   & i2\<le>N &x=absTransfRule env M (f  i2 i1)"
          using assms b2 b1 b3 by auto
        have "x \<in> absTransfRule env M ` twoParamsCons N f "
          using b4 by auto
      }
      ultimately show "x \<in> absTransfRule env M ` twoParamsCons N f"
        by blast
    qed
  qed
qed

subsection \<open>strengthenVsObs: strengthening invariants versus observable invariants \<close>


definition isInvCorespDef :: "formula \<Rightarrow> envType \<Rightarrow> nat \<Rightarrow> bool" where
  "isInvCorespDef f env M \<equiv>
    isImplyForm f \<and>
    (\<forall>s. fitEnv s env \<longrightarrow>
     (formEval (ant f) s \<longrightarrow> formEval (ant f) (abs1 M s)) \<and>
     (formEval (cons f) (abs1 M s) \<longrightarrow> formEval (cons f) s))"

lemma isInvCorespDefI:
  "\<forall>s. fitEnv s e \<longrightarrow> (formEval a s \<longrightarrow> formEval a (abs1 M s)) \<and>
                      (formEval c (abs1 M s) \<longrightarrow> formEval c s) \<Longrightarrow>
   isInvCorespDef (a \<longrightarrow>\<^sub>f c) e M"
  unfolding isInvCorespDef_def by auto

lemma invCoresp1:
  assumes a1: "formEval antf s \<longrightarrow> formEval antf (abs1 M s)"
    and a2: "formEval consf (abs1 M s) \<longrightarrow> formEval consf s"
    and a3: "formEval (antf \<longrightarrow>\<^sub>f consf) (abs1 M s)"
  shows "formEval (antf \<longrightarrow>\<^sub>f consf) s"
  using a1 a2 a3 by auto

lemma invCorespImply:
  assumes a1: "isInvCorespDef invf env M"
    and a2: "formEval invf (abs1 M s)"
    and a3: "fitEnv s env"
  shows "formEval invf s"
proof (cut_tac a1, case_tac invf)
  prefer 5
  fix x11 x12
  assume b1:"invf = (x11 \<longrightarrow>\<^sub>f x12)"
  have b2: "ant invf = x11" by (cut_tac b1,auto)
  have b3: "cons invf = x12" by (cut_tac b1,auto)
  show "formEval invf s"
  proof (cut_tac b1,simp del:evalImp,rule invCoresp1)
    show "formEval x11 s \<longrightarrow> formEval x11 (abs1 M s)"
      by (cut_tac b1 a1 a3, unfold isInvCorespDef_def ,auto)
  next
    show "formEval x12 (abs1 M s) \<longrightarrow> formEval x12 s"
      by (cut_tac b1 a1 a3, unfold isInvCorespDef_def ,auto)
  next
    show "formEval (x11 \<longrightarrow>\<^sub>f x12) (abs1 M s)"
      by (cut_tac b1 a2, auto)
  qed
qed (auto simp add: isInvCorespDef_def)

lemma SymLemmaOnExcl2:
  assumes "symPredSet' N Is"
    and "symProtRules' N rs"
    and "1 \<le> N"
    and "symPair pair N"
    and "reachableUpTo Is rs k s"
    and "\<forall>s k l. l \<le> 1 \<longrightarrow> reachableUpTo Is rs k s \<longrightarrow>
          formEval ((\<not>\<^sub>f (Const (index 0) =\<^sub>f Const (index l)) \<and>\<^sub>f ant0 0 l) \<longrightarrow>\<^sub>f cons0 0 l) s"
    and "i \<le> N"
    and "j \<le> N"
    and "\<forall>i j. ant0 i j = fst pair i"
    and "\<forall>i j. cons0 i j = snd pair j"
  shows "formEval (ant0 j i \<longrightarrow>\<^sub>f forallFormExcl (cons0 i) j N) s"
proof -
  have "formEval (constrInvByExcl pair j N) s"
    apply (rule SymLemmaOnExcl[OF assms(1-5) _ assms(8)])
    using assms(10) assms(6) assms(9) by auto
  then show ?thesis
    using assms(9-10) constrInvByExcl_def by auto 
qed

lemma SymLemmaOnExcl2':
  assumes "symPredSet' N Is"
    and "symProtRules' N rs"
    and "1 \<le> N"
    and "symPair pair N"
    and "reachableUpTo Is rs k s"
    and "\<forall>s k l j. l \<le> M  \<longrightarrow> j \<le>M \<longrightarrow> reachableUpTo Is rs k s \<longrightarrow>
          formEval ((\<not>\<^sub>f (Const (index j) =\<^sub>f Const (index l)) \<and>\<^sub>f ant0 j l) \<longrightarrow>\<^sub>f cons0 j l) s"
    and "i \<le> N"
    and "j \<le> N"
    and "\<forall>i j. ant0 i j = fst pair i"
    and "\<forall>i j. cons0 i j = snd pair j"
    and "M\<le>N \<and> 1\<le>M"
  shows "formEval (ant0 j i \<longrightarrow>\<^sub>f forallFormExcl (cons0 i) j N) s"
proof -
  have "formEval (constrInvByExcl pair j N) s"
   
  proof(rule SymLemmaOnExcl'[where N="N" and Is="Is" and rs="rs" and M="M" and pair="pair" and k="k"])
    show " symPredSet' N Is"
      using assms(1) by blast
  next
    show "symProtRules' N rs"
      using assms(2) by blast
  next
    show "1 \<le> N"
      using assms(3) by auto
  next
    show "symPair pair N"
      using assms(4) by auto    
  next
    show "reachableUpTo Is rs k s"
      by (simp add: assms(5))
  next
    show " \<forall>s i l k. l \<le> M \<longrightarrow> k \<le> M \<longrightarrow> reachableUpTo Is rs i s \<longrightarrow> formEval (constrInv pair k l) s"
      
    proof((rule allI)+ ,(rule impI)+ )
      fix s i l k
      assume "l \<le> M" and  "k \<le> M" and  "reachableUpTo Is rs i s "
      have c0:"(fst pair k) =ant0 k j"
          by (simp add: assms(9))
      have c1:"(snd pair l) =cons0 i l"
          by (simp add: assms(10))  
      show "formEval (constrInv pair k l) s"
      proof(simp add:c0 c1,(rule impI)+)
        assume d1:" formEval (ant0 k j) s" and d2:"k \<noteq> l "
        show "formEval (cons0 i l) s"
          apply(cut_tac assms(6))
          using \<open>k \<le> M\<close> \<open>l \<le> M\<close> \<open>reachableUpTo Is rs i s\<close> assms(10) assms(9) d1 d2 evalAnd by force
      qed
    qed
  next
    show "j \<le> N"
      by (simp add: assms(8))
  next
    show "M \<le> N \<and> 1 \<le> M"
      using assms(11) by auto
  qed     
      
  then show ?thesis
    using assms(9-10) constrInvByExcl_def by auto 
qed


lemma SymLemmaOnExcl3':
  assumes "symPredSet' N Is"
    and "symProtRules' N rs"
    and "1 \<le> N"
    and "symPair pair N"
    and "reachableUpTo Is rs k s"
    and "\<forall>s k l j. l \<le> M  \<longrightarrow> j \<le>M \<longrightarrow> reachableUpTo Is rs k s \<longrightarrow>
          formEval ((\<not>\<^sub>f (Const (index j) =\<^sub>f Const (index l)) \<and>\<^sub>f ant0  j l)  \<longrightarrow>\<^sub>f cons0  j l) s"
    and "i \<le> N"
    and "j \<le> N"
    and "\<forall>i j. ant0 i j = fst pair i"
    and "\<forall>i j. cons0 i j = snd pair j"
    and "M\<le>N \<and> 1\<le>M"
  shows "formEval (ant0 i j \<longrightarrow>\<^sub>f forallFormExcl (cons0 j) i N) s"
proof -
  have "formEval (constrInvByExcl pair i N) s"
   
  proof(rule SymLemmaOnExcl'[where N="N" and Is="Is" and rs="rs" and M="M" and pair="pair" and k="k"])
    show " symPredSet' N Is"
      using assms(1) by blast
  next
    show "symProtRules' N rs"
      using assms(2) by blast
  next
    show "1 \<le> N"
      using assms(3) by auto
  next
    show "symPair pair N"
      using assms(4) by auto    
  next
    show "reachableUpTo Is rs k s"
      by (simp add: assms(5))
  next
    show " \<forall>s i l k. l \<le> M \<longrightarrow> k \<le> M \<longrightarrow> reachableUpTo Is rs i s \<longrightarrow> formEval (constrInv pair k l) s"
      
    proof((rule allI)+ ,(rule impI)+ )
      fix s i l k
      assume "l \<le> M" and  "k \<le> M" and  "reachableUpTo Is rs i s "
      have c0:"(fst pair k) =ant0 k j"
          by (simp add: assms(9))
      have c1:"(snd pair l) =cons0 i l"
          by (simp add: assms(10))  
      show "formEval (constrInv pair k l) s"
      proof(simp add:c0 c1,(rule impI)+)
        assume d1:" formEval (ant0 k j) s" and d2:"k \<noteq> l "
        show "formEval (cons0 i l) s"
          apply(cut_tac assms(6))
          using \<open>k \<le> M\<close> \<open>l \<le> M\<close> \<open>reachableUpTo Is rs i s\<close> assms(10) assms(9) d1 d2 evalAnd by force
      qed
    qed
  next
    show "i \<le> N"
      by (simp add: assms(7))
  next
    show "M \<le> N \<and> 1 \<le> M"
      using assms(11) by auto
  qed     
      
  then show ?thesis
    using assms(9-10) constrInvByExcl_def by auto 
qed

definition strengthenVsObs ::
  "(nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> nat \<Rightarrow>bool" where
  "strengthenVsObs f f' N \<equiv>
    \<exists>ant cons.
     (\<lambda>i j. ant i j \<longrightarrow>\<^sub>f cons i j) = f \<and> f' = f \<or>
     (\<lambda>i j. ant j i \<longrightarrow>\<^sub>f forallFormExcl (cons i) j N) = f \<and>
     (\<lambda>i j. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f ant i j \<longrightarrow>\<^sub>f cons i j) = f' \<and>
     (\<exists>pair. symPair pair N \<and> (\<forall>i j. ant i j = fst pair i) \<and> (\<forall>i j. cons i j = snd pair j)) \<or>
     (\<lambda>i j. ant i j \<longrightarrow>\<^sub>f forallFormExcl (cons j) i N) = f \<and>
     (\<lambda>i j. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f ant i j \<longrightarrow>\<^sub>f cons i j) = f' \<and>
     (\<exists>pair. symPair pair N \<and> (\<forall>i j. ant i j = fst pair i) \<and> (\<forall>i j. cons i j = snd pair j))"

lemma strengthenVsObsSame:
  "strengthenVsObs (\<lambda>i j. a i j \<longrightarrow>\<^sub>f c i j) (\<lambda>i j. a i j \<longrightarrow>\<^sub>f c i j) N"
  unfolding strengthenVsObs_def by auto

(*lemma strengthenVsObsSame1:
  "strengthenVsObs f f  N"
  unfolding strengthenVsObs_def *)
  

lemma strengthenVsObsDiff:
  assumes "symParamForm N a"
    and "symParamForm N c"
  shows "strengthenVsObs (\<lambda>i j. a j \<longrightarrow>\<^sub>f forallFormExcl c j N)
                         (\<lambda>i j. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f a i \<longrightarrow>\<^sub>f c j) N"
  unfolding strengthenVsObs_def
  apply (rule exI[where x="\<lambda>i j. a i"])
  apply (rule exI[where x="\<lambda>i j. c j"])
  apply (rule disjI2) using assms by auto

lemma strengthenVsObsDiff1:
  assumes "symParamForm N a"
    and "symParamForm N c"
  shows "strengthenVsObs (\<lambda>i j. a i \<longrightarrow>\<^sub>f forallFormExcl c i N)
                         (\<lambda>i j. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f a i \<longrightarrow>\<^sub>f c j) N"
  unfolding strengthenVsObs_def
  apply (rule exI[where x="\<lambda>i j. a i"])
  apply (rule exI[where x="\<lambda>i j. c j"])
  apply (rule disjI2) using assms by auto

definition strengthenVsObsLs ::
  "(nat \<Rightarrow> nat \<Rightarrow> formula) list \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list \<Rightarrow> nat \<Rightarrow> bool" where
  "strengthenVsObsLs ls1 ls2 N = (\<forall>f1\<in>set ls1. \<exists>f2\<in>set ls2. strengthenVsObs f1 f2 N)"




lemma SymLemmaOnExcl3:
  assumes "symPredSet' N Is"
    and "symProtRules' N rs"
    and "1 \<le> N"
     
    and "reachableUpTo Is rs k s"
    and "\<forall>s k l j. l \<le> M  \<longrightarrow> j \<le>M \<longrightarrow> reachableUpTo Is rs k s \<longrightarrow>
          formEval (f' j l) s"
    and "i \<le> N"
    and "j \<le> N"
    and "strengthenVsObs f f' N"
    and "M\<le>N \<and> 1\<le>M" 
    and "symParamForm2 N f' "
  shows "formEval (f i j) s"
proof -
  have "\<exists>l. l <= (1::nat)"
    by arith
  then obtain l where "l\<le>(1::nat)"
    by blast
  have "l \<le>M"
    using \<open>l \<le> 1\<close> assms(9) le_trans by blast
    
  from assms(8) obtain ant0 cons0 where d1: "
         ((\<lambda>i j. ant0 i j \<longrightarrow>\<^sub>f cons0 i j) = f \<and> f' = f \<or>
          (\<lambda>i j. ant0 j i \<longrightarrow>\<^sub>f forallFormExcl (cons0 i) j N) = f \<and>
          (\<lambda>i j. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f ant0 i j \<longrightarrow>\<^sub>f cons0 i j) = f' \<and>
          (\<exists>pair. symPair pair N \<and> (\<forall>i j. ant0 i j = fst pair i) \<and> (\<forall>i j. cons0 i j = snd pair j)) \<or>
          (\<lambda>i j. ant0 i j \<longrightarrow>\<^sub>f forallFormExcl (cons0 j) i N) = f \<and>
           (\<lambda>i j. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f ant0 i j \<longrightarrow>\<^sub>f cons0 i j) = f' \<and>
         (\<exists>pair. symPair pair N \<and> (\<forall>i j. ant0 i j = fst pair i) \<and> (\<forall>i j. cons0 i j = snd pair j)))"
       unfolding strengthenVsObs_def by blast
      moreover
      {assume d2:"(\<lambda>i j. ant0 i j \<longrightarrow>\<^sub>f cons0 i j) =f \<and> f'=f"
        
        have "formEval (f'  0 l) s"
          using \<open>l \<le> M\<close> assms(4) assms(5) by blast 
        
        have c30: "(\<exists>p h. p permutes {i. i \<le> N} \<and> h\<le> 1\<and>
         equivForm (applySym2Form p (f' 0 h)) (f' i j))"
          using assms(10) assms(3) assms(6) assms(7) symOnFunc2 by blast
       
        then obtain p h where 
          c5: "p permutes {i. i \<le> N} \<and> h \<le> 1 \<and> equivForm (applySym2Form p (f' 0 h)) (f' i j)"
          by blast

        have c6:"formEval (applySym2Form p (f' 0 h)) s" thm SymLemma
          apply(rule_tac N="N" and fs="Is" and rs="rs" in SymLemma')
          using assms(1) apply blast
          using assms(2) apply blast
          using assms(5) assms(9) c5 d2 apply auto[1]
           
          using   c5 apply blast 
          using assms(4) by auto
         
        have  "formEval (f' i j) s"
          using c5 c6 equivForm_def by blast 
        then have "formEval (f i j) s"
          by (simp add: d2)

         
          
      }
      
      moreover
      {assume d2:"(\<lambda>i j. ant0 j i \<longrightarrow>\<^sub>f forallFormExcl (cons0 i) j N) = f \<and>
                  (\<lambda>i j. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f ant0 i j \<longrightarrow>\<^sub>f cons0 i j) = f' \<and>
                  (\<exists>pair. symPair pair N \<and> (\<forall>i j. ant0 i j = fst pair i) \<and> (\<forall>i j. cons0 i j = snd pair j))" 
        from d2 obtain pair where d3:"symPair pair N \<and>
           (\<forall>i j. ant0 i j = fst pair i) \<and> (\<forall>i j. cons0 i j = snd pair j)" 
          by blast
        have d4:"f=(\<lambda>i j. ant0 j i \<longrightarrow>\<^sub>f forallFormExcl (cons0 i) j N) "
          using d2 by fastforce
          
        have "formEval (f i j) s"
          apply(simp only:d4,rule_tac   Is="Is" and rs="rs" and M="M" and N="N" in SymLemmaOnExcl3')
          using assms(1) apply blast
          using assms(2) apply blast
          using assms(3) apply auto[1]
          using d3       apply auto[1]
          using assms(4) apply auto[1]
           using assms(5) d2 apply blast
           using assms(7) apply blast
          using assms(6) apply blast
          using d3 apply auto[1]
          using d3 apply auto[1]
          using assms(9) by auto
          
        
      }

     moreover
      {assume d2:"
      (\<lambda>i j. ant0 i j \<longrightarrow>\<^sub>f forallFormExcl (cons0 j) i N) = f \<and>
           (\<lambda>i j. \<not>\<^sub>f Const (index i) =\<^sub>f Const (index j) \<and>\<^sub>f ant0 i j \<longrightarrow>\<^sub>f cons0 i j) = f' \<and>
         (\<exists>pair. symPair pair N \<and> (\<forall>i j. ant0 i j = fst pair i) \<and> (\<forall>i j. cons0 i j = snd pair j))"
      from d2 obtain pair where d3:"symPair pair N \<and>
           (\<forall>i j. ant0 i j = fst pair i) \<and> (\<forall>i j. cons0 i j = snd pair j)" 
          by blast
        have d4:"f=(\<lambda>i j. ant0 i j \<longrightarrow>\<^sub>f forallFormExcl (cons0 j) i N) "
          using d2 by fastforce
          
        have "formEval (f i j) s"
          apply(simp only:d4,rule_tac   Is="Is" and rs="rs" and M="M" and N="N" in SymLemmaOnExcl3')
          using assms(1) apply blast
          using assms(2) apply blast
          using assms(3) apply auto[1]
                 apply auto[1]
          using d3 apply auto[1]
          using d3 apply auto[1]
          using assms(4) apply auto[1]
          using assms(5) d2 apply blast
          apply (simp add: assms(6))
          apply (simp add: assms(7))
          apply (simp add: d3)
           apply (simp add: d3)
          using assms(9) by auto
      }
      ultimately show "formEval (f i j) s"
        by blast
    qed

definition dataParamVsObs ::"(nat \<Rightarrow> nat \<Rightarrow> formula) \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula)\<Rightarrow>string \<Rightarrow>string \<Rightarrow> bool" where
  " dataParamVsObs f f' pv gv  \<equiv>
   ( \<exists>ant  .
     f= (\<lambda>d i. ant  i \<longrightarrow>\<^sub>f (IVar (Para pv i) =\<^sub>f (IVar (Ident gv))))   \<and>
     f'=(\<lambda>d i. ant i \<longrightarrow>\<^sub>f (IVar (Para pv i) =\<^sub>f(Const (data d))) \<longrightarrow>\<^sub>f ( (IVar (Ident gv))  =\<^sub>f (Const (data d))))  )"

primrec  dataParamVsObsLs ::"(nat \<Rightarrow> nat \<Rightarrow> formula) list \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list \<Rightarrow>string list\<Rightarrow>string list\<Rightarrow> bool" where
  " dataParamVsObsLs [] fs' pvs gvs  = True "| 
  " dataParamVsObsLs (f# fs)  fs' pvs gvs =
        (  dataParamVsObs f (hd fs') (hd pvs) (hd gvs) \<and>  dataParamVsObsLs (fs)  (tl fs') (tl pvs) (tl gvs))"



lemma DSymLemmaOnExcl:
  assumes "DsymPredSet' D Is"
    and "DsymProtRules' D rs"
    and "1 \<le> D " 
    and "reachableUpTo Is rs k s"
    and "\<forall>i. DsymParamForm D (\<lambda>d. f d i)"
    and "\<forall>s i .   reachableUpTo Is rs i s \<longrightarrow> formEval (f  0 l) s"
    and "d \<le> D"  
  shows "formEval (f d l) s"


proof -
  have "\<exists>p. p permutes {i. i \<le> D} \<and> p 0 = d" thm permute_inv_ij
    using \<open>d \<le> D\<close>
    using assms(4) permute_inv_i by presburger   
  then obtain p where "p permutes {i. i \<le> D} \<and> p 0 = d"
    by blast
  have " DsymParamForm D (\<lambda>d. f d l)"
    using assms(5) by blast
    
  have c1: "\<exists>p. p permutes {i. i \<le> D} \<and>
    equivForm (applyDSym2Form p (f 0 l)) (f d l)"
    using assms(5)    
    apply(drule_tac x="l" in spec) 
    apply(rule_tac x="p" in exI)
    using DsymParamForm_def \<open>p permutes {i. i \<le> D} \<and> p 0 = d\<close> by force
  then obtain p where c1: "p permutes {i. i \<le> D} \<and>
    equivForm (applyDSym2Form p (f 0 l)) (f d l) " 
    by blast
  have c2: "formEval (applyDSym2Form p  (f 0 l)) s"
    apply(rule DSymLemma')
    using assms(1) apply simp
    using assms(2) apply simp
    using assms(6) apply simp
    using c1 apply simp
    using assms(4) apply simp
    done
     
  show  c3: "formEval (f d l) s"
    using c1 c2 equivForm_def by blast 
qed



lemma DSymLemmaOnDataCoherence:
  assumes a1:"DsymPredSet' D Is"
    and a2:"DsymProtRules' D rs"
    and "reachableUpTo Is rs k s"
    and "dataParamVsObs f f' pv gv"
    and "\<forall>s i .   reachableUpTo Is rs i s \<longrightarrow> formEval (f'  0 l) s"
    and "\<forall>k s. reachableUpTo Is rs k s \<longrightarrow>(\<exists> d. s ( (Para pv l)) =(data d) \<and> d\<le> D) "
    and "1 \<le> D "
    (*and "d \<le> D"*)
    
    and "\<forall>i. DsymParamForm D (\<lambda>d. f' d i)"
  shows "formEval (f d l) s"
proof -
  have "  ( \<exists>ant  .
     f=(\<lambda>d i. ant  i \<longrightarrow>\<^sub>f (IVar (Para pv i) =\<^sub>f (IVar (Ident gv)))) \<and>
     f'=(\<lambda>d i. ant i \<longrightarrow>\<^sub>f (IVar (Para pv i) =\<^sub>f(Const (data d))) \<longrightarrow>\<^sub>f ( (IVar (Ident gv))  =\<^sub>f (Const (data d))))  )"
    using assms(4) dataParamVsObs_def by auto
  then obtain ant where b1:" f =(\<lambda>d i. ant  i \<longrightarrow>\<^sub>f (IVar (Para pv i) =\<^sub>f (IVar (Ident gv))))   \<and>
    f'= (\<lambda>d i. ant i \<longrightarrow>\<^sub>f (IVar (Para pv i) =\<^sub>f(Const (data d))) \<longrightarrow>\<^sub>f ( (IVar (Ident gv))  =\<^sub>f (Const (data d)))) "
    by blast

  show "formEval (f d l) s"
  proof(cut_tac b1,simp, rule impI )
    assume b1':"formEval (ant l) s"
    have "\<exists>d. s (Para pv l) =data d \<and> d \<le> D"
      using assms(3) assms(6) by auto 
        
    then obtain d0 where b2:"s (Para pv l) =data d0  \<and> d0 \<le> D"
      by blast
    have b3:"formEval (f' d0 l) s"
      apply(rule_tac Is="Is" and rs="rs" and f="f'" in DSymLemmaOnExcl)
      using a1 apply assumption
      using a2 apply blast
      using assms(7) apply blast
      using assms(3) apply auto[1]
      using assms(8)  apply assumption
      using assms(5) apply auto[1]
      using b2 apply auto[1]
      done
    have "s (Ident gv) = data d0"
      using b3 b2 b1 b1' by auto
    show "s (Para pv l) = s (Ident gv)"
      by (simp add: \<open>s (Ident gv) = data d0\<close> b2)
  qed
qed

subsection \<open>Auxiliary lemmas\<close>

text \<open>For showing invariants by hand, usually type correctness\<close>

lemma invIntro:
  assumes "\<And>s0. (\<forall>f\<in>fs. formEval f s0) \<Longrightarrow> Inv s0"
    and "\<And>r sk. r \<in> rs \<Longrightarrow> formEval (pre r) sk \<Longrightarrow> Inv sk \<Longrightarrow> Inv (trans1 (act r) sk)"
  shows "reachableUpTo fs rs k s \<Longrightarrow> Inv s"
proof (induct k arbitrary: s)
  case 0
  then show ?case
    apply (elim reachableUpTo0)
    using assms(1) by auto
next
  case (Suc k)
  show ?case
    using Suc(2)
    apply (elim reachableUpToSuc)
    subgoal for s' g a
      using Suc.hyps assms(2) by fastforce
    done
qed


lemma noEffect1 [intro,simp]:
  "(\<And>i. v \<notin> varOfStmt (pf i)) \<Longrightarrow> largestInd v N pf = None"
  by (induct_tac N, auto)

lemma fitEnvAssignConst [intro,simp]:
  "fitEnv s env \<Longrightarrow> env v = getValueType c \<Longrightarrow> fitEnv (trans1 (assign (v, Const c)) s) env"
  using fitEnv_def by auto

lemma fitEnvAssignVar [intro,simp]:
  "fitEnv s env \<Longrightarrow> env v = env v' \<Longrightarrow> fitEnv (trans1 (assign (v, IVar v')) s) env"
  using fitEnv_def by auto

lemma largestIndLeN [intro,simp]:
  "largestInd v N pS = Some i \<Longrightarrow> i \<le> N"
  by (simp add: largestIndSome)

lemma fitEnvAssignIte [intro,simp]:
  assumes 0:"fitEnv s env " and
    1:"deriveExp env (iteForm b e1 e2)=Some(t)" and 
    2:"env v = t"
  shows "fitEnv (trans1 (assign (v, iteForm b e1 e2)) s) env"
proof(unfold fitEnv_def,rule allI,rule impI)
  fix va
  assume a1:"env va \<noteq> anyType "
  show "typeOf (trans1 (assign (v, iteForm b e1 e2)) s) va = env va"
  proof(case_tac "v=va")
    assume b1:"v = va"
    show "typeOf (trans1 (assign (v, iteForm b e1 e2)) s) va = env va"
      apply(cut_tac b1 a1 0 1 ,auto)
      apply(case_tac "expEval e1 s",auto)
      apply (smt (z3) "2" boolTypeSafe dataTypeSafe getValueType.simps(1) indexTypeSafe option.distinct(1) typeType.exhaust)
      apply (smt (z3) "2" boolTypeSafe dataTypeSafe enumTypeSafe getValueType.simps(2) option.distinct(1) typeType.exhaust)
      apply (smt (z3) "2" dataTypeSafe enumTypeSafe getValueType.simps(3) indexTypeSafe option.distinct(1) typeType.exhaust)
      apply (smt (z3) "2" boolTypeSafe dataTypeSafe enumTypeSafe getValueType.simps(4) indexTypeSafe option.distinct(1) typeType.exhaust)
      apply (smt (z3) "2" boolTypeSafe enumTypeSafe getValueType.simps(5) indexTypeSafe option.distinct(1) typeType.exhaust)
      by (smt (z3) "2" boolTypeSafe dataTypeSafe enumTypeSafe indexTypeSafe option.distinct(1) typeType.exhaust)
   next
    assume b1:"v \<noteq> va"
    show "typeOf (trans1 (assign (v, iteForm b e1 e2)) s) va = env va"
      using "0" a1 b1 fitEnv_def by auto
  qed
qed
      
       
lemma fitEnvForall [intro,simp]:
  "fitEnv s env \<Longrightarrow>
    \<forall>i\<le>N. fitEnv (trans1 (pS i) s) env \<Longrightarrow> fitEnv (trans1 (forallStm pS N) s) env"
  using fitEnv_def
  apply auto
  by (case_tac "largestInd v N pS",auto)

lemma fitEnvForallExcl [intro,simp]:
  "fitEnv s env \<Longrightarrow>
    \<forall>i\<le>N. fitEnv (trans1 (pS i) s) env \<Longrightarrow> fitEnv (trans1 (forallStmExcl pS j N) s) env"
  using fitEnv_def
  apply auto
  apply (case_tac "largestIndExcl v j N pS",auto)
  by (meson largestIndExclSome)

lemma fitEnvPar [intro,simp]:
   "fitEnv s env \<Longrightarrow>
    fitEnv (trans1 S1 s) env \<Longrightarrow>
    fitEnv (trans1 S2 s) env \<Longrightarrow> fitEnv (trans1 (S1 || S2) s) env"
  using fitEnv_def by auto

lemma fitEnvIte [intro,simp]:
   "fitEnv s env \<Longrightarrow>
    fitEnv (trans1 S1 s) env \<Longrightarrow>
    fitEnv (trans1 S2 s) env \<Longrightarrow> fitEnv (trans1 (IF b DO S1 ELSE S2 FI) s) env"
  using fitEnv_def by auto

lemma fitEnvSkip [intro,simp]:
   "fitEnv s env \<Longrightarrow> fitEnv (trans1 skip s) env"
  using fitEnv_def by auto

lemma absTransConstOnIndex:
  assumes a: "absTransfConst M c = index n"
    and b: "n \<le> M"
  shows "c = index n"
  using a b apply (case_tac c, auto)
  by (case_tac "M < x2", auto)

lemma image_UnI:
  "f ` A1 = B1 \<Longrightarrow> f ` A2 = B2 \<Longrightarrow> f ` (A1 \<union> A2) = B1 \<union> B2"
  by auto


lemma symPredSetExist:
  assumes a:"symParamForm N f"
  shows "symPredSet' N {(\<exists>\<^sub>fi. f i) N}"
proof(unfold symPredSet'_def,(rule allI)+,(rule impI)+,simp)
  fix p
  assume b1:"p permutes {x. x \<le> N}"
  have "symParamForm N (\<lambda>j.(\<exists>\<^sub>fi. f i) N)"
  apply(cut_tac a b1 , unfold symParamForm_def,auto)
  apply (auto simp add: equivForm_def symParamForm_def)
  apply (metis mem_Collect_eq permutes_in_image)
    by (metis b1 mem_Collect_eq permutes_def)

  show "equivForm ((\<exists>\<^sub>fi. applySym2Form p (f i)) N) (existForm f N) "
    using \<open>symParamForm N (\<lambda>j. (\<exists>\<^sub>fi. f i) N)\<close> b1 symParamForm_def by auto 
qed

lemma symPredSetExistForall:
  assumes a:"symParamForm2 N f"
  shows "symPredSet' N {(\<exists>\<^sub>fi. (\<forall>\<^sub>fp. f i p) N) N}"
 apply (rule symPredSetExist)
  apply(rule symParamFormForall)
  using assms by blast


lemma DsymPredSetExist:
  assumes a:"DsymParamForm N f"
  shows "DsymPredSet' N {(\<exists>\<^sub>fi. f i) N}"
proof(unfold DsymPredSet'_def,(rule allI)+,(rule impI)+,simp)
  fix p
  assume b1:"p permutes {x. x \<le> N}"
  have "DsymParamForm N (\<lambda>j.(\<exists>\<^sub>fi. f i) N)"
  apply(cut_tac a b1 , unfold DsymParamForm_def,auto)
  apply (auto simp add: equivForm_def DsymParamForm_def)
  apply (metis mem_Collect_eq permutes_in_image)
    by (metis b1 mem_Collect_eq permutes_def)

  show "equivForm ((\<exists>\<^sub>fi. applyDSym2Form p (f i)) N) (existForm f N) "
    using \<open>DsymParamForm N (\<lambda>j. (\<exists>\<^sub>fi. f i) N)\<close> b1 DsymParamForm_def by auto 
qed

lemma DsymPredSetExistForall:
  assumes a:"DsymParamForm2 N f"
  shows "DsymPredSet' N {(\<exists>\<^sub>fi. (\<forall>\<^sub>fp. f i p) N) N}"
 apply (rule DsymPredSetExist)
  apply(rule DsymParamFormForall)
  using assms by blast



lemma strengthenFwExt1:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>i j. strengthenRuleByFrmL2 (map2' (lemmasFor_r N) j i) (r i) = r_ref N i" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenFwRel (oneParamCons N r)  (set (InvS N)) (oneParamCons N (r_ref N)) N "
proof(unfold strengthenFwRel_def,rule allI,rule impI)
  fix r'
  assume a1:"r' \<in> oneParamCons N (r_ref N) "
  from a1 have b1:"\<exists>i. i\<le>N &r'=r_ref N i"
    by auto
  then obtain i where b1:"i\<le>N &r'=r_ref N i"
    by blast  
    
  show " (\<exists>ra invL i j.
              i \<le> N \<and>
              j \<le> N \<and>
              invL \<in> set (InvS N) \<and>
              ra \<in> oneParamCons N r \<and>
              r' = strengthenRuleByFrmL2 (map2' invL i j) ra) \<or>
          r' \<in> oneParamCons N r"
    apply(rule disjI1,rule exI[where x="r i"])  
    apply(
        rule exI[where x="lemmasFor_r N"],
        rule exI[where x=0],
        rule exI[where x=i])
    apply(cut_tac a1 b1 a3 a4,auto)
    done
qed


lemma strengthenBwExt1:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>i j. strengthenRuleByFrmL2 (map2' (lemmasFor_r N) j i) (r i) = r_ref N i" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenBwRel (oneParamCons N r)  (set (InvS N)) (oneParamCons N (r_ref N)) N "
proof(unfold strengthenBwRel_def,rule allI,rule impI)
  fix ra
  assume a1:"ra \<in> oneParamCons N (r ) "
  from a1 have b1:"\<exists>i. i\<le>N &ra=r  i"
    by auto
  then obtain i where b1:"i\<le>N &ra=r i"
    by blast  
    
  show "(\<exists>invL i j.
              i \<le> N \<and>
              j \<le> N \<and>
              invL \<in> set (InvS N) \<and>
              strengthenRuleByFrmL2 (map2' invL i j) ra \<in> oneParamCons N (r_ref N)) \<or>
          ra \<in> oneParamCons N (r_ref N) "
    apply(rule disjI1)  
    apply(
        rule exI[where x="lemmasFor_r N"],
        rule exI[where x=0],
        rule exI[where x=i])
    apply(cut_tac a1 b1 a3 a4,auto)
    done
qed


lemma strengthenExt1:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>i j. strengthenRuleByFrmL2 (map2' (lemmasFor_r N) j i) (r i) = r_ref N i" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenRel (oneParamCons N r)  (set (InvS N)) (oneParamCons N (r_ref N)) N "
  using a3 a4 strengthenBwExt1 strengthenFwExt1 strengthenRel_def by presburger




lemma strengthenFwExt2:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>i j. strengthenRuleByFrmL2 (map2' (lemmasFor_r N) i j) (r i j) = r_ref N i j" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenFwRel (twoParamsCons N r)  (set (InvS N)) (twoParamsCons N (r_ref N)) N "
proof(unfold strengthenFwRel_def,rule allI,rule impI)
  fix r'
  assume a1:"r' \<in> twoParamsCons N (r_ref N) "
  from a1 have b1:"\<exists>i j. i\<le>N & j\<le>N &r'=r_ref N i j"
    by auto
  then obtain i and j where b1:"i\<le>N &j\<le>N & r'=r_ref N i j"
    by blast  
    
  show " (\<exists>ra invL i j.
              i \<le> N \<and>
              j \<le> N \<and>
              invL \<in> set (InvS N) \<and>
              ra \<in> twoParamsCons N r \<and>
              r' = strengthenRuleByFrmL2 (map2' invL i j) ra) \<or>
          r' \<in> twoParamsCons N r"
    apply(rule disjI1,rule exI[where x="r i j"])  
    apply(
        rule exI[where x="lemmasFor_r N"],
        rule exI[where x=i],
        rule exI[where x=j])
    apply(cut_tac a1 b1 a3 a4,auto)
    done
qed


lemma strengthenBwExt2:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>i j. strengthenRuleByFrmL2 (map2' (lemmasFor_r N)  i j) (r i j) = r_ref N i j" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenBwRel (twoParamsCons N r)  (set (InvS N)) (twoParamsCons N (r_ref N)) N "
proof(unfold strengthenBwRel_def,rule allI,rule impI)
  fix ra
  assume a1:"ra \<in> twoParamsCons N (r ) "
  from a1 have b1:"\<exists>i j. i\<le>N &j\<le>N &ra=r  i j"
    by auto
  then obtain i and j where b1:"i\<le>N &j\<le>N &ra=r i j"
    by blast  
    
  show "(\<exists>invL i j.
              i \<le> N \<and>
              j \<le> N \<and>
              invL \<in> set (InvS N) \<and>
              strengthenRuleByFrmL2 (map2' invL i j) ra
              \<in> twoParamsCons N (r_ref N)) \<or>
          ra \<in> twoParamsCons N (r_ref N) "
    apply(rule disjI1)  
    apply(
        rule exI[where x="lemmasFor_r N"],
        rule exI[where x=i],
        rule exI[where x=j])
    apply(cut_tac a1 b1 a3 a4,auto)
    done
qed


lemma strengthenExt2:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>i j. strengthenRuleByFrmL2 (map2' (lemmasFor_r N)  i j) (r i j) = r_ref N i j" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenRel (twoParamsCons N r)  (set (InvS N)) (twoParamsCons N (r_ref N)) N "
  using a3 a4 strengthenBwExt2 strengthenFwExt2 strengthenRel_def by presburger

lemma strengthenRefl:
  shows "strengthenRel r S r N"
  using strenRelBwRefl' strenRelFwRefl strengthenRel_def by force


lemma strenFwRelUnion:
  assumes a1:"strengthenFwRel rs1 S rs1' N " and
  a2:"strengthenFwRel rs2 S rs2' N"
  shows "strengthenFwRel (rs1 \<union> rs2) S (rs1' \<union> rs2') N"
  apply(cut_tac a1 a2, unfold strengthenFwRel_def)
  by (metis Un_iff) 


lemma strenRelUnion:
  assumes a1:"strengthenRel rs1 S rs1' N " and
  a2:"strengthenRel rs2 S rs2' N"
  shows "strengthenRel (rs1 \<union> rs2) S (rs1' \<union> rs2') N"
  apply(cut_tac a1 a2, unfold strengthenRel_def)
  by (simp add: strenFwRelUnion strenRelBwUnion) 

definition skipRule::"rule"  where [simp]:
"skipRule \<equiv> chaos \<triangleright> skip"


subsection \<open>CMP  and DCMP\<close>

definition isParamProtInvSet::"(rule set) \<Rightarrow>( formula set)=>
 ((((nat \<Rightarrow> nat \<Rightarrow> formula) list) set)) \<Rightarrow> nat\<Rightarrow> bool" where [simp]:
"isParamProtInvSet rules Is InvS N\<equiv>
(\<forall>k invL f s i j. invL \<in>   (InvS ) \<longrightarrow> f \<in> set invL \<longrightarrow>
           reachableUpTo Is rules  k s \<longrightarrow>
           i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> formEval (f i j) s)" 

definition isAbstractProtInvSet::"(rule set) \<Rightarrow>( formula set)=>
 ((((nat \<Rightarrow> nat \<Rightarrow> formula) list) set)) \<Rightarrow> nat\<Rightarrow> envType \<Rightarrow>bool" where [simp]:
"isAbstractProtInvSet rules Is InvS   M env\<equiv>
(\<forall>i invL f s l. l\<le>M \<and> invL \<in>  (InvS ) \<longrightarrow> f \<in> set invL \<longrightarrow>
           reachableUpTo (absTransfForm (env) M ` (Is))
               rules i s \<longrightarrow>
           formEval (absTransfForm (env) M (f 0 l)) s)" 



definition isProtObsInvSet::"(rule set) \<Rightarrow>( formula set)=>
 ((((nat \<Rightarrow> nat \<Rightarrow> formula) list) set)) \<Rightarrow> nat\<Rightarrow> envType \<Rightarrow>bool" where [simp]:
"isProtObsInvSet rules Is InvS   M env\<equiv>
(\<forall>i invL f s l k. l\<le>M \<and> k\<le>M \<and> invL \<in>  (InvS ) \<longrightarrow> f \<in> set invL \<longrightarrow>
           reachableUpTo Is
               rules i s \<longrightarrow>
           formEval (absTransfForm (env) M (f l k)) s)"




lemma CMP:
  assumes a1: "\<And>r. r \<in> rs2 \<longrightarrow> wellFormedRule env N r"
    and a2: "\<forall>invL f. invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow> symParamForm2 N f"
    and a3: "M\<le>N" 
    and a4: "symPredSet' N Is"  
    and a5: "1  \<le> M"
    and a7: "isProtObsInvSet absRules (absTransfForm (env) M ` Is) S' M env "
    and a8: "\<forall>pinvL pf i j. pinvL \<in> S' \<longrightarrow> pf \<in> set pinvL \<longrightarrow> i \<le> M \<longrightarrow> j\<le>M \<longrightarrow>
               safeForm  env  M (pf  i j) \<and> deriveForm env (pf  i j)"
    and a9: "strengthenRel rs S rs2 N" 
    and a10: "symProtRules' N rs2"
     
    
    and a13: "\<And>r. r \<in> rs2 \<longrightarrow> deriveRule env r"
    and a14: "\<And>f. f \<in> Is \<longrightarrow> deriveForm env f"
    and a15: "\<forall>s i. reachableUpTo Is rs2 i s \<longrightarrow> fitEnv s env"
    and a17: "\<forall>invL\<in>S. \<exists>invL'\<in>S'. strengthenVsObsLs invL invL' N"

    and a18:"absTransfRule (env )  M ` rs2  \<subseteq>\<^sub>r absRules  " 
  shows "isParamProtInvSet  rs Is S N"


proof(unfold isParamProtInvSet_def,(rule allI)+,(rule impI)+)
  fix k invL f s i j
  assume b0:"invL \<in>  S" and b0':" reachableUpTo Is rs k s"  and b01:"f \<in> set invL"
    and b02:"i\<le>N" and b03:"j\<le>N"
  let ?absRules="absTransfRule (env )  M ` rs2"
  have a7':"isProtObsInvSet ?absRules (absTransfForm (env) M ` Is) S' M env " 
  proof(unfold isProtObsInvSet_def,(rule allI)+,(rule impI)+)
    fix i invL f s l k
    assume b1:"l \<le> M \<and> k \<le> M \<and> invL \<in> S'"   and b3:"f \<in> set invL" 
      and b4:"reachableUpTo (absTransfForm env M ` Is) (absTransfRule env M ` rs2) i s"  

    have "\<forall>r1. r1 \<in> ?absRules \<longrightarrow> (\<exists>r2. r2 \<in> absRules \<and> equivRule r1 r2)"
      by (meson a18 equivRuleSubsetEq_def equivRuleSym)
      
    have "reachableUpTo (absTransfForm env M ` Is) absRules i s" 
      using \<open>\<forall>r1. r1 \<in> ?absRules \<longrightarrow> (\<exists>r2. r2 \<in> absRules \<and> equivRule r1 r2)\<close> b4 ruleSetMonoImplyreachStateMono by blast

    
      
    show " formEval (absTransfForm env M (f l k)) s"
      using \<open>reachableUpTo (absTransfForm env M ` Is) absRules i s\<close> a7 b1 b3 isProtObsInvSet_def by blast
      
  qed    
     
    
 (* Step 1: show that the system before abstraction (but after strengthening) respects the
     invariants in S'. This uses the correctness of abstraction.    *)

  have b1': "\<forall>i invL f s l k. l \<le> M \<longrightarrow> k\<le>M \<longrightarrow>invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow> reachableUpTo Is rs2 i s \<longrightarrow>
             formEval (f  l k) s"
  proof ((rule allI)+,(rule impI)+)
    fix i invL f s l k
    assume c1: "f \<in> set invL " and c0: "reachableUpTo Is rs2 i s" and c02:"invL \<in> S'"
      and c03:"(k::nat) \<le>M " and c04:"(l::nat) \<le>M "
    have c2: "predSimSet env Is ({f'. \<exists>f. f \<in>Is \<and> f'=absTransfForm env M f})  M"
      by (smt (verit) absTransfFormSim2 evalDontCareForm mem_Collect_eq predSimSet_def predSim_def)
    have c3: "transSimRules env rs2 {r'. \<exists>r. r \<in> rs2 \<and>   r'= (absTransfRule env M r)} M"
    proof (unfold transSimRules_def,rule ballI)
      fix r
      assume d1: "r \<in> rs2"
      show "\<exists>r' \<in> {r'. \<exists>r. r \<in> rs2 \<and> 
       r'=  (absTransfRule env M r)}. transSimRule env r r' M "
      proof (rule_tac x=" absTransfRule env M r" in bexI)
        show "transSimRule env r (absTransfRule env M r) M"
        proof (rule absRuleSim,cut_tac a5,simp)
          show "wellFormedRule env N r"
            using a1  d1 strengthenRule2Keep by blast 
        next
          show "M \<le>N"
            using a3  by auto
        qed
      next
        show "absTransfRule env M r\<in> {r'. \<exists>r. r \<in> rs2 \<and> r' = absTransfRule env M r}  "
          using d1 by blast
      qed
    qed
    have c4: "reachableUpTo {f'. \<exists>f. f \<in> Is \<and> f' = absTransfForm env M f}
      {r'. \<exists>r. r \<in> rs2 \<and> r' = absTransfRule env M r} i (abs1 M s)"
    proof (rule_tac ?fs1.0="Is" and ?rs1.0="rs2" in transSimRulesReachable)
      show "predSimSet env Is {f'. \<exists>f. f \<in> Is \<and> f' = absTransfForm env M f} M"
        using c2 by blast
    next
      show "transSimRules env rs2 {r'. \<exists>r. r \<in> rs2 \<and> r' = absTransfRule env M r} M"
        using c3 by blast
    next
      show "reachableUpTo Is rs2 i s"
        using c0 by blast
    next
      show  "\<And>r. r\<in>rs2 \<longrightarrow>deriveRule env r"
        using a13 by blast
    next
      show "\<And>f. f \<in> Is \<longrightarrow> deriveForm env f"
        using a14 by blast
    next
      show "\<forall>s i. reachableUpTo Is rs2 i s \<longrightarrow> fitEnv s env"
        using a15 by blast
    qed
    have c5:"fitEnv s env"
      using a15 c0 by blast

    have c6:"(absTransfRule (env )  M ` rs2) = {r'. \<exists>r. r \<in> rs2 \<and> r' = absTransfRule env M r}"
      by blast
      
    have c7:"(absTransfForm (env) M ` Is) = {f'. \<exists>f. f \<in> Is \<and> f' = absTransfForm env M f} "
      by blast
    show "formEval (f l k) s"
     
    proof -
      
        have d3:"formEval (absTransfForm env M (f l k)) (abs1 M s)"
          using a7' c02 c03 c04 c1 c4 c6 c7 by auto 
        
    
      have "safeForm env M  (f l k) "
        using a8 c02 c03 c04 c1 by blast 

      
      have d5:" deriveForm env (f  l k)"
        using a8 c02 c03 c04 c1 by blast
         
      have "formEval (f l k) s = formEval (absTransfForm env M (f l k)) (abs1 M s)"
        by (simp add: \<open>safeForm env M (f l k)\<close> c5 d5 safeEval1) 
      show "formEval (f l k) s "
        by (simp add: \<open>formEval (f l k) s = formEval (absTransfForm env M (f l k)) (abs1 M s)\<close> d3)
        
     
    qed
  qed
  (* Step 2: show that the system before abstraction (but after strengthening) respects the
     invariants in S. This uses the implication between S and S'. *)
  have b1: "\<forall>i invL f s j k. invL \<in> S \<longrightarrow> f \<in> set invL \<longrightarrow> reachableUpTo Is rs2 i s \<longrightarrow> j \<le> N \<longrightarrow>k\<le>N
            \<longrightarrow>  formEval (f  j k) s"
  proof ((rule allI)+,(rule impI)+)
    fix i invL f s j k
    assume c1: "f \<in> set invL " and c0: "reachableUpTo Is rs2 i s" and c02:"invL \<in> S" and
      c03:"j \<le>N" and c04:"k \<le>N"
    obtain invL' where invL': "invL' \<in> S'" "strengthenVsObsLs invL invL' N"
        using a17 c02 by blast
    obtain f' where f': "f' \<in> set invL'" "strengthenVsObs f f' N"
        using invL' c1 unfolding strengthenVsObsLs_def by blast
    show "formEval (f j k) s"
      apply(rule_tac N="N" and Is="Is" and rs="rs2" and k="i" and M="M" and f'="f'" in SymLemmaOnExcl3 )
      using a4 apply blast
      using a10 apply blast
      apply (meson a3 a5 leD leI less_le_trans)
      using c0 apply blast
      using b1' f'(1) invL'(1) apply blast
      apply (simp add: c03)
      apply (simp add: c04)
      apply (simp add: f'(2))
      using a3 a5 apply blast
      using a2 f'(1) invL'(1) by blast
  qed 
  let ?S= "{cinvL. \<exists>i j invL. i\<le>N \<and> j \<le>N \<and> invL \<in>S\<and>cinvL=map2'  invL i j }"
  (* Step 4: show that the system before abstraction and strengthening respects the
     invariants in S. This uses the correctness of strengthening. *)
  have b7: "\<forall>i s. reachableUpTo Is rs i s \<longrightarrow>
    reachableUpTo Is rs2 i s \<and> (\<forall>invL f. invL \<in> ?S \<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s)"
  proof (rule allI, rule strengthenFrmList2Prot2SimProt) 
    fix i
    have a11:"\<forall>r. r \<in> rs \<longrightarrow> (\<exists>invL i j. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> strengthenRuleByFrmL2 (map2' invL i j) r \<in> rs2) \<or> r \<in> rs2"
      using a9 strengthenBwRel_def strengthenRel_def by auto
    show "\<forall>r. r \<in> rs \<longrightarrow>
           (\<exists>invL. invL \<in> {cinvL. \<exists>i j invL. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> cinvL = map2' invL i j} \<and>
                   strengthenRuleByFrmL2 invL r \<in> rs2) \<or> r \<in> rs2"
      by (metis (mono_tags, lifting) a11 mem_Collect_eq) 
  next
    show "\<forall>i s invL f.
           reachableUpTo Is rs2 i s \<longrightarrow>
           invL \<in> {cinvL. \<exists>i j invL. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> cinvL = map2' invL i j} \<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s"
    proof((rule allI)+,(rule impI)+)
      fix i s invL f
      assume c1: "reachableUpTo Is rs2 i s" and  
        c2: "invL \<in> {cinvL. \<exists>i j invL. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> cinvL = map2' invL i j}" and 
        c3: "f \<in> set invL" (* \<and>i\<noteq>j*)
      have c4:"\<exists>i j invL0. i \<le> N \<and> j \<le> N \<and> invL0 \<in> S \<and> invL = map2' invL0 i j"
        using c2 by force
      then obtain i and j and invL0 where c5: "i \<le> N \<and> j \<le> N \<and> invL0 \<in> S \<and> invL = map2' invL0 i j" 
        by blast
      have c6: "\<exists>pf. pf \<in> set invL0 \<and> f = pf i j"
        using c3 c5 map2'Corres by blast
      then obtain pf where c7: "pf \<in> set invL0 \<and> f = pf i j"
        by blast
      show "formEval f s"
        using b1 c1 c5 c7 by blast 
    qed    
  qed
  show "formEval (f i j) s"
    using b0 b0' b01 b02 b03 b1 b7 by blast
qed   


lemma CMP1:
  assumes a1: "\<And>r. r \<in> rs2 \<longrightarrow> wellFormedRule env N r"
    and a2: "\<forall>invL f. invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow> symParamForm2 N f"
    and a3: "M\<le>N" 
    and a4: "symPredSet' N Is"  
    and a5: "1  \<le> M"
    and a6:"\<forall>invL f l k. invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow> l \<le> M \<longrightarrow> k\<le>M \<longrightarrow> absTransfForm env M (f l k) = f l k"
    and a7: "isParamProtInvSet absRules absIs S'  M"
    and a8: "\<forall>pinvL pf i j. pinvL \<in> S' \<longrightarrow> pf \<in> set pinvL \<longrightarrow> i \<le> M \<longrightarrow> j\<le>M \<longrightarrow>
               safeForm  env  M (pf  i j) \<and> deriveForm env (pf  i j)"
    and a9: "strengthenRel rs S rs2 N" 
    and a10: "symProtRules' N rs2"
     
    
    and a13: "\<And>r. r \<in> rs2 \<longrightarrow> deriveRule env r"
    and a14: "\<And>f. f \<in> Is \<longrightarrow> deriveForm env f"
    and a15: "\<forall>s i. reachableUpTo Is rs2 i s \<longrightarrow> fitEnv s env"
    and a16:"(absTransfForm (env) M ` Is) = absIs"
    and a17: "\<forall>invL\<in>S. \<exists>invL'\<in>S'. strengthenVsObsLs invL invL' N"

    and a18:"absTransfRule (env )  M ` rs2  \<subseteq>\<^sub>r absRules  " 
  shows "isParamProtInvSet  rs Is S N"


proof(unfold isParamProtInvSet_def,(rule allI)+,(rule impI)+)
  fix k invL f s i j
  assume b0:"invL \<in>  S" and b0':" reachableUpTo Is rs k s"  and b01:"f \<in> set invL"
    and b02:"i\<le>N" and b03:"j\<le>N"
  let ?absRules="absTransfRule (env )  M ` rs2"
  have a7':"isProtObsInvSet ?absRules (absTransfForm (env) M ` Is) S' M env " 
  proof(unfold isProtObsInvSet_def,(rule allI)+,(rule impI)+)
    fix i invL f s l k
    assume b1:"l \<le> M \<and> k \<le> M \<and> invL \<in> S'"   and b3:"f \<in> set invL" 
      and b4:"reachableUpTo (absTransfForm env M ` Is) (absTransfRule env M ` rs2) i s"  

    have "\<forall>r1. r1 \<in> ?absRules \<longrightarrow> (\<exists>r2. r2 \<in> absRules \<and> equivRule r1 r2)"
      by (meson a18 equivRuleSubsetEq_def equivRuleSym)
      
    have "reachableUpTo (absTransfForm env M ` Is) absRules i s" 
      using \<open>\<forall>r1. r1 \<in> ?absRules \<longrightarrow> (\<exists>r2. r2 \<in> absRules \<and> equivRule r1 r2)\<close> b4 ruleSetMonoImplyreachStateMono by blast

    
      
    show " formEval (absTransfForm env M (f l k)) s"
      using \<open>reachableUpTo (absTransfForm env M ` Is) absRules i s\<close>  a16 b1 b3 
      apply auto
      apply(subgoal_tac "(absTransfForm env M (f l k)) =f l k",simp)
      apply(cut_tac a7, unfold isParamProtInvSet_def)
       apply presburger
      apply(cut_tac a6)
      by blast
  qed    
     
    
 (* Step 1: show that the system before abstraction (but after strengthening) respects the
     invariants in S'. This uses the correctness of abstraction.    *)

  have b1': "\<forall>i invL f s l k. l \<le> M \<longrightarrow> k\<le>M \<longrightarrow>invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow> reachableUpTo Is rs2 i s \<longrightarrow>
             formEval (f  l k) s"
  proof ((rule allI)+,(rule impI)+)
    fix i invL f s l k
    assume c1: "f \<in> set invL " and c0: "reachableUpTo Is rs2 i s" and c02:"invL \<in> S'"
      and c03:"(k::nat) \<le>M " and c04:"(l::nat) \<le>M "
    have c2: "predSimSet env Is ({f'. \<exists>f. f \<in>Is \<and> f'=absTransfForm env M f})  M"
      by (smt (verit) absTransfFormSim2 evalDontCareForm mem_Collect_eq predSimSet_def predSim_def)
    have c3: "transSimRules env rs2 {r'. \<exists>r. r \<in> rs2 \<and>   r'= (absTransfRule env M r)} M"
    proof (unfold transSimRules_def,rule ballI)
      fix r
      assume d1: "r \<in> rs2"
      show "\<exists>r' \<in> {r'. \<exists>r. r \<in> rs2 \<and> 
       r'=  (absTransfRule env M r)}. transSimRule env r r' M "
      proof (rule_tac x=" absTransfRule env M r" in bexI)
        show "transSimRule env r (absTransfRule env M r) M"
        proof (rule absRuleSim,cut_tac a5,simp)
          show "wellFormedRule env N r"
            using a1  d1 strengthenRule2Keep by blast 
        next
          show "M \<le>N"
            using a3  by auto
        qed
      next
        show "absTransfRule env M r\<in> {r'. \<exists>r. r \<in> rs2 \<and> r' = absTransfRule env M r}  "
          using d1 by blast
      qed
    qed
    have c4: "reachableUpTo {f'. \<exists>f. f \<in> Is \<and> f' = absTransfForm env M f}
      {r'. \<exists>r. r \<in> rs2 \<and> r' = absTransfRule env M r} i (abs1 M s)"
    proof (rule_tac ?fs1.0="Is" and ?rs1.0="rs2" in transSimRulesReachable)
      show "predSimSet env Is {f'. \<exists>f. f \<in> Is \<and> f' = absTransfForm env M f} M"
        using c2 by blast
    next
      show "transSimRules env rs2 {r'. \<exists>r. r \<in> rs2 \<and> r' = absTransfRule env M r} M"
        using c3 by blast
    next
      show "reachableUpTo Is rs2 i s"
        using c0 by blast
    next
      show  "\<And>r. r\<in>rs2 \<longrightarrow>deriveRule env r"
        using a13 by blast
    next
      show "\<And>f. f \<in> Is \<longrightarrow> deriveForm env f"
        using a14 by blast
    next
      show "\<forall>s i. reachableUpTo Is rs2 i s \<longrightarrow> fitEnv s env"
        using a15 by blast
    qed
    have c5:"fitEnv s env"
      using a15 c0 by blast

    have c6:"(absTransfRule (env )  M ` rs2) = {r'. \<exists>r. r \<in> rs2 \<and> r' = absTransfRule env M r}"
      by blast
      
    have c7:"(absTransfForm (env) M ` Is) = {f'. \<exists>f. f \<in> Is \<and> f' = absTransfForm env M f} "
      by blast
    show "formEval (f l k) s"
     
    proof -
      
        have d3:"formEval (absTransfForm env M (f l k)) (abs1 M s)"
          using a7' c02 c03 c04 c1 c4 c6 c7 by auto 
        
    
      have "safeForm env M  (f l k) "
        using a8 c02 c03 c04 c1 by blast 

      
      have d5:" deriveForm env (f  l k)"
        using a8 c02 c03 c04 c1 by blast
         
      have "formEval (f l k) s = formEval (absTransfForm env M (f l k)) (abs1 M s)"
        by (simp add: \<open>safeForm env M (f l k)\<close> c5 d5 safeEval1) 
      show "formEval (f l k) s "
        by (simp add: \<open>formEval (f l k) s = formEval (absTransfForm env M (f l k)) (abs1 M s)\<close> d3)
        
     
    qed
  qed
  (* Step 2: show that the system before abstraction (but after strengthening) respects the
     invariants in S. This uses the implication between S and S'. *)
  have b1: "\<forall>i invL f s j k. invL \<in> S \<longrightarrow> f \<in> set invL \<longrightarrow> reachableUpTo Is rs2 i s \<longrightarrow> j \<le> N \<longrightarrow>k\<le>N
            \<longrightarrow>  formEval (f  j k) s"
  proof ((rule allI)+,(rule impI)+)
    fix i invL f s j k
    assume c1: "f \<in> set invL " and c0: "reachableUpTo Is rs2 i s" and c02:"invL \<in> S" and
      c03:"j \<le>N" and c04:"k \<le>N"
    obtain invL' where invL': "invL' \<in> S'" "strengthenVsObsLs invL invL' N"
        using a17 c02 by blast
    obtain f' where f': "f' \<in> set invL'" "strengthenVsObs f f' N"
        using invL' c1 unfolding strengthenVsObsLs_def by blast
    show "formEval (f j k) s"
      apply(rule_tac N="N" and Is="Is" and rs="rs2" and k="i" and M="M" and f'="f'" in SymLemmaOnExcl3 )
      using a4 apply blast
      using a10 apply blast
      apply (meson a3 a5 leD leI less_le_trans)
      using c0 apply blast
      using b1' f'(1) invL'(1) apply blast
      apply (simp add: c03)
      apply (simp add: c04)
      apply (simp add: f'(2))
      using a3 a5 apply blast
      using a2 f'(1) invL'(1) by blast
  qed 
  let ?S= "{cinvL. \<exists>i j invL. i\<le>N \<and> j \<le>N \<and> invL \<in>S\<and>cinvL=map2'  invL i j }"
  (* Step 4: show that the system before abstraction and strengthening respects the
     invariants in S. This uses the correctness of strengthening. *)
  have b7: "\<forall>i s. reachableUpTo Is rs i s \<longrightarrow>
    reachableUpTo Is rs2 i s \<and> (\<forall>invL f. invL \<in> ?S \<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s)"
  proof (rule allI, rule strengthenFrmList2Prot2SimProt) 
    fix i
    have a11:"\<forall>r. r \<in> rs \<longrightarrow> (\<exists>invL i j. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> strengthenRuleByFrmL2 (map2' invL i j) r \<in> rs2) \<or> r \<in> rs2"
      using a9 strengthenBwRel_def strengthenRel_def by auto
    show "\<forall>r. r \<in> rs \<longrightarrow>
           (\<exists>invL. invL \<in> {cinvL. \<exists>i j invL. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> cinvL = map2' invL i j} \<and>
                   strengthenRuleByFrmL2 invL r \<in> rs2) \<or> r \<in> rs2"
      by (metis (mono_tags, lifting) a11 mem_Collect_eq) 
  next
    show "\<forall>i s invL f.
           reachableUpTo Is rs2 i s \<longrightarrow>
           invL \<in> {cinvL. \<exists>i j invL. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> cinvL = map2' invL i j} \<longrightarrow> f \<in> set invL \<longrightarrow> formEval f s"
    proof((rule allI)+,(rule impI)+)
      fix i s invL f
      assume c1: "reachableUpTo Is rs2 i s" and  
        c2: "invL \<in> {cinvL. \<exists>i j invL. i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> cinvL = map2' invL i j}" and 
        c3: "f \<in> set invL" (* \<and>i\<noteq>j*)
      have c4:"\<exists>i j invL0. i \<le> N \<and> j \<le> N \<and> invL0 \<in> S \<and> invL = map2' invL0 i j"
        using c2 by force
      then obtain i and j and invL0 where c5: "i \<le> N \<and> j \<le> N \<and> invL0 \<in> S \<and> invL = map2' invL0 i j" 
        by blast
      have c6: "\<exists>pf. pf \<in> set invL0 \<and> f = pf i j"
        using c3 c5 map2'Corres by blast
      then obtain pf where c7: "pf \<in> set invL0 \<and> f = pf i j"
        by blast
      show "formEval f s"
        using b1 c1 c5 c7 by blast 
    qed    
  qed
  show "formEval (f i j) s"
    using b0 b0' b01 b02 b03 b1 b7 by blast
qed 

definition strengthenDIFwRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>nat\<Rightarrow>bool" where
"strengthenDIFwRel rs S rs2 D N\<equiv>
\<forall>r'. r' \<in> rs2 \<longrightarrow> ((\<exists>r invL d i j. d \<le>D \<and> i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> r \<in> rs \<and>
                r' = strengthenRuleByFrmL2 (map2' invL  j i) r) \<or> r' \<in> rs)"

definition strengthenDIBwRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>nat\<Rightarrow>bool" where
"strengthenDIBwRel rs S rs2 D N\<equiv>
\<forall>r. r \<in> rs \<longrightarrow> ((\<exists>invL d i j. d \<le> D\<and> i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and>
                strengthenRuleByFrmL2 (map2' invL  j i) r \<in> rs2) \<or> r \<in> rs2)"

definition strengthenDIRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>nat\<Rightarrow>bool" where
"strengthenDIRel rs S rs2 D N\<equiv>
  strengthenDIFwRel rs S rs2 D N \<and> strengthenDIBwRel rs S rs2 D N"

(*definition isProtDObsInvSet::"(rule set) \<Rightarrow>( formula set)=>
 ((((nat \<Rightarrow> nat \<Rightarrow> formula) list) set))\<Rightarrow> nat \<Rightarrow> envType \<Rightarrow>bool" where [simp]:
"isProtDObsInvSet rules Is InvS D   env\<equiv>
(\<forall>i invL f s l k. l\<le>D \<and> k\<le>D \<and> invL \<in>  (InvS ) \<longrightarrow> f \<in> set invL \<longrightarrow>
           reachableUpTo Is
               rules i s \<longrightarrow>
           formEval (DabsTransfForm (env)  (f l k)) s)"*)

definition isAbstractProtInvSetAtData::"(rule set) \<Rightarrow>( formula set)=>
 ((((nat \<Rightarrow> nat \<Rightarrow> formula) list) set)) \<Rightarrow> nat \<Rightarrow>envType \<Rightarrow>bool" where [simp]:
"isAbstractProtInvSetAtData rules Is InvS  M  env\<equiv>
(\<forall>i invL f s l. l\<le>M \<and> invL \<in>  (InvS ) \<longrightarrow> f \<in> set invL \<longrightarrow>
           reachableUpTo (DabsTransfForm (env)  ` (Is))
               rules i s \<longrightarrow>
           formEval (DabsTransfForm (env)  (f 0 l)) s)" 



definition isProtObsInvSetAtData::"(rule set) \<Rightarrow>( formula set)=>
 ((((nat \<Rightarrow> nat \<Rightarrow> formula) list) set)) \<Rightarrow> nat\<Rightarrow> envType \<Rightarrow>bool" where [simp]:
"isProtObsInvSetAtData rules Is InvS   M env\<equiv>
(\<forall>i invL f s l k. l\<le>M \<and> k\<le>M \<and> invL \<in>  (InvS ) \<longrightarrow> f \<in> set invL \<longrightarrow>
           reachableUpTo Is
               rules i s \<longrightarrow>
           formEval (absTransfForm (env) M (f l k)) s)"

(*definition isProtDObsInvSet::"(rule set) \<Rightarrow>( formula set)=>( (nat =>nat=>formula) set) 
  \<Rightarrow> nat \<Rightarrow>nat \<Rightarrow> envType \<Rightarrow>bool" where [simp]:
  "isProtDObsInvSet rs Is dpInvs D N  env\<equiv>
    (\<forall> i d s k pf. i\<le>N \<and> d\<le>D \<and> (reachableUpTo Is rs k s) \<and> pf : dpInvs \<longrightarrow> 
    formEval (DabsTransfForm (env)  (pf  d i)) s)"*)


definition isParamProtInvSetAtData::"(rule set) \<Rightarrow>( formula set)=>
 ((((nat \<Rightarrow> nat \<Rightarrow> formula) ) set)) \<Rightarrow> nat\<Rightarrow> nat\<Rightarrow>bool" where [simp]:
"isParamProtInvSetAtData rules Is dpInvS D N\<equiv>
(\<forall>k   f s i d.    f \<in> dpInvS  \<longrightarrow>
           reachableUpTo Is rules  k s \<longrightarrow>
           i \<le> N \<longrightarrow> d\<le> D \<longrightarrow> formEval (f  d i) s)" 

definition isProtDObsInvSet::"(rule set) \<Rightarrow>( formula set)=>( (nat =>nat=>formula) set) 
  \<Rightarrow> nat \<Rightarrow>nat \<Rightarrow> envType \<Rightarrow>bool" where [simp]:
  "isProtDObsInvSet rs Is dpInvs D N  env\<equiv>
    (\<forall> i d s k pf. i\<le>N \<and> d\<le>D \<and> (reachableUpTo Is rs k s) \<and> pf : dpInvs \<longrightarrow> 
    formEval (DabsTransfForm (env)  (pf  d i)) s)"


definition isDParamProtInvSet::"(rule set) \<Rightarrow>( formula set)=>
 ((((nat \<Rightarrow> nat \<Rightarrow> formula) ) set)) \<Rightarrow> nat\<Rightarrow> nat\<Rightarrow>bool" where [simp]:
"isDParamProtInvSet rules Is dpInvS D N\<equiv>
(\<forall>k   f s i d.    f \<in> dpInvS  \<longrightarrow>
           reachableUpTo Is rules  k s \<longrightarrow>
           i \<le> N \<longrightarrow> d\<le> D \<longrightarrow> formEval (f  d i) s)" 


lemma DABS0:
  assumes a0:"env dontCareVar=anyType" and 
      a1:"\<And>r. r \<in> rs \<longrightarrow> DwellFormedRule env  r" 
(*\<forall>k invL f s i j. invL \<in>   (InvS ) \<longrightarrow> f \<in> set invL \<longrightarrow>
           reachableUpTo Is rules  k s \<longrightarrow>
           i \<le> N \<longrightarrow> d\<le> D \<longrightarrow> formEval (f  d i) s*)
    and a2:"\<forall>k invL f s i j. invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow>
      (reachableUpTo (DabsTransfForm env` Is) DabsRules k s) \<longrightarrow>
      i \<le> M \<longrightarrow> j\<le> M \<longrightarrow> formEval  (f i j) s"  (* invL f i j k s*)

    and a3: "\<forall>pf i d k s. pf \<in> DS' \<longrightarrow>   i \<le> M \<longrightarrow> d =0 \<longrightarrow>
      (reachableUpTo (DabsTransfForm env` Is) DabsRules k s) \<longrightarrow>
        formEval ( (pf d i)) s" 

    and a4: "\<forall>pf  d i. pf \<in> DS' \<longrightarrow>   i \<le> M \<longrightarrow> d =0 \<longrightarrow>
               DsafeForm  env   (pf d i) \<and> deriveForm env (pf d i)"  

    and a41:"\<forall> invL pf  i j. invL \<in> S' \<longrightarrow> pf \<in> set invL 
   \<longrightarrow> i \<le> M \<longrightarrow> j\<le> M \<longrightarrow>DsafeForm  env   (pf  i j) \<and> deriveForm env (pf  i j)"  

   and a42: "\<forall>pf i. pf \<in> DS' \<longrightarrow> DsymParamForm D (\<lambda>d. pf d i)"

    and a5:"DsymPredSet' D Is" 
    
    and a10D: "DsymProtRules' D rs"
    and a13: "\<And>r. r \<in> rs \<longrightarrow> deriveRule env r"
    and a14: "\<And>f. f \<in> Is \<longrightarrow> deriveForm env f"
    and a15: "\<forall>s i. reachableUpTo Is rs i s \<longrightarrow> fitEnv s env" 
    and a16:"1 \<le> D"
    and a18:"DabsTransfRule env`  rs  \<subseteq> DabsRules  "  
(*invL f i j k s*)
shows "(\<forall>k invL f s i j . invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow> 
      (reachableUpTo Is rs  k s) \<longrightarrow>
      i \<le> M \<longrightarrow> j\<le> M \<longrightarrow> formEval  (f i j) s) \<and> 
      (\<forall>k pf  s d i. pf \<in> DS' \<longrightarrow>   i \<le> M \<longrightarrow> d \<le>D\<longrightarrow>
      (reachableUpTo Is rs k s) \<longrightarrow>
        formEval ( (pf d i)) s)" (is "?Pf1 N & ?Pf2 M D")
proof(rule conjI)
  show "?Pf1 N"
  proof((rule allI)+,(rule impI)+)
    fix k invL f s i j
    assume b1:"invL \<in> S'" and b2:"f \<in> set invL" and b3:"reachableUpTo Is rs  k s" and 
      b4:"i \<le> M" and b5:"j\<le> M"
    have c1:"reachableUpTo (DabsTransfForm env` Is) DabsRules    k (Dabs1 s)"
    proof (rule_tac ?fs1.0="Is" and ?rs1.0="rs" in DtransSimRulesReachable)
      show "DpredSimSet env Is (DabsTransfForm env ` Is)" 
      proof(unfold  DpredSimSet_def DpredSim_def) 
        show "\<forall>f2\<in>DabsTransfForm env ` Is.
       \<exists>f1\<in>Is. \<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
        proof
          fix f2
          assume "f2 \<in> DabsTransfForm env ` Is"
          have "\<exists> f1. f1\<in>Is \<and> f2=DabsTransfForm env f1"
            using \<open>f2 \<in> DabsTransfForm env ` Is\<close> by blast
          then obtain f1 where "f1\<in>Is \<and> f2=DabsTransfForm env f1"
            by blast
          
          show "\<exists>f1\<in>Is. \<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
          proof(rule_tac x="f1" in bexI)  
            have "DabsTransfForm env f1 \<noteq>dontCareForm \<or>
              DabsTransfForm env f1 = dontCareForm " by blast
            moreover 
           {assume   "DabsTransfForm env f1 \<noteq>dontCareForm" (* using DsafeTransf*)
                have "\<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
              by (simp add: DabsTransfFormSim \<open>DabsTransfForm env f1 \<noteq> dontCareForm\<close> \<open>f1 \<in> Is \<and> f2 = DabsTransfForm env f1\<close> a0)
          }
          moreover
          {assume   "DabsTransfForm env f1 =dontCareForm" (* using DsafeTransf*)
                have "\<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
                  by (simp add: \<open>DabsTransfForm env f1 = dontCareForm\<close> \<open>f1 \<in> Is \<and> f2 = DabsTransfForm env f1\<close>)
          }
          ultimately  show "\<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
            by blast
          next
            show "f1 \<in> Is"
              by (simp add: \<open>f1 \<in> Is \<and> f2 = DabsTransfForm env f1\<close>)
              
          
          qed 
        qed
      qed
    next
      show "DtransSimRules env rs DabsRules"
      proof (unfold DtransSimRules_def,rule ballI)  
        fix r
        assume "r \<in> rs "
        show "Bex DabsRules (DtransSimRule env r) "
        proof
          show "DtransSimRule env r (DabsTransfRule env r)"
            by (simp add: DabsRuleSim \<open>r \<in> rs\<close> a0 a1)
        next
          show "DabsTransfRule env r \<in> DabsRules"
            using \<open>r \<in> rs\<close> a18 by blast
        qed
      qed
    next
      fix r
      show "r \<in> rs \<longrightarrow> deriveRule env r"
        by (simp add: a13)
    next
      fix f
      show "f \<in> Is \<longrightarrow> deriveForm env f"
        using a14 by presburger
    next
      show "\<forall>s i. reachableUpTo Is rs i s \<longrightarrow> fitEnv s env"
        using a15 by blast
    next
      show "reachableUpTo Is rs k s "
        using b3 by blast
    qed
    have "formEval  (f i j) (Dabs1 s)"
      using a2 b1 b2 b4 b5 c1 by presburger
    have "DsafeForm  env   (f  i j) "
      using a41 b1 b2 b4 b5 apply(drule_tac x="invL" in spec)
      apply(drule_tac x="f" in exI) by blast  
    have "DabsTransfForm  env (f i j) =f i j"   
      using a41   DsafeTransf
      by (simp add: \<open>DsafeForm env (f i j)\<close> a0) 
    show "formEval (f i j) s"
      by (metis DsafeEval1 \<open>DsafeForm env (f i j)\<close> \<open>formEval (f i j) (Dabs1 s)\<close> a0 a15 b3)
      
  qed
next
  show "\<forall> k pf s d i.
       pf \<in> DS' \<longrightarrow> i \<le> M \<longrightarrow> d \<le> D \<longrightarrow> reachableUpTo Is rs k s \<longrightarrow> formEval (  (pf d i)) s"
  proof((rule allI)+,(rule impI)+)
    fix pf i d k s
    assume  "pf \<in> DS'"  " i \<le> M"  " d \<le> D" " reachableUpTo Is rs k s"
    

    have "\<forall>s ia. reachableUpTo Is rs ia s \<longrightarrow> formEval (pf 0 i) s"  
    proof((rule allI)+, rule impI)
      fix s ia
      assume "reachableUpTo Is rs ia s "
      have " fitEnv s env"
        using \<open>reachableUpTo Is rs ia s\<close> a15 by blast

      have c1:"reachableUpTo (DabsTransfForm env` Is) DabsRules ia (Dabs1 s)"
      proof (rule_tac ?fs1.0="Is" and ?rs1.0="rs" in DtransSimRulesReachable)
        show "DpredSimSet env Is (DabsTransfForm env ` Is)" 
        proof(unfold  DpredSimSet_def DpredSim_def) 
          show "\<forall>f2\<in>DabsTransfForm env ` Is.
        \<exists>f1\<in>Is. \<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
          proof
            fix f2
            assume "f2 \<in> DabsTransfForm env ` Is"
            have "\<exists> f1. f1\<in>Is \<and> f2=DabsTransfForm env f1"
              using \<open>f2 \<in> DabsTransfForm env ` Is\<close> by blast
            then obtain f1 where "f1\<in>Is \<and> f2=DabsTransfForm env f1"
              by blast
          
            show "\<exists>f1\<in>Is. \<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
            proof(rule_tac x="f1" in bexI)  
              have "DabsTransfForm env f1 \<noteq>dontCareForm \<or>
                DabsTransfForm env f1 = dontCareForm " by blast
              moreover 
              {assume   "DabsTransfForm env f1 \<noteq>dontCareForm" (* using DsafeTransf*)
                  have "\<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
                    by (simp add: DabsTransfFormSim \<open>DabsTransfForm env f1 \<noteq> dontCareForm\<close> \<open>f1 \<in> Is \<and> f2 = DabsTransfForm env f1\<close> a0)
                }
                moreover
                {assume   "DabsTransfForm env f1 =dontCareForm" (* using DsafeTransf*)
                  have "\<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
                    by (simp add: \<open>DabsTransfForm env f1 = dontCareForm\<close> \<open>f1 \<in> Is \<and> f2 = DabsTransfForm env f1\<close>)
                }
                ultimately  show "\<forall>s. fitEnv s env \<longrightarrow> deriveForm env f1 \<longrightarrow> formEval f1 s \<longrightarrow> formEval f2 (Dabs1 s)"
                  by blast
              next
                show "f1 \<in> Is"
                  by (simp add: \<open>f1 \<in> Is \<and> f2 = DabsTransfForm env f1\<close>)
              
          
              qed 
            qed
          qed
        next
          show "DtransSimRules env rs DabsRules"
          proof (unfold DtransSimRules_def,rule ballI)  
            fix r
            assume "r \<in> rs "
            show "Bex DabsRules (DtransSimRule env r) "
            proof
              show "DtransSimRule env r (DabsTransfRule env r)"
                by (simp add: DabsRuleSim \<open>r \<in> rs\<close> a0 a1)
            next
              show "DabsTransfRule env r \<in> DabsRules"
                using \<open>r \<in> rs\<close> a18 by blast
            qed
          qed
        next
          fix r
          show "r \<in> rs \<longrightarrow> deriveRule env r"
            by (simp add: a13)
        next
          fix f
          show "f \<in> Is \<longrightarrow> deriveForm env f"
            using a14 by presburger
        next
          show "\<forall>s i. reachableUpTo Is rs i s \<longrightarrow> fitEnv s env"
            using a15 by blast
        next
          show "reachableUpTo Is rs ia s "
            using \<open>reachableUpTo Is rs ia s\<close> by auto 
        qed
        have "formEval  (pf 0 i) (Dabs1 s)"
          using a3 c1   \<open>pf \<in> DS' \<close> \<open>i \<le> M \<close>
         by auto
       have "DsafeForm  env   (pf  0 i) "
         using a4  \<open>pf \<in> DS' \<close> \<open>i \<le> M \<close> by auto 
       have "DabsTransfForm  env (pf 0 i) =pf 0 i"   
         using a41   DsafeTransf
         by (auto simp add: \<open>DsafeForm env (pf 0 i)\<close> a0) 
       
      have " formEval (pf 0 i) (Dabs1 s)"
        using \<open>formEval (pf 0 i) (Dabs1 s)\<close> by auto
      show "formEval (pf 0 i) s"
        using DsafeEval1 \<open>DsafeForm env (pf 0 i)\<close> \<open>fitEnv s env\<close> \<open>formEval (pf 0 i) (Dabs1 s)\<close> a0 by presburger
    qed
        
    show  " formEval (  (pf d i)) s"
      apply (rule_tac f="pf" and k="k" in DSymLemmaOnExcl)
      using a5 apply simp
      using a10D apply simp
      using a16 apply simp
      using \<open>reachableUpTo Is rs k s\<close>  apply simp
      using a42 \<open>pf \<in> DS' \<close> apply blast
      using \<open>\<forall>s ia. reachableUpTo Is rs ia s \<longrightarrow> formEval (pf 0 i) s\<close> apply blast
      using \<open>d \<le> D\<close> by simp 
  qed
qed


lemma DABS:
  assumes a0:"env dontCareVar=anyType" and 
      a1:"\<And>r. r \<in> rs \<longrightarrow> DwellFormedRule env  r" 

    and a2:"\<forall>k invL f s i j. invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow>
      (reachableUpTo (DabsTransfForm env` Is) DabsRules k s) \<longrightarrow>
      i \<le> M \<longrightarrow> j\<le> M \<longrightarrow> formEval  (f i j) s" 

    and a3: "\<forall>  k s d i.    i \<le> M \<longrightarrow> d =0 \<longrightarrow>
      (reachableUpTo (DabsTransfForm env` Is) DabsRules k s) \<longrightarrow>
        formEval ( (dataInv' d i)) s" 

    and a4: "\<forall> i d.   i \<le> M \<longrightarrow> d =0 \<longrightarrow>
               DsafeForm  env   (dataInv' d i) \<and> deriveForm env (dataInv' d i)"  

    and a41:"\<forall>invL pf i j. invL \<in> S' \<longrightarrow> pf \<in> set invL \<longrightarrow>i \<le> M \<longrightarrow> j\<le> M
   \<longrightarrow> DsafeForm  env   (pf  i j) \<and> deriveForm env (pf  i j)"  

   and a42: "\<forall> i.  DsymParamForm D (\<lambda>d. dataInv' d i)"

    and a5:"DsymPredSet' D Is" 
    and a6:"dataParamVsObs dataInv dataInv' pv gv"
    and a7:" \<forall>k s i. reachableUpTo Is rs k s \<longrightarrow>i \<le> M \<longrightarrow> (\<exists>d. s (Para pv i) = data d \<and> d \<le> D)"
    and a10D: "DsymProtRules' D rs"
    and a13: "\<And>r. r \<in> rs \<longrightarrow> deriveRule env r"
    and a14: "\<And>f. f \<in> Is \<longrightarrow> deriveForm env f"
    and a15: "\<forall>s i. reachableUpTo Is rs i s \<longrightarrow> fitEnv s env" 
    and a16:"1 \<le> D"
    and a18:"DabsTransfRule env`  rs  \<subseteq> DabsRules  "  

shows "(\<forall>k invL f s i j. invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow>
      (reachableUpTo Is rs  k s) \<longrightarrow>
      i \<le> M \<longrightarrow> j\<le> M \<longrightarrow> formEval  (f i j) s) \<and> 
      (\<forall> k s d i.   i \<le> M \<longrightarrow>
      (reachableUpTo Is rs k s) \<longrightarrow>
        formEval ( (dataInv d i)) s)" (is "?Pf1 N & ?Pf2 M D")
proof -
   let ?DS'="{dataInv'}"
   have b1:"(\<forall>k invL f s i j. invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow>
      (reachableUpTo Is rs  k s) \<longrightarrow>
      i \<le> M \<longrightarrow> j\<le> M \<longrightarrow> formEval  (f i j) s) \<and> 
      (\<forall> k pf s d i. pf \<in> ?DS' \<longrightarrow>   i \<le> M \<longrightarrow> d \<le>D \<longrightarrow>
      (reachableUpTo Is rs k s) \<longrightarrow>
        formEval ( (pf d i)) s)"
     apply(rule_tac ?S'="S'" and  DS'="?DS'"  and Is="Is" and rs="rs" in DABS0)
     using assms(1) apply assumption
     using assms(2) apply assumption
     using assms(3) apply assumption  
     using assms(4) apply auto[1]
     using assms(5) apply auto[1]
     using assms(6) apply assumption
     using assms(7) apply auto[1]
     using assms(8) apply assumption 
     using assms by auto
   then have b2:"(\<forall>pf i d k s. pf \<in> ?DS' \<longrightarrow>   i \<le> M \<longrightarrow> d \<le>D \<longrightarrow>
      (reachableUpTo Is rs k s) \<longrightarrow>
        formEval ( (pf d i)) s)"
     by blast
   have "?Pf2 M D" 
   proof((rule allI)+,(rule impI)+)
     fix i d k s
     assume c1:"i \<le> M"    " reachableUpTo Is rs k s"
     show " formEval (dataInv d i) s" 
       apply(rule_tac D="D" and Is="Is" and rs="rs" and k="k" and s="s" and d="d" in  DSymLemmaOnDataCoherence)
       using assms apply auto[1]
       using assms apply auto[1]
       apply (simp add: \<open>reachableUpTo Is rs k s\<close>) 
       using assms apply auto[1]
           apply (simp add: b1 c1(1))
       using a7 c1(1) apply auto[1]
       using assms apply auto[1] 
       by (simp add: a42)
   qed
   with b1 show ?thesis
     by blast
 qed


subsection \<open>replace link \<close>

(*n[i].data = auxDATA ---- lhe =rhe
v:=lhe \<longrightarrow>v:=rhe
memDATA:= n[i].data;--->memDATA:=auxData*)


primrec replaceStm::"statement \<Rightarrow>varType \<Rightarrow> varType \<Rightarrow>statement" where
"replaceStm (assign pair) lhv rhv =
  (let v =fst pair in let e =snd pair in 
  if ( e=(IVar lhv) ) then assign (v, (IVar rhv)) else assign (v, e))" |

"replaceStm (parallel  s1 s2) lhv rhv =
  parallel (replaceStm s1 lhv rhv) (replaceStm s2 lhv rhv) "  |

"replaceStm skip lhv rhv = skip" |

"replaceStm (iteStm b s1 s2) lhv rhv=
  iteStm b (replaceStm s1 lhv rhv) (replaceStm s2 lhv rhv) "  |   

"replaceStm (forallStm pf N) lhv rhv=(forallStm pf N)" |

"replaceStm (forallStmExcl pf i N) lhv rhv=(forallStmExcl pf i N)"

lemma replaceStmVars1:
   
  shows "(x:varOfStmt S1 )\<longrightarrow>(x:varOfStmt (replaceStm (S1 ) lhv rhv))"
proof(induct_tac S1,auto)qed


lemma replaceStmVars2:
   
  shows "(x:varOfStmt (replaceStm (S1 ) lhv rhv)) \<longrightarrow>(x:varOfStmt S1 )"
proof(induct_tac S1,auto simp add:Let_def)qed


lemma replaceStmSame:
  assumes a1:"s lhv= s rhv"
  shows "trans1 stm s=trans1 (replaceStm stm lhv rhv) s" (is "?P stm")
proof(induct_tac stm )
  show "?P skip"
    by auto
next
  fix x
  show "?P (assign x)"
  proof(case_tac "snd x =(IVar lhv)")
    assume "snd x =(IVar lhv)"
    show "?P (assign x)"
    proof
      fix xa
      show "trans1 (assign x) s xa = trans1 (replaceStm (assign x) lhv rhv) s xa"
      proof(case_tac "xa = fst x")
        show "trans1 (assign x) s xa = trans1 (replaceStm (assign x) lhv rhv) s xa"
          by (smt (z3) assms evalVar fst_conv replaceStm.simps(1) snd_conv trans1.simps(2))
      next
        show "trans1 (assign x) s xa = trans1 (replaceStm (assign x) lhv rhv) s xa"
          by (smt (z3) assms evalVar fst_conv replaceStm.simps(1) snd_conv trans1.simps(2))
        
      qed
    qed
  next
     assume "snd x~=(IVar lhv)"
     show "?P (assign x)"
       by (simp add: \<open>snd x \<noteq> IVar lhv\<close>)
   qed
 next
   fix S1 S2
   assume "?P S1" "?P S2"
   show "?P (parallel S1 S2)"
   proof
     fix x
     show " trans1 (S1 || S2) s x = trans1 (replaceStm (S1 || S2) lhv rhv) s x "
     proof(case_tac "x:varOfStmt S1")
       assume "x:varOfStmt S1"
       have "x:varOfStmt (replaceStm (S1 ) lhv rhv)"
         by (simp add: \<open>x \<in> varOfStmt S1\<close> replaceStmVars1) 
         
       show " trans1 (S1 || S2) s x = trans1 (replaceStm (S1 || S2) lhv rhv) s x "
         by (simp add: \<open>trans1 S1 s = trans1 (replaceStm S1 lhv rhv) s\<close> \<open>x \<in> varOfStmt (replaceStm S1 lhv rhv)\<close> \<open>x \<in> varOfStmt S1\<close>)
     next
        assume "\<not>x:varOfStmt S1"
        have "~x:varOfStmt (replaceStm (S1 ) lhv rhv)"
          using \<open>x \<notin> varOfStmt S1\<close> replaceStmVars2 by blast 
          
        show " trans1 (S1 || S2) s x = trans1 (replaceStm (S1 || S2) lhv rhv) s x "
          by (simp add: \<open>trans1 S2 s = trans1 (replaceStm S2 lhv rhv) s\<close> \<open>x \<notin> varOfStmt (replaceStm S1 lhv rhv)\<close> \<open>x \<notin> varOfStmt S1\<close>)
      qed     
    qed    
 qed(auto)
     

 

    
primrec replaceRule::"rule \<Rightarrow>varType \<Rightarrow> varType \<Rightarrow>rule" where
"replaceRule (guard g stm) l r=(guard g (replaceStm stm l r))"

definition replaceRel::"varType \<Rightarrow> varType  \<Rightarrow> rule \<Rightarrow>rule\<Rightarrow> formula \<Rightarrow>bool" where 
"replaceRel lv rv r1 r2 pref1\<equiv>
  (has_conj (pre(r1))   pref1)  \<and> r2= replaceRule r1 lv rv "

lemma replaceRulePre:
  assumes "replaceRel lv rv r1 r2 pref" (*"formEval  (implyForm pref (eqn (IVar lv) (IVar rv))) s"*)
  "formEval (pre r1) s"
shows "formEval (pre r2) s"
proof -
  have "\<exists> g1 act1. r1=guard g1 act1"
    by (meson pre.cases)
  then obtain g1 and act1 where a1:"r1=guard g1 act1"
    by blast
  have "\<exists> g2 act2. r2=guard g2 act2"
    by (meson pre.cases)
  then obtain g2 and act2 where a2:"r2=guard g2 act2"
    by blast
  have a3:"g1 =g2 \<and> act2=replaceStm act1 lv rv \<and> (has_conj (pre(r1)) pref)"
    using assms a1 a2 apply(unfold replaceRel_def,auto)
    done
  (*have a4:"formEval pref s"
    using a3 assms(3) has_conj_correct by auto*)
  show ?thesis
    using a1 a2 a3  assms(2)  by auto
qed

lemma replaceRulePreInv:
  assumes "replaceRel lv rv r1 r2 pref" (*"formEval  (implyForm pref (eqn (IVar lv) (IVar rv))) s"*)
  "formEval (pre r2) s"
shows "formEval (pre r1) s"
proof -
  have "\<exists> g1 act1. r1=guard g1 act1"
    by (meson pre.cases)
  then obtain g1 and act1 where a1:"r1=guard g1 act1"
    by blast
  have "\<exists> g2 act2. r2=guard g2 act2"
    by (meson pre.cases)
  then obtain g2 and act2 where a2:"r2=guard g2 act2"
    by blast
  have a3:"g1 =g2 \<and> act2=replaceStm act1 lv rv \<and> (has_conj (pre(r1)) pref)"
    using assms a1 a2 apply(unfold replaceRel_def,auto)
    done
  (*have a4:"formEval pref s"
    using a3 assms(3) has_conj_correct by auto*)
  show ?thesis
    using a1 a2 a3  assms(2)  by auto
qed

lemma replaceRulePreEq:
  assumes "replaceRel lv rv r1 r2 pref" (*"formEval  (implyForm pref (eqn (IVar lv) (IVar rv))) s"*)
  shows " (pre r1) = (pre r2)"
proof -
  have "\<exists> g1 act1. r1=guard g1 act1"
    by (meson pre.cases)
  then obtain g1 and act1 where a1:"r1=guard g1 act1"
    by blast
  have "\<exists> g2 act2. r2=guard g2 act2"
    by (meson pre.cases)
  then obtain g2 and act2 where a2:"r2=guard g2 act2"
    by blast
  have a3:"g1 =g2 \<and> act2=replaceStm act1 lv rv \<and> (has_conj (pre(r1)) pref)"
    using assms a1 a2 apply(unfold replaceRel_def,auto)
    done
  (*have a4:"formEval pref s"
    using a3 assms(3) has_conj_correct by auto*)
  show ?thesis
    using a1 a2 a3     by auto
qed


  
lemma replaceRuleEq:
  assumes "replaceRel lv rv r1 r2 pref" "formEval  (implyForm pref (eqn (IVar lv) (IVar rv))) s"
  "formEval (pre r1) s"
  shows "trans1 (act r1) s =trans1 (act r2) s" 
proof -
  have "\<exists> g1 act1. r1=guard g1 act1"
    by (meson pre.cases)
  then obtain g1 and act1 where a1:"r1=guard g1 act1"
    by blast
  have "\<exists> g2 act2. r2=guard g2 act2"
    by (meson pre.cases)
  then obtain g2 and act2 where a2:"r2=guard g2 act2"
    by blast
  have a3:"g1 =g2 \<and> act2=replaceStm act1 lv rv \<and> (has_conj (pre(r1))  pref)"
    using assms a1 a2 apply(unfold replaceRel_def,auto)
    done
  have a4:"formEval pref s"
    using a3 assms(3) has_conj_correct by auto
  have a4:"s lv =s rv"
    using a4 assms(2) by fastforce 
  show "trans1 (act r1) s =trans1 (act r2) s" 
    using a1 a2 a3 apply simp
    by (meson a4 replaceStmSame)
qed

lemma replaceRuleEqInv:
  assumes "replaceRel lv rv r1 r2 pref" "formEval  (implyForm pref (eqn (IVar lv) (IVar rv))) s"
  "formEval (pre r2) s"
  shows "trans1 (act r1) s =trans1 (act r2) s" 
proof -
  have "\<exists> g1 act1. r1=guard g1 act1"
    by (meson pre.cases)
  then obtain g1 and act1 where a1:"r1=guard g1 act1"
    by blast
  have "\<exists> g2 act2. r2=guard g2 act2"
    by (meson pre.cases)
  then obtain g2 and act2 where a2:"r2=guard g2 act2"
    by blast
  have a3:"g1 =g2 \<and> act2=replaceStm act1 lv rv \<and> (has_conj (pre(r1))  pref)"
    using assms a1 a2 apply(unfold replaceRel_def,auto)
    done
  have a30:"pre r1= pre r2"
    using assms(1) replaceRulePreEq by auto
  have a4:"formEval (pre r1)  s"
    by (simp add: a30 assms(3))
    
  have a4:"formEval pref s"
    using a3 a4 has_conj_correct by auto 
  have a4:"s lv =s rv"
    using a4 assms(2) by fastforce 
  show "trans1 (act r1) s =trans1 (act r2) s" 
    using a1 a2 a3 apply simp
    by (meson a4 replaceStmSame)
qed
(*replace 
n[i].st = E −\<rightarrow> n[i].data = auxDATA
guard \<Longrightarrow> r
rule "Idle"
n[i].st = E ==>
n[i].st:= I;
x:= true;
memDATA:= n[i].data;
endrule

----> 
rule "IdleRep"
n[i].st = E ==>
n[i].st:= I;
x:= true;
memDATA:= auxDATA;
endrule*)
definition isProtInv::"rule set \<Rightarrow>formula set \<Rightarrow>formula \<Rightarrow>bool" where 
"isProtInv rs Is f \<equiv> \<forall>s i. reachableUpTo Is rs i s \<longrightarrow>formEval f s"

lemma replaceFrmListProt1SimProt:
  assumes a1: "\<forall>r. r \<in> rs \<longrightarrow>
   ((\<exists>lv rv r2 pref. replaceRel lv rv r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs I (implyForm pref (eqn (IVar lv) (IVar rv))) ) \<or> r \<in> rs')"  
  
  shows "\<forall>s. reachableUpTo I rs i s \<longrightarrow>
             (reachableUpTo I rs' i s )" (is "?P i")
proof (induct_tac i)  
  show "?P 0"
    by (meson  reachableSet0 reachableUpTo0) 
next
  fix n
  assume b0:"?P n"
  show "?P (Suc n)"
  proof((rule allI)+,(rule impI)+)
    fix s
    assume b1: "reachableUpTo I rs (Suc n) s"  
    have c1:"\<exists>s0 g a. guard g a \<in> rs \<and> reachableUpTo I rs n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by (metis b1 reachableUpToSuc) 
    from c1 obtain s0 g a where c1:
      "guard g a \<in> rs \<and> reachableUpTo I rs n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by blast
    let ?r="guard g a"
    have c2: "(\<exists>lv rv r2 pref. replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs I (implyForm pref (eqn (IVar lv) (IVar rv)))) 
      \<or> ?r \<in> rs'"
      using a1 c1 by blast
    moreover
    {
      assume c2:"\<exists>lv rv r2 pref. replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs I (implyForm pref (eqn (IVar lv) (IVar rv)))"
      from c2 obtain lv rv r2 pref where c2:
        " replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs'  \<and> isProtInv  rs I (implyForm pref (eqn (IVar lv) (IVar rv)))"
        by blast
      have c3:"formEval (pre r2) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRulePre) 
      have c5: "trans1 (act (r2)) s0 = trans1 (act ?r) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRuleEq) 
      have c7: "reachableUpTo I rs' n s0"
        using b0 c1 by blast 
      have "reachableUpTo I rs' (Suc n) (trans1 (act (r2)) s0)"
        by (metis act.simps c2 c3 c7 pre.cases pre.simps reachableSetNext) 
      have "reachableUpTo I rs' (Suc n) s"
        using \<open>reachableUpTo I rs' (Suc n) (trans1 (act r2) s0)\<close> c1 c5 by auto
    }
    moreover
    {
      assume c2: "guard g a \<in> rs'"
      have "reachableUpTo I rs' (Suc n) s"
        using  b0 c1 c2 reachableSetNext by blast 
    }
    ultimately show "reachableUpTo I rs' (Suc n) s "
      using assms by blast 
  qed
qed 

lemma replaceFrmListProt1SimProt2:
  assumes a1: "\<forall>r2. r2 \<in> rs' \<longrightarrow>
   ((\<exists>lv rv r pref. replaceRel lv rv r r2 pref \<and> r   \<in> rs \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv))) ) \<or> r2 \<in> rs)"  
  and a2:"\<forall>r. r \<in>rs \<longrightarrow>(\<exists>lv rv r2 pref. replaceRel lv rv r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))) 
      \<or> r \<in> rs'"
  shows "\<forall>s. reachableUpTo I rs' i s =
             (reachableUpTo I rs i s )" (is "?P i") 
proof (induct_tac i)  
  show "?P 0"
    by (meson  reachableSet0 reachableUpTo0) 
next
  fix n
  assume b0:"?P n"
  show "?P (Suc n)"
  proof((rule allI)+,(rule iffI))
    fix s
    assume b1:" reachableUpTo I rs' (Suc n) s"
     have c1:"\<exists>s0 g a. guard g a \<in> rs' \<and> reachableUpTo I rs' n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by (metis b1 reachableUpToSuc) 
    from c1 obtain s0 g a where c1:
      "guard g a \<in> rs' \<and> reachableUpTo I rs' n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by blast
    let ?r2="guard g a"
    have c2: "(\<exists>lv rv r pref. replaceRel lv rv r ?r2 pref \<and> r   \<in> rs \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))) 
      \<or> ?r2 \<in> rs"
      using a1 c1 by blast
    
    moreover
    {
      assume c2:"(\<exists>lv rv r pref. replaceRel lv rv r ?r2 pref \<and> r   \<in> rs \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))) "
      from c2 obtain lv rv r pref where c2:
        " replaceRel lv rv r ?r2 pref \<and> r   \<in> rs  \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))"
        by blast
      have c3:"formEval (pre ?r2) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRulePre) 
      have c5: "trans1 (act (?r2)) s0 = trans1 (act ?r2) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRuleEq) 
      have "pre r =pre ?r2"
        using c2 replaceRulePreEq by blast
        
       have c3:"formEval (pre r) s0"
         using \<open>pre r = pre (g \<triangleright> a)\<close> c3 by auto 
      have c5: "trans1 (act (?r2)) s0 = trans1 (act ?r2) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRuleEq)
      have c7: "reachableUpTo I rs n s0"
        using b0 c1 by blast 
      have "reachableUpTo I rs (Suc n) (trans1 (act (r)) s0)"
        by (metis act.simps c2 c3 c7 pre.cases pre.simps reachableSetNext) 
      have "reachableUpTo I rs (Suc n) s"
        using \<open>reachableUpTo I rs (Suc n) (trans1 (act r) s0)\<close> c1 c2 isProtInv_def replaceRuleEqInv by auto 
    }
    moreover
    {
      assume c2: "guard g a \<in> rs"
      have "reachableUpTo I rs (Suc n) s"
        using  b0 c1 c2 reachableSetNext by blast 
    }
    ultimately show "reachableUpTo I rs (Suc n) s "
      using assms by blast   
  next 
    fix s
    assume b1:" reachableUpTo I rs (Suc n) s"
     have c1:"\<exists>s0 g a. guard g a \<in> rs \<and> reachableUpTo I rs n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by (metis b1 reachableUpToSuc) 
    from c1 obtain s0 g a where c1:
      "guard g a \<in> rs \<and> reachableUpTo I rs n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by blast
    let ?r="guard g a"
    have c2: "(\<exists>lv rv r2 pref. replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))) 
      \<or> ?r \<in> rs'"
      by (simp add: a2 c1)
      
    
    moreover
    {
      assume c2:"(\<exists>lv rv r2 pref. replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv))))  "
      from c2 obtain lv rv r2 pref where c2:
        " replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs'  \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))"
        by blast
      have c3:"formEval (pre ?r) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRulePre) 
      have c5: "trans1 (act (?r)) s0 = trans1 (act r2) s0"
        using b0 c1 c2 c3 isProtInv_def replaceRuleEq by blast 
      have "pre ?r =pre r2"
        using c2 replaceRulePreEq by blast
        
       have c3:"formEval (pre r2) s0"
         using \<open>pre (g \<triangleright> a) = pre r2\<close> c3 by auto 
      have c5: "trans1 (act (r2)) s0 = trans1 (act r2) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRuleEq)
      have c7: "reachableUpTo I rs n s0"
        using b0 c1 by blast 
      have "reachableUpTo I rs' (Suc n) (trans1 (act (r2)) s0)"
        by (metis \<open>pre (g \<triangleright> a) = pre r2\<close> act.elims b0 c1 c2 pre.simps reachableSetNext) 
      have "reachableUpTo I rs' (Suc n) s"
        by (metis \<open>reachableUpTo I rs' (Suc n) (trans1 (act r2) s0)\<close> act.simps b0 c1 c2 c3 isProtInv_def replaceRuleEqInv)  
    }
    moreover
    {
      assume c2: "guard g a \<in> rs'"
      have "reachableUpTo I rs' (Suc n) s"
        using  b0 c1 c2 reachableSetNext by blast 
    }
    ultimately show "reachableUpTo I rs' (Suc n) s "
      using assms by blast  
  qed
qed 

lemma replaceCMP:
  assumes "\<forall>k invL f s i j.
       invL \<in> set INVS \<longrightarrow>
       f \<in> set invL \<longrightarrow>
       reachableUpTo IS RS' k s \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> formEval (f i j) s"
  "\<forall>r. r \<in> RS \<longrightarrow>
   ((\<exists>lv rv r2 pref invL j.  j\<le>N \<and>replaceRel (lv j) rv r r2 (pref j) \<and> r2   \<in> RS' \<and> invL \<in> set INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL ) \<or> r \<in> RS')"  

   "\<forall>r2. r2 \<in> RS' \<longrightarrow>
   ((\<exists>lv rv r pref invL j.  j\<le>N \<and>replaceRel (lv j) rv r r2 (pref j) \<and> r   \<in> RS \<and> invL \<in> set INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL ) \<or> r2 \<in> RS)"
    
  shows "\<forall>k invL f s i j.
       invL \<in> set INVS \<longrightarrow>
       f \<in> set invL \<longrightarrow>
       reachableUpTo IS RS k s \<longrightarrow> i \<le> N \<longrightarrow> j \<le> N \<longrightarrow> formEval (f i j) s"
proof((rule allI)+,(rule impI)+)
  fix k invL f s i0 j0
  assume "invL \<in> set INVS" " f \<in> set invL"  "reachableUpTo IS RS k s" "i0 \<le> N" " j0 \<le> N"
  let ?invset="{f. \<exists>invL f' i j. i \<le> N \<and> j \<le> N \<and>invL \<in> set INVS \<and> f' \<in> set invL}"
  have "\<forall>r. r \<in> RS \<longrightarrow>
   ((\<exists>lv rv r2 pref. replaceRel lv rv r r2 pref \<and> r2   \<in> RS' \<and> isProtInv  RS' IS (implyForm pref (eqn (IVar lv) (IVar rv))) ) \<or> r \<in> RS')"  
  proof(rule allI,rule impI)
    fix r
    assume "r \<in> RS"
    have "((\<exists>lv rv r2 pref invL j.  j\<le>N \<and>replaceRel (lv j) rv r r2 (pref j) \<and> r2   \<in> RS' \<and> invL \<in> set INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL ) \<or> r \<in> RS')"
      by (simp add: \<open>r \<in> RS\<close> assms(2))
    moreover
    {assume b1:"(\<exists>lv rv r2 pref invL j.  j\<le>N \<and>replaceRel (lv j) rv r r2 (pref j) \<and> r2   \<in> RS' \<and> invL \<in> set INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL )"
      from b1 obtain lv rv r2 pref invL j where b2:" ( j\<le>N \<and>replaceRel (lv j) rv r r2 (pref j) \<and> r2   \<in> RS' \<and> invL \<in> set INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL )"
        by blast
      have "(\<exists>lv rv r2 pref. replaceRel lv rv r r2 pref \<and> r2 \<in> RS' \<and> isProtInv RS' IS (pref \<longrightarrow>\<^sub>f IVar lv =\<^sub>f IVar rv)) \<or> r \<in> RS'"
        apply(rule disjI1)
        apply(rule_tac x="lv j" in exI) apply(rule_tac x="rv" in exI)  apply(rule_tac x="r2" in exI)
        apply(rule_tac x="pref j" in exI)
        apply(rule conjI)
        apply (simp add: b2)
        using assms(1) b2 isProtInv_def by blast
    }
   moreover
   {assume b1:" r \<in> RS'"
     have "(\<exists>lv rv r2 pref. replaceRel lv rv r r2 pref \<and> r2 \<in> RS' \<and> isProtInv RS' IS (pref \<longrightarrow>\<^sub>f IVar lv =\<^sub>f IVar rv)) \<or> r \<in> RS'"
       by(rule disjI2,cut_tac b1,assumption)
   }
   ultimately 
   show "(\<exists>lv rv r2 pref. replaceRel lv rv r r2 pref \<and> r2 \<in> RS' \<and> isProtInv RS' IS (pref \<longrightarrow>\<^sub>f IVar lv =\<^sub>f IVar rv)) \<or> r \<in> RS'"
     by blast
 qed
 
  have "\<forall>r2. r2 \<in> RS' \<longrightarrow>
   ((\<exists>lv rv r pref .   replaceRel (lv ) rv r r2 (pref ) \<and> r   \<in> RS   
      \<and> isProtInv  RS' IS (implyForm pref (eqn (IVar lv) (IVar rv))))  \<or> r2 \<in> RS)"
 proof(rule allI,rule impI)
    fix r20
    assume "r20 \<in> RS'"
    have "((\<exists>lv rv r pref invL j.  j\<le>N \<and>replaceRel (lv j) rv r r20 (pref j) \<and> r   \<in> RS \<and> invL \<in> set INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL ) \<or> r20 \<in> RS)"
      by (simp add: \<open>r20 \<in> RS'\<close> assms(3))
    moreover
    {assume b1:"(\<exists>lv rv r pref invL j.  j\<le>N \<and>replaceRel (lv j) rv r r20 (pref j) \<and> r   \<in> RS \<and> invL \<in> set INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL )"
      from b1 obtain lv rv r pref invL j where b2:" ( j\<le>N \<and>replaceRel (lv j) rv r r20 (pref j) \<and> r   \<in> RS \<and> invL \<in> set INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL )"
        by blast
      have "(\<exists>lv rv r pref  . replaceRel lv rv r r20 pref \<and> r \<in> RS \<and> isProtInv RS' IS (pref \<longrightarrow>\<^sub>f IVar lv =\<^sub>f IVar rv)) \<or> r20 \<in> RS"
        apply(rule disjI1)
        apply(rule_tac x="lv j" in exI) apply(rule_tac x="rv" in exI)  apply(rule_tac x="r" in exI)
        apply(rule_tac x="pref j" in exI) 
        apply(rule conjI)
        apply (simp add: b2)
        using assms(1) b2 isProtInv_def by blast
    }
   moreover
   {assume b1:" r20 \<in> RS"
     have "(\<exists>lv rv r pref. replaceRel lv rv r r20 pref \<and> r \<in> RS \<and> isProtInv RS' IS (pref \<longrightarrow>\<^sub>f IVar lv =\<^sub>f IVar rv)) \<or> r20 \<in> RS"
       by(rule disjI2,cut_tac b1,assumption)
   }
   ultimately 
   show "(\<exists>lv rv r pref. replaceRel lv rv r r20 pref \<and> r \<in> RS \<and> isProtInv RS' IS (pref \<longrightarrow>\<^sub>f IVar lv =\<^sub>f IVar rv)) \<or> r20 \<in> RS"
     by blast
 qed 
  have "reachableUpTo IS RS' k s"
    using \<open>\<forall>r. r \<in> RS \<longrightarrow> (\<exists>lv rv r2 pref. replaceRel lv rv r r2 pref \<and> r2 \<in> RS' \<and> isProtInv RS' IS (pref \<longrightarrow>\<^sub>f IVar lv =\<^sub>f IVar rv)) \<or> r \<in> RS'\<close> \<open>\<forall>r2. r2 \<in> RS' \<longrightarrow> (\<exists>lv rv r pref. replaceRel lv rv r r2 pref \<and> r \<in> RS \<and> isProtInv RS' IS (pref \<longrightarrow>\<^sub>f IVar lv =\<^sub>f IVar rv)) \<or> r2 \<in> RS\<close> \<open>reachableUpTo IS RS k s\<close> replaceFrmListProt1SimProt2 by blast
  show "formEval (f i0 j0) s"
    using \<open>f \<in> set invL\<close> \<open>i0 \<le> N\<close> \<open>invL \<in> set INVS\<close> \<open>j0 \<le> N\<close> \<open>reachableUpTo IS RS' k s\<close> assms(1) by auto
qed  

definition repFwRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>bool" where
"repFwRel RS INVS RS' N\<equiv>
  (\<forall>r. r \<in> RS \<longrightarrow>
   ((\<exists>lv rv r2 pref invL j.  j\<le>N \<and>replaceRel (lv j) rv r r2 (pref j) \<and> r2   \<in> RS' \<and> invL \<in>   INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL ) \<or> r \<in> RS'))"

definition repBwRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>bool" where
"repBwRel RS INVS RS' N\<equiv>
  (\<forall>r2. r2 \<in> RS' \<longrightarrow>
   ((\<exists>lv rv r pref invL j.  j\<le>N \<and>replaceRel (lv j) rv r r2 (pref j) \<and> r   \<in> RS \<and> invL \<in>   INVS \<and>
      (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) \<in> set invL ) \<or> r2 \<in> RS))"

definition repEqRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>bool" where
"repEqRel RS INVS RS' N\<equiv> repFwRel RS INVS RS' N \<and> repBwRel RS INVS RS' N"

lemma repRelBwUnion:
  assumes a1:"repBwRel rs1 S rs1' N " and
  a2:"repBwRel rs2 S rs2' N"
  shows "repBwRel (rs1 \<union> rs2) S (rs1' \<union> rs2') N"
  apply(cut_tac a1 a2, unfold repBwRel_def)
  by fastforce 
  

lemma repRelBwRefl': 
  shows "repBwRel rs S rs N"
  apply( unfold repBwRel_def)
  by (metis)


lemma repRelFwUnion:
  assumes a1:"repFwRel rs1 S rs1' N " and
  a2:"repFwRel rs2 S rs2' N"
  shows "repFwRel (rs1 \<union> rs2) S (rs1' \<union> rs2') N"
  apply(cut_tac a1 a2, unfold repFwRel_def)
   by fastforce  
  

lemma repRelFwRefl': 
  shows "repFwRel rs S rs N"
  apply( unfold repFwRel_def)
  by (metis)

lemma repEqRefl:
  shows "repEqRel r S r N"
  using repRelBwRefl' repRelFwRefl'  repEqRel_def by force

 

lemma repEqRelUnion:
  assumes a1:"repEqRel rs1 S rs1' N " and
  a2:"repEqRel rs2 S rs2' N"
  shows "repEqRel (rs1 \<union> rs2) S (rs1' \<union> rs2') N"
  apply(cut_tac a1 a2, unfold repEqRel_def)
  by (simp add: repRelFwUnion repRelBwUnion) 

lemma repFwExt1:
  assumes 
a2:"\<forall>i j. replaceRel (lv j) rv (r j) ( r2 j) (pref j) " and 
a4:"[ (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) ] : S"
shows "repFwRel (oneParamCons N r)  S (oneParamCons N r2) N "
proof(unfold repFwRel_def,rule allI,rule impI)
  fix ra
  assume a1:"ra \<in> oneParamCons N (r ) "
  from a1 have b1:"\<exists>i. i\<le>N &ra=r  i"
    by auto
  then obtain i where b1:"i\<le>N &ra=r i"
    by blast  
    
  show "(\<exists>lv rv r2a pref invL j. j \<le> N \<and> replaceRel (lv j) rv ra r2a (pref j) \<and> r2a \<in> oneParamCons N r2 \<and> invL \<in> S \<and> (\<lambda>i j. pref j \<longrightarrow>\<^sub>f IVar (lv j) =\<^sub>f IVar rv) \<in> set invL) \<or>
          ra \<in> oneParamCons N r2"
    apply(rule disjI1)  
    apply(rule_tac x="lv" in exI)
    apply(rule_tac exI[where x=rv])
    apply(rule_tac x="r2 i" in exI)
    apply(rule exI[where x=pref])
    apply(
        rule exI[where x="[ (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) ]"])
    apply(    rule exI[where x=i])
    apply(cut_tac a1 b1 a2 a4,auto)
    done
qed

lemma repBwExt1:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a2:"\<forall>i j. replaceRel (lv j) rv (r j) ( r2 j) (pref j) " and 
a4:"[ (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) ] : S"
shows "repBwRel (oneParamCons N r)  S (oneParamCons N r2) N "
proof(unfold repBwRel_def,rule allI,rule impI)
  fix r2a
  assume a1:"r2a \<in> oneParamCons N (r2 ) "
  from a1 have b1:"\<exists>i. i\<le>N &r2a=r2  i"
    by auto
  then obtain i where b1:"i\<le>N &r2a=r2 i"
    by blast  
    
  show "(\<exists>lv rv ra pref invL j.
              j \<le> N \<and>
              replaceRel (lv j) rv ra r2a (pref j) \<and>
              ra \<in> oneParamCons N r \<and> invL \<in>   S \<and> (\<lambda>i j. pref j \<longrightarrow>\<^sub>f IVar (lv j) =\<^sub>f IVar rv) \<in> set invL) \<or>
          r2a \<in> oneParamCons N r"
    apply(rule disjI1)  
    apply(
        rule_tac x="lv" in exI,
        rule_tac x="rv" in exI,
        rule_tac x=" r i" in exI,
        rule_tac x="pref" in exI,
        rule_tac x="[ (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) ]" in exI,
        rule_tac x="i" in exI)
    apply(cut_tac a1 b1 a2 a4,auto)
    done
qed

lemma repEqExt1:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a2:"\<forall>i j. replaceRel (lv j) rv (r j) ( r2 j) (pref j) " and 
a4:"[ (\<lambda>i j. (implyForm (pref j) (eqn (IVar (lv j)) (IVar rv)))) ] : S"
shows "repEqRel (oneParamCons N r)  S (oneParamCons N r2) N " 
  using a2 a4 apply(unfold  repEqRel_def) 
  apply(rule conjI,rule repFwExt1,assumption+ )
  by( rule repBwExt1,assumption+ ) 
(*lemma replaceFrmListProt1SimProt3:
  assumes a1: "\<forall>r. r \<in> rs \<longrightarrow>
   ((\<exists>lv rv r2 pref. replaceRel lv rv r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv))) ) \<or> r \<in> rs')"  
  
  shows "\<forall>s. reachableUpTo I rs i s =
             (reachableUpTo I rs' i s )" (is "?P i")
proof (induct_tac i)  
  show "?P 0"
    by (meson  reachableSet0 reachableUpTo0) 
next
  fix n
  assume b0:"?P n"
  show "?P (Suc n)"
  proof((rule allI)+,(rule )+)
    fix s
    assume b1: "reachableUpTo I rs (Suc n) s"  
    have c1:"\<exists>s0 g a. guard g a \<in> rs \<and> reachableUpTo I rs n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by (metis b1 reachableUpToSuc) 
    from c1 obtain s0 g a where c1:
      "guard g a \<in> rs \<and> reachableUpTo I rs n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by blast
    let ?r="guard g a"
    have c2: "(\<exists>lv rv r2 pref. replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))) 
      \<or> ?r \<in> rs'"
      using a1 c1 by blast
    moreover
    {
      assume c2:"\<exists>lv rv r2 pref. replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))"
      from c2 obtain lv rv r2 pref where c2:
        " replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs'  \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))"
        by blast
      have c3:"formEval (pre r2) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRulePre) 
      have c5: "trans1 (act (r2)) s0 = trans1 (act ?r) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRuleEq) 
      have c7: "reachableUpTo I rs' n s0"
        using b0 c1 by blast 
      have "reachableUpTo I rs' (Suc n) (trans1 (act (r2)) s0)"
        by (metis act.simps c2 c3 c7 pre.cases pre.simps reachableSetNext) 
      have "reachableUpTo I rs' (Suc n) s"
        using \<open>reachableUpTo I rs' (Suc n) (trans1 (act r2) s0)\<close> c1 c5 by auto
    }
    moreover
    {
      assume c2: "guard g a \<in> rs'"
      have "reachableUpTo I rs' (Suc n) s"
        using  b0 c1 c2 reachableSetNext by blast 
    }
    ultimately show "reachableUpTo I rs' (Suc n) s "
      using assms by blast 
  next
    fix s
    assume b1:" reachableUpTo I rs' (Suc n) s"
     have c1:"\<exists>s0 g a. guard g a \<in> rs' \<and> reachableUpTo I rs' n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by (metis b1 reachableUpToSuc) 
    from c1 obtain s0 g a where c1:
      "guard g a \<in> rs' \<and> reachableUpTo I rs' n s0 \<and> formEval g s0 \<and> trans1 a s0 = s"
      by blast
    let ?r2="guard g a"
    have c2: "(\<exists>lv rv r pref. replaceRel lv rv r ?r2 pref \<and> ?r2   \<in> rs' \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))) 
      \<or> r \<in> rs'"
      using a1 c1 by blast
    have c2: "(\<exists>lv rv r2 pref. replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))) 
      \<or> ?r \<in> rs'"
      using a1 c1 by blast
    moreover
    {
      assume c2:"\<exists>lv rv r2 pref. replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs' \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))"
      from c2 obtain lv rv r2 pref where c2:
        " replaceRel lv rv ?r r2 pref \<and> r2   \<in> rs'  \<and> isProtInv  rs' I (implyForm pref (eqn (IVar lv) (IVar rv)))"
        by blast
      have c3:"formEval (pre r2) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRulePre) 
      have c5: "trans1 (act (r2)) s0 = trans1 (act ?r) s0"
        by (metis c1 c2 isProtInv_def pre.simps replaceRuleEq) 
      have c7: "reachableUpTo I rs' n s0"
        using b0 c1 by blast 
      have "reachableUpTo I rs' (Suc n) (trans1 (act (r2)) s0)"
        by (metis act.simps c2 c3 c7 pre.cases pre.simps reachableSetNext) 
      have "reachableUpTo I rs' (Suc n) s"
        using \<open>reachableUpTo I rs' (Suc n) (trans1 (act r2) s0)\<close> c1 c5 by auto
    }
    moreover
    {
      assume c2: "guard g a \<in> rs'"
      have "reachableUpTo I rs' (Suc n) s"
        using  b0 c1 c2 reachableSetNext by blast 
    }
    ultimately show "reachableUpTo I rs' (Suc n) s "
      using assms by blast   
  qed
qed 
 *)
(*
lemma DCMP:
  assumes a1: "\<And>r. r \<in> rs2 \<longrightarrow> wellFormedRule env N r"
    and a2: "\<forall>invL f. invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow> symParamForm2 N f"
    and a2D:"\<forall>invL f. invL \<in> S' \<longrightarrow> f \<in> set invL \<longrightarrow> DsymParamForm2 D f"
    and a3: "M\<le>N" 
    and a4: "symPredSet' N Is" 
    and a5:"DsymPredSet' D Is" 
    and a5: "1  \<le> M"
    and a7: "isProtObsInvSet absRules (DabsTransfForm env (absTransfForm (env) M ` Is)) S' M env "
    and a8: "\<forall>pinvL pf i j. pinvL \<in> S' \<longrightarrow> pf \<in> set pinvL \<longrightarrow> i \<le> M \<longrightarrow> j\<le>M \<longrightarrow>
               safeForm  env  M (pf  i j) \<and> deriveForm env (pf  i j)"
    and a8D: "\<forall>pinvL pf i j. pinvL \<in> S' \<longrightarrow> pf \<in> set pinvL \<longrightarrow> i \<le> M \<longrightarrow> j\<le>M \<longrightarrow>
               DsafeForm  env  M (pf  i j) \<and> deriveForm env (pf  i j)"
   
    and a9: "strengthenDIRel rs S rs2 D N"  
    and a10: "symProtRules' N rs2"
     
     
    and a10D: "DsymProtRules' D rs2"
    and a13: "\<And>r. r \<in> rs2 \<longrightarrow> deriveRule env r"
    and a14: "\<And>f. f \<in> Is \<longrightarrow> deriveForm env f"
    and a15: "\<forall>s i. reachableUpTo Is rs2 i s \<longrightarrow> fitEnv s env"
    and a17: "\<forall>invL\<in>S. \<exists>invL'\<in>S'. strengthenVsObsLs invL invL' N"

    and a18:"DabsTransfRule env (absTransfRule (env )  M ` rs2)  \<subseteq>\<^sub>r absRules  " 
  shows "isParamProtInvSet  rs Is S N"
*)

subsection \<open>others \<close>

lemma invIntro1:
    "\<lbrakk>reachableUpTo fs rs k s;
    \<And>s0. (\<forall>f\<in>fs. formEval f s0) \<Longrightarrow> Inv s0;
    \<And>r sk. r \<in> rs \<Longrightarrow> formEval (pre r) sk \<Longrightarrow> Inv sk \<Longrightarrow> Inv (trans1 (act r) sk)\<rbrakk>
   \<Longrightarrow> Inv s"
  using invIntro by blast



definition twoDIParamsCons :: "nat\<Rightarrow>nat \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> rule) \<Rightarrow> rule set" where [simp]:
  "twoDIParamsCons D N pr \<equiv>  {r. \<exists>i j. i \<le> D \<and> j \<le> N \<and> r = pr i j}"



lemma DIsymParaRuleInfSymRuleSet:
  assumes a: "\<forall>d. symParamRule N ( pr d)"  and b:"\<forall>p d i. applySym2Rule p ( pr d i)=\<^sub>rpr d (p i)"
  shows "symProtRules' N (twoDIParamsCons DN N pr)"
proof(unfold symProtRules'_def twoDIParamsCons_def,(rule allI)+)
  fix p r
    show "p permutes {x. x \<le> N} \<and> r \<in> {r. \<exists>i j. i \<le> DN \<and> j \<le> N \<and> r = pr i j} \<longrightarrow>
           (\<exists>r'. r' \<in> {r. \<exists>i j. i \<le> DN \<and> j \<le> N \<and> r = pr i j} \<and> (applySym2Rule p r =\<^sub>r r'))"
    proof(rule impI)
      assume a1:" p permutes {x. x \<le> N} \<and> r \<in> {r. \<exists>i j. i \<le> DN \<and> j \<le> N \<and> r = pr i j}"
      obtain i and j where "i \<le> DN \<and> j \<le> N \<and> r = pr i j"
        using a1 by auto
      have a2:" equivRule (applySym2Rule p (pr  i j)) ( (pr i (p j)))"
        using a b  apply(unfold  symParamRule_def, auto) done

      show " (\<exists>r'. r' \<in> {r. \<exists>i j. i \<le> DN \<and> j \<le> N \<and> r = pr i j} \<and> (applySym2Rule p r =\<^sub>r r'))"
        using \<open>i \<le> DN \<and> j \<le> N \<and> r = pr i j\<close> a1 a2 permutes_in_image by fastforce
    qed
  qed


lemma DIsymParaRuleInfSymRuleSetD:
  assumes b:"\<forall>p d i. applyDSym2Rule p ( pr d i)=\<^sub>rpr (p d) ( i)"
  shows "DsymProtRules' DN (twoDIParamsCons DN N pr)"
proof(unfold DsymProtRules'_def twoDIParamsCons_def,(rule allI)+)
  fix p r
  show "p permutes {x. x \<le> DN} \<and> r \<in> {r. \<exists>i j. i \<le> DN \<and> j \<le> N \<and> r = pr i j} \<longrightarrow>
           (\<exists>r'. r' \<in> {r. \<exists>i j. i \<le> DN \<and> j \<le> N \<and> r = pr i j} \<and> (applyDSym2Rule p r =\<^sub>r r'))"
  proof(rule impI)
      assume a1:" p permutes {x. x \<le> DN} \<and> r \<in> {r. \<exists>i j. i \<le> DN \<and> j \<le> N \<and> r = pr i j}"
      obtain i and j where "i \<le> DN \<and> j \<le> N \<and> r = pr i j"
        using a1 by auto
      (*have a2:" equivRule (applyDSym2Rule p (pr  i j)) ( (pr (p i) ( j)))"
        using a b by(unfold  DsymParamRule_def, auto)*)

      show " (\<exists>r'. r' \<in> {r. \<exists>i j. i \<le> DN \<and> j \<le> N \<and> r = pr i j} \<and> (applyDSym2Rule p r =\<^sub>r r'))"
        using a1 b permutes_in_image by fastforce 
    qed
  qed

(*
definition strengthenDIFwRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>nat\<Rightarrow>bool" where
"strengthenDIFwRel rs S rs2 D N\<equiv>
\<forall>r'. r' \<in> rs2 \<longrightarrow> ((\<exists>r invL d i j. d \<le>D \<and> i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and> r \<in> rs \<and>
                r' = strengthenRuleByFrmL2 (map2' invL  j i) r) \<or> r' \<in> rs)"

definition strengthenDIBwRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>nat\<Rightarrow>bool" where
"strengthenDIBwRel rs S rs2 D N\<equiv>
\<forall>r. r \<in> rs \<longrightarrow> ((\<exists>invL d i j. d \<le> D\<and> i \<le> N \<and> j \<le> N \<and> invL \<in> S \<and>
                strengthenRuleByFrmL2 (map2' invL  j i) r \<in> rs2) \<or> r \<in> rs2)"

definition strengthenDIRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>nat\<Rightarrow>bool" where
"strengthenDIRel rs S rs2 D N\<equiv>
  strengthenDIFwRel rs S rs2 D N \<and> strengthenDIBwRel rs S rs2 D N"

definition strengthenRel::"rule set \<Rightarrow> (nat \<Rightarrow> nat \<Rightarrow> formula) list set \<Rightarrow> rule set\<Rightarrow> nat \<Rightarrow>bool" where
"strengthenRel rs S rs2 N\<equiv>
  strengthenFwRel rs S rs2 N \<and> strengthenBwRel rs S rs2 N"


*)

lemma strengthenFwExt3:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>i j d. strengthenRuleByFrmL2 (map2' (lemmasFor_r N)  j i) (r d i) = r_ref N d i" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenDIFwRel (twoDIParamsCons D N r)  (set (InvS N)) (twoDIParamsCons D N (r_ref N)) D N "
proof(unfold strengthenDIFwRel_def,rule allI,rule impI)
  fix r'
  assume a1:"r' \<in> twoDIParamsCons D N (r_ref N) "
  from a1 have b1:"\<exists>d i. d\<le>D & i\<le>N &r'=r_ref N d i"
    by auto
  then obtain d and i where b1:"d\<le>D & i\<le>N & r'=r_ref N d i"
    by blast  
    
  show " (\<exists>ra invL d i j.
              d \<le> D \<and>
              i \<le> N \<and> j \<le> N \<and>
              invL \<in> set (InvS N) \<and>
              ra \<in> twoDIParamsCons D N r \<and>
              r' = strengthenRuleByFrmL2 (map2' invL j i) ra) \<or>
          r' \<in> twoDIParamsCons D N r"
    
    apply(rule disjI1,rule exI[where x="r d i"])  
    apply(
        rule exI[where x="lemmasFor_r N"],
        rule exI[where x=0],
        rule exI[where x=i])
    apply(cut_tac a1 b1 a3 a4,auto)
    done 
qed

lemma strengthenBwExt3:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>i j d. strengthenRuleByFrmL2 (map2' (lemmasFor_r N)   j i) (r  d i) = r_ref N d i" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenDIBwRel (twoDIParamsCons D N r)  (set (InvS N)) (twoDIParamsCons D N (r_ref N)) D N "
proof(unfold strengthenDIBwRel_def,rule allI,rule impI)
  fix ra
  assume a1:"ra \<in> twoDIParamsCons D N (r ) "
  from a1 have b1:"\<exists>d i. d\<le>D & i\<le>N &ra=r d  i"
    by auto
  then obtain d and i where b1:"d\<le>D &i\<le>N &ra=r d i"
    by blast  
  
  (*fix ra
  assume a1:"ra \<in> twoDIParamsCons D N (r ) "
  from a1 have b1:"\<exists>d i. d\<le>D &i\<le>N &ra=r   d i"
    by auto
  then obtain d and i where b1:"d\<le>D &i\<le>N &ra=r d i"
    by blast *) 
    
  show "(\<exists>invL d i j.
              d \<le> D \<and>
              i \<le> N \<and> j \<le> N \<and>
              invL \<in> set (InvS N) \<and>
              strengthenRuleByFrmL2 (map2' invL  j i) ra
              \<in> twoDIParamsCons D N (r_ref N)) \<or>
          ra \<in> twoDIParamsCons D N (r_ref N) "
    apply(rule disjI1)  
    apply(
        rule exI[where x="lemmasFor_r N"],
        rule exI[where x=d],
        rule exI[where x=i],
        rule exI[where x=0])
    apply(cut_tac a1 b1 a3 a4,auto)
    done
     
qed


lemma strengthenExt3:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>i j d. strengthenRuleByFrmL2 (map2' (lemmasFor_r N) j i) (r d i) = r_ref N d i" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenDIRel (twoDIParamsCons D  N r)  (set (InvS N)) (twoDIParamsCons D N (r_ref N)) D N "
proof(unfold strengthenDIRel_def,rule conjI)
  show "strengthenDIFwRel (twoDIParamsCons D N r) (set (InvS N)) (twoDIParamsCons D N (r_ref N)) D N"
    apply(rule strengthenFwExt3)
    using a3 apply force
    using a4 apply force
    done
next
  show "strengthenDIBwRel (twoDIParamsCons D N r) (set (InvS N)) (twoDIParamsCons D N (r_ref N)) D N"
   using a3 a4 strengthenBwExt3 strengthenFwExt3 strengthenDIRel_def by presburger

qed




lemma strengthenDFwExt1:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>d i j. strengthenRuleByFrmL2 (map2' (lemmasFor_r N) j i) (r d i) = r_ref d  i" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenFwRel (twoDIParamsCons D N  r)  (set (InvS N)) (twoDIParamsCons D N  (r_ref )) N "
proof(unfold strengthenFwRel_def,rule allI,rule impI)
  fix r'
  assume a1:"r' \<in> twoDIParamsCons D N r_ref "
  from a1 have b1:"\<exists>d i. d \<le>D \<and> i\<le>N &r'=r_ref d i"
    by auto
  then obtain d and i where b1:"d\<le>D \<and> i\<le>N &r'=r_ref d i"
    by blast  
    
  show " (\<exists>ra invL i j.
              i \<le> N \<and>
              j \<le> N \<and>
              invL \<in> set (InvS N) \<and>
              ra \<in> twoDIParamsCons D N r  \<and>
              r' = strengthenRuleByFrmL2 (map2' invL i j) ra) \<or>
          r' \<in> twoDIParamsCons D N  r"
    apply(rule disjI1,rule exI[where x="r d i"])  
    apply(
        rule exI[where x="lemmasFor_r N"],
        rule exI[where x=0],
        rule exI[where x=i])
    apply(cut_tac a1 b1 a3 a4,auto)
    done
qed


lemma strengthenDBwExt1:
  assumes 
(*a1:"r_refs N = oneParamCons N (r_ref N)" and
a2:"rs N =  oneParamCons N (r N)" and*)
a3:"\<forall>d i j. strengthenRuleByFrmL2 (map2' (lemmasFor_r N) j i) (r d i) = r_ref d i" and
a4:"(lemmasFor_r N) : set(InvS N)"
shows "strengthenBwRel (twoDIParamsCons D N r)  (set (InvS N)) (twoDIParamsCons D N (r_ref )) N "
proof(unfold strengthenBwRel_def,rule allI,rule impI)
  fix ra
  assume a1:"ra \<in>twoDIParamsCons D N (r ) "
  from a1 have b1:"\<exists>d i. d \<le>D \<and> i\<le>N &ra=r d i"
    by auto
  then obtain d and i where b1:"d \<le>D \<and> i\<le>N &ra=r d i"
    by blast  
    
  show "(\<exists>invL i j.
              i \<le> N \<and>
              j \<le> N \<and>
              invL \<in> set (InvS N) \<and>
              strengthenRuleByFrmL2 (map2' invL i j) ra \<in>twoDIParamsCons D N (r_ref )) \<or>
          ra \<in> twoDIParamsCons D N (r_ref ) "
    apply(rule disjI1)  
    apply(
        rule exI[where x="lemmasFor_r N"],
        rule exI[where x=0],
        rule exI[where x=i])
    apply(cut_tac a1 b1 a3 a4,auto)
    done
qed

lemma strengthenDExt1:
  assumes "\<forall>d i j. strengthenRuleByFrmL2 (map2' (lemmasFor_r N) j i) (r d i) = r_ref  d i " and 
"lemmasFor_r N \<in> set (InvS N) "
shows " strengthenRel (twoDIParamsCons D N r) (set (InvS N)) (twoDIParamsCons D N (r_ref )) N"
  using assms(1) assms(2) strengthenDBwExt1 strengthenDFwExt1 strengthenRel_def by blast


lemma absGenD:
  assumes "\<And>d i. absTransfRule env M (f d i) = (if i \<le> M then (g d i) else h)"
    and "M < N"
  shows "absTransfRule env M ` (twoDIParamsCons D N f) = (twoDIParamsCons D M g) \<union> {h}"
  apply (auto simp add: assms image_def)
  apply blast
  apply (metis assms(1) assms(2) leD order_refl)
  by (metis assms(1) assms(2) dual_order.strict_implies_order le_trans)  


lemma absGenDd:
  assumes "\<And>d i. absTransfRule env M0 (f d i) = (if i \<le> M0 then (g d i) else h d)"
    and "M0 < N"
  shows "absTransfRule env M0 ` (twoDIParamsCons D N f) = 
  (twoDIParamsCons D M0 g) \<union> {r. \<exists>d. d \<le>D \<and> r=h d}"
  apply (auto simp add: assms image_def)
  apply blast
  apply (metis assms(1) assms(2) leD order_refl)
  apply (metis assms(1) assms(2) dual_order.strict_implies_order le_trans)
  by (metis assms(1) assms(2) less_le_not_le order_refl)  
  

lemma DabsGenDd:
  assumes "\<And>d i. d \<le>D \<and> i\<le>N \<Longrightarrow>DabsTransfRule env   (f d i) = (if d = 0 then (f d i) else f 1 i)"
    and "0 < D"
  shows "DabsTransfRule env   ` (twoDIParamsCons D N f) = 
  (twoDIParamsCons 1 N f) "
  apply (auto simp add: assms image_def)
  apply blast 
  apply (metis assms(1) assms(2) leD order_refl)
  by (metis One_nat_def assms(1) assms(2) dual_order.refl less_one order_less_le)  

lemma equivFormForall:
  assumes "symParamForm  N pf" "p permutes {x. x \<le> N}" 
  shows " equivForm (forallForm (\<lambda>i. pf (p i)) N) (forallForm pf N)"
proof -
  (*fix p
  assume "p permutes {x. x \<le> N}"*)
  have "symPredSet' N {(\<forall>\<^sub>fi. pf i) N}"
    using assms symPredSetForall by presburger

  then show " equivForm (forallForm (\<lambda>i. pf (p i)) N) (forallForm pf N)"
    unfolding symPredSet'_def
    apply auto
    using \<open>p permutes {x. x \<le> N}\<close> assms equivForm_def symParamForm_def by force
qed

lemma existDformSym:
  assumes "\<forall>p d.  p permutes {x. x \<le> N} \<longrightarrow>equivForm (applySym2Form p (f d) ) (f d) "   
  shows "\<forall>p .  p permutes {x. x \<le> N} \<longrightarrow>equivForm ((existForm (\<lambda>k. applySym2Form p (f k)) D)) (existForm (\<lambda>k. f k) D)"
  apply(unfold equivForm_def,auto)
  using assms equivForm_def apply blast
  using assms equivForm_def by blast

lemma symPredSetExistD:
  assumes   "\<forall>p d.  p permutes {x. x \<le> N} \<longrightarrow> equivForm (applySym2Form p (f d) ) (f d) "
  shows "symPredSet' N {(\<exists>\<^sub>fd. f d) D}"
proof(unfold symPredSet'_def,(rule allI)+,(rule impI)+,simp)
  fix p
  assume b1:"p permutes {x. x \<le> N}"
   
 

  show "equivForm ((\<exists>\<^sub>fi. applySym2Form p (f i)) D) (existForm f D) "
    using b1 assms(1) existDformSym by blast  
qed

lemma DsymapplyFormNone:
  assumes "\<forall>r p. r \<in> R \<longrightarrow> equivForm ( applyDSym2Form p r) r"
  shows "DsymPredSet' DN R"
  using DsymPredSet'_def assms by blast 
    

lemma DsymapplyRuleNone:
  assumes "\<forall>r p. r \<in> R \<longrightarrow> equivRule ( applyDSym2Rule p r) r"
  shows "DsymProtRules'  DN R"
  using DsymProtRules'_def assms by blast 

 lemma StrengthRelRules2Rule_strMono : 
  "\<lbrakk>strengthenRel rs invs rs' N; invs \<subseteq> invs'\<rbrakk> \<Longrightarrow> strengthenRel rs invs' rs' N"
   apply(unfold    strengthenRel_def)
   apply(rule conjI)
   apply(unfold  strengthenFwRel_def)
   apply blast
   apply(unfold  strengthenBwRel_def)
   by (meson subsetD)

lemma isParamProtInvsetUn:
  "isParamProtInvSet rs Is (A \<union> B) N =( (isParamProtInvSet rs Is A N) \<and> (isParamProtInvSet rs Is B N))"
  by(unfold isParamProtInvSet_def,auto)
end


