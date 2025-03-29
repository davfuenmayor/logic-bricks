section \<open>Relations\<close>
text \<open>A theory of (heterogeneous) relations as set-valued functions. Relations inherit the structures
 of both sets and functions and enrich them in manifold ways.\<close>

theory relations (* A basic theory of relations (qua set-valued functions) *)
imports func_sets
begin

named_theorems rel_defs and rel_simps

subsection \<open>Constructing Relations\<close>

subsubsection \<open>Product and Sum\<close>
text \<open>Relations can also be constructed out of pairs of sets, via (cartesian) product and (disjoint) sum.\<close>

definition product::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<times>" 90)
  where "(\<times>) \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<and>)"
definition sum::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<uplus>" 90)
  where "(\<uplus>) \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<or>)"

declare product_def[rel_defs] sum_def[rel_defs]

lemma "A \<times> B = (\<lambda>x y. A x \<and> B y)" unfolding rel_defs comb_defs ..
lemma "A \<uplus> B = (\<lambda>x y. A x \<or> B y)" unfolding rel_defs comb_defs ..


subsubsection \<open>Pairs and Copairs\<close>
text \<open>A (co)atomic-like relation can be constructed out of two elements.\<close>

definition pair::"'a \<Rightarrow> 'b \<Rightarrow> Rel('a,'b)" ("\<langle>_,_\<rangle>")
  where \<open>pair \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<and>) \<Q> \<Q>\<close> \<comment> \<open>relational counterpart of 'singleton'\<close>
definition copair::"'a \<Rightarrow> 'b \<Rightarrow> Rel('a,'b)" ("\<lblot>_,_\<rblot>")
  where \<open>copair \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<or>) \<D> \<D>\<close> \<comment> \<open>relational counterpart of 'cosingleton'\<close>

declare pair_def[rel_defs] copair_def[rel_defs]

lemma "\<langle>a,b\<rangle> = (\<lambda>x y. a = x \<and> b = y)" unfolding rel_defs comb_defs ..
lemma "\<lblot>a,b\<rblot> = (\<lambda>x y. a \<noteq> x \<or> b \<noteq> y)" unfolding rel_defs comb_defs ..

text\<open>Recalling that\<close>
lemma "\<^bold>B\<^sub>2\<^sub>2 = \<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>1" unfolding comb_defs ..

text \<open>We have that pair and copair can be defined in terms of \<open>(\<times>)\<close> and \<open>(\<uplus>)\<close> directly.\<close>
lemma "pair   = \<^bold>B\<^sub>1\<^sub>1 (\<times>) \<Q> \<Q>" unfolding rel_defs comb_defs ..
lemma "copair = \<^bold>B\<^sub>1\<^sub>1 (\<uplus>) \<D> \<D>" unfolding rel_defs comb_defs ..
lemma "\<langle>a,b\<rangle> = {a} \<times> {b}" unfolding rel_defs comb_defs ..
lemma "\<lblot>a,b\<rblot> = \<lbrace>a\<rbrace> \<uplus> \<lbrace>b\<rbrace>" unfolding rel_defs comb_defs ..


text \<open>We conveniently extrapolate the definitions of unique/singleton from sets to relations.\<close>
definition uniqueR::"Set(Rel('a,'b))" ("unique\<^sup>2") \<comment> \<open>R holds of at most one pair of elements (R may hold of none)\<close>
  where \<open>unique\<^sup>2 R \<equiv> \<forall>a b x y. (R a b \<and> R x y) \<rightarrow> (a = x \<and> b = y)\<close>
definition singletonR::"Set(Rel('a,'b))" ("\<exists>!\<^sup>2") \<comment> \<open>R holds of exactly one pair of elements, i.e. R is a 'singleton relation'\<close>
  where \<open>\<exists>!\<^sup>2 R \<equiv> \<exists>x y. R x y \<and> (\<forall>a b. R a b \<rightarrow> (a = x \<and> b = y))\<close>

declare uniqueR_def[rel_defs] singletonR_def[rel_defs]

lemma uniqueR_def2: "unique\<^sup>2 = \<nexists>\<^sup>2 \<union> \<exists>!\<^sup>2" unfolding rel_defs func_defs comb_defs by blast
lemma singletonR_def2: "\<exists>!\<^sup>2 = \<exists>\<^sup>2 \<inter> unique\<^sup>2" unfolding rel_defs func_defs comb_defs apply (rule ext) by blast

(*Clearly, pairs correspond one-to-one to "singleton relations" *)
lemma pair_singletonR: "\<exists>!\<^sup>2 \<langle>a,b\<rangle>" unfolding rel_defs comb_defs by simp
lemma singletonR_def3: "\<exists>!\<^sup>2 R = (\<exists>a b. R = \<langle>a,b\<rangle>)" unfolding rel_defs comb_defs by metis


subsection \<open>Boolean Algebraic Structure\<close>

subsubsection \<open>Boolean Operations\<close>
text \<open>As we have seen, relations correspond to indexed (families of) sets. Hence it is not surprising
 that they inherit their boolean algebraic structure. Moreover, we saw previously how boolean set 
 operations arise via "indexation" of HOL's boolean connectives (via \<open>\<^bold>\<Phi>\<^sub>m\<^sub>1\<close> combinators). The relational
 boolean operations arise analogously by "double-indexation" of HOL's counterparts (via \<open>\<^bold>\<Phi>\<^sub>m\<^sub>2\<close> combinators),
 or, equivalently, by "indexation" of the corresponding set counterparts, as shown below.\<close>
definition univR::"Rel('a,'b)" ("\<UU>\<^sup>r")
  where "\<UU>\<^sup>r \<equiv> \<^bold>\<Phi>\<^sub>0\<^sub>1 \<UU>" \<comment> \<open>the universal relation\<close>
definition emptyR::"Rel('a,'b)" ("\<emptyset>\<^sup>r")
  where "\<emptyset>\<^sup>r \<equiv> \<^bold>\<Phi>\<^sub>0\<^sub>1 \<emptyset>"  \<comment> \<open>the empty relation\<close>
definition complR::"EOp(Rel('a,'b))" ("\<midarrow>\<^sup>r") 
  where \<open>\<midarrow>\<^sup>r \<equiv> \<^bold>\<Phi>\<^sub>1\<^sub>1 \<midarrow>\<close>  \<comment> \<open>relation complement\<close>
definition interR::"EOp\<^sub>2(Rel('a,'b))" (infixl "\<inter>\<^sup>r" 54) 
  where "(\<inter>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<inter>)" \<comment> \<open>relation intersection\<close>
definition unionR::"EOp\<^sub>2(Rel('a,'b))" (infixl "\<union>\<^sup>r" 53) 
  where "(\<union>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<union>)" \<comment> \<open>relation union\<close>
definition diffR:: "EOp\<^sub>2(Rel('a,'b))" (infixl "\<setminus>\<^sup>r" 51) 
  where "(\<setminus>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<setminus>)" \<comment> \<open>relation difference\<close>
definition implR::"EOp\<^sub>2(Rel('a,'b))" (infixr "\<Rightarrow>\<^sup>r" 51) 
  where "(\<Rightarrow>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<Rightarrow>)"  \<comment> \<open>relation implication\<close>
definition dimplR::"EOp\<^sub>2(Rel('a,'b))" (infix "\<Leftrightarrow>\<^sup>r" 51) 
  where "(\<Leftrightarrow>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<Leftrightarrow>)" \<comment> \<open>relation double-implication\<close>
definition sdiffR::"EOp\<^sub>2(Rel('a,'b))" (infix "\<triangle>\<^sup>r" 51) 
  where "(\<triangle>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<triangle>)" \<comment> \<open>relation symmetric difference (aka. xor)\<close>

text \<open>Convenient notation for reversed implication.\<close>
abbreviation(input) lpmiR::"EOp\<^sub>2(Rel('a,'b))" (infixl "\<Leftarrow>\<^sup>r" 51)
  where "A \<Leftarrow>\<^sup>r B \<equiv> B \<Rightarrow>\<^sup>r A"

declare univR_def[rel_defs] emptyR_def[rel_defs]
        complR_def[rel_defs] interR_def[rel_defs] unionR_def[rel_defs]
        implR_def[rel_defs] dimplR_def[rel_defs] diffR_def[rel_defs] sdiffR_def[rel_defs]

text \<open>We add a convenient superscript notation, as commonly found in the literature.\<close>
notation (input) complR ("(_)\<^sup>\<midarrow>") notation(output) complR ("'(_')\<^sup>\<midarrow>")

text \<open>Point-based definitions\<close>
lemma "\<UU>\<^sup>r = \<^bold>\<Phi>\<^sub>0\<^sub>2 \<T>" unfolding comb_defs unfolding rel_defs func_defs comb_defs ..
lemma "\<UU>\<^sup>r = (\<lambda>x y. \<T>)" unfolding rel_defs func_defs comb_defs ..
lemma "\<emptyset>\<^sup>r = \<^bold>\<Phi>\<^sub>0\<^sub>2 \<F>" unfolding rel_defs func_defs comb_defs ..
lemma "\<emptyset>\<^sup>r = (\<lambda>x y. \<F>)" unfolding rel_defs func_defs comb_defs ..
lemma "\<midarrow>\<^sup>r = \<^bold>\<Phi>\<^sub>1\<^sub>2(\<not>)" unfolding rel_defs func_defs comb_defs ..
lemma "\<midarrow>\<^sup>rR = (\<lambda>x y. \<not>R x y)" unfolding rel_defs func_defs comb_defs ..
lemma "(\<inter>\<^sup>r) = \<^bold>\<Phi>\<^sub>2\<^sub>2(\<and>)" unfolding rel_defs func_defs comb_defs ..
lemma "R \<inter>\<^sup>r T = (\<lambda>x y. R x y \<and> T x y)" unfolding rel_defs func_defs comb_defs ..
lemma "(\<union>\<^sup>r) = \<^bold>\<Phi>\<^sub>2\<^sub>2(\<or>)" unfolding rel_defs func_defs comb_defs ..
lemma "R \<union>\<^sup>r T = (\<lambda>x y. R x y \<or> T x y)" unfolding rel_defs func_defs comb_defs ..
\<comment> \<open>... and so on\<close>

text \<open>Product and sum satisfy the corresponding DeMorgan dualities.\<close>
lemma prodSum_simp1: "\<midarrow>\<^sup>r(A \<times> B) = \<midarrow>A \<uplus> \<midarrow>B" 
  unfolding rel_defs func_defs comb_defs by simp
lemma prodSum_simp2: "\<midarrow>\<^sup>r(A \<uplus> B) = \<midarrow>A \<times> \<midarrow>B" 
  unfolding rel_defs func_defs comb_defs by simp
lemma prodSum_simp1': "\<midarrow>\<^sup>r((\<midarrow>A) \<times> (\<midarrow>B)) = A \<uplus> B" 
  unfolding rel_defs func_defs comb_defs by simp
lemma prodSum_simp2': "\<midarrow>\<^sup>r((\<midarrow>A) \<uplus> (\<midarrow>B)) = A \<times> B" 
  unfolding rel_defs func_defs comb_defs by simp

text \<open>Pairs and copairs are related via relation-complement as expected.\<close>
lemma copair_simp: "\<midarrow>\<^sup>r\<lblot>a,b\<rblot> = \<langle>a,b\<rangle>" 
  unfolding rel_defs func_defs comb_defs by simp

declare prodSum_simp1 [rel_simps] prodSum_simp2 [rel_simps] 
        prodSum_simp1' [rel_simps] prodSum_simp2' [rel_simps]


subsubsection \<open>Ordering Structure\<close>
text \<open>Similarly, relations also inherit the ordering structure of sets.\<close>

text \<open>Analogously to the notion of "equalizer" of two functions, we have the "orderer" or two relations:\<close>
definition orderer::"Rel('a,'b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('a)" (infixr "\<sqsubseteq>" 51) 
  where "(\<sqsubseteq>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>)"

declare orderer_def[rel_defs]

lemma "R \<sqsubseteq> T = (\<lambda>x. R x \<subseteq> T x)" unfolding rel_defs comb_defs ..

text \<open>We encode the notion of sub-/super-relation building upon the set counterparts.\<close>
definition subrel::"ERel(Rel('a,'b))" (infixr "\<subseteq>\<^sup>r" 51) 
  where "(\<subseteq>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>\<forall> (\<subseteq>)"

declare subrel_def[rel_defs]

lemma subrel_setdef:   "R \<subseteq>\<^sup>r T = (\<forall>x. R x \<subseteq> T x)" unfolding rel_defs func_defs comb_defs ..
lemma "R \<subseteq>\<^sup>r T = (\<forall>x y. R x y \<rightarrow> T x y)" unfolding rel_defs func_defs comb_defs ..
lemma "R \<subseteq>\<^sup>r T = \<forall>\<^sup>2(R \<Rightarrow>\<^sup>r T)" unfolding rel_defs func_defs comb_defs ..
lemma subrel_def2: "(\<subseteq>\<^sup>r) = \<forall> \<circ>\<^sub>2 (\<sqsubseteq>)" unfolding rel_defs func_defs comb_defs ..
lemma subrel_reldef:   "(\<subseteq>\<^sup>r) = \<forall>\<^sup>2 \<circ>\<^sub>2 (\<Rightarrow>\<^sup>r)" unfolding rel_defs func_defs comb_defs ..

abbreviation(input) superrel::"ERel(Rel('a,'b))" (infixr "\<supseteq>\<^sup>r" 51) 
   where "B \<supseteq>\<^sup>r A \<equiv> A \<subseteq>\<^sup>r B"

text \<open>The "power-relation" operation corresponds to the (partial) application of superrel.\<close>
abbreviation(input) powerrel::"Rel('a,'b) \<Rightarrow> Set(Rel('a,'b))" ("\<wp>\<^sup>r")
  where "\<wp>\<^sup>r \<equiv> (\<supseteq>\<^sup>r)"

lemma "\<wp>\<^sup>rA = (\<lambda>B. B \<subseteq>\<^sup>r A)" unfolding rel_defs func_defs comb_defs by auto

text \<open>Alternative characterizations of the sub/super-rel orderings in terms of fixed-points.\<close>
lemma subrel_defFP:   "(\<subseteq>\<^sup>r) = FP \<circ> (\<union>\<^sup>r)" unfolding rel_defs func_defs comb_defs by metis
lemma superrel_defFP: "(\<supseteq>\<^sup>r) = FP \<circ> (\<inter>\<^sup>r)" unfolding rel_defs func_defs comb_defs by metis
lemma "(R \<subseteq>\<^sup>r T) = (T = R \<union>\<^sup>r T)" unfolding rel_defs func_defs comb_defs by metis
lemma "(T \<supseteq>\<^sup>r R) = (R = T \<inter>\<^sup>r R)" unfolding rel_defs func_defs comb_defs by metis

text \<open>Sub-relation is antisymmetric\<close>
lemma subrel_antisym: "R \<subseteq>\<^sup>r T \<Longrightarrow> R \<supseteq>\<^sup>r T \<Longrightarrow> R = T" unfolding rel_defs func_defs comb_defs by blast

text \<open>Two relations are said to "overlap" (or "intersect") if their intersection is non-empty\<close>
definition overlapR::"ERel(Rel('a,'b))" (infix "\<sqinter>\<^sup>r" 52)
  where "(\<sqinter>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>\<exists> (\<sqinter>)"
text \<open>Dually, two relations form a "cover" if every pair belongs to one or the other.\<close>
definition coverR::"ERel(Rel('a,'b))" (infix "\<squnion>\<^sup>r" 53)
  where "(\<squnion>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>\<forall> (\<squnion>)"

declare overlapR_def[rel_defs] coverR_def[rel_defs]

text \<open>Convenient notation: Two relations can also be said to be "incompatible" analogously to sets.\<close>
abbreviation(input) incompatR::"ERel(Rel('a,'b))" (infix "\<bottom>\<^sup>r" 52)
  where "(\<bottom>\<^sup>r) \<equiv> \<nexists>\<^sup>2 \<circ>\<^sub>2 (\<inter>\<^sup>r)"

lemma coverR_reldef:  "(\<squnion>\<^sup>r) = \<forall>\<^sup>2 \<circ>\<^sub>2 (\<union>\<^sup>r)" unfolding rel_defs func_defs comb_defs ..
lemma overlapR_reldef:  "(\<sqinter>\<^sup>r) = \<exists>\<^sup>2 \<circ>\<^sub>2 (\<inter>\<^sup>r)"  unfolding rel_defs func_defs comb_defs ..
lemma "A \<squnion>\<^sup>r B = \<forall>\<^sup>2(A \<union>\<^sup>r B)" unfolding rel_defs func_defs comb_defs ..
lemma "A \<sqinter>\<^sup>r B = \<exists>\<^sup>2(A \<inter>\<^sup>r B)" unfolding rel_defs func_defs comb_defs ..
lemma "A \<bottom>\<^sup>r B = \<nexists>\<^sup>2(A \<inter>\<^sup>r B)" unfolding rel_defs comb_defs ..


subsubsection \<open>Infinitary Operations\<close>

text \<open>We can also generalize union and intersection to the infinitary case.\<close>
definition biginterR::"EOp\<^sub>G(Rel('a,'b))" ("\<Inter>\<^sup>r") 
  where "\<Inter>\<^sup>r \<equiv> \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>0 image \<^bold>T)"
definition bigunionR::"EOp\<^sub>G(Rel('a,'b))" ("\<Union>\<^sup>r")
  where "\<Union>\<^sup>r \<equiv> \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>0 image \<^bold>T)"

declare biginterR_def[rel_defs] bigunionR_def[rel_defs]

lemma "\<Inter>\<^sup>rS a = \<Inter>\<lparr>(\<lambda>R. R a) S\<rparr>" unfolding rel_defs func_defs comb_defs ..
lemma "\<Union>\<^sup>rS a = \<Union>\<lparr>(\<lambda>R. R a) S\<rparr>" unfolding rel_defs func_defs comb_defs ..

text \<open>Alternative definitions in terms of quantifiers directly.\<close>
lemma biginterR_def2: "\<Inter>\<^sup>rS = (\<lambda>a b. \<forall>R. S R \<rightarrow> R a b)" 
  unfolding rel_defs func_defs comb_defs by metis
lemma bigunionR_def2: "\<Union>\<^sup>rS = (\<lambda>a b. \<exists>R. S R \<and> R a b)" 
  unfolding rel_defs func_defs comb_defs by metis


text \<open>We say of a set of relations that it "overlaps" (or "intersects") if there exists a shared pair.\<close>
abbreviation(input) bigoverlapR::"Set(Set(Rel('a,'b)))" ("\<Sqinter>\<^sup>r")
  where "\<Sqinter>\<^sup>r \<equiv> \<exists>\<^sup>2 \<circ> \<Inter>\<^sup>r"
text \<open>Dually, a set of relations forms a "cover" if every pair is contained in at least one of the relations.\<close>
abbreviation(input) bigcoverR::"Set(Set(Rel('a,'b)))" ("\<Squnion>\<^sup>r")
  where "\<Squnion>\<^sup>r \<equiv> \<forall>\<^sup>2 \<circ> \<Union>\<^sup>r"

lemma "\<Sqinter>\<^sup>rS = \<exists>\<^sup>2(\<Inter>\<^sup>rS)" unfolding comb_defs ..
lemma "\<Squnion>\<^sup>rS = \<forall>\<^sup>2(\<Union>\<^sup>rS)" unfolding comb_defs ..


subsection \<open>Function-like Structure I\<close>

text \<open>We have seen the shared (boolean) algebraic structure between sets and relations. 
 We now explore their shared structure with functions.\<close>

text \<open>We start by noting that, given a relation \<open>R\<close> of type \<open>Rel('a,'b)\<close>, we refer to the semantic domain of 
 type \<open>'a\<close> as R's "source" domain, which is identical to R's domain when seen as a (set-valued) function. 
 Analogously, we refer to the semantic domain for type \<open>'b\<close> as R's "target" domain, which is in fact
 different from its codomain when seen as a (set-valued) function (corresponding to the type \<open>'b \<Rightarrow> o\<close>).\<close>


subsubsection \<open>Range and Cylindrification\<close>
text \<open>We define the left- (right-) range of a relation as the set of those objects in the source (target)
 domain that reach to (are reached by) some element in the target (source) domain.\<close>

definition leftRange::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "leftRange \<equiv> \<exists> \<circ>\<^sub>2 \<^bold>A"
definition rightRange::"Rel('a,'b) \<Rightarrow> Set('b)"
  where "rightRange \<equiv> \<exists> \<circ>\<^sub>2 \<^bold>C"

lemma "leftRange R a = (\<exists>x. R a x)" unfolding leftRange_def comb_defs ..
lemma "rightRange R b = (\<exists>x. R x b)" unfolding rightRange_def comb_defs ..


text \<open>Dually, the left- (right-) dual-range of a relation is the set of those objects in the source (target)
 domain that reach to (are reached by) all elements in the target (source) domain.\<close>
definition leftDualRange::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "leftDualRange \<equiv> \<forall> \<circ>\<^sub>2 \<^bold>A"
definition rightDualRange::"Rel('a,'b) \<Rightarrow> Set('b)"
  where "rightDualRange \<equiv> \<forall> \<circ>\<^sub>2 \<^bold>C"

lemma "leftDualRange R a = (\<forall>x. R a x)" unfolding leftDualRange_def comb_defs ..
lemma "rightDualRange R b = (\<forall>x. R x b)" unfolding rightDualRange_def comb_defs ..

declare leftRange_def[rel_defs] rightRange_def[rel_defs]
        leftDualRange_def[rel_defs] rightDualRange_def[rel_defs]

text \<open>Both pairs of definitions are "dual" wrt. complement.\<close>
lemma "rightDualRange R = \<midarrow>(rightRange R\<^sup>\<midarrow>)" unfolding rel_defs func_defs comb_defs by simp
lemma "leftDualRange R = \<midarrow>(leftRange R\<^sup>\<midarrow>)" unfolding rel_defs func_defs comb_defs by simp

text \<open>For the left we have in fact that ranges are obtained directly by composition with \<open>\<exists>\<close> and \<open>\<forall>\<close>.\<close>
lemma leftRange_def2: "leftRange = \<^bold>B \<exists>" unfolding rel_defs comb_defs ..
lemma leftDualRange_def2: "leftDualRange = \<^bold>B \<forall>" unfolding rel_defs comb_defs ..

text \<open>The operations below perform what is known as "cylindrification" in the literature on relation algebra.\<close>
definition leftCylinder::"Set('b) \<Rightarrow> Rel('a,'b)"
  where "leftCylinder \<equiv> \<^bold>K"
definition rightCylinder::"Set('a) \<Rightarrow> Rel('a,'b)"
  where "rightCylinder \<equiv> \<^bold>B \<^bold>K"

declare leftCylinder_def[rel_defs] rightCylinder_def[rel_defs]

lemma "leftCylinder  S = (\<lambda>a b. S b)" unfolding rel_defs comb_defs ..
lemma "rightCylinder S = (\<lambda>a b. S a)" unfolding rel_defs comb_defs ..

text \<open>Alternative formulation in terms of cartesian product.\<close>
lemma leftCylinder_def2:  "leftCylinder  A = \<UU> \<times> A" unfolding rel_defs func_defs comb_defs by simp
lemma rightCylinder_def2: "rightCylinder A = A \<times> \<UU>" unfolding rel_defs func_defs comb_defs by simp

text \<open>They act inverse to (right and left) range by transforming sets into (left and right-ideal) relations.\<close>
lemma "rightRange (leftCylinder A) = A"  unfolding rel_defs comb_defs by simp
lemma "leftRange (rightCylinder A) = A"  unfolding rel_defs comb_defs by simp 

text \<open>Also note that:\<close>
lemma "R \<subseteq>\<^sup>r rightCylinder (leftRange R)" unfolding rel_defs func_defs comb_defs by simp
lemma "R \<subseteq>\<^sup>r leftCylinder (rightRange R)" unfolding rel_defs func_defs comb_defs by auto
proposition "rightCylinder (leftRange R) \<subseteq>\<^sup>r R"  nitpick \<comment> \<open>countermodel found\<close> oops
proposition "leftCylinder (rightRange R) \<subseteq>\<^sup>r R"  nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>Source and target restrictions (as relation-operations) can be encoded in terms of cylindrification.\<close>
definition sourceRestriction::"Set('a) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('a,'b)" ("_\<downharpoonleft>_")
  where "sourceRestriction \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<inter>\<^sup>r) rightCylinder \<^bold>I"
definition targetRestriction::"Set('b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('a,'b)" ("_\<downharpoonright>_")
  where "targetRestriction \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<inter>\<^sup>r) leftCylinder \<^bold>I"

declare sourceRestriction_def[rel_defs] targetRestriction_def[rel_defs]

lemma "A\<downharpoonleft>R = rightCylinder A \<inter>\<^sup>r R" unfolding rel_defs comb_defs ..
lemma "B\<downharpoonright>R = leftCylinder  B \<inter>\<^sup>r R" unfolding rel_defs comb_defs ..
lemma "A\<downharpoonleft>R = (\<lambda>a b. A a \<and> R a b)" unfolding rel_defs comb_defs func_defs by simp
lemma "B\<downharpoonright>R = (\<lambda>a b. B b \<and> R a b)" unfolding rel_defs comb_defs func_defs by simp


subsubsection \<open>Uniqueness and Determinism\<close>

text \<open>By composition with \<open>unique\<close>, we obtain the set of deterministic (or "univalent") elements.
 They get assigned at most one value under the relation (which then behaves deterministically on them)\<close>
definition deterministic::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "deterministic \<equiv> \<^bold>B unique"

text \<open>Also, by composition with \<open>\<exists>!\<close>, we obtain the set of total(ly) deterministic elements. 
 They get assigned precisely one value under the relation (which then behaves as a function on them)\<close>
definition totalDeterministic::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "totalDeterministic \<equiv> \<^bold>B \<exists>!"

declare deterministic_def[rel_defs] totalDeterministic_def[rel_defs]

lemma totalDeterministic_def2: "totalDeterministic R = deterministic R \<inter> leftRange R" 
  unfolding rel_defs func_defs comb_defs by (metis (mono_tags, opaque_lifting))

text \<open>Right- resp. left-unique relations; aka. univalent/(partial-)functional resp. injective relations.\<close>
definition rightUnique::"Set(Rel('a,'b))" 
  where "rightUnique \<equiv> \<forall> \<circ> deterministic"
definition leftUnique::"Set(Rel('a,'b))"
  where "leftUnique \<equiv> \<forall> \<circ> deterministic \<circ> \<^bold>C"

declare rightUnique_def [rel_defs] leftUnique_def [rel_defs]

text \<open>Further names for special kinds of relations, also common in the literature.\<close>
abbreviation(input)   "one_to_one R \<equiv>  leftUnique R \<and>  rightUnique R" \<comment> \<open>injective and functional\<close>
abbreviation(input)  "one_to_many R \<equiv>  leftUnique R \<and> \<not>rightUnique R" \<comment> \<open>injective and not functional\<close>
abbreviation(input) " many_to_one R \<equiv> \<not>leftUnique R \<and>  rightUnique R" \<comment> \<open>functional and not injective\<close>
abbreviation(input) "many_to_many R \<equiv> \<not>leftUnique R \<and> \<not>rightUnique R" \<comment> \<open>neither injective nor functional\<close>

text \<open>Pairs are both right-unique and left-unique, i.e. one-to-one.\<close>
lemma "singletonR \<subseteq> one_to_one" unfolding rel_defs func_defs comb_defs by auto
proposition "one_to_one \<subseteq> singletonR" nitpick \<comment> \<open>counterexample: e.g. empty relation\<close> oops 

text \<open>In fact, any relation can also be generated by its right- resp. left-unique subrelations.\<close>
lemma rightUnique_gen: "R = \<Union>\<^sup>r(\<wp>\<^sup>r R \<inter> rightUnique)" \<comment> \<open>proof by external provers\<close>
  unfolding bigunionR_def2 oops (*TODO*)
lemma leftUnique_gen: "R = \<Union>\<^sup>r(\<wp>\<^sup>r R \<inter> leftUnique)"  \<comment> \<open>proof by external provers\<close>
  unfolding bigunionR_def2 oops (*TODO*)


subsubsection \<open>Totality\<close>

text \<open>Right- resp. left-unique relations; aka. surjective resp. total/serial/multi-functional relations.\<close>
definition rightTotal::"Set(Rel('a,'b))"
  where "rightTotal \<equiv> \<forall> \<circ> rightRange"
definition leftTotal::"Set(Rel('a,'b))"
  where "leftTotal \<equiv> \<forall> \<circ> leftRange"

declare rightTotal_def[rel_defs] leftTotal_def[rel_defs]

text \<open>A relation that relates each element in its source to precisely one element in its target 
 corresponds to a (total) function. They can also be characterized as being both total and functional
 (i.e. left-total and right-unique) relations.\<close>
definition totalFunction::"Set(Rel('a,'b))"
  where "totalFunction \<equiv> \<forall> \<circ> totalDeterministic"

declare totalFunction_def[rel_defs]

lemma totalFunction_def2: "totalFunction R = (leftTotal R \<and> rightUnique R)"
  unfolding rel_defs func_defs comb_defs by metis

text \<open>The inverse of a function (qua relation) is always left-unique and right-total.\<close>
lemma "leftUnique f\<inverse>" unfolding rel_defs func_defs comb_defs by simp
lemma "rightTotal f\<inverse>" unfolding rel_defs func_defs comb_defs by simp


subsection \<open>Transformations between Relations and (Sets of) Functions\<close>

subsubsection \<open>From (Sets of) Functions to Relations\<close>

text \<open>A given function can be disguised as a relation.\<close>
definition asRel::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" ("asRel")
  where "asRel \<equiv> \<^bold>B \<Q>"

declare asRel_def[rel_defs]

lemma "asRel f = \<Q> \<circ> f" unfolding rel_defs ..
lemma "asRel f = (\<lambda>a. \<Q> (f a))" unfolding rel_defs comb_defs ..
lemma "asRel f = (\<lambda>a. (\<lambda>b. \<Q> (f a) b))" unfolding rel_defs comb_defs ..
lemma "asRel f = (\<lambda>a b. f a = b)" unfolding rel_defs comb_defs ..

text \<open>Alternative characterization:\<close>
lemma asRel_def2: "asRel = \<^bold>C \<circ> inverse" unfolding rel_defs func_defs comb_defs ..
lemma "asRel f = \<^bold>C (f\<inverse>)" unfolding asRel_def2 comb_defs ..

text \<open>Relations corresponding to lifted functions are always left-total and right-unique (i.e. functions).\<close>
lemma "totalFunction (asRel f)" unfolding rel_defs func_defs comb_defs by simp


text \<open>A given set of functions can be transformed (or "aggregated") into a relation.\<close>
definition intoRel::"Set('a \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" ("intoRel")
  where "intoRel \<equiv> \<^bold>C (image \<circ> \<^bold>T)"

declare intoRel_def[rel_defs]

lemma "intoRel = (\<lambda>S a. \<lparr>(\<^bold>T a) S\<rparr>)" unfolding rel_defs comb_defs ..
lemma "intoRel S a = \<lparr>(\<lambda>f. f a) S\<rparr>" unfolding rel_defs comb_defs ..

text \<open>Alternative characterization (in terms of relational bigunion):\<close>
lemma intoRel_def2: "intoRel = \<Union>\<^sup>r \<circ> (image asRel)" unfolding rel_defs func_defs comb_defs by blast
lemma "intoRel S = \<Union>\<^sup>r\<lparr>asRel S\<rparr>" unfolding intoRel_def2 comb_defs ..


subsubsection \<open>From Relations to (Sets of) Functions\<close>

text \<open>A given relation can be disguised as a function (and go unnoticed under certain circumstances).\<close>
definition asFun::"Rel('a,'b) \<Rightarrow> ('a \<Rightarrow> 'b)" ("asFun")
  where "asFun \<equiv> \<^bold>B \<epsilon>"

declare asFun_def[rel_defs] 

lemma "asFun R = \<epsilon> \<circ> R" unfolding rel_defs ..
lemma "asFun R = (\<lambda>a. \<epsilon>(R a))" unfolding rel_defs comb_defs ..
lemma "asFun R = (\<lambda>a. \<epsilon> b. R a b)" unfolding rel_defs comb_defs ..

lemma asFun_def2: "totalFunction R \<Longrightarrow> asFun R = \<iota> \<circ> R" \<comment> \<open>alternative definition for total functions\<close>
  unfolding rel_defs func_defs comb_defs apply (rule ext)+ by (metis Uniq_I someI the1_equality')


text \<open>Transforming (or 'decomposing') a given relation into a set of functions.\<close>
definition intoFunSet::"Rel('a,'b) \<Rightarrow> Set('a \<Rightarrow> 'b)" ("intoFunSet")
  where "intoFunSet \<equiv> \<^bold>C ((\<subseteq>\<^sup>r) \<circ> asRel)"

declare intoFunSet_def[rel_defs] 

lemma "intoFunSet R = (\<lambda>f. asRel f \<subseteq>\<^sup>r R)" unfolding rel_defs comb_defs ..
lemma "intoFunSet R = (\<lambda>f. \<forall>a b. f a = b \<rightarrow> R a b)" unfolding rel_defs func_defs comb_defs ..
text \<open>Another perspective:\<close>
lemma intoFunSet_def2: "intoFunSet = \<^bold>B\<^sub>1\<^sub>1 \<wp>\<^sup>r \<^bold>I asRel" unfolding rel_defs func_defs comb_defs ..


subsubsection \<open>Back-and-Forth Translation Conditions\<close> (*TODO: make simplification rules out of this*)

text \<open>Disguising a function as a relation, and back as a function, gives back the original function.\<close>
lemma funRel_trans: "asFun (asRel f) = f" unfolding rel_defs comb_defs by simp 

text \<open>However, disguising a relation as a function, and back as a relation, does not give anything recognizable.\<close>
proposition "asRel (asFun R) = R" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>In case of left-total relations, what we get back is a strict subrelation.\<close>
lemma relFun_trans1: "leftTotal R \<Longrightarrow> asRel (asFun R) \<subseteq>\<^sup>r R" unfolding rel_defs func_defs comb_defs by (metis someI)
proposition "leftTotal R \<Longrightarrow> R \<subseteq>\<^sup>r asRel (asFun R)" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>In case of right-unique relations, what we get back is a strict superrelation.\<close>
lemma relFun_trans2: "rightUnique R \<Longrightarrow> R \<subseteq>\<^sup>r asRel (asFun R)" unfolding rel_defs func_defs comb_defs by auto
proposition "rightUnique R \<Longrightarrow> asRel (asFun R) \<subseteq>\<^sup>r R" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>Indeed, we get back the original relation when it is a total-function.\<close>
lemma relFun_trans: "totalFunction R \<Longrightarrow> asRel (asFun R) = R" 
  unfolding asFun_def2 unfolding rel_defs func_defs comb_defs apply (rule ext)+ by (metis the_equality)


text \<open>Transforming a set of functions into a relation, and back to a set of functions, gives a strict superset.\<close>
lemma funsetRel_trans1: "S \<subseteq> intoFunSet (intoRel S)" unfolding rel_defs func_defs comb_defs by auto
proposition "intoFunSet (intoRel S) \<subseteq> S" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>We get the original set in those cases where it corresponds already to a transformed relation.\<close>
lemma funsetRel_trans2:"let S = intoFunSet R in intoFunSet (intoRel S) \<subseteq> S" unfolding rel_defs func_defs comb_defs by metis

text \<open>Transforming a relation into a set of functions, and back to a relation, gives a strict subrelation.\<close>
lemma relFunSet_trans1: "intoRel (intoFunSet R) \<subseteq>\<^sup>r R" unfolding rel_defs func_defs comb_defs by blast
proposition "R \<subseteq>\<^sup>r intoRel (intoFunSet R)" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>In fact, we get the original relation in case it is left-total.\<close>
lemma leftTotal_auxsimp: "leftTotal R \<Longrightarrow> R a b = (let f = (asFun R)[a \<mapsto> b] in (f a = b \<and> (asRel f) \<subseteq>\<^sup>r R))"
  unfolding func_defs rel_defs comb_defs by (metis (full_types) some_eq_imp)
lemma relFunSet_trans2: "leftTotal R \<Longrightarrow> R \<subseteq>\<^sup>r intoRel (intoFunSet R)"
  unfolding subrel_def orderer_def unfolding intoRel_def intoFunSet_def unfolding func_defs comb_defs by (meson leftTotal_auxsimp)
lemma relFunSet_simp: "leftTotal R \<Longrightarrow> intoRel (intoFunSet R) = R"
  by (simp add: relFunSet_trans1 relFunSet_trans2 subrel_antisym)


subsection \<open>Transpose and Cotranspose\<close>

text \<open>Relations come with two further idiosyncratic unary operations.
 The first one is transposition (aka. "converse" or "reverse"), which naturally arises by seeing
 relations as binary operations (with boolean codomain), and corresponds to the \<open>\<^bold>C\<close> combinator.
 The second one, which we call "cotransposition", corresponds to the transpose/converse of the 
 complement (which is in fact identical to the complement of the transpose).\<close>

definition transpose::"Rel('a,'b) \<Rightarrow> Rel('b,'a)" ("\<smile>")
  where "\<smile> \<equiv> \<^bold>C"
definition cotranspose::"Rel('a,'b) \<Rightarrow> Rel('b,'a)" ("\<sim>")
  where "\<sim> \<equiv> \<midarrow>\<^sup>r \<circ> \<^bold>C"

declare transpose_def[rel_defs] cotranspose_def[rel_defs]

text \<open>Most of the time we will employ the following superscript notation (analogously to complement).\<close>
notation(input) transpose  ("(_)\<^sup>\<smile>") and cotranspose  ("(_)\<^sup>\<sim>") 
notation(output) transpose  ("'(_')\<^sup>\<smile>") and cotranspose  ("'(_')\<^sup>\<sim>") 

lemma "R\<^sup>\<sim> = R\<^sup>\<smile>\<^sup>\<midarrow>" unfolding rel_defs comb_defs ..
lemma "R\<^sup>\<sim> = R\<^sup>\<midarrow>\<^sup>\<smile>" unfolding rel_defs func_defs comb_defs ..

lemma transpose_involutive: "R\<^sup>\<smile>\<^sup>\<smile> = R" unfolding rel_defs func_defs comb_defs by simp
lemma cotranspose_involutive: "R\<^sup>\<sim>\<^sup>\<sim> = R" unfolding rel_defs func_defs comb_defs by simp
lemma complement_involutive: "R\<^sup>\<midarrow>\<^sup>\<midarrow> = R" unfolding rel_defs func_defs comb_defs by simp

text \<open>Clearly, (co)transposition (co)distributes over union and intersection.\<close>
lemma "(R \<union>\<^sup>r T)\<^sup>\<smile> = (R\<^sup>\<smile>) \<union>\<^sup>r (T\<^sup>\<smile>)" unfolding rel_defs func_defs comb_defs ..
lemma "(R \<inter>\<^sup>r T)\<^sup>\<smile> = (R\<^sup>\<smile>) \<inter>\<^sup>r (T\<^sup>\<smile>)" unfolding rel_defs func_defs comb_defs ..
lemma "(R \<union>\<^sup>r T)\<^sup>\<sim> = (R\<^sup>\<sim>) \<inter>\<^sup>r (T\<^sup>\<sim>)" unfolding rel_defs func_defs comb_defs by simp
lemma "(R \<inter>\<^sup>r T)\<^sup>\<sim> = (R\<^sup>\<sim>) \<union>\<^sup>r (T\<^sup>\<sim>)" unfolding rel_defs func_defs comb_defs by simp

text \<open>The inverse of a function corresponds to its converse when seen as a relation.\<close>
lemma \<open>f\<inverse> = (asRel f)\<^sup>\<smile>\<close> unfolding rel_defs func_defs comb_defs ..

text \<open>Relational "lifting" commutes with transpose.\<close>
lemma relLiftEx_trans: "\<^bold>\<Phi>\<^sub>\<exists> (R\<^sup>\<smile>) = (\<^bold>\<Phi>\<^sub>\<exists> R)\<^sup>\<smile>" unfolding rel_defs func_defs comb_defs ..
lemma relLiftAll_trans: "\<^bold>\<Phi>\<^sub>\<forall> (R\<^sup>\<smile>) = (\<^bold>\<Phi>\<^sub>\<forall> R)\<^sup>\<smile>" unfolding rel_defs func_defs comb_defs ..
text \<open>And "dually commutes" with co-transpose.\<close>
lemma relLiftEx_cotrans: "\<^bold>\<Phi>\<^sub>\<exists> (R\<^sup>\<sim>) = (\<^bold>\<Phi>\<^sub>\<forall> R)\<^sup>\<sim>" unfolding rel_defs func_defs comb_defs by simp
lemma relLiftAll_cotrans: "\<^bold>\<Phi>\<^sub>\<forall> (R\<^sup>\<sim>) = (\<^bold>\<Phi>\<^sub>\<exists> R)\<^sup>\<sim>" unfolding rel_defs func_defs comb_defs by simp


text \<open>Using transpose, we can encode a convenient notion of "interpolants" (wrt. two relations) as the set of
 elements that "bridge" between two given points (belonging each to one of the relations), as follows.\<close>
definition interpolants :: "Rel('a,'c) \<Rightarrow> Rel('c,'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> Set('c)"
  where "interpolants \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<inter>) \<^bold>A \<smile>"
text \<open>And, since we are at it, we add a convenient dual notion.\<close>
definition dualInterpolants :: "Rel('a,'c) \<Rightarrow> Rel('c,'b) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> Set('c)"
  where "dualInterpolants \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<union>) \<^bold>A \<smile>"

declare interpolants_def[rel_defs] dualInterpolants_def[rel_defs]

lemma "interpolants     R\<^sub>1 R\<^sub>2 a b = R\<^sub>1 a \<inter> R\<^sub>2\<^sup>\<smile> b" unfolding rel_defs comb_defs ..
lemma "dualInterpolants R\<^sub>1 R\<^sub>2 a b = R\<^sub>1 a \<union> R\<^sub>2\<^sup>\<smile> b" unfolding rel_defs comb_defs ..
lemma "interpolants     R\<^sub>1 R\<^sub>2 a b = (\<lambda>c. R\<^sub>1 a c \<and> R\<^sub>2 c b)" unfolding rel_defs func_defs comb_defs ..
lemma "dualInterpolants R\<^sub>1 R\<^sub>2 a b = (\<lambda>c. R\<^sub>1 a c \<or> R\<^sub>2 c b)" unfolding rel_defs func_defs comb_defs ..


subsection \<open>Structure Preservation and Reflection\<close>

text \<open>The function f preserves the relational structure of R into T.\<close>
abbreviation(input) preserving::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Set(Op('a,'b))" ("_,_-preserving")
  where "R,T-preserving f \<equiv> \<forall>X Y. R X Y \<rightarrow> T (f X) (f Y)"

text \<open>The function f reflects the relational structure of T into R.\<close>
abbreviation(input) reflecting::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Set(Op('a,'b))" ("_,_-reflecting")
  where "R,T-reflecting f \<equiv> \<forall>X Y. R X Y \<leftarrow> T (f X) (f Y)"

text \<open>This generalizes the notion of order-embedding to (endo)relations in general.\<close>
abbreviation(input) embedding::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Set(Op('a,'b))" ("_,_-embedding")
  where "R,T-embedding f \<equiv> \<forall>X Y. R X Y = T (f X) (f Y)"

text \<open>Clearly, a function is an embedding iff it is both preserving and reflecting.\<close>
lemma "R,T-embedding f = (R,T-preserving f \<and> R,T-reflecting f)" by auto

text \<open>An endofunction f is said to be monotonic resp. anti(mono)tonic wrt an endorelation R when it 
  is R-preserving resp. R-reversing\<close>
definition monotonic::"ERel('a) \<Rightarrow> Set(EOp('a))" ("_-MONO")
  where "R-MONO \<equiv> R,R-preserving"
definition antitonic::"ERel('a) \<Rightarrow> Set(EOp('a))" ("_-ANTI")
  where "R-ANTI \<equiv> R,R\<^sup>\<smile>-preserving"

declare monotonic_def[rel_defs] antitonic_def[rel_defs] 

lemma "R-MONO f = (\<forall>A B. R A B \<longrightarrow> R (f A) (f B))" unfolding rel_defs comb_defs ..
lemma "R-ANTI f = (\<forall>A B. R A B \<longrightarrow> R (f B) (f A))" unfolding rel_defs comb_defs ..
lemma "(\<subseteq>\<^sup>r)-MONO f = (\<forall>A B. A \<subseteq>\<^sup>r B \<longrightarrow> f A \<subseteq>\<^sup>r f B)" unfolding rel_defs comb_defs ..
lemma "(\<subseteq>\<^sup>r)-ANTI f = (\<forall>A B. A \<subseteq>\<^sup>r B \<longrightarrow> f B \<subseteq>\<^sup>r f A)" unfolding rel_defs comb_defs ..

text \<open>Monotonic endofunctions are called "closure/interior operators" when they satisfy particular properties.\<close>
definition closure ("_-CLOSURE")
  where "R-CLOSURE \<phi> \<equiv> R-MONO \<phi> \<and> R-EXPN \<phi> \<and> R-wCNTR \<phi>"
definition interior ("_-INTERIOR")
  where "R-INTERIOR \<phi> \<equiv> R-MONO \<phi> \<and> R-CNTR \<phi> \<and> R-wEXPN \<phi>"

declare closure_def[rel_defs] interior_def[rel_defs]

lemma closure_setprop: "(\<subseteq>)-CLOSURE f = (\<forall>A B. (A \<subseteq> f B) \<leftrightarrow> (f A \<subseteq> f B))"
  unfolding rel_defs func_defs comb_defs by (smt (z3)) 


subsection \<open>Function-like Structure II\<close>

subsubsection \<open>Monoidal Structure (composition and its dual)\<close>

text \<open>In analogy to functions, relations can also be composed, as follows:\<close>
definition relComp::"Rel('a,'b) \<Rightarrow> Rel('b,'c) \<Rightarrow>  Rel('a,'c)" (infixr ";\<^sup>r" 55)
  where "(;\<^sup>r) =  \<^bold>B\<^sub>2\<^sub>2 (\<sqinter>) \<^bold>A \<smile> "
text \<open>Again, we can in fact define an operator that acts as a "dual" to relation-composition:\<close>
definition relDualComp::"Rel('c,'a) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('c,'b)" (infixr "\<dagger>\<^sup>r" 55)
  where "(\<dagger>\<^sup>r) \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<squnion>) \<^bold>A \<smile>"

declare relDualComp_def[rel_defs] relComp_def[rel_defs]

lemma "R\<^sub>1 ;\<^sup>r R\<^sub>2 = (\<lambda>a b. R\<^sub>1 a \<sqinter> R\<^sub>2\<^sup>\<smile> b)" unfolding rel_defs comb_defs ..
lemma "R\<^sub>1 \<dagger>\<^sup>r R\<^sub>2 = (\<lambda>a b. R\<^sub>1 a \<squnion> R\<^sub>2\<^sup>\<smile> b)" unfolding rel_defs comb_defs ..
lemma "R\<^sub>1 ;\<^sup>r R\<^sub>2 = (\<lambda>a b. \<exists>c. R\<^sub>1 a c \<and> R\<^sub>2 c b)" unfolding rel_defs func_defs comb_defs ..
lemma "R\<^sub>1 \<dagger>\<^sup>r R\<^sub>2 = (\<lambda>a b. \<forall>c. R\<^sub>1 a c \<or> R\<^sub>2 c b)" unfolding rel_defs func_defs comb_defs ..
lemma "R\<^sub>1 ;\<^sup>r R\<^sub>2 = (\<lambda>a b. \<exists>(interpolants R\<^sub>1 R\<^sub>2 a b))" unfolding rel_defs func_defs comb_defs ..
lemma "R\<^sub>1 \<dagger>\<^sup>r R\<^sub>2 = (\<lambda>a b. \<forall>(dualInterpolants R\<^sub>1 R\<^sub>2 a b))" unfolding rel_defs func_defs comb_defs ..
lemma "R\<^sub>1 ;\<^sup>r R\<^sub>2 = (\<exists> \<circ>\<^sub>2 (interpolants R\<^sub>1 R\<^sub>2))" unfolding rel_defs func_defs comb_defs ..
lemma "R\<^sub>1 \<dagger>\<^sup>r R\<^sub>2 = (\<forall> \<circ>\<^sub>2 (dualInterpolants R\<^sub>1 R\<^sub>2))" unfolding rel_defs func_defs comb_defs ..
lemma relComp_def2:     "(;\<^sup>r) = \<exists> \<circ>\<^sub>4 interpolants" unfolding rel_defs func_defs comb_defs ..
lemma relDualComp_def2: "(\<dagger>\<^sup>r) = \<forall> \<circ>\<^sub>4 dualInterpolants" unfolding rel_defs func_defs comb_defs ..

text \<open>We introduce convenient "flipped" notations for (dual-)composition (analogous to those for functions).\<close>
abbreviation(input) relComp_t::"Rel('b,'c) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('a,'c)" (infixl "\<circ>\<^sup>r" 55)
  where "R \<circ>\<^sup>r T \<equiv> T ;\<^sup>r R"
abbreviation(input) relDualComp_t::"Rel('c,'b) \<Rightarrow> Rel('a,'c) \<Rightarrow> Rel('a,'b)" (infixl "\<bullet>\<^sup>r" 55)
  where "R \<bullet>\<^sup>r T \<equiv> T \<dagger>\<^sup>r R"

text \<open>Unsurprisingly, (relational) composition and dual-composition are dual wrt. (relational) complement.\<close>
lemma relCompDuality1: "R \<bullet>\<^sup>r T = ((R\<^sup>\<midarrow>) \<circ>\<^sup>r (T\<^sup>\<midarrow>))\<^sup>\<midarrow>" 
  unfolding rel_defs func_defs comb_defs by auto
lemma relCompDuality2: "R \<circ>\<^sup>r T = ((R\<^sup>\<midarrow>) \<bullet>\<^sup>r (T\<^sup>\<midarrow>))\<^sup>\<midarrow>" 
  unfolding rel_defs func_defs comb_defs by auto

text \<open>Moreover, relation (dual)composition and (dis)equality satisfy the monoid conditions\<close>
lemma relComp_assoc: "(R \<circ>\<^sup>r T) \<circ>\<^sup>r V = R \<circ>\<^sup>r (T \<circ>\<^sup>r V)" \<comment> \<open>associativity\<close>
  unfolding rel_defs func_defs comb_defs by auto                   
lemma relComp_id1: "\<Q> \<circ>\<^sup>r R = R"                     \<comment> \<open>identity 1\<close>
  unfolding rel_defs func_defs comb_defs by simp                   
lemma relComp_id2: "R \<circ>\<^sup>r \<Q> = R"                     \<comment> \<open>identity 2\<close>
  unfolding rel_defs func_defs comb_defs by simp   
lemma relCompDual_assoc: "(R \<bullet>\<^sup>r T) \<bullet>\<^sup>r V = R \<bullet>\<^sup>r (T \<bullet>\<^sup>r V)" \<comment> \<open>associativity\<close>
  unfolding rel_defs func_defs comb_defs by auto                   
lemma relCompDual_id1: "\<D> \<bullet>\<^sup>r R = R"                     \<comment> \<open>identity 1\<close>
  unfolding rel_defs func_defs comb_defs by auto                   
lemma relCompDual_id2: "R \<bullet>\<^sup>r \<D> = R"                     \<comment> \<open>identity 2\<close>
  unfolding rel_defs func_defs comb_defs by simp 

text \<open>Transpose acts as an "antihomomorphism" wrt. composition as well as its dual.\<close>
lemma relComp_antihom:     "(R \<circ>\<^sup>r T)\<^sup>\<smile> = ((T\<^sup>\<smile>) \<circ>\<^sup>r (R\<^sup>\<smile>))" unfolding rel_defs func_defs comb_defs by auto
lemma relCompDual_antihom: "(R \<bullet>\<^sup>r T)\<^sup>\<smile> = ((T\<^sup>\<smile>) \<bullet>\<^sup>r (R\<^sup>\<smile>))" unfolding rel_defs func_defs comb_defs by auto

text \<open>In a similar spirit, we have:\<close>
lemma "(R \<circ>\<^sup>r T)\<^sup>\<sim> = ((T\<^sup>\<sim>) \<bullet>\<^sup>r (R\<^sup>\<sim>))" unfolding rel_defs func_defs comb_defs by auto
lemma "(R \<bullet>\<^sup>r T)\<^sup>\<sim> = ((T\<^sup>\<sim>) \<circ>\<^sup>r (R\<^sup>\<sim>))" unfolding rel_defs func_defs comb_defs by auto


subsubsection \<open>Residuals\<close>

text \<open>Introduce residuals (on the left resp. right) wrt. composition taken as \<open>(;\<^sup>r)\<close>.\<close>
definition residualOnRight::"Rel('c,'a) \<Rightarrow> Rel('c,'b) \<Rightarrow> Rel('a,'b)" (infix "\<Zrres>\<^sup>r" 99)
  where "R \<Zrres>\<^sup>r S \<equiv> (R\<^sup>\<sim>) \<dagger>\<^sup>r S"
definition residualOnLeft::"Rel('a,'c) \<Rightarrow> Rel('b,'c) \<Rightarrow> Rel('a,'b)" (infix "\<Zndres>\<^sup>r" 99)
  where "R \<Zndres>\<^sup>r S \<equiv>  R  \<dagger>\<^sup>r (S\<^sup>\<sim>)"

declare residualOnRight_def[rel_defs] residualOnLeft_def[rel_defs]

text \<open>Residuals can alternatively be defined using converse and complement.\<close>
lemma residualOnRight_def2: "R \<Zrres>\<^sup>r S = ((R\<^sup>\<smile>) ;\<^sup>r (S\<^sup>\<midarrow>))\<^sup>\<midarrow>" unfolding rel_defs func_defs comb_defs by simp
lemma residualOnLeft_def2:  "R \<Zndres>\<^sup>r S = ((R\<^sup>\<midarrow>) ;\<^sup>r (S\<^sup>\<smile>))\<^sup>\<midarrow>" unfolding rel_defs func_defs comb_defs by simp

text \<open>We verify that they work as residuals wrt. \<open>(;\<^sup>r)\<close> in the expected way.\<close>
lemma residual_simp1: "(R ;\<^sup>r S \<subseteq>\<^sup>r T) = (S \<subseteq>\<^sup>r R \<Zrres>\<^sup>r T)" unfolding rel_defs func_defs comb_defs by auto
lemma residual_simp2: "(R ;\<^sup>r S \<subseteq>\<^sup>r T) = (R \<subseteq>\<^sup>r T \<Zndres>\<^sup>r S)" unfolding rel_defs func_defs comb_defs by auto

text \<open>Introduce some convenient reversed notation for the corresponding residuals wrt. \<open>(\<circ>\<^sup>r)\<close>.\<close>
abbreviation(input) residualOnRight_t (infix "\<Zdres>\<^sup>r" 99)
  where "R \<Zdres>\<^sup>r S \<equiv> S \<Zrres>\<^sup>r R"
abbreviation(input) residualOnLeft_t (infix "\<Znrres>\<^sup>r" 99)
  where "R \<Znrres>\<^sup>r S \<equiv> S \<Zndres>\<^sup>r R"

text \<open>Check alternative characterization.\<close>
lemma "R \<Znrres>\<^sup>r S = ((R\<^sup>\<smile>) \<circ>\<^sup>r (S\<^sup>\<midarrow>))\<^sup>\<midarrow>" unfolding rel_defs func_defs comb_defs by simp
lemma "R \<Zdres>\<^sup>r S = ((R\<^sup>\<midarrow>) \<circ>\<^sup>r (S\<^sup>\<smile>))\<^sup>\<midarrow>" unfolding rel_defs func_defs comb_defs by simp

text \<open>Verify that they work as residuals wrt. \<open>(\<circ>\<^sup>r)\<close> in the expected way.\<close>
lemma "(R \<circ>\<^sup>r S \<subseteq>\<^sup>r T) = (S \<subseteq>\<^sup>r R \<Znrres>\<^sup>r T)" unfolding rel_defs func_defs comb_defs by auto
lemma "(R \<circ>\<^sup>r S \<subseteq>\<^sup>r T) = (R \<subseteq>\<^sup>r T \<Zdres>\<^sup>r S)" unfolding rel_defs func_defs comb_defs by auto


subsubsection \<open>Ideal Elements\<close>

text \<open>A related property of relations is that of (generating a) left- resp. right ideal.\<close>
definition leftIdeal::"Set(Rel('a,'b))"
  where "leftIdeal \<equiv> FP ((;\<^sup>r) \<UU>\<^sup>r)"
definition rightIdeal::"Set(Rel('a,'b))"
  where "rightIdeal \<equiv> FP ((\<circ>\<^sup>r) \<UU>\<^sup>r)"

declare leftIdeal_def[rel_defs] rightIdeal_def[rel_defs]

lemma "leftIdeal  R = (R = \<UU>\<^sup>r ;\<^sup>r R)" unfolding rel_defs func_defs comb_defs ..
lemma "rightIdeal R = (R = R  ;\<^sup>r \<UU>\<^sup>r)" unfolding rel_defs func_defs comb_defs ..

text \<open>An alternative, equivalent definition also common in the literature (e.g. on semirings).\<close>
lemma leftIdeal_def2:  "leftIdeal  R = (\<forall>T. R \<circ>\<^sup>r T \<subseteq>\<^sup>r R)" unfolding rel_defs func_defs comb_defs by meson
lemma rightIdeal_def2: "rightIdeal R = (\<forall>T. R ;\<^sup>r T \<subseteq>\<^sup>r R)" unfolding rel_defs func_defs comb_defs by meson

text \<open>In fact, the left/right-cylindrification operations discussed previously return left/right-ideal 
 (generating) relations. Moreover, all left/right-ideal relations can be generated this way.\<close>
lemma "rightIdeal = range rightCylinder" unfolding rel_defs func_defs comb_defs apply (rule ext) by metis
lemma "leftIdeal  = range leftCylinder" unfolding rel_defs func_defs comb_defs apply (rule ext) by metis


subsubsection \<open>Kernel of a Relation\<close>

text \<open>The \<open>kernel\<close> of a relation relates those elements in its source domain that are related to some 
 same value (i.e. whose images overlap).\<close>
definition relKernel::"Rel('a,'b) \<Rightarrow> ERel('a)"
  where "relKernel \<equiv> \<^bold>\<Psi>\<^sub>2 (\<sqinter>)"

declare relKernel_def[rel_defs]

lemma "relKernel R = (\<lambda>x y. R x \<sqinter> R y)" unfolding relKernel_def comb_defs ..

text \<open>The notion of kernel for relations corresponds to (and generalizes) the functional counterpart.\<close>
lemma "relKernel (asRel f) = kernel f" unfolding rel_defs func_defs comb_defs by metis
lemma "totalFunction R \<Longrightarrow> kernel (asFun R) = relKernel R" unfolding rel_defs func_defs comb_defs by (metis (mono_tags))


subsubsection \<open>Pullback and Equalizer of a Pair of Relations\<close>

text \<open>The pullback (aka. fiber product) of two relations R and T (sharing the same target), 
 relates those pairs of elements that get assigned some same value by R and T respectively.\<close>
definition relPullback :: "Rel('a,'c) \<Rightarrow> Rel('b,'c) \<Rightarrow> Rel('a,'b)"
  where "relPullback \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<sqinter>)"

declare relPullback_def[rel_defs]

lemma "relPullback R T = (\<lambda>x y. R x \<sqinter> T y)" unfolding relPullback_def comb_defs ..

text \<open>Pullback can be said to be "symmetric" in the following sense.\<close>
lemma relPullback_symm: "relPullback = \<^bold>C\<^sub>2\<^sub>1\<^sub>4\<^sub>3 relPullback" unfolding relPullback_def func_defs comb_defs by metis
lemma relPullback_symm': "relPullback R T x y = relPullback T R y x" apply (subst relPullback_symm) unfolding comb_defs ..
lemma "relPullback = \<^bold>C \<circ>\<^sub>2 (\<^bold>C relPullback)" apply (subst relPullback_symm) unfolding comb_defs ..

text \<open>The notion of pullback for relations corresponds to (and generalizes) the functional counterpart.\<close>
lemma "relPullback (asRel f) (asRel g) = pullback f g" 
  unfolding rel_defs comb_defs func_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> pullback (asFun R) (asFun T) = relPullback R T" 
  unfolding rel_defs comb_defs func_defs by (metis (mono_tags))

text \<open>Converse and kernel of a relation can be easily stated in terms of relation-pullback.\<close>
lemma "\<^bold>C = relPullback \<Q>" unfolding rel_defs func_defs comb_defs by auto
lemma "relKernel = \<^bold>W relPullback" unfolding rel_defs comb_defs ..


text \<open>The equalizer of two relations \<open>R\<close> and \<open>T\<close> (sharing the same source and target) is the set of 
 elements \<open>x\<close> in their (common) source that are related to some same value (i.e. \<open>R x\<close> and \<open>T x\<close> intersect).\<close>
definition relEqualizer :: "Rel('a,'b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('a)"
  where "relEqualizer \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<sqinter>)"

declare relEqualizer_def[rel_defs]

lemma "relEqualizer R T = (\<lambda>x. R x \<sqinter> T x)" unfolding rel_defs comb_defs ..

text \<open>In fact, the equalizer of two relations can be stated in terms of their pullback.\<close>
lemma "relEqualizer = \<^bold>W \<circ>\<^sub>2 relPullback" unfolding rel_defs comb_defs ..

text \<open>Note that we can swap the roles of "points" and "functions" in the above definitions using permutators.\<close>
lemma "\<^bold>R relEqualizer x = (\<lambda>R T. R x \<sqinter> T x)" unfolding rel_defs comb_defs ..
lemma "\<^bold>C\<^sub>2 relPullback x y = (\<lambda>R T. R x \<sqinter> T y)" unfolding rel_defs comb_defs ..

text \<open>The notion of equalizer for relations corresponds to (and generalizes) the functional counterpart.\<close>
lemma "relEqualizer (asRel f) (asRel g) = equalizer f g" 
  unfolding rel_defs comb_defs func_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> equalizer (asFun R) (asFun T) = relEqualizer R T" 
  unfolding rel_defs comb_defs func_defs by (metis (mono_tags))


subsubsection \<open>Pushout and Coequalizer of a Pair of Relations\<close>

text \<open>The pushout (aka. fiber coproduct) of two relations R and T (sharing the same source), relates
 pairs of elements (in their targets) whose preimages under R resp. T intersect.\<close>
abbreviation relPushout :: "Rel('a,'b) \<Rightarrow> Rel('a,'c) \<Rightarrow> Rel('b,'c)"
  where "relPushout R T \<equiv> relPullback R\<^sup>\<smile> T\<^sup>\<smile>"

lemma "relPushout R T = (\<lambda>x y. R\<^sup>\<smile> x \<sqinter> T\<^sup>\<smile> y)" unfolding rel_defs comb_defs ..

text \<open>The notion of pushout for relations corresponds to (and generalizes) the functional counterpart.\<close>
lemma "relPushout (asRel f) (asRel g) = pushout f g" 
  unfolding rel_defs comb_defs func_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> pushout (asFun R) (asFun T) = relPushout R T" 
  unfolding rel_defs comb_defs func_defs by (metis (full_types))

text \<open>The coequalizer of two relations R and T (sharing the same source and target) is the set of 
 elements in their (common) target whose preimage under R resp. T intersect.\<close>
abbreviation relCoequalizer :: "Rel('a,'b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('b)"
  where "relCoequalizer R T \<equiv> relEqualizer R\<^sup>\<smile> T\<^sup>\<smile>" 

lemma "relCoequalizer R T = (\<lambda>x. R\<^sup>\<smile> x \<sqinter> T\<^sup>\<smile> x)" unfolding rel_defs comb_defs ..

text \<open>The coequalizer of two relations can be stated in terms of pushout.\<close>
lemma "relCoequalizer = \<^bold>W \<circ>\<^sub>2 relPushout" unfolding rel_defs comb_defs ..

text \<open>The notion of coequalizer for relations corresponds to (and generalizes) the functional counterpart.\<close>
lemma "relCoequalizer (asRel f) (asRel g) = coequalizer f g" 
  unfolding rel_defs comb_defs func_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> coequalizer (asFun R) (asFun T) = relCoequalizer R T" 
  unfolding rel_defs comb_defs func_defs by (metis (full_types))


subsubsection \<open>Diagonal Elements\<close>

text \<open>The notion of diagonal (aka. reflexive) elements of an endorelation is the relational counterpart 
 to the notion of fixed-points of an endofunction. It corresponds to the \<open>\<^bold>W\<close> combinator.\<close>
abbreviation(input) diagonal::"ERel('a) \<Rightarrow> Set('a)" ("\<Delta>")
  where "\<Delta> \<equiv> \<^bold>W"

lemma "\<Delta> R x = R x x" unfolding rel_defs comb_defs ..

lemma "\<Delta> (asRel f) = FP f" 
  unfolding rel_defs comb_defs func_defs by auto
lemma "totalFunction R \<Longrightarrow> FP (asFun R) = \<Delta> R" 
  unfolding rel_defs comb_defs func_defs by (metis someI)

text \<open>Analogously, the notion of anti-diagonal (aka. irreflexive) elements of an endorelation 
 (notation: \<open>\<Delta>\<^sup>\<midarrow>\<close>) is the relational counterpart to the notion of non-fixed-points of an endofunction.\<close>
lemma "\<Delta>\<^sup>\<midarrow> = \<midarrow>\<^sup>r\<Delta>" unfolding rel_defs comb_defs ..
lemma "\<Delta>\<^sup>\<midarrow> = \<Delta> \<circ> \<midarrow>\<^sup>r" unfolding rel_defs func_defs comb_defs ..
lemma "\<Delta>\<^sup>\<midarrow> R x = (\<not>R x x)" unfolding rel_defs func_defs comb_defs ..
lemma "\<Delta>\<^sup>\<midarrow> = \<midarrow> \<circ> \<Delta>" unfolding rel_defs func_defs comb_defs ..
lemma "\<Delta>\<^sup>\<midarrow> R = \<midarrow>(\<Delta> R)" unfolding rel_defs func_defs comb_defs ..

lemma "\<Delta>\<^sup>\<midarrow> (asRel f) = nFP f" 
  unfolding rel_defs comb_defs func_defs by auto
lemma "totalFunction R \<Longrightarrow> nFP (asFun R) = \<Delta>\<^sup>\<midarrow> R" 
  unfolding rel_defs comb_defs func_defs by (metis someI)


subsection \<open>Relation-based Set-Operations\<close>

text \<open>We can extend the definitions of the (pre)image set-operator from functions to relations
 together with their "dual" counterparts.\<close>
definition rightImage::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)"
  where "rightImage \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>C)"
definition leftImage::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)"
  where "leftImage \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>A)"
definition rightDualImage::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)" 
  where "rightDualImage \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<subseteq>) \<^bold>C)"
definition leftDualImage::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)" 
  where "leftDualImage \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<subseteq>) \<^bold>A)"

declare rightImage_def[rel_defs] leftImage_def[rel_defs] rightDualImage_def[rel_defs] leftDualImage_def[rel_defs] 

notation(input) rightImage ("_-rightImage") and  leftImage ("_-leftImage") and
                rightDualImage ("_-rightDualImage") and  leftDualImage ("_-leftDualImage")

lemma "R-rightImage A = (\<lambda>b. R\<^sup>\<smile> b \<sqinter> A)" unfolding rel_defs comb_defs ..
lemma "R-leftImage B = (\<lambda>a. R a \<sqinter> B)" unfolding rel_defs comb_defs ..
lemma "R-rightDualImage A = (\<lambda>b. R\<^sup>\<smile> b \<subseteq> A)" unfolding rel_defs comb_defs ..
lemma "R-leftDualImage B = (\<lambda>a. R a \<subseteq> B)" unfolding rel_defs comb_defs ..

lemma "R-rightImage A b = (\<exists>a. R a b \<and> A a)" unfolding rel_defs func_defs comb_defs ..
lemma "R-leftImage B a = (\<exists>b. R a b \<and> B b)" unfolding rel_defs func_defs comb_defs ..
lemma "R-rightDualImage A b = (\<forall>a. R a b \<rightarrow> A a)" unfolding rel_defs func_defs comb_defs ..
lemma "R-leftDualImage B a = (\<forall>b. R a b \<rightarrow> B b)" unfolding rel_defs func_defs comb_defs ..

text \<open>Convenient characterizations in terms of big-union and big-intersection.\<close>
lemma rightImage_def2: "rightImage = \<Union> \<circ>\<^sub>2 image"
  unfolding rel_defs func_defs comb_defs by fastforce
lemma leftImage_def2: "leftImage = \<Union> \<circ>\<^sub>2 (image \<circ> \<smile>)"
  unfolding rel_defs func_defs comb_defs by fastforce
lemma rightDualImage_def2: "rightDualImage = \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 image \<midarrow>\<^sup>r \<midarrow>)"
  unfolding rel_defs func_defs comb_defs by fastforce
lemma leftDualImage_def2: "leftDualImage = \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 image \<sim> \<midarrow>)"
  unfolding rel_defs func_defs comb_defs by fastforce

lemma "R-rightImage A = \<Union>\<lparr>R A\<rparr>" unfolding rightImage_def2 comb_defs ..
lemma "R-leftImage B = \<Union>\<lparr>R\<^sup>\<smile> B\<rparr>" unfolding leftImage_def2 comb_defs ..
lemma "R-rightDualImage A =  \<Inter>\<lparr>R\<^sup>\<midarrow> \<midarrow>A\<rparr>" unfolding rightDualImage_def2 comb_defs ..
lemma "R-leftDualImage B =  \<Inter>\<lparr>R\<^sup>\<sim> \<midarrow>B\<rparr>" unfolding leftDualImage_def2 comb_defs ..

text \<open>As expected, relational right- resp. left-image correspond to functional image resp. preimage.\<close>
lemma "rightImage (asRel f) = image f" 
  unfolding rel_defs comb_defs func_defs by auto
lemma "leftImage (asRel f) = preimage f" 
  unfolding rel_defs comb_defs func_defs by auto
lemma "totalFunction R \<Longrightarrow> image (asFun R) = rightImage R" 
  unfolding rel_defs comb_defs func_defs by (metis someI)
lemma "totalFunction R \<Longrightarrow> preimage (asFun R) = leftImage R"
  unfolding rel_defs comb_defs func_defs by (metis someI)

text \<open>Clearly, each direction (right/left) uniquely determines the other (its transpose).\<close>
lemma rightImage_defT: "R-rightImage = R\<^sup>\<smile>-leftImage" unfolding rel_defs comb_defs ..
lemma leftImage_defT: "R-leftImage = R\<^sup>\<smile>-rightImage" unfolding rel_defs comb_defs ..
lemma rightDualImage_defT: "R-rightDualImage = R\<^sup>\<smile>-leftDualImage" unfolding rel_defs comb_defs ..
lemma leftDualImage_defT: "R-leftDualImage = R\<^sup>\<smile>-rightDualImage" unfolding rel_defs comb_defs ..


text \<open>Following operators (aka. "polarities") are inspired by (and generalize) the notion of upper/lower 
 bounds of a set wrt. an ordering. They are defined here for relations in general.\<close>
definition rightBound::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)"
  where "rightBound \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>C)"                                 (*cf. rightDualImage (using \<supseteq>)*)
definition leftBound::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)"
  where "leftBound \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>A)"                                   (*cf. leftDualImage (using \<supseteq>)*)
definition rightDualBound::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)"
  where  "rightDualBound \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>C)"              (*cf. rightImage (preprocessed with \<midarrow>)*)
definition leftDualBound::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)"
  where  "leftDualBound \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>A)"                (*cf. leftImage (preprocessed with \<midarrow>)*)

declare rightBound_def[rel_defs] leftBound_def[rel_defs] rightDualBound_def[rel_defs] leftDualBound_def[rel_defs]

notation(input) rightBound ("_-rightBound") and  leftBound ("_-leftBound") and
                rightDualBound ("_-rightDualBound") and  leftDualBound ("_-leftDualBound")

lemma "R-rightBound A = (\<lambda>b. A \<subseteq> R\<^sup>\<smile> b)" unfolding rel_defs func_defs comb_defs ..
lemma "R-leftBound B = (\<lambda>a. B \<subseteq> R a)" unfolding rel_defs func_defs comb_defs ..
lemma "R-rightDualBound A = (\<lambda>b. \<midarrow>(R\<^sup>\<smile> b) \<sqinter> \<midarrow>A)" unfolding rel_defs comb_defs ..
lemma "R-leftDualBound B = (\<lambda>a. \<midarrow>(R a) \<sqinter> \<midarrow>B)" unfolding rel_defs comb_defs ..

lemma "R-rightBound A = (\<lambda>b. \<forall>a. A a \<rightarrow> R a b)" unfolding rel_defs func_defs comb_defs ..
lemma "R-leftBound B = (\<lambda>a. \<forall>b. B b \<rightarrow> R a b)" unfolding rel_defs func_defs comb_defs ..
lemma "R-rightDualBound A = (\<lambda>b. \<exists>a. \<not>R a b \<and> \<not>A a)" unfolding rel_defs func_defs comb_defs ..
lemma "R-leftDualBound B = (\<lambda>a. \<exists>b. \<not>R a b \<and> \<not>B b)" unfolding rel_defs func_defs comb_defs ..

text \<open>Alternative (more insightful?) definitions for dual-bounds.\<close>
lemma rightDualBound_def': "rightDualBound = \<midarrow>\<^sup>r \<circ> (\<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<squnion>) \<^bold>C))" unfolding rel_defs func_defs comb_defs by simp
lemma leftDualBound_def':   "leftDualBound = \<midarrow>\<^sup>r \<circ> (\<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<squnion>) \<^bold>A))" unfolding rel_defs func_defs comb_defs by simp

lemma "R-rightDualBound A = \<midarrow>(\<lambda>b. R\<^sup>\<smile> b \<squnion> A)" unfolding rightDualBound_def' rel_defs func_defs comb_defs ..
lemma  "R-leftDualBound B = \<midarrow>(\<lambda>a. R a \<squnion> B)" unfolding leftDualBound_def' rel_defs func_defs comb_defs ..


text \<open>Convenient characterizations in terms of big-union and big-intersection.\<close>
lemma rightBound_def2: "rightBound = \<Inter> \<circ>\<^sub>2 image"
  unfolding rel_defs func_defs comb_defs by fastforce
lemma leftBound_def2: "leftBound = \<Inter> \<circ>\<^sub>2 (image \<circ> \<smile>)"
  unfolding rel_defs func_defs comb_defs by fastforce
lemma rightDualBound_def2: "rightDualBound = \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 image \<midarrow>\<^sup>r \<midarrow>)"
  unfolding rel_defs func_defs comb_defs by fastforce
lemma leftDualBound_def2: "leftDualBound = \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 image \<sim> \<midarrow>)"
  unfolding rel_defs func_defs comb_defs by fastforce

lemma "R-rightBound A = \<Inter>\<lparr>R A\<rparr>" unfolding rightBound_def2 comb_defs ..
lemma "R-leftBound B = \<Inter>\<lparr>R\<^sup>\<smile> B\<rparr>" unfolding leftBound_def2 comb_defs ..
lemma "R-rightDualBound A = \<Union>\<lparr>R\<^sup>\<midarrow> \<midarrow>A\<rparr>" unfolding rightDualBound_def2 comb_defs ..
lemma "R-leftDualBound B = \<Union>\<lparr>R\<^sup>\<sim> \<midarrow>B\<rparr>" unfolding leftDualBound_def2 comb_defs ..


text \<open>Some particular properties of right and left bounds.\<close>
lemma right_dual_hom: "R-rightBound(\<Union>S) = \<Inter>\<lparr>R-rightBound S\<rparr>" 
  unfolding rel_defs func_defs comb_defs by fastforce
lemma left_dual_hom:   "R-leftBound(\<Union>S) = \<Inter>\<lparr>R-leftBound S\<rparr>" 
  unfolding rel_defs func_defs comb_defs by fastforce 

text \<open>Note, however:\<close>
proposition "R-rightBound(\<Inter>S) = \<Union>\<lparr>R-rightBound S\<rparr>" nitpick \<comment> \<open>countermodel found\<close> oops
proposition  "R-leftBound(\<Inter>S) = \<Union>\<lparr>R-leftBound S\<rparr>" nitpick \<comment> \<open>countermodel found\<close> oops
text \<open>We have, rather:\<close>
lemma "R-rightBound(\<Inter>S) \<supseteq> \<Union>\<lparr>R-rightBound S\<rparr>"
  unfolding rel_defs func_defs comb_defs by fastforce
lemma  "R-leftBound(\<Inter>S) \<supseteq> \<Union>\<lparr>R-leftBound S\<rparr>" 
  unfolding rel_defs func_defs comb_defs by fastforce

text \<open>Clearly, each direction (right/left) uniquely determines the other (its transpose).\<close>
lemma rightBound_defT: "R-rightBound = R\<^sup>\<smile>-leftBound" unfolding rel_defs comb_defs ..
lemma leftBound_defT: "R-leftBound = R\<^sup>\<smile>-rightBound" unfolding rel_defs comb_defs ..
lemma rightBoundDual_defT: "R-rightDualBound = R\<^sup>\<smile>-leftDualBound" unfolding rel_defs comb_defs ..
lemma leftBoundDual_defT: "R-leftDualBound = R\<^sup>\<smile>-rightDualBound" unfolding rel_defs comb_defs ..

text \<open>In fact, there exists a particular "relational duality" between images and bounds, as follows:\<close>
lemma rightImage_dualR: "R-rightImage = (R\<^sup>\<midarrow>-rightBound)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_dualR: "R-leftImage = (R\<^sup>\<midarrow>-leftBound)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualImage_dualR: "R-rightDualImage = (R\<^sup>\<midarrow>-rightDualBound)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_dualR: "R-leftDualImage = (R\<^sup>\<midarrow>-leftDualBound)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_dualR: "R-rightBound = (R\<^sup>\<midarrow>-rightImage)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_dualR: "R-leftBound = (R\<^sup>\<midarrow>-leftImage)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_dualR: "R-rightDualBound = (R\<^sup>\<midarrow>-rightDualImage)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_dualR: "R-leftDualBound = (R\<^sup>\<midarrow>-leftDualImage)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto

text \<open>Finally, ranges can be expressed in terms of images and bounds.\<close>
lemma leftRange_simp: "leftImage R \<UU> = leftRange R" unfolding rel_defs func_defs comb_defs by simp
lemma rightRange_simp: "rightImage R \<UU> = rightRange R" unfolding rel_defs func_defs comb_defs by simp
lemma leftDualRange_simp: "leftBound R \<UU> = leftDualRange R" unfolding rel_defs func_defs comb_defs by simp
lemma rightDualRange_simp: "rightBound R \<UU> = rightDualRange R" unfolding rel_defs func_defs comb_defs by simp

declare leftRange_simp[rel_simps] rightRange_simp[rel_simps] 
        leftDualRange_simp[rel_simps] rightDualRange_simp[rel_simps]


subsection \<open>Type-lifting and Monads\<close>

subsubsection \<open>Set Monad\<close>

text \<open>We can conceive of types of form \<open>Set('a)\<close>, i.e. \<open>'a \<Rightarrow> o\<close>, as arising via an "environmentalization"
 (or "indexation") of the boolean type \<open>o\<close> by the type \<open>'a\<close> (i.e. as an instance of the environment 
 monad discussed previously). Furthermore, we can adopt an alternative perspective and consider a 
 constructor that returns the type of boolean "valuations" (or "classifiers") for objects of type \<open>'a\<close>.
 This type constructor comes with a monad structure too (and is also an applicative and a functor).\<close>

abbreviation(input) unit_set::"'a \<Rightarrow> Set('a)"
  where "unit_set \<equiv> \<Q>"
abbreviation(input) fmap_set::"('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "fmap_set \<equiv> image"
abbreviation(input) join_set::"Set(Set('a)) \<Rightarrow> Set('a)"
  where "join_set \<equiv> \<Union>"
abbreviation(input) ap_set::"Set('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "ap_set \<equiv> rightImage \<circ> intoRel"
abbreviation(input) rbind_set::"('a \<Rightarrow> Set('b)) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "rbind_set \<equiv> rightImage" \<comment> \<open>reversed bind\<close>

text \<open>We define the customary bind operation as "flipped" \<open>rbind\<close> (which seems more intuitive).\<close>
abbreviation bind_set::"Set('a) \<Rightarrow> ('a \<Rightarrow> Set('b)) \<Rightarrow> Set('b)"
  where "bind_set \<equiv> \<^bold>C rbind_set"

text \<open>Some properties of monads in general.\<close>
lemma "rbind_set = join_set \<circ>\<^sub>2 fmap_set" unfolding rel_defs func_defs comb_defs by metis
lemma "join_set = rbind_set \<^bold>I" unfolding rel_defs func_defs comb_defs by metis
\<comment> \<open>... and so on\<close>

text \<open>Some properties of this particular monad.\<close>
lemma "ap_set = \<Union>\<^sup>r \<circ> (image image)" unfolding rel_defs func_defs comb_defs by blast
\<comment> \<open>... and so on\<close>

text \<open>Verifies compliance with the monad laws.\<close>
lemma "monadLaw1 unit_set bind_set" unfolding rel_defs func_defs comb_defs by simp
lemma "monadLaw2 unit_set bind_set" unfolding rel_defs func_defs comb_defs by simp
lemma "monadLaw3 bind_set" unfolding rel_defs func_defs comb_defs by auto


subsubsection \<open>Relation Monad\<close>

text \<open>In fact, the \<open>Rel('a,'b)\<close> type constructor also comes with a monad structure, which can be seen as 
 a kind of "monad composition" of the environment monad with the set monad.\<close>

abbreviation(input) unit_rel::"'a \<Rightarrow> Rel('b,'a)"
  where "unit_rel \<equiv> \<^bold>K \<circ> \<Q>"
abbreviation(input) fmap_rel::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "fmap_rel \<equiv> \<^bold>B \<circ> image"
abbreviation(input) join_rel::"Rel('c,Rel('c,'a)) \<Rightarrow> Rel('c,'a)"
  where "join_rel \<equiv> \<^bold>W \<circ> (\<^bold>B \<Union>\<^sup>r)"
abbreviation(input) ap_rel::"Rel('c, 'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "ap_rel \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (rightImage \<circ> intoRel)"
abbreviation(input) rbind_rel::"('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "rbind_rel \<equiv> (\<^bold>\<Phi>\<^sub>2\<^sub>1 rightImage) \<circ> \<^bold>C" \<comment> \<open>reversed bind\<close>

text \<open>Again, we define the bind operation as "flipped" rbind\<close>
abbreviation bind_rel::"Rel('c,'a) \<Rightarrow> ('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'b)"
  where "bind_rel \<equiv> \<^bold>C rbind_rel"

text \<open>Some properties of monads in general.\<close>
lemma "rbind_rel = join_rel \<circ>\<^sub>2 fmap_rel" unfolding rel_defs func_defs comb_defs by metis
lemma "join_rel = rbind_rel \<^bold>I" unfolding rel_defs func_defs comb_defs by metis
\<comment> \<open>... and so on\<close>

text \<open>Note that for the relation monad we have:\<close>
lemma "unit_rel = \<^bold>B unit_env unit_set" ..
lemma "fmap_rel = \<^bold>B fmap_env fmap_set" ..
lemma "ap_rel = \<^bold>\<Phi>\<^sub>2\<^sub>1 ap_set" ..
lemma "rbind_rel = \<^bold>B (\<^bold>C \<^bold>B \<^bold>C) \<^bold>\<Phi>\<^sub>2\<^sub>1 rbind_set" unfolding comb_defs ..
\<comment> \<open>... and so on\<close>

text \<open>Finally, verify compliance with the monad laws.\<close>
lemma "monadLaw1 unit_rel bind_rel" unfolding rel_defs func_defs comb_defs by simp
lemma "monadLaw2 unit_rel bind_rel" unfolding rel_defs func_defs comb_defs by simp
lemma "monadLaw3 bind_rel" unfolding rel_defs func_defs comb_defs by auto

end