theory rels (* A basic theory of relations (qua set-valued functions) *)
imports sets funcs
begin

section \<open>Relations\<close>

(*Relations inherit the structures of both sets and functions and enrich them in manifold ways.*)

named_theorems rel_defs  (*container for related definitions*)
named_theorems rel_simps (*container for related simplification rules*)


subsection \<open>Set-like structure\<close>

(*Analogously to sets, we define that a given relation holds of all, resp. at least one, pair or elements.*)
abbreviation(input) AllR::"Set(Rel('a,'b))" ("\<forall>\<^sup>r") 
  where "\<forall>\<^sup>rR \<equiv> \<forall>a b. R a b" (*i.e. \<forall>a. \<forall>(R a) resp. \<forall>(\<forall>\<circ>R) resp. \<^bold>B\<forall>(\<^bold>B\<forall>)*)
abbreviation(input) ExR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r")
  where "\<exists>\<^sup>rR \<equiv> \<exists>a b. R a b" (*i.e. \<exists>a. \<exists>(R a) resp. \<exists>(\<exists>\<circ>R) resp. \<^bold>B\<exists>(\<^bold>B\<exists>)*)

abbreviation NotExR::"Set(Rel('a,'b))" ("\<nexists>\<^sup>r") (*for convenience*)
  where "\<nexists>\<^sup>rR \<equiv> \<not>\<exists>\<^sup>rR"


subsubsection \<open>Boolean operations\<close>
(*As we have seen, (curried) relations correspond to indexed families of sets. 
  It is thus not surprising that they inherit their Boolean algebra structure.*)

definition univR::"Rel('a,'b)" ("\<UU>\<^sup>r")
  where "\<UU>\<^sup>r \<equiv> \<^bold>K \<UU>" (* the universal relation *)
definition emptyR::"Rel('a,'b)" ("\<emptyset>\<^sup>r")
  where "\<emptyset>\<^sup>r \<equiv> \<^bold>K \<emptyset>"  (* the empty relation *)
definition complR::"EOp(Rel('a,'b))" ("\<midarrow>\<^sup>r") 
  where \<open>\<midarrow>\<^sup>r \<equiv> \<^bold>B(\<midarrow>)\<close> (* relation complement *)
definition interR::"EOp\<^sub>2(Rel('a,'b))" (infixl "\<inter>\<^sup>r" 54) 
  where "(\<inter>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<inter>)" (* relation intersection *)
definition unionR::"EOp\<^sub>2(Rel('a,'b))" (infixl "\<union>\<^sup>r" 53) 
  where "(\<union>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<union>)" (* relation union *)
definition diffR:: "EOp\<^sub>2(Rel('a,'b))" (infixl "\<setminus>\<^sup>r" 51) 
  where "(\<setminus>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<setminus>)" (* relation difference *)
definition implR::"EOp\<^sub>2(Rel('a,'b))" (infixr "\<Rightarrow>\<^sup>r" 51) 
  where "(\<Rightarrow>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<Rightarrow>)" (* relation implication *)
definition dimplR::"EOp\<^sub>2(Rel('a,'b))" (infix "\<Leftrightarrow>\<^sup>r" 51) 
  where "(\<Leftrightarrow>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<Leftrightarrow>)" (* relation double-implication *)
definition sdiffR::"EOp\<^sub>2(Rel('a,'b))" (infix "\<triangle>\<^sup>r" 51) 
  where "(\<triangle>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1(\<triangle>)" (* relation symmetric difference (aka. xor) *)

(*Let's put rel-related definitions in the "rel_defs" bag *)
declare univR_def[rel_defs] emptyR_def[rel_defs]
        complR_def[rel_defs] interR_def[rel_defs] unionR_def[rel_defs]
        implR_def[rel_defs] dimplR_def[rel_defs] diffR_def[rel_defs] sdiffR_def[rel_defs]

notation (input) complR ("(_)\<^sup>\<midarrow>") (* alternative superscript notation common in the literature *)
notation(output) complR ("'(_')\<^sup>\<midarrow>")

(*Set-based definitions*)
lemma "\<UU>\<^sup>r = (\<lambda>x. \<UU>)" unfolding rel_defs comb_defs ..
lemma "\<emptyset>\<^sup>r = (\<lambda>x. \<emptyset>)" unfolding rel_defs comb_defs ..
lemma "\<midarrow>\<^sup>rR = (\<lambda>x. \<midarrow>(R x))" unfolding rel_defs comb_defs ..
lemma "R \<inter>\<^sup>r T = (\<lambda>x. R x \<inter> T x)" unfolding rel_defs comb_defs ..
lemma "R \<union>\<^sup>r T = (\<lambda>x. R x \<union> T x)" unfolding rel_defs comb_defs ..
lemma "R \<setminus>\<^sup>r T = (\<lambda>x. R x \<setminus> T x)" unfolding rel_defs comb_defs ..
lemma "R \<Rightarrow>\<^sup>r T = (\<lambda>x. R x \<Rightarrow> T x)" unfolding rel_defs comb_defs ..
lemma "R \<Leftrightarrow>\<^sup>r T = (\<lambda>x. R x \<Leftrightarrow> T x)" unfolding rel_defs comb_defs ..
lemma "R \<triangle>\<^sup>r T = (\<lambda>x. R x \<triangle> T x)" unfolding rel_defs comb_defs ..

(*Point-based definitions*)
lemma "\<UU>\<^sup>r = (\<lambda>x y. True)" unfolding rel_defs set_defs comb_defs ..
lemma "\<emptyset>\<^sup>r = (\<lambda>x y. False)" unfolding rel_defs set_defs comb_defs ..
lemma "\<midarrow>\<^sup>rR = (\<lambda>x y. \<not>R x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<inter>\<^sup>r T = (\<lambda>x y. R x y \<and> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<union>\<^sup>r T = (\<lambda>x y. R x y \<or> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<setminus>\<^sup>r T = (\<lambda>x y. R x y \<leftharpoondown> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<Rightarrow>\<^sup>r T = (\<lambda>x y. R x y \<rightarrow> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<Leftrightarrow>\<^sup>r T = (\<lambda>x y. R x y \<leftrightarrow> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<triangle>\<^sup>r T = (\<lambda>x y. R x y \<rightleftharpoons> T x y)" unfolding rel_defs set_defs comb_defs ..

(*We can also generalize union and intersection to the infinitary case*)
definition biginterR::"EOp\<^sub>G(Rel('a,'b))" ("\<Inter>\<^sup>r") 
  where "\<Inter>\<^sup>r \<equiv> \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>0 image \<^bold>T)"
definition bigunionR::"EOp\<^sub>G(Rel('a,'b))" ("\<Union>\<^sup>r")
  where "\<Union>\<^sup>r \<equiv> \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>0 image \<^bold>T)"

declare biginterR_def[rel_defs] bigunionR_def[rel_defs]

lemma "\<Inter>\<^sup>rS a = \<Inter>\<lparr>(\<lambda>R. R a) S\<rparr>" unfolding rel_defs func_defs set_defs comb_defs ..
lemma "\<Union>\<^sup>rS a = \<Union>\<lparr>(\<lambda>R. R a) S\<rparr>" unfolding rel_defs func_defs set_defs comb_defs ..

(*Alternative definitions in terms of quantifiers directly*)
lemma biginterR_def2: "\<Inter>\<^sup>rS = (\<lambda>a b. \<forall>R. S R \<rightarrow> R a b)" 
  unfolding rel_defs set_defs func_defs comb_defs by metis
lemma bigunionR_def2: "\<Union>\<^sup>rS = (\<lambda>a b. \<exists>R. S R \<and> R a b)" 
  unfolding rel_defs set_defs func_defs comb_defs by metis


subsubsection \<open>Ordering structure\<close>
(*Similarly, relations also inherit the ordering structure of sets.*)

(*Analogously to the notion of 'equalizer' of two functions, we have the 'orderer' or two relations:*)
definition orderer::"Rel('a,'b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('a)" (infixr "\<sqsubseteq>" 51) 
  where "(\<sqsubseteq>) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<subseteq>)"

lemma "R \<sqsubseteq> T = (\<lambda>x. R x \<subseteq> T x)" unfolding orderer_def comb_defs ..

(*Relations are analogously ordered as sets, via the 'subrelation' (endo)relation.*)
definition subrel::"ERel(Rel('a,'b))" (infixr "\<subseteq>\<^sup>r" 51) 
  where "(\<subseteq>\<^sup>r) \<equiv>  \<forall> \<circ>\<^sub>2 (\<sqsubseteq>)"

declare orderer_def[rel_defs] subrel_def[rel_defs] 

lemma subrel_setdef: "R \<subseteq>\<^sup>r T = (\<forall>x. R x \<subseteq> T x)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<subseteq>\<^sup>r T = (\<forall>x y. R x y \<rightarrow> T x y)" unfolding rel_defs set_defs comb_defs ..

lemma subrel_def2: "(\<subseteq>\<^sup>r) = \<forall>\<^sup>r \<circ>\<^sub>2 (\<Rightarrow>\<^sup>r)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<subseteq>\<^sup>r T = \<forall>\<^sup>r(R \<Rightarrow>\<^sup>r T)" unfolding rel_defs set_defs comb_defs ..

(*Subrelation is antisymmetric, as expected*)
lemma subrel_antisymm: "R \<subseteq>\<^sup>r T \<Longrightarrow> T \<subseteq>\<^sup>r R \<Longrightarrow> R = T" unfolding rel_defs set_defs comb_defs by blast


abbreviation(input) superrel::"ERel(Rel('a,'b))" (infixr "\<supseteq>\<^sup>r" 51) (*convenient notation*)
  where "A \<supseteq>\<^sup>r B \<equiv> B \<subseteq>\<^sup>r A" 

(* The "power-relation" operation corresponds to the (partial) application of superrel *)
notation superrel ("\<wp>\<^sup>r")
lemma "\<wp>\<^sup>rA = (\<lambda>B. B \<subseteq>\<^sup>r A)" unfolding comb_defs ..

(*Two relations are said to 'overlap' (or 'intersect') if their intersection is non-empty*)
definition overlapR::"ERel(Rel('a,'b))" (infix "\<sqinter>\<^sup>r" 52)
  where "(\<sqinter>\<^sup>r) \<equiv> \<exists>\<^sup>r \<circ>\<^sub>2 (\<inter>\<^sup>r)"
(*dually, two relations form a 'cover' if every pair belongs to one or the other *)
definition coverR::"ERel(Rel('a,'b))" (infix "\<squnion>\<^sup>r" 53)
  where "(\<squnion>\<^sup>r) \<equiv> \<forall>\<^sup>r \<circ>\<^sub>2 (\<union>\<^sup>r)"
(*Two relations are said to be 'incompatible' if their intersection is empty*)
definition incompatR::"ERel(Rel('a,'b))" (infix "\<bottom>\<^sup>r" 52)
  where "(\<bottom>\<^sup>r) \<equiv> \<nexists>\<^sup>r \<circ>\<^sub>2 (\<inter>\<^sup>r)"

declare incompatR_def[rel_defs] overlapR_def[rel_defs] coverR_def[rel_defs]

lemma "A \<sqinter>\<^sup>r B = \<exists>\<^sup>r(A \<inter>\<^sup>r B)" unfolding rel_defs comb_defs ..
lemma "A \<sqinter>\<^sup>r B = (\<exists>x. A x \<sqinter> B x)" unfolding rel_defs set_defs comb_defs ..
lemma "A \<sqinter>\<^sup>r B = (\<exists>x y. (A x y \<and> B x y))" unfolding rel_defs set_defs comb_defs ..

lemma "A \<squnion>\<^sup>r B = \<forall>\<^sup>r(A \<union>\<^sup>r B)" unfolding rel_defs comb_defs ..
lemma "A \<squnion>\<^sup>r B = (\<forall>x. A x \<squnion> B x)" unfolding rel_defs set_defs comb_defs ..
lemma "A \<squnion>\<^sup>r B = (\<forall>x y. A x y \<or> B x y)" unfolding rel_defs set_defs comb_defs ..

lemma "A \<bottom>\<^sup>r B = \<nexists>\<^sup>r(A \<inter>\<^sup>r B)" unfolding rel_defs comb_defs ..
lemma "A \<bottom>\<^sup>r B = (\<nexists>x y. A x y \<and> B x y)" unfolding rel_defs set_defs comb_defs ..
lemma "A \<bottom>\<^sup>r B = (\<not>(A \<sqinter>\<^sup>r B))" unfolding rel_defs comb_defs ..


definition psubrel::"ERel(Rel('a,'b))" (infixr "\<subset>\<^sup>r" 51) (*proper subrelation*)
  where "(\<subset>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>2 (\<leftharpoondown>) (\<subseteq>\<^sup>r) (\<supseteq>\<^sup>r)"

declare psubrel_def[rel_defs]

lemma "R \<subset>\<^sup>r T = (R \<subseteq>\<^sup>r T \<and> \<exists>\<^sup>r(T \<setminus>\<^sup>r R))" unfolding rel_defs set_defs comb_defs by simp
lemma "R \<subset>\<^sup>r T = (R \<subseteq>\<^sup>r T \<leftharpoondown> (T \<subseteq>\<^sup>r R))" unfolding rel_defs set_defs comb_defs ..

(*Note, however, that the following does not hold*)
lemma "R \<subset>\<^sup>r T \<longrightarrow> (\<forall>a. R a \<subset> T a)" nitpick oops (*countermodel*)
(*Only this holds:*)
lemma psubrel_prop1: "(\<forall>a. R a \<subset> T a) \<longrightarrow> R \<subset>\<^sup>r T" 
  unfolding rel_defs unfolding set_defs comb_defs by simp

abbreviation(input) psuperrel::"ERel(Rel('a,'b))" (infixr "\<supset>\<^sup>r" 51) (*proper superset*)
  where "A \<supset>\<^sup>r B \<equiv> B \<subset>\<^sup>r A" 

(*We say of a set of relations that it 'overlaps' (or 'intersects') if there exists a 'shared' pair.*)
abbreviation(input) bigoverlapR::"Set(Set(Rel('a,'b)))" ("\<Sqinter>\<^sup>r")
  where "\<Sqinter>\<^sup>r \<equiv> \<exists>\<^sup>r \<circ> \<Inter>\<^sup>r"
(*dually, a set of relations forms a 'cover' if every pair is contained in at least one of the relations.*)
abbreviation(input) bigcoverR::"Set(Set(Rel('a,'b)))" ("\<Squnion>\<^sup>r")
  where "\<Squnion>\<^sup>r \<equiv> \<forall>\<^sup>r \<circ> \<Union>\<^sup>r"

lemma "\<Sqinter>\<^sup>rS = \<exists>\<^sup>r(\<Inter>\<^sup>rS)" unfolding comb_defs ..
lemma "\<Squnion>\<^sup>rS = \<forall>\<^sup>r(\<Union>\<^sup>rS)" unfolding comb_defs ..


subsection \<open>Constructing relations\<close>

subsubsection \<open>Pairs and Copairs\<close>
(*A (co)atomic-like relation can be constructed out of two elements*)

definition pair::"'a \<Rightarrow> 'b \<Rightarrow> Rel('a,'b)" ("\<langle>_,_\<rangle>")
  where \<open>pair \<equiv> \<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<and>) \<Q> \<Q>\<close> (*relational counterpart of 'singleton'*)
definition copair::"'a \<Rightarrow> 'b \<Rightarrow> Rel('a,'b)" ("\<lblot>_,_\<rblot>")
  where \<open>copair \<equiv> \<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<or>) \<D> \<D>\<close> (*relational counterpart of 'cosingleton'*)

declare pair_def[rel_defs] copair_def[rel_defs]

lemma "\<langle>a,b\<rangle> = (\<lambda>x y. a = x \<and> b = y)" unfolding rel_defs comb_defs ..
lemma "\<lblot>a,b\<rblot> = (\<lambda>x y. a \<noteq> x \<or> b \<noteq> y)" unfolding rel_defs comb_defs ..

(*Pairs and copairs are related via relation-complement as expected*)
lemma "\<midarrow>\<^sup>r\<lblot>a,b\<rblot> = \<langle>a,b\<rangle>" unfolding rel_defs set_defs comb_defs by simp

(*We conveniently extrapolate the definitions of unique/singleton from sets to relations*)
definition uniqueR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r\<^sub>\<le>\<^sub>1") (* R holds of at most one pair of elements (R may hold of none)*)
  where \<open>\<exists>\<^sup>r\<^sub>\<le>\<^sub>1 R \<equiv> \<forall>a b x y. (R a b \<and> R x y) \<rightarrow> (a = x \<and> b = y)\<close>
definition singletonR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r\<^sub>1") (* R holds of exactly one pair of elements, i.e. R is a 'singleton relation'*)
  where \<open>\<exists>\<^sup>r\<^sub>1 R \<equiv> \<exists>x y. R x y \<and> (\<forall>a b. R a b \<rightarrow> (a = x \<and> b = y))\<close>

declare uniqueR_def[rel_defs] singletonR_def[rel_defs]

lemma uniqueR_def2: "\<exists>\<^sup>r\<^sub>\<le>\<^sub>1 = \<nexists>\<^sup>r \<union> \<exists>\<^sup>r\<^sub>1" unfolding rel_defs set_defs comb_defs by blast
lemma singletonR_def2: "\<exists>\<^sup>r\<^sub>1 = \<exists>\<^sup>r \<inter> \<exists>\<^sup>r\<^sub>\<le>\<^sub>1" unfolding rel_defs set_defs comb_defs apply (rule ext) by blast

(*Clearly, pairs correspond one-to-one to "singleton relations" *)
lemma pair_singletonR: "\<exists>\<^sup>r\<^sub>1 \<langle>a,b\<rangle>" unfolding rel_defs comb_defs by simp
lemma singletonR_def3: "\<exists>\<^sup>r\<^sub>1 R = (\<exists>a b. R = \<langle>a,b\<rangle>)" unfolding rel_defs comb_defs by metis

(*Any given relation R can be (join) generated by its singleton (pair) subrelations*)
lemma singletonR_gen: "R = \<Union>\<^sup>r(singletonR \<inter> (\<supseteq>\<^sup>r) R)"  
  unfolding bigunionR_def2 singletonR_def3 unfolding rel_defs set_defs comb_defs apply (rule ext) by auto


subsubsection \<open>Product and Sum\<close>
(*Relations can also be constructed out of pairs of sets, via (cartesian) product and (disjoint) sum*)

definition product::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<times>" 90)
  where "(\<times>) \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<and>)"
definition sum::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<uplus>" 90)
  where "(\<uplus>) \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<or>)"

declare product_def[rel_defs] sum_def[rel_defs]

lemma "A \<times> B = (\<lambda>x y. A x \<and> B y)" unfolding rel_defs comb_defs ..
lemma "A \<uplus> B = (\<lambda>x y. A x \<or> B y)" unfolding rel_defs comb_defs ..

(*Product and sum satisfy the corresponding deMorgan duality*)
lemma "\<midarrow>\<^sup>r(A \<times> B) = \<midarrow>A \<uplus> \<midarrow>B" unfolding rel_defs set_defs comb_defs by simp
lemma "\<midarrow>\<^sup>r(A \<uplus> B) = \<midarrow>A \<times> \<midarrow>B" unfolding rel_defs set_defs comb_defs by simp

(*Pair and copair can be defined in terms of product and sum respectively*)
lemma "\<langle>a,b\<rangle> = {a} \<times> {b}" unfolding rel_defs comb_defs ..
lemma "\<lblot>a,b\<rblot> = \<lbrace>a\<rbrace> \<uplus> \<lbrace>b\<rbrace>" unfolding rel_defs comb_defs ..


subsection \<open>Function-like properties\<close>

(*We have seen the shared (boolean) algebraic structure between sets and relations. 
 We now explore their shared structure with functions.*)

(*We start by noting that, given a relation R of type Rel('a,'b), we refer to the semantic domain of 
 type 'a as R's "source" domain, which is identical to R's domain when seen as a (set-valued) function. 
 Analogously, we refer to the semantic domain for type 'b as R's "target" domain, which is in fact
 different from its codomain when seen as a (set-valued) function (corresponding to the type 'b \<Rightarrow> o). *)


subsubsection \<open>Ranges and deterministic elements\<close>
(*We define the left- (right-) range of a relation as the set of those objects in the source (target)
 domain that reach to (are reached by) some element in the target (source) domain*)

definition leftRange::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "leftRange \<equiv> \<exists> \<circ>\<^sub>2 \<^bold>I"
definition rightRange::"Rel('a,'b) \<Rightarrow> Set('b)"
  where "rightRange \<equiv> \<exists> \<circ>\<^sub>2 \<^bold>C"

lemma "leftRange R a = (\<exists>x. R a x)" unfolding leftRange_def comb_defs ..
lemma "rightRange R b = (\<exists>x. R x b)" unfolding rightRange_def comb_defs ..


(*Dually, the left- (right-) dual-range of a relation is the set of those objects in the source (target)
 domain that reach to (are reached by) all elements in the target (source) domain*)
definition leftDualRange::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "leftDualRange \<equiv> \<forall> \<circ>\<^sub>2 \<^bold>I"
definition rightDualRange::"Rel('a,'b) \<Rightarrow> Set('b)"
  where "rightDualRange \<equiv> \<forall> \<circ>\<^sub>2 \<^bold>C"

lemma "leftDualRange R a = (\<forall>x. R a x)" unfolding leftDualRange_def comb_defs ..
lemma "rightDualRange R b = (\<forall>x. R x b)" unfolding rightDualRange_def comb_defs ..

declare leftRange_def[rel_defs] rightRange_def[rel_defs]
        leftDualRange_def[rel_defs] rightDualRange_def[rel_defs]

(*Both pairs of definitions are 'dual' wrt. complement *)
lemma "rightDualRange R = \<midarrow>(rightRange R\<^sup>\<midarrow>)" unfolding rel_defs set_defs comb_defs by simp
lemma "leftDualRange R = \<midarrow>(leftRange R\<^sup>\<midarrow>)" unfolding rel_defs set_defs comb_defs by simp

(*For the left we have in fact that ranges are obtained directly by composition with \<exists> and \<forall> *)
lemma leftRange_def2: "leftRange = \<^bold>B \<exists>" unfolding rel_defs comb_defs ..
lemma leftDualRange_def2: "leftDualRange = \<^bold>B \<forall>" unfolding rel_defs comb_defs ..


(*Similarly, by composition with \<exists>\<^sub>\<le>\<^sub>1, we obtain the set of deterministic (or 'univalent') elements.
 They get assigned at most one value under the relation (which then behaves deterministically on them)*)
definition deterministic::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "deterministic \<equiv> \<^bold>B \<exists>\<^sub>\<le>\<^sub>1"

(*Also, by composition with \<exists>\<^sub>1, we obtain the set of total(ly) deterministic elements. 
 They get assigned precisely one value under the relation (which then behaves as a function on them)*)
definition totalDeterministic::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "totalDeterministic \<equiv> \<^bold>B \<exists>\<^sub>1"

declare deterministic_def[rel_defs] totalDeterministic_def[rel_defs]

lemma totalDeterministic_def2: "totalDeterministic R = deterministic R \<inter> leftRange R" 
  unfolding rel_defs set_defs comb_defs by (metis (mono_tags, opaque_lifting))


subsubsection \<open>Uniqueness properties\<close>

definition rightUnique::"Set(Rel('a,'b))" (*aka. univalent, (partial-)functional *)
  where "rightUnique \<equiv> \<forall> \<circ> deterministic"
definition leftUnique::"Set(Rel('a,'b))" (*aka. injective*)
  where "leftUnique \<equiv> \<forall> \<circ> deterministic \<circ> \<^bold>C"

declare rightUnique_def [rel_defs] leftUnique_def [rel_defs]

(*Further names for special kinds of relations*)
abbreviation(input)   "one_to_one R \<equiv>  leftUnique R \<and>  rightUnique R" (*injective and functional*)
abbreviation(input)  "one_to_many R \<equiv>  leftUnique R \<and> \<not>rightUnique R" (*injective and not functional*)
abbreviation(input) " many_to_one R \<equiv> \<not>leftUnique R \<and>  rightUnique R" (*functional and not injective*)
abbreviation(input) "many_to_many R \<equiv> \<not>leftUnique R \<and> \<not>rightUnique R" (*neither injective nor functional*)

(*Pairs are both right-unique and left-unique, i.e. one-to-one*)
lemma "singletonR \<subseteq> one_to_one" unfolding rel_defs set_defs comb_defs by auto
lemma "one_to_one \<subseteq> singletonR" nitpick oops (*counterexample: e.g. empty relation*)

(*In fact, any relation can also be generated by its right- resp. left-unique subrelations*)
lemma rightUnique_gen: "R = \<Union>\<^sup>r(rightUnique \<inter> \<wp>\<^sup>r R)" 
 unfolding bigunionR_def2 unfolding rel_defs set_defs comb_defs apply simp sorry (*reconstruction fails*)
lemma leftUnique_gen: "R \<subseteq>\<^sup>r \<Union>\<^sup>r(leftUnique \<inter> \<wp>\<^sup>r R)" 
  unfolding bigunionR_def2 unfolding rel_defs set_defs comb_defs apply simp sorry (*reconstruction fails*)


subsubsection \<open>Totality properties\<close>

definition rightTotal::"Set(Rel('a,'b))" (*aka. surjective*)
  where "rightTotal \<equiv> \<forall> \<circ> rightRange"
definition leftTotal::"Set(Rel('a,'b))" (*aka. total, serial, multi-function*)
  where "leftTotal \<equiv> \<forall> \<circ> leftRange"

declare rightTotal_def[rel_defs] leftTotal_def[rel_defs]

(*A relation that relates each element in its source to precisely one element in its target 
 corresponds to a (total) function. They can also be characterized as being both total and functional
 (i.e. left-total and right-unique) relations*)
definition totalFunction::"Set(Rel('a,'b))"
  where "totalFunction \<equiv> \<forall> \<circ> totalDeterministic"

declare totalFunction_def[rel_defs]

lemma totalFunction_def2: "totalFunction R = (leftTotal R \<and> rightUnique R)"
  unfolding rel_defs set_defs comb_defs by metis

(*The inverse of a function (qua relation) is always left-unique and right-total*)
lemma "leftUnique f\<inverse>" unfolding rel_defs func_defs set_defs comb_defs by simp
lemma "rightTotal f\<inverse>" unfolding rel_defs func_defs set_defs comb_defs by simp


subsection \<open>Birectional transformations between relations and (sets of) functions\<close>

subsubsection \<open>From (sets of) functions to relations\<close>

(*A given function can be disguised as a relation*)
definition asRel::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" ("asRel")
  where "asRel \<equiv> \<^bold>B \<Q>"

declare asRel_def[rel_defs]

lemma "asRel f = \<Q> \<circ> f" unfolding rel_defs ..
lemma "asRel f = (\<lambda>a. \<Q> (f a))" unfolding rel_defs comb_defs ..
lemma "asRel f = (\<lambda>a. (\<lambda>b. \<Q> (f a) b))" unfolding rel_defs comb_defs ..
lemma "asRel f = (\<lambda>a b. f a = b)" unfolding rel_defs comb_defs ..

(*Alternative characterization*)
lemma asRel_def2: "asRel = \<^bold>C \<circ> inverse" unfolding rel_defs func_defs comb_defs ..
lemma "asRel f = (f\<inverse>)\<Zcat>" unfolding asRel_def2 comb_defs ..

(*Relations corresponding to lifted functions are always left-total and right-unique (i.e. functions) *)
lemma "totalFunction (asRel f)" unfolding rel_defs set_defs comb_defs by simp


(*A given set of functions can be transformed (or 'aggregated') into a relation*)
definition intoRel::"Set('a \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" ("intoRel")
  where "intoRel \<equiv> (image \<circ> \<^bold>T)\<Zcat>"

declare intoRel_def[rel_defs]

lemma "intoRel = (\<lambda>S a. \<lparr>(\<^bold>T a) S\<rparr>)" unfolding rel_defs comb_defs ..
lemma "intoRel S a = \<lparr>(\<lambda>f. f a) S\<rparr>" unfolding rel_defs comb_defs ..

(*Alternative characterization (in terms of relational bigunion)*)
lemma intoRel_def2: "intoRel = \<Union>\<^sup>r \<circ> (image asRel)" unfolding rel_defs set_defs func_defs comb_defs by blast
lemma "intoRel S = \<Union>\<^sup>r\<lparr>asRel S\<rparr>" unfolding intoRel_def2 comb_defs ..


subsubsection \<open>From relations to (sets of) functions\<close>

(*A given relation can be disguised as a function (and go unnoticed under certain circumstances) *)
definition asFun::"Rel('a,'b) \<Rightarrow> ('a \<Rightarrow> 'b)" ("asFun")
  where "asFun \<equiv> \<^bold>B \<epsilon>"

declare asFun_def[rel_defs] 

lemma "asFun R = \<epsilon> \<circ> R" unfolding rel_defs ..
lemma "asFun R = (\<lambda>a. \<epsilon>(R a))" unfolding rel_defs comb_defs ..
lemma "asFun R = (\<lambda>a. \<epsilon> b. R a b)" unfolding rel_defs comb_defs ..

lemma asFun_def2: "totalFunction R \<Longrightarrow> asFun R = \<iota> \<circ> R" (*alternative definition for total functions*)
  unfolding rel_defs set_defs comb_defs apply (rule ext)+ by (metis Uniq_I someI the1_equality')


(* Transforming (or 'decomposing') a given relation into a set of functions *)
definition intoFunSet::"Rel('a,'b) \<Rightarrow> Set('a \<Rightarrow> 'b)" ("intoFunSet")
  where "intoFunSet \<equiv> ((\<subseteq>\<^sup>r) \<circ> asRel)\<Zcat>"

declare intoFunSet_def[rel_defs] 

lemma "intoFunSet R = (\<lambda>f. asRel f \<subseteq>\<^sup>r R)" unfolding rel_defs comb_defs ..
lemma "intoFunSet R = (\<lambda>f. \<forall>a b. f a = b \<rightarrow> R a b)" unfolding rel_defs set_defs comb_defs ..
(*Another perspective:*)
lemma intoFunSet_def2: "intoFunSet = \<^bold>B\<^sub>2\<^sub>1\<^sub>1 \<wp>\<^sup>r \<^bold>I asRel" unfolding rel_defs set_defs comb_defs ..


subsubsection \<open>Back and forth translation conditions\<close> (*TODO: make simplification rules out of this*)

(*Disguising a function as a relation, and back as a function, gives back the original function*)
lemma "asFun (asRel f) = f" unfolding rel_defs comb_defs by simp 

(*However, disguising a relation as a function, and back as a relation, does not give anything recognizable*)
lemma "asRel (asFun R) = R" nitpick oops (*counterexample*)

(*In case of left-total relations, what we get back is a strict subrelation*)
lemma "leftTotal R \<Longrightarrow> asRel (asFun R) \<subseteq>\<^sup>r R" unfolding rel_defs set_defs comb_defs by (metis someI)
lemma "leftTotal R \<Longrightarrow> R \<subseteq>\<^sup>r asRel (asFun R)" nitpick oops (*counterexample*)

(*In case of right-unique relations, what we get back is a strict superrelation*)
lemma "rightUnique R \<Longrightarrow> R \<subseteq>\<^sup>r asRel (asFun R)" unfolding rel_defs set_defs comb_defs by auto
lemma "rightUnique R \<Longrightarrow> asRel (asFun R) \<subseteq>\<^sup>r R" nitpick oops (*counterexample*)

(*Indeed, we get back the original relation when it is a total-function *)
lemma "totalFunction R \<Longrightarrow> asRel (asFun R) = R" 
  unfolding asFun_def2 unfolding rel_defs set_defs comb_defs apply (rule ext)+ by (metis the_equality)


(*Transforming a set of functions into a relation, and back to a set of functions, gives a strict superset*)
lemma "S \<subseteq> intoFunSet (intoRel S)" unfolding rel_defs set_defs func_defs comb_defs by auto
lemma "intoFunSet (intoRel S) \<subseteq> S" nitpick oops (*counterexample*)

(*We get the original set in those cases where it corresponds already to a transformed relation*)
lemma "let S = intoFunSet R in intoFunSet (intoRel S) \<subseteq> S" unfolding rel_defs set_defs func_defs comb_defs by metis

(*Transforming a relation into a set of functions, and back to a relation, gives a strict subrelation*)
lemma relFunSet_eq1: "intoRel (intoFunSet R) \<subseteq>\<^sup>r R" unfolding rel_defs func_defs set_defs comb_defs by blast
lemma "R \<subseteq>\<^sup>r intoRel (intoFunSet R)" nitpick oops (*counterexample*)

(*In fact, we get the original relation in case it is left-total*)
lemma leftTotal_auxsimp: "leftTotal R \<Longrightarrow> R a b = (let f = (asFun R)[a \<mapsto> b] in (f a = b \<and> (asRel f) \<subseteq>\<^sup>r R))"
  unfolding func_defs rel_defs set_defs comb_defs by (metis (full_types) some_eq_imp)
lemma relFunSet_eq2: "leftTotal R \<Longrightarrow> R \<subseteq>\<^sup>r intoRel (intoFunSet R)"
  unfolding subrel_def orderer_def unfolding intoRel_def intoFunSet_def unfolding set_defs func_defs comb_defs by (meson leftTotal_auxsimp)
lemma relFunSet_simp: "leftTotal R \<Longrightarrow> R = intoRel (intoFunSet R)"
  apply (rule ext)+ using relFunSet_eq1 relFunSet_eq2 by (metis subrel_antisymm)


subsection \<open>Function-like algebraic structure\<close>

subsubsection \<open>Monoidal structure (relation-composition and its dual)\<close>

(*Analogously to functions, relations can also be composed. We introduce 'relation-composition' below*)
definition relComp::"Rel('a,'b) \<Rightarrow> Rel('b,'c) \<Rightarrow>  Rel('a,'c)" (infixr ";\<^sup>r" 55)
 where "(;\<^sup>r) = \<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<sqinter>) \<^bold>I \<^bold>C"

lemma "R\<^sub>1 ;\<^sup>r R\<^sub>2 = (\<lambda>a b. R\<^sub>1 a \<sqinter> R\<^sub>2\<Zcat> b)" 
  unfolding relComp_def set_defs comb_defs ..
lemma "R\<^sub>1 ;\<^sup>r R\<^sub>2 = (\<lambda>a b. \<exists>c. R\<^sub>1 a c \<and> R\<^sub>2 c b)"
  unfolding relComp_def rel_defs set_defs comb_defs ..

(*For relations, we can in fact define an operator that acts as a 'dual' to relation-composition*)
definition relDualComp::"Rel('c,'a) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('c,'b)" (infixr ":\<^sup>r" 55)
  where "(:\<^sup>r) \<equiv> \<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<squnion>) \<^bold>I \<^bold>C"

lemma "(R\<^sub>1 :\<^sup>r R\<^sub>2) = (\<lambda>a b. R\<^sub>1 a \<squnion> R\<^sub>2\<Zcat> b)" 
  unfolding relDualComp_def set_defs comb_defs ..
lemma "(R\<^sub>1 :\<^sup>r R\<^sub>2) = (\<lambda>a b. \<forall>c. R\<^sub>1 a c \<or> R\<^sub>2 c b)"
  unfolding relDualComp_def set_defs comb_defs ..

declare relDualComp_def[rel_defs] relComp_def[rel_defs]

(*We introduce convenient 'flipped' notations for (dual-)composition (analogous to those for functions)*)
abbreviation(input) relComp_t::"Rel('b,'c) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('a,'c)" (infixl "\<circ>\<^sup>r" 55)
  where "R \<circ>\<^sup>r T \<equiv> T ;\<^sup>r R"
abbreviation(input) relDualComp_t::"Rel('c,'b) \<Rightarrow> Rel('a,'c) \<Rightarrow> Rel('a,'b)" (infixl "\<bullet>\<^sup>r" 55)
  where "R \<bullet>\<^sup>r T \<equiv> T :\<^sup>r R"

(*Unsurprisingly, (relational) composition and dual-composition are dual wrt. (relational) complement*)
lemma relCompDuality1: "R \<bullet>\<^sup>r T = ((R\<^sup>\<midarrow>) \<circ>\<^sup>r (T\<^sup>\<midarrow>))\<^sup>\<midarrow>" 
  unfolding rel_defs set_defs comb_defs by auto
lemma relCompDuality2: "R \<circ>\<^sup>r T = ((R\<^sup>\<midarrow>) \<bullet>\<^sup>r (T\<^sup>\<midarrow>))\<^sup>\<midarrow>" 
  unfolding rel_defs set_defs comb_defs by auto

(*Moreover, relation (dual)composition and (dis)equality satisfy the monoid conditions*)
lemma relComp_assoc: "(R \<circ>\<^sup>r T) \<circ>\<^sup>r V = R \<circ>\<^sup>r (T \<circ>\<^sup>r V)" (* associativity *)
  unfolding rel_defs set_defs comb_defs by auto                   
lemma relComp_id1: "\<Q> \<circ>\<^sup>r R = R"                     (* identity 1 *)
  unfolding rel_defs set_defs comb_defs by simp                   
lemma relComp_id2: "R \<circ>\<^sup>r \<Q> = R"                     (* identity 2 *)
  unfolding rel_defs set_defs comb_defs by simp   
lemma relCompDual_assoc: "(R \<bullet>\<^sup>r T) \<bullet>\<^sup>r V = R \<bullet>\<^sup>r (T \<bullet>\<^sup>r V)" (* associativity *)
  unfolding rel_defs set_defs comb_defs by auto                   
lemma relCompDual_id1: "\<D> \<bullet>\<^sup>r R = R"                     (* identity 1 *)
  unfolding rel_defs set_defs comb_defs by auto                   
lemma relCompDual_id2: "R \<bullet>\<^sup>r \<D> = R"                     (* identity 2 *)
  unfolding rel_defs set_defs comb_defs by simp 


subsubsection \<open>Transpose and cotranspose of a relation\<close>

(*Relations come with two further idiosyncratic unary operations.
 The first one is transposition (aka. "converse" or "reverse"), which naturally arises by seeing
 relations as binary operations (with boolean codomain), and corresponds to the \<^bold>C combinator.
 The second one, which we call "cotransposition", corresponds to the transposition/converse of the 
 complement (which is in fact identical to the complement of the transpose).*)

(*We reuse the existing notation to refer to the transpose/converse/reverse of a relation*)
lemma "R\<Zcat> = \<^bold>C R" unfolding comb_defs ..

(*We introduce convenient notation for the cotranspose*)
abbreviation cotranspose::"Rel('a,'b) \<Rightarrow> Rel('b,'a)" ("\<sim>\<^sup>r")
  where "\<sim>\<^sup>r \<equiv> \<midarrow>\<^sup>r \<circ> \<^bold>C"

notation(input) cotranspose  ("(_)\<^sup>\<sim>") (*convenient superscript notation*)

lemma "R\<^sup>\<sim> = R\<Zcat>\<^sup>\<midarrow>" unfolding comb_defs ..
lemma cotranspose_dual: "R\<^sup>\<sim> = R\<^sup>\<midarrow>\<Zcat>" unfolding comb_defs rel_defs set_defs ..
lemma cotranspose_involutive: "R\<^sup>\<sim>\<^sup>\<sim> = R" unfolding rel_defs set_defs comb_defs by simp

(*Clearly, (co)transposition (co)distributes over union and intersection*)
lemma "(R \<union>\<^sup>r T)\<Zcat> = (R\<Zcat>) \<union>\<^sup>r (T\<Zcat>)" unfolding rel_defs set_defs comb_defs ..
lemma "(R \<inter>\<^sup>r T)\<Zcat> = (R\<Zcat>) \<inter>\<^sup>r (T\<Zcat>)" unfolding rel_defs set_defs comb_defs ..
lemma "(R \<union>\<^sup>r T)\<^sup>\<sim> = (R\<^sup>\<sim>) \<inter>\<^sup>r (T\<^sup>\<sim>)" unfolding rel_defs set_defs comb_defs by simp
lemma "(R \<inter>\<^sup>r T)\<^sup>\<sim> = (R\<^sup>\<sim>) \<union>\<^sup>r (T\<^sup>\<sim>)" unfolding rel_defs set_defs comb_defs by simp

(*The inverse of a function corresponds to its converse when seen as a relation *)
lemma \<open>f\<inverse> = (asRel f)\<Zcat>\<close> unfolding rel_defs func_defs comb_defs ..


subsubsection \<open>Kernel of a relation\<close>

(*The "kernel" of a relation relates those elements in its source domain that are related to some 
 same value (i.e. whose images overlap)*)
definition relKernel::"Rel('a,'b) \<Rightarrow> ERel('a)"
  where "relKernel \<equiv> \<^bold>\<Psi>\<^sub>2 (\<sqinter>)"

declare relKernel_def[rel_defs]

lemma "relKernel R = (\<lambda>x y. R x \<sqinter> R y)" unfolding relKernel_def comb_defs ..

lemma "relKernel (asRel f) = kernel f" unfolding rel_defs func_defs set_defs comb_defs by metis
lemma "totalFunction R \<Longrightarrow> kernel (asFun R) = relKernel R" unfolding rel_defs func_defs set_defs comb_defs by (metis (mono_tags))


subsubsection \<open>Pullback and equalizer of a pair of relations\<close>

(*The pullback (aka. fiber product) of two relations 'R' and 'T' (sharing the same codomain), 
 relates those pairs of elements that get assigned some same value by 'R' and 'T' respectively*)
definition relPullback :: "Rel('a,'c) \<Rightarrow> Rel('b,'c) \<Rightarrow> Rel('a,'b)"
  where "relPullback \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<sqinter>)"

declare relPullback_def[rel_defs]

lemma "relPullback R T = (\<lambda>x y. R x \<sqinter> T y)" unfolding relPullback_def comb_defs ..

lemma "relPullback (asRel f) (asRel g) = pullback f g" 
  unfolding rel_defs comb_defs func_defs set_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> pullback (asFun R) (asFun T) = relPullback R T" 
  unfolding rel_defs comb_defs func_defs set_defs by (metis (mono_tags))

(*Converse and kernel of a relation can be easily stated in terms of relation-pullback*)
lemma "\<^bold>C = relPullback \<Q>" unfolding rel_defs set_defs comb_defs by auto
lemma "relKernel = \<^bold>W relPullback" unfolding rel_defs comb_defs ..


(*The equalizer of two relations 'R' and 'T' (sharing the same source and target) is the set of 
 elements 'x' in their (common) source that are related to some same value (i.e. R x and T x intersect). *)
definition relEqualizer :: "Rel('a,'b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('a)"
  where "relEqualizer \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<sqinter>)"

declare relEqualizer_def[rel_defs]

lemma "relEqualizer R T = (\<lambda>x. R x \<sqinter> T x)" unfolding rel_defs comb_defs ..

(*In fact, the equalizer of two relations can be stated in terms of their pullback*)
lemma "relEqualizer = \<^bold>W \<circ>\<^sub>2 relPullback" unfolding rel_defs comb_defs ..

(*Note that we can swap the roles of 'points' and 'functions' in the above definitions using permutators *)
lemma "\<^bold>R relEqualizer x = (\<lambda>R T. R x \<sqinter> T x)" unfolding rel_defs comb_defs ..
lemma "\<^bold>C\<^sub>2 relPullback x y = (\<lambda>R T. R x \<sqinter> T y)" unfolding rel_defs comb_defs ..

lemma "relEqualizer (asRel f) (asRel g) = equalizer f g" 
  unfolding rel_defs comb_defs func_defs set_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> equalizer (asFun R) (asFun T) = relEqualizer R T" 
  unfolding rel_defs comb_defs func_defs set_defs by (metis (mono_tags))


subsubsection \<open>Pushout and coequalizer of a pair of relations\<close>

(*The pushout (aka. fiber coproduct) of two relations 'R' and 'T' (sharing the same source), relates
 pairs of elements (in their targets) whose preimages under 'R' resp. 'T' intersect *)
abbreviation relPushout :: "Rel('a,'b) \<Rightarrow> Rel('a,'c) \<Rightarrow> Rel('b,'c)"
  where "relPushout R T \<equiv> relPullback (R\<Zcat>) (T\<Zcat>)"

lemma "relPushout R T = (\<lambda>x y. R\<Zcat> x \<sqinter> T\<Zcat> y)" unfolding rel_defs comb_defs ..

lemma "relPushout (asRel f) (asRel g) = pushout f g" 
  unfolding rel_defs comb_defs func_defs set_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> pushout (asFun R) (asFun T) = relPushout R T" 
  unfolding rel_defs comb_defs func_defs set_defs by (metis (full_types))

(*The coequalizer of two relations 'R' and 'T' (sharing the same source and target) is the set of 
 elements in their (common) target whose preimage under 'R' resp. 'T' intersect*)
abbreviation relCoequalizer :: "Rel('a,'b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('b)"
  where "relCoequalizer R T \<equiv> relEqualizer (R\<Zcat>) (T\<Zcat>)" 

lemma "relCoequalizer R T = (\<lambda>x. (R\<Zcat>) x \<sqinter> (T\<Zcat>) x)" unfolding rel_defs comb_defs ..

(*The coequalizer of two relations can be stated in terms of pushout*)
lemma "relCoequalizer = \<^bold>W \<circ>\<^sub>2 relPushout" unfolding rel_defs comb_defs ..

lemma "relCoequalizer (asRel f) (asRel g) = coequalizer f g" 
  unfolding rel_defs comb_defs func_defs set_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> coequalizer (asFun R) (asFun T) = relCoequalizer R T" 
  unfolding rel_defs comb_defs func_defs set_defs by (metis (full_types))


subsubsection \<open>Fixed-points of endorelations\<close>

definition relFixedpoint::"ERel('a) \<Rightarrow> Set('a)" ("rfp") (*i.e. set of "reflexive elements"*)
  where "rfp \<equiv> \<^bold>W"
definition relCofixedpoint::"ERel('a) \<Rightarrow> Set('a)" ("rcfp") (*i.e. set of "irreflexive elements"*)
  where "rcfp \<equiv> \<^bold>W \<circ> \<midarrow>\<^sup>r"

declare relFixedpoint_def[rel_defs] relCofixedpoint_def[rel_defs]

lemma "rfp R x = R x x" unfolding rel_defs comb_defs ..
lemma "rcfp R x = (\<not>R x x)" unfolding rel_defs set_defs comb_defs ..

lemma "relFixedpoint (asRel f) = fixedpoint f" 
  unfolding rel_defs comb_defs func_defs by auto
lemma "totalFunction R \<Longrightarrow> fixedpoint (asFun R) = relFixedpoint R" 
  unfolding rel_defs comb_defs set_defs func_defs by (metis someI)

lemma "relCofixedpoint (asRel f) = cofixedpoint f" 
  unfolding rel_defs comb_defs set_defs func_defs by auto
lemma "totalFunction R \<Longrightarrow> cofixedpoint (asFun R) = relCofixedpoint R" 
  unfolding rel_defs comb_defs set_defs func_defs by (metis someI)


subsection \<open>Set-operations defined from relations\<close>

(*We can extend the definitions of the (pre)image set-operator from functions to relations
 together with their 'dual' counterparts*)
definition rightImage::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)" ("_-rightImage")
  where "rightImage \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>C)\<Zcat>"
definition leftImage::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)" ("_-leftImage")
  where "leftImage \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>A)\<Zcat>"
definition rightDualImage::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)" ("_-rightDualImage")
  where "rightDualImage \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<subseteq>) \<^bold>C)\<Zcat>"
definition leftDualImage::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)" ("_-leftDualImage")
  where "leftDualImage \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<subseteq>) \<^bold>A)\<Zcat>"

declare rightImage_def[rel_defs] leftImage_def[rel_defs]
        rightDualImage_def[rel_defs] leftDualImage_def[rel_defs] 

lemma "R-rightImage A = (\<lambda>b. R\<Zcat> b \<sqinter> A)" unfolding rel_defs comb_defs ..
lemma "R-leftImage B = (\<lambda>a. R a \<sqinter> B)" unfolding rel_defs comb_defs ..
lemma "R-rightDualImage A = (\<lambda>b. R\<Zcat> b \<subseteq> A)" unfolding rel_defs comb_defs ..
lemma "R-leftDualImage B = (\<lambda>a. R a \<subseteq> B)" unfolding rel_defs comb_defs ..

lemma "R-rightImage A b = (\<exists>a. R a b \<and> A a)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-leftImage B a = (\<exists>b. R a b \<and> B b)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-rightDualImage A b = (\<forall>a. R a b \<rightarrow> A a)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-leftDualImage B a = (\<forall>b. R a b \<rightarrow> B b)" unfolding rel_defs set_defs func_defs comb_defs ..

(*Following operators (aka. "polarities") are inspired by (and generalize) the notion of upper/lower 
 bounds of a set wrt. an ordering. They are defined for relations in general.*)
definition rightBound::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)" ("_-rightBound")
  where "rightBound \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>C)\<Zcat>"                                 (*cf. rightDualImage (using \<supseteq>)*)
definition leftBound::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)" ("_-leftBound")
  where "leftBound \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>A)\<Zcat>"                                   (*cf. leftDualImage (using \<supseteq>)*)
definition rightDualBound::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)" ("_-rightDualBound")
  where  "rightDualBound \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>C)\<Zcat>"              (*cf. rightImage (preprocessed with \<midarrow>)*)
definition leftDualBound::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)" ("_-leftDualBound")
  where  "leftDualBound \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>A)\<Zcat>"                (*cf. leftImage (preprocessed with \<midarrow>)*)

declare rightBound_def[rel_defs] leftBound_def[rel_defs]
        rightDualBound_def[rel_defs] leftDualBound_def[rel_defs]

lemma "R-rightBound A = (\<lambda>b. A \<subseteq> R\<Zcat> b)" unfolding rel_defs comb_defs ..
lemma "R-leftBound B = (\<lambda>a. B \<subseteq> R a)" unfolding rel_defs comb_defs ..
lemma "R-rightDualBound A = (\<lambda>b. \<midarrow>(R\<Zcat> b) \<sqinter> \<midarrow>A)" unfolding rel_defs comb_defs ..
lemma "R-leftDualBound B = (\<lambda>a. \<midarrow>(R a) \<sqinter> \<midarrow>B)" unfolding rel_defs comb_defs ..

lemma "R-rightBound A = (\<lambda>b. \<forall>a. A a \<rightarrow> R a b)" unfolding rel_defs set_defs comb_defs ..
lemma "R-leftBound B = (\<lambda>a. \<forall>b. B b \<rightarrow> R a b)" unfolding rel_defs set_defs comb_defs ..
lemma "R-rightDualBound A = (\<lambda>b. \<exists>a. \<not>R a b \<and> \<not>A a)" unfolding rel_defs set_defs comb_defs ..
lemma "R-leftDualBound B = (\<lambda>a. \<exists>b. \<not>R a b \<and> \<not>B b)" unfolding rel_defs set_defs comb_defs ..

(*Alternative (more insightful?) definitions for dual-bounds*)
lemma rightDualBound_def': "rightDualBound = \<midarrow>\<^sup>r \<circ> ((\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<squnion>) \<^bold>C)\<Zcat>)" unfolding rel_defs set_defs comb_defs by simp
lemma leftDualBound_def':   "leftDualBound = \<midarrow>\<^sup>r \<circ> ((\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<squnion>) \<^bold>A)\<Zcat>)" unfolding rel_defs set_defs comb_defs by simp

lemma "R-rightDualBound A = \<midarrow>(\<lambda>b. R\<Zcat> b \<squnion> A)" unfolding rightDualBound_def' rel_defs set_defs comb_defs ..
lemma  "R-leftDualBound B = \<midarrow>(\<lambda>a. R a \<squnion> B)" unfolding leftDualBound_def' rel_defs set_defs comb_defs ..


(*Convenient characterizations in terms of big-union and big-intersection*)
lemma rightImage_def2: "rightImage = \<Union> \<circ>\<^sub>2 image"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma leftImage_def2: "leftImage = \<Union> \<circ>\<^sub>2 (image \<circ> \<^bold>C)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma rightDualImage_def2: "rightDualImage = \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 image \<midarrow>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma leftDualImage_def2: "leftDualImage = \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 image \<sim>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce

lemma "R-rightImage A = \<Union>\<lparr>R A\<rparr>" unfolding rightImage_def2 comb_defs ..
lemma "R-leftImage B = \<Union>\<lparr>R\<Zcat> B\<rparr>" unfolding leftImage_def2 comb_defs ..
lemma "R-rightDualImage A =  \<Inter>\<lparr>R\<^sup>\<midarrow> \<midarrow>A\<rparr>" unfolding rightDualImage_def2 comb_defs ..
lemma "R-leftDualImage B =  \<Inter>\<lparr>R\<^sup>\<sim> \<midarrow>B\<rparr>" unfolding leftDualImage_def2 comb_defs ..

lemma rightBound_def2: "rightBound = \<Inter> \<circ>\<^sub>2 image"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma leftBound_def2: "leftBound = \<Inter> \<circ>\<^sub>2 (image \<circ> \<^bold>C)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma rightDualBound_def2: "rightDualBound = \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 image \<midarrow>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma leftDualBound_def2: "leftDualBound = \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 image \<sim>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce

lemma "R-rightBound A = \<Inter>\<lparr>R A\<rparr>" unfolding rightBound_def2 comb_defs ..
lemma "R-leftBound B = \<Inter>\<lparr>R\<Zcat> B\<rparr>" unfolding leftBound_def2 comb_defs ..
lemma "R-rightDualBound A = \<Union>\<lparr>R\<^sup>\<midarrow> \<midarrow>A\<rparr>" unfolding rightDualBound_def2 comb_defs ..
lemma "R-leftDualBound B = \<Union>\<lparr>R\<^sup>\<sim> \<midarrow>B\<rparr>" unfolding leftDualBound_def2 comb_defs ..

(*Clearly, each direction (right/left) uniquely determines the other (its transpose)*)
lemma rightImage_defT: "R-rightImage = R\<Zcat>-leftImage" unfolding rel_defs comb_defs ..
lemma leftImage_defT: "R-leftImage = R\<Zcat>-rightImage" unfolding rel_defs comb_defs ..
lemma rightDualImage_defT: "R-rightDualImage = R\<Zcat>-leftDualImage" unfolding rel_defs comb_defs ..
lemma leftDualImage_defT: "R-leftDualImage = R\<Zcat>-rightDualImage" unfolding rel_defs comb_defs ..

lemma rightBound_defT: "R-rightBound = R\<Zcat>-leftBound" unfolding rel_defs comb_defs ..
lemma leftBound_defT: "R-leftBound = R\<Zcat>-rightBound" unfolding rel_defs comb_defs ..
lemma rightBoundDual_defT: "R-rightDualBound = R\<Zcat>-leftDualBound" unfolding rel_defs comb_defs ..
lemma leftBoundDual_defT: "R-leftDualBound = R\<Zcat>-rightDualBound" unfolding rel_defs comb_defs ..

(*Some particular properties of right and left bounds*)
lemma right_dual_hom: "R-rightBound(\<Union>S) = \<Inter>\<lparr>R-rightBound S\<rparr>" 
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma left_dual_hom:   "R-leftBound(\<Union>S) = \<Inter>\<lparr>R-leftBound S\<rparr>" 
  unfolding rel_defs set_defs func_defs comb_defs by fastforce 
(*Note, however:*)
lemma "R-rightBound(\<Inter>S) = \<Union>\<lparr>R-rightBound S\<rparr>" nitpick oops (*counterexample*)
lemma  "R-leftBound(\<Inter>S) = \<Union>\<lparr>R-leftBound S\<rparr>" nitpick oops (*counterexample*)
(*We have, rather:*)
lemma "R-rightBound(\<Inter>S) \<supseteq> \<Union>\<lparr>R-rightBound S\<rparr>"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma  "R-leftBound(\<Inter>S) \<supseteq> \<Union>\<lparr>R-leftBound S\<rparr>" 
  unfolding rel_defs set_defs func_defs comb_defs by fastforce

lemma leftRange_simp: "leftImage R \<UU> = leftRange R" unfolding rel_defs set_defs comb_defs by simp
lemma rightRange_simp: "rightImage R \<UU> = rightRange R" unfolding rel_defs set_defs comb_defs by simp
lemma leftDualRange_simp: "leftBound R \<UU> = leftDualRange R" unfolding rel_defs set_defs comb_defs by simp
lemma rightDualRange_simp: "rightBound R \<UU> = rightDualRange R" unfolding rel_defs set_defs comb_defs by simp

declare leftRange_simp[rel_simps] rightRange_simp[rel_simps] 
        leftDualRange_simp[rel_simps] rightDualRange_simp[rel_simps]

(*As expected, relational right- resp. left-image correspond to functional image resp. preimage*)
lemma "rightImage (asRel f) = image f" 
  unfolding rel_defs comb_defs func_defs by auto
lemma "leftImage (asRel f) = preimage f" 
  unfolding rel_defs comb_defs set_defs func_defs by auto
lemma "totalFunction R \<Longrightarrow> image (asFun R) = rightImage R" 
  unfolding rel_defs comb_defs set_defs func_defs by (metis someI)
lemma "totalFunction R \<Longrightarrow> preimage (asFun R) = leftImage R"
  unfolding rel_defs comb_defs set_defs func_defs by (metis someI)

end