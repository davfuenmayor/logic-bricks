theory rels (* A basic theory of relations (qua set-valued functions) *)
imports sets funcs
begin

section \<open>Relations\<close>

(*Relations inherit the structures of both sets and functions and enrich them in manifold ways.*)

named_theorems rel_defs  (*container for related definitions*)
named_theorems rel_simps (*container for related simplification rules*)


subsection \<open>Constructing relations\<close>


subsubsection \<open>Product and Sum\<close>
(*Relations can also be constructed out of pairs of sets, via (cartesian) product and (disjoint) sum*)

definition product::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<times>" 90)
  where "(\<times>) \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<and>)"
definition sum::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<uplus>" 90)
  where "(\<uplus>) \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<or>)"

declare product_def[rel_defs] sum_def[rel_defs]

lemma "A \<times> B = (\<lambda>x y. A x \<and> B y)" unfolding rel_defs comb_defs ..
lemma "A \<uplus> B = (\<lambda>x y. A x \<or> B y)" unfolding rel_defs comb_defs ..


subsubsection \<open>Pairs and Copairs\<close>
(*A (co)atomic-like relation can be constructed out of two elements*)

definition pair::"'a \<Rightarrow> 'b \<Rightarrow> Rel('a,'b)" ("\<langle>_,_\<rangle>")
  where \<open>pair \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<and>) \<Q> \<Q>\<close> (*relational counterpart of 'singleton'*)
definition copair::"'a \<Rightarrow> 'b \<Rightarrow> Rel('a,'b)" ("\<lblot>_,_\<rblot>")
  where \<open>copair \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<or>) \<D> \<D>\<close> (*relational counterpart of 'cosingleton'*)

declare pair_def[rel_defs] copair_def[rel_defs]

lemma "\<langle>a,b\<rangle> = (\<lambda>x y. a = x \<and> b = y)" unfolding rel_defs comb_defs ..
lemma "\<lblot>a,b\<rblot> = (\<lambda>x y. a \<noteq> x \<or> b \<noteq> y)" unfolding rel_defs comb_defs ..

(*Recalling that *)
lemma "\<^bold>B\<^sub>2\<^sub>2 = \<^bold>B\<^sub>1\<^sub>1 \<circ> \<^bold>B\<^sub>1\<^sub>1" unfolding comb_defs ..

(*We have that pair and copair can be defined in terms of (\<times>) and (\<uplus>) directly*)
lemma "pair   = \<^bold>B\<^sub>1\<^sub>1 (\<times>) \<Q> \<Q>" unfolding rel_defs comb_defs ..
lemma "copair = \<^bold>B\<^sub>1\<^sub>1 (\<uplus>) \<D> \<D>" unfolding rel_defs comb_defs ..
lemma "\<langle>a,b\<rangle> = {a} \<times> {b}" unfolding rel_defs comb_defs ..
lemma "\<lblot>a,b\<rblot> = \<lbrace>a\<rbrace> \<uplus> \<lbrace>b\<rbrace>" unfolding rel_defs comb_defs ..



(*We conveniently extrapolate the definitions of unique/singleton from sets to relations*)
definition uniqueR::"Set(Rel('a,'b))" ("!\<^sup>2") (* R holds of at most one pair of elements (R may hold of none)*)
  where \<open>!\<^sup>2 R \<equiv> \<forall>a b x y. (R a b \<and> R x y) \<rightarrow> (a = x \<and> b = y)\<close>
definition singletonR::"Set(Rel('a,'b))" ("\<exists>!\<^sup>2") (* R holds of exactly one pair of elements, i.e. R is a 'singleton relation'*)
  where \<open>\<exists>!\<^sup>2 R \<equiv> \<exists>x y. R x y \<and> (\<forall>a b. R a b \<rightarrow> (a = x \<and> b = y))\<close>

declare uniqueR_def[rel_defs] singletonR_def[rel_defs]

lemma uniqueR_def2: "!\<^sup>2 = \<nexists>\<^sup>2 \<union> \<exists>!\<^sup>2" unfolding rel_defs set_defs comb_defs by blast
lemma singletonR_def2: "\<exists>!\<^sup>2 = \<exists>\<^sup>2 \<inter> !\<^sup>2" unfolding rel_defs set_defs comb_defs apply (rule ext) by blast

(*Clearly, pairs correspond one-to-one to "singleton relations" *)
lemma pair_singletonR: "\<exists>!\<^sup>2 \<langle>a,b\<rangle>" unfolding rel_defs comb_defs by simp
lemma singletonR_def3: "\<exists>!\<^sup>2 R = (\<exists>a b. R = \<langle>a,b\<rangle>)" unfolding rel_defs comb_defs by metis


subsection \<open>Set-like structure\<close>

subsubsection \<open>Boolean operations\<close>
(*As we have seen, (curried) relations correspond to indexed families of sets. 
  It is thus not surprising that they inherit their Boolean algebra structure.*)

definition univR::"Rel('a,'b)" ("\<UU>\<^sup>r")
  where "\<UU>\<^sup>r \<equiv> \<^bold>\<Phi>\<^sub>0\<^sub>2 \<T>" (* the universal relation *)
definition emptyR::"Rel('a,'b)" ("\<emptyset>\<^sup>r")
  where "\<emptyset>\<^sup>r \<equiv> \<^bold>\<Phi>\<^sub>0\<^sub>2 \<F>"  (* the empty relation *)
definition complR::"EOp(Rel('a,'b))" ("\<midarrow>\<^sup>r") 
  where \<open>\<midarrow>\<^sup>r \<equiv> \<^bold>\<Phi>\<^sub>1\<^sub>2(\<not>)\<close> (* relation complement *)
definition interR::"EOp\<^sub>2(Rel('a,'b))" (infixl "\<inter>\<^sup>r" 54) 
  where "(\<inter>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>2(\<and>)" (* relation intersection *)
definition unionR::"EOp\<^sub>2(Rel('a,'b))" (infixl "\<union>\<^sup>r" 53) 
  where "(\<union>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>2(\<or>)" (* relation union *)
definition diffR:: "EOp\<^sub>2(Rel('a,'b))" (infixl "\<setminus>\<^sup>r" 51) 
  where "(\<setminus>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>2(\<leftharpoondown>)" (* relation difference *)
definition implR::"EOp\<^sub>2(Rel('a,'b))" (infixr "\<Rightarrow>\<^sup>r" 51) 
  where "(\<Rightarrow>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>2(\<rightarrow>)" (* relation implication *)
definition dimplR::"EOp\<^sub>2(Rel('a,'b))" (infix "\<Leftrightarrow>\<^sup>r" 51) 
  where "(\<Leftrightarrow>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>2(\<leftrightarrow>)" (* relation double-implication *)
definition sdiffR::"EOp\<^sub>2(Rel('a,'b))" (infix "\<triangle>\<^sup>r" 51) 
  where "(\<triangle>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>2(\<rightleftharpoons>)" (* relation symmetric difference (aka. xor) *)

(*Let's put rel-related definitions in the "rel_defs" bag *)
declare univR_def[rel_defs] emptyR_def[rel_defs]
        complR_def[rel_defs] interR_def[rel_defs] unionR_def[rel_defs]
        implR_def[rel_defs] dimplR_def[rel_defs] diffR_def[rel_defs] sdiffR_def[rel_defs]

notation (input) complR ("(_)\<^sup>\<midarrow>") (* alternative superscript notation common in the literature *)
notation(output) complR ("'(_')\<^sup>\<midarrow>")

(*Set-based definitions*)
lemma "\<UU>\<^sup>r = \<^bold>\<Phi>\<^sub>0\<^sub>1 \<UU>" unfolding comb_defs unfolding rel_defs set_defs comb_defs ..
lemma "\<UU>\<^sup>r = (\<lambda>x. \<UU>)" unfolding rel_defs set_defs comb_defs ..
lemma "\<emptyset>\<^sup>r = \<^bold>\<Phi>\<^sub>0\<^sub>1 \<emptyset>" unfolding rel_defs set_defs comb_defs ..
lemma "\<emptyset>\<^sup>r = (\<lambda>x. \<emptyset>)" unfolding rel_defs set_defs comb_defs ..
lemma "\<midarrow>\<^sup>r = \<^bold>\<Phi>\<^sub>1\<^sub>1 \<midarrow>" unfolding rel_defs set_defs comb_defs ..
lemma "\<midarrow>\<^sup>rR = (\<lambda>x. \<midarrow>(R x))" unfolding rel_defs set_defs comb_defs ..
lemma "(\<inter>\<^sup>r) = \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<inter>)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<inter>\<^sup>r T = (\<lambda>x. R x \<inter> T x)" unfolding rel_defs set_defs comb_defs ..
lemma "(\<union>\<^sup>r) = \<^bold>\<Phi>\<^sub>2\<^sub>1 (\<union>)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<union>\<^sup>r T = (\<lambda>x. R x \<union> T x)" unfolding rel_defs set_defs comb_defs ..
(*and so on*)

(*Point-based definitions*)
lemma "\<UU>\<^sup>r = (\<lambda>x y. \<T>)" unfolding rel_defs set_defs comb_defs ..
lemma "\<emptyset>\<^sup>r = (\<lambda>x y. \<F>)" unfolding rel_defs set_defs comb_defs ..
lemma "\<midarrow>\<^sup>rR = (\<lambda>x y. \<not>R x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<inter>\<^sup>r T = (\<lambda>x y. R x y \<and> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<union>\<^sup>r T = (\<lambda>x y. R x y \<or> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<setminus>\<^sup>r T = (\<lambda>x y. R x y \<leftharpoondown> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<Rightarrow>\<^sup>r T = (\<lambda>x y. R x y \<rightarrow> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<Leftrightarrow>\<^sup>r T = (\<lambda>x y. R x y \<leftrightarrow> T x y)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<triangle>\<^sup>r T = (\<lambda>x y. R x y \<rightleftharpoons> T x y)" unfolding rel_defs set_defs comb_defs ..

(*We can also generalize union and intersection to the infinitary case*)
definition biginterR::"EOp\<^sub>G(Rel('a,'b))" ("\<Inter>\<^sup>r") 
  where "\<Inter>\<^sup>r \<equiv> \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>0 image \<^bold>T)"
definition bigunionR::"EOp\<^sub>G(Rel('a,'b))" ("\<Union>\<^sup>r")
  where "\<Union>\<^sup>r \<equiv> \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>0 image \<^bold>T)"

declare biginterR_def[rel_defs] bigunionR_def[rel_defs]

lemma "\<Inter>\<^sup>rS a = \<Inter>\<lparr>(\<lambda>R. R a) S\<rparr>" unfolding rel_defs func_defs set_defs comb_defs ..
lemma "\<Union>\<^sup>rS a = \<Union>\<lparr>(\<lambda>R. R a) S\<rparr>" unfolding rel_defs func_defs set_defs comb_defs ..

(*Alternative definitions in terms of quantifiers directly*)
lemma biginterR_def2: "\<Inter>\<^sup>rS = (\<lambda>a b. \<forall>R. S R \<rightarrow> R a b)" 
  unfolding rel_defs set_defs func_defs comb_defs by metis
lemma bigunionR_def2: "\<Union>\<^sup>rS = (\<lambda>a b. \<exists>R. S R \<and> R a b)" 
  unfolding rel_defs set_defs func_defs comb_defs by metis


(*Product and sum satisfy the corresponding deMorgan dualities*)
lemma prodSum_simp1: "\<midarrow>\<^sup>r(A \<times> B) = \<midarrow>A \<uplus> \<midarrow>B" 
  unfolding rel_defs set_defs comb_defs by simp
lemma prodSum_simp2: "\<midarrow>\<^sup>r(A \<uplus> B) = \<midarrow>A \<times> \<midarrow>B" 
  unfolding rel_defs set_defs comb_defs by simp
lemma prodSum_simp1': "\<midarrow>\<^sup>r((\<midarrow>A) \<times> (\<midarrow>B)) = A \<uplus> B" 
  unfolding rel_defs set_defs comb_defs by simp
lemma prodSum_simp2': "\<midarrow>\<^sup>r((\<midarrow>A) \<uplus> (\<midarrow>B)) = A \<times> B" 
  unfolding rel_defs set_defs comb_defs by simp

(*Pairs and copairs are related via relation-complement as expected*)
lemma copair_simp: "\<midarrow>\<^sup>r\<lblot>a,b\<rblot> = \<langle>a,b\<rangle>" 
  unfolding rel_defs set_defs comb_defs by simp

declare prodSum_simp1 [rel_simps] prodSum_simp2 [rel_simps] prodSum_simp1' [rel_simps] prodSum_simp2' [rel_simps]


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

lemma subrel_def2: "(\<subseteq>\<^sup>r) = \<forall>\<^sup>2 \<circ>\<^sub>2 (\<Rightarrow>\<^sup>r)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<subseteq>\<^sup>r T = \<forall>\<^sup>2(R \<Rightarrow>\<^sup>r T)" unfolding rel_defs set_defs comb_defs ..

(*Subrelation is antisymmetric, as expected*)
lemma subrel_antisymm: "R \<subseteq>\<^sup>r T \<Longrightarrow> T \<subseteq>\<^sup>r R \<Longrightarrow> R = T" unfolding rel_defs set_defs comb_defs by blast


abbreviation(input) superrel::"ERel(Rel('a,'b))" (infixr "\<supseteq>\<^sup>r" 51) (*convenient notation*)
  where "A \<supseteq>\<^sup>r B \<equiv> B \<subseteq>\<^sup>r A" 

(* The "power-relation" operation corresponds to the (partial) application of superrel *)
notation superrel ("\<wp>\<^sup>r")
lemma "\<wp>\<^sup>rA = (\<lambda>B. B \<subseteq>\<^sup>r A)" unfolding comb_defs ..

(*In fact, any given relation R can be (join) generated by its singleton (pair) subrelations*)
lemma singletonR_gen: "R = \<Union>\<^sup>r(\<exists>!\<^sup>2 \<inter> \<wp>\<^sup>rR)"  
  unfolding bigunionR_def2 singletonR_def3 unfolding rel_defs set_defs comb_defs apply (rule ext) by auto


(*Two relations are said to 'overlap' (or 'intersect') if their intersection is non-empty*)
definition overlapR::"ERel(Rel('a,'b))" (infix "\<sqinter>\<^sup>r" 52)
  where "(\<sqinter>\<^sup>r) \<equiv> \<exists>\<^sup>2 \<circ>\<^sub>2 (\<inter>\<^sup>r)"
(*dually, two relations form a 'cover' if every pair belongs to one or the other *)
definition coverR::"ERel(Rel('a,'b))" (infix "\<squnion>\<^sup>r" 53)
  where "(\<squnion>\<^sup>r) \<equiv> \<forall>\<^sup>2 \<circ>\<^sub>2 (\<union>\<^sup>r)"
(*Two relations are said to be 'incompatible' if their intersection is empty*)
definition incompatR::"ERel(Rel('a,'b))" (infix "\<bottom>\<^sup>r" 52)
  where "(\<bottom>\<^sup>r) \<equiv> \<nexists>\<^sup>2 \<circ>\<^sub>2 (\<inter>\<^sup>r)"

declare incompatR_def[rel_defs] overlapR_def[rel_defs] coverR_def[rel_defs]

lemma "A \<sqinter>\<^sup>r B = \<exists>\<^sup>2(A \<inter>\<^sup>r B)" unfolding rel_defs comb_defs ..
lemma "A \<sqinter>\<^sup>r B = (\<exists>x. A x \<sqinter> B x)" unfolding rel_defs set_defs comb_defs ..
lemma "A \<sqinter>\<^sup>r B = (\<exists>x y. (A x y \<and> B x y))" unfolding rel_defs set_defs comb_defs ..

lemma "A \<squnion>\<^sup>r B = \<forall>\<^sup>2(A \<union>\<^sup>r B)" unfolding rel_defs comb_defs ..
lemma "A \<squnion>\<^sup>r B = (\<forall>x. A x \<squnion> B x)" unfolding rel_defs set_defs comb_defs ..
lemma "A \<squnion>\<^sup>r B = (\<forall>x y. A x y \<or> B x y)" unfolding rel_defs set_defs comb_defs ..

lemma "A \<bottom>\<^sup>r B = \<nexists>\<^sup>2(A \<inter>\<^sup>r B)" unfolding rel_defs comb_defs ..
lemma "A \<bottom>\<^sup>r B = (\<nexists>x y. A x y \<and> B x y)" unfolding rel_defs set_defs comb_defs ..
lemma "A \<bottom>\<^sup>r B = (\<not>(A \<sqinter>\<^sup>r B))" unfolding rel_defs comb_defs ..


definition psubrel::"ERel(Rel('a,'b))" (infixr "\<subset>\<^sup>r" 51) (*proper subrelation*)
  where "(\<subset>\<^sup>r) \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>2 (\<leftharpoondown>) (\<subseteq>\<^sup>r) (\<supseteq>\<^sup>r)"

declare psubrel_def[rel_defs]

lemma "R \<subset>\<^sup>r T = (R \<subseteq>\<^sup>r T \<and> \<exists>\<^sup>2(T \<setminus>\<^sup>r R))" unfolding rel_defs set_defs comb_defs by simp
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
  where "\<Sqinter>\<^sup>r \<equiv> \<exists>\<^sup>2 \<circ> \<Inter>\<^sup>r"
(*dually, a set of relations forms a 'cover' if every pair is contained in at least one of the relations.*)
abbreviation(input) bigcoverR::"Set(Set(Rel('a,'b)))" ("\<Squnion>\<^sup>r")
  where "\<Squnion>\<^sup>r \<equiv> \<forall>\<^sup>2 \<circ> \<Union>\<^sup>r"

lemma "\<Sqinter>\<^sup>rS = \<exists>\<^sup>2(\<Inter>\<^sup>rS)" unfolding comb_defs ..
lemma "\<Squnion>\<^sup>rS = \<forall>\<^sup>2(\<Union>\<^sup>rS)" unfolding comb_defs ..


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
  where "leftRange \<equiv> \<exists> \<circ>\<^sub>2 \<^bold>A"
definition rightRange::"Rel('a,'b) \<Rightarrow> Set('b)"
  where "rightRange \<equiv> \<exists> \<circ>\<^sub>2 \<^bold>C"

lemma "leftRange R a = (\<exists>x. R a x)" unfolding leftRange_def comb_defs ..
lemma "rightRange R b = (\<exists>x. R x b)" unfolding rightRange_def comb_defs ..


(*Dually, the left- (right-) dual-range of a relation is the set of those objects in the source (target)
 domain that reach to (are reached by) all elements in the target (source) domain*)
definition leftDualRange::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "leftDualRange \<equiv> \<forall> \<circ>\<^sub>2 \<^bold>A"
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


(*Similarly, by composition with !, we obtain the set of deterministic (or 'univalent') elements.
 They get assigned at most one value under the relation (which then behaves deterministically on them)*)
definition deterministic::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "deterministic \<equiv> \<^bold>B unique"

(*Also, by composition with \<exists>\<^sub>1, we obtain the set of total(ly) deterministic elements. 
 They get assigned precisely one value under the relation (which then behaves as a function on them)*)
definition totalDeterministic::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "totalDeterministic \<equiv> \<^bold>B singleton"

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
lemma rightUnique_gen: "R = \<Union>\<^sup>r(\<wp>\<^sup>r R \<inter> rightUnique)"
  unfolding bigunionR_def2 oops (*TODO*)
lemma leftUnique_gen: "R = \<Union>\<^sup>r(\<wp>\<^sup>r R \<inter> leftUnique)" 
  unfolding bigunionR_def2 oops (*TODO*)


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
lemma "asRel f = \<^bold>C (f\<inverse>)" unfolding asRel_def2 comb_defs ..

(*Relations corresponding to lifted functions are always left-total and right-unique (i.e. functions) *)
lemma "totalFunction (asRel f)" unfolding rel_defs set_defs comb_defs by simp


(*A given set of functions can be transformed (or 'aggregated') into a relation*)
definition intoRel::"Set('a \<Rightarrow> 'b) \<Rightarrow> Rel('a,'b)" ("intoRel")
  where "intoRel \<equiv> \<^bold>C (image \<circ> \<^bold>T)"

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
  where "intoFunSet \<equiv> \<^bold>C ((\<subseteq>\<^sup>r) \<circ> asRel)"

declare intoFunSet_def[rel_defs] 

lemma "intoFunSet R = (\<lambda>f. asRel f \<subseteq>\<^sup>r R)" unfolding rel_defs comb_defs ..
lemma "intoFunSet R = (\<lambda>f. \<forall>a b. f a = b \<rightarrow> R a b)" unfolding rel_defs set_defs comb_defs ..
(*Another perspective:*)
lemma intoFunSet_def2: "intoFunSet = \<^bold>B\<^sub>1\<^sub>1 \<wp>\<^sup>r \<^bold>I asRel" unfolding rel_defs set_defs comb_defs ..


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


subsection \<open>Transpose and cotranspose\<close>

(*Relations come with two further idiosyncratic unary operations.
 The first one is transposition (aka. "converse" or "reverse"), which naturally arises by seeing
 relations as binary operations (with boolean codomain), and corresponds to the \<^bold>C combinator.
 The second one, which we call "cotransposition", corresponds to the transpose/converse of the 
 complement (which is in fact identical to the complement of the transpose).*)

definition transpose::"Rel('a,'b) \<Rightarrow> Rel('b,'a)" ("\<smile>")
  where "\<smile> \<equiv> \<^bold>C"
definition cotranspose::"Rel('a,'b) \<Rightarrow> Rel('b,'a)" ("\<frown>")
  where "\<frown> \<equiv> \<midarrow>\<^sup>r \<circ> \<^bold>C"

declare transpose_def[rel_defs] cotranspose_def[rel_defs]

(*Most of the time we will employ the following superscript notation (analogously to complement)*)
notation(input) transpose  ("(_)\<^sup>\<smile>") and cotranspose  ("(_)\<^sup>\<frown>") 
notation(output) transpose  ("'(_')\<^sup>\<smile>") and cotranspose  ("'(_')\<^sup>\<frown>") 

lemma "R\<^sup>\<frown> = R\<^sup>\<smile>\<^sup>\<midarrow>" unfolding rel_defs comb_defs ..
lemma "R\<^sup>\<frown> = R\<^sup>\<midarrow>\<^sup>\<smile>" unfolding rel_defs comb_defs ..

lemma transpose_involutive: "R\<^sup>\<smile>\<^sup>\<smile> = R" unfolding rel_defs set_defs comb_defs by simp
lemma cotranspose_involutive: "R\<^sup>\<frown>\<^sup>\<frown> = R" unfolding rel_defs set_defs comb_defs by simp
lemma complement_involutive: "R\<^sup>\<midarrow>\<^sup>\<midarrow> = R" unfolding rel_defs set_defs comb_defs by simp

(*Clearly, (co)transposition (co)distributes over union and intersection*)
lemma "(R \<union>\<^sup>r T)\<^sup>\<smile> = (R\<^sup>\<smile>) \<union>\<^sup>r (T\<^sup>\<smile>)" unfolding rel_defs set_defs comb_defs ..
lemma "(R \<inter>\<^sup>r T)\<^sup>\<smile> = (R\<^sup>\<smile>) \<inter>\<^sup>r (T\<^sup>\<smile>)" unfolding rel_defs set_defs comb_defs ..
lemma "(R \<union>\<^sup>r T)\<^sup>\<frown> = (R\<^sup>\<frown>) \<inter>\<^sup>r (T\<^sup>\<frown>)" unfolding rel_defs set_defs comb_defs by simp
lemma "(R \<inter>\<^sup>r T)\<^sup>\<frown> = (R\<^sup>\<frown>) \<union>\<^sup>r (T\<^sup>\<frown>)" unfolding rel_defs set_defs comb_defs by simp

(*The inverse of a function corresponds to its converse when seen as a relation *)
lemma \<open>f\<inverse> = (asRel f)\<^sup>\<smile>\<close> unfolding rel_defs func_defs comb_defs ..



subsection \<open>Function-like algebraic structure\<close>

subsubsection \<open>Monoidal structure (relation-composition and its dual)\<close>

(*Analogously to functions, relations can also be composed. We introduce 'relation-composition' below*)
definition relComp::"Rel('a,'b) \<Rightarrow> Rel('b,'c) \<Rightarrow>  Rel('a,'c)" (infixr ";\<^sup>r" 55)
 where "(;\<^sup>r) = \<^bold>B\<^sub>2\<^sub>2 (\<sqinter>) \<^bold>A \<smile>"

lemma "R\<^sub>1 ;\<^sup>r R\<^sub>2 = (\<lambda>a b. R\<^sub>1 a \<sqinter> R\<^sub>2\<^sup>\<smile> b)" 
  unfolding relComp_def set_defs comb_defs ..
lemma "R\<^sub>1 ;\<^sup>r R\<^sub>2 = (\<lambda>a b. \<exists>c. R\<^sub>1 a c \<and> R\<^sub>2 c b)"
  unfolding relComp_def rel_defs set_defs comb_defs ..

(*For relations, we can in fact define an operator that acts as a 'dual' to relation-composition*)
definition relDualComp::"Rel('c,'a) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('c,'b)" (infixr ":\<^sup>r" 55)
  where "(:\<^sup>r) \<equiv> \<^bold>B\<^sub>2\<^sub>2 (\<squnion>) \<^bold>A \<smile>"

lemma "(R\<^sub>1 :\<^sup>r R\<^sub>2) = (\<lambda>a b. R\<^sub>1 a \<squnion> R\<^sub>2\<^sup>\<smile> b)" 
  unfolding relDualComp_def set_defs comb_defs ..
lemma "(R\<^sub>1 :\<^sup>r R\<^sub>2) = (\<lambda>a b. \<forall>c. R\<^sub>1 a c \<or> R\<^sub>2 c b)"
  unfolding relDualComp_def rel_defs set_defs comb_defs ..

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


subsubsection \<open>Kernel of a relation\<close>

(*The "kernel" of a relation relates those elements in its source domain that are related to some 
 same value (i.e. whose images overlap)*)
definition relKernel::"Rel('a,'b) \<Rightarrow> ERel('a)"
  where "relKernel \<equiv> \<^bold>\<Psi>\<^sub>2 (\<sqinter>)"

declare relKernel_def[rel_defs]

lemma "relKernel R = (\<lambda>x y. R x \<sqinter> R y)" unfolding relKernel_def comb_defs ..

(*The notion of kernel for relations corresponds to (and generalizes) the functional counterpart*)
lemma "relKernel (asRel f) = kernel f" unfolding rel_defs func_defs set_defs comb_defs by metis
lemma "totalFunction R \<Longrightarrow> kernel (asFun R) = relKernel R" unfolding rel_defs func_defs set_defs comb_defs by (metis (mono_tags))


subsubsection \<open>Pullback and equalizer of a pair of relations\<close>

(*The pullback (aka. fiber product) of two relations 'R' and 'T' (sharing the same target), 
 relates those pairs of elements that get assigned some same value by 'R' and 'T' respectively*)
definition relPullback :: "Rel('a,'c) \<Rightarrow> Rel('b,'c) \<Rightarrow> Rel('a,'b)"
  where "relPullback \<equiv> \<^bold>B\<^sub>1\<^sub>1 (\<sqinter>)"

declare relPullback_def[rel_defs]

lemma "relPullback R T = (\<lambda>x y. R x \<sqinter> T y)" unfolding relPullback_def comb_defs ..

(*The notion of pullback for relations corresponds to (and generalizes) the functional counterpart*)
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

(*The notion of equalizer for relations corresponds to (and generalizes) the functional counterpart*)
lemma "relEqualizer (asRel f) (asRel g) = equalizer f g" 
  unfolding rel_defs comb_defs func_defs set_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> equalizer (asFun R) (asFun T) = relEqualizer R T" 
  unfolding rel_defs comb_defs func_defs set_defs by (metis (mono_tags))


subsubsection \<open>Pushout and coequalizer of a pair of relations\<close>

(*The pushout (aka. fiber coproduct) of two relations 'R' and 'T' (sharing the same source), relates
 pairs of elements (in their targets) whose preimages under 'R' resp. 'T' intersect *)
abbreviation relPushout :: "Rel('a,'b) \<Rightarrow> Rel('a,'c) \<Rightarrow> Rel('b,'c)"
  where "relPushout R T \<equiv> relPullback R\<^sup>\<smile> T\<^sup>\<smile>"

lemma "relPushout R T = (\<lambda>x y. R\<^sup>\<smile> x \<sqinter> T\<^sup>\<smile> y)" unfolding rel_defs comb_defs ..

(*The notion of pushout for relations corresponds to (and generalizes) the functional counterpart*)
lemma "relPushout (asRel f) (asRel g) = pushout f g" 
  unfolding rel_defs comb_defs func_defs set_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> pushout (asFun R) (asFun T) = relPushout R T" 
  unfolding rel_defs comb_defs func_defs set_defs by (metis (full_types))

(*The coequalizer of two relations 'R' and 'T' (sharing the same source and target) is the set of 
 elements in their (common) target whose preimage under 'R' resp. 'T' intersect*)
abbreviation relCoequalizer :: "Rel('a,'b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Set('b)"
  where "relCoequalizer R T \<equiv> relEqualizer R\<^sup>\<smile> T\<^sup>\<smile>" 

lemma "relCoequalizer R T = (\<lambda>x. R\<^sup>\<smile> x \<sqinter> T\<^sup>\<smile> x)" unfolding rel_defs comb_defs ..

(*The coequalizer of two relations can be stated in terms of pushout*)
lemma "relCoequalizer = \<^bold>W \<circ>\<^sub>2 relPushout" unfolding rel_defs comb_defs ..

(*The notion of coequalizer for relations corresponds to (and generalizes) the functional counterpart*)
lemma "relCoequalizer (asRel f) (asRel g) = coequalizer f g" 
  unfolding rel_defs comb_defs func_defs set_defs by fastforce
lemma "totalFunction R \<Longrightarrow> totalFunction T \<Longrightarrow> coequalizer (asFun R) (asFun T) = relCoequalizer R T" 
  unfolding rel_defs comb_defs func_defs set_defs by (metis (full_types))


subsubsection \<open>Diagonal elements\<close>

(*The notion of diagonal (aka. reflexive) elements of an endorelation is the relational counterpart 
 to the notion of fixed-points of an endofunction. It corresponds to the \<^bold>W combinator.*)
abbreviation(input) diagonal::"ERel('a) \<Rightarrow> Set('a)" ("\<Delta>")
  where "\<Delta> \<equiv> \<^bold>W"

lemma "\<Delta> R x = R x x" unfolding rel_defs comb_defs ..

lemma "\<Delta> (asRel f) = FP f" 
  unfolding rel_defs comb_defs func_defs by auto
lemma "totalFunction R \<Longrightarrow> FP (asFun R) = \<Delta> R" 
  unfolding rel_defs comb_defs set_defs func_defs by (metis someI)

(*Analogously, the notion of non-diagonal (aka. irreflexive) elements of an endorelation (notation: \<Delta>\<^sup>\<midarrow>)
 is the relational counterpart to the notion of non-fixed-points of an endofunction.*)
lemma "\<Delta>\<^sup>\<midarrow> = \<midarrow>\<^sup>r\<Delta>" unfolding rel_defs comb_defs ..
lemma "\<Delta>\<^sup>\<midarrow> = \<Delta> \<circ> \<midarrow>\<^sup>r" unfolding rel_defs comb_defs ..
lemma "\<Delta>\<^sup>\<midarrow> R x = (\<not>R x x)" unfolding rel_defs comb_defs ..
lemma "\<Delta>\<^sup>\<midarrow> = \<midarrow> \<circ> \<Delta>" unfolding rel_defs set_defs comb_defs ..
lemma "\<Delta>\<^sup>\<midarrow> R = \<midarrow>(\<Delta> R)" unfolding rel_defs set_defs comb_defs ..

lemma "\<Delta>\<^sup>\<midarrow> (asRel f) = nFP f" 
  unfolding rel_defs comb_defs set_defs func_defs by auto
lemma "totalFunction R \<Longrightarrow> nFP (asFun R) = \<Delta>\<^sup>\<midarrow> R" 
  unfolding rel_defs comb_defs set_defs func_defs by (metis someI)


subsection \<open>Set-operations defined from relations\<close>

(*We can extend the definitions of the (pre)image set-operator from functions to relations
 together with their 'dual' counterparts*)
definition rightImage::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)"
  where "rightImage \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>C)"
definition leftImage::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)"
  where "leftImage \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>A)"
definition rightDualImage::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)" 
  where "rightDualImage \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<subseteq>) \<^bold>C)"
definition leftDualImage::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)" 
  where "leftDualImage \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<subseteq>) \<^bold>A)"

declare rightImage_def[rel_defs] leftImage_def[rel_defs] rightDualImage_def[rel_defs] leftDualImage_def[rel_defs] 

(*Convenient input notation*)
notation(input) rightImage ("_-rightImage") and  leftImage ("_-leftImage") and
                rightDualImage ("_-rightDualImage") and  leftDualImage ("_-leftDualImage")

lemma "R-rightImage A = (\<lambda>b. R\<^sup>\<smile> b \<sqinter> A)" unfolding rel_defs comb_defs ..
lemma "R-leftImage B = (\<lambda>a. R a \<sqinter> B)" unfolding rel_defs comb_defs ..
lemma "R-rightDualImage A = (\<lambda>b. R\<^sup>\<smile> b \<subseteq> A)" unfolding rel_defs comb_defs ..
lemma "R-leftDualImage B = (\<lambda>a. R a \<subseteq> B)" unfolding rel_defs comb_defs ..

lemma "R-rightImage A b = (\<exists>a. R a b \<and> A a)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-leftImage B a = (\<exists>b. R a b \<and> B b)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-rightDualImage A b = (\<forall>a. R a b \<rightarrow> A a)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-leftDualImage B a = (\<forall>b. R a b \<rightarrow> B b)" unfolding rel_defs set_defs func_defs comb_defs ..

(*Convenient characterizations in terms of big-union and big-intersection*)
lemma rightImage_def2: "rightImage = \<Union> \<circ>\<^sub>2 image"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma leftImage_def2: "leftImage = \<Union> \<circ>\<^sub>2 (image \<circ> \<smile>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma rightDualImage_def2: "rightDualImage = \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 image \<midarrow>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma leftDualImage_def2: "leftDualImage = \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 image \<frown> \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce

lemma "R-rightImage A = \<Union>\<lparr>R A\<rparr>" unfolding rightImage_def2 comb_defs ..
lemma "R-leftImage B = \<Union>\<lparr>R\<^sup>\<smile> B\<rparr>" unfolding leftImage_def2 comb_defs ..
lemma "R-rightDualImage A =  \<Inter>\<lparr>R\<^sup>\<midarrow> \<midarrow>A\<rparr>" unfolding rightDualImage_def2 comb_defs ..
lemma "R-leftDualImage B =  \<Inter>\<lparr>R\<^sup>\<frown> \<midarrow>B\<rparr>" unfolding leftDualImage_def2 comb_defs ..

(*As expected, relational right- resp. left-image correspond to functional image resp. preimage*)
lemma "rightImage (asRel f) = image f" 
  unfolding rel_defs comb_defs func_defs by auto
lemma "leftImage (asRel f) = preimage f" 
  unfolding rel_defs comb_defs set_defs func_defs by auto
lemma "totalFunction R \<Longrightarrow> image (asFun R) = rightImage R" 
  unfolding rel_defs comb_defs set_defs func_defs by (metis someI)
lemma "totalFunction R \<Longrightarrow> preimage (asFun R) = leftImage R"
  unfolding rel_defs comb_defs set_defs func_defs by (metis someI)

(*Clearly, each direction (right/left) uniquely determines the other (its transpose)*)
lemma rightImage_defT: "R-rightImage = R\<^sup>\<smile>-leftImage" unfolding rel_defs comb_defs ..
lemma leftImage_defT: "R-leftImage = R\<^sup>\<smile>-rightImage" unfolding rel_defs comb_defs ..
lemma rightDualImage_defT: "R-rightDualImage = R\<^sup>\<smile>-leftDualImage" unfolding rel_defs comb_defs ..
lemma leftDualImage_defT: "R-leftDualImage = R\<^sup>\<smile>-rightDualImage" unfolding rel_defs comb_defs ..


(*Following operators (aka. "polarities") are inspired by (and generalize) the notion of upper/lower 
 bounds of a set wrt. an ordering. They are defined here for relations in general.*)
definition rightBound::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)"
  where "rightBound \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>C)"                                 (*cf. rightDualImage (using \<supseteq>)*)
definition leftBound::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)"
  where "leftBound \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>A)"                                   (*cf. leftDualImage (using \<supseteq>)*)
definition rightDualBound::"Rel('a,'b) \<Rightarrow> SetOp('a,'b)"
  where  "rightDualBound \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>C)"              (*cf. rightImage (preprocessed with \<midarrow>)*)
definition leftDualBound::"Rel('a,'b) \<Rightarrow> SetOp('b,'a)"
  where  "leftDualBound \<equiv> \<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>A)"                (*cf. leftImage (preprocessed with \<midarrow>)*)

declare rightBound_def[rel_defs] leftBound_def[rel_defs] rightDualBound_def[rel_defs] leftDualBound_def[rel_defs]

(*Convenient input notation*)
notation(input) rightBound ("_-rightBound") and  leftBound ("_-leftBound") and
                rightDualBound ("_-rightDualBound") and  leftDualBound ("_-leftDualBound")

lemma "R-rightBound A = (\<lambda>b. A \<subseteq> R\<^sup>\<smile> b)" unfolding rel_defs comb_defs ..
lemma "R-leftBound B = (\<lambda>a. B \<subseteq> R a)" unfolding rel_defs comb_defs ..
lemma "R-rightDualBound A = (\<lambda>b. \<midarrow>(R\<^sup>\<smile> b) \<sqinter> \<midarrow>A)" unfolding rel_defs comb_defs ..
lemma "R-leftDualBound B = (\<lambda>a. \<midarrow>(R a) \<sqinter> \<midarrow>B)" unfolding rel_defs comb_defs ..

lemma "R-rightBound A = (\<lambda>b. \<forall>a. A a \<rightarrow> R a b)" unfolding rel_defs set_defs comb_defs ..
lemma "R-leftBound B = (\<lambda>a. \<forall>b. B b \<rightarrow> R a b)" unfolding rel_defs set_defs comb_defs ..
lemma "R-rightDualBound A = (\<lambda>b. \<exists>a. \<not>R a b \<and> \<not>A a)" unfolding rel_defs set_defs comb_defs ..
lemma "R-leftDualBound B = (\<lambda>a. \<exists>b. \<not>R a b \<and> \<not>B b)" unfolding rel_defs set_defs comb_defs ..

(*Alternative (more insightful?) definitions for dual-bounds*)
lemma rightDualBound_def': "rightDualBound = \<midarrow>\<^sup>r \<circ> (\<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<squnion>) \<^bold>C))" unfolding rel_defs set_defs comb_defs by simp
lemma leftDualBound_def':   "leftDualBound = \<midarrow>\<^sup>r \<circ> (\<^bold>C (\<^bold>B\<^sub>2\<^sub>0 (\<squnion>) \<^bold>A))" unfolding rel_defs set_defs comb_defs by simp

lemma "R-rightDualBound A = \<midarrow>(\<lambda>b. R\<^sup>\<smile> b \<squnion> A)" unfolding rightDualBound_def' rel_defs set_defs comb_defs ..
lemma  "R-leftDualBound B = \<midarrow>(\<lambda>a. R a \<squnion> B)" unfolding leftDualBound_def' rel_defs set_defs comb_defs ..


(*Convenient characterizations in terms of big-union and big-intersection*)
lemma rightBound_def2: "rightBound = \<Inter> \<circ>\<^sub>2 image"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma leftBound_def2: "leftBound = \<Inter> \<circ>\<^sub>2 (image \<circ> \<smile>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma rightDualBound_def2: "rightDualBound = \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 image \<midarrow>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma leftDualBound_def2: "leftDualBound = \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 image \<frown> \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce

lemma "R-rightBound A = \<Inter>\<lparr>R A\<rparr>" unfolding rightBound_def2 comb_defs ..
lemma "R-leftBound B = \<Inter>\<lparr>R\<^sup>\<smile> B\<rparr>" unfolding leftBound_def2 comb_defs ..
lemma "R-rightDualBound A = \<Union>\<lparr>R\<^sup>\<midarrow> \<midarrow>A\<rparr>" unfolding rightDualBound_def2 comb_defs ..
lemma "R-leftDualBound B = \<Union>\<lparr>R\<^sup>\<frown> \<midarrow>B\<rparr>" unfolding leftDualBound_def2 comb_defs ..


(*Some particular properties of rsight and left bounds*)
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

(*Clearly, each direction (right/left) uniquely determines the other (its transpose)*)
lemma rightBound_defT: "R-rightBound = R\<^sup>\<smile>-leftBound" unfolding rel_defs comb_defs ..
lemma leftBound_defT: "R-leftBound = R\<^sup>\<smile>-rightBound" unfolding rel_defs comb_defs ..
lemma rightBoundDual_defT: "R-rightDualBound = R\<^sup>\<smile>-leftDualBound" unfolding rel_defs comb_defs ..
lemma leftBoundDual_defT: "R-leftDualBound = R\<^sup>\<smile>-rightDualBound" unfolding rel_defs comb_defs ..

(*In fact, there exists a particular 'relational duality' between images and bounds, as follows*)
lemma rightImage_dualR: "R-rightImage = (R\<^sup>\<midarrow>-rightBound)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftImage_dualR: "R-leftImage = (R\<^sup>\<midarrow>-leftBound)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma rightDualImage_dualR: "R-rightDualImage = (R\<^sup>\<midarrow>-rightDualBound)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftDualImage_dualR: "R-leftDualImage = (R\<^sup>\<midarrow>-leftDualBound)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma rightBound_dualR: "R-rightBound = (R\<^sup>\<midarrow>-rightImage)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftBound_dualR: "R-leftBound = (R\<^sup>\<midarrow>-leftImage)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma rightDualBound_dualR: "R-rightDualBound = (R\<^sup>\<midarrow>-rightDualImage)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftDualBound_dualR: "R-leftDualBound = (R\<^sup>\<midarrow>-leftDualImage)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto

(*Finally, ranges can be expressed in terms of images and bounds*)
lemma leftRange_simp: "leftImage R \<UU> = leftRange R" unfolding rel_defs set_defs comb_defs by simp
lemma rightRange_simp: "rightImage R \<UU> = rightRange R" unfolding rel_defs set_defs comb_defs by simp
lemma leftDualRange_simp: "leftBound R \<UU> = leftDualRange R" unfolding rel_defs set_defs comb_defs by simp
lemma rightDualRange_simp: "rightBound R \<UU> = rightDualRange R" unfolding rel_defs set_defs comb_defs by simp

declare leftRange_simp[rel_simps] rightRange_simp[rel_simps] 
        leftDualRange_simp[rel_simps] rightDualRange_simp[rel_simps]


subsection \<open>Monads\<close>

subsubsection \<open>Set monad\<close>

(*We can conceive of types of form Set('a), i.e. 'a \<Rightarrow> o, as arising via an 'environmentalization'
 (or 'indexation') of the boolean type (o) by the type 'a (i.e. as an instance of the environment 
 monad discussed previously). Furthermore, we can adopt an alternative perspective and consider a 
 constructor that returns the type of boolean 'valuations' (or 'classifiers') for objects of type 'a.
 This type constructor comes with a monad structure too (and is also an applicative and a functor).*)

abbreviation(input) unit_set::"'a \<Rightarrow> Set('a)"
  where "unit_set \<equiv> \<Q>"
abbreviation(input) fmap_set::"('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "fmap_set \<equiv> image"
abbreviation(input) join_set::"Set(Set('a)) \<Rightarrow> Set('a)"
  where "join_set \<equiv> \<Union>"
abbreviation(input) ap_set::"Set('a \<Rightarrow> 'b) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "ap_set \<equiv> rightImage \<circ> intoRel"
abbreviation(input) rbind_set::"('a \<Rightarrow> Set('b)) \<Rightarrow> Set('a) \<Rightarrow> Set('b)"
  where "rbind_set \<equiv> rightImage" (*reversed bind*)

(*We define the customary bind operation as 'flipped' rbind (which seems more intuitive)*)
abbreviation bind_set::"Set('a) \<Rightarrow> ('a \<Rightarrow> Set('b)) \<Rightarrow> Set('b)"
  where "bind_set \<equiv> \<^bold>C rbind_set"

(*Some properties of monads in general*)
lemma "rbind_set = join_set \<circ>\<^sub>2 fmap_set" unfolding rel_defs set_defs func_defs comb_defs by metis
lemma "join_set = rbind_set \<^bold>I" unfolding rel_defs set_defs comb_defs by metis
(*...*)

(*Some properties of this particular monad*)
lemma "ap_set = \<Union>\<^sup>r \<circ> (image image)" unfolding rel_defs func_defs set_defs comb_defs by blast
(*...*)

(*Verifies compliance with the monad laws*)
lemma "LawBind1 unit_set bind_set" unfolding rel_defs set_defs comb_defs by simp
lemma "LawBind2 unit_set bind_set" unfolding rel_defs set_defs comb_defs by simp
lemma "LawBind3 bind_set" unfolding rel_defs set_defs comb_defs by auto


subsubsection \<open>Relation monad\<close>

(*In fact, the Rel('a,'b) type constructor also comes with a monad structure, which can be seen as 
 a kind of "monad composition" of the environment monad with the set monad.*)

abbreviation(input) unit_rel::"'a \<Rightarrow> Rel('b,'a)"
  where "unit_rel \<equiv> \<^bold>K \<circ> \<Q>"
abbreviation(input) fmap_rel::"('a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "fmap_rel \<equiv> \<^bold>B \<circ> image"
abbreviation(input) join_rel::"Rel('c,Rel('c,'a)) \<Rightarrow> Rel('c,'a)"
  where "join_rel \<equiv> \<^bold>W \<circ> (\<^bold>B \<Union>\<^sup>r)"
abbreviation(input) ap_rel::"Rel('c, 'a \<Rightarrow> 'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "ap_rel \<equiv> \<^bold>\<Phi>\<^sub>2\<^sub>1 (rightImage \<circ> intoRel)"
abbreviation(input) rbind_rel::"('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)"
  where "rbind_rel \<equiv> (\<^bold>\<Phi>\<^sub>2\<^sub>1 rightImage) \<circ> \<^bold>C" (*reversed bind*)

(*Again, we define the bind operation as 'flipped' rbind*)
abbreviation bind_rel::"Rel('c,'a) \<Rightarrow> ('a \<Rightarrow> Rel('c,'b)) \<Rightarrow> Rel('c,'b)"
  where "bind_rel \<equiv> \<^bold>C rbind_rel"

(*Some properties of monads in general*)
lemma "rbind_rel = join_rel \<circ>\<^sub>2 fmap_rel" unfolding rel_defs set_defs func_defs comb_defs by metis
lemma "join_rel = rbind_rel \<^bold>I" unfolding rel_defs set_defs func_defs comb_defs by metis
(*...*)

(*Note that for the relation monad we have*)
lemma "unit_rel = \<^bold>B unit_env unit_set" ..
lemma "fmap_rel = \<^bold>B fmap_env fmap_set" ..
lemma "ap_rel = \<^bold>\<Phi>\<^sub>2\<^sub>1 ap_set" ..
lemma "rbind_rel = \<^bold>B (\<^bold>C \<^bold>B \<^bold>C) \<^bold>\<Phi>\<^sub>2\<^sub>1 rbind_set" unfolding comb_defs ..
(*...*)

(*Finally, verify compliance with the monad laws*)
lemma "LawBind1 unit_rel bind_rel" unfolding rel_defs set_defs comb_defs by simp
lemma "LawBind2 unit_rel bind_rel" unfolding rel_defs set_defs comb_defs by simp
lemma "LawBind3 bind_rel" unfolding rel_defs set_defs comb_defs by auto

end