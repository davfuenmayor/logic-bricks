theory rels (* A basic theory of relations (qua set-valued functions) *)
imports sets funcs
begin

section \<open>Relations\<close>

named_theorems rel_defs  (*container for related definitions*)
named_theorems rel_simps (*container for related simplification rules*)

(*Analogously to sets, we define that a given relation holds of all, resp. at least one, pair or elements.*)
abbreviation(input) AllR::"Set(Rel('a,'b))" ("\<forall>\<^sup>r") 
  where "\<forall>\<^sup>rR \<equiv> \<forall>a b. R a b" (*i.e. \<forall>a. \<forall>(R a) resp. \<forall>(\<forall>\<circ>R) resp. \<^bold>B\<forall>(\<^bold>B\<forall>)*)
abbreviation(input) ExR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r")
  where "\<exists>\<^sup>rR \<equiv> \<exists>a b. R a b" (*i.e. \<exists>a. \<exists>(R a) resp. \<exists>(\<exists>\<circ>R) resp. \<^bold>B\<exists>(\<^bold>B\<exists>)*)

abbreviation NotExR::"Set(Rel('a,'b))" ("\<nexists>\<^sup>r") (*for convenience*)
  where "\<nexists>\<^sup>rR \<equiv> \<not>\<exists>\<^sup>rR"


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

(*For the left we have in fact that*)
lemma leftRange_def2: "leftRange = \<^bold>B \<exists>" unfolding rel_defs comb_defs ..
lemma leftDualRange_def2: "leftDualRange = \<^bold>B \<forall>" unfolding rel_defs comb_defs ..



subsection \<open>Boolean structure\<close>

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


abbreviation(input) superrel::"ERel(Rel('a,'b))" (infixr "\<supseteq>\<^sup>r" 51) (*convenient notation*)
  where "A \<supseteq>\<^sup>r B \<equiv> B \<subseteq>\<^sup>r A" 

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


subsection \<open>Transpose and cotranspose\<close>

(*Relations come with two further idiosyncratic unary operations.
 The first one, "converse", naturally arises from an understanding of relations as binary operations
 (with boolean codomain) and corresponds to transposition (\<^bold>C combinator).
 The second one, which we call "cotransposition", corresponds to the transposition of the complement,
 (which is in fact identical to the complement of the transpose).*)

(*We reuse the existing notation to refer to the converse/reverse/transpose of a relation*)
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


subsection \<open>Monoidal structure\<close>
(*We have seen the shared (boolean) algebraic structure between sets and relations. 
 We now explore their shared (monoidal) algebraic structure with functions.*)

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


subsection \<open>Constructing relations\<close>

(*Out of pairs of elements: pair and copair*)
definition pair::"'a \<Rightarrow> 'b \<Rightarrow> Rel('a,'b)" ("\<langle>_,_\<rangle>")
  where \<open>pair \<equiv> \<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<and>) \<Q> \<Q>\<close> (*relational counterpart of 'singleton'*)
definition copair::"'a \<Rightarrow> 'b \<Rightarrow> Rel('a,'b)" ("\<lblot>_,_\<rblot>")
  where \<open>copair \<equiv> \<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<or>) \<D> \<D>\<close> (*relational counterpart of 'cosingleton'*)

declare pair_def[rel_defs] copair_def[rel_defs]

lemma "\<langle>a,b\<rangle> = (\<lambda>x y. a = x \<and> b = y)" unfolding rel_defs comb_defs ..
lemma "\<lblot>a,b\<rblot> = (\<lambda>x y. a \<noteq> x \<or> b \<noteq> y)" unfolding rel_defs comb_defs ..

(*Pairs and copairs are related via relation-complement as expected*)
lemma "\<midarrow>\<^sup>r\<lblot>a,b\<rblot> = \<langle>a,b\<rangle>" unfolding rel_defs set_defs comb_defs by simp


(*Out of pairs of sets: (cartesian) product and (disjoint) sum*)
definition product::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<times>" 90)
  where "(\<times>) \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<and>)"
definition sum::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<uplus>" 90)
  where "(\<uplus>) \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<or>)"

declare product_def[rel_defs] sum_def[rel_defs]

lemma "A \<times> B = (\<lambda>x y. A x \<and> B y)" unfolding rel_defs comb_defs ..
lemma "A \<uplus> B = (\<lambda>x y. A x \<or> B y)" unfolding rel_defs comb_defs ..

(*Pair and copair can be defined in terms of product and sum respectively*)
lemma "\<langle>a,b\<rangle> = \<Q> a \<times> \<Q> b" unfolding rel_defs comb_defs ..
lemma "\<lblot>a,b\<rblot> = \<D> a \<uplus> \<D> b" unfolding rel_defs comb_defs ..

end