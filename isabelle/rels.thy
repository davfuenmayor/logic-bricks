theory rels (* A basic theory of relations (qua set-valued functions) *)
imports sets funcs
begin

section \<open>Relations\<close>

named_theorems rel_defs  (*container for related definitions*)

(*Analogously to sets, we define that a given relation holds of all, resp. at least one, pair or elements.*)
abbreviation(input) AllR::"Set(Rel('a,'b))" ("\<forall>\<^sup>r") 
  where "\<forall>\<^sup>rR \<equiv> \<forall>a b. R a b" (*i.e. \<forall>a. \<forall>(R a) or \<forall>(\<forall>\<circ>R)*)
abbreviation(input) ExR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r")
  where "\<exists>\<^sup>rR \<equiv> \<exists>a b. R a b" (*i.e. \<exists>a. \<exists>(R a) or \<exists>(\<exists>\<circ>R)*)

abbreviation NotExR::"Set(Rel('a,'b))" ("\<nexists>\<^sup>r") (*for convenience*)
  where "\<nexists>\<^sup>rR \<equiv> \<not>\<exists>\<^sup>rR"


subsection \<open>Algebraic structure\<close>

subsubsection \<open>Boolean structure\<close>
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

notation (input) complR ("(_)\<^sup>-") (* alternative superscript notation common in the literature *)
notation(output) complR ("'(_')\<^sup>-")

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


subsubsection \<open>Transpose and cotranspose\<close>

(*Relations come with two further idiosyncratic unary operations.
 The first one, "converse", naturally arises from an understanding of relations as binary operations
 (with boolean codomain) and corresponds to transposition (\<^bold>C combinator).
 The second one, which we call "cotransposition", corresponds to the transposition of the complement,
 (which is in fact identical to the complement of the transpose).*)

(*We reuse the existing notation to refer to the converse/transpose of a relation*)
lemma "\<^bold>R\<^sup>t = \<^bold>C \<^bold>R" unfolding comb_defs ..

(*We introduce convenient notation for the cotranspose*)
abbreviation cotranspose::"Rel('a,'b) \<Rightarrow> Rel('b,'a)" ("\<sim>\<^sup>r")
  where "\<sim>\<^sup>r \<equiv> \<midarrow>\<^sup>r \<circ> \<^bold>C"

notation(input) cotranspose  ("(_)\<^sup>\<sim>") (*convenient superscript notation*)

lemma "R\<^sup>\<sim> = R\<^sup>t\<^sup>-" unfolding comb_defs ..
lemma cotranspose_dual: "R\<^sup>\<sim> = R\<^sup>-\<^sup>t" unfolding comb_defs rel_defs set_defs ..
lemma cotranspose_involutive: "R\<^sup>\<sim>\<^sup>\<sim> = R" unfolding rel_defs set_defs comb_defs by simp


subsubsection \<open>Ordering structure\<close>
(*Similarly, relations also inherit the ordering structure of sets.*)

(*The algebra of relations is analogously ordered, via the 'subrelation' (endo)relation.*)
definition subrel::"ERel(Rel('a,'b))" (infixr "\<subseteq>\<^sup>r" 51) 
  where "(\<subseteq>\<^sup>r) \<equiv>  \<forall> \<circ>\<^sub>2 (\<^bold>\<Phi>\<^sub>2\<^sub>1(\<subseteq>))"
definition psubrel::"ERel(Rel('a,'b))" (infixr "\<subset>\<^sup>r" 51) (*proper subrelation*)
  where "(\<subset>\<^sup>r) \<equiv> (\<and>) \<circ>\<^sub>2 \<langle> (\<subseteq>\<^sup>r) , (\<exists>\<^sup>r \<circ>\<^sub>2 ((\<setminus>\<^sup>r)\<^sup>t)) \<rangle>"

lemma subrel_setdef: "R \<subseteq>\<^sup>r T = (\<forall>x. R x \<subseteq> T x)" unfolding subrel_def comb_defs ..
lemma "R \<subseteq>\<^sup>r T = (\<forall>x y. R x y \<rightarrow> T x y)" unfolding subrel_def set_defs comb_defs ..

declare subrel_def[rel_defs] psubrel_def[rel_defs]

(*It also holds that*)
lemma "(\<subseteq>\<^sup>r) = \<forall>\<^sup>r \<circ>\<^sub>2 (\<Rightarrow>\<^sup>r)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<subseteq>\<^sup>r T = \<forall>\<^sup>r(R \<Rightarrow>\<^sup>r T)" unfolding rel_defs set_defs comb_defs ..
lemma "R \<subset>\<^sup>r T = (R \<subseteq>\<^sup>r T \<and> \<exists>\<^sup>r(T \<setminus>\<^sup>r R))" unfolding rel_defs comb_defs ..
(*Note, however, that the following does not hold*)
lemma "R \<subset>\<^sup>r T \<longrightarrow> (\<forall>a. R a \<subset> T a)" nitpick oops (*countermodel*)
(*Only this holds:*)
lemma psubrel_prop1: "(\<forall>a. R a \<subset> T a) \<longrightarrow> R \<subset>\<^sup>r T" 
  unfolding rel_defs unfolding set_defs comb_defs by simp

(*Let us add the following convenient abbreviations for the reversed versions of (proper) subrel*)
abbreviation(input) superrel::"ERel(Rel('a,'b))" (infixr "\<supseteq>\<^sup>r" 51)
  where "(\<supseteq>\<^sup>r) \<equiv> (\<subseteq>\<^sup>r)\<^sup>t" 
abbreviation(input) psuperrel::"ERel(Rel('a,'b))" (infixr "\<supset>\<^sup>r" 51) (*proper superset*)
  where "(\<supset>\<^sup>r) \<equiv> (\<subset>\<^sup>r)\<^sup>t" 

(*As expected*)
lemma "(A \<supseteq>\<^sup>r B) = (B \<subseteq>\<^sup>r A)" unfolding comb_defs ..
lemma "(A \<supset>\<^sup>r B) = (B \<subset>\<^sup>r A)" unfolding comb_defs ..


(*Characterizing properties of relational bigunion and biginter*)
lemma biginterR_prop: "S R \<longrightarrow> \<Inter>\<^sup>rS \<subseteq>\<^sup>r R" 
  unfolding rel_defs set_defs func_defs comb_defs by auto
lemma bigunionR_prop: "S R \<longrightarrow> R \<subseteq>\<^sup>r \<Union>\<^sup>rS" 
  unfolding rel_defs set_defs func_defs comb_defs by auto

(*Two relations are said to 'overlap' (or 'intersect') if their intersection is non-empty*)
abbreviation(input) overlapR::"ERel(Rel('a,'b))" (infixr "\<sqinter>\<^sup>r" 52)
  where "(\<sqinter>\<^sup>r) \<equiv> \<exists>\<^sup>r \<circ>\<^sub>2 (\<inter>\<^sup>r)"
(*dually, two relations form a 'cover' if every pair belongs to one or the other *)
abbreviation(input) coverR::"ERel(Rel('a,'b))" (infixr "\<squnion>\<^sup>r" 53)
  where "(\<squnion>\<^sup>r) \<equiv> \<forall>\<^sup>r \<circ>\<^sub>2 (\<union>\<^sup>r)"

(*We say of a set of relations that it 'overlaps' (or 'intersects') if there exists a 'shared' pair.*)
abbreviation(input) bigoverlapR::"Set(Set(Rel('a,'b)))" ("\<Sqinter>\<^sup>r")
  where "\<Sqinter>\<^sup>r \<equiv> \<exists>\<^sup>r \<circ> \<Inter>\<^sup>r"
(*dually, a set of relations forms a 'cover' if every pair is contained in at least one of the relations.*)
abbreviation(input) bigcoverR::"Set(Set(Rel('a,'b)))" ("\<Squnion>\<^sup>r")
  where "\<Squnion>\<^sup>r \<equiv> \<forall>\<^sup>r \<circ> \<Union>\<^sup>r"

lemma "A \<sqinter>\<^sup>r B = \<exists>\<^sup>r(A \<inter>\<^sup>r B)" unfolding comb_defs ..
lemma "A \<sqinter>\<^sup>r B = (\<exists>x. A x \<sqinter> B x)" unfolding rel_defs comb_defs ..
lemma "A \<sqinter>\<^sup>r B = (\<exists>x y. (A x y \<and> B x y))" unfolding rel_defs set_defs comb_defs ..
lemma "A \<squnion>\<^sup>r B = \<forall>\<^sup>r(A \<union>\<^sup>r B)" unfolding comb_defs ..
lemma "A \<squnion>\<^sup>r B = (\<forall>x. A x \<squnion> B x)" unfolding rel_defs comb_defs ..
lemma "A \<squnion>\<^sup>r B = (\<forall>x y. A x y \<or> B x y)" unfolding rel_defs set_defs comb_defs ..

lemma "\<Sqinter>\<^sup>rS = \<exists>\<^sup>r(\<Inter>\<^sup>rS)" unfolding comb_defs ..
lemma "\<Squnion>\<^sup>rS = \<forall>\<^sup>r(\<Union>\<^sup>rS)" unfolding comb_defs ..


subsubsection \<open>Monoidal structure\<close>
(*We have seen the shared (boolean) algebraic structure between sets and relations. 
 We now explore their shared (monoidal) algebraic structure with functions.*)

(*Analogously to functions, relations can also be composed.*)
definition relComp::"Rel('b,'c) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('a,'c)" (infixl "\<circ>\<^sup>r" 55)
  where "(\<circ>\<^sup>r) =  \<^bold>C\<^sub>1\<^sub>4\<^sub>2\<^sub>3(\<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<sqinter>) \<^bold>C \<^bold>A)"

declare relComp_def[rel_defs]

lemma relComp_def2: "(\<circ>\<^sup>r) = \<^bold>C\<^sub>2\<^sub>3\<^sub>1\<^sub>4(\<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<sqinter>) \<^bold>A \<^bold>C)"
  unfolding rel_defs set_defs comb_defs by metis (*requires deep rewriting wrt \<sqinter>'s commutativity*)
lemma "R\<^sub>2 \<circ>\<^sup>r R\<^sub>1 = (\<lambda>a b. R\<^sub>1 a \<sqinter> R\<^sub>2\<^sup>t b)" 
  unfolding relComp_def2 set_defs comb_defs ..
lemma "R\<^sub>2 \<circ>\<^sup>r R\<^sub>1 = (\<lambda>a b. \<exists>c. R\<^sub>1 a c \<and> R\<^sub>2 c b)"
  unfolding relComp_def2 rel_defs set_defs comb_defs ..

(*Relation composition and identity satisfy the monoid conditions*)
lemma relComp_assoc: "(R \<circ>\<^sup>r T) \<circ>\<^sup>r V = R \<circ>\<^sup>r (T \<circ>\<^sup>r V)" (* associativity *)
  unfolding rel_defs set_defs comb_defs by auto                   
lemma relComp_idl: "\<Q> \<circ>\<^sup>r R = R"                     (* left identity *)
  unfolding rel_defs set_defs comb_defs by simp                   
lemma relComp_idr: "R \<circ>\<^sup>r \<Q> = R"                     (* right identity *)
  unfolding rel_defs set_defs comb_defs by simp   


(*For relations, we can in fact define an operator that acts as a 'dual' to relation-composition*)
definition relCompDual::"Rel('a,'b) \<Rightarrow> Rel('c,'a) \<Rightarrow> Rel('c,'b)" (infixl "\<bullet>\<^sup>r" 55)
  where "(\<bullet>\<^sup>r) \<equiv>  \<^bold>C\<^sub>1\<^sub>4\<^sub>2\<^sub>3(\<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<squnion>) \<^bold>C \<^bold>A)"

declare relCompDual_def[rel_defs]

lemma relCompDual_def2: "(\<bullet>\<^sup>r) = \<^bold>C\<^sub>2\<^sub>3\<^sub>1\<^sub>4(\<^bold>B\<^sub>2\<^sub>2\<^sub>2 (\<squnion>) \<^bold>A \<^bold>C)"
  unfolding rel_defs set_defs comb_defs by metis (*requires deep rewriting wrt \<squnion>'s commutativity*)
lemma "R\<^sub>2 \<bullet>\<^sup>r R\<^sub>1 = (\<lambda>a b. R\<^sub>1 a \<squnion> R\<^sub>2\<^sup>t b)" 
  unfolding relCompDual_def2 set_defs comb_defs ..
lemma "R\<^sub>2 \<bullet>\<^sup>r R\<^sub>1 = (\<lambda>a b. \<forall>c. R\<^sub>1 a c \<or> R\<^sub>2 c b)"
  unfolding relCompDual_def2 set_defs comb_defs ..

(*Relation composition and identity satisfy the monoid conditions*)
lemma relCompDual_assoc: "(R \<bullet>\<^sup>r T) \<bullet>\<^sup>r V = R \<bullet>\<^sup>r (T \<bullet>\<^sup>r V)" (* associativity *)
  unfolding rel_defs set_defs comb_defs by auto                   
lemma relCompDual_idl: "\<D> \<bullet>\<^sup>r R = R"                     (* left identity *)
  unfolding rel_defs set_defs comb_defs by simp                   
lemma relCompDual_idr: "R \<bullet>\<^sup>r \<D> = R"                     (* right identity *)
  unfolding rel_defs set_defs comb_defs by auto  

lemma relCompDuality1: "R \<bullet>\<^sup>r T = ((R\<^sup>-) \<circ>\<^sup>r (T\<^sup>-))\<^sup>-" 
  unfolding rel_defs set_defs comb_defs by auto
lemma relCompDuality2: "R \<circ>\<^sup>r T = ((R\<^sup>-) \<bullet>\<^sup>r (T\<^sup>-))\<^sup>-" 
  unfolding rel_defs set_defs comb_defs by auto


(*Finally, we introduce an convenient 'flipped' notation for composition (analogously to functions)*)
abbreviation(input) relComp_t::"Rel('a,'b) \<Rightarrow> Rel('b,'c) \<Rightarrow> Rel('a,'c)" (infixr ";\<^sup>r" 55)
  where "R ;\<^sup>r T \<equiv> T \<circ>\<^sup>r R"

lemma "R\<^sub>1 ;\<^sup>r R\<^sub>2 = (\<lambda>a b. R\<^sub>1 a \<sqinter> R\<^sub>2\<^sup>t b)" 
  unfolding relComp_def2 set_defs comb_defs ..


subsection \<open>Cartesian-Product and Disjoint-Sum\<close>

definition product::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<times>" 90)
  where "(\<times>) \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<and>)"
definition sum::"Set('a) \<Rightarrow> Set('b) \<Rightarrow> Rel('a,'b)" (infixl "\<uplus>" 90)
  where "(\<uplus>) \<equiv> \<^bold>B\<^sub>2\<^sub>1\<^sub>1 (\<or>)"

declare product_def[rel_defs] sum_def[rel_defs]

lemma "A \<times> B = (\<lambda>x y. A x \<and> B y)" unfolding rel_defs comb_defs ..
lemma "A \<uplus> B = (\<lambda>x y. A x \<or> B y)" unfolding rel_defs comb_defs ..


subsection \<open>Lower and upper (aka. left resp. right) ranges of relations\<close>

(*For a relation R we define its lower- (resp. upper-) range as the set of those objects in the 
 source (resp. target) that reach to (are reached by) some element in the target (resp. source)*)
definition lowerRange::"Rel('a,'b) \<Rightarrow> Set('a)"
  where "lowerRange \<equiv> \<exists> \<circ>\<^sub>2 \<^bold>A"
definition upperRange::"Rel('a,'b) \<Rightarrow> Set('b)"
  where "upperRange \<equiv> \<exists> \<circ>\<^sub>2 \<^bold>C"

lemma "lowerRange R a = (\<exists>x. R a x)" unfolding lowerRange_def comb_defs ..
lemma "upperRange R b = (\<exists>x. R x b)" unfolding upperRange_def comb_defs ..

declare lowerRange_def[rel_defs] upperRange_def[rel_defs]


subsection \<open>Constructing relations\<close>

(*The counterparts of singleton-sets are 'singleton-relations' (we reserve the word 'pair' for another notion)*)
abbreviation(input) mk_singletonR::"'a \<Rightarrow> 'b \<Rightarrow> Rel('a,'b)" ("\<lblot>_,_\<rblot>")
  where \<open>\<lblot>a,b\<rblot> \<equiv> \<lambda>x y. x = a \<and> y = b\<close>
(*...*)


subsection \<open>Basic properties/predicates on relations\<close>

definition uniqueR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r\<^sub>\<le>\<^sub>1") (*R holds of at most one pair of elements (may hold of none)*)
  where \<open>\<exists>\<^sup>r\<^sub>\<le>\<^sub>1 R \<equiv> \<forall>a b x y. (R a b \<and> R x y) \<rightarrow> (a = x \<and> b = y)\<close>
definition singletonR::"Set(Rel('a,'b))" ("\<exists>\<^sup>r\<^sub>1") (*R holds of exactly one pair of elements*)
  where \<open>\<exists>\<^sup>r\<^sub>1 R \<equiv> \<exists>x y. R x y \<and> (\<forall>a b. R a b \<rightarrow> (a = x \<and> b = y))\<close>
(*...*)

declare uniqueR_def[rel_defs] singletonR_def[rel_defs]

lemma singletonR_def2: "\<exists>\<^sup>r\<^sub>1 R = (\<exists>\<^sup>r R \<and> \<exists>\<^sup>r\<^sub>\<le>\<^sub>1 R)"
  unfolding rel_defs by blast
lemma singletonR_def3: "\<exists>\<^sup>r\<^sub>1A = (\<exists>a b. A = \<lblot>a,b\<rblot>)"
  unfolding singletonR_def2 unfolding rel_defs by blast


end