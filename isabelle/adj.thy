theory adj
 imports diagrams endorels
begin

named_theorems adj_defs

section \<open>Adjunctions\<close>
(*The term "adjunction" is quite overloaded in the literature. Here we consider two flavors:
1) Galois-connections (aka. dual-adjunctions or Galois-adjunctions), which are contravariant. 
2) Adjunctions (aka. residuations), which are covariant. We refer to them just as "adjunctions" (simpliciter)*)

subsection \<open>Galois-connections\<close>

(*Galois-connections (aka. Galois- or dual-adjunctions) relate pairs of functions (having flipped domain-codomain) 
 wrt. a pair of endorelations (usually orderings on the functions' domains). We focus in this section on
 the traditional notion of 'contravariant' Galois-connection wrt. a pair of arbitrary relations R\<^sub>1 and R\<^sub>2.
 Note that a 'covariant' version, aka. adjunction (simpliciter), can always be defined by reversing R\<^sub>2 below.*)

subsubsection \<open>Relational version\<close>

(*We introduce a convenient notion of 'relational Galois-connection' relating a given pair of relations
 F & G wrt. another pair of relations R\<^sub>1 & R\<^sub>2 (as parameters). This generalizes the traditional 'functional'
 notion, while sidestepping the use of descriptions and their associated existence/uniqueness assumptions.*)
definition relGalois::"Rel('a,'b) \<Rightarrow> Rel('c,'d) \<Rightarrow> Rel('a,'d) \<Rightarrow> Rel('c,'b) \<Rightarrow> o" ("_,_-GAL\<^sup>r")
  where "R\<^sub>1,R\<^sub>2-GAL\<^sup>r F G \<equiv>  \<sqdot> \<midarrow>R\<^sub>2 \<rightarrow> \<sqdot> 
                          G\<down>        \<down>F\<^sup>\<smile>
                           \<sqdot> \<midarrow>R\<^sub>1\<^sup>\<smile>\<rightarrow> \<sqdot>  "

declare relGalois_def[adj_defs]

(*We get a more intuitive representation for Galois-connections by rotating the above (square) diagram
 by 90\<degree> clockwise. Note that in such "Galois diagrams" composition is read along the SW–NE diagonal!*)
abbreviation(input) relGaloisDiagram (" \<sqdot> \<leftarrow>_\<midarrow> \<sqdot> // _\<up> \<down>_ // \<sqdot> \<midarrow>_\<rightarrow> \<sqdot>") 
  where  " \<sqdot> \<leftarrow>G\<midarrow> \<sqdot> 
         R\<^sub>1\<up>      \<down>R\<^sub>2
           \<sqdot> \<midarrow>F\<rightarrow> \<sqdot>   \<equiv> R\<^sub>1,R\<^sub>2-GAL\<^sup>r F G"

lemma relGalois_def2:  " \<sqdot> \<leftarrow>G\<midarrow> \<sqdot> 
                       R\<^sub>1\<up>      \<down>R\<^sub>2
                         \<sqdot> \<midarrow>F\<rightarrow> \<sqdot>   = (F ;\<^sup>r (R\<^sub>2\<^sup>\<smile>) = R\<^sub>1 ;\<^sup>r (G\<^sup>\<smile>))"
  unfolding adj_defs rel_defs func_defs comb_defs by meson

(* An alternative definition *)
lemma relGalois_altdef: "relGalois = \<^bold>C (\<^bold>B\<^sub>2\<^sub>2 \<Q> relPullback (\<^bold>C relPullback))" unfolding adj_defs rel_defs comb_defs by metis
lemma "R\<^sub>1,R\<^sub>2-GAL\<^sup>r = (\<lambda>F G. \<Q> (relPullback R\<^sub>2 F) (\<^bold>C relPullback R\<^sub>1 G))" unfolding relGalois_altdef comb_defs ..
lemma "R\<^sub>1,R\<^sub>2-GAL\<^sup>r = (\<lambda>F G. relPullback R\<^sub>2 F = relPullback G R\<^sub>1)" unfolding relGalois_altdef comb_defs ..
lemma "R\<^sub>1,R\<^sub>2-GAL\<^sup>r = (\<lambda>F G. \<forall>b a. relPullback R\<^sub>2 F b a \<leftrightarrow> relPullback G R\<^sub>1 b a)" unfolding relGalois_altdef comb_defs by fastforce
lemma relGalois_setdef: "R\<^sub>1,R\<^sub>2-GAL\<^sup>r = (\<lambda>F G. \<forall>a b. (R\<^sub>2 b \<sqinter> F a) \<leftrightarrow> (G b \<sqinter> R\<^sub>1 a))" unfolding relGalois_altdef rel_defs comb_defs by metis

(*Galois-connections are clearly 'symmetric' in the following sense*)
lemma relGalois_symm: "R\<^sub>1,R\<^sub>2-GAL\<^sup>r F G = R\<^sub>2,R\<^sub>1-GAL\<^sup>r G F"
  by (metis relComp_antihom relGalois_def2 transpose_involutive)

(*Galois-connections and dualities are intertranslatable in several ways*)
lemma "R\<^sub>1,R\<^sub>2-GAL\<^sup>r  F G = R\<^sub>1,R\<^sub>2\<^sup>\<smile>-DUAL\<^sup>r F (G\<^sup>\<smile>)" unfolding adj_defs rel_defs func_defs comb_defs by meson
lemma "n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T = n\<^sub>1,n\<^sub>2\<^sup>\<smile>-GAL\<^sup>r  R (T\<^sup>\<smile>)" unfolding adj_defs rel_defs func_defs comb_defs by meson
lemma "R\<^sub>1,R\<^sub>2-GAL\<^sup>r  F G =  F,G\<^sup>\<smile>-DUAL\<^sup>r R\<^sub>1 (R\<^sub>2\<^sup>\<smile>)" unfolding adj_defs rel_defs func_defs comb_defs by meson
lemma "n\<^sub>1,n\<^sub>2-DUAL\<^sup>r R T =  R,T\<^sup>\<smile>-GAL\<^sup>r  n\<^sub>1 (n\<^sub>2\<^sup>\<smile>)" unfolding adj_defs rel_defs func_defs comb_defs by meson

(*Drawing upon the above, we can sketch solutions to the problem of finding a right/left adjoint to 
 a given relation, for those particular cases where R\<^sub>1/R\<^sub>2 have sections or retractions*)
lemma "relSplitting R\<^sub>1 m \<Longrightarrow> R\<^sub>1,R\<^sub>2-GAL\<^sup>r F (R\<^sub>2 ;\<^sup>r (F\<^sup>\<smile>) ;\<^sup>r (m\<^sup>\<smile>))"
  unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma "relSplitting R\<^sub>2 m \<Longrightarrow> R\<^sub>1,R\<^sub>2-GAL\<^sup>r (R\<^sub>1 ;\<^sup>r (G\<^sup>\<smile>) ;\<^sup>r (m\<^sup>\<smile>)) G"
  unfolding adj_defs rel_defs comb_defs func_defs by metis

(*For the (very common) particular case where R\<^sub>1 and R\<^sub>2 are endorelations (possibly on different types),
 we can introduce the following operation (parameterized with R\<^sub>1 & R\<^sub>2) that given a relation F returns
 another relation G, its Galois 'adjoint', so that F and G form a Galois-connection (wrt. R\<^sub>1 & R\<^sub>2)*)
definition relAdjoint::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Rel('a,'b) \<Rightarrow> Rel('b,'a)" ("_,_-adj\<^sup>r")
  where "relAdjoint \<equiv> \<^bold>B\<^sub>1\<^sub>1 \<^bold>I (\<^bold>E lub) relPullback"

declare relAdjoint_def[adj_defs]

lemma "R\<^sub>1,R\<^sub>2-adj\<^sup>r = (\<^bold>E lub R\<^sub>1) (relPullback R\<^sub>2)" unfolding adj_defs comb_defs ..
lemma relAdjoint_setdef: "R\<^sub>1,R\<^sub>2-adj\<^sup>r F = (\<lambda>b. (R\<^sub>1-lub (\<lambda>a. R\<^sub>2 b \<sqinter> F a)))" unfolding adj_defs comb_defs relPullback_def ..

(*Some useful things can be said of adjoints already in this general (relational) case*)
lemma "antisymmetric R\<^sub>1 \<Longrightarrow> rightUnique F \<Longrightarrow> rightUnique (R\<^sub>1,R\<^sub>2-adj\<^sup>r F)" (*right-uniqueness preservation*)
  unfolding adj_defs comb_defs by (simp add: B1_comb_def \<Phi>21_comb_def antisymm_greatest_unique antisymmetric_symm deterministic_def glb_def lub_defT rightUnique_def)
(*... more*)

(*An interesting question is that of determining minimal conditions under which the previous definition
 behaves as expected. A partial solution is provided below for illustration, where it remains to find
 out under which conditions a relation F has a Galois adjoint that is a total function. A real answer 
 for the general case is left as exercise (solving for particular cases will be enough later on). *)
lemma relGalois_prop: "skeletal R\<^sub>1 \<Longrightarrow> \<exists>(R\<^sub>1,R\<^sub>2-GAL\<^sup>r F \<inter> totalFunction) 
                              \<Longrightarrow> R\<^sub>1,R\<^sub>2-GAL\<^sup>r F (R\<^sub>1,R\<^sub>2-adj\<^sup>r F)"
  unfolding adj_defs endorel_defs func_defs rel_defs comb_defs
  apply (rule ext)+ apply auto apply (metis (no_types, opaque_lifting)) by (smt (verit, best)) 

(*The related question of uniqueness of Galois adjoints (when they exist) is simpler*)
lemma relGalois_rightUnique: "skeletal R\<^sub>1 \<Longrightarrow> !((R\<^sub>1,R\<^sub>2-GAL\<^sup>r F) \<inter> rightUnique)" 
  oops (*TODO: fix reconstruction*)


subsection \<open>Functional version\<close>

(*We now move towards the notion of (functional) Galois-connections, still slightly generalized, 
 such that it relates pairs of functions f & g wrt a pair of arbitrary relations R\<^sub>1 & R\<^sub>2.
 We encode this notion as a particular case of the relational Galois-connection discussed above. *)
definition galois::"Rel('a,'b) \<Rightarrow> Rel('c,'d) \<Rightarrow> Rel(('a \<Rightarrow>'d),('c \<Rightarrow> 'b))" ("_,_-GAL")
  where "galois \<equiv> \<^bold>B\<^sub>1\<^sub>1\<^sub>1\<^sub>1 relGalois \<^bold>I \<^bold>I asRel asRel"

declare galois_def[adj_defs]

lemma "R\<^sub>1,R\<^sub>2-GAL f g = R\<^sub>1,R\<^sub>2-GAL\<^sup>r (asRel f) (asRel g)" unfolding adj_defs comb_defs ..
lemma "R\<^sub>1,R\<^sub>2-GAL f g = (\<forall>b a. R\<^sub>2 b \<sqinter> {f a} = {g b} \<sqinter> R\<^sub>1 a)" unfolding adj_defs rel_defs func_defs comb_defs by metis

(*We also introduce a convenient diagram notation for functional Galois connections*)
abbreviation(input) galoisDiagram (" \<sqdot> \<leftarrow>_\<midarrow> \<sqdot> // _\<up> \<down>_ // \<sqdot> \<midarrow>_\<rightarrow> \<sqdot>") 
  where  " \<sqdot> \<leftarrow>g\<midarrow> \<sqdot> 
         R\<^sub>1\<up>      \<down>R\<^sub>2
           \<sqdot> \<midarrow>f\<rightarrow> \<sqdot>   \<equiv> R\<^sub>1,R\<^sub>2-GAL f g"

lemma galois_def2: " \<sqdot> \<leftarrow>g\<midarrow> \<sqdot> 
                   R\<^sub>1\<up>      \<down>R\<^sub>2
                     \<sqdot> \<midarrow>f\<rightarrow> \<sqdot>   = (\<forall>a b. R\<^sub>2 b (f a) \<leftrightarrow> R\<^sub>1 a (g b))" 
  unfolding adj_defs rel_defs func_defs comb_defs by metis

(* An alternative definition *)
lemma galois_altdef: "galois = \<^bold>C (\<^bold>B\<^sub>2\<^sub>2 \<Q> (\<^bold>B\<^sub>1\<^sub>1 \<^bold>I) (\<^bold>C \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 \<^bold>I)))" unfolding galois_def2 comb_defs by metis
lemma "R\<^sub>1,R\<^sub>2-GAL f g = ((\<^bold>B\<^sub>1\<^sub>1 \<^bold>I) R\<^sub>2 f = (\<^bold>C \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 \<^bold>I)) R\<^sub>1 g)" unfolding galois_altdef comb_defs ..
lemma "R\<^sub>1,R\<^sub>2-GAL f g = (\<forall>a b. (\<^bold>B\<^sub>1\<^sub>1 \<^bold>I) R\<^sub>2 f a b \<leftrightarrow> (\<^bold>C \<circ>\<^sub>2 (\<^bold>B\<^sub>1\<^sub>1 \<^bold>I)) R\<^sub>1 g a b)" unfolding galois_altdef comb_defs by metis
lemma "R\<^sub>1,R\<^sub>2-GAL f g = (relPullback R\<^sub>2 (asRel f) = relPullback (asRel g) R\<^sub>1)" unfolding galois_altdef relGalois_altdef comb_defs rel_defs func_defs comb_defs by simp

(*Again, Galois-connections are 'symmetric' in the following sense*)
lemma galois_symm: "R\<^sub>1,R\<^sub>2-GAL f g = R\<^sub>2,R\<^sub>1-GAL g f" unfolding adj_defs rel_defs func_defs comb_defs by metis

(*For the (very common) particular case where R\<^sub>1 and R\<^sub>2 are endorelations (possibly on different types),
 we can introduce the following operation (parameterized with R\<^sub>1 and R\<^sub>2) that given a function f 
 returns another relation g, its 'adjoint', so that f and g form a Galois-connection (wrt. R\<^sub>1 and R\<^sub>2)*)
definition adjoint::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Op('a,'b) \<Rightarrow> Op('b,'a)" ("_,_-adj")
  where "adjoint \<equiv> (\<^bold>B\<^sub>3 \<iota>) \<circ> ((\<^bold>B\<^sub>1\<^sub>3 \<^bold>I lub) (\<^bold>B\<^sub>1\<^sub>1 \<^bold>I)) "

declare adjoint_def[adj_defs]

lemma "R\<^sub>1,R\<^sub>2-adj f = (\<lambda>b. \<iota> (R\<^sub>1-lub (\<lambda>a. R\<^sub>2 b (f a))))" unfolding adj_defs comb_defs ..

(*As mentioned previously, (covariant) adjunctions can be encoded by reversing the parameter R\<^sub>2*)
abbreviation(input) adjunction::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Rel(Op('a,'b),Op('b,'a))" ("_,_-ADJ")
  where "R\<^sub>1,R\<^sub>2-ADJ \<equiv> R\<^sub>1,R\<^sub>2\<^sup>\<smile>-GAL" 

(*We also introduce a convenient diagram notation for adjunctions (with a reversed right arrow)*)
abbreviation(input) adjunctionDiagram (" \<sqdot> \<leftarrow>_\<midarrow> \<sqdot> // _\<up> \<up>_ // \<sqdot> \<midarrow>_\<rightarrow> \<sqdot>") 
  where  " \<sqdot> \<leftarrow>g\<midarrow> \<sqdot> 
         R\<^sub>1\<up>      \<up>R\<^sub>2
           \<sqdot> \<midarrow>f\<rightarrow> \<sqdot>   \<equiv> R\<^sub>1,R\<^sub>2-ADJ f g"

lemma adjunction_def2: " \<sqdot> \<leftarrow>g\<midarrow> \<sqdot> 
                       R\<^sub>1\<up>      \<up>R\<^sub>2
                         \<sqdot> \<midarrow>f\<rightarrow> \<sqdot>   = (\<forall>a b. R\<^sub>2 (f a) b \<leftrightarrow> R\<^sub>1 a (g b))" 
  unfolding adj_defs rel_defs func_defs comb_defs by metis

(*Note that the (covariant) adjunction is not 'symmetric' in the sense the Galois-connection is*)
lemma "R\<^sub>1,R\<^sub>2-ADJ f g = R\<^sub>2,R\<^sub>1-ADJ g f" nitpick oops (*countermodel*)

(*A possible explanation for the adjectives 'covariant' and 'contravariant'*)
lemma "preorder R \<Longrightarrow> R,R-ADJ f g \<Longrightarrow> R-MONO g" 
  unfolding adj_defs preorder_def2 rel_defs func_defs comb_defs by metis
lemma "preorder R \<Longrightarrow> R,R-GAL f g \<Longrightarrow> R-ANTI g" 
  unfolding adj_defs preorder_def2 rel_defs func_defs comb_defs by metis

(*Hence, when working with (covariant) adjunctions we need to introduce two operations (parameterized 
 with R\<^sub>1 and R\<^sub>2) which when given functions f resp. g return their 'right' resp. 'left' adjoint.*)
abbreviation(input) rightAdjoint::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Op('a,'b) \<Rightarrow> Op('b,'a)" ("_,_-rightAdj")
  where "R\<^sub>1,R\<^sub>2-rightAdj \<equiv> R\<^sub>1,R\<^sub>2\<^sup>\<smile>-adj"
abbreviation(input) leftAdjoint::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Op('b,'a) \<Rightarrow> Op('a,'b)" ("_,_-leftAdj")
  where "R\<^sub>1,R\<^sub>2-leftAdj \<equiv> R\<^sub>2\<^sup>\<smile>,R\<^sub>1-adj"

lemma "R\<^sub>1,R\<^sub>2-rightAdj f = (\<lambda>b. \<iota> (R\<^sub>1-lub (\<lambda>a. R\<^sub>2 (f a) b)))" unfolding adj_defs rel_defs comb_defs ..
lemma "R\<^sub>1,R\<^sub>2-leftAdj g = (\<lambda>a. \<iota> (R\<^sub>2-glb (\<lambda>b. R\<^sub>1 a (g b))))" unfolding adj_defs glb_defT comb_defs ..
  
lemma "R\<^sub>1,R\<^sub>2-leftAdj = R\<^sub>2\<^sup>\<smile>,R\<^sub>1\<^sup>\<smile>-rightAdj" by (simp add: transpose_involutive)

(*Our adjoint operator behaves as expected for those functions that have indeed some adjoint (again,
 we still have to find out under which minimal conditions such adjoints exist for the general case).*)
lemma galois_prop: "skeletal R\<^sub>1 \<Longrightarrow> \<exists>(R\<^sub>1,R\<^sub>2-GAL f) \<Longrightarrow> R\<^sub>1,R\<^sub>2-GAL f (R\<^sub>1,R\<^sub>2-adj f)"
  unfolding adj_defs skeletal_def2 reflexive_def4 antisymmetric_reldef comb_defs
  unfolding endorel_defs rel_defs  func_defs comb_defs apply (rule ext)+  oops (*TODO: reconstruct*)

(*We can conveniently extend the previous definitions towards indexed functions (e.g. binary endooperations) *)
definition galois2::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Rel('e-Env(Op('a,'b)),'e-Env(Op('b,'a)))" ("_,_-GAL\<^sub>2")
  where "R\<^sub>1,R\<^sub>2-GAL\<^sub>2 \<equiv> \<^bold>\<Phi>\<^sub>\<forall> (R\<^sub>1,R\<^sub>2-GAL)"
abbreviation(input) adjunction2::"ERel('a) \<Rightarrow> ERel('b) \<Rightarrow> Rel('e-Env(Op('a,'b)),'e-Env(Op('b,'a)))" ("_,_-ADJ\<^sub>2")
  where "R\<^sub>1,R\<^sub>2-ADJ\<^sub>2 \<equiv> R\<^sub>1,R\<^sub>2\<^sup>\<smile>-GAL\<^sub>2"

declare galois2_def[adj_defs]

lemma    "R\<^sub>1,R\<^sub>2-GAL\<^sub>2 f g = (\<forall>x. R\<^sub>1,R\<^sub>2-GAL (f x) (g x))" unfolding relLiftAll_def adj_defs comb_defs ..
lemma "R\<^sub>1,R\<^sub>2-ADJ\<^sub>2 f g = (\<forall>x. R\<^sub>1,R\<^sub>2-ADJ (f x) (g x))" unfolding relLiftAll_def adj_defs comb_defs ..
lemma    "R\<^sub>1,R\<^sub>2-GAL\<^sub>2 f g = (\<forall>a b c. R\<^sub>2 b (f c a) \<leftrightarrow> R\<^sub>1 a (g c b))" unfolding adj_defs rel_defs func_defs comb_defs by metis
lemma "R\<^sub>1,R\<^sub>2-ADJ\<^sub>2 f g = (\<forall>a b c. R\<^sub>2 (f c a) b \<leftrightarrow> R\<^sub>1 a (g c b))" unfolding adj_defs rel_defs func_defs comb_defs by metis
(*For instance, in the case of subset ordering*)
lemma    "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 f g = (\<forall>a b c. b \<subseteq> (f c) a \<leftrightarrow> a \<subseteq> (g c) b)" unfolding adj_defs rel_defs func_defs comb_defs oops
lemma "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 f g = (\<forall>a b c. (f c) a \<subseteq> b \<leftrightarrow> a \<subseteq> (g c) b)" unfolding adj_defs rel_defs func_defs comb_defs oops


(*A convenient 'lifting' rule for (Galois) and adjunctions (and for any arities)*)
lemma galois_lift1: "R\<^sub>1,R\<^sub>2-GAL f g \<Longrightarrow> (\<^bold>\<Phi>\<^sub>\<forall> R\<^sub>1),(\<^bold>\<Phi>\<^sub>\<forall> R\<^sub>2)-GAL (\<^bold>\<Phi>\<^sub>1\<^sub>1 f) (\<^bold>\<Phi>\<^sub>1\<^sub>1 g)"
  by (simp add: B1_comb_def B3_comb_def \<Phi>21_comb_def galois_def2 relLiftAll_def)
lemma adjunction_lift1: "R\<^sub>1,R\<^sub>2-ADJ f g \<Longrightarrow> (\<^bold>\<Phi>\<^sub>\<forall> R\<^sub>1),(\<^bold>\<Phi>\<^sub>\<forall> R\<^sub>2)-ADJ (\<^bold>\<Phi>\<^sub>1\<^sub>1 f) (\<^bold>\<Phi>\<^sub>1\<^sub>1 g)"
  by (simp add: B1_comb_def B3_comb_def \<Phi>21_comb_def adjunction_def2 relLiftAll_def)

lemma galois_lift2: "R\<^sub>1,R\<^sub>2-GAL\<^sub>2 f g \<Longrightarrow> (\<^bold>\<Phi>\<^sub>\<forall> R\<^sub>1),(\<^bold>\<Phi>\<^sub>\<forall> R\<^sub>2)-GAL\<^sub>2 (\<^bold>\<Phi>\<^sub>2\<^sub>1 f) (\<^bold>\<Phi>\<^sub>2\<^sub>1 g)"
  by (simp add: B3_comb_def \<Phi>21_comb_def galois_def2 relLiftAll_def galois2_def)
lemma adjunction_lift2: "R\<^sub>1,R\<^sub>2-ADJ\<^sub>2 f g \<Longrightarrow> (\<^bold>\<Phi>\<^sub>\<forall> R\<^sub>1),(\<^bold>\<Phi>\<^sub>\<forall> R\<^sub>2)-ADJ\<^sub>2 (\<^bold>\<Phi>\<^sub>2\<^sub>1 f) (\<^bold>\<Phi>\<^sub>2\<^sub>1 g)"
  using galois_lift2 by (metis relLiftAll_trans)


subsection \<open>Concrete examples\<close>

(*Integer addition and substraction form a Galois-connection wrt equality and an adjunction wrt inequality*)
lemma "\<Q>,\<Q>-GAL (\<lambda>x::int. x + a) (\<lambda>x. x - a)" unfolding adj_defs rel_defs func_defs comb_defs by fastforce
lemma "(\<le>),(\<le>)-ADJ (\<lambda>x::int. x + a) (\<lambda>x. x - a)" unfolding adj_defs rel_defs func_defs comb_defs by (simp add: le_diff_eq)
(*Symmetric difference is self-adjoint wrt equality (but not wrt inequality)*)
lemma "\<Q>,\<Q>-GAL ((\<triangle>) a) ((\<triangle>) a)" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "(\<subseteq>),(\<subseteq>)-GAL ((\<triangle>) a) ((\<triangle>) a)" nitpick oops (*counterexample*)
lemma "(\<subseteq>),(\<subseteq>)-ADJ ((\<triangle>) a) ((\<triangle>) a)" nitpick oops (*counterexample*)

lemma "(\<le>)-MONO (f::int\<Rightarrow>int) \<Longrightarrow> \<Q>,\<Q>-GAL f g \<Longrightarrow> (\<le>),(\<le>)-ADJ f g"
  unfolding adj_defs rel_defs func_defs comb_defs by (metis nle_le)
lemma "(\<le>),(\<le>)-ADJ (f::int\<Rightarrow>int) (g::int\<Rightarrow>int) \<Longrightarrow> \<Q>,\<Q>-GAL f g"
  unfolding adj_defs rel_defs func_defs comb_defs apply (rule ext)+ apply auto oops (*TODO prove*)

(*The relation-based right- and left-bound operators form a Galois-connection *)
lemma "(\<subseteq>),(\<subseteq>)-GAL R-rightBound R-leftBound" unfolding adj_defs rel_defs func_defs comb_defs by auto
(*The relation-based right-image and left-dualimage operators form a (covariant) adjunction *)
lemma "(\<subseteq>),(\<subseteq>)-ADJ R-rightImage R-leftDualImage" unfolding adj_defs rel_defs func_defs comb_defs by auto

(*The usual 'residuation' properties of boolean connectives (recall that '\<rightarrow>' is an ordering on {\<T>,\<F>})*)
lemma and_impl_adj: "(\<rightarrow>),(\<rightarrow>)-ADJ\<^sub>2 (\<and>) (\<rightarrow>)" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma dimpl_or_adj: "(\<rightarrow>),(\<rightarrow>)-ADJ\<^sub>2 (\<rightharpoonup>) (\<or>)" unfolding adj_defs rel_defs func_defs comb_defs by auto

(*Note that we can use the 'adjunction lifting' rule to prove adjunctions on lifted (indexed) operations*)
lemma "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<inter>) (\<Rightarrow>)" by (simp add: adjunction_lift2 and_impl_adj impl_def inter_def subset_def)
lemma "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-ADJ\<^sub>2 (\<inter>\<^sup>r) (\<Rightarrow>\<^sup>r)" by (simp add: adjunction_lift2 and_impl_adj implR_def impl_def interR_def inter_def subrel_def subset_def)


(*The examples below require importing Complex_Main*)
(*
lemma "a \<noteq> 0 \<Longrightarrow> \<Q>,\<Q>-ADJ (\<lambda>x::rat. x * a) (\<lambda>x::rat. x / a)" 
  unfolding diagram_defs by (simp add: nonzero_eq_divide_eq)
lemma "0 < a \<Longrightarrow> (\<le>),(\<le>)-ADJ (\<lambda>x::rat. x * a) (\<lambda>x::rat. x / a)"
  unfolding diagram_defs by (simp add: pos_le_divide_eq)
*)

end
