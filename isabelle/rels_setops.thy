theory rels_setops (* A basic theory of relation-derived set-operations *)
imports rels_adj
begin

subsection \<open>Set-operations defined from relations\<close>

(*We can extend the definitions of the (pre)image set-operator from functions to relations
 together with their 'dual' counterparts*)
definition rightImage::"Rel('a,'b) \<Rightarrow> Op(Set('a),Set('b))" ("_-rightImage")
  where "rightImage \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>C)\<Zcat>"
definition leftImage::"Rel('a,'b) \<Rightarrow> Op(Set('b),Set('a))" ("_-leftImage")
  where "leftImage \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>A)\<Zcat>"
definition rightDualImage::"Rel('a,'b) \<Rightarrow> Op(Set('a),Set('b))" ("_-rightDualImage")
  where "rightDualImage \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<subseteq>) \<^bold>C)\<Zcat>"
definition leftDualImage::"Rel('a,'b) \<Rightarrow> Op(Set('b),Set('a))" ("_-leftDualImage")
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
definition rightBound::"Rel('a,'b) \<Rightarrow> Op(Set('a),Set('b))" ("_-rightBound")
  where "rightBound \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>C)\<Zcat>" (*cf. rightDualImage (using \<supseteq>)*)
definition leftBound::"Rel('a,'b) \<Rightarrow> Op(Set('b),Set('a))" ("_-leftBound")
  where "leftBound \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>A)\<Zcat>" (*cf. leftDualImage (using \<supseteq>)*)
definition rightDualBound::"Rel('a,'b) \<Rightarrow> Op(Set('a),Set('b))" ("_-rightDualBound")
  where  "rightDualBound \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>C)\<Zcat>" (*cf. rightImage (preprocessed with \<midarrow>)*)
definition leftDualBound::"Rel('a,'b) \<Rightarrow> Op(Set('b),Set('a))" ("_-leftDualBound")
  where  "leftDualBound \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>A)\<Zcat>" (*cf. leftImage (preprocessed with \<midarrow>)*)

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

(*Alternative (possibly more insightful) definitions for dual-bounds*)
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


(*This is a good moment to recall that unary operations on sets (set-operations) are also relations...*)
term "(F :: SetOp('a,'b)) :: Rel(Set('a),'b)"
(*... and thus can be ordered as such (via \<subseteq>\<^sup>r)*)
lemma fixes F::"SetOp('a,'b)" and G::"SetOp('a,'b)"
  shows "F \<subseteq>\<^sup>r G = (\<forall>A. F A \<subseteq> G A)" unfolding rel_defs comb_defs set_defs .. (*read as: F is a sub-operation wrt G*)

(*Recalling*)
lemma fixes F::"Set('b) \<Rightarrow> Set('c)" and G::"Set('a) \<Rightarrow> Set('b)"
  shows "(F \<circ> G) = (\<lambda>x. F (G x))" unfolding comb_defs ..

(*Composition and identity satisfy the monoid conditions.*)
lemma fixes F::"Set('b) \<Rightarrow> Set('c)" and G::"Set('a) \<Rightarrow> Set('b)" and H::"Set('z) \<Rightarrow> Set('a)"
  shows "((F \<circ> G) \<circ> H) = (F \<circ> (G \<circ> H))" unfolding comb_defs ..    (* associativity *)
lemma fixes F::"Set('b) \<Rightarrow> Set('c)"
  shows "(\<^bold>I \<circ> f) = f" unfolding comb_defs ..                   (* identity *)


(*Following abbreviation generalizes the notion of order-embedding to (endo)relations in general*)
abbreviation(input) relEmbedding ("_,_-embedding_")
  where "R,T-embedding \<phi> \<equiv> (\<And>X Y. R X Y \<leftrightarrow> T (\<phi> X) (\<phi> Y))"

(*Operators are (dual) embeddings between relation-ordering and the (converse) operator-ordering*)
lemma rightImage_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding rightImage"
  unfolding rel_defs set_defs comb_defs by fast
lemma leftImage_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding leftImage"
  unfolding rel_defs set_defs comb_defs by fast
lemma rightDualImage_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding rightDualImage"
  unfolding rel_defs set_defs comb_defs by fast
lemma leftDualImage_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding leftDualImage"
  unfolding rel_defs set_defs comb_defs by fast
lemma rightBound_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding rightBound"
  unfolding rel_defs set_defs comb_defs by fast
lemma leftBound_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding leftBound"
  unfolding rel_defs set_defs comb_defs by fast
lemma rightDualBound_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding rightDualBound"
  unfolding rel_defs set_defs comb_defs by fast
lemma leftDualBound_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding leftDualBound"
  unfolding rel_defs set_defs comb_defs by fast


subsubsection \<open>Set-operators\<close>

definition setopCompDual::"SetOp('a,'b) \<Rightarrow> SetOp('c,'a) \<Rightarrow> SetOp('c,'b)" (infixl "\<bullet>" 55)
  where "(\<bullet>) \<equiv> \<lambda>f g. \<lambda>x. f (\<midarrow>(g x))"

abbreviation(input) setopCompDual_t (infixr ":" 55)
  where "f : g \<equiv> g \<bullet> f"

declare setopCompDual_def[rel_defs]

lemma "(f \<bullet> g) = ((f\<^sup>\<midarrow>) \<circ> (g\<^sup>\<midarrow>))\<^sup>\<midarrow>" 
  unfolding rel_defs set_defs comb_defs by simp

lemma setopCompDuality1: "(f \<bullet> g) = (f \<circ> (g\<^sup>\<midarrow>))" 
  unfolding rel_defs set_defs comb_defs by simp
lemma setopCompDuality2: "(f \<circ> g) = (f \<bullet> (g\<^sup>\<midarrow>))" 
  unfolding rel_defs set_defs comb_defs by simp


(*Operators are also (dual) homomorphisms from the monoid of relations to the monoid of (set-)operators*)

(*First of all, they map the relational unit \<Q> (resp. its dual \<D>) to the functional unit \<^bold>I (resp. its dual \<midarrow>)*)
lemma rightImage_hom_id: "rightImage \<Q> = \<^bold>I"
  unfolding rel_defs set_defs comb_defs by simp
lemma leftImage_hom_id: "leftImage \<Q> = \<^bold>I"
  unfolding rel_defs set_defs comb_defs by simp
lemma rightDualImage_hom_id: "rightDualImage \<Q> = \<^bold>I"
  unfolding rel_defs set_defs comb_defs by simp
lemma leftDualImage_hom_id: "leftDualImage \<Q> = \<^bold>I"
  unfolding rel_defs set_defs comb_defs by simp
lemma rightBound_hom_id: "rightBound \<D> = \<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftBound_hom_id: "leftBound \<D> = \<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma rightDualBound_hom_id: "rightDualBound \<D> = \<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftDualBound_hom_id: "leftDualBound \<D> = \<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto

(*Moreover, they map the relational composition \<circ>\<^sup>r (resp. its dual \<bullet>\<^sup>r) to their functional counterparts *)
lemma rightImage_hom_comp: "(A \<circ>\<^sup>r B)-rightImage = (A-rightImage) \<circ> (B-rightImage)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma leftImage_hom_comp: "(A \<circ>\<^sup>r B)-leftImage = (B-leftImage) \<circ> (A-leftImage)" (*note reversed*)
  unfolding rel_defs set_defs comb_defs by auto
lemma rightDualImage_hom_comp:  "(A \<circ>\<^sup>r B)-rightDualImage = (A-rightDualImage) \<circ> (B-rightDualImage)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma leftDualImage_hom_comp: "(A \<circ>\<^sup>r B)-leftDualImage = (B-leftDualImage) \<circ> (A-leftDualImage)" (*note reversed*)
  unfolding rel_defs set_defs comb_defs by auto
lemma rightBound_hom_comp: "(A \<bullet>\<^sup>r B)-rightBound = (A-rightBound) \<bullet> (B-rightBound)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma leftBound_hom_comp: "(A \<bullet>\<^sup>r B)-leftBound = (B-leftBound) \<bullet> (A-leftBound)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma rightDualBound_hom_comp: "(A \<bullet>\<^sup>r B)-rightDualBound = (A-rightDualBound) \<bullet> (B-rightDualBound)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma leftDualBound_hom_comp: "(A \<bullet>\<^sup>r B)-leftDualBound = (B-leftDualBound) \<bullet> (A-leftDualBound)" 
  unfolding rel_defs set_defs comb_defs by auto


(*Operators are also (dual) homomorphisms from the BA of relations to the BA of (set-)operators*)

(*As for the lattice operations, we have the following homomorphisms*)
lemma rightImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-rightImage = R\<^sub>1-rightImage \<union>\<^sup>r R\<^sub>2-rightImage"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-leftImage = R\<^sub>1-leftImage \<union>\<^sup>r R\<^sub>2-leftImage"
  unfolding rel_defs set_defs comb_defs by auto
lemma rightBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-rightBound = R\<^sub>1-rightBound \<inter>\<^sup>r R\<^sub>2-rightBound"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-leftBound = R\<^sub>1-leftBound \<inter>\<^sup>r R\<^sub>2-leftBound"
  unfolding rel_defs set_defs comb_defs by auto
(*as well as the following dual ('anti') homomorphisms*)
lemma rightDualImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-rightDualImage = R\<^sub>1-rightDualImage \<inter>\<^sup>r R\<^sub>2-rightDualImage"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftDualImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-leftDualImage = R\<^sub>1-leftDualImage \<inter>\<^sup>r R\<^sub>2-leftDualImage"
  unfolding rel_defs set_defs comb_defs by auto
lemma rightDualBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-rightDualBound = R\<^sub>1-rightDualBound \<union>\<^sup>r R\<^sub>2-rightDualBound"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftDualBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-leftDualBound = R\<^sub>1-leftDualBound \<union>\<^sup>r R\<^sub>2-leftDualBound"
  unfolding rel_defs set_defs comb_defs by auto

(*...and for the complements*)
lemma rightImage_hom_compl: "(R\<^sup>\<midarrow>)-rightImage = (R-rightBound)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftImage_hom_compl: "(R\<^sup>\<midarrow>)-leftImage = (R-leftBound)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma rightDualImage_hom_compl: "(R\<^sup>\<midarrow>)-rightDualImage = (R-rightDualBound)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftDualImage_hom_compl: "(R\<^sup>\<midarrow>)-leftDualImage = (R-leftDualBound)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma rightBound_hom_compl: "(R\<^sup>\<midarrow>)-rightBound = (R-rightImage)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftBound_hom_compl: "(R\<^sup>\<midarrow>)-leftBound = (R-leftImage)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma rightDualBound_hom_compl: "(R\<^sup>\<midarrow>)-rightDualBound = (R-rightDualImage)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma leftDualBound_hom_compl: "(R\<^sup>\<midarrow>)-leftDualBound = (R-leftDualImage)\<^sup>\<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto


section \<open>Dualities and Adjunctions\<close>

(*Dualities between some pairs of operators*)

lemma "DUAL \<midarrow> \<midarrow>" (*complement is self-dual*)
  unfolding comb_defs set_defs by simp
lemma "DUAL (R-rightImage) (R-rightDualImage)"
  unfolding rel_defs comb_defs set_defs by simp
lemma "DUAL (R-leftImage) (R-leftDualImage)"
  unfolding rel_defs comb_defs set_defs by simp
lemma "DUAL (R-rightBound) (R-rightDualBound)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "DUAL (R-leftBound) (R-leftDualBound)"
  unfolding rel_defs comb_defs set_defs by auto


(*Adjunctions between some pairs of operators*)

lemma "RESID \<^bold>I \<^bold>I"
  unfolding comb_defs by simp
lemma "RESID (R-rightImage) (R-leftDualImage)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "RESID (R-leftImage) (R-rightDualImage)"
  unfolding rel_defs comb_defs set_defs by auto

lemma "CORESID \<midarrow> \<midarrow>"
  unfolding comb_defs set_defs by simp
lemma "CORESID (R-rightBound) (R-leftDualBound)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "CORESID (R-leftBound) (R-rightDualBound)"
  unfolding rel_defs comb_defs set_defs by auto

lemma "GALOIS \<midarrow> \<midarrow>"
  unfolding comb_defs set_defs by auto
lemma "GALOIS (R-rightBound) (R-leftBound)"
  unfolding rel_defs comb_defs set_defs by auto

lemma "DGALOIS \<midarrow> \<midarrow>"
  unfolding comb_defs set_defs by auto
lemma "DGALOIS (R-leftDualBound) (R-rightDualBound)"
  unfolding rel_defs comb_defs set_defs by auto

lemma "CONJ \<^bold>I \<^bold>I"
  unfolding comb_defs by simp
lemma "CONJ (R-rightImage) (R-leftImage)"
  unfolding rel_defs comb_defs set_defs by auto

lemma "DCONJ \<^bold>I \<^bold>I"
  unfolding comb_defs by simp
lemma "DCONJ (R-leftDualImage) (R-rightDualImage)"
  unfolding rel_defs comb_defs set_defs by auto

lemma "RESID \<midarrow> \<midarrow>" nitpick oops (*counterexample: complement is NOT self-residuated*)
lemma "CORESID \<^bold>I \<^bold>I" nitpick oops (*counterexample: identity is NOT self-coresiduated*)
lemma "GALOIS \<^bold>I \<^bold>I" nitpick oops (*counterexample: identity is NOT self-Galois-adjoint*)
lemma "DGALOIS \<^bold>I \<^bold>I" nitpick oops (*counterexample: identity is NOT self-dualGalois-adjoint*)
lemma "CONJ \<midarrow> \<midarrow>" nitpick oops (*counterexample: complement is NOT self-conjugated*)
lemma "DCONJ \<midarrow> \<midarrow>" nitpick oops (*counterexample: complement is NOT self-dualConjugated*)

(*Moreover, the following also don't hold: *)
lemma "RESID \<^bold>I \<midarrow>" nitpick oops (*counterexample*)
lemma "RESID \<midarrow> \<^bold>I" nitpick oops (*counterexample*)
lemma "CORESID \<^bold>I \<midarrow>" nitpick oops (*counterexample*)
lemma "CORESID \<midarrow> \<^bold>I" nitpick oops (*counterexample*)
lemma "GALOIS \<^bold>I \<midarrow>" nitpick oops (*counterexample*)
lemma "DGALOIS \<^bold>I \<midarrow>" nitpick oops (*counterexample*)
lemma "CONJ \<^bold>I \<midarrow>" nitpick oops (*counterexample*)
lemma "DCONJ \<^bold>I \<midarrow>" nitpick oops (*counterexample*)

end