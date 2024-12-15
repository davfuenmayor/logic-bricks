theory rels_setops (* A basic theory of relation-derived set-operations *)
imports rels_adj
begin

subsection \<open>Set-operations defined from relations\<close>

(*We can extend the definitions of the (pre)image set-operator from functions to relations
 together with their 'dual' counterparts*)
definition upImage::"Rel('a,'b) \<Rightarrow> Op(Set('a),Set('b))" ("_-upImage")
  where "upImage \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>C)\<^sup>t"
definition downImage::"Rel('a,'b) \<Rightarrow> Op(Set('b),Set('a))" ("_-downImage")
  where "downImage \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<sqinter>) \<^bold>A)\<^sup>t"
definition upImageDual::"Rel('a,'b) \<Rightarrow> Op(Set('a),Set('b))" ("_-upImageDual")
  where "upImageDual \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<subseteq>) \<^bold>C)\<^sup>t"
definition downImageDual::"Rel('a,'b) \<Rightarrow> Op(Set('b),Set('a))" ("_-downImageDual")
  where "downImageDual \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<subseteq>) \<^bold>A)\<^sup>t"

declare upImageDual_def[rel_defs] downImageDual_def[rel_defs] upImage_def[rel_defs] downImage_def[rel_defs]

lemma "R-upImage A = (\<lambda>b. R\<^sup>t b \<sqinter> A)" unfolding rel_defs comb_defs ..
lemma "R-downImage B = (\<lambda>a. R a \<sqinter> B)" unfolding rel_defs comb_defs ..
lemma "R-upImageDual A = (\<lambda>b. R\<^sup>t b \<subseteq> A)" unfolding rel_defs comb_defs ..
lemma "R-downImageDual B = (\<lambda>a. R a \<subseteq> B)" unfolding rel_defs comb_defs ..

lemma "R-upImage A b = (\<exists>a. R a b \<and> A a)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-downImage B a = (\<exists>b. R a b \<and> B b)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-upImageDual A b = (\<forall>a. R a b \<rightarrow> A a)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-downImageDual B a = (\<forall>b. R a b \<rightarrow> B b)" unfolding rel_defs set_defs func_defs comb_defs ..

(*Clearly, each direction (up/down) uniquely determines the other*)
lemma upImage_defT: "R-upImage = R\<^sup>t-downImage" 
  unfolding rel_defs comb_defs ..
lemma downImage_defT: "R-downImage = R\<^sup>t-upImage" 
  unfolding rel_defs comb_defs ..
lemma upImageDual_defT: "R-upImageDual = R\<^sup>t-downImageDual" 
  unfolding rel_defs comb_defs ..
lemma downImageDual_defT: "R-downImageDual = R\<^sup>t-upImageDual" 
  unfolding rel_defs comb_defs ..

(*TODO: explain this!*)
lemma upImage_defComp: "upImage = (;\<^sup>r) \<^bold>I" unfolding rel_defs unfolding comb_defs ..
lemma "upImage = \<^bold>T \<^bold>I (;\<^sup>r)" unfolding rel_defs comb_defs .. (*cf. eval-cont := \<^bold>T \<^bold>I*)
lemma "R-upImage = R \<circ>\<^sup>r \<^bold>I" unfolding rel_defs comb_defs ..

(*Convenient characterizations in terms of big-union and big-intersection*)
lemma upImage_def2: "upImage = \<Union> \<circ>\<^sub>2 image"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma downImage_def2: "downImage = \<Union> \<circ>\<^sub>2 (image \<circ> \<^bold>C)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma upImageDual_def2: "upImageDual = \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 image \<midarrow>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma downImageDual_def2: "downImageDual = \<Inter> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 image \<sim>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce

lemma "R-upImage A = \<Union>\<lparr>R A\<rparr>" unfolding upImage_def2 comb_defs ..
lemma "R-downImage B = \<Union>\<lparr>R\<^sup>t B\<rparr>" unfolding downImage_def2 comb_defs ..
lemma "R-upImageDual A =  \<Inter>\<lparr>R\<^sup>- \<midarrow>A\<rparr>" unfolding upImageDual_def2 comb_defs ..
lemma "R-downImageDual B =  \<Inter>\<lparr>R\<^sup>\<sim> \<midarrow>B\<rparr>" unfolding downImageDual_def2 comb_defs ..

(*TODO: show that they satisfy closure resp. interior conditions*)


(*Following operators (aka. polarities) generalize the notion of upper/lower bounds of a set (wrt. a relation)*)
definition upperBounds::"Rel('a,'b) \<Rightarrow> Op(Set('a),Set('b))" ("_-upperBounds")
  where "upperBounds \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>C)\<^sup>t" (*cf. upImageDual (with \<supseteq>)*)
definition lowerBounds::"Rel('a,'b) \<Rightarrow> Op(Set('b),Set('a))" ("_-lowerBounds")
  where "lowerBounds \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<supseteq>) \<^bold>A)\<^sup>t" (*cf. downImageDual (with \<supseteq>)*)
definition upperBoundsDual::"Rel('a,'b) \<Rightarrow> Op(Set('a),Set('b))" ("_-upperBoundsDual")
  where  "upperBoundsDual \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>C)\<^sup>t" (*cf. upImage (with complement)*)
definition lowerBoundsDual::"Rel('a,'b) \<Rightarrow> Op(Set('b),Set('a))" ("_-lowerBoundsDual")
  where  "lowerBoundsDual \<equiv> (\<^bold>B\<^sub>2\<^sub>2\<^sub>0 (\<^bold>\<Psi>\<^sub>2 (\<sqinter>) \<midarrow>) \<^bold>A)\<^sup>t" (*cf. downImage (with complement)*)

declare upperBounds_def[rel_defs] lowerBounds_def[rel_defs]
        upperBoundsDual_def[rel_defs] lowerBoundsDual_def[rel_defs]

lemma "R-upperBounds A = (\<lambda>b. A \<subseteq> R\<^sup>t b)" unfolding rel_defs comb_defs ..
lemma "R-lowerBounds B = (\<lambda>a. B \<subseteq> R a)" unfolding rel_defs comb_defs ..
lemma "R-upperBoundsDual A = (\<lambda>b. \<midarrow>(R\<^sup>t b) \<sqinter> \<midarrow>A)" unfolding rel_defs comb_defs ..
lemma "R-lowerBoundsDual B = (\<lambda>a. \<midarrow>(R a) \<sqinter> \<midarrow>B)" unfolding rel_defs comb_defs ..

lemma "R-upperBounds A = (\<lambda>b. \<forall>a. A a \<longrightarrow> R a b)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-lowerBounds B = (\<lambda>a. \<forall>b. B b \<longrightarrow> R a b)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-upperBoundsDual A = (\<lambda>b. \<exists>a. \<not>R a b \<and> \<not>A a)" unfolding rel_defs set_defs func_defs comb_defs ..
lemma "R-lowerBoundsDual B = (\<lambda>a. \<exists>b. \<not>R a b \<and> \<not>B b)" unfolding rel_defs set_defs func_defs comb_defs ..

(*For the dual variants we have possibly more insightful definitions*)
lemma upperBoundsDual_def': "R-upperBoundsDual A = \<midarrow>(\<lambda>b. (A \<squnion> R\<^sup>t b))" 
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBoundsDual_def': "R-lowerBoundsDual B = \<midarrow>(\<lambda>a. (B \<squnion> R a))" 
  unfolding rel_defs set_defs comb_defs by auto

lemma "R-upperBoundsDual A = \<midarrow>(\<lambda>b. \<forall>a. A a \<or> R a b)" 
  unfolding upperBoundsDual_def' set_defs comb_defs ..
lemma "R-lowerBoundsDual B = \<midarrow>(\<lambda>a. \<forall>b. B b \<or> R a b)" 
  unfolding lowerBoundsDual_def' set_defs comb_defs ..

(*Convenient characterizations in terms of big-union and big-intersection*)
lemma upperBounds_def2: "upperBounds = \<Inter> \<circ>\<^sub>2 image"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma lowerBounds_def2: "lowerBounds = \<Inter> \<circ>\<^sub>2 (image \<circ> \<^bold>C)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma upperBoundsDual_def2: "upperBoundsDual =  \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 image \<midarrow>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma lowerBoundsDual_def2: "lowerBoundsDual = \<Union> \<circ>\<^sub>2 (\<^bold>B\<^sub>2\<^sub>1\<^sub>1 image \<sim>\<^sup>r \<midarrow>)"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce

lemma "R-upperBounds A = \<Inter>\<lparr>R A\<rparr>" unfolding upperBounds_def2 comb_defs ..
lemma "R-lowerBounds A = \<Inter>\<lparr>R\<^sup>t A\<rparr>" unfolding lowerBounds_def2 comb_defs ..
lemma "R-upperBoundsDual A = \<Union>\<lparr>R\<^sup>- \<midarrow>A\<rparr>" unfolding upperBoundsDual_def2 comb_defs ..
lemma "R-lowerBoundsDual B = \<Union>\<lparr>R\<^sup>\<sim> \<midarrow>B\<rparr>" unfolding lowerBoundsDual_def2 comb_defs ..


(*In fact, each polarity uniquely determines the other*)
lemma upperBounds_defT: "R-upperBounds = R\<^sup>t-lowerBounds" 
  unfolding rel_defs comb_defs ..
lemma lowerBounds_defT: "R-lowerBounds = R\<^sup>t-upperBounds" 
  unfolding rel_defs comb_defs ..
lemma upperBoundsDual_defT: "R-upperBoundsDual = R\<^sup>t-lowerBoundsDual" 
  unfolding rel_defs comb_defs ..
lemma lowerBoundsDual_defT: "R-lowerBoundsDual = R\<^sup>t-upperBoundsDual" 
  unfolding rel_defs comb_defs ..

(*TODO: show that they satisfy closure resp. interior conditions*)


(*Further interesting interdefinitions (duality wrt relational complement)*)
lemma upImage_def3: "R-upImage = (R\<^sup>--upperBounds)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma upperBounds_def3: "R-upperBounds = (R\<^sup>--upImage)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma downImage_def3: "R-downImage = (R\<^sup>--lowerBounds)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBounds_def3: "R-lowerBounds = (R\<^sup>--downImage)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto

lemma upImageDual_def3: "R-upImageDual = (R\<^sup>--upperBoundsDual)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma upperBoundsDual_def3: "R-upperBoundsDual = (R\<^sup>--upImageDual)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma downImageDual_def3: "R-downImageDual = (R\<^sup>--lowerBoundsDual)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBoundsDual_def3: "R-lowerBoundsDual = (R\<^sup>--downImageDual)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto

(*Some properties of upper and lower bounds*)
lemma upper_dual_hom: "R-upperBounds(\<Union>S) = \<Inter>\<lparr>R-upperBounds S\<rparr>" 
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma lower_dual_hom: "R-lowerBounds(\<Union>S) = \<Inter>\<lparr>R-lowerBounds S\<rparr>" 
  unfolding rel_defs set_defs func_defs comb_defs by fastforce  

(*Note, however:*)
lemma "R-upperBounds(\<Inter>S) = \<Union>\<lparr>R-upperBounds S\<rparr>" nitpick oops (*counterexample*)
lemma "R-lowerBounds(\<Inter>S) = \<Union>\<lparr>R-lowerBounds S\<rparr>" nitpick oops (*counterexample*)
(*We have, rather:*)
lemma "R-upperBounds(\<Inter>S) \<supseteq> \<Union>\<lparr>R-upperBounds S\<rparr>"
  unfolding rel_defs set_defs func_defs comb_defs by fastforce
lemma "R-lowerBounds(\<Inter>S) \<supseteq> \<Union>\<lparr>R-lowerBounds S\<rparr>" 
  unfolding rel_defs set_defs func_defs comb_defs by fastforce


(*We say that the previous operators are dual to each other because..*)
abbreviation "dual \<phi> \<equiv> \<midarrow> \<circ> \<phi> \<circ> \<midarrow>"

lemma "upImageDual R = dual (upImage R)"
  unfolding rel_defs set_defs comb_defs by simp
lemma "downImageDual R = dual (downImage R)"
  unfolding rel_defs set_defs comb_defs by simp
lemma "upperBoundsDual R = dual (upperBounds R)"
  unfolding rel_defs set_defs comb_defs by auto
lemma "lowerBoundsDual R = dual (lowerBounds R)"
  unfolding rel_defs set_defs comb_defs by auto


(*This is a good moment to recall that unary operations on sets (set-operations) are also relations...*)
term "(F :: SetOp('a,'b)) :: Rel(Set('a),'b)"
(*... and thus can be ordered as such (via \<subseteq>\<^sup>r)*)
lemma fixes F::"SetOp('a,'b)" and G::"SetOp('a,'b)"
  shows "F \<subseteq>\<^sup>r G = (\<forall>A. F A \<subseteq> G A)" unfolding rel_defs comb_defs set_defs .. (*read as: F is a sub-operation wrt G*)

(*Recalling*)
lemma fixes F::"Set('b) \<Rightarrow> Set('c)" and G::"Set('a) \<Rightarrow> Set('b)"
  shows "F \<circ> G = (\<lambda>x. F (G x))" unfolding comb_defs ..

(*Composition and identity satisfy the monoid conditions.*)
lemma fixes F::"Set('b) \<Rightarrow> Set('c)" and G::"Set('a) \<Rightarrow> Set('b)" and H::"Set('z) \<Rightarrow> Set('a)"
  shows "(F \<circ> G) \<circ> H = F \<circ> (G \<circ> H)" unfolding comb_defs ..    (* associativity *)
lemma fixes F::"Set('b) \<Rightarrow> Set('c)"
  shows "\<^bold>I \<circ> f = f" unfolding comb_defs ..                   (* identity *)


(*Following abbreviation generalizes the notion of order-embedding to (endo)relations in general*)
abbreviation(input) relEmbedding ("_,_-embedding_")
  where "R,T-embedding \<phi> \<equiv> (\<And>X Y. R X Y \<leftrightarrow> T (\<phi> X) (\<phi> Y))"

(*Operators are (dual) embeddings between relation-ordering and the (converse) operator-ordering*)
lemma upImage_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding upImage"
  unfolding rel_defs set_defs comb_defs by fast
lemma downImage_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding downImage"
  unfolding rel_defs set_defs comb_defs by fast
lemma upImageDual_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding upImageDual"
  unfolding rel_defs set_defs comb_defs by fast
lemma downImageDual_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding downImageDual"
  unfolding rel_defs set_defs comb_defs by fast
lemma upperBounds_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding upperBounds"
  unfolding rel_defs set_defs comb_defs by fast
lemma lowerBounds_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding lowerBounds"
  unfolding rel_defs set_defs comb_defs by fast
lemma upperBoundsDual_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding upperBoundsDual"
  unfolding rel_defs set_defs comb_defs by fast
lemma lowerBoundsDual_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding lowerBoundsDual"
  unfolding rel_defs set_defs comb_defs by fast


subsubsection \<open>Set-operators\<close>

definition setopCompDual::"SetOp('a,'b) \<Rightarrow> SetOp('c,'a) \<Rightarrow> SetOp('c,'b)" (infixl "\<bullet>" 55)
  where "(\<bullet>) \<equiv> \<lambda>f g. \<lambda>x. f (\<midarrow>(g x))"


declare setopCompDual_def[rel_defs]

lemma setopCompDual_def2: "(\<bullet>) = (\<lambda>f g. ((f\<^sup>-) \<circ> (g\<^sup>-))\<^sup>-)" 
  unfolding rel_defs set_defs comb_defs by simp


(*Operators are also (dual) homomorphisms from the monoid of relations to the monoid of (set-)operators*)

(*First of all, they map the relational unit \<Q> (resp. its dual \<D>) to the functional unit \<^bold>I (resp. its dual \<midarrow>)*)
lemma upImage_hom_id: "upImage \<Q> = \<^bold>I"
  unfolding rel_defs set_defs comb_defs by simp
lemma downImage_hom_id: "downImage \<Q> = \<^bold>I"
  unfolding rel_defs set_defs comb_defs by simp
lemma upImageDual_hom_id: "upImageDual \<Q> = \<^bold>I"
  unfolding rel_defs set_defs comb_defs by simp
lemma downImageDual_hom_id: "downImageDual \<Q> = \<^bold>I"
  unfolding rel_defs set_defs comb_defs by simp
lemma upperBounds_hom_id: "upperBounds \<D> = \<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBounds_hom_id: "lowerBounds \<D> = \<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma upperBoundsDual_hom_id: "upperBoundsDual \<D> = \<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBoundsDual_hom_id: "lowerBoundsDual \<D> = \<midarrow>"
  unfolding rel_defs set_defs comb_defs by auto

(*Moreover, they map the relational composition \<circ>\<^sup>r (resp. its dual \<bullet>\<^sup>r) to their functional counterparts *)
lemma upImage_hom_comp: "(A \<circ>\<^sup>r B)-upImage = (A-upImage) \<circ> (B-upImage)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma downImage_hom_comp: "(A \<circ>\<^sup>r B)-downImage = (B-downImage) \<circ> (A-downImage)" (*reversed*)
  unfolding rel_defs set_defs comb_defs by auto
lemma upImageDual_hom_comp:  "(A \<circ>\<^sup>r B)-upImageDual = (A-upImageDual) \<circ> (B-upImageDual)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma downImageDual_hom_comp: "(A \<circ>\<^sup>r B)-downImageDual = (B-downImageDual) \<circ> (A-downImageDual)" (*reversed*)
  unfolding rel_defs set_defs comb_defs by auto
lemma upperBounds_hom_comp: "(A \<bullet>\<^sup>r B)-upperBounds = (A-upperBounds) \<bullet> (B-upperBounds)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBounds_hom_comp: "(A \<bullet>\<^sup>r B)-lowerBounds = (B-lowerBounds) \<bullet> (A-lowerBounds)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma upperBoundsDual_hom_comp: "(A \<bullet>\<^sup>r B)-upperBoundsDual = (A-upperBoundsDual) \<bullet> (B-upperBoundsDual)" 
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBoundsDual_hom_comp: "(A \<bullet>\<^sup>r B)-lowerBoundsDual = (B-lowerBoundsDual) \<bullet> (A-lowerBoundsDual)" 
  unfolding rel_defs set_defs comb_defs by auto


(*Operators are also (dual) homomorphisms from the BA of relations to the BA of (set-)operators*)

(*As for the lattice operations, we have*)
lemma upImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-upImage = R\<^sub>1-upImage \<union>\<^sup>r R\<^sub>2-upImage"
  unfolding rel_defs set_defs comb_defs by auto
lemma downImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-downImage = R\<^sub>1-downImage \<union>\<^sup>r R\<^sub>2-downImage"
  unfolding rel_defs set_defs comb_defs by auto
lemma upImage_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-upperBounds = R\<^sub>1-upperBounds \<inter>\<^sup>r R\<^sub>2-upperBounds"
  unfolding rel_defs set_defs comb_defs by auto
lemma downImage_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-lowerBounds = R\<^sub>1-lowerBounds \<inter>\<^sup>r R\<^sub>2-lowerBounds"
  unfolding rel_defs set_defs comb_defs by auto
lemma upImageDual_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-upImageDual = R\<^sub>1-upImageDual \<inter>\<^sup>r R\<^sub>2-upImageDual"
  unfolding rel_defs set_defs comb_defs by auto
lemma downImageDual_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-downImageDual = R\<^sub>1-downImageDual \<inter>\<^sup>r R\<^sub>2-downImageDual"
  unfolding rel_defs set_defs comb_defs by auto
lemma upperBoundsDual_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-upperBoundsDual = R\<^sub>1-upperBoundsDual \<union>\<^sup>r R\<^sub>2-upperBoundsDual"
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBoundsDual_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-lowerBoundsDual = R\<^sub>1-lowerBoundsDual \<union>\<^sup>r R\<^sub>2-lowerBoundsDual"
  unfolding rel_defs set_defs comb_defs by auto

(*...and for the complements*)
lemma upImage_hom_compl: "(R\<^sup>-)-upImage = (R-upperBounds)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma downImage_hom_compl: "(R\<^sup>-)-downImage = (R-lowerBounds)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma upImageDual_hom_compl: "(R\<^sup>-)-upImageDual = (R-upperBoundsDual)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma downImageDual_hom_compl: "(R\<^sup>-)-downImageDual = (R-lowerBoundsDual)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma upperBounds_hom_compl: "(R\<^sup>-)-upperBounds = (R-upImage)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBounds_hom_compl: "(R\<^sup>-)-lowerBounds = (R-downImage)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma upperBoundsDual_hom_compl: "(R\<^sup>-)-upperBoundsDual = (R-upImageDual)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto
lemma lowerBoundsDual_hom_compl: "(R\<^sup>-)-lowerBoundsDual = (R-downImageDual)\<^sup>-"
  unfolding rel_defs set_defs comb_defs by auto


section \<open>Dualities and Adjunctions\<close>

(*Dualities between some pairs of operators*)
lemma "DUAL (R-upImage) (R-upImageDual)"
  unfolding rel_defs comb_defs set_defs by simp
lemma "DUAL (R-downImage) (R-downImageDual)"
  unfolding rel_defs comb_defs set_defs by simp
lemma "DUAL (R-upperBounds) (R-upperBoundsDual)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "DUAL (R-lowerBounds) (R-lowerBoundsDual)"
  unfolding rel_defs comb_defs set_defs by auto

(*Adjunctions between some pairs of operators*)
lemma "RESID (R-upImage) (R-downImageDual)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "RESID (R-downImage) (R-upImageDual)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "CORESID (R-upperBounds) (R-lowerBoundsDual)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "CORESID (R-lowerBounds) (R-upperBoundsDual)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "GALOIS (R-upperBounds) (R-lowerBounds)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "DGALOIS (R-lowerBoundsDual) (R-upperBoundsDual)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "CONJ (R-upImage) (R-downImage)"
  unfolding rel_defs comb_defs set_defs by auto
lemma "DCONJ (R-downImageDual) (R-upImageDual)"
  unfolding rel_defs comb_defs set_defs by auto

end