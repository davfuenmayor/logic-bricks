theory rels_setops (* A basic theory of relation-derived set-operations *)
imports rels_adj
begin

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