section \<open>General Theory of Relation-based Operators\<close>
text \<open>It is well known that (n+1-ary) relations give rise to (n-ary) operations on sets (called "operators").
 We explore some basic algebraic properties of relation-based set-operators.\<close>

theory operators
imports adjunctions
begin

subsection \<open>Set-Operators from Binary Relations\<close>
text \<open>This is the (non-trivial) base case. It is very common in logic, so it gets an special treatment.\<close>

text \<open>Add some convenient (arguably less visually-cluttering) notation, reminiscent of logical operations.\<close>
notation(input) leftImage ("_-\<diamond>\<^sub>\<leftarrow>") and leftDualImage ("_-\<box>\<^sub>\<leftarrow>") and 
                rightImage ("_-\<diamond>\<^sub>\<rightarrow>") and rightDualImage ("_-\<box>\<^sub>\<rightarrow>") and
                leftBound ("_-\<odot>\<^sub>\<leftarrow>") and leftDualBound ("_-\<ominus>\<^sub>\<leftarrow>") and
                rightBound ("_-\<odot>\<^sub>\<rightarrow>") and rightDualBound ("_-\<ominus>\<^sub>\<rightarrow>")
\<comment> \<open>and extend this notation to the transformations themselves\<close>
notation(input) leftImage ("\<diamond>\<^sub>\<leftarrow>") and leftDualImage ("\<box>\<^sub>\<leftarrow>") and 
                rightImage ("\<diamond>\<^sub>\<rightarrow>") and rightDualImage ("\<box>\<^sub>\<rightarrow>") and
                leftBound ("\<odot>\<^sub>\<leftarrow>") and leftDualBound ("\<ominus>\<^sub>\<leftarrow>") and
                rightBound ("\<odot>\<^sub>\<rightarrow>") and rightDualBound ("\<ominus>\<^sub>\<rightarrow>")


subsubsection \<open>Order Embedding\<close>

text \<open>This is a good moment to recall that unary operations on sets (set-operations) are also relations...\<close>
term "(F :: SetOp('a,'b)) :: Rel(Set('a),'b)"
text \<open>... and thus can be ordered as such. Thus read \<open>F \<subseteq>\<^sup>2 G\<close> as: "F is a sub-operation of G".\<close>
lemma fixes F::"SetOp('a,'b)" and G::"SetOp('a,'b)"
  shows "F \<subseteq>\<^sup>2 G = (\<forall>A. F A \<subseteq> G A)" unfolding rel_defs comb_defs func_defs ..

text \<open>Operators are (dual) embeddings between the sub-relation and the (converse of) sub-operation ordering.\<close>
lemma rightImage_embedding: "(\<subseteq>\<^sup>2),(\<subseteq>\<^sup>2)-embedding \<diamond>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs unfolding func_defs comb_defs by fast
lemma leftImage_embedding: "(\<subseteq>\<^sup>2),(\<subseteq>\<^sup>2)-embedding \<diamond>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma rightDualImage_embedding: "(\<subseteq>\<^sup>2),(\<supseteq>\<^sup>2)-embedding \<box>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma leftDualImage_embedding: "(\<subseteq>\<^sup>2),(\<supseteq>\<^sup>2)-embedding \<box>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma rightBound_embedding: "(\<subseteq>\<^sup>2),(\<subseteq>\<^sup>2)-embedding \<odot>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma leftBound_embedding: "(\<subseteq>\<^sup>2),(\<subseteq>\<^sup>2)-embedding \<odot>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma rightDualBound_embedding: "(\<subseteq>\<^sup>2),(\<supseteq>\<^sup>2)-embedding \<ominus>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma leftDualBound_embedding: "(\<subseteq>\<^sup>2),(\<supseteq>\<^sup>2)-embedding \<ominus>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by fast


subsubsection \<open>Homomorphisms\<close>
text \<open>Operators are also (dual) homomorphisms from the monoid of relations to the monoid of (set-)operators.\<close>

text \<open>First of all, they map the relational unit \<open>\<Q>\<close> (resp. its dual \<open>\<D>\<close>) to the functional unit \<open>\<^bold>I\<close> (resp. its dual \<open>\<midarrow>\<close>).\<close>
lemma rightImage_hom_id: "\<Q>-\<diamond>\<^sub>\<rightarrow> = \<^bold>I"
  unfolding rel_defs func_defs comb_defs by simp
lemma leftImage_hom_id: "\<Q>-\<diamond>\<^sub>\<leftarrow> = \<^bold>I"
  unfolding rel_defs func_defs comb_defs by simp
lemma rightDualImage_hom_id: "\<Q>-\<box>\<^sub>\<rightarrow> = \<^bold>I"
  unfolding rel_defs func_defs comb_defs by simp
lemma leftDualImage_hom_id: "\<Q>-\<box>\<^sub>\<leftarrow> = \<^bold>I"
  unfolding rel_defs func_defs comb_defs by simp
lemma rightBound_hom_id: "\<D>-\<odot>\<^sub>\<rightarrow> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_id: "\<D>-\<odot>\<^sub>\<leftarrow> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_id: "\<D>-\<ominus>\<^sub>\<rightarrow> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_id: "\<D>-\<ominus>\<^sub>\<leftarrow> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto

text \<open>Moreover, they map the relational composition \<open>\<circ>\<^sup>2\<close> (resp. its dual \<open>\<bullet>\<^sup>2\<close>) to their functional counterparts.\<close>
lemma rightImage_hom_comp: "(A ; B)-\<diamond>\<^sub>\<rightarrow> = (A-\<diamond>\<^sub>\<rightarrow>) \<ggreater> (B-\<diamond>\<^sub>\<rightarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_hom_comp: "(A ; B)-\<diamond>\<^sub>\<leftarrow> = (B-\<diamond>\<^sub>\<leftarrow>) \<ggreater> (A-\<diamond>\<^sub>\<leftarrow>)"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualImage_hom_comp:  "(A ; B)-\<box>\<^sub>\<rightarrow> = (A-\<box>\<^sub>\<rightarrow>) \<ggreater> (B-\<box>\<^sub>\<rightarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_hom_comp: "(A ; B)-\<box>\<^sub>\<leftarrow> = (B-\<box>\<^sub>\<leftarrow>) \<ggreater> (A-\<box>\<^sub>\<leftarrow>)"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_hom_comp: "(A \<dagger> B)-\<odot>\<^sub>\<rightarrow> = (A-\<odot>\<^sub>\<rightarrow>) \<ggreater>\<^sup>d (B-\<odot>\<^sub>\<rightarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_comp: "(A \<dagger> B)-\<odot>\<^sub>\<leftarrow> = (B-\<odot>\<^sub>\<leftarrow>) \<ggreater>\<^sup>d (A-\<odot>\<^sub>\<leftarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_comp: "(A \<dagger> B)-\<ominus>\<^sub>\<rightarrow> = (A-\<ominus>\<^sub>\<rightarrow>) \<ggreater>\<^sup>d (B-\<ominus>\<^sub>\<rightarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_comp: "(A \<dagger> B)-\<ominus>\<^sub>\<leftarrow> = (B-\<ominus>\<^sub>\<leftarrow>) \<ggreater>\<^sup>d (A-\<ominus>\<^sub>\<leftarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto

text \<open>Operators are also (dual) lattice homomorphisms from the BA of relations to the BA of set-operators.\<close>
lemma rightImage_hom_join: "(R\<^sub>1 \<union>\<^sup>2 R\<^sub>2)-\<diamond>\<^sub>\<rightarrow> = R\<^sub>1-\<diamond>\<^sub>\<rightarrow> \<union>\<^sup>2 R\<^sub>2-\<diamond>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_hom_join: "(R\<^sub>1 \<union>\<^sup>2 R\<^sub>2)-\<diamond>\<^sub>\<leftarrow> = R\<^sub>1-\<diamond>\<^sub>\<leftarrow> \<union>\<^sup>2 R\<^sub>2-\<diamond>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>2 R\<^sub>2)-\<odot>\<^sub>\<rightarrow> = R\<^sub>1-\<odot>\<^sub>\<rightarrow> \<inter>\<^sup>2 R\<^sub>2-\<odot>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>2 R\<^sub>2)-\<odot>\<^sub>\<leftarrow> = R\<^sub>1-\<odot>\<^sub>\<leftarrow> \<inter>\<^sup>2 R\<^sub>2-\<odot>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by auto
\<comment> \<open> dual ('anti') homomorphisms\<close>
lemma rightDualImage_hom_join: "(R\<^sub>1 \<union>\<^sup>2 R\<^sub>2)-\<box>\<^sub>\<rightarrow> = R\<^sub>1-\<box>\<^sub>\<rightarrow> \<inter>\<^sup>2 R\<^sub>2-\<box>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_hom_join: "(R\<^sub>1 \<union>\<^sup>2 R\<^sub>2)-\<box>\<^sub>\<leftarrow> = R\<^sub>1-\<box>\<^sub>\<leftarrow> \<inter>\<^sup>2 R\<^sub>2-\<box>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>2 R\<^sub>2)-\<ominus>\<^sub>\<rightarrow> = R\<^sub>1-\<ominus>\<^sub>\<rightarrow> \<union>\<^sup>2 R\<^sub>2-\<ominus>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>2 R\<^sub>2)-\<ominus>\<^sub>\<leftarrow> = R\<^sub>1-\<ominus>\<^sub>\<leftarrow> \<union>\<^sup>2 R\<^sub>2-\<ominus>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by auto

text \<open>As for complement, we have a particular morphism property between images and bounds (cf. dualities below).\<close>
lemma rightImage_hom_compl: "(R\<^sup>\<midarrow>)-\<diamond>\<^sub>\<rightarrow> = (R-\<odot>\<^sub>\<rightarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_hom_compl: "(R\<^sup>\<midarrow>)-\<diamond>\<^sub>\<leftarrow> = (R-\<odot>\<^sub>\<leftarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualImage_hom_compl: "(R\<^sup>\<midarrow>)-\<box>\<^sub>\<rightarrow> = (R-\<ominus>\<^sub>\<rightarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_hom_compl: "(R\<^sup>\<midarrow>)-\<box>\<^sub>\<leftarrow> = (R-\<ominus>\<^sub>\<leftarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_hom_compl: "(R\<^sup>\<midarrow>)-\<odot>\<^sub>\<rightarrow> = (R-\<diamond>\<^sub>\<rightarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_compl: "(R\<^sup>\<midarrow>)-\<odot>\<^sub>\<leftarrow> = (R-\<diamond>\<^sub>\<leftarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_compl: "(R\<^sup>\<midarrow>)-\<ominus>\<^sub>\<rightarrow> = (R-\<box>\<^sub>\<rightarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_compl: "(R\<^sup>\<midarrow>)-\<ominus>\<^sub>\<leftarrow> = (R-\<box>\<^sub>\<leftarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto


subsubsection \<open>Dualities (illustrated with diagrams)\<close>
text \<open>Dualities between some pairs of relation-based set-operators.\<close>

lemma leftImage_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<diamond>\<^sub>\<leftarrow>) (R-\<box>\<^sub>\<leftarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by simp
lemma "  \<sqdot> \<midarrow>R-\<diamond>\<^sub>\<leftarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<down>           \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<box>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>   " using dual_def leftImage_dual by blast
lemma rightImage_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<diamond>\<^sub>\<rightarrow>) (R-\<box>\<^sub>\<rightarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by simp
lemma "  \<sqdot> \<midarrow>R-\<diamond>\<^sub>\<rightarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<down>           \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<box>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>   " using dual_def rightImage_dual by blast

lemma leftBound_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<odot>\<^sub>\<leftarrow>) (R-\<ominus>\<^sub>\<leftarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma "  \<sqdot> \<midarrow>R-\<odot>\<^sub>\<leftarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<down>           \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<ominus>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>   " using dual_def leftBound_dual by blast
lemma rightBound_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<odot>\<^sub>\<rightarrow>) (R-\<ominus>\<^sub>\<rightarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma "  \<sqdot> \<midarrow>R-\<odot>\<^sub>\<rightarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<down>           \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<ominus>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>   " using dual_def rightBound_dual by blast

text \<open>Recall that set-operators are also relations (and thus can be ordered as such). We thus have following
  dualities between the transformations themselves (cf. morphisms wrt. complement discussed above).\<close>
lemma leftImageBound_dual: "\<midarrow>\<^sup>2,\<midarrow>\<^sup>2-DUAL \<diamond>\<^sub>\<leftarrow> \<odot>\<^sub>\<leftarrow>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<diamond>\<^sub>\<leftarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>2\<down>        \<down>\<midarrow>\<^sup>2
         \<sqdot> \<midarrow>\<odot>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>   " using dual_def leftImageBound_dual by blast
lemma rightImageBound_dual: "\<midarrow>\<^sup>2,\<midarrow>\<^sup>2-DUAL \<diamond>\<^sub>\<rightarrow> \<odot>\<^sub>\<rightarrow>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<diamond>\<^sub>\<rightarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>2\<down>         \<down>\<midarrow>\<^sup>2
         \<sqdot> \<midarrow>\<odot>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>   " using dual_def rightImageBound_dual by blast

lemma leftDualImageBound_dual: "\<midarrow>\<^sup>2,\<midarrow>\<^sup>2-DUAL \<box>\<^sub>\<leftarrow> \<ominus>\<^sub>\<leftarrow>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<box>\<^sub>\<leftarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>2\<down>        \<down>\<midarrow>\<^sup>2
         \<sqdot> \<midarrow>\<ominus>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>   " using dual_def leftDualImageBound_dual by blast
lemma rightDualImageBound_dual: "\<midarrow>\<^sup>2,\<midarrow>\<^sup>2-DUAL \<box>\<^sub>\<rightarrow> \<ominus>\<^sub>\<rightarrow>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<box>\<^sub>\<rightarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>2\<down>        \<down>\<midarrow>\<^sup>2
         \<sqdot> \<midarrow>\<ominus>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>   " using dual_def rightDualImageBound_dual by blast


subsubsection \<open>Adjunctions (illustrated with diagrams)\<close>

text \<open>In order theory it is not uncommon to refer to a (covariant) adjunction as a "residuation".\<close>
lemma leftImage_residuation:  "(\<subseteq>),(\<subseteq>)-ADJ (R-\<diamond>\<^sub>\<leftarrow>) (R-\<box>\<^sub>\<rightarrow>)"  unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<box>\<^sub>\<rightarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>           \<up>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<diamond>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>    " by (simp add: leftImage_residuation)
lemma rightImage_residuation: "(\<subseteq>),(\<subseteq>)-ADJ (R-\<diamond>\<^sub>\<rightarrow>) (R-\<box>\<^sub>\<leftarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<box>\<^sub>\<leftarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>           \<up>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<diamond>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>    " by (simp add: rightImage_residuation)

text \<open>We may refer to a residuation between complements of operators as a "co-residuation" (between the operators).\<close>
lemma leftBound_coresiduation:  "(\<subseteq>),(\<subseteq>)-ADJ (R-\<odot>\<^sub>\<leftarrow>)\<^sup>\<midarrow> (R-\<ominus>\<^sub>\<rightarrow>)\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>(R-\<ominus>\<^sub>\<rightarrow>)\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>              \<up>(\<subseteq>)
          \<sqdot> \<midarrow>(R-\<odot>\<^sub>\<leftarrow>)\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: leftBound_coresiduation)
lemma rightBound_coresiduation: "(\<subseteq>),(\<subseteq>)-ADJ (R-\<odot>\<^sub>\<rightarrow>)\<^sup>\<midarrow> (R-\<ominus>\<^sub>\<leftarrow>)\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>(R-\<ominus>\<^sub>\<leftarrow>)\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>              \<up>(\<subseteq>)
          \<sqdot> \<midarrow>(R-\<odot>\<^sub>\<rightarrow>)\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: rightBound_coresiduation)

text \<open>There is a Galois connection between the right and left bounds.\<close>
lemma rightBound_galois: "(\<subseteq>),(\<subseteq>)-GAL (R-\<odot>\<^sub>\<rightarrow>) (R-\<odot>\<^sub>\<leftarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<odot>\<^sub>\<leftarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>           \<down>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<odot>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>    " by (simp add: rightBound_galois)
text \<open>We shall refer to a Galois connection with reversed orderings as a "dual-Galois-connection".\<close>
lemma leftDualBound_dualgalois: "(\<supseteq>),(\<supseteq>)-GAL (R-\<ominus>\<^sub>\<leftarrow>) (R-\<ominus>\<^sub>\<rightarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<ominus>\<^sub>\<rightarrow> \<midarrow> \<sqdot> 
      (\<supseteq>)\<up>           \<down>(\<supseteq>)
          \<sqdot> \<midarrow>R-\<ominus>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>    " by (simp add: leftDualBound_dualgalois)

text \<open>We also refer to a (dual) Galois connection between complements of operators as "(dual) conjugation".\<close>
lemma rightImage_conjugation: "(\<subseteq>),(\<subseteq>)-GAL (R-\<diamond>\<^sub>\<rightarrow>)\<^sup>\<midarrow> (R-\<diamond>\<^sub>\<leftarrow>)\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>(R-\<diamond>\<^sub>\<leftarrow>)\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>              \<down>(\<subseteq>)
          \<sqdot> \<midarrow>(R-\<diamond>\<^sub>\<rightarrow>)\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: rightImage_conjugation)
lemma leftDualImage_dualconjugation: "(\<supseteq>),(\<supseteq>)-GAL (R-\<box>\<^sub>\<leftarrow>)\<^sup>\<midarrow> (R-\<box>\<^sub>\<rightarrow>)\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>(R-\<box>\<^sub>\<rightarrow>)\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<supseteq>)\<up>              \<down>(\<supseteq>)
          \<sqdot> \<midarrow>(R-\<box>\<^sub>\<leftarrow>)\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: leftDualImage_dualconjugation)


subsubsection \<open>Operators for N-ary Relations\<close>

text \<open>Let us start by recalling that images and bounds are two sides of the same dual coin.\<close>
lemma "\<midarrow>\<^sup>2,\<midarrow>\<^sup>2-DUAL \<diamond>\<^sub>\<leftarrow> \<odot>\<^sub>\<leftarrow>" using leftImageBound_dual by simp
lemma "\<midarrow>\<^sup>2,\<midarrow>\<^sup>2-DUAL \<diamond>\<^sub>\<rightarrow> \<odot>\<^sub>\<rightarrow>" using rightImageBound_dual by simp

text \<open>Recall that for binary relations the analogous of preimage is the left-image operator, definable as
 the right-image of their converse. We now "lift" this idea to higher arities, noting that we must now
 consider six permutations, so we have to come up with a richer naming scheme. In the ternary case,
 we conveniently use a numbering scheme, related to the family of \<open>\<^bold>C\<^sub>a\<^sub>b\<^sub>c\<close> combinators (permutators).\<close>
abbreviation(input) image123::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<diamond>\<^sub>1\<^sub>2\<^sub>3")
  where "\<diamond>\<^sub>1\<^sub>2\<^sub>3 \<equiv> \<^bold>C\<^sub>1\<^sub>2\<^sub>3 \<ggreater> rightImage\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>2\<^sub>3\<close> as identity permutation is its own inverse (involutive)\<close>
abbreviation(input) image132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<diamond>\<^sub>1\<^sub>3\<^sub>2")
  where "\<diamond>\<^sub>1\<^sub>3\<^sub>2 \<equiv> \<^bold>C\<^sub>1\<^sub>3\<^sub>2 \<ggreater> rightImage\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<close> is its own inverse\<close>
abbreviation(input) image213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<diamond>\<^sub>2\<^sub>1\<^sub>3")
  where "\<diamond>\<^sub>2\<^sub>1\<^sub>3 \<equiv> \<^bold>C\<^sub>2\<^sub>1\<^sub>3 \<ggreater> rightImage\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<close> is its own inverse\<close>
abbreviation(input) image231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<diamond>\<^sub>2\<^sub>3\<^sub>1")
  where "\<diamond>\<^sub>2\<^sub>3\<^sub>1 \<equiv> \<^bold>C\<^sub>3\<^sub>1\<^sub>2 \<ggreater> rightImage\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<^sub>3\<close> is the inverse of \<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<^sub>3\<close>\<close>
abbreviation(input) image312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<diamond>\<^sub>3\<^sub>1\<^sub>2")
  where "\<diamond>\<^sub>3\<^sub>1\<^sub>2 \<equiv> \<^bold>C\<^sub>2\<^sub>3\<^sub>1 \<ggreater> rightImage\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<^sub>3\<close> is the inverse of \<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<^sub>3\<close>\<close>
abbreviation(input) image321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<diamond>\<^sub>3\<^sub>2\<^sub>1")
  where "\<diamond>\<^sub>3\<^sub>2\<^sub>1 \<equiv> \<^bold>C\<^sub>3\<^sub>2\<^sub>1 \<ggreater> rightImage\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>2\<^sub>1/\<^bold>C\<^sub>3\<close> is its own inverse\<close>

notation(input) image123 ("_-\<diamond>\<^sub>1\<^sub>2\<^sub>3") and image132 ("_-\<diamond>\<^sub>1\<^sub>3\<^sub>2") and
                image213 ("_-\<diamond>\<^sub>2\<^sub>1\<^sub>3") and image231 ("_-\<diamond>\<^sub>2\<^sub>3\<^sub>1") and 
                image312 ("_-\<diamond>\<^sub>3\<^sub>1\<^sub>2") and image321 ("_-\<diamond>\<^sub>3\<^sub>2\<^sub>1")

lemma "R-\<diamond>\<^sub>1\<^sub>2\<^sub>3 = (\<lambda>A B. \<lambda>c. \<exists>a b. R a b c \<and> A a \<and> B b)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<diamond>\<^sub>1\<^sub>3\<^sub>2 = (\<lambda>A C. \<lambda>b. \<exists>a c. R a b c \<and> A a \<and> C c)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<diamond>\<^sub>2\<^sub>1\<^sub>3 = (\<lambda>B A. \<lambda>c. \<exists>b a. R a b c \<and> B b \<and> A a)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<diamond>\<^sub>2\<^sub>3\<^sub>1 = (\<lambda>B C. \<lambda>a. \<exists>b c. R a b c \<and> B b \<and> C c)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<diamond>\<^sub>3\<^sub>1\<^sub>2 = (\<lambda>C A. \<lambda>b. \<exists>c a. R a b c \<and> C c \<and> A a)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<diamond>\<^sub>3\<^sub>2\<^sub>1 = (\<lambda>C B. \<lambda>a. \<exists>c b. R a b c \<and> C c \<and> B b)" unfolding rel_defs func_defs comb_defs by metis

text \<open>Note that the images (in general: all operators) of a relation can be interrelated via permutation.\<close>
lemma "R-\<diamond>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<diamond>\<^sub>1\<^sub>3\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<diamond>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<diamond>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<diamond>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<diamond>\<^sub>2\<^sub>3\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<diamond>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>1\<^sub>2 R)-\<diamond>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<diamond>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<diamond>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment>\<open>...\<open>R-\<diamond>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<diamond>\<^sub>i\<^sub>j\<^sub>k\<close>\<close> \<comment> \<open>same permutation\<close>
lemma "R-\<diamond>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<diamond>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<diamond>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<diamond>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment>\<open>...\<open>R-\<diamond>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<diamond>\<^sub>i\<^sub>k\<^sub>j\<close>\<close> \<comment> \<open>swap 2 and 3\<close>
lemma "R-\<diamond>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<diamond>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<diamond>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<diamond>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment>\<open>...\<open>R-\<diamond>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<diamond>\<^sub>j\<^sub>i\<^sub>k\<close>\<close> \<comment> \<open>swap 1 and 2\<close>
lemma "R-\<diamond>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<diamond>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<diamond>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<diamond>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment>\<open>...\<open>R-\<diamond>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<diamond>\<^sub>j\<^sub>k\<^sub>i\<close>\<close> \<comment> \<open>left rotation\<close>
lemma "R-\<diamond>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<diamond>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<diamond>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<diamond>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
\<comment>\<open>...\<open>R-\<diamond>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<diamond>\<^sub>k\<^sub>i\<^sub>j\<close>\<close> \<comment> \<open>right rotation\<close>
lemma "R-\<diamond>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<diamond>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<diamond>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<diamond>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
\<comment>\<open>...\<open>R-\<diamond>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<diamond>\<^sub>k\<^sub>j\<^sub>i\<close>\<close> \<comment> \<open>full reverse\<close>


text \<open>Analogously as the case for images/preimages, when we "lift" the notion of bounds to higher arities
 we consider several permutations, and come up with a numbering scheme based on permutations.\<close>
abbreviation(input) bound123::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<odot>\<^sub>1\<^sub>2\<^sub>3")
  where "\<odot>\<^sub>1\<^sub>2\<^sub>3 \<equiv> \<^bold>C\<^sub>1\<^sub>2\<^sub>3 \<ggreater> rightBound\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>2\<^sub>3\<close> being identity is its own inverse (involutive)\<close>
abbreviation(input) bound132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<odot>\<^sub>1\<^sub>3\<^sub>2")
  where "\<odot>\<^sub>1\<^sub>3\<^sub>2 \<equiv> \<^bold>C\<^sub>1\<^sub>3\<^sub>2 \<ggreater> rightBound\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<close> is its own inverse\<close>
abbreviation(input) bound213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<odot>\<^sub>2\<^sub>1\<^sub>3")
  where "\<odot>\<^sub>2\<^sub>1\<^sub>3 \<equiv> \<^bold>C\<^sub>2\<^sub>1\<^sub>3 \<ggreater> rightBound\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<close> is its own inverse\<close>
abbreviation(input) bound231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<odot>\<^sub>2\<^sub>3\<^sub>1")
  where "\<odot>\<^sub>2\<^sub>3\<^sub>1 \<equiv> \<^bold>C\<^sub>3\<^sub>1\<^sub>2 \<ggreater> rightBound\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<^sub>3\<close> is the inverse of \<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<^sub>3\<close>\<close>
abbreviation(input) bound312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<odot>\<^sub>3\<^sub>1\<^sub>2")
  where "\<odot>\<^sub>3\<^sub>1\<^sub>2 \<equiv> \<^bold>C\<^sub>2\<^sub>3\<^sub>1 \<ggreater> rightBound\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<^sub>3\<close> is the inverse of \<open>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<^sub>3\<close>\<close>
abbreviation(input) bound321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<odot>\<^sub>3\<^sub>2\<^sub>1")
  where "\<odot>\<^sub>3\<^sub>2\<^sub>1 \<equiv> \<^bold>C\<^sub>3\<^sub>2\<^sub>1 \<ggreater> rightBound\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>2\<^sub>1/\<^bold>C\<^sub>3\<close> is its own inverse\<close>

notation(input) bound123 ("_-\<odot>\<^sub>1\<^sub>2\<^sub>3") and bound132 ("_-\<odot>\<^sub>1\<^sub>3\<^sub>2") and
                bound213 ("_-\<odot>\<^sub>2\<^sub>1\<^sub>3") and bound231 ("_-\<odot>\<^sub>2\<^sub>3\<^sub>1") and 
                bound312 ("_-\<odot>\<^sub>3\<^sub>1\<^sub>2") and bound321 ("_-\<odot>\<^sub>3\<^sub>2\<^sub>1")

lemma "R-\<odot>\<^sub>1\<^sub>2\<^sub>3 = (\<lambda>A B. \<lambda>c. \<forall>a b. A a \<rightarrow> B b \<rightarrow> R a b c)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<odot>\<^sub>1\<^sub>3\<^sub>2 = (\<lambda>A C. \<lambda>b. \<forall>a c. A a \<rightarrow> C c \<rightarrow> R a b c)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<odot>\<^sub>2\<^sub>1\<^sub>3 = (\<lambda>B A. \<lambda>c. \<forall>b a. B b \<rightarrow> A a \<rightarrow> R a b c)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<odot>\<^sub>2\<^sub>3\<^sub>1 = (\<lambda>B C. \<lambda>a. \<forall>b c. B b \<rightarrow> C c \<rightarrow> R a b c)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<odot>\<^sub>3\<^sub>1\<^sub>2 = (\<lambda>C A. \<lambda>b. \<forall>c a. C c \<rightarrow> A a \<rightarrow> R a b c)" unfolding rel_defs func_defs comb_defs by metis
lemma "R-\<odot>\<^sub>3\<^sub>2\<^sub>1 = (\<lambda>C B. \<lambda>a. \<forall>c b. C c \<rightarrow> B b \<rightarrow> R a b c)" unfolding rel_defs func_defs comb_defs by metis

text \<open>Again, note that the different bound operators can be similarly interrelated by permutation.\<close>
lemma "R-\<odot>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<odot>\<^sub>1\<^sub>3\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<odot>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<odot>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<odot>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<odot>\<^sub>2\<^sub>3\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<odot>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>1\<^sub>2 R)-\<odot>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<odot>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<odot>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<odot>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<odot>\<^sub>i\<^sub>j\<^sub>k\<close>\<close> \<comment> \<open>same permutation\<close>
lemma "R-\<odot>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<odot>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<odot>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<odot>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<odot>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<odot>\<^sub>i\<^sub>k\<^sub>j\<close>\<close> \<comment> \<open>swap 2 and 3\<close>
lemma "R-\<odot>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<odot>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<odot>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<odot>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<odot>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<odot>\<^sub>j\<^sub>i\<^sub>k\<close>\<close>  \<comment> \<open>swap 1 and 2\<close>
lemma "R-\<odot>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<odot>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<odot>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<odot>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<odot>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<odot>\<^sub>j\<^sub>k\<^sub>i\<close>\<close> \<comment> \<open>left rotation\<close>
lemma "R-\<odot>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<odot>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<odot>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<odot>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<odot>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<odot>\<^sub>k\<^sub>i\<^sub>j\<close>\<close> \<comment> \<open>right rotation\<close>
lemma "R-\<odot>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<odot>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<odot>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<odot>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<odot>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<odot>\<^sub>k\<^sub>j\<^sub>i\<close>\<close> \<comment> \<open>full reverse\<close>


subsubsection \<open>Dual-Images and Dual-Bounds\<close>

text \<open>As in the case of binary relations, (left-, right-, ...) image-operators have their duals too.\<close>
abbreviation(input) dualImage123::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<box>\<^sub>1\<^sub>2\<^sub>3")
  where "\<box>\<^sub>1\<^sub>2\<^sub>3 \<equiv> \<^bold>C\<^sub>1\<^sub>2\<^sub>3 \<ggreater> rightDualImage\<^sub>2"     \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>2\<^sub>3\<close> being identity is its own inverse (involutive)\<close>
abbreviation(input) dualImage132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<box>\<^sub>1\<^sub>3\<^sub>2")
  where "\<box>\<^sub>1\<^sub>3\<^sub>2 \<equiv> \<^bold>C\<^sub>1\<^sub>3\<^sub>2 \<ggreater> rightDualImage\<^sub>2"     \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<close> is its own inverse\<close>
abbreviation(input) dualImage213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<box>\<^sub>2\<^sub>1\<^sub>3")
  where "\<box>\<^sub>2\<^sub>1\<^sub>3 \<equiv> \<^bold>C\<^sub>2\<^sub>1\<^sub>3 \<ggreater> rightDualImage\<^sub>2"     \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<close> is its own inverse\<close>
abbreviation(input) dualImage231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<box>\<^sub>2\<^sub>3\<^sub>1")
  where "\<box>\<^sub>2\<^sub>3\<^sub>1 \<equiv> \<^bold>C\<^sub>3\<^sub>1\<^sub>2 \<ggreater> rightDualImage\<^sub>2"     \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<^sub>3\<close> is the inverse of \<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<^sub>3\<close>\<close>
abbreviation(input) dualImage312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<box>\<^sub>3\<^sub>1\<^sub>2")
  where "\<box>\<^sub>3\<^sub>1\<^sub>2 \<equiv> \<^bold>C\<^sub>2\<^sub>3\<^sub>1 \<ggreater> rightDualImage\<^sub>2"     \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<^sub>3\<close> is the inverse of \<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<^sub>3\<close>\<close>
abbreviation(input) dualImage321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<box>\<^sub>3\<^sub>2\<^sub>1")
  where "\<box>\<^sub>3\<^sub>2\<^sub>1 \<equiv> \<^bold>C\<^sub>3\<^sub>2\<^sub>1 \<ggreater> rightDualImage\<^sub>2"     \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>2\<^sub>1/\<^bold>C\<^sub>3\<close> is its own inverse\<close>

notation(input) dualImage123 ("_-\<box>\<^sub>1\<^sub>2\<^sub>3") and dualImage132 ("_-\<box>\<^sub>1\<^sub>3\<^sub>2") and 
                dualImage213 ("_-\<box>\<^sub>2\<^sub>1\<^sub>3") and dualImage231 ("_-\<box>\<^sub>2\<^sub>3\<^sub>1") and
                dualImage312 ("_-\<box>\<^sub>3\<^sub>1\<^sub>2") and dualImage321 ("_-\<box>\<^sub>3\<^sub>2\<^sub>1")

lemma "R-\<box>\<^sub>1\<^sub>2\<^sub>3 = (\<lambda>A B. \<lambda>c. \<forall>a b. R a b c \<rightarrow> A a \<or> B b)" unfolding rel_defs func_defs comb_defs ..
lemma "R-\<box>\<^sub>1\<^sub>3\<^sub>2 = (\<lambda>A C. \<lambda>b. \<forall>a c. R a b c \<rightarrow> A a \<or> C c)" unfolding rel_defs func_defs comb_defs ..
lemma "R-\<box>\<^sub>2\<^sub>1\<^sub>3 = (\<lambda>B A. \<lambda>c. \<forall>b a. R a b c \<rightarrow> B b \<or> A a)" unfolding rel_defs func_defs comb_defs ..
lemma "R-\<box>\<^sub>2\<^sub>3\<^sub>1 = (\<lambda>B C. \<lambda>a. \<forall>b c. R a b c \<rightarrow> B b \<or> C c)" unfolding rel_defs func_defs comb_defs ..
lemma "R-\<box>\<^sub>3\<^sub>2\<^sub>1 = (\<lambda>C B. \<lambda>a. \<forall>c b. R a b c \<rightarrow> C c \<or> B b)" unfolding rel_defs func_defs comb_defs ..
lemma "R-\<box>\<^sub>3\<^sub>1\<^sub>2 = (\<lambda>C A. \<lambda>b. \<forall>c a. R a b c \<rightarrow> C c \<or> A a)" unfolding rel_defs func_defs comb_defs ..

text \<open>Again, note that the dual-images of a relation can be similarly interrelated by permutation.\<close>
lemma "R-\<box>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<box>\<^sub>1\<^sub>3\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<box>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<box>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<box>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<box>\<^sub>2\<^sub>3\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<box>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>1\<^sub>2 R)-\<box>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<box>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<box>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<box>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<box>\<^sub>i\<^sub>j\<^sub>k\<close>\<close> \<comment> \<open>same permutation\<close>
lemma "R-\<box>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<box>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<box>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<box>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<box>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<box>\<^sub>i\<^sub>k\<^sub>j\<close>\<close> \<comment> \<open>swap 2 and 3\<close>
lemma "R-\<box>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<box>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<box>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<box>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<box>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<box>\<^sub>j\<^sub>i\<^sub>k\<close>\<close> \<comment> \<open>swap 1 and 2\<close>
lemma "R-\<box>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<box>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<box>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<box>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<box>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<box>\<^sub>j\<^sub>k\<^sub>i\<close>\<close> \<comment> \<open>left rotation\<close>
lemma "R-\<box>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<box>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<box>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<box>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<box>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<box>\<^sub>k\<^sub>i\<^sub>j\<close>\<close> \<comment> \<open>right rotation\<close>
lemma "R-\<box>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<box>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<box>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<box>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<box>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<box>\<^sub>k\<^sub>j\<^sub>i\<close>\<close> \<comment> \<open>full reverse\<close>

abbreviation(input) dualBound123::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<ominus>\<^sub>1\<^sub>2\<^sub>3")
  where "\<ominus>\<^sub>1\<^sub>2\<^sub>3 \<equiv> \<^bold>C\<^sub>1\<^sub>2\<^sub>3 \<ggreater> rightDualBound\<^sub>2" \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>2\<^sub>3\<close> as identity permutation is its own inverse (involutive)\<close>
abbreviation(input) dualBound132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<ominus>\<^sub>1\<^sub>3\<^sub>2")
  where "\<ominus>\<^sub>1\<^sub>3\<^sub>2 \<equiv> \<^bold>C\<^sub>1\<^sub>3\<^sub>2 \<ggreater> rightDualBound\<^sub>2" \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<close> is its own inverse\<close>
abbreviation(input) dualBound213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<ominus>\<^sub>2\<^sub>1\<^sub>3")
  where "\<ominus>\<^sub>2\<^sub>1\<^sub>3 \<equiv> \<^bold>C\<^sub>2\<^sub>1\<^sub>3 \<ggreater> rightDualBound\<^sub>2" \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<close> is its own inverse\<close>
abbreviation(input) dualBound231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<ominus>\<^sub>2\<^sub>3\<^sub>1")
  where "\<ominus>\<^sub>2\<^sub>3\<^sub>1 \<equiv> \<^bold>C\<^sub>3\<^sub>1\<^sub>2 \<ggreater> rightDualBound\<^sub>2" \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<^sub>3\<close> is the inverse of \<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<^sub>3\<close>\<close>
abbreviation(input) dualBound312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<ominus>\<^sub>3\<^sub>1\<^sub>2")
  where "\<ominus>\<^sub>3\<^sub>1\<^sub>2 \<equiv> \<^bold>C\<^sub>2\<^sub>3\<^sub>1 \<ggreater> rightDualBound\<^sub>2" \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<^sub>3\<close> is the inverse of \<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<^sub>3\<close>\<close>
abbreviation(input) dualBound321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<ominus>\<^sub>3\<^sub>2\<^sub>1")
  where "\<ominus>\<^sub>3\<^sub>2\<^sub>1 \<equiv> \<^bold>C\<^sub>3\<^sub>2\<^sub>1 \<ggreater> rightDualBound\<^sub>2" \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>2\<^sub>1/\<^bold>C\<^sub>3\<close> is its own inverse\<close>

notation(input) dualBound123 ("_-\<ominus>\<^sub>1\<^sub>2\<^sub>3") and dualBound132 ("_-\<ominus>\<^sub>1\<^sub>3\<^sub>2") and
                dualBound213 ("_-\<ominus>\<^sub>2\<^sub>1\<^sub>3") and dualBound231 ("_-\<ominus>\<^sub>2\<^sub>3\<^sub>1") and 
                dualBound312 ("_-\<ominus>\<^sub>3\<^sub>1\<^sub>2") and dualBound321 ("_-\<ominus>\<^sub>3\<^sub>2\<^sub>1")

lemma "R-\<ominus>\<^sub>1\<^sub>2\<^sub>3 = (\<lambda>A B. \<lambda>c. \<exists>a b. \<not>A a \<and> \<not>B b \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<ominus>\<^sub>1\<^sub>3\<^sub>2 = (\<lambda>A C. \<lambda>b. \<exists>a c. \<not>A a \<and> \<not>C c \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<ominus>\<^sub>2\<^sub>1\<^sub>3 = (\<lambda>B A. \<lambda>c. \<exists>b a. \<not>B b \<and> \<not>A a \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<ominus>\<^sub>2\<^sub>3\<^sub>1 = (\<lambda>B C. \<lambda>a. \<exists>b c. \<not>B b \<and> \<not>C c \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<ominus>\<^sub>3\<^sub>1\<^sub>2 = (\<lambda>C A. \<lambda>b. \<exists>c a. \<not>C c \<and> \<not>A a \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<ominus>\<^sub>3\<^sub>2\<^sub>1 = (\<lambda>C B. \<lambda>a. \<exists>c b. \<not>C c \<and> \<not>B b \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast

text \<open>Similarly, dual-bounds can also be similarly interrelated by permutation.\<close>
lemma "R-\<ominus>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<ominus>\<^sub>1\<^sub>3\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<ominus>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<ominus>\<^sub>2\<^sub>3\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>1\<^sub>2 R)-\<ominus>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<ominus>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<ominus>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<ominus>\<^sub>i\<^sub>j\<^sub>k\<close>\<close> \<comment> \<open>same permutation\<close>
lemma "R-\<ominus>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<ominus>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<ominus>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<ominus>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<ominus>\<^sub>i\<^sub>k\<^sub>j\<close>\<close> \<comment> \<open>swap 2 and 3\<close>
lemma "R-\<ominus>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<ominus>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<ominus>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<ominus>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<ominus>\<^sub>j\<^sub>i\<^sub>k\<close>\<close> \<comment> \<open>swap 1 and 2\<close>
lemma "R-\<ominus>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<ominus>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<ominus>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<ominus>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<ominus>\<^sub>j\<^sub>k\<^sub>i\<close>\<close> \<comment> \<open>left rotation\<close>
lemma "R-\<ominus>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<ominus>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<ominus>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<ominus>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<ominus>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<ominus>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<ominus>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<ominus>\<^sub>k\<^sub>j\<^sub>i\<close>\<close> \<comment> \<open>full reverse\<close>


subsection \<open>Transformations\<close>

text \<open>We can always make a unary image/bound operator out of its binary counterpart as follows.\<close>
lemma "R-\<diamond>\<^sub>\<rightarrow> A = (\<^bold>K R)-\<diamond>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<odot>\<^sub>\<rightarrow> A = (\<^bold>K R)-\<odot>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<diamond>\<^sub>\<leftarrow> A = (\<^bold>K R\<^sup>\<smile>)-\<diamond>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<odot>\<^sub>\<leftarrow> A = (\<^bold>K R\<^sup>\<smile>)-\<odot>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis

text \<open>And the same holds for the dual variants.\<close>
lemma "R-\<box>\<^sub>\<rightarrow> A = (\<^bold>K R)-\<box>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<ominus>\<^sub>\<rightarrow> A = (\<^bold>K R)-\<ominus>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<box>\<^sub>\<leftarrow> A = (\<^bold>K R\<^sup>\<smile>)-\<box>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<ominus>\<^sub>\<leftarrow> A = (\<^bold>K R\<^sup>\<smile>)-\<ominus>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis

text \<open>The converse conversion is not possible in general:\<close>
proposition "\<forall>T. \<exists>R. \<forall>A. (T-\<diamond>\<^sub>1\<^sub>2\<^sub>3 A A) = (R-\<diamond>\<^sub>\<rightarrow> A)" nitpick \<comment> \<open>countermodel found\<close> oops
text \<open>In particular, this does not hold (for arbitrary T)\<close>  (*TODO: how to restrict T so that it holds?*)
proposition "(T-\<diamond>\<^sub>1\<^sub>2\<^sub>3 A A) = ((\<lambda>a b. T a a b)-\<diamond>\<^sub>\<rightarrow> A)" nitpick \<comment> \<open>countermodel found\<close> oops

text \<open>Note, among others:\<close>
lemma "(\<inter>) = \<Q>\<^sub>3-\<diamond>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<union>) = \<Q>\<^sub>3-\<box>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<Rightarrow>) = \<midarrow> \<ggreater> (\<Q>\<^sub>3-\<box>\<^sub>1\<^sub>2\<^sub>3)" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<inter>) \<ggreater>\<^sub>2 \<midarrow> = \<D>\<^sub>3-\<odot>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<union>) \<ggreater>\<^sub>2 \<midarrow> = \<D>\<^sub>3-\<ominus>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<setminus>) = \<midarrow> \<ggreater> (\<D>\<^sub>3-\<ominus>\<^sub>1\<^sub>2\<^sub>3)" unfolding rel_defs comb_defs func_defs by fast
text \<open>In fact, the previous hold for any permutation (ternary dis/equality being also fully commutative).\<close>
lemma "(\<inter>) = \<Q>\<^sub>3-\<diamond>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<union>) = \<Q>\<^sub>3-\<box>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<Rightarrow>) = \<midarrow> \<ggreater> (\<Q>\<^sub>3-\<box>\<^sub>3\<^sub>1\<^sub>2)" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<inter>) \<ggreater>\<^sub>2 \<midarrow> = \<D>\<^sub>3-\<odot>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<union>) \<ggreater>\<^sub>2 \<midarrow> = \<D>\<^sub>3-\<ominus>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs func_defs by fast
lemma "(\<setminus>) = \<midarrow> \<ggreater> (\<D>\<^sub>3-\<ominus>\<^sub>3\<^sub>1\<^sub>2)" unfolding rel_defs comb_defs func_defs by fast
\<comment> \<open>... and so on\<close>


subsection \<open>Adjunctions\<close>
text \<open>Similar adjunction conditions obtain among binary set-operators as for their unary counterparts.\<close>

subsubsection \<open>Residuation and Coresiduation\<close>
text \<open>Residuation (coresiduation) between \<open>\<diamond>\<close> and \<open>\<box>\<close> obtains when swapping second and third parameters
 and complementing/negating the first argument.\<close>

text \<open>Noting that:\<close>
lemma "(\<midarrow> \<ggreater> (R-\<box>\<^sub>1\<^sub>2\<^sub>3)) A B = R-\<box>\<^sub>1\<^sub>2\<^sub>3 (\<midarrow>A) B" unfolding rel_defs func_defs comb_defs ..

text \<open>We have:\<close>
lemma image123_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>1\<^sub>2\<^sub>3) (\<midarrow> \<ggreater> (R-\<box>\<^sub>1\<^sub>3\<^sub>2))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image132_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>1\<^sub>3\<^sub>2) (\<midarrow> \<ggreater> (R-\<box>\<^sub>1\<^sub>2\<^sub>3))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image213_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>2\<^sub>1\<^sub>3) (\<midarrow> \<ggreater> (R-\<box>\<^sub>2\<^sub>3\<^sub>1))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image231_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>2\<^sub>3\<^sub>1) (\<midarrow> \<ggreater> (R-\<box>\<^sub>2\<^sub>1\<^sub>3))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image312_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>3\<^sub>1\<^sub>2) (\<midarrow> \<ggreater> (R-\<box>\<^sub>3\<^sub>2\<^sub>1))" unfolding adj_defs rel_defs func_defs comb_defs by metis
lemma image321_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>3\<^sub>2\<^sub>1) (\<midarrow> \<ggreater> (R-\<box>\<^sub>3\<^sub>1\<^sub>2))" unfolding adj_defs rel_defs func_defs comb_defs by metis

lemma dualimage123_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<ggreater> (R-\<diamond>\<^sub>1\<^sub>2\<^sub>3)) (R-\<box>\<^sub>1\<^sub>3\<^sub>2)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualimage132_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<ggreater> (R-\<diamond>\<^sub>1\<^sub>3\<^sub>2)) (R-\<box>\<^sub>1\<^sub>2\<^sub>3)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualimage213_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<ggreater> (R-\<diamond>\<^sub>2\<^sub>1\<^sub>3)) (R-\<box>\<^sub>2\<^sub>3\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualimage231_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<ggreater> (R-\<diamond>\<^sub>2\<^sub>3\<^sub>1)) (R-\<box>\<^sub>2\<^sub>1\<^sub>3)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualimage312_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<ggreater> (R-\<diamond>\<^sub>3\<^sub>1\<^sub>2)) (R-\<box>\<^sub>3\<^sub>2\<^sub>1)" unfolding adj_defs rel_defs func_defs comb_defs by metis
lemma dualimage321_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<ggreater> (R-\<diamond>\<^sub>3\<^sub>2\<^sub>1)) (R-\<box>\<^sub>3\<^sub>1\<^sub>2)" unfolding adj_defs rel_defs func_defs comb_defs by metis


subsubsection \<open>Galois-connection and its Dual\<close>
text \<open>(Dual)Galois-connections for pairs of \<open>\<odot>\<close> (\<open>\<ominus>\<close>) also obtain when swapping second and third parameters.\<close>

lemma bound123_galois: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 (R-\<odot>\<^sub>1\<^sub>2\<^sub>3) (R-\<odot>\<^sub>1\<^sub>3\<^sub>2)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma bound213_galois: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 (R-\<odot>\<^sub>2\<^sub>1\<^sub>3) (R-\<odot>\<^sub>2\<^sub>3\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma bound312_galois: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 (R-\<odot>\<^sub>3\<^sub>1\<^sub>2) (R-\<odot>\<^sub>3\<^sub>2\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by fastforce 

lemma dualBound123_dualgalois: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 (R-\<ominus>\<^sub>1\<^sub>2\<^sub>3) (R-\<ominus>\<^sub>1\<^sub>3\<^sub>2)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualBound213_dualgalois: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 (R-\<ominus>\<^sub>2\<^sub>1\<^sub>3) (R-\<ominus>\<^sub>2\<^sub>3\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualBound312_dualgalois: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 (R-\<ominus>\<^sub>3\<^sub>1\<^sub>2) (R-\<ominus>\<^sub>3\<^sub>2\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by metis


subsubsection \<open>Conjugation and its Dual\<close>
text \<open>Similarly, (dual)conjugations for pairs of \<open>\<diamond>\<close> (\<open>\<box>\<close>) obtain when swapping second and third parameters.\<close>

lemma image123_conjugation: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 ((R-\<diamond>\<^sub>1\<^sub>2\<^sub>3) \<ggreater>\<^sub>2 \<midarrow>) ((R-\<diamond>\<^sub>1\<^sub>3\<^sub>2) \<ggreater>\<^sub>2 \<midarrow>)"  unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image213_conjugation: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 ((R-\<diamond>\<^sub>2\<^sub>1\<^sub>3) \<ggreater>\<^sub>2 \<midarrow>) ((R-\<diamond>\<^sub>2\<^sub>3\<^sub>1) \<ggreater>\<^sub>2 \<midarrow>)"  unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image312_conjugation: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 ((R-\<diamond>\<^sub>3\<^sub>1\<^sub>2) \<ggreater>\<^sub>2 \<midarrow>) ((R-\<diamond>\<^sub>3\<^sub>2\<^sub>1) \<ggreater>\<^sub>2 \<midarrow>)"  unfolding adj_defs rel_defs comb_defs func_defs by fastforce

lemma dualImage123_dualconjugation: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 ((R-\<box>\<^sub>1\<^sub>2\<^sub>3) \<ggreater>\<^sub>2 \<midarrow>) ((R-\<box>\<^sub>1\<^sub>3\<^sub>2) \<ggreater>\<^sub>2 \<midarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualImage213_dualconjugation: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 ((R-\<box>\<^sub>2\<^sub>1\<^sub>3) \<ggreater>\<^sub>2 \<midarrow>) ((R-\<box>\<^sub>2\<^sub>3\<^sub>1) \<ggreater>\<^sub>2 \<midarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualImage312_dualconjugation: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 ((R-\<box>\<^sub>3\<^sub>1\<^sub>2) \<ggreater>\<^sub>2 \<midarrow>) ((R-\<box>\<^sub>3\<^sub>2\<^sub>1) \<ggreater>\<^sub>2 \<midarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by metis

end