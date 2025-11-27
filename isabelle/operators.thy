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
                leftBound ("_-\<odot>\<^sub>\<leftarrow>") and leftDualBound ("_-\<oslash>\<^sub>\<leftarrow>") and
                rightBound ("_-\<odot>\<^sub>\<rightarrow>") and rightDualBound ("_-\<oslash>\<^sub>\<rightarrow>")
\<comment> \<open>and extend this notation to the transformations themselves\<close>
notation(input) leftImage ("\<diamond>\<^sub>\<leftarrow>") and leftDualImage ("\<box>\<^sub>\<leftarrow>") and 
                rightImage ("\<diamond>\<^sub>\<rightarrow>") and rightDualImage ("\<box>\<^sub>\<rightarrow>") and
                leftBound ("\<odot>\<^sub>\<leftarrow>") and leftDualBound ("\<oslash>\<^sub>\<leftarrow>") and
                rightBound ("\<odot>\<^sub>\<rightarrow>") and rightDualBound ("\<oslash>\<^sub>\<rightarrow>")


subsubsection \<open>Order Embedding\<close>

text \<open>This is a good moment to recall that unary operations on sets (set-operations) are also relations...\<close>
term "(F :: SetOp('a,'b)) :: Rel(Set('a),'b)"
text \<open>... and thus can be ordered as such. Thus read \<open>F \<subseteq>\<^sup>r G\<close> as: "F is a sub-operation of G".\<close>
lemma fixes F::"SetOp('a,'b)" and G::"SetOp('a,'b)"
  shows "F \<subseteq>\<^sup>r G = (\<forall>A. F A \<subseteq> G A)" unfolding rel_defs comb_defs func_defs ..

text \<open>Operators are (dual) embeddings between the sub-relation and the (converse of) sub-operation ordering.\<close>
lemma rightImage_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding \<diamond>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs unfolding func_defs comb_defs by fast
lemma leftImage_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding \<diamond>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma rightDualImage_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding \<box>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma leftDualImage_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding \<box>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma rightBound_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding \<odot>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma leftBound_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding \<odot>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma rightDualBound_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding \<oslash>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by fast
lemma leftDualBound_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding \<oslash>\<^sub>\<leftarrow>"
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
lemma rightDualBound_hom_id: "\<D>-\<oslash>\<^sub>\<rightarrow> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_id: "\<D>-\<oslash>\<^sub>\<leftarrow> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto

text \<open>Moreover, they map the relational composition \<open>\<circ>\<^sup>r\<close> (resp. its dual \<open>\<bullet>\<^sup>r\<close>) to their functional counterparts.\<close>
lemma rightImage_hom_comp: "(A \<circ>\<^sup>r B)-\<diamond>\<^sub>\<rightarrow> = (A-\<diamond>\<^sub>\<rightarrow>) \<circ> (B-\<diamond>\<^sub>\<rightarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_hom_comp: "(A \<circ>\<^sup>r B)-\<diamond>\<^sub>\<leftarrow> = (B-\<diamond>\<^sub>\<leftarrow>) \<circ> (A-\<diamond>\<^sub>\<leftarrow>)"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualImage_hom_comp:  "(A \<circ>\<^sup>r B)-\<box>\<^sub>\<rightarrow> = (A-\<box>\<^sub>\<rightarrow>) \<circ> (B-\<box>\<^sub>\<rightarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_hom_comp: "(A \<circ>\<^sup>r B)-\<box>\<^sub>\<leftarrow> = (B-\<box>\<^sub>\<leftarrow>) \<circ> (A-\<box>\<^sub>\<leftarrow>)"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_hom_comp: "(A \<bullet>\<^sup>r B)-\<odot>\<^sub>\<rightarrow> = (A-\<odot>\<^sub>\<rightarrow>) \<bullet> (B-\<odot>\<^sub>\<rightarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_comp: "(A \<bullet>\<^sup>r B)-\<odot>\<^sub>\<leftarrow> = (B-\<odot>\<^sub>\<leftarrow>) \<bullet> (A-\<odot>\<^sub>\<leftarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_comp: "(A \<bullet>\<^sup>r B)-\<oslash>\<^sub>\<rightarrow> = (A-\<oslash>\<^sub>\<rightarrow>) \<bullet> (B-\<oslash>\<^sub>\<rightarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_comp: "(A \<bullet>\<^sup>r B)-\<oslash>\<^sub>\<leftarrow> = (B-\<oslash>\<^sub>\<leftarrow>) \<bullet> (A-\<oslash>\<^sub>\<leftarrow>)" 
  unfolding rel_defs func_defs comb_defs by auto

text \<open>Operators are also (dual) lattice homomorphisms from the BA of relations to the BA of set-operators.\<close>
lemma rightImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-\<diamond>\<^sub>\<rightarrow> = R\<^sub>1-\<diamond>\<^sub>\<rightarrow> \<union>\<^sup>r R\<^sub>2-\<diamond>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-\<diamond>\<^sub>\<leftarrow> = R\<^sub>1-\<diamond>\<^sub>\<leftarrow> \<union>\<^sup>r R\<^sub>2-\<diamond>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-\<odot>\<^sub>\<rightarrow> = R\<^sub>1-\<odot>\<^sub>\<rightarrow> \<inter>\<^sup>r R\<^sub>2-\<odot>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-\<odot>\<^sub>\<leftarrow> = R\<^sub>1-\<odot>\<^sub>\<leftarrow> \<inter>\<^sup>r R\<^sub>2-\<odot>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by auto
\<comment> \<open> dual ('anti') homomorphisms\<close>
lemma rightDualImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-\<box>\<^sub>\<rightarrow> = R\<^sub>1-\<box>\<^sub>\<rightarrow> \<inter>\<^sup>r R\<^sub>2-\<box>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-\<box>\<^sub>\<leftarrow> = R\<^sub>1-\<box>\<^sub>\<leftarrow> \<inter>\<^sup>r R\<^sub>2-\<box>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-\<oslash>\<^sub>\<rightarrow> = R\<^sub>1-\<oslash>\<^sub>\<rightarrow> \<union>\<^sup>r R\<^sub>2-\<oslash>\<^sub>\<rightarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-\<oslash>\<^sub>\<leftarrow> = R\<^sub>1-\<oslash>\<^sub>\<leftarrow> \<union>\<^sup>r R\<^sub>2-\<oslash>\<^sub>\<leftarrow>"
  unfolding rel_defs func_defs comb_defs by auto

text \<open>As for complement, we have a particular morphism property between images and bounds (cf. dualities below).\<close>
lemma rightImage_hom_compl: "(R\<^sup>\<midarrow>)-\<diamond>\<^sub>\<rightarrow> = (R-\<odot>\<^sub>\<rightarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_hom_compl: "(R\<^sup>\<midarrow>)-\<diamond>\<^sub>\<leftarrow> = (R-\<odot>\<^sub>\<leftarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualImage_hom_compl: "(R\<^sup>\<midarrow>)-\<box>\<^sub>\<rightarrow> = (R-\<oslash>\<^sub>\<rightarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_hom_compl: "(R\<^sup>\<midarrow>)-\<box>\<^sub>\<leftarrow> = (R-\<oslash>\<^sub>\<leftarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_hom_compl: "(R\<^sup>\<midarrow>)-\<odot>\<^sub>\<rightarrow> = (R-\<diamond>\<^sub>\<rightarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_compl: "(R\<^sup>\<midarrow>)-\<odot>\<^sub>\<leftarrow> = (R-\<diamond>\<^sub>\<leftarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_compl: "(R\<^sup>\<midarrow>)-\<oslash>\<^sub>\<rightarrow> = (R-\<box>\<^sub>\<rightarrow>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_compl: "(R\<^sup>\<midarrow>)-\<oslash>\<^sub>\<leftarrow> = (R-\<box>\<^sub>\<leftarrow>)\<^sup>\<midarrow>"
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

lemma leftBound_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<odot>\<^sub>\<leftarrow>) (R-\<oslash>\<^sub>\<leftarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma "  \<sqdot> \<midarrow>R-\<odot>\<^sub>\<leftarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<down>           \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<oslash>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>   " using dual_def leftBound_dual by blast
lemma rightBound_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<odot>\<^sub>\<rightarrow>) (R-\<oslash>\<^sub>\<rightarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma "  \<sqdot> \<midarrow>R-\<odot>\<^sub>\<rightarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<down>           \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<oslash>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>   " using dual_def rightBound_dual by blast

text \<open>Recall that set-operators are also relations (and thus can be ordered as such). We thus have following
  dualities between the transformations themselves (cf. morphisms wrt. complement discussed above).\<close>
lemma leftImageBound_dual: "\<midarrow>\<^sup>r,\<midarrow>\<^sup>r-DUAL \<diamond>\<^sub>\<leftarrow> \<odot>\<^sub>\<leftarrow>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<diamond>\<^sub>\<leftarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>r\<down>        \<down>\<midarrow>\<^sup>r
         \<sqdot> \<midarrow>\<odot>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>   " using dual_def leftImageBound_dual by blast
lemma rightImageBound_dual: "\<midarrow>\<^sup>r,\<midarrow>\<^sup>r-DUAL \<diamond>\<^sub>\<rightarrow> \<odot>\<^sub>\<rightarrow>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<diamond>\<^sub>\<rightarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>r\<down>         \<down>\<midarrow>\<^sup>r
         \<sqdot> \<midarrow>\<odot>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>   " using dual_def rightImageBound_dual by blast

lemma leftDualImageBound_dual: "\<midarrow>\<^sup>r,\<midarrow>\<^sup>r-DUAL \<box>\<^sub>\<leftarrow> \<oslash>\<^sub>\<leftarrow>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<box>\<^sub>\<leftarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>r\<down>        \<down>\<midarrow>\<^sup>r
         \<sqdot> \<midarrow>\<oslash>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>   " using dual_def leftDualImageBound_dual by blast
lemma rightDualImageBound_dual: "\<midarrow>\<^sup>r,\<midarrow>\<^sup>r-DUAL \<box>\<^sub>\<rightarrow> \<oslash>\<^sub>\<rightarrow>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<box>\<^sub>\<rightarrow> \<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>r\<down>        \<down>\<midarrow>\<^sup>r
         \<sqdot> \<midarrow>\<oslash>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>   " using dual_def rightDualImageBound_dual by blast


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
lemma leftBound_coresiduation:  "(\<subseteq>),(\<subseteq>)-ADJ (R-\<odot>\<^sub>\<leftarrow>)\<^sup>\<midarrow> (R-\<oslash>\<^sub>\<rightarrow>)\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>(R-\<oslash>\<^sub>\<rightarrow>)\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>              \<up>(\<subseteq>)
          \<sqdot> \<midarrow>(R-\<odot>\<^sub>\<leftarrow>)\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: leftBound_coresiduation)
lemma rightBound_coresiduation: "(\<subseteq>),(\<subseteq>)-ADJ (R-\<odot>\<^sub>\<rightarrow>)\<^sup>\<midarrow> (R-\<oslash>\<^sub>\<leftarrow>)\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>(R-\<oslash>\<^sub>\<leftarrow>)\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>              \<up>(\<subseteq>)
          \<sqdot> \<midarrow>(R-\<odot>\<^sub>\<rightarrow>)\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: rightBound_coresiduation)

text \<open>There is a Galois connection between the right and left bounds.\<close>
lemma rightBound_galois: "(\<subseteq>),(\<subseteq>)-GAL (R-\<odot>\<^sub>\<rightarrow>) (R-\<odot>\<^sub>\<leftarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<odot>\<^sub>\<leftarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>           \<down>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<odot>\<^sub>\<rightarrow> \<rightarrow> \<sqdot>    " by (simp add: rightBound_galois)
text \<open>We shall refer to a Galois connection with reversed orderings as a "dual-Galois-connection".\<close>
lemma leftDualBound_dualgalois: "(\<supseteq>),(\<supseteq>)-GAL (R-\<oslash>\<^sub>\<leftarrow>) (R-\<oslash>\<^sub>\<rightarrow>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<oslash>\<^sub>\<rightarrow> \<midarrow> \<sqdot> 
      (\<supseteq>)\<up>           \<down>(\<supseteq>)
          \<sqdot> \<midarrow>R-\<oslash>\<^sub>\<leftarrow> \<rightarrow> \<sqdot>    " by (simp add: leftDualBound_dualgalois)

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
lemma "\<midarrow>\<^sup>r,\<midarrow>\<^sup>r-DUAL \<diamond>\<^sub>\<leftarrow> \<odot>\<^sub>\<leftarrow>" using leftImageBound_dual by simp
lemma "\<midarrow>\<^sup>r,\<midarrow>\<^sup>r-DUAL \<diamond>\<^sub>\<rightarrow> \<odot>\<^sub>\<rightarrow>" using rightImageBound_dual by simp

text \<open>Recall that for binary relations the analogous of preimage is the left-image operator, definable as
 the right-image of their converse. We now "lift" this idea to higher arities, noting that we must now
 consider six permutations, so we have to come up with a richer naming scheme. In the ternary case,
 we conveniently use a numbering scheme, related to the family of \<open>\<^bold>C\<^sub>a\<^sub>b\<^sub>c\<close> combinators (permutators).\<close>
abbreviation(input) image123::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<diamond>\<^sub>1\<^sub>2\<^sub>3")
  where "\<diamond>\<^sub>1\<^sub>2\<^sub>3 \<equiv> rightImage\<^sub>2 \<circ> \<^bold>C\<^sub>1\<^sub>2\<^sub>3"       \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>2\<^sub>3\<close> as identity permutation is its own inverse (involutive)\<close>
abbreviation(input) image132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<diamond>\<^sub>1\<^sub>3\<^sub>2")
  where "\<diamond>\<^sub>1\<^sub>3\<^sub>2 \<equiv> rightImage\<^sub>2 \<circ> \<^bold>C\<^sub>1\<^sub>3\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<close> is its own inverse\<close>
abbreviation(input) image213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<diamond>\<^sub>2\<^sub>1\<^sub>3")
  where "\<diamond>\<^sub>2\<^sub>1\<^sub>3 \<equiv> rightImage\<^sub>2 \<circ> \<^bold>C\<^sub>2\<^sub>1\<^sub>3"       \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<close> is its own inverse\<close>
abbreviation(input) image231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<diamond>\<^sub>2\<^sub>3\<^sub>1")
  where "\<diamond>\<^sub>2\<^sub>3\<^sub>1 \<equiv> rightImage\<^sub>2 \<circ> \<^bold>C\<^sub>3\<^sub>1\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<close> is the inverse of \<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<close>\<close>
abbreviation(input) image312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<diamond>\<^sub>3\<^sub>1\<^sub>2")
  where "\<diamond>\<^sub>3\<^sub>1\<^sub>2 \<equiv> rightImage\<^sub>2 \<circ> \<^bold>C\<^sub>2\<^sub>3\<^sub>1"       \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<close> is the inverse of \<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<close>\<close>
abbreviation(input) image321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<diamond>\<^sub>3\<^sub>2\<^sub>1")
  where "\<diamond>\<^sub>3\<^sub>2\<^sub>1 \<equiv> rightImage\<^sub>2 \<circ> \<^bold>C\<^sub>3\<^sub>2\<^sub>1"       \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>2\<^sub>1\<close> is its own inverse\<close>

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
  where "\<odot>\<^sub>1\<^sub>2\<^sub>3 \<equiv> rightBound\<^sub>2 \<circ> \<^bold>C\<^sub>1\<^sub>2\<^sub>3"       \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>2\<^sub>3\<close> being identity is its own inverse (involutive)\<close>
abbreviation(input) bound132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<odot>\<^sub>1\<^sub>3\<^sub>2")
  where "\<odot>\<^sub>1\<^sub>3\<^sub>2 \<equiv> rightBound\<^sub>2 \<circ> \<^bold>C\<^sub>1\<^sub>3\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<close> is its own inverse\<close>
abbreviation(input) bound213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<odot>\<^sub>2\<^sub>1\<^sub>3")
  where "\<odot>\<^sub>2\<^sub>1\<^sub>3 \<equiv> rightBound\<^sub>2 \<circ> \<^bold>C\<^sub>2\<^sub>1\<^sub>3"       \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<close> is its own inverse\<close>
abbreviation(input) bound231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<odot>\<^sub>2\<^sub>3\<^sub>1")
  where "\<odot>\<^sub>2\<^sub>3\<^sub>1 \<equiv> rightBound\<^sub>2 \<circ> \<^bold>C\<^sub>3\<^sub>1\<^sub>2"       \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<close> is the inverse of \<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<close>\<close>
abbreviation(input) bound312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<odot>\<^sub>3\<^sub>1\<^sub>2")
  where "\<odot>\<^sub>3\<^sub>1\<^sub>2 \<equiv> rightBound\<^sub>2 \<circ> \<^bold>C\<^sub>2\<^sub>3\<^sub>1"       \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<close> is the inverse of \<open>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<close>\<close>
abbreviation(input) bound321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<odot>\<^sub>3\<^sub>2\<^sub>1")
  where "\<odot>\<^sub>3\<^sub>2\<^sub>1 \<equiv> rightBound\<^sub>2 \<circ> \<^bold>C\<^sub>3\<^sub>2\<^sub>1"       \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>2\<^sub>1\<close> is its own inverse\<close>

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
  where "\<box>\<^sub>1\<^sub>2\<^sub>3 \<equiv> rightDualImage\<^sub>2 \<circ> \<^bold>C\<^sub>1\<^sub>2\<^sub>3"     \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>2\<^sub>3\<close> being identity is its own inverse (involutive)\<close>
abbreviation(input) dualImage132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<box>\<^sub>1\<^sub>3\<^sub>2")
  where "\<box>\<^sub>1\<^sub>3\<^sub>2 \<equiv> rightDualImage\<^sub>2 \<circ> \<^bold>C\<^sub>1\<^sub>3\<^sub>2"     \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<close> is its own inverse\<close>
abbreviation(input) dualImage213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<box>\<^sub>2\<^sub>1\<^sub>3")
  where "\<box>\<^sub>2\<^sub>1\<^sub>3 \<equiv> rightDualImage\<^sub>2 \<circ> \<^bold>C\<^sub>2\<^sub>1\<^sub>3"     \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<close> is its own inverse\<close>
abbreviation(input) dualImage231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<box>\<^sub>2\<^sub>3\<^sub>1")
  where "\<box>\<^sub>2\<^sub>3\<^sub>1 \<equiv> rightDualImage\<^sub>2 \<circ> \<^bold>C\<^sub>3\<^sub>1\<^sub>2"     \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<close> is the inverse of \<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<close>\<close>
abbreviation(input) dualImage312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<box>\<^sub>3\<^sub>1\<^sub>2")
  where "\<box>\<^sub>3\<^sub>1\<^sub>2 \<equiv> rightDualImage\<^sub>2 \<circ> \<^bold>C\<^sub>2\<^sub>3\<^sub>1"     \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<close> is the inverse of \<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<close>\<close>
abbreviation(input) dualImage321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<box>\<^sub>3\<^sub>2\<^sub>1")
  where "\<box>\<^sub>3\<^sub>2\<^sub>1 \<equiv> rightDualImage\<^sub>2 \<circ> \<^bold>C\<^sub>3\<^sub>2\<^sub>1"     \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>2\<^sub>1\<close> is its own inverse\<close>

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

abbreviation(input) dualBound123::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<oslash>\<^sub>1\<^sub>2\<^sub>3")
  where "\<oslash>\<^sub>1\<^sub>2\<^sub>3 \<equiv> rightDualBound\<^sub>2 \<circ> \<^bold>C\<^sub>1\<^sub>2\<^sub>3" \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>2\<^sub>3\<close> as identity permutation is its own inverse (involutive)\<close>
abbreviation(input) dualBound132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<oslash>\<^sub>1\<^sub>3\<^sub>2")
  where "\<oslash>\<^sub>1\<^sub>3\<^sub>2 \<equiv> rightDualBound\<^sub>2 \<circ> \<^bold>C\<^sub>1\<^sub>3\<^sub>2" \<comment> \<open>\<open>\<^bold>C\<^sub>1\<^sub>3\<^sub>2\<close> is its own inverse\<close>
abbreviation(input) dualBound213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<oslash>\<^sub>2\<^sub>1\<^sub>3")
  where "\<oslash>\<^sub>2\<^sub>1\<^sub>3 \<equiv> rightDualBound\<^sub>2 \<circ> \<^bold>C\<^sub>2\<^sub>1\<^sub>3" \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>1\<^sub>3\<close> is its own inverse\<close>
abbreviation(input) dualBound231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<oslash>\<^sub>2\<^sub>3\<^sub>1")
  where "\<oslash>\<^sub>2\<^sub>3\<^sub>1 \<equiv> rightDualBound\<^sub>2 \<circ> \<^bold>C\<^sub>3\<^sub>1\<^sub>2" \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<close> is the inverse of \<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<close>\<close>
abbreviation(input) dualBound312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<oslash>\<^sub>3\<^sub>1\<^sub>2")
  where "\<oslash>\<^sub>3\<^sub>1\<^sub>2 \<equiv> rightDualBound\<^sub>2 \<circ> \<^bold>C\<^sub>2\<^sub>3\<^sub>1" \<comment> \<open>\<open>\<^bold>C\<^sub>2\<^sub>3\<^sub>1/\<^bold>R\<close> is the inverse of \<open>\<^bold>C\<^sub>3\<^sub>1\<^sub>2/\<^bold>L\<close>\<close>
abbreviation(input) dualBound321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<oslash>\<^sub>3\<^sub>2\<^sub>1")
  where "\<oslash>\<^sub>3\<^sub>2\<^sub>1 \<equiv> rightDualBound\<^sub>2 \<circ> \<^bold>C\<^sub>3\<^sub>2\<^sub>1" \<comment> \<open>\<open>\<^bold>C\<^sub>3\<^sub>2\<^sub>1\<close> is its own inverse\<close>

notation(input) dualBound123 ("_-\<oslash>\<^sub>1\<^sub>2\<^sub>3") and dualBound132 ("_-\<oslash>\<^sub>1\<^sub>3\<^sub>2") and
                dualBound213 ("_-\<oslash>\<^sub>2\<^sub>1\<^sub>3") and dualBound231 ("_-\<oslash>\<^sub>2\<^sub>3\<^sub>1") and 
                dualBound312 ("_-\<oslash>\<^sub>3\<^sub>1\<^sub>2") and dualBound321 ("_-\<oslash>\<^sub>3\<^sub>2\<^sub>1")

lemma "R-\<oslash>\<^sub>1\<^sub>2\<^sub>3 = (\<lambda>A B. \<lambda>c. \<exists>a b. \<not>A a \<and> \<not>B b \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<oslash>\<^sub>1\<^sub>3\<^sub>2 = (\<lambda>A C. \<lambda>b. \<exists>a c. \<not>A a \<and> \<not>C c \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<oslash>\<^sub>2\<^sub>1\<^sub>3 = (\<lambda>B A. \<lambda>c. \<exists>b a. \<not>B b \<and> \<not>A a \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<oslash>\<^sub>2\<^sub>3\<^sub>1 = (\<lambda>B C. \<lambda>a. \<exists>b c. \<not>B b \<and> \<not>C c \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<oslash>\<^sub>3\<^sub>1\<^sub>2 = (\<lambda>C A. \<lambda>b. \<exists>c a. \<not>C c \<and> \<not>A a \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<oslash>\<^sub>3\<^sub>2\<^sub>1 = (\<lambda>C B. \<lambda>a. \<exists>c b. \<not>C c \<and> \<not>B b \<and> \<not>R a b c)" unfolding rel_defs func_defs comb_defs by fast

text \<open>Similarly, dual-bounds can also be similarly interrelated by permutation.\<close>
lemma "R-\<oslash>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<oslash>\<^sub>1\<^sub>3\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<oslash>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<oslash>\<^sub>2\<^sub>3\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>1\<^sub>2 R)-\<oslash>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<oslash>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<oslash>\<^sub>1\<^sub>2\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<oslash>\<^sub>i\<^sub>j\<^sub>k\<close>\<close> \<comment> \<open>same permutation\<close>
lemma "R-\<oslash>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<oslash>\<^sub>2\<^sub>1\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<oslash>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<oslash>\<^sub>1\<^sub>3\<^sub>2 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<oslash>\<^sub>i\<^sub>k\<^sub>j\<close>\<close> \<comment> \<open>swap 2 and 3\<close>
lemma "R-\<oslash>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<oslash>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<oslash>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<oslash>\<^sub>2\<^sub>1\<^sub>3 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<oslash>\<^sub>j\<^sub>i\<^sub>k\<close>\<close> \<comment> \<open>swap 1 and 2\<close>
lemma "R-\<oslash>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>1\<^sub>3\<^sub>2 R)-\<oslash>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<oslash>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<oslash>\<^sub>2\<^sub>3\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<oslash>\<^sub>j\<^sub>k\<^sub>i\<close>\<close> \<comment> \<open>left rotation\<close>
lemma "R-\<oslash>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<oslash>\<^sub>3\<^sub>2\<^sub>1" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>3\<^sub>1\<^sub>2 = (\<^bold>C\<^sub>2\<^sub>3\<^sub>1 R)-\<oslash>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>2\<^sub>1\<^sub>3 R)-\<oslash>\<^sub>3\<^sub>1\<^sub>2" unfolding rel_defs comb_defs ..
lemma "R-\<oslash>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>3\<^sub>2\<^sub>1 R)-\<oslash>\<^sub>1\<^sub>2\<^sub>3" unfolding rel_defs comb_defs ..
\<comment> \<open>...\<open>R-\<oslash>\<^sub>3\<^sub>2\<^sub>1 = (\<^bold>C\<^sub>i\<^sub>j\<^sub>k R)-\<oslash>\<^sub>k\<^sub>j\<^sub>i\<close>\<close> \<comment> \<open>full reverse\<close>


subsection \<open>Transformations\<close>

text \<open>We can always make a unary image/bound operator out of its binary counterpart as follows.\<close>
lemma "R-\<diamond>\<^sub>\<rightarrow> A = (\<^bold>K R)-\<diamond>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<odot>\<^sub>\<rightarrow> A = (\<^bold>K R)-\<odot>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<diamond>\<^sub>\<leftarrow> A = (\<^bold>K R\<^sup>\<smile>)-\<diamond>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<odot>\<^sub>\<leftarrow> A = (\<^bold>K R\<^sup>\<smile>)-\<odot>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis

text \<open>And the same holds for the dual variants.\<close>
lemma "R-\<box>\<^sub>\<rightarrow> A = (\<^bold>K R)-\<box>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<oslash>\<^sub>\<rightarrow> A = (\<^bold>K R)-\<oslash>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<box>\<^sub>\<leftarrow> A = (\<^bold>K R\<^sup>\<smile>)-\<box>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis
lemma "R-\<oslash>\<^sub>\<leftarrow> A = (\<^bold>K R\<^sup>\<smile>)-\<oslash>\<^sub>1\<^sub>2\<^sub>3 A A" unfolding rel_defs comb_defs func_defs by metis

text \<open>The converse conversion is not possible in general:\<close>
proposition "\<forall>T. \<exists>R. \<forall>A. (T-\<diamond>\<^sub>1\<^sub>2\<^sub>3 A A) = (R-\<diamond>\<^sub>\<rightarrow> A)" nitpick \<comment> \<open>countermodel found\<close> oops
text \<open>In particular, this does not hold (for arbitrary T)\<close>  (*TODO: how to restrict T so that it holds?*)
proposition "(T-\<diamond>\<^sub>1\<^sub>2\<^sub>3 A A) = ((\<lambda>a b. T a a b)-\<diamond>\<^sub>\<rightarrow> A)" nitpick \<comment> \<open>countermodel found\<close> oops


subsection \<open>Adjunctions\<close>
text \<open>Similar adjunction conditions obtain among binary set-operators as for their unary counterparts.\<close>


subsubsection \<open>Implication-like Operations (and their duals)\<close>

text \<open>We obtain implication-like operations by negating/complementing the first argument of the binary operation.\<close>
abbreviation(input) implicative123::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<Rrightarrow>\<^sub>1\<^sub>2\<^sub>3")
  where "\<Rrightarrow>\<^sub>1\<^sub>2\<^sub>3 R \<equiv> (\<box>\<^sub>1\<^sub>2\<^sub>3 R) \<circ> \<midarrow>"
abbreviation(input) implicative132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<Rrightarrow>\<^sub>1\<^sub>3\<^sub>2")
  where "\<Rrightarrow>\<^sub>1\<^sub>3\<^sub>2 R \<equiv> (\<box>\<^sub>1\<^sub>3\<^sub>2 R) \<circ> \<midarrow>"    
abbreviation(input) implicative213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<Rrightarrow>\<^sub>2\<^sub>1\<^sub>3")
  where "\<Rrightarrow>\<^sub>2\<^sub>1\<^sub>3 R \<equiv> (\<box>\<^sub>2\<^sub>1\<^sub>3 R) \<circ> \<midarrow>"   
abbreviation(input) implicative231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<Rrightarrow>\<^sub>2\<^sub>3\<^sub>1")
  where "\<Rrightarrow>\<^sub>2\<^sub>3\<^sub>1 R \<equiv> (\<box>\<^sub>2\<^sub>3\<^sub>1 R) \<circ> \<midarrow>"   
abbreviation(input) implicative312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<Rrightarrow>\<^sub>3\<^sub>1\<^sub>2")
  where "\<Rrightarrow>\<^sub>3\<^sub>1\<^sub>2 R \<equiv> (\<box>\<^sub>3\<^sub>1\<^sub>2 R) \<circ> \<midarrow>"   
abbreviation(input) implicative321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<Rrightarrow>\<^sub>3\<^sub>2\<^sub>1")
  where "\<Rrightarrow>\<^sub>3\<^sub>2\<^sub>1 R \<equiv> (\<box>\<^sub>3\<^sub>2\<^sub>1 R) \<circ> \<midarrow>"  

notation(input) implicative123 ("_-\<Rrightarrow>\<^sub>1\<^sub>2\<^sub>3") and implicative132 ("_-\<Rrightarrow>\<^sub>1\<^sub>3\<^sub>2") and implicative213 ("_-\<Rrightarrow>\<^sub>2\<^sub>1\<^sub>3") and
                implicative231 ("_-\<Rrightarrow>\<^sub>2\<^sub>3\<^sub>1") and implicative312 ("_-\<Rrightarrow>\<^sub>3\<^sub>1\<^sub>2") and implicative321 ("_-\<Rrightarrow>\<^sub>3\<^sub>2\<^sub>1")

text \<open>We have, for instance:\<close>
lemma "R-\<Rrightarrow>\<^sub>1\<^sub>2\<^sub>3 A B = R-\<box>\<^sub>1\<^sub>2\<^sub>3 (\<midarrow>A) B" unfolding rel_defs func_defs comb_defs ..

text \<open>More explicitly, we have:\<close>
lemma "R-\<Rrightarrow>\<^sub>1\<^sub>2\<^sub>3 = (\<lambda>A B. \<lambda>c. \<forall>a b. R a b c \<rightarrow> (A a \<rightarrow> B b))" unfolding rel_defs func_defs comb_defs by simp
lemma "R-\<Rrightarrow>\<^sub>1\<^sub>3\<^sub>2 = (\<lambda>A C. \<lambda>b. \<forall>a c. R a b c \<rightarrow> (A a \<rightarrow> C c))" unfolding rel_defs func_defs comb_defs by simp
lemma "R-\<Rrightarrow>\<^sub>2\<^sub>1\<^sub>3 = (\<lambda>B A. \<lambda>c. \<forall>b a. R a b c \<rightarrow> (B b \<rightarrow> A a))" unfolding rel_defs func_defs comb_defs by simp
lemma "R-\<Rrightarrow>\<^sub>2\<^sub>3\<^sub>1 = (\<lambda>B C. \<lambda>a. \<forall>b c. R a b c \<rightarrow> (B b \<rightarrow> C c))" unfolding rel_defs func_defs comb_defs by simp
lemma "R-\<Rrightarrow>\<^sub>3\<^sub>2\<^sub>1 = (\<lambda>C B. \<lambda>a. \<forall>c b. R a b c \<rightarrow> (C c \<rightarrow> B b))" unfolding rel_defs func_defs comb_defs by simp
lemma "R-\<Rrightarrow>\<^sub>3\<^sub>1\<^sub>2 = (\<lambda>C A. \<lambda>b. \<forall>c a. R a b c \<rightarrow> (C c \<rightarrow> A a))" unfolding rel_defs func_defs comb_defs by simp

text \<open>We obtain their duals in the same way.\<close>
abbreviation(input) dualimplicative123::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('b) \<Rightarrow> Set('c)" ("\<angle>\<^sub>1\<^sub>2\<^sub>3")
  where "\<angle>\<^sub>1\<^sub>2\<^sub>3 R \<equiv> (\<oslash>\<^sub>1\<^sub>2\<^sub>3 R) \<circ> \<midarrow>"
abbreviation(input) dualimplicative132::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('a) \<Rightarrow> Set('c) \<Rightarrow> Set('b)" ("\<angle>\<^sub>1\<^sub>3\<^sub>2")
  where "\<angle>\<^sub>1\<^sub>3\<^sub>2 R \<equiv> (\<oslash>\<^sub>1\<^sub>3\<^sub>2 R) \<circ> \<midarrow>"    
abbreviation(input) dualimplicative213::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('a) \<Rightarrow> Set('c)" ("\<angle>\<^sub>2\<^sub>1\<^sub>3")
  where "\<angle>\<^sub>2\<^sub>1\<^sub>3 R \<equiv> (\<oslash>\<^sub>2\<^sub>1\<^sub>3 R) \<circ> \<midarrow>"   
abbreviation(input) dualimplicative231::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('b) \<Rightarrow> Set('c) \<Rightarrow> Set('a)" ("\<angle>\<^sub>2\<^sub>3\<^sub>1")
  where "\<angle>\<^sub>2\<^sub>3\<^sub>1 R \<equiv> (\<oslash>\<^sub>2\<^sub>3\<^sub>1 R) \<circ> \<midarrow>"   
abbreviation(input) dualimplicative312::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('a) \<Rightarrow> Set('b)" ("\<angle>\<^sub>3\<^sub>1\<^sub>2")
  where "\<angle>\<^sub>3\<^sub>1\<^sub>2 R \<equiv> (\<oslash>\<^sub>3\<^sub>1\<^sub>2 R) \<circ> \<midarrow>"   
abbreviation(input) dualimplicative321::"Rel\<^sub>3('a,'b,'c) \<Rightarrow> Set('c) \<Rightarrow> Set('b) \<Rightarrow> Set('a)" ("\<angle>\<^sub>3\<^sub>2\<^sub>1")
  where "\<angle>\<^sub>3\<^sub>2\<^sub>1 R \<equiv> (\<oslash>\<^sub>3\<^sub>2\<^sub>1 R) \<circ> \<midarrow>"  

notation(input) dualimplicative123 ("_-\<angle>\<^sub>1\<^sub>2\<^sub>3") and dualimplicative132 ("_-\<angle>\<^sub>1\<^sub>3\<^sub>2") and dualimplicative213 ("_-\<angle>\<^sub>2\<^sub>1\<^sub>3") and
                dualimplicative231 ("_-\<angle>\<^sub>2\<^sub>3\<^sub>1") and dualimplicative312 ("_-\<angle>\<^sub>3\<^sub>1\<^sub>2") and dualimplicative321 ("_-\<angle>\<^sub>3\<^sub>2\<^sub>1")

text \<open>We have, for instance:\<close>
lemma "R-\<angle>\<^sub>1\<^sub>2\<^sub>3 A B = R-\<oslash>\<^sub>1\<^sub>2\<^sub>3 (\<midarrow>A) B" unfolding rel_defs func_defs comb_defs ..

text \<open>More explicitly, we have:\<close>
lemma "R-\<angle>\<^sub>1\<^sub>2\<^sub>3 = (\<lambda>A B. \<lambda>c. \<exists>a b. (A a \<leftharpoondown> B b) \<leftharpoondown> R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<angle>\<^sub>1\<^sub>3\<^sub>2 = (\<lambda>A C. \<lambda>b. \<exists>a c. (A a \<leftharpoondown> C c) \<leftharpoondown> R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<angle>\<^sub>2\<^sub>1\<^sub>3 = (\<lambda>B A. \<lambda>c. \<exists>b a. (B b \<leftharpoondown> A a) \<leftharpoondown> R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<angle>\<^sub>2\<^sub>3\<^sub>1 = (\<lambda>B C. \<lambda>a. \<exists>b c. (B b \<leftharpoondown> C c) \<leftharpoondown> R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<angle>\<^sub>3\<^sub>2\<^sub>1 = (\<lambda>C B. \<lambda>a. \<exists>c b. (C c \<leftharpoondown> B b) \<leftharpoondown> R a b c)" unfolding rel_defs func_defs comb_defs by fast
lemma "R-\<angle>\<^sub>3\<^sub>1\<^sub>2 = (\<lambda>C A. \<lambda>b. \<exists>c a. (C c \<leftharpoondown> A a) \<leftharpoondown> R a b c)" unfolding rel_defs func_defs comb_defs by fast

text \<open>Note, among others:\<close>
lemma "\<Q>\<^sub>3-\<diamond>\<^sub>1\<^sub>2\<^sub>3 = (\<inter>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<Q>\<^sub>3-\<box>\<^sub>1\<^sub>2\<^sub>3 = (\<union>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<Q>\<^sub>3-\<Rrightarrow>\<^sub>1\<^sub>2\<^sub>3 = (\<Rightarrow>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<D>\<^sub>3-\<odot>\<^sub>1\<^sub>2\<^sub>3 = \<midarrow> \<circ>\<^sub>2 (\<inter>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<D>\<^sub>3-\<oslash>\<^sub>1\<^sub>2\<^sub>3 = \<midarrow> \<circ>\<^sub>2 (\<union>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<D>\<^sub>3-\<angle>\<^sub>1\<^sub>2\<^sub>3 = (\<setminus>)" unfolding rel_defs comb_defs func_defs by fast
text \<open>In fact, the previous hold for any permutation (ternary dis/equality being also fully commutative).\<close>
lemma "\<Q>\<^sub>3-\<diamond>\<^sub>3\<^sub>1\<^sub>2 = (\<inter>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<Q>\<^sub>3-\<box>\<^sub>3\<^sub>1\<^sub>2 = (\<union>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<Q>\<^sub>3-\<Rrightarrow>\<^sub>3\<^sub>1\<^sub>2 = (\<Rightarrow>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<D>\<^sub>3-\<odot>\<^sub>3\<^sub>1\<^sub>2 = \<midarrow> \<circ>\<^sub>2 (\<inter>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<D>\<^sub>3-\<oslash>\<^sub>3\<^sub>1\<^sub>2 = \<midarrow> \<circ>\<^sub>2 (\<union>)" unfolding rel_defs comb_defs func_defs by fast
lemma "\<D>\<^sub>3-\<angle>\<^sub>3\<^sub>1\<^sub>2 = (\<setminus>)" unfolding rel_defs comb_defs func_defs by fast
\<comment> \<open>... and so on\<close>

text \<open>Implicative and dual-implicative are "dual" in the following sense (for any permutation):\<close>
lemma "\<Rrightarrow>\<^sub>3\<^sub>2\<^sub>1 = \<midarrow> \<circ>\<^sub>3 \<angle>\<^sub>3\<^sub>2\<^sub>1 \<circ> \<midarrow>\<^sup>3" unfolding adj_defs rel_defs comb_defs func_defs by fast
lemma "\<angle>\<^sub>3\<^sub>2\<^sub>1 = \<midarrow> \<circ>\<^sub>3 \<Rrightarrow>\<^sub>3\<^sub>2\<^sub>1 \<circ> \<midarrow>\<^sup>3" unfolding adj_defs rel_defs comb_defs func_defs by fast
lemma "R-\<Rrightarrow>\<^sub>3\<^sub>2\<^sub>1 = \<midarrow> \<circ>\<^sub>2 (R\<^sup>\<midarrow>-\<angle>\<^sub>3\<^sub>2\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by fast
lemma "R-\<angle>\<^sub>3\<^sub>2\<^sub>1 = \<midarrow> \<circ>\<^sub>2 (R\<^sup>\<midarrow>-\<Rrightarrow>\<^sub>3\<^sub>2\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by fast
\<comment> \<open>... and so on\<close>


subsubsection \<open>Residuation and Coresiduation\<close>
text \<open>Residuation (coresiduation) between \<open>\<diamond>\<close> and \<open>\<Rrightarrow>\<close> (\<open>\<odot>\<close> and \<open>\<angle>\<close>) obtains when swapping second and third parameters.\<close>

lemma image123_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>1\<^sub>2\<^sub>3) (R-\<Rrightarrow>\<^sub>1\<^sub>3\<^sub>2)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image132_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>1\<^sub>3\<^sub>2) (R-\<Rrightarrow>\<^sub>1\<^sub>2\<^sub>3)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image213_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>2\<^sub>1\<^sub>3) (R-\<Rrightarrow>\<^sub>2\<^sub>3\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image231_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>2\<^sub>3\<^sub>1) (R-\<Rrightarrow>\<^sub>2\<^sub>1\<^sub>3)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image312_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>3\<^sub>1\<^sub>2) (R-\<Rrightarrow>\<^sub>3\<^sub>2\<^sub>1)" unfolding adj_defs rel_defs func_defs comb_defs by metis
lemma image321_residuation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (R-\<diamond>\<^sub>3\<^sub>2\<^sub>1) (R-\<Rrightarrow>\<^sub>3\<^sub>1\<^sub>2)" unfolding adj_defs rel_defs func_defs comb_defs by metis

lemma bound123_coresiduation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<odot>\<^sub>1\<^sub>2\<^sub>3)) (\<midarrow> \<circ>\<^sub>2 (R-\<angle>\<^sub>1\<^sub>3\<^sub>2))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma bound132_coresiduation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<odot>\<^sub>1\<^sub>3\<^sub>2)) (\<midarrow> \<circ>\<^sub>2 (R-\<angle>\<^sub>1\<^sub>2\<^sub>3))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma bound213_coresiduation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<odot>\<^sub>2\<^sub>1\<^sub>3)) (\<midarrow> \<circ>\<^sub>2 (R-\<angle>\<^sub>2\<^sub>3\<^sub>1))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma bound231_coresiduation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<odot>\<^sub>2\<^sub>3\<^sub>1)) (\<midarrow> \<circ>\<^sub>2 (R-\<angle>\<^sub>2\<^sub>1\<^sub>3))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma bound312_coresiduation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<odot>\<^sub>3\<^sub>1\<^sub>2)) (\<midarrow> \<circ>\<^sub>2 (R-\<angle>\<^sub>3\<^sub>2\<^sub>1))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma bound321_coresiduation: "(\<subseteq>),(\<subseteq>)-ADJ\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<odot>\<^sub>3\<^sub>2\<^sub>1)) (\<midarrow> \<circ>\<^sub>2 (R-\<angle>\<^sub>3\<^sub>1\<^sub>2))" unfolding adj_defs rel_defs comb_defs func_defs by metis


subsubsection \<open>Galois-connection and its Dual\<close>
text \<open>(Dual)Galois-connections for pairs of \<open>\<odot>\<close> (\<open>\<oslash>\<close>) also obtain when swapping second and third parameters.\<close>

lemma bound123_galois: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 (R-\<odot>\<^sub>1\<^sub>2\<^sub>3) (R-\<odot>\<^sub>1\<^sub>3\<^sub>2)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma bound213_galois: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 (R-\<odot>\<^sub>2\<^sub>1\<^sub>3) (R-\<odot>\<^sub>2\<^sub>3\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma bound312_galois: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 (R-\<odot>\<^sub>3\<^sub>1\<^sub>2) (R-\<odot>\<^sub>3\<^sub>2\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by fastforce 

lemma dualBound123_dualgalois: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 (R-\<oslash>\<^sub>1\<^sub>2\<^sub>3) (R-\<oslash>\<^sub>1\<^sub>3\<^sub>2)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualBound213_dualgalois: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 (R-\<oslash>\<^sub>2\<^sub>1\<^sub>3) (R-\<oslash>\<^sub>2\<^sub>3\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualBound312_dualgalois: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 (R-\<oslash>\<^sub>3\<^sub>1\<^sub>2) (R-\<oslash>\<^sub>3\<^sub>2\<^sub>1)" unfolding adj_defs rel_defs comb_defs func_defs by metis


subsubsection \<open>Conjugation and its Dual\<close>
text \<open>Similarly, (dual)conjugations for pairs of \<open>\<diamond>\<close> (\<open>\<box>\<close>) obtain when swapping second and third parameters.\<close>

lemma image123_conjugation: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<diamond>\<^sub>1\<^sub>2\<^sub>3)) (\<midarrow> \<circ>\<^sub>2 (R-\<diamond>\<^sub>1\<^sub>3\<^sub>2))"  unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image213_conjugation: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<diamond>\<^sub>2\<^sub>1\<^sub>3)) (\<midarrow> \<circ>\<^sub>2 (R-\<diamond>\<^sub>2\<^sub>3\<^sub>1))"  unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma image312_conjugation: "(\<subseteq>),(\<subseteq>)-GAL\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<diamond>\<^sub>3\<^sub>1\<^sub>2)) (\<midarrow> \<circ>\<^sub>2 (R-\<diamond>\<^sub>3\<^sub>2\<^sub>1))"  unfolding adj_defs rel_defs comb_defs func_defs by fastforce

lemma dualImage123_dualconjugation: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<box>\<^sub>1\<^sub>2\<^sub>3)) (\<midarrow> \<circ>\<^sub>2 (R-\<box>\<^sub>1\<^sub>3\<^sub>2))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualImage213_dualconjugation: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<box>\<^sub>2\<^sub>1\<^sub>3)) (\<midarrow> \<circ>\<^sub>2 (R-\<box>\<^sub>2\<^sub>3\<^sub>1))" unfolding adj_defs rel_defs comb_defs func_defs by metis
lemma dualImage312_dualconjugation: "(\<supseteq>),(\<supseteq>)-GAL\<^sub>2 (\<midarrow> \<circ>\<^sub>2 (R-\<box>\<^sub>3\<^sub>1\<^sub>2)) (\<midarrow> \<circ>\<^sub>2 (R-\<box>\<^sub>3\<^sub>2\<^sub>1))" unfolding adj_defs rel_defs comb_defs func_defs by metis

end