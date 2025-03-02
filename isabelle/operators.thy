theory operators (* A basic theory of algebraic properties of operations *)
imports adj
begin

section \<open>Set Operations\<close>

(*Add some convenient (arguably less visually-cluttering) notation, reminiscent of logical operations*)
notation(input) leftImage ("\<diamond>") and leftDualImage ("\<box>") and 
                rightImage ("\<diamond>''") and rightDualImage ("\<box>''")
notation(input) leftBound ("\<Zdres>") and leftDualBound ("\<Zndres>") and
                rightBound ("\<Zrres>") and rightDualBound ("\<Znrres>")
notation(input) leftImage ("_-\<diamond>") and leftDualImage ("_-\<box>") and 
                rightImage ("_-\<diamond>''") and rightDualImage ("_-\<box>''")
notation(input) leftBound ("_-\<Zdres>") and leftDualBound ("_-\<Zndres>") and
                rightBound ("_-\<Zrres>") and rightDualBound ("_-\<Znrres>")

subsection \<open>Order embedding\<close>

(*This is a good moment to recall that unary operations on sets (set-operations) are also relations...*)
term "(F :: SetOp('a,'b)) :: Rel(Set('a),'b)"
(*... and thus can be ordered as such. Thus read "F \<subseteq>\<^sup>r G" as: "F is a sub-operation of G" *)
lemma fixes F::"SetOp('a,'b)" and G::"SetOp('a,'b)"
  shows "F \<subseteq>\<^sup>r G = (\<forall>A. F A \<subseteq> G A)" unfolding rel_defs comb_defs func_defs ..

(*Operators are (dual) embeddings between the sub-relation and the (converse) sub-operation orderings*)
lemma rightImage_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding \<diamond>'"
  unfolding rel_defs func_defs comb_defs unfolding func_defs comb_defs by fast
lemma leftImage_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding \<diamond>"
  unfolding rel_defs func_defs comb_defs by fast
lemma rightDualImage_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding \<box>'"
  unfolding rel_defs func_defs comb_defs by fast
lemma leftDualImage_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding \<box>"
  unfolding rel_defs func_defs comb_defs by fast
lemma rightBound_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding \<Zrres>"
  unfolding rel_defs func_defs comb_defs by fast
lemma leftBound_embedding: "(\<subseteq>\<^sup>r),(\<subseteq>\<^sup>r)-embedding \<Zdres>"
  unfolding rel_defs func_defs comb_defs by fast
lemma rightDualBound_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding \<Znrres>"
  unfolding rel_defs func_defs comb_defs by fast
lemma leftDualBound_embedding: "(\<subseteq>\<^sup>r),(\<supseteq>\<^sup>r)-embedding \<Zndres>"
  unfolding rel_defs func_defs comb_defs by fast


subsection \<open>Homomorphisms\<close>
(*Operators are also (dual) homomorphisms from the monoid of relations to the monoid of (set-)operators*)

(*First of all, they map the relational unit \<Q> (resp. its dual \<D>) to the functional unit \<^bold>I (resp. its dual \<midarrow>)*)
lemma rightImage_hom_id: "\<Q>-\<diamond>' = \<^bold>I"
  unfolding rel_defs func_defs comb_defs by simp
lemma leftImage_hom_id: "\<Q>-\<diamond> = \<^bold>I"
  unfolding rel_defs func_defs comb_defs by simp
lemma rightDualImage_hom_id: "\<Q>-\<box>' = \<^bold>I"
  unfolding rel_defs func_defs comb_defs by simp
lemma leftDualImage_hom_id: "\<Q>-\<box> = \<^bold>I"
  unfolding rel_defs func_defs comb_defs by simp
lemma rightBound_hom_id: "\<D>-\<Zrres> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_id: "\<D>-\<Zdres> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_id: "\<D>-\<Znrres> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_id: "\<D>-\<Zndres> = \<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto

(*Moreover, they map the relational composition \<circ>\<^sup>r (resp. its dual \<bullet>\<^sup>r) to their functional counterparts *)
lemma rightImage_hom_comp: "(A \<circ>\<^sup>r B)-\<diamond>' = (A-\<diamond>') \<circ> (B-\<diamond>')" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_hom_comp: "(A \<circ>\<^sup>r B)-\<diamond> = (B-\<diamond>) \<circ> (A-\<diamond>)"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualImage_hom_comp:  "(A \<circ>\<^sup>r B)-\<box>' = (A-\<box>') \<circ> (B-\<box>')" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_hom_comp: "(A \<circ>\<^sup>r B)-\<box> = (B-\<box>) \<circ> (A-\<box>)"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_hom_comp: "(A \<bullet>\<^sup>r B)-\<Zrres> = (A-\<Zrres>) \<bullet> (B-\<Zrres>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_comp: "(A \<bullet>\<^sup>r B)-\<Zdres> = (B-\<Zdres>) \<bullet> (A-\<Zdres>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_comp: "(A \<bullet>\<^sup>r B)-\<Znrres> = (A-\<Znrres>) \<bullet> (B-\<Znrres>)" 
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_comp: "(A \<bullet>\<^sup>r B)-\<Zndres> = (B-\<Zndres>) \<bullet> (A-\<Zndres>)" 
  unfolding rel_defs func_defs comb_defs by auto

(*Operators are also (dual) homomorphisms from the BA of relations to the BA of (set-)operators*)

(*As for the lattice operations, we have the following homomorphisms*)
lemma rightImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-\<diamond>' = R\<^sub>1-\<diamond>' \<union>\<^sup>r R\<^sub>2-\<diamond>'"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-\<diamond> = R\<^sub>1-\<diamond> \<union>\<^sup>r R\<^sub>2-\<diamond>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-\<Zrres> = R\<^sub>1-\<Zrres> \<inter>\<^sup>r R\<^sub>2-\<Zrres>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-\<Zdres> = R\<^sub>1-\<Zdres> \<inter>\<^sup>r R\<^sub>2-\<Zdres>"
  unfolding rel_defs func_defs comb_defs by auto
(*as well as the following dual ('anti') homomorphisms*)
lemma rightDualImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-\<box>' = R\<^sub>1-\<box>' \<inter>\<^sup>r R\<^sub>2-\<box>'"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_hom_join: "(R\<^sub>1 \<union>\<^sup>r R\<^sub>2)-\<box> = R\<^sub>1-\<box> \<inter>\<^sup>r R\<^sub>2-\<box>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-\<Znrres> = R\<^sub>1-\<Znrres> \<union>\<^sup>r R\<^sub>2-\<Znrres>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_meet: "(R\<^sub>1 \<inter>\<^sup>r R\<^sub>2)-\<Zndres> = R\<^sub>1-\<Zndres> \<union>\<^sup>r R\<^sub>2-\<Zndres>"
  unfolding rel_defs func_defs comb_defs by auto

(*...and for the complements*)
lemma rightImage_hom_compl: "(R\<^sup>\<midarrow>)-\<diamond>' = (R-\<Zrres>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftImage_hom_compl: "(R\<^sup>\<midarrow>)-\<diamond> = (R-\<Zdres>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualImage_hom_compl: "(R\<^sup>\<midarrow>)-\<box>' = (R-\<Znrres>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualImage_hom_compl: "(R\<^sup>\<midarrow>)-\<box> = (R-\<Zndres>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightBound_hom_compl: "(R\<^sup>\<midarrow>)-\<Zrres> = (R-\<diamond>')\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftBound_hom_compl: "(R\<^sup>\<midarrow>)-\<Zdres> = (R-\<diamond>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma rightDualBound_hom_compl: "(R\<^sup>\<midarrow>)-\<Znrres> = (R-\<box>')\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto
lemma leftDualBound_hom_compl: "(R\<^sup>\<midarrow>)-\<Zndres> = (R-\<box>)\<^sup>\<midarrow>"
  unfolding rel_defs func_defs comb_defs by auto


subsection \<open>Dualities and Adjunctions (illustrated with diagrams)\<close>

subsubsection \<open>Dualities\<close>
(*Dualities between some pairs of relation-based set-operators*)

lemma leftImage_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<diamond>) (R-\<box>)" unfolding adj_defs rel_defs comb_defs func_defs by simp
lemma "  \<sqdot> \<midarrow>R-\<diamond>\<rightarrow> \<sqdot> 
       \<midarrow>\<down>         \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<box>\<rightarrow> \<sqdot>   " using dual_def leftImage_dual by blast
lemma rightImage_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<diamond>') (R-\<box>')" unfolding adj_defs rel_defs comb_defs func_defs by simp
lemma "  \<sqdot> \<midarrow>R-\<diamond>'\<rightarrow> \<sqdot> 
       \<midarrow>\<down>         \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<box>'\<rightarrow> \<sqdot>   " using dual_def rightImage_dual by blast

lemma leftBound_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<Zdres>) (R-\<Zndres>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma "  \<sqdot> \<midarrow>R-\<Zdres>\<rightarrow> \<sqdot> 
       \<midarrow>\<down>         \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<Zndres>\<rightarrow> \<sqdot>   " using dual_def leftBound_dual by blast
lemma rightBound_dual: "\<midarrow>,\<midarrow>-DUAL (R-\<Zrres>) (R-\<Znrres>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma "  \<sqdot> \<midarrow>R-\<Zrres>\<rightarrow> \<sqdot> 
       \<midarrow>\<down>         \<down>\<midarrow>
         \<sqdot> \<midarrow>R-\<Znrres>\<rightarrow> \<sqdot>   " using dual_def rightBound_dual by blast

(*Recall that set-operators are also relations (and thus can be ordered as such). We thus have the 
 following dualities between the transformations themselves*)
lemma leftImageBound_dual: "\<midarrow>\<^sup>r,\<midarrow>\<^sup>r-DUAL \<diamond> \<Zdres>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<diamond>\<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>r\<down>       \<down>\<midarrow>\<^sup>r
         \<sqdot> \<midarrow>\<Zdres> \<rightarrow> \<sqdot>   " using dual_def leftImageBound_dual by blast
lemma rightImageBound_dual: "\<midarrow>\<^sup>r,\<midarrow>\<^sup>r-DUAL \<diamond>' \<Zrres>" unfolding adj_defs rel_defs func_defs comb_defs by auto
lemma "  \<sqdot> \<midarrow>\<diamond>'\<rightarrow> \<sqdot> 
       \<midarrow>\<^sup>r\<down>       \<down>\<midarrow>\<^sup>r
         \<sqdot> \<midarrow>\<Zrres> \<rightarrow> \<sqdot>   " using dual_def rightImageBound_dual by blast


subsubsection \<open>Residuation\<close>

(*In order theory it is not uncommon to refer to a (covariant) adjunction as a "residuation"*)
lemma leftImage_residuation:  "(\<subseteq>),(\<subseteq>)-ADJ (R-\<diamond>) (R-\<box>')"  unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<box>'\<midarrow> \<sqdot> 
      (\<subseteq>)\<up>          \<up>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<diamond> \<rightarrow> \<sqdot>    " by (simp add: leftImage_residuation)
lemma rightImage_residuation: "(\<subseteq>),(\<subseteq>)-ADJ (R-\<diamond>') (R-\<box>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<box>\<midarrow> \<sqdot> 
      (\<subseteq>)\<up>          \<up>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<diamond>' \<rightarrow> \<sqdot>    " by (simp add: rightImage_residuation)

(*We may refer to a residuation between complements of operators as a "co-residuation" (between the operators)*)
lemma leftBound_coresiduation:  "(\<subseteq>),(\<subseteq>)-ADJ (R-\<Zdres>)\<^sup>\<midarrow> (R-\<Znrres>)\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<Znrres>\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>           \<up>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<Zdres>\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: leftBound_coresiduation)
lemma rightBound_coresiduation: "(\<subseteq>),(\<subseteq>)-ADJ (R-\<Zrres>)\<^sup>\<midarrow> (R-\<Zndres>)\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<Zndres>\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>           \<up>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<Zrres>\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: rightBound_coresiduation)


subsubsection \<open>Galois-connection\<close>

lemma rightBound_galois: "(\<subseteq>),(\<subseteq>)-GAL (R-\<Zrres>) (R-\<Zdres>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<Zdres>\<midarrow> \<sqdot> 
      (\<subseteq>)\<up>          \<down>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<Zrres> \<rightarrow> \<sqdot>    " by (simp add: rightBound_galois)
(*We may refer to a Galois connection with reversed orderings as a "dual-Galois-connection"*)
lemma leftDualBound_dualgalois: "(\<supseteq>),(\<supseteq>)-GAL (R-\<Zndres>) (R-\<Znrres>)" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<Znrres>\<midarrow> \<sqdot> 
      (\<supseteq>)\<up>         \<down>(\<supseteq>)
          \<sqdot> \<midarrow>R-\<Zndres>\<rightarrow> \<sqdot>    " by (simp add: leftDualBound_dualgalois)


subsubsection \<open>Conjugation\<close>

(*We also refer to a (dual) Galois connection between complements of operators as "(dual) conjugation"*)
lemma rightImage_conjugation: "(\<subseteq>),(\<subseteq>)-GAL (R-\<diamond>')\<^sup>\<midarrow> (R-\<diamond>)\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<diamond>\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<subseteq>)\<up>           \<down>(\<subseteq>)
          \<sqdot> \<midarrow>R-\<diamond>'\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: rightImage_conjugation)
lemma leftDualImage_dualconjugation: "(\<supseteq>),(\<supseteq>)-GAL (R-\<box>)\<^sup>\<midarrow> (R-\<box>')\<^sup>\<midarrow>" unfolding adj_defs rel_defs comb_defs func_defs by auto
lemma   " \<sqdot> \<leftarrow>R-\<box>'\<^sup>\<midarrow> \<midarrow> \<sqdot> 
      (\<supseteq>)\<up>            \<down>(\<supseteq>)
          \<sqdot> \<midarrow> R-\<box>\<^sup>\<midarrow> \<rightarrow> \<sqdot>    " by (simp add: leftDualImage_dualconjugation)

end