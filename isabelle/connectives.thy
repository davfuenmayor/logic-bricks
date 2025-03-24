theory connectives (*Basic theory of logical connectives*)
(* imports connectives_equality    (*via positiva*) *)
imports connectives_disequality (*via negativa*)
begin

subsection \<open>Defined connectives\<close>
text \<open>We illustrate how the logical connectives could have been defined in terms of equality resp. disequality.
 (We actually work with them as they are provided by Isabelle/HOL (with some notational changes).\<close>

subsubsection \<open>Biconditional (aka. iff, double-implication)\<close>
text \<open>Biconditional is just equality (for booleans).\<close>
lemma iff_defQ: "(\<leftrightarrow>) = \<Q>" by auto
lemma "(\<leftrightarrow>) = (\<lambda>A B. A = B)" by auto

subsubsection \<open>XOR (aka. symmetric difference)\<close>
text \<open>XOR is just disequality (for booleans).\<close>
lemma xor_defQ: "(\<rightleftharpoons>) = \<D>" by auto
lemma "(\<rightleftharpoons>) = (\<lambda>A B. A \<noteq> B)" by auto


subsubsection \<open>Conjunction, disjunction, and (co)implication\<close>
text \<open>We can encode them by their truth tables.\<close>

lemma and_defQ:  "(\<and>) = \<^bold>B\<^sub>2\<^sub>0 (\<Q>::ERel(Set(ERel(o)))) \<^bold>V (\<^bold>V \<T> \<T>)" unfolding comb_defs by (metis (full_types))
lemma or_defQ:   "(\<or>) = \<^bold>B\<^sub>2\<^sub>0 (\<D>::ERel(Set(ERel(o)))) \<^bold>V (\<^bold>V \<F> \<F>)" unfolding comb_defs by (metis (full_types))
lemma impl_defQ: "(\<rightarrow>) = \<^bold>B\<^sub>2\<^sub>0 (\<D>::ERel(Set(ERel(o)))) \<^bold>V (\<^bold>V \<T> \<F>)" unfolding comb_defs by (metis (full_types))
lemma excl_defQ: "(\<leftharpoondown>) = \<^bold>B\<^sub>2\<^sub>0 (\<Q>::ERel(Set(ERel(o)))) \<^bold>V (\<^bold>V \<T> \<F>)" unfolding comb_defs by (metis (mono_tags, lifting))

lemma "(\<and>)  = (\<lambda>A B. (\<lambda>r::ERel(o). r A B) = (\<lambda>r. r \<T> \<T>))" by (metis (full_types))
lemma "(\<or>)  = (\<lambda>A B. (\<lambda>r::ERel(o). r A B) \<noteq> (\<lambda>r. r \<F> \<F>))" by (metis (full_types))
lemma "(\<rightarrow>) = (\<lambda>A B. (\<lambda>r::ERel(o). r A B) \<noteq> (\<lambda>r. r \<T> \<F>))" by (metis (full_types))
lemma "(\<leftharpoondown>) = (\<lambda>A B. (\<lambda>r::ERel(o). r A B) = (\<lambda>r. r \<T> \<F>))" by (metis (full_types) le_boolI' order_antisym)

declare iff_defQ [eq_defs] xor_defQ [eq_defs] 
        and_defQ [eq_defs] or_defQ [eq_defs] impl_defQ [eq_defs] excl_defQ [eq_defs]


subsection \<open>Quantifiers and co.\<close>

text \<open>Quantifiers can also be defined using equality/disequality.\<close>
lemma ex_defQ:  "\<exists> = \<D> (\<^bold>K \<F>)" unfolding comb_defs by fastforce
lemma all_defQ: "\<forall> = \<Q> (\<^bold>K \<T>)" unfolding comb_defs by fastforce

declare ex_defQ [eq_defs] all_defQ [eq_defs]

lemma "\<exists>\<phi> = (\<phi> \<noteq> (\<lambda>x. \<F>))" by fastforce
lemma "\<forall>\<phi> = (\<phi> = (\<lambda>x. \<T>))" by fastforce

text \<open>Moreover, they are also definable using indefinite descriptions \<open>\<epsilon>\<close> resp. \<open>\<delta>\<close> and the \<open>\<^bold>\<Pi>\<^sub>1\<^sub>1\<^sub>1/\<^bold>O\<close> combinator\<close>
lemma ex_defEps:  "\<exists> = \<^bold>O \<epsilon>" unfolding comb_defs by (metis (full_types))
lemma all_defEps: "\<forall> = \<^bold>O \<delta>"  unfolding Delta_def comb_defs by (meson someI_ex)

lemma "\<exists>\<phi> = \<phi>(\<epsilon> x.  \<phi> x)" unfolding ex_defEps comb_defs ..
lemma "\<forall>\<phi> = \<phi>(\<epsilon> x. \<not>\<phi> x)" unfolding Delta_def all_defEps comb_defs ..

text \<open>We introduce convenient arity-extended versions of the quantifiers\<close>
abbreviation(input) All2 ("\<forall>\<^sup>2") 
  where "\<forall>\<^sup>2R \<equiv> \<forall>a b. R a b" (* \<forall>(\<forall>\<circ>R) i.e. \<^bold>B\<forall>(\<^bold>B\<forall>)*)
abbreviation(input) All3 ("\<forall>\<^sup>3") 
  where "\<forall>\<^sup>3R \<equiv> \<forall>a b c. R a b c"
\<comment> \<open>... and so on\<close>
abbreviation(input) Ex2 ("\<exists>\<^sup>2")
  where "\<exists>\<^sup>2R \<equiv> \<exists>a b. R a b" (* \<exists>(\<exists>\<circ>R) i.e. \<^bold>B\<exists>(\<^bold>B\<exists>) *)
abbreviation(input) Ex3 ("\<exists>\<^sup>3")
  where "\<exists>\<^sup>3R \<equiv> \<exists>a b c. R a b c"
\<comment> \<open>... and so on\<close>
abbreviation NotEx2 ("\<nexists>\<^sup>2") 
  where "\<nexists>\<^sup>2R \<equiv> \<not>\<exists>\<^sup>2R"
abbreviation NotEx3 ("\<nexists>\<^sup>3") 
  where "\<nexists>\<^sup>3R \<equiv> \<not>\<exists>\<^sup>3R"
\<comment> \<open>... and so on\<close>


subsection \<open>Definite description (for booleans)\<close>

text \<open>Henkin (1963) also defines \<open>\<iota>::(o\<Rightarrow>o)\<Rightarrow>o\<close> via equality, namely as: \<open>\<Q> \<^bold>I\<close>.
Note, however, that in Isabelle/HOL the term \<open>\<iota>::(o\<Rightarrow>o)\<Rightarrow>o\<close> is not introduced as a definition.
Instead, \<open>\<iota>::(o\<Rightarrow>o)\<Rightarrow>o\<close> is an instance of \<open>\<iota>::('a\<Rightarrow>o)\<Rightarrow>'a\<close>, which is an axiomatized (polymorphic) constant.\<close>
lemma "\<iota> = \<Q> \<^bold>I" nitpick oops \<comment> \<open>countermodel\<close>


end
