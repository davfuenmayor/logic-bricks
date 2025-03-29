theory connectives_disequality
  imports logic_bridge
begin

section \<open>Logical Connectives (using primitive disequality)\<close>

text \<open>Via negativa: disequality (notation: \<open>\<D>\<close>, infix \<open>\<noteq>\<close>) is all you can tell.\<close>

subsection \<open>Basic Connectives\<close>

subsubsection \<open>Falsum\<close>
text \<open>Since no function is non-self-identical, the following serves as definition of falsum/false.\<close>
lemma false_defQ: "\<F> = \<D> \<D> \<D>" by simp 
lemma "\<F> = (\<D> \<noteq> \<D>)" by simp

subsubsection \<open>Identity (for booleans)\<close>
text \<open>In fact, the identity function (for booleans) is also definable from disequality alone.\<close>
lemma id_defQ: "\<^bold>I = \<D> \<F>" unfolding comb_defs by simp
lemma "\<^bold>I = \<D> (\<D> \<D> \<D>)" unfolding comb_defs by simp (*expanded*)

subsubsection \<open>Verum\<close>
text \<open>Asserting that two different functions are different is a good way to encode verum.\<close>
lemma true_defQ: "\<T> = \<D> \<^bold>I (\<^bold>K \<F>)" unfolding comb_defs by metis
lemma "\<T> = (\<^bold>I \<noteq> \<^bold>K \<F>)" unfolding comb_defs by metis
lemma "\<T> = \<D>(\<D>(\<D> \<D> \<D>))(\<^bold>K(\<D> \<D> \<D>))" unfolding comb_defs by metis (*expanded*)

subsubsection \<open>Negation\<close>
text \<open>We can negate a proposition P by asserting that "P is not true" (i.e. P is not equal to verum).\<close>
lemma not_defQ: "(\<not>) = \<D> \<T>" unfolding comb_defs by simp
lemma "(\<not>) = (\<lambda>P. P \<noteq> \<T>)" by simp
lemma "(\<not>) = \<D>(\<D>(\<D>(\<D> \<D> \<D>))(\<^bold>K(\<D> \<D> \<D>)))" unfolding comb_defs by metis (*expanded*)

subsubsection \<open>Equality\<close>
text \<open>Using negation we can define equality for any type (not only boolean).\<close>
lemma eq_defQ: "\<Q> = (\<not>) \<circ>\<^sub>2 \<D>" unfolding comb_defs by simp
lemma "\<Q> = (\<lambda>A B. \<not>(A \<noteq> B))"  by simp

named_theorems eq_defs
declare false_defQ [eq_defs] id_defQ [eq_defs] 
        true_defQ [eq_defs] not_defQ [eq_defs] eq_defQ [eq_defs]

end