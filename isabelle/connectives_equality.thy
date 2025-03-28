theory connectives_equality
  imports base
begin

section \<open>Logical Connectives (using primitive equality)\<close>

text \<open>Via positiva: equality (notation: \<open>\<Q>\<close>, infix \<open>=\<close>) is all you can tell.\<close>

subsection \<open>Basic Connectives\<close>

subsubsection \<open>Verum\<close>
text \<open>Since any function is self-identical, the following serves as definition of verum/true.\<close>
lemma true_defQ: "\<T> = \<Q> \<Q> \<Q>" by simp
lemma "\<T> = (\<Q> = \<Q>)" by simp

subsubsection \<open>Identity (for booleans)\<close>
text \<open>In fact, the identity function (for booleans) is also definable from equality alone.\<close>
lemma id_defQ: "\<^bold>I = \<Q> \<T>" unfolding comb_defs by auto
lemma "\<^bold>I = \<Q> (\<Q> \<Q> \<Q>)" unfolding comb_defs by auto (*expanded*)

subsubsection \<open>Falsum\<close>
text \<open>Asserting that two different functions are equal is a good way to encode falsum.\<close>
lemma false_defQ: "\<F> = \<Q> \<^bold>I (\<^bold>K \<T>)" unfolding comb_defs by metis
lemma "\<F> = (\<^bold>I = \<^bold>K \<T>)" unfolding comb_defs by metis
lemma "\<F> = \<Q>(\<Q>(\<Q> \<Q> \<Q>))(\<^bold>K(\<Q> \<Q> \<Q>))" unfolding comb_defs by metis  (*expanded*)

subsubsection \<open>Negation\<close>
text \<open>We can negate a proposition P by asserting that 'P is absurd' (i.e. P is equal to falsum).\<close>
lemma not_defQ: "(\<not>) = \<Q> \<F>" unfolding comb_defs by auto
lemma "(\<not>) = (\<lambda>P. P = \<F>)" by simp
lemma "(\<not>) = \<Q>(\<Q>(\<Q>(\<Q> \<Q> \<Q>))(\<^bold>K(\<Q> \<Q> \<Q>)))" unfolding comb_defs apply (rule ext) by metis (*expanded*)

subsubsection \<open>Disequality\<close>
text \<open>Using negation we can define disequality for any type (not only boolean).\<close>
lemma diseq_defQ: "\<D> = (\<not>) \<circ>\<^sub>2 \<Q>" unfolding comb_defs by simp
lemma "\<D> = (\<lambda>A B. \<not>(A = B))" by simp

named_theorems eq_defs
declare true_defQ [eq_defs] id_defQ [eq_defs] 
        false_defQ [eq_defs] not_defQ [eq_defs] diseq_defQ [eq_defs]


end