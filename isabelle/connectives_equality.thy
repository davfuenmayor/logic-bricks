theory connectives_equality
  imports base
begin

section \<open>Basic logical connectives (using primitive equality)\<close>

(*Via positiva: equality (notation: \<Q>, infix =) is all you can tell.*)

subsection \<open>Basic connectives\<close>

subsubsection \<open>Verum\<close>
(* Since any function is self-identical, the following serves as definition of verum/true *)
lemma true_defQ: "\<T> = \<Q> \<Q> \<Q>" by simp
lemma "\<T> = (\<Q> = \<Q>)" by simp

subsubsection \<open>Identity (for booleans)\<close>
(* In fact, the identity function (for booleans) is also definable from equality alone*)
lemma id_defQ: "\<^bold>I = \<Q> \<T>" unfolding comb_defs by auto
lemma "\<^bold>I = \<Q> (\<Q> \<Q> \<Q>)" unfolding comb_defs by auto (*expanded*)

subsubsection \<open>Falsum\<close>
(*Asserting that two different functions are equal is a good way to encode falsum*)
lemma false_defQ: "\<F> = \<Q> \<^bold>I (\<^bold>K \<T>)" unfolding comb_defs by metis
lemma "\<F> = (\<^bold>I = \<^bold>K \<T>)" unfolding comb_defs by metis
lemma "\<F> = \<Q>(\<Q>(\<Q> \<Q> \<Q>))(\<^bold>K(\<Q> \<Q> \<Q>))" unfolding comb_defs by metis  (*expanded*)

subsubsection \<open>Negation\<close>
(*We can negate a proposition P by asserting that 'P is absurd' (i.e. P is equal to falsum)*)
lemma not_defQ: "(\<not>) = \<Q> \<F>" unfolding comb_defs by auto
lemma "(\<not>) = (\<lambda>P. P = \<F>)" by simp
lemma "(\<not>) = \<Q>(\<Q>(\<Q>(\<Q> \<Q> \<Q>))(\<^bold>K(\<Q> \<Q> \<Q>)))" unfolding comb_defs apply (rule ext) by metis (*expanded*)

subsubsection \<open>Disequality\<close>
(*Using negation we can define disequality for any type (not only boolean)*)
lemma diseq_defQ: "\<D> = (\<not>) \<circ>\<^sub>2 \<Q>" unfolding comb_defs by simp
lemma "\<D> = (\<lambda>A B. \<not>(A = B))" by simp

named_theorems eq_defs
declare true_defQ [eq_defs] id_defQ [eq_defs] 
        false_defQ [eq_defs] not_defQ [eq_defs] diseq_defQ [eq_defs]


end